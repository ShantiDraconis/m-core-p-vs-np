"""Scan every unique Lean blob for (a) unconditional inhabitants of terminal
P vs NP targets and (b) trust-breaking constructs. Usage:
  python3 -I scan.py BLOBDIR BLOBMAP OUTDIR
"""
import os, re, sys, json, collections

blobdir, blobmap, outdir = sys.argv[1:4]
os.makedirs(outdir, exist_ok=True)

where = collections.defaultdict(list)  # blob -> [(ref, path)]
for line in open(blobmap):
    h, ref, path = line.rstrip("\n").split("\t")
    where[h].append((ref, path))

TERMINAL = [
    "PneqNP", "OfficialPneqNP", "G21Pointwise", "NormalizedG21Pointwise",
    "G22Contradiction", "P02Target", "SATFailGap", "UniversalFailure",
    "FailureGenerator", "SeparationCertificate", "SATInternalClosure",
    "SATExternalClosure", "FinalGapCertificate",
]
term_re = re.compile(r"\b(" + "|".join(TERMINAL) + r")\b")
notinp_re = re.compile(r"¬\s*\(?\s*InP\b|Not\s*\(?\s*InP\b")

decl_re = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
    r"(theorem|lemma|def|abbrev|instance|example|axiom|opaque)\b\s*([^\s:({\[]*)",
    re.M)

def strip_comments(s):
    s = re.sub(r"/-.*?-/", lambda m: " " * len(m.group(0)), s, flags=re.S)
    s = re.sub(r"--[^\n]*", "", s)
    return s

def split_sig(text, start):
    """Return (binders, type) for the declaration header starting at start."""
    depth = 0
    i = start
    colon = None
    n = len(text)
    while i < n:
        c = text[i]
        if c in "([{⦃⟨":
            depth += 1
        elif c in ")]}⦄⟩":
            depth -= 1
        elif depth == 0:
            if text.startswith(":=", i):
                break
            if c == ":" and colon is None:
                colon = i
            if text.startswith(" where", i) or text.startswith("\nwhere", i):
                break
            if c == "\n" and i + 1 < n and text[i + 1] == "|" and colon is not None:
                break
            # next declaration start guard
            if c == "\n" and decl_re.match(text, i + 1):
                break
        i += 1
    if colon is None:
        return text[start:i], ""
    return text[start:colon], text[colon + 1:i]

uncond, cond_pneqnp, trust = [], [], []
for fn in sorted(os.listdir(blobdir)):
    h = fn[:-5]
    raw = open(os.path.join(blobdir, fn), encoding="utf-8", errors="replace").read()
    text = strip_comments(raw)
    locs = where[h]
    for kw, rx in [("sorry", r"\bsorry\b"), ("admit", r"\badmit\b"),
                   ("native_decide", r"\bnative_decide\b"),
                   ("implemented_by", r"implemented_by"), ("extern", r"@\[extern"),
                   ("unsafe", r"\bunsafe\b"), ("ofReduceBool", r"ofReduceBool")]:
        for m in re.finditer(rx, text):
            ln = text.count("\n", 0, m.start()) + 1
            trust.append({"kind": kw, "blob": h, "line": ln, "locs": locs[:3],
                          "nlocs": len(locs)})
    for m in decl_re.finditer(text):
        kind, name = m.group(1), m.group(2)
        binders, typ = split_sig(text, m.end())
        typ_n = " ".join(typ.split())
        bind_n = " ".join(binders.split())
        ln = text.count("\n", 0, m.start()) + 1
        rec = {"kind": kind, "name": name, "binders": bind_n, "type": typ_n,
               "blob": h, "line": ln, "locs": locs[:3], "nlocs": len(locs)}
        if kind in ("axiom", "opaque"):
            trust.append(dict(rec, kind=kind))
        if kind in ("theorem", "lemma", "def", "abbrev", "instance", "example"):
            hits_term = term_re.search(typ_n) or notinp_re.search(typ_n)
            if hits_term and bind_n.strip() == "" and kind in ("theorem", "lemma", "example", "instance"):
                uncond.append(rec)
            elif hits_term and kind in ("def", "abbrev") and bind_n.strip() == "" \
                    and not typ_n.startswith("Prop") and typ_n != "":
                # a def whose *type* is a terminal object is a candidate inhabitant
                uncond.append(rec)
            if re.fullmatch(r"(OfficialPneqNP\b.*|PneqNP)", typ_n.strip()) and bind_n.strip():
                cond_pneqnp.append(rec)

json.dump(uncond, open(os.path.join(outdir, "uncond.json"), "w"), indent=1, ensure_ascii=False)
json.dump(cond_pneqnp, open(os.path.join(outdir, "cond.json"), "w"), indent=1, ensure_ascii=False)
json.dump(trust, open(os.path.join(outdir, "trust.json"), "w"), indent=1, ensure_ascii=False)
print("unconditional terminal-typed declarations:", len(uncond))
print("conditional PneqNP theorems:", len(cond_pneqnp))
print("trust-breaking hits:", len(trust))
print(collections.Counter(t["kind"] for t in trust))
