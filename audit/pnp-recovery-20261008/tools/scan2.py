"""Type-based search for unconditional inhabitants of P-vs-NP lower-bound /
separation statements, resolving Prop aliases transitively (so renamed
endpoints are found by their body, not their name).

Usage: python3 -I scan2.py BLOBDIR BLOBMAP OUTJSON
"""
import os, re, sys, json, collections

blobdir, blobmap, outjson = sys.argv[1:4]
where = collections.defaultdict(list)
for line in open(blobmap):
    h, ref, path = line.rstrip("\n").split("\t")
    where[h].append((ref, path))

SEED = {
    "PolyDTMCandidate", "PolyDTMRealization", "InP", "UniversalFailure",
    "FailureGenerator", "PneqNP", "OfficialPneqNP", "SATNotInP", "G21Pointwise",
    "G22Contradiction", "P02Target", "SATFailGap", "SeparationCertificate",
    "SATInternalClosure", "SATExternalClosure", "FinalGapCertificate",
    "UniversalSATFailure", "SATLowerBoundCertificate", "PneNP", "P_ne_NP",
    "PNotEqNP", "PneqNP_official", "OfficialStatement",
}

decl_re = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
    r"(theorem|lemma|def|abbrev|instance|example|axiom|opaque|structure|class|inductive)\b\s*([^\s:({\[]*)",
    re.M)

def strip_comments(s):
    s = re.sub(r"/-.*?-/", lambda m: " " * len(m.group(0)), s, flags=re.S)
    return re.sub(r"--[^\n]*", "", s)

def header_and_body(text, start, end):
    depth, i, colon, assign = 0, start, None, None
    while i < end:
        c = text[i]
        if c in "([{⦃⟨": depth += 1
        elif c in ")]}⦄⟩": depth -= 1
        elif depth == 0:
            if text.startswith(":=", i): assign = i; break
            if c == ":" and colon is None: colon = i
            if re.match(r"\s+where\b", text[i:i+7]): assign = i; break
        i += 1
    binders = text[start:colon] if colon is not None else text[start:(assign or end)]
    typ = text[colon + 1:(assign if assign is not None else end)] if colon is not None else ""
    body = text[assign + 2:end] if assign is not None else ""
    n = lambda s: " ".join(s.split())
    return n(binders), n(typ), n(body)

decls = []
for fn in sorted(os.listdir(blobdir)):
    h = fn[:-5]
    text = strip_comments(open(os.path.join(blobdir, fn), encoding="utf-8", errors="replace").read())
    ms = list(decl_re.finditer(text))
    for k, m in enumerate(ms):
        end = ms[k + 1].start() if k + 1 < len(ms) else len(text)
        # cut at #print / end / namespace lines
        cut = re.search(r"^(#|end\b|namespace\b|section\b|open\b|variable\b)", text[m.end():end], re.M)
        if cut: end = m.end() + cut.start()
        b, t, body = header_and_body(text, m.end(), end)
        decls.append(dict(kind=m.group(1), name=m.group(2), binders=b, type=t, body=body,
                          blob=h, line=text.count("\n", 0, m.start()) + 1))

# transitive alias closure on short names
short = lambda n: n.split(".")[-1]
alias_body = collections.defaultdict(list)
for d in decls:
    if d["kind"] in ("def", "abbrev") and d["binders"] == "" and d["type"] in ("Prop", ""):
        alias_body[short(d["name"])].append(d["body"])
    if d["kind"] in ("structure", "class", "inductive") and d["binders"] == "":
        alias_body[short(d["name"])].append(d["body"] + " " + d["type"])
tok = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
flag = set(SEED)
changed = True
while changed:
    changed = False
    for name, bodies in alias_body.items():
        if name in flag: continue
        for body in bodies:
            if any(short(t) in flag for t in tok.findall(body)):
                flag.add(name); changed = True; break

ARROW = re.compile(r"↔|→|->|\bIff\b")
hits = []
for d in decls:
    if d["kind"] not in ("theorem", "lemma", "def", "abbrev", "example", "instance"): continue
    if d["binders"] != "" or d["type"] in ("", "Prop", "Type"): continue
    t = d["type"]
    if ARROW.search(t): continue
    if t.startswith("¬"):  # refutations are reported separately
        kind = "refutation"
    else:
        kind = "inhabitant"
    used = sorted({short(x) for x in tok.findall(t)} & flag)
    if used:
        hits.append(dict(d, cls=kind, flagged=used, locs=where[d["blob"]][:3], nlocs=len(where[d["blob"]])))
json.dump({"n_decls": len(decls), "n_flagged_aliases": len(flag), "hits": hits},
          open(outjson, "w"), indent=1, ensure_ascii=False)
print("decls:", len(decls), "flagged names:", len(flag), "hits:", len(hits))
for x in hits:
    print(f"{x['cls']:11s} {x['kind']} {x['name']} :: {x['type'][:80]} | flags={x['flagged'][:3]} | {x['locs'][0][0]} {x['locs'][0][1]} n={x['nlocs']}")
