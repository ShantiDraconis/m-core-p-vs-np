"""Win-win / case-split scanner over extracted Lean blobs of many repos.

For every theorem/lemma it records (hypotheses, conclusion). Then it finds:
  A. complementary pairs: same conclusion X, one with hypothesis H, the other
     with hypothesis ¬H (or H → False), possibly via one level of Prop aliases;
  B. dichotomies: a theorem proving `A ∨ B` and two theorems A → X, B → X;
  C. one-sided conditionals on named open hypotheses (RH, Hodge, BSD, ...):
     H → X exists but ¬H → X does not;
  D. explicit case-split machinery (WinWin, by_cases, Classical.em, Or.elim)
     inside proofs.

Usage: python3 -I winwin_scan.py WWDIR OUTJSON
WWDIR contains one subdir per repo with blobs/ and blobmap.tsv (extract.sh).
"""
import os, re, sys, json, collections

wwdir, outjson = sys.argv[1:3]

decl_re = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
    r"(theorem|lemma|def|abbrev|structure|class|axiom)\b\s*([^\s:({\[]*)", re.M)

def strip_comments(s):
    s = re.sub(r"/-.*?-/", lambda m: " " * len(m.group(0)), s, flags=re.S)
    return re.sub(r"--[^\n]*", "", s)

OPEN_ = "([{⦃⟨"
CLOSE = ")]}⦄⟩"

def split_header(text, start, end):
    depth, i, colon, assign = 0, start, None, None
    while i < end:
        c = text[i]
        if c in OPEN_: depth += 1
        elif c in CLOSE: depth -= 1
        elif depth == 0:
            if text.startswith(":=", i): assign = i; break
            if c == ":" and colon is None: colon = i
            if text.startswith(" where", i) or text.startswith("\nwhere", i): assign = i; break
            if text.startswith("|", i) and colon is not None: assign = i; break
        i += 1
    binders = text[start:colon] if colon is not None else text[start:(assign or end)]
    typ = text[colon + 1:(assign if assign is not None else end)] if colon is not None else ""
    body = text[assign:end] if assign is not None else ""
    n = lambda s: " ".join(s.split())
    return n(binders), n(typ), n(body)

def top_binders(b):
    """yield (bracket, names, type) for each top-level binder group."""
    out, depth, cur, br = [], 0, "", None
    for c in b:
        if c in OPEN_:
            if depth == 0: br, cur = c, ""
            else: cur += c
            depth += 1
        elif c in CLOSE:
            depth -= 1
            if depth == 0:
                if ":" in cur:
                    names, t = cur.split(":", 1)
                    out.append((br, names.split(), t.strip()))
                else:
                    out.append((br, [], cur.strip()))
            else: cur += c
        elif depth > 0: cur += c
    return out

def split_arrows(t):
    """split a type on top-level → into premises and conclusion."""
    parts, depth, cur, i = [], 0, "", 0
    # strip leading ∀ binders are kept in the conclusion
    while i < len(t):
        c = t[i]
        if c in OPEN_: depth += 1
        elif c in CLOSE: depth -= 1
        if depth == 0 and t.startswith("→", i):
            parts.append(cur.strip()); cur = ""; i += 1; continue
        if depth == 0 and (t.startswith("∀", i) or t.startswith("∃", i) or t.startswith("fun", i)) and cur.strip() == "":
            # quantified: rest is a single conclusion
            cur += t[i:]; break
        cur += c; i += 1
    parts.append(cur.strip())
    return parts[:-1], parts[-1]

def norm(s):
    s = " ".join(s.split())
    while s.startswith("(") and s.endswith(")") and balanced(s[1:-1]):
        s = s[1:-1].strip()
    return s

def balanced(s):
    d = 0
    for c in s:
        if c in OPEN_: d += 1
        elif c in CLOSE:
            d -= 1
            if d < 0: return False
    return d == 0

def negate_forms(h):
    h = norm(h)
    return {f"¬{h}", f"¬ {h}", f"¬({h})", f"¬ ({h})", f"{h} → False", f"({h}) → False"}

def is_neg(h):
    h = norm(h)
    if h.startswith("¬"): return norm(h[1:])
    if h.endswith("→ False"):
        p, c = split_arrows(h)
        if c == "False" and len(p) == 1: return norm(p[0])
    return None

TYPEISH = re.compile(r"^(Type|Sort|ℕ|ℤ|ℚ|ℝ|ℂ|Nat|Int|Real|Complex|Fin|List|Set|Finset|Bool|String|Array|Option|Fintype|DecidableEq|Inhabited|Nonempty|Prop)\b")

OPEN_HYP = re.compile(
    r"(RiemannHypothesis|\bRH\b|GRH|Hodge(Conjecture)?|BSD|BirchSwinnerton|YangMills|MassGap|"
    r"NavierStokes|Regularity|BlowUp|Smooth|PneqNP|G21Pointwise|SATNotInP|Beal|Poincare|Collatz|"
    r"Goldbach|TwinPrime|OffCritical|offCritical|CriticalLine|criticalLine)")

repos = sorted(d for d in os.listdir(wwdir) if os.path.isdir(os.path.join(wwdir, d)))
thms, aliases, wwuses = [], collections.defaultdict(set), []
for repo in repos:
    base = os.path.join(wwdir, repo)
    where = collections.defaultdict(list)
    bm = os.path.join(base, "blobmap.tsv")
    if not os.path.exists(bm): continue
    for line in open(bm):
        h, ref, path = line.rstrip("\n").split("\t")
        where[h].append((ref, path))
    bd = os.path.join(base, "blobs")
    for fn in sorted(os.listdir(bd)):
        h = fn[:-5]
        raw = open(os.path.join(bd, fn), encoding="utf-8", errors="replace").read()
        text = strip_comments(raw)
        ms = list(decl_re.finditer(text))
        for k, m in enumerate(ms):
            end = ms[k + 1].start() if k + 1 < len(ms) else len(text)
            cut = re.search(r"^(#|end\b|namespace\b|section\b|open\b|variable\b|universe\b)", text[m.end():end], re.M)
            if cut: end = m.end() + cut.start()
            kind, name = m.group(1), m.group(2)
            b, t, body = split_header(text, m.end(), end)
            line = text.count("\n", 0, m.start()) + 1
            loc = where[h][0]
            if kind in ("def", "abbrev") and t.strip() == "Prop" and not top_binders(b) and body.startswith(":="):
                aliases[name.split(".")[-1]].add(norm(body[2:]))
            if kind in ("theorem", "lemma"):
                hyps = []
                for br, names, bt in top_binders(b):
                    if br in "({" and bt and not TYPEISH.match(bt) and not re.match(r"^[a-zα-ω]\w*$", bt):
                        hyps.append(norm(bt))
                prem, concl = split_arrows(t)
                hyps += [norm(p) for p in prem]
                rec = dict(repo=repo, name=name, hyps=hyps, concl=norm(concl), blob=h,
                           ref=loc[0], path=loc[1], nrefs=len(where[h]), line=line,
                           sorry=bool(re.search(r"\bsorry\b|\badmit\b", body)))
                thms.append(rec)
                if re.search(r"WinWin|by_cases|Classical\.em|\bem\b|Or\.elim|byCases|Classical\.byContradiction|by_contra", body):
                    if OPEN_HYP.search(t + " " + b) or "WinWin" in body:
                        wwuses.append(dict(repo=repo, name=name, type=t[:300], path=loc[1], ref=loc[0], line=line,
                                           mech=sorted(set(re.findall(r"WinWin|by_cases|Classical\.em|Or\.elim|byCases|by_contra|Classical\.byContradiction", body)))))

# expand one alias level for negation detection
def expansions(h):
    out = {h}
    s = h.split()[0] if h.split() else h
    if h in aliases: out |= aliases[h]
    return out

# A. complementary pairs
by_concl = collections.defaultdict(list)
for i, r in enumerate(thms):
    by_concl[r["concl"]].append(i)
pairs, seen = [], set()
for concl, idx in by_concl.items():
    if len(idx) < 2 or concl in ("False", "True", ""): continue
    hypmap = collections.defaultdict(list)
    for i in idx:
        for hh in thms[i]["hyps"]:
            for e in expansions(hh):
                hypmap[e].append(i)
    for hh, is_ in hypmap.items():
        n = is_neg(hh)
        if n is None: continue
        pos = []
        for e in [n] + list(aliases.get(n, [])):
            pos += hypmap.get(norm(e), [])
        # positive also via alias whose body equals n
        for a, bodies in aliases.items():
            if n in bodies: pos += hypmap.get(a, [])
        for i in is_:
            for j in pos:
                key = (thms[j]["repo"], thms[j]["name"], thms[i]["repo"], thms[i]["name"])
                if key in seen: continue
                seen.add(key)
                pairs.append(dict(conclusion=concl, hypothesis=n, pos=thms[j], neg=thms[i]))

# B. dichotomies A ∨ B proved (no hyps), and A → X, B → X
def top_or(c):
    depth, i = 0, 0
    while i < len(c):
        ch = c[i]
        if ch in OPEN_: depth += 1
        elif ch in CLOSE: depth -= 1
        elif depth == 0 and ch == "∨":
            return norm(c[:i]), norm(c[i+1:])
        i += 1
    return None
by_hyp = collections.defaultdict(list)
for i, r in enumerate(thms):
    for hh in r["hyps"]:
        by_hyp[hh].append(i)
dich = []
for r in thms:
    if r["hyps"] or r["sorry"]: continue
    o = top_or(r["concl"])
    if not o: continue
    A, B = o
    xa = {thms[i]["concl"]: thms[i] for i in by_hyp.get(A, []) if len(thms[i]["hyps"]) == 1}
    xb = {thms[i]["concl"]: thms[i] for i in by_hyp.get(B, []) if len(thms[i]["hyps"]) == 1}
    common = set(xa) & set(xb)
    dich.append(dict(thm=r, A=A, B=B, A_consumers=len(xa), B_consumers=len(xb),
                     closes=[dict(X=x, viaA=xa[x]["name"], viaB=xb[x]["name"]) for x in sorted(common)]))

# C. one-sided conditionals on named open hypotheses
one_sided = collections.defaultdict(lambda: dict(pos=[], neg=[]))
for r in thms:
    for hh in r["hyps"]:
        if not OPEN_HYP.search(hh) or len(hh) > 160: continue
        n = is_neg(hh)
        key = n if n is not None else hh
        side = "neg" if n is not None else "pos"
        one_sided[key][side].append((r["repo"], r["name"], r["concl"][:160], r["path"], r["sorry"]))

summary = dict(
    theorems=len(thms), repos=len(repos), prop_aliases=len(aliases),
    complementary_pairs=len(pairs),
    nontrivial_pairs=len([p for p in pairs if not p["pos"]["sorry"] and not p["neg"]["sorry"]]),
    dichotomies=len(dich), dichotomies_closing=len([d for d in dich if d["closes"]]),
    open_hyps_pos_only=len([k for k, v in one_sided.items() if v["pos"] and not v["neg"]]),
    open_hyps_both=len([k for k, v in one_sided.items() if v["pos"] and v["neg"]]),
    open_hyps_neg_only=len([k for k, v in one_sided.items() if v["neg"] and not v["pos"]]),
    winwin_like_proofs=len(wwuses),
)
json.dump(dict(summary=summary, pairs=pairs, dichotomies=dich,
               one_sided={k: v for k, v in one_sided.items()}, winwin_uses=wwuses),
          open(outjson, "w"), indent=1, ensure_ascii=False)
print(json.dumps(summary, indent=1))
