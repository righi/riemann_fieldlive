# prune.py: delete the declarations that an analysis found unreachable, from a Lean source tree.
#
#   python3 prune.py SRC_DIR DROPPED_CONSTANTS EDGES [--apply] [--out deleted.txt]
#
# SRC_DIR            the project's src/ directory (edited in place with --apply)
# DROPPED_CONSTANTS  dropped-constants.txt from fieldlive (one kernel name per line)
# EDGES              dead-edges.csv from fieldlive ("src,,dst"; .csv or .csv.gz)
#
# Make your structural edits first (remove the field and its assignments, change signatures, ...),
# then run this to delete what only they used. Without --apply it only reports.
#
# 1. Locate top-level declarations by namespace tracking; candidates are located declarations whose
#    exact kernel name is in the dead set.
# 2. Fixed point: keep a candidate if surviving text in its own file, or in a file that (transitively)
#    imports it, mentions any dotted suffix of its name; also keep every dead constant that cannot be
#    located (anonymous instances, ...) unless it is an auxiliary of a deleted candidate. A kept
#    constant keeps its dead dependencies (kernel edges).
# 3. Delete the remaining candidates, with their doc comments, attributes and `... in` prefixes.
#    Clump headers and module boundaries are left alone. Build afterwards: the text check is
#    conservative, but code that is already unreachable still has to compile.
import os, re, sys, gzip, csv, collections
argv = sys.argv[1:]
OUT = "prune-deleted.txt"
if "--out" in argv:
    k = argv.index("--out"); OUT = argv[k + 1]; del argv[k:k + 2]
APPLY = "--apply" in argv
SRC, DROPF, EDGES = [a for a in argv if not a.startswith("--")][:3]
dead = set(l.strip() for l in open(DROPF, encoding="utf-8") if l.strip())
edges = collections.defaultdict(set)
for r in csv.reader((gzip.open(EDGES, "rt") if EDGES.endswith(".gz") else open(EDGES, encoding="utf-8"))):
    if r[0] in dead and r[2] in dead: edges[r[0]].add(r[2])

def unpriv(n):
    m = re.match(r"_private\.(?:[^.]+\.)*?0\.(.*)", n)
    return m.group(1) if m else n

# ---------- read tree ----------
files = {}
for root, _, fs in os.walk(SRC):
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(root, f); rel = os.path.relpath(p, SRC)
            files[rel] = open(p, encoding="utf-8").read().split("\n")
mod2file = {f[:-5].replace("/", "."): f for f in files}
lines = {f: list(ls) for f, ls in files.items()}

# ---------- imports / downstream ----------
# imports may be `import X`, or under the module system `public import X`, `meta import X`, `import all X`
IMP = re.compile(r"^(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?(\S+)", re.M)
rev = collections.defaultdict(set)
for f, ls in files.items():
    for m in IMP.findall("\n".join(ls)):
        if m in mod2file: rev[mod2file[m]].add(f)
_down = {}
def downstream(f):
    if f not in _down:
        seen = {f}; st = [f]
        while st:
            for g in rev[st.pop()]:
                if g not in seen: seen.add(g); st.append(g)
        _down[f] = seen
    return _down[f]

# ---------- declaration spans ----------
KW = r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom|irreducible_def)"
MODS = r"(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+)*"
HDR = re.compile(r"^(?:@\[[^\]]*\]\s*)?" + MODS + KW + r"\s+(?:\{[^}]*\}\s*)?([^\s:({\[]+)")
STARTERS = re.compile(r"^(?:@\[|/-|--|namespace\b|end\b|section\b|open\b|variable\b|universe\b|attribute\b|set_option\b|"
                      r"noncomputable\b|private\b|protected\b|import\b|macro\b|syntax\b|notation\b|infix|prefix|postfix|local\b|scoped\b|"
                      r"elab\b|deriving\b|mutual\b|initialize\b|alias\b|example\b|export\b|#|omit\b|include\b|"
                      + KW[3:-1] + r"\b)")
dup = set()
decl_at = {}     # name -> (file, start, end)  [start inclusive, end exclusive; includes leading doc/attr lines]
for f, ls in files.items():
    ns = []; i = 0; n = len(ls); pend = None
    starts = [j for j, l in enumerate(ls) if l and not l[0].isspace() and STARTERS.match(l)] + [n]
    for k in range(len(starts) - 1):
        a, b = starts[k], starts[k + 1]; l = ls[a]
        if l.startswith("namespace "): ns.append(l.split()[1]); pend = None; continue
        if l.startswith("section") or l.startswith("noncomputable section"): ns.append(None); pend = None; continue
        if l.startswith("end"):
            if ns: ns.pop()
            pend = None; continue
        last = next((ls[j].rstrip() for j in range(b - 1, a - 1, -1) if ls[j].strip()), "")
        # doc comments, attributes, and any `... in` command prefix belong to the declaration that follows
        if (l.startswith(("/--", "@[")) and not HDR.match(l)) or \
           (not HDR.match(l) and not l.startswith(("namespace ", "end", "section")) and last.endswith(" in")):
            if pend is None: pend = a
            continue
        m = HDR.match(l)
        if m:
            nm = m.group(1).rstrip(".")
            full = nm[len("_root_."):] if nm.startswith("_root_.") else ".".join([x for x in ns if x] + [nm])
            if full in decl_at: dup.add(full)
            decl_at.setdefault(full, (f, pend if pend is not None else a, b))
        pend = None

AUX = re.compile(r"\.(eq_\d+|eq_def|_proof_\d+|proof_\d+|match_\d+|mk|rec|casesOn|recOn|noConfusion|noConfusionType|"
                 r"injEq|inj|below|brecOn|_sunfold|_unfold|ext_iff|ext|_simp_\d+|sizeOf_spec|_cstage\d|_closed_\d+)(\..*)?$")
cand = {}        # kernel name -> located name
for d in dead:
    u = unpriv(d)
    if u in decl_at and u not in dup:
        if d.startswith("_private.") and not d.startswith("_private." + decl_at[u][0][:-5].replace("/", ".") + "."): continue
        cand[d] = u
def owner(d):
    u = unpriv(d); p = u.split(".")
    for i in range(len(p) - 1, 0, -1):
        if ".".join(p[:i]) in decl_at: return ".".join(p[:i])
    return None

TOK = re.compile(r"[\w'!?.₀-₉ₐ-ₜͰ-Ͽ]+")
keep = set()                      # dead kernel names we keep
def close(xs):
    st = list(xs)
    while st:
        d = st.pop()
        if d in keep: continue
        keep.add(d); st.extend(edges[d])

for it in range(1, 50):
    deleted = {cand[d] for d in cand if d not in keep}
    # unresolved dead constants (not located, not auxiliary of something deleted) stay
    unres = {d for d in dead - keep if d not in cand and (owner(d) not in deleted)}
    # surviving text per file
    gone = collections.defaultdict(list)
    for nm in deleted:
        f, a, b = decl_at[nm]; gone[f].append((a, b))
    def surviving_tokens(f):
        ls = lines[f]; mask = [l is not None for l in ls]
        for a, b in gone.get(f, ()):
            for j in range(a, b): mask[j] = False
        return set(TOK.findall("\n".join(l for l, k in zip(ls, mask) if k)))
    keys = collections.defaultdict(lambda: collections.defaultdict(set))  # file -> {suffix key -> located names}
    for nm in deleted:
        f = decl_at[nm][0]; p = nm.split(".")
        for i in range(len(p)): keys[f][".".join(p[i:])].add(nm)
    need = collections.defaultdict(set)   # file to scan -> decl files whose keys apply
    for f in keys:
        for g in downstream(f): need[g].add(f)
    hit = set()
    for g, fs in need.items():
        toks = surviving_tokens(g)
        for t in toks:
            pp = t.strip(".").split(".")
            for i in range(len(pp)):
                k = ".".join(pp[i:])
                for f in fs:
                    hit |= keys[f].get(k, set())
    hitk = {d for d in cand if cand[d] in hit}
    new = (hitk | unres) - keep
    print(f"iter {it}: candidates deleted {len(deleted)}, text-referenced {len(hitk - keep)}, unresolved {len(unres - keep)}", flush=True)
    if not new: break
    close(new)

deleted = sorted({cand[d] for d in cand if d not in keep})
spans = collections.defaultdict(list)
for nm in deleted:
    f, a, b = decl_at[nm]; spans[f].append((a, b))
nl = 0
for f, sp in spans.items():
    for a, b in sp:
        for j in range(a, b):
            if lines[f][j] is not None: lines[f][j] = None; nl += 1
print("import edges:", sum(len(v) for v in rev.values()))
print("ambiguous names among dead:", sum(1 for d in dead if unpriv(d) in dup))
print(f"FINAL: delete {len(deleted)} declarations, {nl} lines in {len(spans)} files; kept {len(keep)} of {len(dead)} dead constants")
open(OUT, "w", encoding="utf-8").write("\n".join(deleted) + "\n")
if APPLY:
    for f in spans:
        out = [l for l in lines[f] if l is not None]
        while len(out) > 1 and out[-1] == "" and out[-2] == "": out.pop()
        open(os.path.join(SRC, f), "w", encoding="utf-8").write("\n".join(out))
    print("applied")
