#!/usr/bin/env python3
"""Refresh the claims column of the dead-field table posted on rh#151.

Usage: refresh151.py RUNDIR [--apply]
  RUNDIR holds by-structure inputs (fields/), table.md (the posted rows), issue151-comment-v*.md
  (the latest posted body) and refresh-state.json ({"since": ISO time, "comment_id": N}).

Without --apply: print new #151 comments and open/merged PRs that mention a table structure,
as proposed claim lines. With --apply: also add the given claims (CLAIM lines on stdin,
"suffix<TAB>text"), regenerate the comment and PATCH it if the body changed.
Needs `gh` logged in. Matching is by the last name component(s) at identifier boundaries.
"""
import glob, json, os, re, subprocess, sys
from datetime import datetime, timezone

REPO = "leanprover-community/riemann-hypothesis"
HERE = os.path.dirname(os.path.abspath(__file__))
# known text matches that are not claims (structure -> PR numbers)
IGNORE = {"GlobalTheory.FunPr.ThetaLocalInputs": {2079, 2169}, "Formalism.L2.NExpTied": {1071},
          "Formalism.BasicNotions.Host": {1929, 2138, 1930, 2462},
          "GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt": {2294, 2296},
          "GlobalTheory.Mem.LiteralAutomorphy.LocalRepresentationTheoryHypothesesAlt": {2294, 2296}}


def gh(*args):
    return subprocess.run(["gh", *args], check=True, capture_output=True, text=True).stdout


def key_of(s):
    c = s.split(".")
    k = c[-1]
    if len(k) < 7:
        k = ".".join(c[-2:])
    if len(k) < 6:
        k = ".".join(c[-3:])
    return k


def mentions(text, k):
    return re.search(r"(?<![A-Za-z0-9_])" + re.escape(k) + r"(?![A-Za-z0-9_'₀-₉]|\.[A-Z])", text) is not None


def main():
    rd = sys.argv[1]
    apply = "--apply" in sys.argv
    st = json.load(open(os.path.join(rd, "refresh-state.json")))
    rows = [l.split("|")[2].strip().strip("`") for l in open(os.path.join(rd, "table.md")).read().split("\n")[2:]
            if l.startswith("|")]
    claims_f = os.path.join(HERE, "claims-151.tsv")
    claimed = {}
    for l in open(claims_f):
        if l.strip() and not l.startswith("#"):
            k, v = l.rstrip("\n").split("\t", 1)
            claimed[k] = v
    def claim_of(s):
        return "; ".join(v for k, v in claimed.items() if s == k or s.endswith("." + k))

    now = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    # 1. new comments
    cs = json.loads(gh("api", f"repos/{REPO}/issues/151/comments?since={st['since']}&per_page=100"))
    cs = [c for c in cs if c["id"] != st["comment_id"] and c["created_at"] > st["since"]]
    print(f"## {len(cs)} new comment(s) since {st['since']}")
    for c in cs:
        hits = [s for s in rows if mentions(c["body"], key_of(s))]
        print(f"- {c['user']['login']} {c['created_at']} id={c['id']}: {c['body'][:300]!r}")
        for s in hits:
            print(f"  PROPOSE\t{key_of(s)}\t{c['user']['login']}\t(current: {claim_of(s) or '-'})")
    # 2. open and recently merged PRs
    prs = json.loads(gh("pr", "list", "-R", REPO, "--state", "open", "--limit", "800",
                        "--json", "number,title,body,author"))
    prs += [dict(p, merged=True) for p in json.loads(gh("pr", "list", "-R", REPO, "--state", "merged", "--limit", "300",
                                                     "--json", "number,title,body,author"))]
    print(f"## {len(prs)} PRs scanned")
    for s in rows:
        k = key_of(s)
        cur = claim_of(s)
        for p in prs:
            if p["number"] in IGNORE.get(s, ()) or p["title"].startswith("chore: batch"):
                continue
            if mentions(p["title"] + "\n" + (p["body"] or ""), k) and f"#{p['number']}" not in cur:
                tag = " merged" if p.get("merged") else ""
                print(f"  PROPOSE\t{k}\t{p['author']['login']} (#{p['number']}{tag})\t(current: {cur or '-'}) {p['title'][:70]}")
    if not apply:
        return
    # 3. apply claim lines from stdin, regenerate, patch if changed
    add = [l.rstrip("\n") for l in sys.stdin if "\t" in l]
    if add:
        with open(claims_f) as f:
            lines = f.read().rstrip("\n").split("\n")
        keys = {l.split("\t")[0]: i for i, l in enumerate(lines)}
        for a in add:
            k = a.split("\t")[0]
            if k in keys:
                lines[keys[k]] = a
            else:
                lines.append(a)
        open(claims_f, "w").write("\n".join(lines) + "\n")
    bs = subprocess.run([sys.executable, os.path.join(HERE, "by-structure.py"), os.path.join(rd, "fields"), claims_f],
                        check=True, capture_output=True, text=True).stdout
    open(os.path.join(rd, "by-structure.tsv"), "w").write(bs)
    data = {r[0]: r for r in (l.split("\t") for l in bs.rstrip("\n").split("\n")[1:])}
    tbl = ["| constants | structure | dead fields | fields | claimed by |", "|---:|---|---:|---|---|"]
    for s in rows:
        _, _, nd, nf, fr, cl, flds = data[s]
        fs = flds.split(",")
        shown = ", ".join(f"`{f}`" for f in fs[:8]) + (f", … (+{len(fs) - 8})" if len(fs) > 8 else "")
        tbl.append(f"| {fr} | `{s}` | {nd} of {nf} | {shown} | {cl} |")
    cur_body = gh("api", f"repos/{REPO}/issues/comments/{st['comment_id']}", "--jq", ".body").rstrip("\n")
    src = cur_body.split("\n")
    i = next(k for k, l in enumerate(src) if l.startswith("| constants"))
    j = i
    while j < len(src) and src[j].startswith("|"):
        j += 1
    new_tbl = src[:i] + tbl + src[j:]
    if new_tbl == src:
        print("table unchanged; not editing")
    else:
        stamp = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%MZ")
        body = re.sub(r"\(updated \d{4}-\d\d-\d\d \d\d:\d\dZ\)", f"(updated {stamp})", "\n".join(new_tbl))
        n = 1 + max([int(m.group(1)) for f in glob.glob(os.path.join(rd, "issue151-comment-v*.md")) if (m := re.search(r"-v(\d+)\.md$", f))] or [0])
        out = os.path.join(rd, f"issue151-comment-v{n}.md")
        open(out, "w").write(body)
        gh("api", "-X", "PATCH", f"repos/{REPO}/issues/comments/{st['comment_id']}", "-F", f"body=@{out}")
        print(f"edited comment {st['comment_id']} ({out})")
    st["since"] = now
    json.dump(st, open(os.path.join(rd, "refresh-state.json"), "w"))


if __name__ == "__main__":
    main()
