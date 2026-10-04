#!/usr/bin/env python3
"""Check (and with --fix, repair) links in the human-facing Markdown docs.

Three checks, on every *.md outside agent-docs/ and external/ (or the files given):
  1. Line links [`name`](path/file.rs#L123): line 123 must define `name`
     (fn / spec fn / proof fn / enum / struct / type / trait; `Type::item`
     means `item`). --fix moves the line number to the unique definition.
  2. Every relative link [..](path) must point at an existing file or dir.
  3. File references must be links (docs convention): a `code span` or an
     agent-docs/... path that names an existing file or directory, but is
     not linked, is reported. A directory only needs one link per doc.
     (Self-references and generic mentions such as
     "each directory's `README.md`" are fine; silence those by rewording.)

  scripts/readme_links.py [--fix] [file.md ...]
Exits non-zero if anything is reported (after --fix: what could not be fixed).
"""
import re, subprocess, sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LINE_LINK = re.compile(r"\[`([^`]+)`\]\(([^)#\s]+)#L(\d+)\)")
ANY_LINK = re.compile(r"\[[^\]]*\]\(([^)\s]+)\)")
PROTECT = re.compile(r"```.*?```|\[[^\]]*\]\([^)]*\)", re.S)
REF = re.compile(r"`([^`\s]+)`|(?<![\w/(\[])(agent-docs/[\w./-]+\.md)")
# Known generic mentions (not references to one file).
GENERIC = {("AGENTS.md", "README.md")}


def defines(line, name):
    base = re.escape(re.sub(r"<.*", "", name).split("::")[-1])
    return re.match(rf"\s*(pub\s+)?((open|closed)\s+)?(spec\s+|proof\s+)?(fn|enum|struct|type|trait)\s+{base}\b", line)


def human_docs():
    out = subprocess.run(["git", "ls-files", "--cached", "--others", "--exclude-standard", "*.md"],
                         cwd=REPO, capture_output=True, text=True).stdout.split()
    docs = [REPO / f for f in out if not f.startswith(("agent-docs/", "external/"))]
    if (REPO / "PLAN.md").exists():
        docs.append(REPO / "PLAN.md")  # owner's plan, git-ignored
    return sorted(set(docs))


def main():
    args = sys.argv[1:]
    fix = "--fix" in args
    files = [Path(a).resolve() for a in args if a != "--fix"] or human_docs()
    bad = 0

    def report(msg):
        nonlocal bad
        bad += 1
        print(msg)

    for doc in files:
        rel_doc = doc.relative_to(REPO)
        text = doc.read_text()

        def check_line(m):
            name, path, ln = m.group(1), m.group(2), int(m.group(3))
            target = doc.parent / path
            if not target.is_file():
                report(f"{rel_doc}: {name} links to missing file {path}")
                return m.group(0)
            lines = target.read_text().splitlines()
            if ln <= len(lines) and defines(lines[ln - 1], name):
                return m.group(0)
            hits = [i + 1 for i, l in enumerate(lines) if defines(l, name)]
            if fix and len(hits) == 1:
                print(f"{rel_doc}: {name} L{ln} -> L{hits[0]}")
                return f"[`{name}`]({path}#L{hits[0]})"
            report(f"{rel_doc}: {name} at {path}#L{ln} is wrong (definitions at {hits})")
            return m.group(0)

        new = LINE_LINK.sub(check_line, text)
        if fix and new != text:
            doc.write_text(new)
            text = new

        for m in ANY_LINK.finditer(text):
            target = m.group(1).split("#")[0]
            if not target or re.match(r"[a-z]+:", target):
                continue
            if not (doc.parent / target).exists():
                report(f"{rel_doc}: link to missing {target}")

        linked = {(doc.parent / m.group(1).split("#")[0]).resolve()
                  for m in ANY_LINK.finditer(text) if not re.match(r"[a-z]+:", m.group(1))}
        free = PROTECT.sub("", text)
        for m in REF.finditer(free):
            cand = (m.group(1) or m.group(2)).rstrip(".,:;").split("#")[0]
            if not re.search(r"[/.]", cand) or cand in (".", "..") or (str(rel_doc), cand) in GENERIC:
                continue
            for base in (doc.parent, REPO):
                p = base / cand
                if p.exists():
                    # a directory needs one link per doc; repeat mentions are fine
                    if p.is_dir() and p.resolve() in linked:
                        break
                    if p.resolve() != doc.resolve():
                        report(f"{rel_doc}: `{cand}` names a file but is not a link")
                    break
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
