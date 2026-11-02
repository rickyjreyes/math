#!/usr/bin/env python3
"""Safely normalize math delimiters for GitHub Markdown (standard library only)."""
from __future__ import annotations
import argparse
import json
import re
from collections import Counter
from pathlib import Path

FENCE = re.compile(r"^ {0,3}(\x60{3,}|~{3,})")
INLINE = re.compile(r"(?<!\\)\\\((.+?)(?<!\\)\\\)")
DISPLAY_ONE = re.compile(r"^( {0,3})\\\[\s*(.*?)\s*\\\](\s*)$")
OPEN_DISPLAY = re.compile(r"^( {0,3})\\\[(\s*)$")
CLOSE_DISPLAY = re.compile(r"^( {0,3})\\\](\s*)$")
LATEX_DELIM = re.compile(r"(?<!\\)\\(?:\(|\)|\[|\])")
BARE_ENV = re.compile(r"(?<!\\)\\begin\{(?:equation\*?|align\*?|gather\*?|multline\*?)\}")
HTML_CODE_OPEN = re.compile(r"<(?:pre|code)\b", flags=re.I)
HTML_CODE_CLOSE = re.compile(r"</(?:pre|code)\s*>", flags=re.I)


def inline_code_ranges(line: str) -> list[tuple[int, int]]:
    spans = []
    i = 0
    while i < len(line):
        if line[i] != chr(96):
            i += 1
            continue
        end = i
        while end < len(line) and line[end] == chr(96):
            end += 1
        delim = line[i:end]
        m = re.search(r"(?<!\x60)" + re.escape(delim) + r"(?!\x60)", line[end:])
        if m:
            b = end + m.start()
            spans.append((i, b + len(delim)))
            i = b + len(delim)
        else:
            spans.append((i, len(line)))
            break
    return spans


def overlaps(a: int, b: int, spans: list[tuple[int, int]]) -> bool:
    return any(a < right and b > left for left, right in spans)


def rewrite_line(line: str, path: str, n: int,
                 warnings: list[dict], counts: Counter) -> str:
    spans = inline_code_ranges(line)
    one = DISPLAY_ONE.fullmatch(line)
    if one and not spans:
        indent, expression, trail = one.groups()
        counts["display_one_line"] += 1
        return f"{indent}{chr(36)*2}\n{indent}{expression}\n{indent}{chr(36)*2}{trail}"
    for pattern, key in ((OPEN_DISPLAY, "display_open"), (CLOSE_DISPLAY, "display_close")):
        m = pattern.fullmatch(line)
        if m and not spans:
            counts[key] += 1
            return f"{m.group(1)}{chr(36)*2}{m.group(2)}"

    def sub(m: re.Match[str]) -> str:
        expression = m.group(1)
        if overlaps(*m.span(), spans):
            return m.group(0)
        if "|" in expression and line.lstrip().startswith("|"):
            warnings.append({"file": path, "line": n, "problem": "math_pipe_in_table"})
            return m.group(0)
        if "$" in expression:
            warnings.append({"file": path, "line": n, "problem": "nested_dollar"})
            return m.group(0)
        counts["inline_pairs"] += 1
        return "$" + expression + "$"
    result = INLINE.sub(sub, line)
    protected_spans = inline_code_ranges(result)
    # GitHub tables split at raw vertical bars even when they occur in inline math.
    # Keep the original equation and surface the location for human review.
    if line.lstrip().startswith("|"):
        for math in re.finditer(r"(?<!\\)\$(?!\$)(.*?)(?<!\\)\$", result):
            if not overlaps(*math.span(), protected_spans):
                if re.search(r"(?<!\\)\|", math.group(1)):
                    warnings.append({"file": path, "line": n,
                                     "problem": "unescaped_pipe_inside_table_math"})
    for pat, name in ((LATEX_DELIM, "unpaired_or_ambiguous_delimiter"),
                      (BARE_ENV, "bare_latex_environment")):
        for m in pat.finditer(result):
            if not overlaps(*m.span(), protected_spans):
                warnings.append({"file": path, "line": n, "problem": name,
                                 "token": m.group(0)})
    return result


def transform(data: str, path: str) -> tuple[str, dict, list[dict]]:
    counts: Counter = Counter()
    warnings: list[dict] = []
    lines = data.splitlines(keepends=True)
    result = []
    fence_char = ""
    fence_len = 0
    html_code = False
    html_comment = False
    frontmatter = bool(lines and lines[0].strip() == "---")
    dollar_display = False
    for n, original in enumerate(lines, 1):
        line = original.rstrip("\r\n")
        ending = original[len(line):]
        if frontmatter:
            result.append(original)
            if n > 1 and line.lstrip() in ("---", "..."):
                frontmatter = False
            continue
        # Existing GitHub MathJax display blocks already contain mathematical TeX.
        # Do not rewrite delimiters nested inside them.
        if not fence_len and line.strip() == "$":
            result.append(original)
            dollar_display = not dollar_display
            continue
        if dollar_display and not fence_len:
            result.append(original)
            continue
        fm = FENCE.match(line)
        if fence_len:
            result.append(original)
            if fm and fm.group(1)[0] == fence_char and len(fm.group(1)) >= fence_len:
                fence_len = 0
            continue
        if fm:
            fence_char, fence_len = fm.group(1)[0], len(fm.group(1))
            result.append(original)
            continue
        if html_code or html_comment:
            result.append(original)
            if html_code and HTML_CODE_CLOSE.search(line):
                html_code = False
            if html_comment and "-->" in line:
                html_comment = False
            continue
        if "<!--" in line:
            result.append(original)
            html_comment = "-->" not in line.split("<!--", 1)[1]
            continue
        if HTML_CODE_OPEN.search(line):
            result.append(original)
            html_code = not bool(HTML_CODE_CLOSE.search(line))
            continue
        result.append(rewrite_line(line, path, n, warnings, counts) + ending)
    return "".join(result), dict(counts), warnings


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--report", type=Path)
    args = ap.parse_args()
    root = args.root.resolve()
    totals: Counter = Counter()
    changed = []
    warnings = []
    files = sorted(p for p in root.rglob("*") if p.is_file() and p.suffix.lower() == ".md"
                   and ".git" not in p.parts)
    for p in files:
        rel = p.relative_to(root).as_posix()
        original = p.read_text(encoding="utf-8")
        fixed, edits, review = transform(original, rel)
        totals.update(edits)
        warnings.extend(review)
        if fixed != original:
            changed.append({"path": rel, "edits": sum(edits.values())})
            if args.write:
                p.write_text(fixed, encoding="utf-8", newline="")
    report = {"markdown_files": len(files), "changed": len(changed),
              "changed_files": changed, "edits": dict(totals),
              "review_count": len(warnings), "warnings": warnings}
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, ensure_ascii=False, indent=2)+"\n",
                               encoding="utf-8")
    print(f"Markdown audit: {len(files)} files, {len(changed)} needing updates, "
          f"{dict(totals)}, {len(warnings)} warnings.")
    for w in warnings[:45]:
        print(f"REVIEW: {w['file']}:{w['line']} {w['problem']}: {w.get('token', '')}")
    if len(warnings) > 45:
        print(f"...and {len(warnings)-45} further warnings (see JSON audit)")
    if args.check and (changed or warnings):
        print("FAIL: GitHub Markdown math has unnormalized or ambiguous render cases")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
