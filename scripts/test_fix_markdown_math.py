#!/usr/bin/env python3
"""Regression tests for GitHub Markdown math-normalization rules."""
from __future__ import annotations
import unittest
from fix_markdown_math import transform


class MathRenderingTests(unittest.TestCase):
    def fix(self, content: str) -> tuple[str, dict, list]:
        return transform(content, "fixture.md")

    def test_inline_math_preserves_tex(self) -> None:
        got, stats, notes = self.fix(r"Assume \(u\in H^2(\mathbb R^2)\) and \(m>0\)." + "\n")
        self.assertEqual(got, r"Assume $u\in H^2(\mathbb R^2)$ and $m>0$." + "\n")
        self.assertEqual(stats.get("inline_pairs"), 2)
        self.assertEqual(notes, [])

    def test_display_math_on_separate_lines(self) -> None:
        got, stats, notes = self.fix("\\[ \n" + r"\frac{1}{2}\int u^2" + "\n\\]\n")
        self.assertEqual(got, "$$ \n" + r"\frac{1}{2}\int u^2" + "\n$$\n")
        self.assertEqual(stats.get("display_open"), 1)
        self.assertEqual(stats.get("display_close"), 1)
        self.assertEqual(notes, [])

    def test_single_line_display_expands_to_block(self) -> None:
        got, stats, notes = self.fix(r"\[ x^2 + y^2 = 1 \]" + "\n")
        self.assertEqual(got, "$$\nx^2 + y^2 = 1\n$$\n")
        self.assertEqual(stats.get("display_one_line"), 1)
        self.assertEqual(notes, [])

    def test_existing_github_math_preserved(self) -> None:
        original = "$$" + "\n" + r"\begin{aligned}\hat u &= 0\end{aligned}" + "\n$$\n"
        got, stats, notes = self.fix(original)
        self.assertEqual(got, original)
        self.assertEqual(stats, {})
        self.assertEqual(notes, [])

    def test_code_fence_and_inline_code_protected(self) -> None:
        tick = chr(96)
        original = (tick*3 + "python\n" + r"print('\(x\)')" + "\n" + tick*3 + "\n"
                    + tick + r"\(not math\)" + tick + " versus " + r"\(a+b\)" + "\n")
        got, stats, notes = self.fix(original)
        self.assertEqual(got, original.replace(r"\(a+b\)", "$a+b$"))
        self.assertEqual(stats.get("inline_pairs"), 1)
        self.assertEqual(notes, [])

    def test_html_comment_preserved(self) -> None:
        original = "<!-- " + r"\(comment\)" + " --> " + r"\(actual\)" + "\n"
        got, _, _ = self.fix(original)
        self.assertEqual(got, original)

    def test_table_absolute_value_warning(self) -> None:
        original = "| Model | " + r"\(|\psi|^2\)" + " | Item |\n"
        got, _, notes = self.fix(original)
        self.assertEqual(got, original)
        self.assertTrue(any(x["problem"] == "math_pipe_in_table" for x in notes))

    def test_github_table_math_unescaped_pipe_warning(self) -> None:
        original = "| Model | $" + r"|\psi|^2" + "$ | Item |\n"
        got, _, notes = self.fix(original)
        self.assertEqual(got, original)
        self.assertTrue(any(x["problem"] == "unescaped_pipe_inside_table_math" for x in notes))

    def test_no_false_warning_on_escaped_norm_pipes(self) -> None:
        original = "| Model | $" + r"\|u\|_{H^2}" + "$ | Item |\n"
        got, _, notes = self.fix(original)
        self.assertEqual(got, original)
        self.assertEqual(notes, [])

    def test_idempotent(self) -> None:
        original = "Theory: " + r"\(E(u)\ge0\)" + "\n"
        once, _, _ = self.fix(original)
        twice, stats, notes = self.fix(once)
        self.assertEqual(once, twice)
        self.assertEqual(stats, {})
        self.assertEqual(notes, [])


if __name__ == "__main__":
    unittest.main()
