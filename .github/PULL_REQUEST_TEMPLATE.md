## GC problem or research issue

- **GC ID(s):** 
- **Existing issue/PR link(s):** (Use `Refs #...` for partial contributions; use `Closes #...` only when the *exact issue* is fully resolved.)
- **Type:** mathematical theorem / counterexample / Lean formalization / scope correction / prior-art review / manuscript-only clarification
- **Scope:** whole GC / scoped milestone / special case / no GC issue

## Mathematical claim and existing work

- **Exact claim and hypotheses:** 
- **Previously available Lean declarations, papers, and earlier results reused:** 
- **What remains unproved or unchanged:** 

## Lean verification, when formal resolution is claimed

- **Lean file(s), without relocating existing modules:** 
- **Fully qualified theorem/lemma declaration(s):** 
- **Commit SHA and successful Lean CI run URL:** 
- **How the encoded theorem matches *each* exact issue acceptance criterion:** 
- **Trusted assumptions or axioms in dependencies:** 
- **Independent theorem-to-issue review reference:** 

If this PR is documentation, prior-art review, or partial research, write *not claiming formal completion* rather than filling in invented proof references.

## Optional paper

- **Existing or new paper path and precise theorem/section:** 
- **Which manuscript claims match the Lean declarations exactly:** 
- **Additional analytic, numerical, or physical discussion not covered by Lean:** 
- **If no paper:** Not required.

## Status, attribution, and non-regression

- [ ] I checked for existing related issues, proof modules, and manuscripts before adding new files.
- [ ] I did not rewrite or move existing proofs/papers to make the GC catalogue appear complete.
- [ ] I distinguished full resolution, a milestone, and partial progress.
- [ ] Any proposed status update is synchronized with `reyes-problem-repository/problem_registry.json` and `STATUS.md`.
- [ ] For formal completion, the existing Lean build passed and mathematical correspondence was reviewed.
- [ ] Contributor and earlier author attribution is preserved.

**Evidence rule:** A passing Lean build proves the encoded proposition, not automatically the full GitHub issue or physical model. Papers are optional, but any claims of formal verification must be aligned with the recorded exact Lean declarations.
