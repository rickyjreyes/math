# Candidate question notebook

**Purpose:** Capture new, pre-GC research ideas and unresolved forks from proved theorems without prematurely declaring them open conjectures. This is a **discovery notebook**, not a duplicate of the 300-question catalogue, adoption map, or progress register. Use the notebook to develop constructive WCT-related questions and record exact limitations when one mechanism fails, without claiming an unproven alternative succeeds. Numbered GC entries remain in [the problem register](STATUS.md); notebook entries are exploratory, may be wrong, and can be rejected without creating a new grand challenge. [Research direction](../RESEARCH_DIRECTION.md).

## N001 · Curvature closure selection after nonuniqueness

**Related:** GC08. **Observation:** Agreement on constant-amplitude plane waves does not determine a unique curvature operator. **Counterexample:** Add any multiple of the Laplacian of intensity to the stated regularized curvature functional. **Next question:** Which physically and mathematically motivated additional axioms leave only one operator, if any? **Falsifier:** Construct two operators satisfying the augmented axioms. **Status:** Candidate refinement; unrestricted uniqueness already refuted.

## N002 · Critical mass at which confined minimizers appear

**Related:** GC06, GC16. **Question:** For a fixed frozen parameter triple, is the set of masses for which the constrained infimum is attained an interval, a disjoint union, or another type of set? **First test:** Examine scaling and separated-bump sequences at boundary masses. **Status:** Candidate; existing whole-space minimization results must be compared first.

## N003 · Selection band versus unique wavelength

**Related:** GC11. **Question:** Under explicitly defined periodic perturbations, do multiple stable stripe wave numbers coexist? **Falsifier to uniqueness:** Exhibit two non-equivalent stable stripe branches at the same parameters. **Status:** Candidate; known Swift–Hohenberg literature already addresses related band behavior.

## N004 · Static Hopf soliton versus dynamically stable wave

**Related:** GC36. **Question:** What additional statement about well-posed time evolution and orbital stability is left after known Hopf-sector minimizing results? **First test:** Freeze the dynamical field equation and perturbation norm. **Status:** Candidate; not a claim that knotted solitons were unknown.

## N005 · Universality under conservation and reversibility

**Related:** GC43. **Question:** Does one fixed phase-labeled conservative reversible radius-one cellular automaton achieve uniform polynomial TM simulation? **First test:** Specify the local rule and prove its required invariants. **Status:** Candidate; general cellular automaton universality already known.

---

## N006 · A zero-width Fourier ring versus localized waves

**Related:** GC14, GC11. **Established:** [FourierShellL2.lean](../lean/MathProofs/FourierShellL2.lean) excludes a nonzero `L²` state with Fourier support entirely on a measure-zero shell; this is a theorem in the stated whole-space setting, not a simulation. **Open fork:** Quantify the minimum bandwidth needed for a specified level of spatial concentration and decay. **First test:** Fix a smooth annular spectral window and derive a normalized spatial-tail estimate or an explicit counterexample. **Status:** New research question; exact-shell obstruction already established, bandwidth claim unproved.

## N007 · Local observation fibers and added measurements

**Related:** GC26, GC27, GC29. **Established:** [V18Rank.lean](../lean/MathProofs/V18Rank.lean) and [V18Identifiability.lean](../lean/MathProofs/V18Identifiability.lean) establish a restricted rank/nullity and a local equal-output fiber. **Open fork:** Can additional independent observables remove the local ambiguity without relying on prior bounds? **First test:** Specify one augmented observation map and establish a rank increase, or prove structural dependence prevents it. **Status:** Candidate follow-up, not global identifiability.

## N008 · Degenerate higher derivatives and the scope of no-go results

**Related:** GC21, GC24, GC25. **Established:** [R16 completion-class obstruction](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/lean/ReleaseProofs/R16_CompletionClasses.lean) covers a specified failure class; it does not say every higher-gradient action is inconsistent. **Open fork:** Which degeneracies and propagated constraints allow a bounded reduced Hamiltonian for a precisely stated parent model? **First test:** Exhibit and check one nontrivial degenerate acceleration Hessian and its constraint preservation, or an obstruction. **Status:** Candidate design question; no parent-theory solution claimed.

## N009 · Finite-mode spectral closure versus true nonlinear dynamics

**Related:** GC13, GC15. **Established:** [FourierLeakage.lean](../lean/MathProofs/FourierLeakage.lean) computes nonlinear convolution/leakage for a specified periodic equation. **Open fork:** Which exceptional finite coordinate sets, if any, can be invariant once exact coefficients and all-data quantifiers are fixed? **First test:** Audit the full existing theorem against GC15, including special singleton and trivial cases, *before* proving anything again. **Status:** Strong existing theorem, GC correspondence under review.

## N010 · Binding at the edge of the proved mass interval

**Related:** GC06, GC16, GC19, GC53. **Established:** [StrictBinding.lean](../lean/MathProofs/StrictBinding.lean), [WholeSpaceMinimizers.lean](../lean/MathProofs/WholeSpaceMinimizers.lean) and [OrbitalStability.lean](../lean/MathProofs/OrbitalStability.lean) treat an explicitly sufficient mass regime in two spatial dimensions. **Open fork:** Identify what happens at and beyond the proven sufficient bound, without assuming the bound is sharp. **First test:** For frozen coefficients, construct an admissible energy comparison near the boundary or prove a larger valid mass interval. **Status:** Candidate extension; proven in-range results preserved.

---

## Reusable entry template

```markdown
## NNN · Working title
**Related GC:** GCxx or none
**Observation or motivation:**
**Exact candidate equation/model:**
**Question or conjectural statement:**
**Fastest possible counterexample and what it would exclude:**
**Constructive theorem or alternative formulation to test:**
**Existing exact-scope theorem or counterexample, if any:**
**What is *not* established by that result:**
**Closest known results to check:**
**First proof milestone:**
**Status:** Candidate / refuted / superseded / promoted
**Contributor and date:**
```

To promote an entry, follow [METHOD.md](METHOD.md) and add a dated literature and counterexample record. Preserve rejected candidates; correcting an incorrect idea is valid progress.
