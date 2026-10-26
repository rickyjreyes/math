import Mathlib
import MathProofs.ModelAlgebra

/-!
# S004 auxiliary-field Dirac bracket and canonical count

The auxiliary first-order real scalar coordinates are (X₁,X₂,V₁,V₂,
λ₁,λ₂), with 12 canonical phase coordinates. The four explicit primary
relations p_{λi}=0 and p_{Xi}-λ_i=0 form a nondegenerate canonical
constraint bracket. We formalize the invertible 4×4 Dirac pairing and
the associated arithmetic count under the absence of additional
constraints. Proving preservation of the primary constraints from the
*full S004 Hamiltonian* is still a distinct open obligation.
-/

namespace ReyesMath

/-- The canonical Poisson bracket of the four explicit auxiliary
constraints acts on constraint-coordinate variations through a
nondegenerate real skew map. -/
def s004DiracBracket (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![u 2, u 3, -u 0, -u 1]

/-- Its explicit inverse is minus the canonical symplectic pairing. -/
def s004DiracInverse (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-u 2, -u 3, u 0, u 1]

/-- The exact canonical constraint bracket has a two-sided inverse. -/
theorem s004_dirac_bracket_left_inverse (u : Fin 4 → ℝ) :
    s004DiracInverse (s004DiracBracket u) = u := by
  funext i
  fin_cases i <;> simp [s004DiracInverse, s004DiracBracket]

theorem s004_dirac_bracket_right_inverse (u : Fin 4 → ℝ) :
    s004DiracBracket (s004DiracInverse u) = u := by
  funext i
  fin_cases i <;> simp [s004DiracInverse, s004DiracBracket]

/-- There is no nonzero null direction of the four-constraint Dirac
bracket, so at this algebraic level all four are second class. -/
theorem s004_four_constraint_bracket_nondegenerate (u : Fin 4 → ℝ)
    (hu : s004DiracBracket u = 0) : u = 0 := by
  calc
    u = s004DiracInverse (s004DiracBracket u) :=
      (s004_dirac_bracket_left_inverse u).symm
    _ = s004DiracInverse 0 := by rw [hu]
    _ = 0 := by
      funext i
      fin_cases i <;> simp [s004DiracInverse]

/-- Counting a 12-dimensional canonical scalar auxiliary phase space
with four second-class and zero first-class constraints leaves exactly
eight physical phase dimensions and four real configuration DOF. -/
theorem s004_four_dof_arithmetic :
    (12 - 2 * 0 - 4 : ℕ) = 8 ∧
      (12 - 2 * 0 - 4 : ℕ) / 2 = 4 ∧
      4 - 2 = (2 : ℕ) := by
  norm_num

end ReyesMath
