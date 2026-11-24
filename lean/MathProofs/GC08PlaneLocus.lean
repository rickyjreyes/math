import MathProofs.GC08Cartesian

/-!
# GC08: polynomial characterization of nonvanishing plane-wave jets

The equations do not divide by amplitude. Division by rho occurs only in
the constructive converse proof, where the value is nonzero.
-/
noncomputable section
namespace ReyesMath.GC08

def phaseMomentum {d : ℕ} (J : Jet d) (i : Fin d) : ℝ :=
  J.a*J.q i-J.b*J.p i

/-- Polynomial constraints for the nonzero plane-wave locus. At nodes these
equations alone do not characterize its closure. -/
def PlaneEquations {d : ℕ} (J : Jet d) : Prop :=
  (∀ i, J.a*J.p i+J.b*J.q i=0) ∧
  (∀ i j, rho J^2*J.A i j = -J.a*phaseMomentum J i*phaseMomentum J j) ∧
  (∀ i j, rho J^2*J.B i j = -J.b*phaseMomentum J i*phaseMomentum J j)

theorem plane_equations {d : ℕ} (a b : ℝ) (k : Fin d → ℝ) :
    PlaneEquations (plane a b k) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    simp only [plane]
    ring
  · intro i j
    simp only [plane,rho,phaseMomentum]
    ring
  · intro i j
    simp only [plane,rho,phaseMomentum]
    ring

/-- A nonvanishing Cartesian jet is a plane-wave jet exactly when these
polynomial equations hold. This is a necessary-and-sufficient converse,
not merely evaluation of the constraints on plane waves. -/
theorem plane_iff_equations {d : ℕ} (J : Jet d) (hn : J.a ≠ 0 ∨ J.b ≠ 0) :
    (∃ k : Fin d → ℝ, J=plane J.a J.b k) ↔ PlaneEquations J := by
  constructor
  · rintro ⟨k,hk⟩
    have h := plane_equations J.a J.b k
    rw [← hk] at h
    exact h
  · intro h
    obtain ⟨hg,hA,hB⟩ := h
    have hr : 0 < rho J := by
      unfold rho
      rcases hn with ha | hb
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg _)
      · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hb)
    let k : Fin d → ℝ := fun i => phaseMomentum J i/rho J
    refine ⟨k,?_⟩
    have hp : J.p = fun i => -J.b*k i := by
      funext i
      dsimp [k]
      field_simp [hr.ne']
      unfold rho phaseMomentum
      linear_combination J.a*(hg i)
    have hq : J.q = fun i => J.a*k i := by
      funext i
      dsimp [k]
      field_simp [hr.ne']
      unfold rho phaseMomentum
      linear_combination J.b*(hg i)
    have hAA : J.A = fun i j => -J.a*k i*k j := by
      funext i j
      dsimp [k]
      field_simp [hr.ne'] <;> nlinarith only [hA i j]
    have hBB : J.B = fun i j => -J.b*k i*k j := by
      funext i j
      dsimp [k]
      field_simp [hr.ne'] <;> nlinarith only [hB i j]
    cases J
    simp only [plane] at *
    congr <;> assumption

end ReyesMath.GC08

#print axioms ReyesMath.GC08.plane_iff_equations
