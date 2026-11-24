import Mathlib

/-!
# GC08: Cartesian phase-current divergence

Candidate algebraic core for the original GC08 operator, NOT M6B.
Real coordinates of complex second-order jets; the analytical field/jet
correspondence, smooth invariant factorization and extension theorem are
recorded separately in docs/GC08_CARTESIAN_CLASSIFICATION_2026-11-24.md.
This module does not yet kernel-certify those analytic arguments.
-/

noncomputable section
namespace ReyesMath.GC08

structure Jet (d : ℕ) where
  a : ℝ
  b : ℝ
  p : Fin d → ℝ
  q : Fin d → ℝ
  A : Fin d → Fin d → ℝ
  B : Fin d → Fin d → ℝ

def rho {d : ℕ} (J : Jet d) : ℝ := J.a ^ 2 + J.b ^ 2

def phaseTrace {d : ℕ} (J : Jet d) : ℝ :=
  ∑ i : Fin d, (J.a * J.B i i - J.b * J.A i i)

def mix {d : ℕ} (J : Jet d) : ℝ :=
  ∑ i : Fin d, (J.a * J.p i + J.b * J.q i) * (J.a * J.q i - J.b * J.p i)

/-- Product/quotient-rule Cartesian expression of GC08 on symmetric jets. -/
def curvature {d : ℕ} (ε : ℝ) (J : Jet d) : ℝ :=
  phaseTrace J / (ε + rho J) - 2 * mix J / (ε + rho J) ^ 2

def densityLaplacian {d : ℕ} (J : Jet d) : ℝ :=
  2 * ∑ i : Fin d, (J.p i ^ 2 + J.q i ^ 2 + J.a * J.A i i + J.b * J.B i i)

def closure {d : ℕ} (ε lam : ℝ) (J : Jet d) : ℝ :=
  curvature ε J + lam * densityLaplacian J

def plane {d : ℕ} (a b : ℝ) (k : Fin d → ℝ) : Jet d :=
  ⟨a, b, fun i => -b * k i, fun i => a * k i,
    fun i j => -a * k i * k j, fun i j => -b * k i * k j⟩

theorem denominator_pos {d : ℕ} {ε : ℝ} (he : 0 < ε) (J : Jet d) :
    0 < ε + rho J := by
  unfold rho
  positivity

theorem curvature_at_zero {d : ℕ} (ε : ℝ) (J : Jet d)
    (ha : J.a = 0) (hb : J.b = 0) : curvature ε J = 0 := by
  simp [curvature, phaseTrace, mix, ha, hb]

theorem plane_trace {d : ℕ} (a b : ℝ) (k : Fin d → ℝ) :
    phaseTrace (plane a b k) = 0 := by
  unfold phaseTrace
  apply Finset.sum_eq_zero
  intro i _
  simp only [plane]
  ring

theorem plane_mix {d : ℕ} (a b : ℝ) (k : Fin d → ℝ) :
    mix (plane a b k) = 0 := by
  unfold mix
  apply Finset.sum_eq_zero
  intro i _
  simp only [plane]
  ring

theorem curvature_plane {d : ℕ} (ε a b : ℝ) (k : Fin d → ℝ) :
    curvature ε (plane a b k) = 0 := by
  simp [curvature, plane_trace, plane_mix]

theorem densityLaplacian_plane {d : ℕ} (a b : ℝ) (k : Fin d → ℝ) :
    densityLaplacian (plane a b k) = 0 := by
  have h : (∑ i : Fin d, ((plane a b k).p i ^ 2 + (plane a b k).q i ^ 2 +
      (plane a b k).a * (plane a b k).A i i +
      (plane a b k).b * (plane a b k).B i i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [plane]
    ring
  simp [densityLaplacian, h]

theorem closure_plane {d : ℕ} (ε lam a b : ℝ) (k : Fin d → ℝ) :
    closure ε lam (plane a b k) = 0 := by
  simp [closure, curvature_plane, densityLaplacian_plane]

/-- The jet at zero of the real affine field 1+x_1 on R². -/
def affineWitness : Jet 2 :=
  ⟨1, 0, fun i => if i = 0 then 1 else 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩

theorem witness_densityLaplacian : densityLaplacian affineWitness = 2 := by
  norm_num [densityLaplacian, affineWitness, Fin.sum_univ_two]

theorem closure_family_distinct (ε lam mu : ℝ) (hne : lam ≠ mu) :
    closure ε lam affineWitness ≠ closure ε mu affineWitness := by
  intro h
  unfold closure at h
  rw [witness_densityLaplacian] at h
  apply hne
  linarith

/-- Polar jet scalar form: p=grad log r, q=grad theta, B=Hess theta. -/
def polarK (ε r trB pq : ℝ) : ℝ :=
  r ^ 2 / (ε + r ^ 2) * trB + 2 * ε * r ^ 2 / (ε + r ^ 2) ^ 2 * pq

/-- Algebraic phase-response law for the polar expression. -/
theorem polar_response (ε r trB pq trW pv : ℝ) :
    polarK ε r (trB + trW) (pq + pv) =
      polarK ε r trB pq + polarK ε r trW pv := by
  unfold polarK
  ring

/-- A response law and zero response on the constant-phase slice determine
the scalar dependence on the two phase slots. This is only the algebraic
uniqueness core, not a formal field-level gauge theorem. -/
theorem polar_scalar_unique (ε r : ℝ) (C : ℝ → ℝ → ℝ)
    (hz : C 0 0 = 0)
    (hshift : ∀ b q w v, C (b + w) (q + v) = C b q + polarK ε r w v) :
    ∀ b q, C b q = polarK ε r b q := by
  intro b q
  simpa [hz] using hshift 0 0 b q

end ReyesMath.GC08

#print axioms ReyesMath.GC08.curvature_at_zero
#print axioms ReyesMath.GC08.closure_plane
#print axioms ReyesMath.GC08.closure_family_distinct
#print axioms ReyesMath.GC08.polar_scalar_unique
