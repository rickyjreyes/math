import MathProofs.GC08Cartesian

/-!
# GC08: exact local phase action and conditional uniqueness on Cartesian jets

The gauge jet is the product-rule action of exp(i phi), with phi=0 at the
base point, grad phi=v and Hess phi=W. A constant phase is handled separately.
The uniqueness proof works on raw jets, not on the earlier scalar polar proxy.
Smooth field correspondence is a separate obligation.
-/
noncomputable section
namespace ReyesMath.GC08
open scoped BigOperators

def rotate {d : ℕ} (c s : ℝ) (J : Jet d) : Jet d :=
  ⟨c*J.a-s*J.b, s*J.a+c*J.b,
   fun i => c*J.p i-s*J.q i, fun i => s*J.p i+c*J.q i,
   fun i j => c*J.A i j-s*J.B i j, fun i j => s*J.A i j+c*J.B i j⟩

def gauge {d : ℕ} (J : Jet d) (v : Fin d → ℝ) (W : Fin d → Fin d → ℝ) : Jet d :=
  ⟨J.a, J.b, fun i => J.p i-J.b*v i, fun i => J.q i+J.a*v i,
   fun i j => J.A i j-J.q i*v j-J.q j*v i-J.a*v i*v j-J.b*W i j,
   fun i j => J.B i j+J.p i*v j+J.p j*v i-J.b*v i*v j+J.a*W i j⟩

/-- The divergence of rho/(epsilon+rho) times grad phi, in actual jet slots. -/
def response {d : ℕ} (ε : ℝ) (J : Jet d) (v : Fin d → ℝ)
    (W : Fin d → Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (rho J * W i i / (ε + rho J) +
    2 * ε * (J.a*J.p i+J.b*J.q i)*v i / (ε+rho J)^2)

private def term {d : ℕ} (ε : ℝ) (J : Jet d) (i : Fin d) : ℝ :=
  (J.a*J.B i i-J.b*J.A i i)/(ε+rho J) -
    2*((J.a*J.p i+J.b*J.q i)*(J.a*J.q i-J.b*J.p i))/(ε+rho J)^2

private theorem curvature_sum {d : ℕ} (ε : ℝ) (J : Jet d) :
    curvature ε J = ∑ i : Fin d, term ε J i := by
  simp only [curvature, phaseTrace, mix, term, Finset.sum_div,
    Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem rho_rotate {d : ℕ} (J : Jet d) (c s : ℝ) (h : c^2+s^2=1) :
    rho (rotate c s J) = rho J := by
  unfold rho rotate
  change (c*J.a-s*J.b)^2+(s*J.a+c*J.b)^2 = J.a^2+J.b^2
  linear_combination (J.a^2+J.b^2)*h

theorem curvature_rotate {d : ℕ} (ε : ℝ) (J : Jet d) (c s : ℝ)
    (h : c^2+s^2=1) : curvature ε (rotate c s J) = curvature ε J := by
  rw [curvature_sum, curvature_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold term
  rw [rho_rotate J c s h]
  have h1 : (rotate c s J).a*(rotate c s J).B i i -
      (rotate c s J).b*(rotate c s J).A i i = J.a*J.B i i-J.b*J.A i i := by
    simp only [rotate]
    linear_combination (J.a*J.B i i-J.b*J.A i i)*h
  have h2 : (rotate c s J).a*(rotate c s J).p i +
      (rotate c s J).b*(rotate c s J).q i = J.a*J.p i+J.b*J.q i := by
    simp only [rotate]
    linear_combination (J.a*J.p i+J.b*J.q i)*h
  have h3 : (rotate c s J).a*(rotate c s J).q i -
      (rotate c s J).b*(rotate c s J).p i = J.a*J.q i-J.b*J.p i := by
    simp only [rotate]
    linear_combination (J.a*J.q i-J.b*J.p i)*h
  rw [h1,h2,h3]

theorem curvature_gauge {d : ℕ} (ε : ℝ) (he : 0 < ε) (J : Jet d)
    (v : Fin d → ℝ) (W : Fin d → Fin d → ℝ) :
    curvature ε (gauge J v W) = curvature ε J + response ε J v W := by
  rw [curvature_sum, curvature_sum]
  unfold response
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hd := (denominator_pos he J).ne'
  have hρ : rho (gauge J v W) = rho J := rfl
  unfold term
  rw [hρ]
  simp only [gauge]
  unfold rho at hd ⊢
  field_simp [hd] <;> ring

/-- Real Cartesian jets have all imaginary components zero. -/
def RealJet {d : ℕ} (J : Jet d) : Prop :=
  J.b = 0 ∧ (∀ i, J.q i = 0) ∧ (∀ i j, J.B i j = 0)

theorem curvature_real {d : ℕ} (ε : ℝ) (J : Jet d)
    (h : RealJet J) : curvature ε J = 0 := by
  obtain ⟨hb,hq,hB⟩ := h
  simp [curvature, phaseTrace, mix, hb, hq, hB]

/-- Every nonzero-value jet has a constant and local phase taking it to
a real jet. Explicit coefficients; no amplitude-zero division is used. -/
theorem exists_real_gauge {d : ℕ} (J : Jet d) (hn : J.a ≠ 0 ∨ J.b ≠ 0) :
    ∃ c s : ℝ, c^2+s^2=1 ∧ ∃ (v : Fin d → ℝ) (W : Fin d → Fin d → ℝ),
      RealJet (gauge (rotate c s J) v W) := by
  have hp : 0 < J.a^2+J.b^2 := by
    rcases hn with ha | hb
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hb)
  let r := Real.sqrt (J.a^2+J.b^2)
  have hr : 0 < r := Real.sqrt_pos.2 hp
  have hr2 : r^2 = J.a^2+J.b^2 := Real.sq_sqrt hp.le
  let c := J.a/r
  let s := -J.b/r
  have hu : c^2+s^2=1 := by
    dsimp [c,s]
    field_simp [hr.ne'] <;> nlinarith [hr2]
  let L := rotate c s J
  have hLa : L.a = r := by
    change c*J.a-s*J.b=r
    dsimp [c,s]
    field_simp [hr.ne'] <;> nlinarith [hr2]
  have hLb : L.b = 0 := by
    change s*J.a+c*J.b=0
    dsimp [c,s]
    field_simp [hr.ne'] <;> ring
  let v : Fin d → ℝ := fun i => -L.q i/r
  let W : Fin d → Fin d → ℝ := fun i j =>
    -(L.B i j+L.p i*v j+L.p j*v i)/r
  refine ⟨c,s,hu,v,W,?_⟩
  refine ⟨hLb,?_,?_⟩
  · intro i
    change L.q i+L.a*v i=0
    rw [hLa]
    dsimp [v]
    field_simp [hr.ne'] <;> ring
  · intro i j
    change L.B i j+L.p i*v j+L.p j*v i-L.b*v i*v j+L.a*W i j=0
    rw [hLa,hLb]
    dsimp [W]
    field_simp [hr.ne'] <;> ring

/-- The exact two phase axioms imply uniqueness at each nonzero raw jet. -/
theorem unique_nonzero {d : ℕ} (ε : ℝ) (he : 0 < ε) (C : Jet d → ℝ)
    (hrot : ∀ J c s, c^2+s^2=1 → C (rotate c s J)=C J)
    (hg : ∀ J v W, C (gauge J v W)=C J+response ε J v W)
    (hreal : ∀ J, RealJet J → C J=0)
    (J : Jet d) (hn : J.a ≠ 0 ∨ J.b ≠ 0) : C J=curvature ε J := by
  obtain ⟨c,s,hu,v,W,hR⟩ := exists_real_gauge J hn
  have hC := hreal _ hR
  have hK := curvature_real ε _ hR
  rw [hg, hrot J c s hu] at hC
  rw [curvature_gauge ε he, curvature_rotate ε J c s hu] at hK
  linarith

/-- Elementary removable-value lemma using only continuity at zero. -/
private theorem zero_of_continuous_off_zero (f : ℝ → ℝ)
    (hc : ContinuousAt f 0) (hz : ∀ t, t ≠ 0 → f t = 0) : f 0 = 0 := by
  by_contra h
  have hp : 0 < |f 0| := abs_pos.mpr h
  obtain ⟨δ,hδ,hd⟩ := (Metric.continuousAt_iff.mp hc) _ hp
  have ht : 0 < δ/2 := by linarith
  have hx : dist (δ/2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    linarith
  have hy := hd hx
  rw [hz _ ht.ne', Real.dist_eq, zero_sub, abs_neg] at hy
  exact (lt_irrefl _ hy)

/-- Global Cartesian uniqueness including every nodal jet. Line continuity
of the difference is weaker than the original globally smooth assumption. -/
theorem unique_all_jets {d : ℕ} (ε : ℝ) (he : 0 < ε) (C : Jet d → ℝ)
    (hrot : ∀ J c s, c^2+s^2=1 → C (rotate c s J)=C J)
    (hg : ∀ J v W, C (gauge J v W)=C J+response ε J v W)
    (hreal : ∀ J, RealJet J → C J=0)
    (hcont : ∀ J : Jet d, ContinuousAt
      (fun t : ℝ => C {J with a := t} - curvature ε {J with a := t}) 0) :
    ∀ J, C J=curvature ε J := by
  intro J
  by_cases ha : J.a = 0
  · let f : ℝ → ℝ := fun t => C {J with a := t} - curvature ε {J with a := t}
    have hf : f 0 = 0 := zero_of_continuous_off_zero f (hcont J) (by
      intro t ht
      apply sub_eq_zero.mpr
      exact unique_nonzero ε he C hrot hg hreal _ (Or.inl ht))
    have hJ : {J with a := (0 : ℝ)} = J := by
      cases J
      simp_all
    apply sub_eq_zero.mp
    simpa only [f,hJ] using hf
  · exact unique_nonzero ε he C hrot hg hreal J (Or.inl ha)

/-- Precisely the symmetry restriction on second derivatives of C² fields. -/
def SymmetricJet {d : ℕ} (J : Jet d) : Prop :=
  (∀ i j, J.A i j = J.A j i) ∧ (∀ i j, J.B i j = J.B j i)

def SymmetricPhase {d : ℕ} (W : Fin d → Fin d → ℝ) : Prop :=
  ∀ i j, W i j = W j i

theorem rotate_symmetric {d : ℕ} (J : Jet d) (c s : ℝ)
    (h : SymmetricJet J) : SymmetricJet (rotate c s J) := by
  constructor <;> intro i j <;> simp only [rotate] <;> rw [h.1 i j, h.2 i j]

theorem gauge_symmetric {d : ℕ} (J : Jet d) (v : Fin d → ℝ)
    (W : Fin d → Fin d → ℝ) (h : SymmetricJet J) (hW : SymmetricPhase W) :
    SymmetricJet (gauge J v W) := by
  constructor
  · intro i j
    simp only [gauge]
    rw [h.1 i j, hW i j]
    ring
  · intro i j
    simp only [gauge]
    rw [h.2 i j, hW i j]
    ring

/-- Symmetrization of a successful phase Hessian preserves its ability to
remove the imaginary part when the original jet is symmetric. -/
theorem exists_real_symmetric_gauge {d : ℕ} (J : Jet d)
    (hJ : SymmetricJet J) (hn : J.a ≠ 0 ∨ J.b ≠ 0) :
    ∃ c s : ℝ, c^2+s^2=1 ∧ ∃ (v : Fin d → ℝ) (W : Fin d → Fin d → ℝ),
      SymmetricPhase W ∧ RealJet (gauge (rotate c s J) v W) := by
  obtain ⟨c,s,hu,v,W,hR⟩ := exists_real_gauge J hn
  let L := rotate c s J
  let V : Fin d → Fin d → ℝ := fun i j => (W i j+W j i)/2
  have hL : SymmetricJet L := rotate_symmetric J c s hJ
  have hV : SymmetricPhase V := by
    intro i j
    dsimp [V]
    ring
  refine ⟨c,s,hu,v,V,hV,?_⟩
  obtain ⟨hb,hq,hB⟩ := hR
  refine ⟨hb,hq,?_⟩
  intro i j
  have hij := hB i j
  have hji := hB j i
  change L.B i j+L.p i*v j+L.p j*v i-L.b*v i*v j+L.a*W i j=0 at hij
  change L.B j i+L.p j*v i+L.p i*v j-L.b*v j*v i+L.a*W j i=0 at hji
  rw [← hL.2 i j] at hji
  change L.B i j+L.p i*v j+L.p j*v i-L.b*v i*v j+L.a*V i j=0
  dsimp [V]
  linear_combination (hij+hji)/2

/-- Exact uniqueness on nonzero symmetric jets. No response or normalization
axiom is imposed on nonsymmetric, unrealizable Hessian coordinates. -/
theorem unique_symmetric_nonzero {d : ℕ} (ε : ℝ) (he : 0 < ε) (C : Jet d → ℝ)
    (hrot : ∀ J c s, SymmetricJet J → c^2+s^2=1 → C (rotate c s J)=C J)
    (hg : ∀ J v W, SymmetricJet J → SymmetricPhase W →
      C (gauge J v W)=C J+response ε J v W)
    (hreal : ∀ J, SymmetricJet J → RealJet J → C J=0)
    (J : Jet d) (hJ : SymmetricJet J) (hn : J.a ≠ 0 ∨ J.b ≠ 0) :
    C J=curvature ε J := by
  obtain ⟨c,s,hu,v,W,hW,hR⟩ := exists_real_symmetric_gauge J hJ hn
  have hL := rotate_symmetric J c s hJ
  have hG := gauge_symmetric (rotate c s J) v W hL hW
  have hC := hreal _ hG hR
  have hK := curvature_real ε _ hR
  rw [hg _ _ _ hL hW, hrot J c s hJ hu] at hC
  rw [curvature_gauge ε he, curvature_rotate ε J c s hu] at hK
  linarith

/-- Exact symmetric-jet uniqueness including nodes; continuity is required
only along the nodal value line, within the symmetric jet space. -/
theorem unique_symmetric_jets {d : ℕ} (ε : ℝ) (he : 0 < ε) (C : Jet d → ℝ)
    (hrot : ∀ J c s, SymmetricJet J → c^2+s^2=1 → C (rotate c s J)=C J)
    (hg : ∀ J v W, SymmetricJet J → SymmetricPhase W →
      C (gauge J v W)=C J+response ε J v W)
    (hreal : ∀ J, SymmetricJet J → RealJet J → C J=0)
    (hcont : ∀ J : Jet d, SymmetricJet J → ContinuousAt
      (fun t : ℝ => C {J with a := t} - curvature ε {J with a := t}) 0) :
    ∀ J, SymmetricJet J → C J=curvature ε J := by
  intro J hJ
  by_cases ha : J.a = 0
  · let f : ℝ → ℝ := fun t => C {J with a := t} - curvature ε {J with a := t}
    have hf : f 0 = 0 := zero_of_continuous_off_zero f (hcont J hJ) (by
      intro t ht
      apply sub_eq_zero.mpr
      exact unique_symmetric_nonzero ε he C hrot hg hreal _ hJ (Or.inl ht))
    have hJ0 : {J with a := (0 : ℝ)} = J := by
      cases J
      simp_all
    apply sub_eq_zero.mp
    simpa only [f,hJ0] using hf
  · exact unique_symmetric_nonzero ε he C hrot hg hreal J hJ (Or.inl ha)

end ReyesMath.GC08

#print axioms ReyesMath.GC08.curvature_rotate
#print axioms ReyesMath.GC08.curvature_gauge
#print axioms ReyesMath.GC08.exists_real_gauge
#print axioms ReyesMath.GC08.unique_all_jets

#print axioms ReyesMath.GC08.unique_symmetric_jets
