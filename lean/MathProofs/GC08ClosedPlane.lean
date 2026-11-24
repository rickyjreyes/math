import Mathlib

/-!
# GC08: exact closed plane-wave locus in complex Cartesian coordinates

A product type supplies the actual finite-dimensional topology. The
nonvanishing plane-wave set and its closure are distinguished, including
the rank-one nodal Hessian stratum. This is a candidate kernel proof.
-/
noncomputable section
namespace ReyesMath.GC08
open Set

abbrev ComplexJet (d : ℕ) :=
  ℂ × (Fin d → ℂ) × (Fin d → Fin d → ℂ)

def complexPlane {d : ℕ} (z : ℂ) (k : Fin d → ℝ) : ComplexJet d :=
  (z, fun i => Complex.I * z * (k i : ℂ),
    fun i j => -z * (k i : ℂ) * (k j : ℂ))

def planeSet (d : ℕ) : Set (ComplexJet d) :=
  {J | ∃ z : ℂ, z ≠ 0 ∧ ∃ k : Fin d → ℝ, J = complexPlane z k}

/-- The real scalar alignment equation for two complex numbers. -/
def aligned (c w : ℂ) : Prop := c.re*w.im-c.im*w.re=0

theorem aligned_real_multiple {c w : ℂ} (hc : c ≠ 0) (ha : aligned c w) :
    ∃ t : ℝ, w = c * (t : ℂ) := by
  unfold aligned at ha
  by_cases hcr : c.re = 0
  · have hci : c.im ≠ 0 := by
      intro h
      apply hc
      apply Complex.ext <;> simp [hcr,h]
    have hwr : w.re = 0 := by
      have h : c.im*w.re=0 := by rw [hcr] at ha; linarith
      exact (mul_eq_zero.mp h).resolve_left hci
    refine ⟨w.im/c.im,?_⟩
    apply Complex.ext
    · simp [Complex.mul_re,hcr,hwr]
    · simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
      field_simp [hci] <;> ring
  · refine ⟨w.re/c.re,?_⟩
    apply Complex.ext
    · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
      field_simp [hcr] <;> ring
    · simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
      field_simp [hcr] <;> linarith

/-- The polynomial test, including the symmetry required of true Hessians.
All equations are polynomial in the real and imaginary coordinates. -/
def closedEquations {d : ℕ} (J : ComplexJet d) : Prop :=
  (∀ i, J.1.re*(J.2.1 i).re+J.1.im*(J.2.1 i).im=0) ∧
  (∀ i j, J.1*J.2.2 i j=J.2.1 i*J.2.1 j) ∧
  (∀ i j k l, J.2.2 i j*J.2.2 k l=J.2.2 i l*J.2.2 k j) ∧
  (∀ i j k l, aligned (J.2.2 i j) (J.2.2 k l)) ∧
  (∀ i j, J.2.2 i j=J.2.2 j i)

theorem complexPlane_equations {d : ℕ} (z : ℂ) (k : Fin d → ℝ) :
    closedEquations (complexPlane z k) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    simp [complexPlane,Complex.mul_re,Complex.mul_im]
    ring
  · intro i j
    simp only [complexPlane]
    calc
      z * (-z * (k i : ℂ) * (k j : ℂ)) =
          Complex.I^2 * (z^2 * (k i : ℂ) * (k j : ℂ)) := by rw [Complex.I_sq]; ring
      _ = _ := by ring
  · intro i j l m
    simp only [complexPlane]
    ring
  · intro i j l m
    simp [aligned,complexPlane,Complex.mul_re,Complex.mul_im]
    ring
  · intro i j
    simp only [complexPlane]
    ring

private theorem nonzero_plane {d : ℕ} (J : ComplexJet d)
    (hz : J.1 ≠ 0) (h : closedEquations J) : J ∈ planeSet d := by
  obtain ⟨hg,hH,_,_,_⟩ := h
  let z := J.1
  have hr : 0 < z.re^2+z.im^2 := by
    by_contra h
    have hr0 : z.re^2+z.im^2 ≤ 0 := le_of_not_gt h
    have hre : z.re=0 := by
      by_contra hn
      linarith [sq_pos_of_ne_zero hn,sq_nonneg z.im]
    have him : z.im=0 := by
      by_contra hn
      linarith [sq_pos_of_ne_zero hn,sq_nonneg z.re]
    apply hz
    change z=0
    apply Complex.ext <;> simp [hre,him]
  let k : Fin d → ℝ := fun i =>
    (z.re*(J.2.1 i).im-z.im*(J.2.1 i).re)/(z.re^2+z.im^2)
  have hgrad : ∀ i, J.2.1 i=Complex.I*z*(k i : ℂ) := by
    intro i
    have he : z.re*(J.2.1 i).re+z.im*(J.2.1 i).im=0 := hg i
    apply Complex.ext
    · simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
        Complex.ofReal_re,Complex.ofReal_im]
      dsimp [k]
      field_simp [hr.ne'] <;> linear_combination z.re*he
    · simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
        Complex.ofReal_re,Complex.ofReal_im]
      dsimp [k]
      field_simp [hr.ne'] <;> linear_combination z.im*he
  have hhess : ∀ i j, J.2.2 i j = -z*(k i : ℂ)*(k j : ℂ) := by
    intro i j
    apply mul_left_cancel₀ (show z ≠ 0 from hz)
    change J.1*J.2.2 i j = _
    rw [hH i j,hgrad i,hgrad j]
    calc
      Complex.I*z*(k i : ℂ)*(Complex.I*z*(k j : ℂ)) =
          Complex.I^2*(z^2*(k i : ℂ)*(k j : ℂ)) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  refine ⟨z,hz,k,?_⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext i
      exact hgrad i
    · funext i j
      exact hhess i j

/-- Rank-one factorization of every nodal Hessian satisfying the polynomial
test. No division by the field value occurs. -/
theorem nodal_factorization {d : ℕ} (J : ComplexJet d)
    (hz : J.1=0) (h : closedEquations J) :
    (∀ i, J.2.1 i=0) ∧
      ∃ c : ℂ, c ≠ 0 ∧ ∃ v : Fin d → ℝ,
        ∀ i j, J.2.2 i j=c*(v i : ℂ)*(v j : ℂ) := by
  obtain ⟨_,hH,hminor,halign,hsym⟩ := h
  have hg : ∀ i, J.2.1 i=0 := by
    intro i
    have hh := hH i i
    rw [hz,zero_mul] at hh
    exact (mul_eq_zero.mp hh.symm).elim id id
  refine ⟨hg,?_⟩
  by_cases hzero : ∀ i j, J.2.2 i j=0
  · exact ⟨1,one_ne_zero,fun _ => 0,fun i j => by simp [hzero i j]⟩
  · have hdiag : ∃ i, J.2.2 i i ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hzero
      intro i j
      have hm := hminor i i j j
      rw [hn i,hn j,zero_mul,← hsym i j] at hm
      exact (mul_eq_zero.mp hm.symm).elim id id
    obtain ⟨i,hi⟩ := hdiag
    let c := J.2.2 i i
    have hv : ∀ j, ∃ t : ℝ, J.2.2 i j=c*(t : ℂ) :=
      fun j => aligned_real_multiple hi (halign i i i j)
    choose v hv using hv
    refine ⟨c,hi,v,?_⟩
    intro j k
    apply mul_left_cancel₀ hi
    change J.2.2 i i * J.2.2 j k = _
    rw [hminor i i j k,← hsym i j,hv k,hv j]
    ring

/-- A polynomial path through a nodal rank-one Hessian. Away from t=0 it
is a genuine nonzero plane-wave jet with wavevector v/t. -/
def nodalPath {d : ℕ} (c : ℂ) (v : Fin d → ℝ) (t : ℝ) : ComplexJet d :=
  (-c*(t : ℂ)^2,
   fun i => -Complex.I*c*(t : ℂ)*(v i : ℂ),
   fun i j => c*(v i : ℂ)*(v j : ℂ))

theorem nodalPath_continuous {d : ℕ} (c : ℂ) (v : Fin d → ℝ) :
    Continuous (nodalPath c v) := by
  unfold nodalPath
  fun_prop

theorem nodalPath_mem_plane {d : ℕ} (c : ℂ) (hc : c ≠ 0)
    (v : Fin d → ℝ) (t : ℝ) (ht : t ≠ 0) :
    nodalPath c v t ∈ planeSet d := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  refine ⟨-c*(t : ℂ)^2,mul_ne_zero (neg_ne_zero.mpr hc) (pow_ne_zero _ htC),
    fun i => v i/t,?_⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext i
      simp only [nodalPath,complexPlane,Complex.ofReal_div]
      field_simp [htC] <;> ring
    · funext i j
      simp only [nodalPath,complexPlane,Complex.ofReal_div]
      field_simp [htC] <;> ring

/-- Every polynomial-test nodal jet lies in the actual topological closure. -/
theorem nodal_mem_closure {d : ℕ} (J : ComplexJet d)
    (hz : J.1=0) (h : closedEquations J) :
    J ∈ closure (planeSet d) := by
  obtain ⟨hg,c,hc,v,hH⟩ := nodal_factorization J hz h
  have hJ : nodalPath c v 0=J := by
    apply Prod.ext
    · simp [nodalPath,hz]
    · apply Prod.ext
      · funext i
        simp [nodalPath,hg i]
      · funext i j
        exact (hH i j).symm
  rw [← hJ,Metric.mem_closure_iff]
  intro ε he
  obtain ⟨δ,hδ,hd⟩ :=
    (Metric.continuousAt_iff.mp (nodalPath_continuous c v).continuousAt) ε he
  have ht : 0 < δ/2 := by linarith
  have hdist : dist (δ/2) (0 : ℝ) < δ := by
    rw [Real.dist_eq,sub_zero,abs_of_pos ht]
    linarith
  refine ⟨nodalPath c v (δ/2),nodalPath_mem_plane c hc v _ ht.ne',?_⟩
  first | exact hd hdist | simpa [dist_comm] using hd hdist

/-- The polynomial set is closed in the actual finite-dimensional topology. -/
theorem closedEquations_isClosed (d : ℕ) :
    IsClosed {J : ComplexJet d | closedEquations J} := by
  have heq : {J : ComplexJet d | closedEquations J} =
      (⋂ i : Fin d, {J : ComplexJet d |
        J.1.re*(J.2.1 i).re+J.1.im*(J.2.1 i).im=0}) ∩
      ((⋂ i : Fin d, ⋂ j : Fin d, {J : ComplexJet d |
        J.1*J.2.2 i j=J.2.1 i*J.2.1 j}) ∩
      ((⋂ i : Fin d, ⋂ j : Fin d, ⋂ k : Fin d, ⋂ l : Fin d,
        {J : ComplexJet d | J.2.2 i j*J.2.2 k l=J.2.2 i l*J.2.2 k j}) ∩
      ((⋂ i : Fin d, ⋂ j : Fin d, ⋂ k : Fin d, ⋂ l : Fin d,
        {J : ComplexJet d | aligned (J.2.2 i j) (J.2.2 k l)}) ∩
      (⋂ i : Fin d, ⋂ j : Fin d, {J : ComplexJet d | J.2.2 i j=J.2.2 j i})))) := by
    ext J
    simp only [mem_setOf_eq,mem_inter_iff,mem_iInter,closedEquations]
  rw [heq]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))
  · apply isClosed_iInter
    intro i
    exact isClosed_eq (by fun_prop) continuous_const
  · apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    exact isClosed_eq (by fun_prop) (by fun_prop)
  · apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro k
    apply isClosed_iInter
    intro l
    exact isClosed_eq (by fun_prop) (by fun_prop)
  · apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro k
    apply isClosed_iInter
    intro l
    change IsClosed {J : ComplexJet d |
      (J.2.2 i j).re*(J.2.2 k l).im-(J.2.2 i j).im*(J.2.2 k l).re=0}
    exact isClosed_eq (by fun_prop) continuous_const
  · apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    exact isClosed_eq (by fun_prop) (by fun_prop)

/-- Necessary AND sufficient global polynomial characterization, in the
actual topological closure, including zero-amplitude fields. -/
theorem closed_plane_iff_equations {d : ℕ} (J : ComplexJet d) :
    J ∈ closure (planeSet d) ↔ closedEquations J := by
  constructor
  · intro hJ
    have hsub : planeSet d ⊆ {L : ComplexJet d | closedEquations L} := by
      rintro L ⟨z,_,k,rfl⟩
      exact complexPlane_equations z k
    exact closure_minimal hsub (closedEquations_isClosed d) hJ
  · intro h
    by_cases hz : J.1=0
    · exact nodal_mem_closure J hz h
    · exact subset_closure (nonzero_plane J hz h)

/-- Plane-wave calibration extends to the complete polynomial locus by
continuity, with no gauge or smooth invariant factorization hypothesis. -/
theorem vanishes_on_closed_plane {d : ℕ} (F : ComplexJet d → ℝ)
    (hF : Continuous F) (hp : ∀ J ∈ planeSet d, F J=0) :
    ∀ J, closedEquations J → F J=0 := by
  intro J hJ
  have hc : IsClosed {L : ComplexJet d | F L=0} :=
    isClosed_eq hF continuous_const
  exact closure_minimal hp hc ((closed_plane_iff_equations J).2 hJ)

end ReyesMath.GC08

#print axioms ReyesMath.GC08.nodal_factorization
#print axioms ReyesMath.GC08.closed_plane_iff_equations
#print axioms ReyesMath.GC08.vanishes_on_closed_plane
