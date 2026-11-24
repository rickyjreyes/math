import MathProofs.GC08Gauge

/-!
# GC08: orthogonal spatial invariance on raw Cartesian jets

The contraction identities are valid for all orthogonal matrices, hence
also for the required proper rotations. No orientation reversal axiom
is imposed on arbitrary admissible closures.
-/
noncomputable section
namespace ReyesMath.GC08
open scoped BigOperators

def Orthogonal {d : ℕ} (R : Fin d → Fin d → ℝ) : Prop :=
  ∀ j k, (∑ i : Fin d, R i j*R i k) = if j=k then 1 else 0

def mv {d : ℕ} (R : Fin d → Fin d → ℝ) (v : Fin d → ℝ) (i : Fin d) : ℝ :=
  ∑ j : Fin d, R i j*v j

def mt {d : ℕ} (R M : Fin d → Fin d → ℝ) (i l : Fin d) : ℝ :=
  ∑ j : Fin d, ∑ k : Fin d, R i j*R l k*M j k

def spatial {d : ℕ} (R : Fin d → Fin d → ℝ) (J : Jet d) : Jet d :=
  ⟨J.a,J.b,mv R J.p,mv R J.q,mt R J.A,mt R J.B⟩

private theorem double_contract {d : ℕ} (R M : Fin d → Fin d → ℝ)
    (hR : Orthogonal R) :
    (∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, R i j*R i k*M j k) =
      ∑ j : Fin d, M j j := by
  calc
    _ = ∑ j : Fin d, ∑ k : Fin d, ∑ i : Fin d, R i j*R i k*M j k := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ j : Fin d, ∑ k : Fin d, (if j=k then 1 else 0)*M j k := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_mul,hR j k]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simp [ite_mul]

theorem trace_mt {d : ℕ} (R M : Fin d → Fin d → ℝ) (hR : Orthogonal R) :
    (∑ i : Fin d, mt R M i i) = ∑ i : Fin d, M i i := by
  exact double_contract R M hR

def dot {d : ℕ} (p q : Fin d → ℝ) : ℝ := ∑ i : Fin d, p i*q i

theorem dot_mv {d : ℕ} (R : Fin d → Fin d → ℝ) (hR : Orthogonal R)
    (p q : Fin d → ℝ) : dot (mv R p) (mv R q)=dot p q := by
  unfold dot
  calc
    _ = ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, R i j*R i k*(p j*q k) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold mv
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := double_contract R (fun j k => p j*q k) hR

private theorem mv_lin {d : ℕ} (R : Fin d → Fin d → ℝ) (p q : Fin d → ℝ)
    (a b : ℝ) :
    (fun i => a*mv R p i+b*mv R q i)=mv R (fun i => a*p i+b*q i) := by
  funext i
  unfold mv
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem mv_lin_sub {d : ℕ} (R : Fin d → Fin d → ℝ) (p q : Fin d → ℝ)
    (a b : ℝ) :
    (fun i => a*mv R p i-b*mv R q i)=mv R (fun i => a*p i-b*q i) := by
  funext i
  unfold mv
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem phaseTrace_spatial {d : ℕ} (R : Fin d → Fin d → ℝ) (hR : Orthogonal R)
    (J : Jet d) : phaseTrace (spatial R J)=phaseTrace J := by
  simp only [phaseTrace,spatial,Finset.sum_sub_distrib,← Finset.mul_sum,trace_mt R _ hR]

theorem mix_spatial {d : ℕ} (R : Fin d → Fin d → ℝ) (hR : Orthogonal R)
    (J : Jet d) : mix (spatial R J)=mix J := by
  change dot (fun i => J.a*mv R J.p i+J.b*mv R J.q i)
    (fun i => J.a*mv R J.q i-J.b*mv R J.p i) =
      dot (fun i => J.a*J.p i+J.b*J.q i) (fun i => J.a*J.q i-J.b*J.p i)
  rw [mv_lin,mv_lin_sub,dot_mv R hR]

theorem curvature_spatial {d : ℕ} (ε : ℝ) (R : Fin d → Fin d → ℝ)
    (hR : Orthogonal R) (J : Jet d) : curvature ε (spatial R J)=curvature ε J := by
  have hr : rho (spatial R J)=rho J := rfl
  simp only [curvature,phaseTrace_spatial R hR,mix_spatial R hR,hr]

theorem densityLaplacian_spatial {d : ℕ} (R : Fin d → Fin d → ℝ)
    (hR : Orthogonal R) (J : Jet d) :
    densityLaplacian (spatial R J)=densityLaplacian J := by
  have hsq : ∀ v : Fin d → ℝ, (∑ i : Fin d, mv R v i^2)=∑ i : Fin d, v i^2 := by
    intro v
    simpa only [dot,pow_two] using dot_mv R hR v v
  simp only [densityLaplacian,spatial,Finset.sum_add_distrib,← Finset.mul_sum,hsq,trace_mt R _ hR]

theorem densityLaplacian_rotate {d : ℕ} (J : Jet d) (c s : ℝ)
    (h : c^2+s^2=1) : densityLaplacian (rotate c s J)=densityLaplacian J := by
  unfold densityLaplacian
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [rotate]
  linear_combination (J.p i^2+J.q i^2+J.a*J.A i i+J.b*J.B i i)*h

theorem closure_spatial {d : ℕ} (ε lam : ℝ) (R : Fin d → Fin d → ℝ)
    (hR : Orthogonal R) (J : Jet d) : closure ε lam (spatial R J)=closure ε lam J := by
  simp only [closure,curvature_spatial ε R hR,densityLaplacian_spatial R hR]

theorem closure_rotate {d : ℕ} (ε lam : ℝ) (J : Jet d) (c s : ℝ)
    (h : c^2+s^2=1) : closure ε lam (rotate c s J)=closure ε lam J := by
  simp only [closure,curvature_rotate ε J c s h,densityLaplacian_rotate J c s h]

end ReyesMath.GC08

#print axioms ReyesMath.GC08.curvature_spatial
#print axioms ReyesMath.GC08.closure_spatial
#print axioms ReyesMath.GC08.closure_rotate
