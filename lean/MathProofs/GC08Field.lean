import MathProofs.GC08Cartesian

/-!
# GC08: actual continuum current divergence

The derivative is taken along Cartesian coordinate lines, not over a
discrete grid. The only analytic hypotheses are the ordinary first and
second directional derivatives of the real and imaginary field components.
-/
noncomputable section
namespace ReyesMath.GC08
open scoped BigOperators

/-- The actual scalar current along a coordinate line. -/
def lineCurrent (ε : ℝ) (a b : ℝ → ℝ) (t : ℝ) : ℝ :=
  (a t * deriv b t - b t * deriv a t)/(ε + a t ^ 2 + b t ^ 2)

/-- Product/quotient rule for the original normalized phase current. -/
theorem lineCurrent_deriv (ε : ℝ) (he : 0 < ε) (a b : ℝ → ℝ) (t p q A B : ℝ)
    (ha : HasDerivAt a p t) (hb : HasDerivAt b q t)
    (hA : HasDerivAt (deriv a) A t) (hB : HasDerivAt (deriv b) B t) :
    deriv (lineCurrent ε a b) t =
      (a t*B-b t*A)/(ε+a t^2+b t^2) -
      2*((a t*p+b t*q)*(a t*q-b t*p))/(ε+a t^2+b t^2)^2 := by
  have hn := (ha.mul hB).sub (hb.mul hA)
  have hd := ((hasDerivAt_const t ε).add (ha.pow 2)).add (hb.pow 2)
  have hp : 0 < ε+a t^2+b t^2 := by positivity
  have h := (hn.div hd hp.ne').deriv
  change deriv (lineCurrent ε a b) t = _ at h
  rw [h, ha.deriv, hb.deriv]
  field_simp [hp.ne'] <;> ring

/-- A coordinate line parameterized from its given base point. -/
def line {d : ℕ} (x : Fin d → ℝ) (i : Fin d) (t : ℝ) : Fin d → ℝ :=
  fun j => x j + if j=i then t else 0

theorem line_zero {d : ℕ} (x : Fin d → ℝ) (i : Fin d) : line x i 0=x := by
  funext j
  simp [line]

/-- First and second partials of the actual coordinate-line restriction. -/
def part {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin d) : ℝ :=
  deriv (fun t => f (line x i t)) 0

def secondPart {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin d) : ℝ :=
  deriv (deriv (fun t => f (line x i t))) 0

/-- Original GC08 operator: coordinate divergence of the normalized current
of a complex field, expressed using its two real components. -/
def fieldCurvature {d : ℕ} (ε : ℝ) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, deriv (lineCurrent ε (fun t => (u (line x i t)).re)
    (fun t => (u (line x i t)).im)) 0

/-- The exact diagonal derivative slots of the continuum field.
Off-diagonal slots are immaterial to this scalar operator. -/
def diagonalJet {d : ℕ} (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : Jet d :=
  ⟨(u x).re,(u x).im,
   part (fun y => (u y).re) x, part (fun y => (u y).im) x,
   fun i j => if i=j then secondPart (fun y => (u y).re) x i else 0,
   fun i j => if i=j then secondPart (fun y => (u y).im) x i else 0⟩

/-- Actual C² coordinate-line hypotheses; not hypotheses about the GC08
formula or a stipulated value of the divergence. -/
def LineRegular {d : ℕ} (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : Prop :=
  ∀ i : Fin d,
    DifferentiableAt ℝ (fun t : ℝ => (u (line x i t)).re) 0 ∧
    DifferentiableAt ℝ (fun t : ℝ => (u (line x i t)).im) 0 ∧
    DifferentiableAt ℝ (deriv (fun t : ℝ => (u (line x i t)).re)) 0 ∧
    DifferentiableAt ℝ (deriv (fun t : ℝ => (u (line x i t)).im)) 0

theorem fieldCurvature_eq_cartesian {d : ℕ} (ε : ℝ) (he : 0 < ε)
    (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) (h : LineRegular u x) :
    fieldCurvature ε u x = curvature ε (diagonalJet u x) := by
  have hsum : ∀ i : Fin d,
      deriv (lineCurrent ε (fun t => (u (line x i t)).re)
        (fun t => (u (line x i t)).im)) 0 =
      ((diagonalJet u x).a*(diagonalJet u x).B i i -
        (diagonalJet u x).b*(diagonalJet u x).A i i)/(ε+rho (diagonalJet u x)) -
      2*(((diagonalJet u x).a*(diagonalJet u x).p i+
        (diagonalJet u x).b*(diagonalJet u x).q i)*
        ((diagonalJet u x).a*(diagonalJet u x).q i-
        (diagonalJet u x).b*(diagonalJet u x).p i))/(ε+rho (diagonalJet u x))^2 := by
    intro i
    obtain ⟨ha,hb,hA,hB⟩ := h i
    have hc := lineCurrent_deriv ε he _ _ 0 _ _ _ _
      ha.hasDerivAt hb.hasDerivAt hA.hasDerivAt hB.hasDerivAt
    simpa only [diagonalJet, part, secondPart, rho, line_zero, if_pos rfl, add_assoc] using hc
  unfold fieldCurvature curvature phaseTrace mix
  rw [Finset.sum_div, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact hsum i

/-- At any actual zero of a field satisfying the ordinary directional C²
hypotheses, its original GC08 divergence vanishes. -/
theorem fieldCurvature_at_zero {d : ℕ} (ε : ℝ) (he : 0 < ε)
    (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) (h : LineRegular u x)
    (hz : u x=0) : fieldCurvature ε u x=0 := by
  rw [fieldCurvature_eq_cartesian ε he u x h]
  apply curvature_at_zero
  · simp [diagonalJet,hz]
  · simp [diagonalJet,hz]

/-- Actual density Laplacian along Cartesian lines. -/
def fieldDensityLaplacian {d : ℕ} (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, secondPart (fun y => (u y).re^2+(u y).im^2) x i

def fieldClosure {d : ℕ} (ε lam : ℝ) (u : (Fin d → ℝ) → ℂ)
    (x : Fin d → ℝ) : ℝ :=
  fieldCurvature ε u x + lam * fieldDensityLaplacian u x

/-- A genuine smooth affine complex field (with zero imaginary part). -/
def affineField (x : Fin 2 → ℝ) : ℂ := Complex.mk (1+x 0) 0

theorem affineField_smooth : ContDiff ℝ ⊤ affineField := by
  have h : ContDiff ℝ ⊤ (fun x : Fin 2 → ℝ => (1+x 0, (0 : ℝ))) := by
    fun_prop
  exact Complex.equivRealProdCLM.symm.contDiff.comp h

private theorem deriv_affine_square (t : ℝ) :
    deriv (fun s : ℝ => (1+s)^2) t=2*(1+t) := by
  have h := ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).pow 2
  convert h.deriv using 1 <;> ring

private theorem second_affine_square :
    deriv (deriv (fun s : ℝ => (1+s)^2)) 0=2 := by
  have hf : deriv (fun s : ℝ => (1+s)^2) = fun t => 2*(1+t) := by
    funext t
    exact deriv_affine_square t
  rw [hf]
  have h := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
    (hasDerivAt_id (0 : ℝ))).const_mul (2 : ℝ)
  convert h.deriv using 1 <;> ring

theorem affineField_densityLaplacian :
    fieldDensityLaplacian affineField 0=2 := by
  unfold fieldDensityLaplacian
  rw [Fin.sum_univ_two]
  have h0 : (fun t : ℝ => (affineField (line 0 0 t)).re^2+
      (affineField (line 0 0 t)).im^2) = fun t => (1+t)^2 := by
    funext t
    simp [affineField,line]
  have h1 : (fun t : ℝ => (affineField (line 0 1 t)).re^2+
      (affineField (line 0 1 t)).im^2) = fun _ => (1 : ℝ) := by
    funext t
    norm_num [affineField,line]
  unfold secondPart
  rw [h0,h1,second_affine_square]
  simp

/-- Pairwise distinct closures on one actual smooth field, not merely a
postulated jet. This witness does not require computing its common K term. -/
theorem field_closure_family_distinct (ε lam mu : ℝ) (hne : lam ≠ mu) :
    ∃ (u : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ),
      ContDiff ℝ ⊤ u ∧ fieldClosure ε lam u x ≠ fieldClosure ε mu u x := by
  refine ⟨affineField,0,affineField_smooth,?_⟩
  intro h
  unfold fieldClosure at h
  rw [affineField_densityLaplacian] at h
  apply hne
  linarith

end ReyesMath.GC08

#print axioms ReyesMath.GC08.lineCurrent_deriv
#print axioms ReyesMath.GC08.fieldCurvature_eq_cartesian
#print axioms ReyesMath.GC08.fieldCurvature_at_zero

#print axioms ReyesMath.GC08.field_closure_family_distinct
