import Mathlib
import MathProofs.V18MiddleDerivatives

/-!
# The complete 31-real-parameter frozen v18 observation map

This is the mathematical real-number analogue of the frozen historical
`SM_Spectrum/_terms_perfection_v18.py` at
`geometry_of_resonance` commit `5a4c58a4206005ad9d46ee2951069186490b01f1`.

The 31 coordinates are exactly 9 light coefficients, 7 middle
coefficients, 13 heavy coefficients, and two suppression parameters.
The 11 strictly positive-target observations are indexed
1,2,3,12,19,53,73,91,95,96,123.

It explicitly includes the source's max floor, exponential clipping,
power clipping, sector branching and special n=3 suppression.

Python/NumPy floating-point rounding and SciPy optimization are
*not* mathematical operations here; finite-decimal inputs are exact reals.
This is not a certified equivalence with arbitrary floating-point runs.

The model and its unclipped local derivatives are deliberately kept
separate from the trigonometric determinant enclosure. Encoding the
map does not alone establish its Jacobian has rank eleven.
-/

noncomputable section
namespace ReyesMath.V18Forward

abbrev Params := Fin 31 → ℝ

/-- Published decimal values of the 9+7+13 coefficients, with the two optimizer
coordinates supplied as real parameters. -/
def frozen (alpha epsilon : ℝ) : Params :=
  ![(0.3877 : ℝ), -2.3676, -8.2963, 6.8830, -1.7948,
    -8.6415, -6.1744, 0.9981, 0.0048,
    2241.1, 5.0632, 9.4062, 1.6469, 0.2092, 998.7, 0.2427,
    98949, 12795, -3.301, 9.039, 61635, -1.189, 17770,
    5.615, 8624, -1.264, 4.685, 896077, -952363,
    alpha, epsilon]

def clip (lo hi x : ℝ) : ℝ := max lo (min hi x)

/-- The n mod 3 parity/topological source coefficient. -/
def topo (n : ℕ) : ℝ :=
  (if n % 3 = 0 then (-1 : ℝ) else if n % 3 = 1 then 0 else 1) *
    (-1 : ℝ) ^ n

/-- Source light-sector mass before the floating-model floor. -/
def lightRaw (p : Params) (n : ℕ) : ℝ :=
  let x : ℝ := n
  let ratio := if n = 0 then 0 else x / (x + 1)
  let chirality := if n = 0 then (1 : ℝ) else x ^ 2
  let base :=
    p 0 * ratio + p 1 * topo n + p 2 * Real.log (1 + x) +
      p 3 * x ^ 2 + p 4 * x ^ 3 +
      p 5 * Real.exp (clip (-50) 50 (p 6 * x)) + p 7 / chirality
  let suppression := (1 + Real.exp (p 29 * (x - p 30)))⁻¹
  let preliminary := base * suppression
  (if n = 3 then preliminary * p 8 else preliminary)

def light (p : Params) (n : ℕ) : ℝ :=
  max (lightRaw p n) (1e-12 : ℝ)

/-- The analytic middle function in exactly the source coefficient order. -/
def middleRaw (p : Params) (n : ℕ) : ℝ :=
  p 14 + p 15 * (n : ℝ) ^ 2 + p 13 * Real.sin (p 11 * n) +
    p 9 * Real.sin (p 10 * n + p 12)

def middle (p : Params) (n : ℕ) : ℝ :=
  max (middleRaw p n) (1e-12 : ℝ)

/-- Heavy correction, including source power clipping and sector gates. -/
def heavyCorrection (p : Params) (n : ℕ) : ℝ :=
  let x : ℝ := n
  if 19 ≤ n ∧ n ≤ 73 then
    p 16 * (clip (1e-6) (1e6) (x / 50)) ^ (clip (-10) 10 (p 18))
  else if 91 ≤ n ∧ n ≤ 123 then
    p 17 * (clip (1e-6) (1e6) (x / 100)) ^ (clip (-10) 10 (p 19)) +
      p 20 * (clip (1e-6) (1e6) (x / 100)) ^ (p 21) +
      p 22 * (clip (1e-6) (1e6) (x / 100)) ^ (p 23) +
      (if n = 95 ∨ n = 96 then
         p 24 * Real.sin (p 25 * x + p 26) else 0) +
      (if n = 123 then p 27 * (x / (x + 1)) + p 28 else 0)
  else 0

def heavy (p : Params) (n : ℕ) : ℝ :=
  max (light p n + heavyCorrection p n) (1e-12 : ℝ)

/-- The actual source's dispatch for the eleven positive-target
observation indices; zero-target n=0 is intentionally not an observable
in the frozen 31-to-11 sensitivity Jacobian. -/
def observed (p : Params) : Fin 11 → ℝ :=
  ![light p 1, light p 2, light p 3,
    middle p 12, middle p 19, middle p 53,
    middle p 73, middle p 91,
    heavy p 95, heavy p 96, heavy p 123]

/-- Selected eleven Jacobian columns in the precise order of the
3+5+3 minor. -/
def selectedColumn : Fin 11 → Fin 31 :=
  ![0, 3, 4, 14, 15, 9, 12, 13, 20, 24, 28]

theorem selectedColumn_injective : Function.Injective selectedColumn := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [selectedColumn]

/-- The floor is inactive when the raw value exceeds it. -/
theorem middle_eq_middleRaw_of_unclipped (p : Params) (n : ℕ)
    (h : (1e-12 : ℝ) ≤ middleRaw p n) : middle p n = middleRaw p n :=
  max_eq_left h

/-- The five-parameter frozen helper represents the full middle formula only
when the two frequency parameters have their stated frozen values. -/
theorem middle_eq_raw_of_unclipped (p : Params) (n : ℕ)
    (h : (1e-12 : ℝ) ≤ middleRaw p n)
    (hscale1 : p 10 = 5.0632) (hscale2 : p 11 = 9.4062) :
    middle p n = V18MiddleDerivatives.raw n (p 14) (p 15)
      (p 9) (p 12) (p 13) := by
  rw [middle_eq_middleRaw_of_unclipped p n h]
  simp [middleRaw, V18MiddleDerivatives.raw, hscale1, hscale2]

/-- All seven middle coefficients are retained in the full parameter map;
the published frozen values specialize to the existing five-column helper. -/
theorem frozen_middleRaw (alpha epsilon : ℝ) (n : ℕ) :
    middleRaw (frozen alpha epsilon) n =
      V18MiddleDerivatives.raw n 998.7 0.2427 2241.1 1.6469 0.2092 := by
  rfl

/-- Retained five-variable helper at the explicitly frozen frequencies. -/
theorem middle_raw_phase_derivative (n : ℕ) (p : Params) :
    HasDerivAt
      (fun phase : ℝ => V18MiddleDerivatives.raw n
        (p 14) (p 15) (p 9) phase (p 13))
      ((p 9) * Real.cos ((5.0632 : ℝ) * n + p 12)) (p 12) :=
  V18MiddleDerivatives.phase_derivative n
    (p 14) (p 15) (p 9) (p 12) (p 13)

theorem selected_middle_matrix_exact :
    V18MiddleDerivatives.selectedMatrix =
      V18MiddleJacobian.middle :=
  V18MiddleDerivatives.selectedMatrix_eq_middle


/-! ## Selected middle sensitivities in the actual 31-dimensional parameter vector -/

/-- The middle offset coordinate is parameter 14 of 31. -/
theorem middle_offset_coordinate_derivative (n : ℕ) (p : Params) :
    HasDerivAt
      (fun x : ℝ => middleRaw (Function.update p (14 : Fin 31) x) n)
      1 (p 14) := by
  convert (hasDerivAt_id (p 14)).add_const
    (p 15 * (n : ℝ) ^ 2 + p 13 * Real.sin (p 11 * n) +
      p 9 * Real.sin (p 10 * n + p 12)) using 1 <;>
    simp [middleRaw, add_assoc]

/-- The quadratic coefficient is parameter 15 of 31. -/
theorem middle_quad_coordinate_derivative (n : ℕ) (p : Params) :
    HasDerivAt
      (fun x : ℝ => middleRaw (Function.update p (15 : Fin 31) x) n)
      ((n : ℝ) ^ 2) (p 15) := by
  have hx := (hasDerivAt_id (p 15)).mul_const ((n : ℝ) ^ 2)
  convert (hx.const_add (p 14)).add_const
    (p 13 * Real.sin (p 11 * n) + p 9 * Real.sin (p 10 * n + p 12)) using 1 <;>
    simp [middleRaw, add_assoc]

/-- The amplitude derivative depends on the live frequency coordinate 10. -/
theorem middle_amp_coordinate_derivative (n : ℕ) (p : Params) :
    HasDerivAt
      (fun x : ℝ => middleRaw (Function.update p (9 : Fin 31) x) n)
      (Real.sin (p 10 * n + p 12)) (p 9) := by
  have hx := (hasDerivAt_id (p 9)).mul_const (Real.sin (p 10 * n + p 12))
  convert hx.const_add
    (p 14 + p 15 * (n : ℝ) ^ 2 + p 13 * Real.sin (p 11 * n)) using 1 <;>
    simp [middleRaw, add_assoc]

/-- Phase derivative at arbitrary values of all 31 coordinates. -/
theorem middle_phase_coordinate_derivative (n : ℕ) (p : Params) :
    HasDerivAt
      (fun x : ℝ => middleRaw (Function.update p (12 : Fin 31) x) n)
      (p 9 * Real.cos (p 10 * n + p 12)) (p 12) := by
  have harg := (hasDerivAt_id (p 12)).const_add (p 10 * (n : ℝ))
  have hs := (Real.hasDerivAt_sin _).comp (p 12) harg
  convert (hs.const_mul (p 9)).const_add
    (p 14 + p 15 * (n : ℝ) ^ 2 + p 13 * Real.sin (p 11 * n)) using 1 <;>
    simp [middleRaw, add_assoc]

/-- The harmonic amplitude derivative depends on frequency coordinate 11. -/
theorem middle_harmonic_coordinate_derivative (n : ℕ) (p : Params) :
    HasDerivAt
      (fun x : ℝ => middleRaw (Function.update p (13 : Fin 31) x) n)
      (Real.sin (p 11 * n)) (p 13) := by
  have hx := (hasDerivAt_id (p 13)).mul_const (Real.sin (p 11 * n))
  convert hx.const_add
    (p 14 + p 15 * (n : ℝ) ^ 2 + p 9 * Real.sin (p 10 * n + p 12)) using 1 <;>
    simp [middleRaw, add_assoc, add_comm, add_left_comm]

/-- Regression certificate: varying source frequency coordinate 10 produces
its actual derivative, rather than the identically zero derivative of a frozen helper. -/
theorem middle_scale1_coordinate_derivative (n : ℕ) (p : Params) :
    HasDerivAt
      (fun x : ℝ => middleRaw (Function.update p (10 : Fin 31) x) n)
      (p 9 * Real.cos (p 10 * n + p 12) * n) (p 10) := by
  have harg := ((hasDerivAt_id (p 10)).mul_const (n : ℝ)).add_const (p 12)
  have hs := (Real.hasDerivAt_sin _).comp (p 10) harg
  convert (hs.const_mul (p 9)).const_add
    (p 14 + p 15 * (n : ℝ) ^ 2 + p 13 * Real.sin (p 11 * n)) using 1 <;>
    simp [middleRaw, add_assoc, mul_assoc]

/-- Regression certificate for the second source frequency coordinate. -/
theorem middle_scale2_coordinate_derivative (n : ℕ) (p : Params) :
    HasDerivAt
      (fun x : ℝ => middleRaw (Function.update p (11 : Fin 31) x) n)
      (p 13 * Real.cos (p 11 * n) * n) (p 11) := by
  have harg := (hasDerivAt_id (p 11)).mul_const (n : ℝ)
  have hs := (Real.hasDerivAt_sin _).comp (p 11) harg
  convert (hs.const_mul (p 13)).const_add
    (p 14 + p 15 * (n : ℝ) ^ 2 + p 9 * Real.sin (p 10 * n + p 12)) using 1 <;>
    simp [middleRaw, add_assoc, add_comm, add_left_comm, mul_assoc]

/-- The Jacobian of this specified full observation map. -/
def jacobian (p : Params) : Params →L[ℝ] (Fin 11 → ℝ) := fderiv ℝ observed p

/-- Model-specific structural nullity, at any differentiability point.
Differentiability is explicit because clipping/floor transitions need not be smooth. -/
theorem local_identifiability (p : Params) (h : DifferentiableAt ℝ observed p) :
    HasFDerivAt observed (jacobian p) p ∧
    Module.finrank ℝ (LinearMap.range (jacobian p).toLinearMap) ≤ 11 ∧
    Module.finrank ℝ (LinearMap.ker (jacobian p).toLinearMap) =
      31 - Module.finrank ℝ (LinearMap.range (jacobian p).toLinearMap) ∧
    20 ≤ Module.finrank ℝ (LinearMap.ker (jacobian p).toLinearMap) := by
  have hr : Module.finrank ℝ (LinearMap.range (jacobian p).toLinearMap) ≤ 11 := by
    simpa using (Submodule.finrank_le (LinearMap.range (jacobian p).toLinearMap))
  have hsum := LinearMap.finrank_range_add_finrank_ker (jacobian p).toLinearMap
  have hdim : Module.finrank ℝ Params = 31 := by simp [Params]
  exact ⟨h.hasFDerivAt, hr, by omega, by omega⟩

/-- Each vector in this Jacobian's kernel has zero first directional derivative
along its actual parameter line. This is not a nonlinear equal-prediction claim. -/
theorem null_direction (p v : Params) (h : DifferentiableAt ℝ observed p)
    (hv : v ∈ LinearMap.ker (jacobian p).toLinearMap) :
    HasDerivAt (fun t : ℝ => observed (p + t • v)) 0 0 := by
  have hv' : jacobian p v = 0 := hv
  have hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hf : HasFDerivAt observed (jacobian p) (p + (0 : ℝ) • v) := by
    simpa [jacobian] using h.hasFDerivAt
  simpa only [hv'] using hf.comp_hasDerivAt 0 hline

end ReyesMath.V18Forward
