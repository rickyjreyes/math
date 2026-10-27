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

/-- Historically stored 9+7+13 coefficients, with the two optimizer
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
  V18MiddleDerivatives.raw n (p 14) (p 15) (p 9) (p 12) (p 13)

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

/-- The middle scalar output exactly coincides with the analytically
differentiated source model when its historical floor is inactive. -/
theorem middle_eq_raw_of_unclipped (p : Params) (n : ℕ)
    (h : (1e-12 : ℝ) ≤ middleRaw p n) :
    middle p n = V18MiddleDerivatives.raw n (p 14) (p 15)
      (p 9) (p 12) (p 13) := by
  change max (V18MiddleDerivatives.raw n (p 14) (p 15)
    (p 9) (p 12) (p 13)) (1e-12 : ℝ) = _
  exact max_eq_left (by simpa only [middleRaw] using h)

/-- In the strict unclipped middle region, the five selected
coordinates have exactly the source-frozen analytic derivatives. -/
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

/-- The frozen middle offset coordinate is parameter 14 of 31. -/
theorem middle_offset_coordinate_derivative (n : ℕ) (p : Params) :
    HasDerivAt
      (fun x : ℝ => middleRaw (Function.update p (14 : Fin 31) x) n)
      1 (p 14) := by
  simpa [middleRaw] using
    V18MiddleDerivatives.offset_derivative n
      (p 14) (p 15) (p 9) (p 12) (p 13)

/-- The frozen quadratic coefficient is parameter 15 of 31. -/
theorem middle_quad_coordinate_derivative (n : ℕ) (p : Params) :
    HasDerivAt
      (fun x : ℝ => middleRaw (Function.update p (15 : Fin 31) x) n)
      ((n : ℝ) ^ 2) (p 15) := by
  simpa [middleRaw] using
    V18MiddleDerivatives.quad_derivative n
      (p 14) (p 15) (p 9) (p 12) (p 13)

/-- The frozen middle amplitude is parameter 9 of 31. -/
theorem middle_amp_coordinate_derivative (n : ℕ) (p : Params) :
    HasDerivAt
      (fun x : ℝ => middleRaw (Function.update p (9 : Fin 31) x) n)
      (Real.sin ((5.0632 : ℝ) * n + p 12)) (p 9) := by
  simpa [middleRaw] using
    V18MiddleDerivatives.amp_derivative n
      (p 14) (p 15) (p 9) (p 12) (p 13)

/-- The frozen middle phase is parameter 12 of 31. -/
theorem middle_phase_coordinate_derivative (n : ℕ) (p : Params) :
    HasDerivAt
      (fun x : ℝ => middleRaw (Function.update p (12 : Fin 31) x) n)
      ((p 9) * Real.cos ((5.0632 : ℝ) * n + p 12)) (p 12) := by
  simpa [middleRaw] using
    V18MiddleDerivatives.phase_derivative n
      (p 14) (p 15) (p 9) (p 12) (p 13)

/-- The frozen middle harmonic coefficient is parameter 13 of 31. -/
theorem middle_harmonic_coordinate_derivative (n : ℕ) (p : Params) :
    HasDerivAt
      (fun x : ℝ => middleRaw (Function.update p (13 : Fin 31) x) n)
      (Real.sin ((9.4062 : ℝ) * n)) (p 13) := by
  simpa [middleRaw] using
    V18MiddleDerivatives.harmonic_derivative n
      (p 14) (p 15) (p 9) (p 12) (p 13)

end ReyesMath.V18Forward
