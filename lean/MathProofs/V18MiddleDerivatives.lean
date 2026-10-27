import Mathlib
import MathProofs.V18MiddleJacobian

/-!
# Analytic derivatives of the frozen v18 middle-sector output

This module derives the five *selected* analytic partial derivatives of the
historical middle-sector prediction, rather than treating the rows as
uninterpreted measurements.  The v18 source uses:

  amp * sin(scale1 * n + phase)
    + harmonic * sin(scale2 * n) + offset + quad * n².

The scale constants here are the frozen source values 5.0632 and 9.4062.
The five independent differentiation variables are
(offset, quad, amp, phase, harmonic).
The outer max(x,1e-12) shares these derivatives only on the
positive (unclipped) sector, certified separately by source-pinned
interval arithmetic; this file does NOT assert a global derivative
through the nonsmooth clipping boundary.
-/

noncomputable section
namespace ReyesMath.V18MiddleDerivatives

def raw (n : ℕ) (offset quad amp phase harmonic : ℝ) : ℝ :=
  offset + quad * (n : ℝ) ^ 2 +
    harmonic * Real.sin ((9.4062 : ℝ) * n) +
    amp * Real.sin ((5.0632 : ℝ) * n + phase)

/-- Offset derivative is identically 1. -/
theorem offset_derivative (n : ℕ) (offset quad amp phase harmonic : ℝ) :
    HasDerivAt (fun x : ℝ => raw n x quad amp phase harmonic) 1 offset := by
  convert (hasDerivAt_id offset).add_const
    (quad * (n : ℝ) ^ 2 + harmonic * Real.sin ((9.4062 : ℝ) * n) +
      amp * Real.sin ((5.0632 : ℝ) * n + phase)) using 1 <;>
    simp [raw, add_assoc]

/-- Quadratic coefficient derivative is exactly n². -/
theorem quad_derivative (n : ℕ) (offset quad amp phase harmonic : ℝ) :
    HasDerivAt (fun x : ℝ => raw n offset x amp phase harmonic)
      ((n : ℝ) ^ 2) quad := by
  have hx := (hasDerivAt_id quad).mul_const ((n : ℝ) ^ 2)
  convert ((hx.const_add offset).add_const
    (harmonic * Real.sin ((9.4062 : ℝ) * n) +
      amp * Real.sin ((5.0632 : ℝ) * n + phase))) using 1 <;>
    simp [raw, add_assoc]

/-- Amplitude derivative equals the first frozen sinusoid. -/
theorem amp_derivative (n : ℕ) (offset quad amp phase harmonic : ℝ) :
    HasDerivAt (fun x : ℝ => raw n offset quad x phase harmonic)
      (Real.sin ((5.0632 : ℝ) * n + phase)) amp := by
  have hx := (hasDerivAt_id amp).mul_const
    (Real.sin ((5.0632 : ℝ) * n + phase))
  convert hx.const_add
    (offset + quad * (n : ℝ) ^ 2 +
      harmonic * Real.sin ((9.4062 : ℝ) * n)) using 1 <;>
    simp [raw, add_assoc, add_comm, add_left_comm]

/-- Phase derivative is amplitude times cosine, by the chain rule. -/
theorem phase_derivative (n : ℕ) (offset quad amp phase harmonic : ℝ) :
    HasDerivAt (fun x : ℝ => raw n offset quad amp x harmonic)
      (amp * Real.cos ((5.0632 : ℝ) * n + phase)) phase := by
  have harg : HasDerivAt (fun x : ℝ => (5.0632 : ℝ) * n + x) 1 phase := by
    convert (hasDerivAt_id phase).const_add ((5.0632 : ℝ) * n) using 1 <;> ring
  have hs : HasDerivAt (fun x : ℝ => Real.sin ((5.0632 : ℝ) * n + x))
      (Real.cos ((5.0632 : ℝ) * n + phase)) phase := by
    simpa using (Real.hasDerivAt_sin _).comp phase harg
  convert (hs.const_mul amp).const_add
    (offset + quad * (n : ℝ) ^ 2 +
      harmonic * Real.sin ((9.4062 : ℝ) * n)) using 1 <;>
    simp [raw, add_assoc, add_comm, add_left_comm]

/-- Harmonic coefficient derivative is the second frozen sinusoid. -/
theorem harmonic_derivative (n : ℕ) (offset quad amp phase harmonic : ℝ) :
    HasDerivAt (fun x : ℝ => raw n offset quad amp phase x)
      (Real.sin ((9.4062 : ℝ) * n)) harmonic := by
  have hx := (hasDerivAt_id harmonic).mul_const
    (Real.sin ((9.4062 : ℝ) * n))
  convert hx.const_add
    (offset + quad * (n : ℝ) ^ 2 +
      amp * Real.sin ((5.0632 : ℝ) * n + phase)) using 1 <;>
    simp [raw, add_assoc, add_comm, add_left_comm]

/-- The five selected source-partial derivatives in column order. -/
def selectedRow (n : ℕ) (amp phase : ℝ) : Fin 5 → ℝ
  | 0 => 1
  | 1 => (n : ℝ) ^ 2
  | 2 => Real.sin ((5.0632 : ℝ) * n + phase)
  | 3 => amp * Real.cos ((5.0632 : ℝ) * n + phase)
  | 4 => Real.sin ((9.4062 : ℝ) * n)

/-- Exact source-frozen derivative row matrix at n=12,19,53,73,91. -/
def selectedMatrix : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i => selectedRow ((![12, 19, 53, 73, 91] : Fin 5 → ℕ) i) 2241.1 1.6469

/-- The analytically differentiated source rows are the matrix used in the
frozen v18 determinant certificate. This checks every declared entry. -/
theorem selectedMatrix_eq_middle :
    selectedMatrix = V18MiddleJacobian.middle := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [selectedMatrix, selectedRow, V18MiddleJacobian.middle]

end ReyesMath.V18MiddleDerivatives
