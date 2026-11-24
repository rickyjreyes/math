import MathProofs.RemainingCores

/-!
# GC11: carrier-frame coercivity and Bogoliubov discriminant

Algebraic core for the ORIGINAL Hamiltonian cubic–quintic equation:
i u_t = (Δ + k₀²)² u - β |u|² u + γ |u|⁴ u.

q = |K|², s = |p|², t = K·p; rho = |A|².
The continuum Fourier transform, conservation, and orbital stability
argument are in the companion research note. This module does not itself
formalize that PDE argument or the Bloch spectral correspondence.
-/

noncomputable section

namespace ReyesMath
namespace GC11Coercivity

open RemainingCores

def frequency (k beta gamma rho q : ℝ) : ℝ :=
  shellSymbol k q - beta * rho + gamma * rho ^ 2

/-- The tangent-subtracted dispersion at a carrier K. -/
def excess (k q s t : ℝ) : ℝ :=
  shellSymbol k (q + s + 2 * t) - shellSymbol k q -
    4 * (q - k ^ 2) * t

theorem excess_eq (k q s t : ℝ) :
    excess k q s t = (s + 2 * t) ^ 2 + 2 * (q - k ^ 2) * s := by
  unfold excess shellSymbol
  ring

theorem excess_lower (k q s t : ℝ) :
    2 * (q - k ^ 2) * s ≤ excess k q s t := by
  rw [excess_eq]
  linarith [sq_nonneg (s + 2 * t)]

theorem excess_nonneg {k q s t : ℝ} (hq : k ^ 2 ≤ q) (hs : 0 ≤ s) :
    0 ≤ excess k q s t := by
  exact le_trans (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hq)) hs)
    (excess_lower k q s t)

theorem excess_pos {k q s t : ℝ} (hq : k ^ 2 < q) (hs : 0 < s) :
    0 < excess k q s t := by
  exact lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) (sub_pos.mpr hq)) hs)
    (excess_lower k q s t)

/-- High-frequency bound, using the geometric Cauchy–Schwarz condition. -/
theorem fourth_order_bound {k q s t : ℝ} (hcs : t ^ 2 ≤ q * s) :
    s ^ 2 ≤ 2 * excess k q s t + (4 * k ^ 2 + 4 * q) * s := by
  rw [excess_eq]
  nlinarith [sq_nonneg (s + 4 * t)]

def potential (beta gamma x : ℝ) : ℝ := -beta / 2 * x ^ 2 + gamma / 3 * x ^ 3

def densitySlope (beta gamma rho : ℝ) : ℝ := -beta * rho + gamma * rho ^ 2

def relativePotential (beta gamma rho x : ℝ) : ℝ :=
  potential beta gamma x - potential beta gamma rho -
    densitySlope beta gamma rho * (x - rho)

theorem relativePotential_eq (beta gamma rho x : ℝ) :
    relativePotential beta gamma rho x =
      (x - rho) ^ 2 * (gamma / 3 * (x + 2 * rho) - beta / 2) := by
  unfold relativePotential potential densitySlope
  ring

/-- Global density coercivity above 3 beta / (4 gamma). -/
theorem relativePotential_lower {beta gamma rho x : ℝ}
    (hg : 0 ≤ gamma) (hx : 0 ≤ x) :
    (2 * gamma * rho / 3 - beta / 2) * (x - rho) ^ 2 ≤
      relativePotential beta gamma rho x := by
  rw [relativePotential_eq]
  have h : 0 ≤ gamma / 3 * x * (x - rho) ^ 2 := by
    exact mul_nonneg (mul_nonneg (div_nonneg hg (by norm_num)) hx) (sq_nonneg _)
  linarith [show (x - rho) ^ 2 * (gamma / 3 * (x + 2 * rho) - beta / 2) -
      (2 * gamma * rho / 3 - beta / 2) * (x - rho) ^ 2 =
      gamma / 3 * x * (x - rho) ^ 2 by ring]

theorem density_coercivity_pos {beta gamma rho : ℝ}
    (h : 3 * beta < 4 * gamma * rho) :
    0 < 2 * gamma * rho / 3 - beta / 2 := by linarith

/-- Even and odd parts of the carrier-frame frequency difference. -/
def evenPart (k q s t : ℝ) : ℝ := s ^ 2 + 2 * (q - k ^ 2) * s + 4 * t ^ 2
def oddPart (k q s t : ℝ) : ℝ := 4 * t * (q - k ^ 2 + s)

theorem even_odd_decomposition (k q s t : ℝ) :
    shellSymbol k (q + s + 2 * t) - shellSymbol k q =
      evenPart k q s t + oddPart k q s t := by
  unfold shellSymbol evenPart oddPart
  ring

/-- Characteristic polynomial of the exact two-sideband matrix. -/
theorem sideband_characteristic (e o c z : ℝ) :
    (o + e + c - z) * (o - e - c - z) + c ^ 2 =
      (z - o) ^ 2 - e * (e + 2 * c) := by ring

theorem sideband_discriminant_nonneg {k q s t c : ℝ}
    (hq : k ^ 2 ≤ q) (hs : 0 ≤ s) (hc : 0 ≤ c) :
    0 ≤ evenPart k q s t * (evenPart k q s t + 2 * c) := by
  have hm : 0 ≤ 2 * (q - k ^ 2) * s :=
    mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hq)) hs
  have he : 0 ≤ evenPart k q s t := by
    unfold evenPart
    linarith [sq_nonneg s, sq_nonneg t]
  exact mul_nonneg he (by linarith)

theorem sideband_discriminant_neg {e c : ℝ} (he : e < 0) (hc : 0 < e + 2 * c) :
    e * (e + 2 * c) < 0 := mul_neg_of_neg_of_pos he hc

/-- Two distinct static carriers at the SAME original parameters.
Both satisfy the strict kinetic and density coercivity hypotheses.
The continuum construction takes the positive square roots of q and rho. -/
theorem two_static_carriers :
    frequency 1 1 1 (4/5) (7/5) = 0 ∧
    frequency 1 1 1 (9/10) (13/10) = 0 ∧
    (1 : ℝ) ^ 2 < 7/5 ∧ (1 : ℝ) ^ 2 < 13/10 ∧
    (3 : ℝ) < 4 * (4/5) ∧ (3 : ℝ) < 4 * (9/10) ∧
    (7/5 : ℝ) ≠ 13/10 := by
  norm_num [frequency, shellSymbol]

end GC11Coercivity
end ReyesMath
