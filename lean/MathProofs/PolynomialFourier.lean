import MathProofs.L2Fourier
import Mathlib.Algebra.Polynomial.Roots

/-!
# Polynomial Fourier multipliers have no nonzero L² eigenstates

On the canonical Plancherel Fourier transform, a nonzero polynomial in
the radial frequency |ξ|² has no nonzero L² kernel. The zero locus is a
finite union of measure-zero spheres, including the possible origin.

The hypothesis is the actual Fourier-side multiplication equation
holding almost everywhere. Translating an arbitrary distributional PDE
to this equation is a separate distributional-Fourier interface step;
the theorem does not assume an unspecified Fourier isometry.
-/

noncomputable section
namespace ReyesMath.PolynomialFourier
open MeasureTheory L2Fourier
open scoped Polynomial

private abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

/-- A fixed squared radial frequency defines a Lebesgue-null set in
positive dimension, whether its value is negative, zero or positive. -/
theorem ae_norm_sq_ne (d : ℕ) (r : ℝ) :
    ∀ᵐ ξ : Rd d ∂volume, ‖ξ‖ ^ 2 ≠ r := by
  by_cases hr : 0 ≤ r
  · have hnull := euclidean_frequency_shell_measure_zero d (Real.sqrt r)
    have havoid : ∀ᵐ ξ : Rd d ∂volume,
        ξ ∉ Metric.sphere (0 : Rd d) (Real.sqrt r) := by
      apply ae_iff.mpr
      simpa only [not_not, Metric.sphere, dist_zero_right] using hnull
    filter_upwards [havoid] with ξ hξ heq
    apply hξ
    simp only [Metric.mem_sphere, dist_zero_right]
    nlinarith [Real.sq_sqrt hr, Real.sqrt_nonneg r, norm_nonneg ξ]
  · have hr' : r < 0 := lt_of_not_ge hr
    exact Filter.Eventually.of_forall fun ξ heq => by
      nlinarith [sq_nonneg (‖ξ‖)]

/-- Every nonzero real polynomial has nonzero radial symbol almost everywhere
in positive Euclidean dimension. The root set is finite, and every
squared-radius level set is Lebesgue null. -/
theorem ae_eval_ne (d : ℕ) (p : ℝ[X]) (hp : p ≠ 0) :
    ∀ᵐ ξ : Rd d ∂volume, Polynomial.eval (‖ξ‖ ^ 2) p ≠ 0 := by
  classical
  let s : Finset ℝ := p.roots.toFinset
  have havoid : ∀ᵐ ξ : Rd d ∂volume, ∀ r ∈ s, ‖ξ‖ ^ 2 ≠ r := by
    induction s using Finset.induction with
    | empty =>
      exact Filter.Eventually.of_forall (by simp)
    | @insert r t hrt iht =>
      filter_upwards [ae_norm_sq_ne d r, iht] with ξ hξ ht a ha
      rcases Finset.mem_insert.mp ha with h | h
      · exact h ▸ hξ
      · exact ht a h
  filter_upwards [havoid] with ξ hξ heq
  have hx : Polynomial.IsRoot p (‖ξ‖ ^ 2) := heq
  have hs : ‖ξ‖ ^ 2 ∈ s := by
    change ‖ξ‖ ^ 2 ∈ p.roots.toFinset
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hx)
  exact hξ _ hs heq

/-- A polynomial Fourier multiplier whose symbol is not identically zero
has trivial kernel in genuine L²(ℝᵈ). -/
theorem multiplier_kernel_zero (d : ℕ) (p : ℝ[X]) (hp : p ≠ 0)
    (u : Sobolev.L2 (d + 1))
    (h : ∀ᵐ ξ : Rd d ∂volume,
      ((Polynomial.eval (‖ξ‖ ^ 2) p : ℝ) : ℂ) *
        (L2Fourier.equivalence (d + 1) u : Rd d → ℂ) ξ = 0) :
    u = 0 := by
  have hn := ae_eval_ne d p hp
  have hzero : (L2Fourier.equivalence (d + 1) u : Rd d → ℂ) =ᵐ[volume]
      (fun _ => 0) := by
    filter_upwards [h, hn] with ξ hprod hn
    exact (mul_eq_zero.mp hprod).resolve_left (by exact_mod_cast hn)
  have hF : L2Fourier.equivalence (d + 1) u = 0 :=
    (Lp.eq_zero_iff_ae_eq_zero).2 hzero
  exact (L2Fourier.equivalence (d + 1)).injective (by simpa using hF)

/-- Spectral shift version: a nonconstant polynomial of -Δ has no
square-integrable eigenstate at any real eigenvalue, provided the
distributional equation has been converted to its Fourier multiplier. -/
theorem shifted_multiplier_kernel_zero (d : ℕ) (p : ℝ[X]) (λ : ℝ)
    (hp : p ≠ Polynomial.C λ)
    (u : Sobolev.L2 (d + 1))
    (h : ∀ᵐ ξ : Rd d ∂volume,
      (((Polynomial.eval (‖ξ‖ ^ 2) p - λ : ℝ) : ℂ) *
        (L2Fourier.equivalence (d + 1) u : Rd d → ℂ) ξ) = 0) :
    u = 0 := by
  have hsub : p - Polynomial.C λ ≠ 0 := sub_ne_zero.mpr hp
  apply multiplier_kernel_zero d (p - Polynomial.C λ) hsub u
  filter_upwards [h] with ξ hξ
  simpa only [Polynomial.eval_sub, Polynomial.eval_C] using hξ

end ReyesMath.PolynomialFourier
