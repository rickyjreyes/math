import Mathlib

/-!
# Kernel-checked interval arithmetic for the v18 certificates

`Bounds` uses closed real intervals. In particular, multiplication checks all
four endpoint products and does not assume signs of the enclosed values.
-/

namespace ReyesMath.V18Interval

def Bounds (lo hi x : ℝ) : Prop := lo ≤ x ∧ x ≤ hi

namespace Bounds

theorem point (x : ℝ) : Bounds x x x := ⟨le_rfl, le_rfl⟩

theorem add {a b c d x y : ℝ} (hx : Bounds a b x) (hy : Bounds c d y) :
    Bounds (a + c) (b + d) (x + y) :=
  ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem neg {a b x : ℝ} (hx : Bounds a b x) : Bounds (-b) (-a) (-x) :=
  ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

theorem sub {a b c d x y : ℝ} (hx : Bounds a b x) (hy : Bounds c d y) :
    Bounds (a - d) (b - c) (x - y) :=
  ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩

theorem widen {a b c d x : ℝ} (hx : Bounds a b x) (hlo : c ≤ a) (hhi : b ≤ d) :
    Bounds c d x := ⟨hlo.trans hx.1, hx.2.trans hhi⟩

theorem mul_right {a b x : ℝ} (hx : Bounds a b x) (c : ℝ) :
    Bounds (min (a*c) (b*c)) (max (a*c) (b*c)) (x*c) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hc),
      (mul_le_mul_of_nonneg_right hx.2 hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hc),
      (mul_le_mul_of_nonpos_right hx.1 hc).trans (le_max_left _ _)⟩

theorem mul {a b c d x y : ℝ} (hx : Bounds a b x) (hy : Bounds c d y) :
    Bounds (min (min (a*c) (a*d)) (min (b*c) (b*d)))
      (max (max (a*c) (a*d)) (max (b*c) (b*d))) (x*y) := by
  have ha : Bounds (min (a*c) (a*d)) (max (a*c) (a*d)) (a*y) := by
    simpa only [mul_comm] using hy.mul_right a
  have hb : Bounds (min (b*c) (b*d)) (max (b*c) (b*d)) (b*y) := by
    simpa only [mul_comm] using hy.mul_right b
  rcases le_total 0 y with hy0 | hy0
  · exact ⟨(min_le_left _ _).trans
        (ha.1.trans (mul_le_mul_of_nonneg_right hx.1 hy0)),
      (mul_le_mul_of_nonneg_right hx.2 hy0).trans (hb.2.trans (le_max_right _ _))⟩
  · exact ⟨(min_le_right _ _).trans
        (hb.1.trans (mul_le_mul_of_nonpos_right hx.2 hy0)),
      (mul_le_mul_of_nonpos_right hx.1 hy0).trans (ha.2.trans (le_max_left _ _))⟩

end Bounds
end ReyesMath.V18Interval
