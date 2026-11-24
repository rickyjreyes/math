import MathProofs.V18Identifiability

/-!
# GC26: exact global fibers of the actual v18 observation map

The quark correction coordinates are absent from the observed dispatch.
The Higgs amplitude and offset occur only in one combination.
These identities do not differentiate any floor or clipping branch.
-/

set_option maxHeartbeats 1000000

noncomputable section
namespace ReyesMath.V18Forward
open Filter
open scoped Topology

/- Concrete projection lemmas prevent exponential expansion of dependent update ifs. -/
@[local simp] private theorem upd_16_0 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (0 : Fin 31) = p 0 := by
  rw [Function.update_of_ne (show (0 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_1 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (1 : Fin 31) = p 1 := by
  rw [Function.update_of_ne (show (1 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_2 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (2 : Fin 31) = p 2 := by
  rw [Function.update_of_ne (show (2 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_3 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (3 : Fin 31) = p 3 := by
  rw [Function.update_of_ne (show (3 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_4 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (4 : Fin 31) = p 4 := by
  rw [Function.update_of_ne (show (4 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_5 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (5 : Fin 31) = p 5 := by
  rw [Function.update_of_ne (show (5 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_6 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (6 : Fin 31) = p 6 := by
  rw [Function.update_of_ne (show (6 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_7 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (7 : Fin 31) = p 7 := by
  rw [Function.update_of_ne (show (7 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_8 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (8 : Fin 31) = p 8 := by
  rw [Function.update_of_ne (show (8 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_9 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (9 : Fin 31) = p 9 := by
  rw [Function.update_of_ne (show (9 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_10 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (10 : Fin 31) = p 10 := by
  rw [Function.update_of_ne (show (10 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_11 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (11 : Fin 31) = p 11 := by
  rw [Function.update_of_ne (show (11 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_12 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (12 : Fin 31) = p 12 := by
  rw [Function.update_of_ne (show (12 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_13 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (13 : Fin 31) = p 13 := by
  rw [Function.update_of_ne (show (13 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_14 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (14 : Fin 31) = p 14 := by
  rw [Function.update_of_ne (show (14 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_15 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (15 : Fin 31) = p 15 := by
  rw [Function.update_of_ne (show (15 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_17 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (17 : Fin 31) = p 17 := by
  rw [Function.update_of_ne (show (17 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_18 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (18 : Fin 31) = p 18 := by
  rw [Function.update_of_ne (show (18 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_19 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (19 : Fin 31) = p 19 := by
  rw [Function.update_of_ne (show (19 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_20 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (20 : Fin 31) = p 20 := by
  rw [Function.update_of_ne (show (20 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_21 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (21 : Fin 31) = p 21 := by
  rw [Function.update_of_ne (show (21 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_22 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (22 : Fin 31) = p 22 := by
  rw [Function.update_of_ne (show (22 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_23 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (23 : Fin 31) = p 23 := by
  rw [Function.update_of_ne (show (23 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_24 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (24 : Fin 31) = p 24 := by
  rw [Function.update_of_ne (show (24 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_25 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (25 : Fin 31) = p 25 := by
  rw [Function.update_of_ne (show (25 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_26 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (26 : Fin 31) = p 26 := by
  rw [Function.update_of_ne (show (26 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_27 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (27 : Fin 31) = p 27 := by
  rw [Function.update_of_ne (show (27 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_28 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (28 : Fin 31) = p 28 := by
  rw [Function.update_of_ne (show (28 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_29 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (29 : Fin 31) = p 29 := by
  rw [Function.update_of_ne (show (29 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_16_30 (p : Params) (t : ℝ) :
    Function.update p (16 : Fin 31) t (30 : Fin 31) = p 30 := by
  rw [Function.update_of_ne (show (30 : Fin 31) ≠ 16 by decide)]
@[local simp] private theorem upd_18_0 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (0 : Fin 31) = p 0 := by
  rw [Function.update_of_ne (show (0 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_1 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (1 : Fin 31) = p 1 := by
  rw [Function.update_of_ne (show (1 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_2 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (2 : Fin 31) = p 2 := by
  rw [Function.update_of_ne (show (2 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_3 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (3 : Fin 31) = p 3 := by
  rw [Function.update_of_ne (show (3 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_4 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (4 : Fin 31) = p 4 := by
  rw [Function.update_of_ne (show (4 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_5 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (5 : Fin 31) = p 5 := by
  rw [Function.update_of_ne (show (5 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_6 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (6 : Fin 31) = p 6 := by
  rw [Function.update_of_ne (show (6 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_7 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (7 : Fin 31) = p 7 := by
  rw [Function.update_of_ne (show (7 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_8 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (8 : Fin 31) = p 8 := by
  rw [Function.update_of_ne (show (8 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_9 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (9 : Fin 31) = p 9 := by
  rw [Function.update_of_ne (show (9 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_10 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (10 : Fin 31) = p 10 := by
  rw [Function.update_of_ne (show (10 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_11 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (11 : Fin 31) = p 11 := by
  rw [Function.update_of_ne (show (11 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_12 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (12 : Fin 31) = p 12 := by
  rw [Function.update_of_ne (show (12 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_13 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (13 : Fin 31) = p 13 := by
  rw [Function.update_of_ne (show (13 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_14 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (14 : Fin 31) = p 14 := by
  rw [Function.update_of_ne (show (14 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_15 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (15 : Fin 31) = p 15 := by
  rw [Function.update_of_ne (show (15 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_16 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (16 : Fin 31) = p 16 := by
  rw [Function.update_of_ne (show (16 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_17 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (17 : Fin 31) = p 17 := by
  rw [Function.update_of_ne (show (17 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_19 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (19 : Fin 31) = p 19 := by
  rw [Function.update_of_ne (show (19 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_20 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (20 : Fin 31) = p 20 := by
  rw [Function.update_of_ne (show (20 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_21 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (21 : Fin 31) = p 21 := by
  rw [Function.update_of_ne (show (21 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_22 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (22 : Fin 31) = p 22 := by
  rw [Function.update_of_ne (show (22 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_23 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (23 : Fin 31) = p 23 := by
  rw [Function.update_of_ne (show (23 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_24 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (24 : Fin 31) = p 24 := by
  rw [Function.update_of_ne (show (24 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_25 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (25 : Fin 31) = p 25 := by
  rw [Function.update_of_ne (show (25 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_26 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (26 : Fin 31) = p 26 := by
  rw [Function.update_of_ne (show (26 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_27 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (27 : Fin 31) = p 27 := by
  rw [Function.update_of_ne (show (27 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_28 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (28 : Fin 31) = p 28 := by
  rw [Function.update_of_ne (show (28 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_29 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (29 : Fin 31) = p 29 := by
  rw [Function.update_of_ne (show (29 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_18_30 (p : Params) (t : ℝ) :
    Function.update p (18 : Fin 31) t (30 : Fin 31) = p 30 := by
  rw [Function.update_of_ne (show (30 : Fin 31) ≠ 18 by decide)]
@[local simp] private theorem upd_27_0 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (0 : Fin 31) = p 0 := by
  rw [Function.update_of_ne (show (0 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_1 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (1 : Fin 31) = p 1 := by
  rw [Function.update_of_ne (show (1 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_2 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (2 : Fin 31) = p 2 := by
  rw [Function.update_of_ne (show (2 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_3 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (3 : Fin 31) = p 3 := by
  rw [Function.update_of_ne (show (3 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_4 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (4 : Fin 31) = p 4 := by
  rw [Function.update_of_ne (show (4 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_5 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (5 : Fin 31) = p 5 := by
  rw [Function.update_of_ne (show (5 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_6 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (6 : Fin 31) = p 6 := by
  rw [Function.update_of_ne (show (6 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_7 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (7 : Fin 31) = p 7 := by
  rw [Function.update_of_ne (show (7 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_8 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (8 : Fin 31) = p 8 := by
  rw [Function.update_of_ne (show (8 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_9 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (9 : Fin 31) = p 9 := by
  rw [Function.update_of_ne (show (9 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_10 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (10 : Fin 31) = p 10 := by
  rw [Function.update_of_ne (show (10 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_11 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (11 : Fin 31) = p 11 := by
  rw [Function.update_of_ne (show (11 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_12 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (12 : Fin 31) = p 12 := by
  rw [Function.update_of_ne (show (12 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_13 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (13 : Fin 31) = p 13 := by
  rw [Function.update_of_ne (show (13 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_14 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (14 : Fin 31) = p 14 := by
  rw [Function.update_of_ne (show (14 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_15 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (15 : Fin 31) = p 15 := by
  rw [Function.update_of_ne (show (15 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_16 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (16 : Fin 31) = p 16 := by
  rw [Function.update_of_ne (show (16 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_17 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (17 : Fin 31) = p 17 := by
  rw [Function.update_of_ne (show (17 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_18 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (18 : Fin 31) = p 18 := by
  rw [Function.update_of_ne (show (18 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_19 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (19 : Fin 31) = p 19 := by
  rw [Function.update_of_ne (show (19 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_20 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (20 : Fin 31) = p 20 := by
  rw [Function.update_of_ne (show (20 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_21 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (21 : Fin 31) = p 21 := by
  rw [Function.update_of_ne (show (21 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_22 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (22 : Fin 31) = p 22 := by
  rw [Function.update_of_ne (show (22 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_23 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (23 : Fin 31) = p 23 := by
  rw [Function.update_of_ne (show (23 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_24 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (24 : Fin 31) = p 24 := by
  rw [Function.update_of_ne (show (24 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_25 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (25 : Fin 31) = p 25 := by
  rw [Function.update_of_ne (show (25 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_26 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (26 : Fin 31) = p 26 := by
  rw [Function.update_of_ne (show (26 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_28 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (28 : Fin 31) = p 28 := by
  rw [Function.update_of_ne (show (28 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_29 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (29 : Fin 31) = p 29 := by
  rw [Function.update_of_ne (show (29 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_27_30 (p : Params) (t : ℝ) :
    Function.update p (27 : Fin 31) t (30 : Fin 31) = p 30 := by
  rw [Function.update_of_ne (show (30 : Fin 31) ≠ 27 by decide)]
@[local simp] private theorem upd_28_0 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (0 : Fin 31) = p 0 := by
  rw [Function.update_of_ne (show (0 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_1 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (1 : Fin 31) = p 1 := by
  rw [Function.update_of_ne (show (1 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_2 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (2 : Fin 31) = p 2 := by
  rw [Function.update_of_ne (show (2 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_3 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (3 : Fin 31) = p 3 := by
  rw [Function.update_of_ne (show (3 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_4 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (4 : Fin 31) = p 4 := by
  rw [Function.update_of_ne (show (4 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_5 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (5 : Fin 31) = p 5 := by
  rw [Function.update_of_ne (show (5 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_6 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (6 : Fin 31) = p 6 := by
  rw [Function.update_of_ne (show (6 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_7 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (7 : Fin 31) = p 7 := by
  rw [Function.update_of_ne (show (7 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_8 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (8 : Fin 31) = p 8 := by
  rw [Function.update_of_ne (show (8 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_9 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (9 : Fin 31) = p 9 := by
  rw [Function.update_of_ne (show (9 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_10 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (10 : Fin 31) = p 10 := by
  rw [Function.update_of_ne (show (10 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_11 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (11 : Fin 31) = p 11 := by
  rw [Function.update_of_ne (show (11 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_12 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (12 : Fin 31) = p 12 := by
  rw [Function.update_of_ne (show (12 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_13 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (13 : Fin 31) = p 13 := by
  rw [Function.update_of_ne (show (13 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_14 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (14 : Fin 31) = p 14 := by
  rw [Function.update_of_ne (show (14 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_15 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (15 : Fin 31) = p 15 := by
  rw [Function.update_of_ne (show (15 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_16 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (16 : Fin 31) = p 16 := by
  rw [Function.update_of_ne (show (16 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_17 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (17 : Fin 31) = p 17 := by
  rw [Function.update_of_ne (show (17 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_18 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (18 : Fin 31) = p 18 := by
  rw [Function.update_of_ne (show (18 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_19 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (19 : Fin 31) = p 19 := by
  rw [Function.update_of_ne (show (19 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_20 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (20 : Fin 31) = p 20 := by
  rw [Function.update_of_ne (show (20 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_21 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (21 : Fin 31) = p 21 := by
  rw [Function.update_of_ne (show (21 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_22 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (22 : Fin 31) = p 22 := by
  rw [Function.update_of_ne (show (22 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_23 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (23 : Fin 31) = p 23 := by
  rw [Function.update_of_ne (show (23 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_24 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (24 : Fin 31) = p 24 := by
  rw [Function.update_of_ne (show (24 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_25 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (25 : Fin 31) = p 25 := by
  rw [Function.update_of_ne (show (25 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_26 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (26 : Fin 31) = p 26 := by
  rw [Function.update_of_ne (show (26 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_27 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (27 : Fin 31) = p 27 := by
  rw [Function.update_of_ne (show (27 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_29 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (29 : Fin 31) = p 29 := by
  rw [Function.update_of_ne (show (29 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem upd_28_30 (p : Params) (t : ℝ) :
    Function.update p (28 : Fin 31) t (30 : Fin 31) = p 30 := by
  rw [Function.update_of_ne (show (30 : Fin 31) ≠ 28 by decide)]
@[local simp] private theorem obs_0 (p : Params) : observed p (0 : Fin 11) = light p 1 := rfl
@[local simp] private theorem obs_1 (p : Params) : observed p (1 : Fin 11) = light p 2 := rfl
@[local simp] private theorem obs_2 (p : Params) : observed p (2 : Fin 11) = light p 3 := rfl
@[local simp] private theorem obs_3 (p : Params) : observed p (3 : Fin 11) = middle p 12 := rfl
@[local simp] private theorem obs_4 (p : Params) : observed p (4 : Fin 11) = middle p 19 := rfl
@[local simp] private theorem obs_5 (p : Params) : observed p (5 : Fin 11) = middle p 53 := rfl
@[local simp] private theorem obs_6 (p : Params) : observed p (6 : Fin 11) = middle p 73 := rfl
@[local simp] private theorem obs_7 (p : Params) : observed p (7 : Fin 11) = middle p 91 := rfl
@[local simp] private theorem obs_8 (p : Params) : observed p (8 : Fin 11) = heavy p 95 := rfl
@[local simp] private theorem obs_9 (p : Params) : observed p (9 : Fin 11) = heavy p 96 := rfl
@[local simp] private theorem obs_10 (p : Params) : observed p (10 : Fin 11) = heavy p 123 := rfl


private theorem upd_16_light (p : Params) (t : ℝ) (n : ℕ) :
    light (Function.update p (16 : Fin 31) t) n = light p n := by
  simp only [light, lightRaw, upd_16_0, upd_16_1, upd_16_2, upd_16_3, upd_16_4, upd_16_5, upd_16_6, upd_16_7, upd_16_8, upd_16_29, upd_16_30]
private theorem upd_16_middle (p : Params) (t : ℝ) (n : ℕ) :
    middle (Function.update p (16 : Fin 31) t) n = middle p n := by
  simp only [middle, middleRaw, upd_16_9, upd_16_10, upd_16_11, upd_16_12, upd_16_13, upd_16_14, upd_16_15]
private theorem upd_16_heavy (p : Params) (t : ℝ) (n : ℕ) (hn : 91 ≤ n)
    (hu : n ≤ 123) :
    heavy (Function.update p (16 : Fin 31) t) n = heavy p n := by
  have hnot : ¬ (19 ≤ n ∧ n ≤ 73) := by omega
  simp only [heavy, upd_16_light, heavyCorrection, if_neg hnot, if_pos ⟨hn, hu⟩,
    upd_16_17, upd_16_19, upd_16_20, upd_16_21, upd_16_22, upd_16_23, upd_16_24, upd_16_25, upd_16_26, upd_16_27, upd_16_28]
theorem observed_update_quarkAmp (p : Params) (t : ℝ) :
    observed (Function.update p (16 : Fin 31) t) = observed p := by
  funext i
  fin_cases i
  · change light (Function.update p (16 : Fin 31) t) 1 = light p 1
    exact upd_16_light p t _
  · change light (Function.update p (16 : Fin 31) t) 2 = light p 2
    exact upd_16_light p t _
  · change light (Function.update p (16 : Fin 31) t) 3 = light p 3
    exact upd_16_light p t _
  · change middle (Function.update p (16 : Fin 31) t) 12 = middle p 12
    exact upd_16_middle p t _
  · change middle (Function.update p (16 : Fin 31) t) 19 = middle p 19
    exact upd_16_middle p t _
  · change middle (Function.update p (16 : Fin 31) t) 53 = middle p 53
    exact upd_16_middle p t _
  · change middle (Function.update p (16 : Fin 31) t) 73 = middle p 73
    exact upd_16_middle p t _
  · change middle (Function.update p (16 : Fin 31) t) 91 = middle p 91
    exact upd_16_middle p t _
  · change heavy (Function.update p (16 : Fin 31) t) 95 = heavy p 95
    exact upd_16_heavy p t _ (by decide) (by decide)
  · change heavy (Function.update p (16 : Fin 31) t) 96 = heavy p 96
    exact upd_16_heavy p t _ (by decide) (by decide)
  · change heavy (Function.update p (16 : Fin 31) t) 123 = heavy p 123
    exact upd_16_heavy p t _ (by decide) (by decide)

private theorem upd_18_light (p : Params) (t : ℝ) (n : ℕ) :
    light (Function.update p (18 : Fin 31) t) n = light p n := by
  simp only [light, lightRaw, upd_18_0, upd_18_1, upd_18_2, upd_18_3, upd_18_4, upd_18_5, upd_18_6, upd_18_7, upd_18_8, upd_18_29, upd_18_30]
private theorem upd_18_middle (p : Params) (t : ℝ) (n : ℕ) :
    middle (Function.update p (18 : Fin 31) t) n = middle p n := by
  simp only [middle, middleRaw, upd_18_9, upd_18_10, upd_18_11, upd_18_12, upd_18_13, upd_18_14, upd_18_15]
private theorem upd_18_heavy (p : Params) (t : ℝ) (n : ℕ) (hn : 91 ≤ n)
    (hu : n ≤ 123) :
    heavy (Function.update p (18 : Fin 31) t) n = heavy p n := by
  have hnot : ¬ (19 ≤ n ∧ n ≤ 73) := by omega
  simp only [heavy, upd_18_light, heavyCorrection, if_neg hnot, if_pos ⟨hn, hu⟩,
    upd_18_17, upd_18_19, upd_18_20, upd_18_21, upd_18_22, upd_18_23, upd_18_24, upd_18_25, upd_18_26, upd_18_27, upd_18_28]
theorem observed_update_quarkPower (p : Params) (t : ℝ) :
    observed (Function.update p (18 : Fin 31) t) = observed p := by
  funext i
  fin_cases i
  · change light (Function.update p (18 : Fin 31) t) 1 = light p 1
    exact upd_18_light p t _
  · change light (Function.update p (18 : Fin 31) t) 2 = light p 2
    exact upd_18_light p t _
  · change light (Function.update p (18 : Fin 31) t) 3 = light p 3
    exact upd_18_light p t _
  · change middle (Function.update p (18 : Fin 31) t) 12 = middle p 12
    exact upd_18_middle p t _
  · change middle (Function.update p (18 : Fin 31) t) 19 = middle p 19
    exact upd_18_middle p t _
  · change middle (Function.update p (18 : Fin 31) t) 53 = middle p 53
    exact upd_18_middle p t _
  · change middle (Function.update p (18 : Fin 31) t) 73 = middle p 73
    exact upd_18_middle p t _
  · change middle (Function.update p (18 : Fin 31) t) 91 = middle p 91
    exact upd_18_middle p t _
  · change heavy (Function.update p (18 : Fin 31) t) 95 = heavy p 95
    exact upd_18_heavy p t _ (by decide) (by decide)
  · change heavy (Function.update p (18 : Fin 31) t) 96 = heavy p 96
    exact upd_18_heavy p t _ (by decide) (by decide)
  · change heavy (Function.update p (18 : Fin 31) t) 123 = heavy p 123
    exact upd_18_heavy p t _ (by decide) (by decide)

def shiftHiggs (p : Params) (t : ℝ) : Params :=
  Function.update (Function.update p (27 : Fin 31) (p 27 + t))
    (28 : Fin 31) (p 28 - (123 / 124 : ℝ) * t)

private theorem shiftHiggs_light (p : Params) (t : ℝ) (n : ℕ) :
    light (shiftHiggs p t) n = light p n := by
  norm_num [shiftHiggs, light, lightRaw]

private theorem shiftHiggs_middle (p : Params) (t : ℝ) (n : ℕ) :
    middle (shiftHiggs p t) n = middle p n := by
  norm_num [shiftHiggs, middle, middleRaw]

private theorem shiftHiggs_heavyCorrection (p : Params) (t : ℝ) (n : Fin 3) :
    heavyCorrection (shiftHiggs p t) (![95, 96, 123] n) =
      heavyCorrection p (![95, 96, 123] n) := by
  fin_cases n <;>
    norm_num [shiftHiggs, heavyCorrection, Matrix.cons_val] <;> ring

theorem observed_shiftHiggs (p : Params) (t : ℝ) :
    observed (shiftHiggs p t) = observed p := by
  have h0 := shiftHiggs_heavyCorrection p t (0 : Fin 3)
  have h1 := shiftHiggs_heavyCorrection p t (1 : Fin 3)
  have h2 := shiftHiggs_heavyCorrection p t (2 : Fin 3)
  change heavyCorrection (shiftHiggs p t) 95 = heavyCorrection p 95 at h0
  change heavyCorrection (shiftHiggs p t) 96 = heavyCorrection p 96 at h1
  change heavyCorrection (shiftHiggs p t) 123 = heavyCorrection p 123 at h2
  funext i
  fin_cases i <;>
    simp [observed, heavy, shiftHiggs_light, shiftHiggs_middle, h0, h1, h2]

/-- Three independent free scalars give an exact global family of equal outputs. -/
def invisibleFamily (p : Params) (a b c : ℝ) : Params :=
  shiftHiggs (Function.update (Function.update p (16 : Fin 31) a)
    (18 : Fin 31) b) c

theorem observed_invisibleFamily (p : Params) (a b c : ℝ) :
    observed (invisibleFamily p a b c) = observed p := by
  simp only [invisibleFamily, observed_shiftHiggs,
    observed_update_quarkPower, observed_update_quarkAmp]

theorem invisibleFamily_injective (p : Params) :
    Function.Injective (fun t : ℝ × ℝ × ℝ =>
      invisibleFamily p t.1 t.2.1 t.2.2) := by
  rintro ⟨a,b,c⟩ ⟨d,e,f⟩ h
  have h16 := congrFun h (16 : Fin 31)
  have h18 := congrFun h (18 : Fin 31)
  have h27 := congrFun h (27 : Fin 31)
  simp [invisibleFamily, shiftHiggs] at h16 h18 h27
  have hc : c = f := by linarith
  exact Prod.ext h16 (Prod.ext h18 hc)

/-- At every ambient point, even at a nonsmooth floor or clip, every
neighborhood contains a distinct point on the exact same fiber. -/
theorem observed_all_points_nonisolated (p : Params) (U : Set Params)
    (hU : U ∈ 𝓝 p) : ∃ q ∈ U, q ≠ p ∧ observed q = observed p := by
  let path : ℝ → Params := fun t => Function.update p (16 : Fin 31) t
  have hc : Continuous path := by
    apply continuous_pi
    intro i
    by_cases hi : i = (16 : Fin 31)
    · subst i
      simpa [path] using (continuous_id : Continuous (fun t : ℝ => t))
    · simpa [path, Function.update, hi] using
        (continuous_const : Continuous (fun _ : ℝ => p i))
  have hp : path (p 16) = p := by
    funext i
    by_cases hi : i = (16 : Fin 31)
    · subst i
      simp [path]
    · simp [path, Function.update, hi]
  have ht : Tendsto path (𝓝 (p 16)) (𝓝 p) := by
    simpa only [ContinuousAt, hp] using (hc.continuousAt (x := p 16))
  have hnear : ∀ᶠ t in 𝓝 (p 16), path t ∈ U := ht hU
  have hne : ∀ᶠ t in 𝓝[≠] (p 16), t ≠ p 16 := self_mem_nhdsWithin
  obtain ⟨t, hu, htne⟩ := ((hnear.filter_mono nhdsWithin_le_nhds).and hne).exists
  refine ⟨path t, hu, ?_, observed_update_quarkAmp p t⟩
  intro he
  apply htne
  simpa [path] using congrFun he (16 : Fin 31)

/-- A relative domain inherits non-isolation whenever it permits arbitrarily
small changes of the unused quark amplitude. The hypothesis is explicit;
a fixed-coordinate prior is not automatically covered. -/
theorem observed_relative_nonisolated (p : Params) (S : Set Params)
    (h : ∀ U : Set Params, U ∈ 𝓝 p →
      ∃ t : ℝ, t ≠ p 16 ∧ Function.update p (16 : Fin 31) t ∈ U ∩ S)
    (U : Set Params) (hU : U ∈ 𝓝 p) :
    ∃ q ∈ U ∩ S, q ≠ p ∧ observed q = observed p := by
  obtain ⟨t, ht, hmem⟩ := h U hU
  refine ⟨_, hmem, ?_, observed_update_quarkAmp p t⟩
  intro he
  apply ht
  simpa using congrFun he (16 : Fin 31)

theorem observed_not_injective : ¬ Function.Injective observed := by
  intro h
  let p : Params := fun _ => 0
  have he := h (observed_update_quarkAmp p 1)
  have hn := congrFun he (16 : Fin 31)
  norm_num [p] at hn

/-- Exact scalar floor-fiber test, including equality at the clipping boundary. -/
theorem floor_eq_iff (x c y : ℝ) :
    max x c = y ↔ x ≤ y ∧ c ≤ y ∧ (x = y ∨ c = y) := by
  constructor
  · intro h
    refine ⟨h ▸ le_max_left x c, h ▸ le_max_right x c, ?_⟩
    rcases le_total x c with hx | hx
    · exact Or.inr ((max_eq_right hx).symm.trans h)
    · exact Or.inl ((max_eq_left hx).symm.trans h)
  · rintro ⟨hx, hc, h | h⟩
    · rw [h, max_eq_left hc]
    · rw [h, max_eq_right hx]

/-- Exact nested floor-fiber test: applies to heavy outputs at every point. -/
theorem nested_floor_eq_iff (x d c y : ℝ) :
    max (max x c + d) c = y ↔
      x + d ≤ y ∧ c + d ≤ y ∧ c ≤ y ∧
      (x + d = y ∨ c + d = y ∨ c = y) := by
  have h : max x c + d = max (x + d) (c + d) := by
    rcases le_total x c with hx | hx
    · rw [max_eq_right hx, max_eq_right (add_le_add_right hx d)]
    · rw [max_eq_left hx, max_eq_left (add_le_add_right hx d)]
  rw [h, floor_eq_iff, max_le_iff, floor_eq_iff]
  tauto

/-- A polynomial with generically nonzero derivative need not be globally injective. -/
theorem generic_rank_counterexample :
    (∀ x : ℝ, x ≠ 0 → HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x ∧
      2 * x ≠ 0) ∧ ¬ Function.Injective (fun t : ℝ => t ^ 2) := by
  constructor
  · intro x hx
    exact ⟨by simpa using (hasDerivAt_pow 2 x), mul_ne_zero (by norm_num) hx⟩
  · intro h
    have hn : (1 : ℝ) = -1 := h (by norm_num)
    norm_num at hn

/-- Any differentiable augmented observation with fewer than 31 output
coordinates has a nontrivial derivative kernel. This is a rank obstruction,
not by itself an obstruction to a singular isolated fiber. -/
theorem augmented_rank_obstruction (N : ℕ) (hN : N < 31)
    (J : Params →L[ℝ] (Fin N → ℝ)) :
    0 < Module.finrank ℝ (LinearMap.ker J.toLinearMap) := by
  have hr : Module.finrank ℝ (LinearMap.range J.toLinearMap) ≤ N := by
    simpa using (Submodule.finrank_le (LinearMap.range J.toLinearMap))
  have hsum := LinearMap.finrank_range_add_finrank_ker J.toLinearMap
  have hdim : Module.finrank ℝ Params = 31 := by simp [Params]
  omega

/-- Strict separation by a positive inner-product pairing is sufficient
for injectivity, independently of the Jacobian. -/
theorem injective_of_strict_pairing {X Y : Type*} (f : X → Y)
    (pairing : X → X → Y → Y → ℝ)
    (h : ∀ x z, x ≠ z → 0 < pairing x z (f x) (f z))
    (hdiag : ∀ x z y, pairing x z y y = 0) :
    Function.Injective f := by
  intro x z hz
  by_contra hne
  have hp := h x z hne
  rw [hz, hdiag] at hp
  exact (lt_irrefl 0 hp)

/-! Historical two-coordinate slice, with all 29 stored coefficients fixed. -/

def historicalNumerator (n : ℕ) : ℝ :=
  frozenLightBase n * (if n = 3 then (0.0048 : ℝ) else 1)

theorem historical_lightRaw (a e : ℝ) (n : ℕ) :
    lightRaw (frozen a e) n =
      historicalNumerator n * (1 + Real.exp (a * ((n : ℝ) - e)))⁻¹ := by
  simp only [lightRaw, frozen, frozenLightBase, historicalNumerator, Matrix.cons_val]
  split_ifs <;> simp_all <;> ring

/-- Two equal, strictly unfloored logistic outputs with a common numerator
force their logit arguments to agree. No approximation of exp is used. -/
theorem logistic_floor_logit_eq (A x z : ℝ)
    (hx : (1e-12 : ℝ) < max (A * (1 + Real.exp x)⁻¹) 1e-12)
    (h : max (A * (1 + Real.exp x)⁻¹) 1e-12 =
      max (A * (1 + Real.exp z)⁻¹) 1e-12) : x = z := by
  have hx' : (1e-12 : ℝ) < A * (1 + Real.exp x)⁻¹ := by
    by_contra! hh
    rw [max_eq_right hh] at hx
    exact (lt_irrefl _ hx)
  have hz : (1e-12 : ℝ) < A * (1 + Real.exp z)⁻¹ := by
    rw [h] at hx
    by_contra! hh
    rw [max_eq_right hh] at hx
    exact (lt_irrefl _ hx)
  have hA : A ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hx'
    norm_num at hx'
  have hv : A * (1 + Real.exp x)⁻¹ = A * (1 + Real.exp z)⁻¹ := by
    simpa only [max_eq_left hx'.le, max_eq_left hz.le] using h
  have hi := mul_left_cancel₀ hA hv
  have hd : 1 + Real.exp x = 1 + Real.exp z := by
    simpa only [inv_inv] using congrArg (fun v : ℝ => v⁻¹) hi
  exact Real.exp_injective (add_left_cancel hd)

/-- Global uniqueness on the historical two-parameter slice whenever
alpha is positive and the first two observed light rows are unfloored.
The competing parameter pair need not be nearby or inside the optimizer box. -/
theorem historical_two_active_unique (a e b f : ℝ) (ha : 0 < a)
    (h0 : (1e-12 : ℝ) < observed (frozen a e) 0)
    (h1 : (1e-12 : ℝ) < observed (frozen a e) 1)
    (h : observed (frozen a e) = observed (frozen b f)) :
    a = b ∧ e = f := by
  have h0' := congrFun h (0 : Fin 11)
  have h1' := congrFun h (1 : Fin 11)
  change (1e-12 : ℝ) < light (frozen a e) 1 at h0
  change (1e-12 : ℝ) < light (frozen a e) 2 at h1
  change light (frozen a e) 1 = light (frozen b f) 1 at h0'
  change light (frozen a e) 2 = light (frozen b f) 2 at h1'
  simp only [light, historical_lightRaw, Nat.cast_one, Nat.cast_ofNat] at h0 h1 h0' h1'
  have he0 := logistic_floor_logit_eq (historicalNumerator 1) _ _ h0 h0'
  have he1 := logistic_floor_logit_eq (historicalNumerator 2) _ _ h1 h1'
  have hab : a = b := by nlinarith only [he0, he1]
  subst b
  have hp : a * e = a * f := by nlinarith only [he0]
  exact ⟨rfl, mul_left_cancel₀ (ne_of_gt ha) hp⟩

/-- At alpha zero the historical epsilon coordinate is exactly invisible. -/
@[local simp] private theorem frozen_at_0 (a e : ℝ) : frozen a e 0 = 0.3877 := rfl
@[local simp] private theorem frozen_at_1 (a e : ℝ) : frozen a e 1 = -2.3676 := rfl
@[local simp] private theorem frozen_at_2 (a e : ℝ) : frozen a e 2 = -8.2963 := rfl
@[local simp] private theorem frozen_at_3 (a e : ℝ) : frozen a e 3 = 6.8830 := rfl
@[local simp] private theorem frozen_at_4 (a e : ℝ) : frozen a e 4 = -1.7948 := rfl
@[local simp] private theorem frozen_at_5 (a e : ℝ) : frozen a e 5 = -8.6415 := rfl
@[local simp] private theorem frozen_at_6 (a e : ℝ) : frozen a e 6 = -6.1744 := rfl
@[local simp] private theorem frozen_at_7 (a e : ℝ) : frozen a e 7 = 0.9981 := rfl
@[local simp] private theorem frozen_at_8 (a e : ℝ) : frozen a e 8 = 0.0048 := rfl
@[local simp] private theorem frozen_at_9 (a e : ℝ) : frozen a e 9 = 2241.1 := rfl
@[local simp] private theorem frozen_at_10 (a e : ℝ) : frozen a e 10 = 5.0632 := rfl
@[local simp] private theorem frozen_at_11 (a e : ℝ) : frozen a e 11 = 9.4062 := rfl
@[local simp] private theorem frozen_at_12 (a e : ℝ) : frozen a e 12 = 1.6469 := rfl
@[local simp] private theorem frozen_at_13 (a e : ℝ) : frozen a e 13 = 0.2092 := rfl
@[local simp] private theorem frozen_at_14 (a e : ℝ) : frozen a e 14 = 998.7 := rfl
@[local simp] private theorem frozen_at_15 (a e : ℝ) : frozen a e 15 = 0.2427 := rfl
@[local simp] private theorem frozen_at_16 (a e : ℝ) : frozen a e 16 = 98949 := rfl
@[local simp] private theorem frozen_at_17 (a e : ℝ) : frozen a e 17 = 12795 := rfl
@[local simp] private theorem frozen_at_18 (a e : ℝ) : frozen a e 18 = -3.301 := rfl
@[local simp] private theorem frozen_at_19 (a e : ℝ) : frozen a e 19 = 9.039 := rfl
@[local simp] private theorem frozen_at_20 (a e : ℝ) : frozen a e 20 = 61635 := rfl
@[local simp] private theorem frozen_at_21 (a e : ℝ) : frozen a e 21 = -1.189 := rfl
@[local simp] private theorem frozen_at_22 (a e : ℝ) : frozen a e 22 = 17770 := rfl
@[local simp] private theorem frozen_at_23 (a e : ℝ) : frozen a e 23 = 5.615 := rfl
@[local simp] private theorem frozen_at_24 (a e : ℝ) : frozen a e 24 = 8624 := rfl
@[local simp] private theorem frozen_at_25 (a e : ℝ) : frozen a e 25 = -1.264 := rfl
@[local simp] private theorem frozen_at_26 (a e : ℝ) : frozen a e 26 = 4.685 := rfl
@[local simp] private theorem frozen_at_27 (a e : ℝ) : frozen a e 27 = 896077 := rfl
@[local simp] private theorem frozen_at_28 (a e : ℝ) : frozen a e 28 = -952363 := rfl
@[local simp] private theorem frozen_at_29 (a e : ℝ) : frozen a e 29 = a := rfl
@[local simp] private theorem frozen_at_30 (a e : ℝ) : frozen a e 30 = e := rfl

theorem historical_zero_alpha (e f : ℝ) :
    observed (frozen 0 e) = observed (frozen 0 f) := by
  funext i
  fin_cases i
  · change light (frozen 0 e) 1 = light (frozen 0 f) 1
    simp [light, lightRaw, middle, middleRaw, heavy, heavyCorrection]
  · change light (frozen 0 e) 2 = light (frozen 0 f) 2
    simp [light, lightRaw, middle, middleRaw, heavy, heavyCorrection]
  · change light (frozen 0 e) 3 = light (frozen 0 f) 3
    simp [light, lightRaw, middle, middleRaw, heavy, heavyCorrection]
  · change middle (frozen 0 e) 12 = middle (frozen 0 f) 12
    simp [light, lightRaw, middle, middleRaw, heavy, heavyCorrection]
  · change middle (frozen 0 e) 19 = middle (frozen 0 f) 19
    simp [light, lightRaw, middle, middleRaw, heavy, heavyCorrection]
  · change middle (frozen 0 e) 53 = middle (frozen 0 f) 53
    simp [light, lightRaw, middle, middleRaw, heavy, heavyCorrection]
  · change middle (frozen 0 e) 73 = middle (frozen 0 f) 73
    simp [light, lightRaw, middle, middleRaw, heavy, heavyCorrection]
  · change middle (frozen 0 e) 91 = middle (frozen 0 f) 91
    simp [light, lightRaw, middle, middleRaw, heavy, heavyCorrection]
  · change heavy (frozen 0 e) 95 = heavy (frozen 0 f) 95
    simp [light, lightRaw, middle, middleRaw, heavy, heavyCorrection]
  · change heavy (frozen 0 e) 96 = heavy (frozen 0 f) 96
    simp [light, lightRaw, middle, middleRaw, heavy, heavyCorrection]
  · change heavy (frozen 0 e) 123 = heavy (frozen 0 f) 123
    simp [light, lightRaw, middle, middleRaw, heavy, heavyCorrection]

/-! The exact geometry of the transformed rectangle, separated from
the source-specific transcendental threshold enclosures. -/

theorem historical_active_prefix (a t h1 h2 h3 : ℝ)
    (ha : 0 ≤ a) (ht : t ≤ a) (h12 : h2 < 2 * h1)
    (h32 : h3 < h2) :
    (h1 ≤ t → h2 ≤ a + t) ∧
    (h2 ≤ a + t → h3 ≤ 2 * a + t) := by
  constructor <;> intro h <;> linarith

/-- The first-row-only fiber, after the logit fixes t, is an exact interval.
This includes the triangle constraints and all remaining floor inequalities. -/
theorem historical_one_active_interval (a t h2 h3 : ℝ)
    (h32 : h3 ≤ h2) :
    (0 ≤ a ∧ a ≤ 50 ∧ 0 ≤ a - t ∧ a - t ≤ 5 * a ∧
      h2 ≤ a + t ∧ h3 ≤ 2 * a + t) ↔
    max 0 (max t (max (-t / 4) (h2 - t))) ≤ a ∧ a ≤ 50 := by
  simp only [max_le_iff]
  constructor
  · rintro ⟨ha, hu, hz, hza, h2a, _⟩
    exact ⟨⟨ha, by linarith, by linarith, by linarith⟩, hu⟩
  · rintro ⟨⟨ha, ht, hneg, hh⟩, hu⟩
    exact ⟨ha, hu, by linarith, by linarith, by linarith, by linarith⟩

/-- In the one-active region the lower endpoint reaches the upper bound
exactly at the exceptional clipping-edge point. -/
theorem historical_exceptional_endpoint (t h1 h2 : ℝ)
    (ht : t < h1) (h12 : h1 < h2) (hupper : h2 < 40)
    (hp : 0 < h2) (hfeas : h2 - 50 ≤ t) :
    max 0 (max t (max (-t / 4) (h2 - t))) = 50 ↔ t = h2 - 50 := by
  have ht50 : t < 50 := by linarith
  have hneg50 : -t / 4 < 50 := by linarith
  constructor
  · intro h
    have hmax := (floor_eq_iff (0 : ℝ) (max t (max (-t / 4) (h2 - t))) 50).mp h
    have hh : max t (max (-t / 4) (h2 - t)) = 50 := by
      rcases hmax.2.2 with h0 | h0
      · norm_num at h0
      · exact h0
    have hmax2 := (floor_eq_iff t (max (-t / 4) (h2 - t)) 50).mp hh
    have hh2 : max (-t / 4) (h2 - t) = 50 := by
      rcases hmax2.2.2 with h0 | h0
      · linarith
      · exact h0
    have hmax3 := (floor_eq_iff (-t / 4) (h2 - t) 50).mp hh2
    rcases hmax3.2.2 with h0 | h0 <;> linarith
  · intro he
    have hh : h2 - t = 50 := by linarith
    rw [hh, max_eq_right hneg50.le, max_eq_right ht50.le]
    norm_num

/-! A source-model plateau, not an assumed constant map. -/

def plateauCenter : Params := fun i =>
  if i = 7 ∨ i = 14 ∨ i = 17 ∨ i = 28 then -1
  else if i = 8 then 1 else 0

@[local simp] private theorem plateau_at_0 : plateauCenter 0 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((0 : Fin 31) = 7 ∨ 0 = 14 ∨ 0 = 17 ∨ 0 = 28)), if_neg (by decide : ¬ ((0 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_1 : plateauCenter 1 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((1 : Fin 31) = 7 ∨ 1 = 14 ∨ 1 = 17 ∨ 1 = 28)), if_neg (by decide : ¬ ((1 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_2 : plateauCenter 2 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((2 : Fin 31) = 7 ∨ 2 = 14 ∨ 2 = 17 ∨ 2 = 28)), if_neg (by decide : ¬ ((2 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_3 : plateauCenter 3 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((3 : Fin 31) = 7 ∨ 3 = 14 ∨ 3 = 17 ∨ 3 = 28)), if_neg (by decide : ¬ ((3 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_4 : plateauCenter 4 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((4 : Fin 31) = 7 ∨ 4 = 14 ∨ 4 = 17 ∨ 4 = 28)), if_neg (by decide : ¬ ((4 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_5 : plateauCenter 5 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((5 : Fin 31) = 7 ∨ 5 = 14 ∨ 5 = 17 ∨ 5 = 28)), if_neg (by decide : ¬ ((5 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_6 : plateauCenter 6 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((6 : Fin 31) = 7 ∨ 6 = 14 ∨ 6 = 17 ∨ 6 = 28)), if_neg (by decide : ¬ ((6 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_7 : plateauCenter 7 = -1 := by
  unfold plateauCenter
  rw [if_pos (by decide : (7 : Fin 31) = 7 ∨ 7 = 14 ∨ 7 = 17 ∨ 7 = 28)]
@[local simp] private theorem plateau_at_8 : plateauCenter 8 = 1 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((8 : Fin 31) = 7 ∨ 8 = 14 ∨ 8 = 17 ∨ 8 = 28)), if_pos (by decide : ((8 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_9 : plateauCenter 9 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((9 : Fin 31) = 7 ∨ 9 = 14 ∨ 9 = 17 ∨ 9 = 28)), if_neg (by decide : ¬ ((9 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_10 : plateauCenter 10 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((10 : Fin 31) = 7 ∨ 10 = 14 ∨ 10 = 17 ∨ 10 = 28)), if_neg (by decide : ¬ ((10 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_11 : plateauCenter 11 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((11 : Fin 31) = 7 ∨ 11 = 14 ∨ 11 = 17 ∨ 11 = 28)), if_neg (by decide : ¬ ((11 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_12 : plateauCenter 12 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((12 : Fin 31) = 7 ∨ 12 = 14 ∨ 12 = 17 ∨ 12 = 28)), if_neg (by decide : ¬ ((12 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_13 : plateauCenter 13 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((13 : Fin 31) = 7 ∨ 13 = 14 ∨ 13 = 17 ∨ 13 = 28)), if_neg (by decide : ¬ ((13 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_14 : plateauCenter 14 = -1 := by
  unfold plateauCenter
  rw [if_pos (by decide : (14 : Fin 31) = 7 ∨ 14 = 14 ∨ 14 = 17 ∨ 14 = 28)]
@[local simp] private theorem plateau_at_15 : plateauCenter 15 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((15 : Fin 31) = 7 ∨ 15 = 14 ∨ 15 = 17 ∨ 15 = 28)), if_neg (by decide : ¬ ((15 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_16 : plateauCenter 16 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((16 : Fin 31) = 7 ∨ 16 = 14 ∨ 16 = 17 ∨ 16 = 28)), if_neg (by decide : ¬ ((16 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_17 : plateauCenter 17 = -1 := by
  unfold plateauCenter
  rw [if_pos (by decide : (17 : Fin 31) = 7 ∨ 17 = 14 ∨ 17 = 17 ∨ 17 = 28)]
@[local simp] private theorem plateau_at_18 : plateauCenter 18 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((18 : Fin 31) = 7 ∨ 18 = 14 ∨ 18 = 17 ∨ 18 = 28)), if_neg (by decide : ¬ ((18 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_19 : plateauCenter 19 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((19 : Fin 31) = 7 ∨ 19 = 14 ∨ 19 = 17 ∨ 19 = 28)), if_neg (by decide : ¬ ((19 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_20 : plateauCenter 20 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((20 : Fin 31) = 7 ∨ 20 = 14 ∨ 20 = 17 ∨ 20 = 28)), if_neg (by decide : ¬ ((20 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_21 : plateauCenter 21 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((21 : Fin 31) = 7 ∨ 21 = 14 ∨ 21 = 17 ∨ 21 = 28)), if_neg (by decide : ¬ ((21 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_22 : plateauCenter 22 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((22 : Fin 31) = 7 ∨ 22 = 14 ∨ 22 = 17 ∨ 22 = 28)), if_neg (by decide : ¬ ((22 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_23 : plateauCenter 23 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((23 : Fin 31) = 7 ∨ 23 = 14 ∨ 23 = 17 ∨ 23 = 28)), if_neg (by decide : ¬ ((23 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_24 : plateauCenter 24 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((24 : Fin 31) = 7 ∨ 24 = 14 ∨ 24 = 17 ∨ 24 = 28)), if_neg (by decide : ¬ ((24 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_25 : plateauCenter 25 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((25 : Fin 31) = 7 ∨ 25 = 14 ∨ 25 = 17 ∨ 25 = 28)), if_neg (by decide : ¬ ((25 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_26 : plateauCenter 26 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((26 : Fin 31) = 7 ∨ 26 = 14 ∨ 26 = 17 ∨ 26 = 28)), if_neg (by decide : ¬ ((26 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_27 : plateauCenter 27 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((27 : Fin 31) = 7 ∨ 27 = 14 ∨ 27 = 17 ∨ 27 = 28)), if_neg (by decide : ¬ ((27 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_28 : plateauCenter 28 = -1 := by
  unfold plateauCenter
  rw [if_pos (by decide : (28 : Fin 31) = 7 ∨ 28 = 14 ∨ 28 = 17 ∨ 28 = 28)]
@[local simp] private theorem plateau_at_29 : plateauCenter 29 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((29 : Fin 31) = 7 ∨ 29 = 14 ∨ 29 = 17 ∨ 29 = 28)), if_neg (by decide : ¬ ((29 : Fin 31) = 8))]
@[local simp] private theorem plateau_at_30 : plateauCenter 30 = 0 := by
  unfold plateauCenter
  rw [if_neg (by decide : ¬ ((30 : Fin 31) = 7 ∨ 30 = 14 ∨ 30 = 17 ∨ 30 = 28)), if_neg (by decide : ¬ ((30 : Fin 31) = 8))]

/-- Every observed coordinate is exactly at the floor on an ambient
neighborhood of an explicit 31-vector. This supports the stronger
topological lower bound on global observation augmentation. -/
theorem observed_constant_near_plateau :
    ∀ᶠ q in 𝓝 plateauCenter, observed q = fun _ => (1e-12 : ℝ) := by
  have hl (i : Fin 3) :
      (fun q => light q (i.val + 1)) =ᶠ[𝓝 plateauCenter]
        (fun _ => (1e-12 : ℝ)) := by
    apply eventually_max_right (continuous_lightRaw (i.val + 1)).continuousAt
    fin_cases i <;> norm_num [lightRaw, clip, topo]
  have hm (i : Fin 5) :
      (fun q => middle q (middleN i)) =ᶠ[𝓝 plateauCenter]
        (fun _ => (1e-12 : ℝ)) := by
    apply eventually_max_right (contDiff_middleRaw (middleN i)).continuous.continuousAt
    fin_cases i <;> norm_num [middleN, middleRaw, Matrix.cons_val]
  have hh (i : Fin 3) :
      (fun q => heavy q (heavyN i)) =ᶠ[𝓝 plateauCenter]
        (fun _ => (1e-12 : ℝ)) := by
    apply eventually_max_right
      ((continuous_light (heavyN i)).add (continuous_heavyCorrection (heavyN i))).continuousAt
    fin_cases i <;>
      norm_num [heavyN, light, lightRaw, heavyCorrection,
        clip, topo, Matrix.cons_val, Real.rpow_zero]
  filter_upwards [hl 0, hl 1, hl 2, hm 0, hm 1, hm 2, hm 3, hm 4,
    hh 0, hh 1, hh 2] with q l0 l1 l2 m0 m1 m2 m3 m4 h0 h1 h2
  funext i
  fin_cases i
  · change light q 1 = (1e-12 : ℝ)
    exact l0
  · change light q 2 = (1e-12 : ℝ)
    exact l1
  · change light q 3 = (1e-12 : ℝ)
    exact l2
  · change middle q 12 = (1e-12 : ℝ)
    exact m0
  · change middle q 19 = (1e-12 : ℝ)
    exact m1
  · change middle q 53 = (1e-12 : ℝ)
    exact m2
  · change middle q 73 = (1e-12 : ℝ)
    exact m3
  · change middle q 91 = (1e-12 : ℝ)
    exact m4
  · change heavy q 95 = (1e-12 : ℝ)
    exact h0
  · change heavy q 96 = (1e-12 : ℝ)
    exact h1
  · change heavy q 123 = (1e-12 : ℝ)
    exact h2

/-- A canonical representative for the three affine invisible directions.
This does not quotient the other, nonlinear observation aliases. -/
def canonicalInvisible (p : Params) : Params :=
  invisibleFamily p 0 0 (-(p 27))

theorem observed_canonicalInvisible (p : Params) :
    observed (canonicalInvisible p) = observed p :=
  observed_invisibleFamily p 0 0 (-(p 27))

theorem canonicalInvisible_zero_coords (p : Params) :
    canonicalInvisible p 16 = 0 ∧ canonicalInvisible p 18 = 0 ∧
      canonicalInvisible p 27 = 0 := by
  simp [canonicalInvisible, invisibleFamily, shiftHiggs]

/-! Exact historical thresholds. -/
def historicalThreshold (n : ℕ) : ℝ :=
  Real.log (historicalNumerator n / (1e-12 : ℝ) - 1)

theorem historical_numerator_bounds :
    (0.4 : ℝ) < historicalNumerator 1 ∧ historicalNumerator 1 < 1 ∧
    2 < historicalNumerator 2 ∧ historicalNumerator 2 < 12 ∧
    (1e-12 : ℝ) < historicalNumerator 3 ∧ historicalNumerator 3 < 0.1 := by
  have h1 := frozenLightBase_one
  have h2 := frozenLightBase_two
  have h3 := frozenLightBase_three
  have u1 := frozenLightBase_one_upper
  have u2 := frozenLightBase_two_upper
  have u3 := frozenLightBase_three_upper
  norm_num [historicalNumerator]
  norm_num at h1 u1 h2 u2 h3 u3
  exact ⟨h1, u1, h2, u2, by linarith, by linarith⟩

private theorem exp_twenty_lt : Real.exp 20 < (3 : ℝ)^20 := by
  have h : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  calc
    Real.exp 20 = Real.exp 1 ^ (20 : ℕ) := by
      rw [← Real.exp_nat_mul] <;> norm_num
    _ < _ := pow_lt_pow_left₀ h (Real.exp_pos _).le (by decide)

private theorem exp_forty_gt : (2.5 : ℝ)^40 < Real.exp 40 := by
  have h : (2.5 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  calc
    (2.5 : ℝ)^40 < Real.exp 1 ^ (40 : ℕ) :=
      pow_lt_pow_left₀ h (by norm_num) (by decide)
    _ = Real.exp 40 := by rw [← Real.exp_nat_mul] <;> norm_num

theorem historical_threshold_bounds :
    0 < historicalThreshold 3 ∧ historicalThreshold 3 < historicalThreshold 1 ∧
    historicalThreshold 1 < historicalThreshold 2 ∧
    20 < historicalThreshold 1 ∧ historicalThreshold 2 < 40 := by
  obtain ⟨h1,u1,h2,u2,h3,u3⟩ := historical_numerator_bounds
  have h3' : 0.00002 < historicalNumerator 3 := by
    have h := frozenLightBase_three
    norm_num [historicalNumerator]
    norm_num <;> linarith
  norm_num at h1 u1 h2 u2 h3 u3 h3'
  have q1 : 0 < historicalNumerator 1 / (1e-12 : ℝ) - 1 := by norm_num <;> linarith
  have q2 : 0 < historicalNumerator 2 / (1e-12 : ℝ) - 1 := by norm_num <;> linarith
  have q3 : 1 < historicalNumerator 3 / (1e-12 : ℝ) - 1 := by norm_num <;> linarith
  unfold historicalThreshold
  refine ⟨Real.log_pos q3, Real.log_lt_log (by norm_num <;> linarith) (by norm_num <;> linarith),
    Real.log_lt_log q1 (by norm_num <;> linarith), ?_, ?_⟩
  · apply (Real.lt_log_iff_exp_lt q1).2
    have h := exp_twenty_lt
    norm_num at h
    norm_num <;> linarith
  · apply (Real.log_lt_iff_lt_exp q2).2
    have h := exp_forty_gt
    norm_num at h
    norm_num <;> linarith

/-- The exact (unrounded) threshold test, valid for any historical row
whose fixed numerator exceeds twice the floor. -/
theorem historical_light_active_iff (a e : ℝ) (n : ℕ)
    (hA : (2e-12 : ℝ) < historicalNumerator n) :
    (1e-12 : ℝ) < light (frozen a e) n ↔
      a * ((n : ℝ) - e) < historicalThreshold n := by
  have hd : 0 < 1 + Real.exp (a * ((n : ℝ) - e)) := by positivity
  norm_num at hA
  have hq : 0 < historicalNumerator n / (1e-12 : ℝ) - 1 := by norm_num <;> linarith
  rw [light, historical_lightRaw, ← div_eq_mul_inv, lt_max_iff, or_iff_left (lt_irrefl _),
    historicalThreshold, Real.lt_log_iff_exp_lt hq, lt_div_iff₀ hd]
  constructor <;> intro h <;> norm_num at h ⊢ <;> linarith

/-- Exact reconstruction from the canonical quotient representative
and the three eliminated coordinates. -/
theorem invisible_reconstruct (p : Params) :
    invisibleFamily (canonicalInvisible p) (p 16) (p 18) (p 27) = p := by
  funext i
  fin_cases i <;>
    norm_num [canonicalInvisible, invisibleFamily, shiftHiggs] <;> ring

/-- An arbitrarily large change in an unused coordinate is completely
invisible to the actual spectral observations. -/
theorem observed_unbounded_coordinate_fiber (p : Params) (R : ℝ) :
    ∃ q : Params, R < q 16 ∧ observed q = observed p := by
  refine ⟨Function.update p (16 : Fin 31) (R + 1), ?_,
    observed_update_quarkAmp p (R + 1)⟩
  simp

/-- Historical heavy rows remain constant for all real alpha and epsilon,
not only at the previously frozen epsilon=5. -/
theorem historical_heavy_light_floor (a e : ℝ) (i : Fin 3) :
    light (frozen a e) (heavyN i) = (1e-12 : ℝ) := by
  have hn : heavyN i ≠ 3 := by fin_cases i <;> decide
  rw [light, historical_lightRaw, historicalNumerator, if_neg hn, mul_one]
  apply max_eq_right
  have h := mul_neg_of_neg_of_pos (frozenLightBase_heavy_neg i)
    (show 0 < (1 + Real.exp (a * ((heavyN i : ℝ) - e)))⁻¹ by positivity)
  linarith

theorem historical_heavy_constant (a e b f : ℝ) (i : Fin 3) :
    heavy (frozen a e) (heavyN i) = heavy (frozen b f) (heavyN i) := by
  simp only [heavy, historical_heavy_light_floor]
  fin_cases i <;> norm_num [heavyN, heavyCorrection, frozen, Matrix.cons_val]

/-- On the historical slice the complete eleven-output fiber is exactly
the fiber of the three light rows. -/
theorem historical_equal_iff_light (a e b f : ℝ) :
    observed (frozen a e) = observed (frozen b f) ↔
      ∀ i : Fin 3, light (frozen a e) (i.val + 1) =
        light (frozen b f) (i.val + 1) := by
  constructor
  · intro h i
    fin_cases i
    · exact congrFun h (0 : Fin 11)
    · exact congrFun h (1 : Fin 11)
    · exact congrFun h (2 : Fin 11)
  · intro h
    funext i
    fin_cases i
    · exact h 0
    · exact h 1
    · exact h 2
    · norm_num [observed, middle, middleRaw, Matrix.cons_val]
    · norm_num [observed, middle, middleRaw, Matrix.cons_val]
    · norm_num [observed, middle, middleRaw, Matrix.cons_val]
    · norm_num [observed, middle, middleRaw, Matrix.cons_val]
    · norm_num [observed, middle, middleRaw, Matrix.cons_val]
    · exact historical_heavy_constant a e b f 0
    · exact historical_heavy_constant a e b f 1
    · exact historical_heavy_constant a e b f 2

/-- All actual outputs obey the positive source floor. -/
theorem observed_floor_le (p : Params) (i : Fin 11) :
    (1e-12 : ℝ) ≤ observed p i := by
  fin_cases i <;> exact le_max_right _ _

/-- A square real observation block with nonzero determinant attains every
right hand side. Used in the analytical full-range proof. -/
theorem square_system_solvable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : A.det ≠ 0) (y : Fin n → ℝ) :
    ∃ x : Fin n → ℝ, A.mulVec x = y := by
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr
    (isUnit_iff_ne_zero.mpr h)
  have hr := Matrix.rank_of_isUnit A hu
  have hs : Function.Surjective A.mulVecLin := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    change Module.finrank ℝ (LinearMap.range A.mulVecLin) =
      Module.finrank ℝ (Fin n → ℝ)
    simpa [Matrix.rank] using hr
  exact hs y

/-! Global attainable-output range, using actual parameters rather than
extrapolating the local derivative theorem. -/

def middlePolar (m : Fin 5 → ℝ) : ℂ :=
  ⟨m 2, 2241.1 * m 3⟩

theorem middle_polar_linear (m : Fin 5 → ℝ) (x : ℝ) :
    ‖middlePolar m‖ * Real.sin (x + (middlePolar m).arg) =
      m 2 * Real.sin x + (2241.1 * m 3) * Real.cos x := by
  rw [Real.sin_add]
  calc
    _ = (‖middlePolar m‖ * Real.cos (middlePolar m).arg) * Real.sin x +
      (‖middlePolar m‖ * Real.sin (middlePolar m).arg) * Real.cos x := by ring
    _ = _ := by rw [Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]; rfl

/-- The constructive 31-vector, with three linear light controls, five
linearized middle controls and three linear heavy controls. -/
def rangeParams (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) : Params :=
  ![l 0, 0, 0, l 1, l 2, 0, 0, 0, 1,
    ‖middlePolar m‖, 5.0632, 9.4062, 1.6469 + (middlePolar m).arg,
    m 4, m 0, m 1,
    0, 0, 0, 0, h 0, -1.189, 0, 0, h 1, -1.264, 4.685, 0, h 2, 0, 0]

@[local simp] private theorem range_at_0 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 0 = l 0 := rfl
@[local simp] private theorem range_at_1 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 1 = 0 := rfl
@[local simp] private theorem range_at_2 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 2 = 0 := rfl
@[local simp] private theorem range_at_3 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 3 = l 1 := rfl
@[local simp] private theorem range_at_4 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 4 = l 2 := rfl
@[local simp] private theorem range_at_5 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 5 = 0 := rfl
@[local simp] private theorem range_at_6 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 6 = 0 := rfl
@[local simp] private theorem range_at_7 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 7 = 0 := rfl
@[local simp] private theorem range_at_8 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 8 = 1 := rfl
@[local simp] private theorem range_at_9 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 9 = ‖middlePolar m‖ := rfl
@[local simp] private theorem range_at_10 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 10 = 5.0632 := rfl
@[local simp] private theorem range_at_11 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 11 = 9.4062 := rfl
@[local simp] private theorem range_at_12 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 12 = 1.6469 + (middlePolar m).arg := rfl
@[local simp] private theorem range_at_13 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 13 = m 4 := rfl
@[local simp] private theorem range_at_14 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 14 = m 0 := rfl
@[local simp] private theorem range_at_15 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 15 = m 1 := rfl
@[local simp] private theorem range_at_16 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 16 = 0 := rfl
@[local simp] private theorem range_at_17 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 17 = 0 := rfl
@[local simp] private theorem range_at_18 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 18 = 0 := rfl
@[local simp] private theorem range_at_19 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 19 = 0 := rfl
@[local simp] private theorem range_at_20 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 20 = h 0 := rfl
@[local simp] private theorem range_at_21 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 21 = -1.189 := rfl
@[local simp] private theorem range_at_22 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 22 = 0 := rfl
@[local simp] private theorem range_at_23 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 23 = 0 := rfl
@[local simp] private theorem range_at_24 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 24 = h 1 := rfl
@[local simp] private theorem range_at_25 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 25 = -1.264 := rfl
@[local simp] private theorem range_at_26 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 26 = 4.685 := rfl
@[local simp] private theorem range_at_27 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 27 = 0 := rfl
@[local simp] private theorem range_at_28 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 28 = h 2 := rfl
@[local simp] private theorem range_at_29 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 29 = 0 := rfl
@[local simp] private theorem range_at_30 (l : Fin 3 → ℝ) (m : Fin 5 → ℝ) (h : Fin 3 → ℝ) :
    rangeParams l m h 30 = 0 := rfl

private theorem range_lightRaw (l : Fin 3 → ℝ) (m : Fin 5 → ℝ)
    (h : Fin 3 → ℝ) (i : Fin 3) :
    lightRaw (rangeParams l m h) (i.val + 1) =
      (V18LightJacobian.base.mulVec l) i / 2 := by
  fin_cases i <;>
    norm_num [lightRaw, topo, clip, V18LightJacobian.base,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.cons_val] <;> ring

private theorem range_middleRaw (l : Fin 3 → ℝ) (m : Fin 5 → ℝ)
    (h : Fin 3 → ℝ) (i : Fin 5) :
    middleRaw (rangeParams l m h) (middleN i) =
      (V18MiddleJacobian.middle.mulVec m) i := by
  fin_cases i <;>
    norm_num [middleRaw, middleN, V18MiddleJacobian.middle,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.cons_val, ← add_assoc] <;>
    first | (rw [middle_polar_linear]; ring) | (rw [show (6329 / 1250 : ℝ) * _ + (16469 / 10000 + (middlePolar m).arg) = (6329 / 1250 * _ + 16469 / 10000) + (middlePolar m).arg by ring]; rw [middle_polar_linear]; ring)

private theorem range_heavyCorrection (l : Fin 3 → ℝ) (m : Fin 5 → ℝ)
    (h : Fin 3 → ℝ) (i : Fin 3) :
    heavyCorrection (rangeParams l m h) (heavyN i) =
      (V18HeavyJacobian.heavy.mulVec h) i := by
  have hm : V18HeavyJacobian.heavy =
      !![(0.95 : ℝ)^(-1.189 : ℝ), Real.sin (-115.395), 0;
         (0.96 : ℝ)^(-1.189 : ℝ), Real.sin (-116.659), 0;
         (1.23 : ℝ)^(-1.189 : ℝ), 0, 1] := rfl
  rw [hm]
  fin_cases i <;>
    norm_num [heavyCorrection, heavyN, clip,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.cons_val] <;> ring

private theorem range_light_independent (l : Fin 3 → ℝ) (m : Fin 5 → ℝ)
    (h : Fin 3 → ℝ) (n : ℕ) :
    light (rangeParams l m h) n = light (rangeParams l m 0) n := by
  simp [light, lightRaw]

/-- Exact image of the full clipped map: every eleven-vector at or above
the source floor is attained. The proof is constructive block solving;
it does not infer global surjectivity from a full-rank derivative. -/
theorem observed_range_exact :
    Set.range observed = {y | ∀ i : Fin 11, (1e-12 : ℝ) ≤ y i} := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact observed_floor_le p
  · intro hy
    change ∀ i : Fin 11, (1e-12 : ℝ) ≤ y i at hy
    obtain ⟨l, hl⟩ := square_system_solvable V18LightJacobian.base
      (by rw [V18LightJacobian.base_det]; norm_num)
      (![2 * y 0, 2 * y 1, 2 * y 2])
    obtain ⟨m, hm⟩ := square_system_solvable V18MiddleJacobian.middle
      V18MiddleJacobian.middle_det_ne_zero (![y 3, y 4, y 5, y 6, y 7])
    let q := rangeParams l m 0
    obtain ⟨h, hh⟩ := square_system_solvable V18HeavyJacobian.heavy
      V18HeavyJacobian.heavy_det_ne_zero
      (![y 8 - light q 95, y 9 - light q 96, y 10 - light q 123])
    let p := rangeParams l m h
    have hlight (i : Fin 3) :
        light p (i.val + 1) = (![y 0, y 1, y 2] : Fin 3 → ℝ) i := by
      change light (rangeParams l m h) (i.val + 1) = _
      rw [light, range_lightRaw, hl]
      fin_cases i
      · norm_num [Matrix.cons_val]; exact (hy 0)
      · norm_num [Matrix.cons_val]; exact (hy 1)
      · norm_num [Matrix.cons_val]; exact (hy 2)
    have hmiddle (i : Fin 5) :
        middle p (middleN i) = (![y 3, y 4, y 5, y 6, y 7] : Fin 5 → ℝ) i := by
      change middle (rangeParams l m h) (middleN i) = _
      rw [middle, range_middleRaw, hm]
      fin_cases i
      · exact max_eq_left (hy 3)
      · exact max_eq_left (hy 4)
      · exact max_eq_left (hy 5)
      · exact max_eq_left (hy 6)
      · exact max_eq_left (hy 7)
    have hheavy (i : Fin 3) :
        heavy p (heavyN i) = (![y 8, y 9, y 10] : Fin 3 → ℝ) i := by
      change heavy (rangeParams l m h) (heavyN i) = _
      rw [heavy, range_light_independent, range_heavyCorrection, hh]
      fin_cases i
      · change max (light q 95 + (y 8 - light q 95)) 1e-12 = y 8
        rw [show light q 95 + (y 8 - light q 95) = y 8 by ring,
          max_eq_left (hy 8)]
      · change max (light q 96 + (y 9 - light q 96)) 1e-12 = y 9
        rw [show light q 96 + (y 9 - light q 96) = y 9 by ring,
          max_eq_left (hy 9)]
      · change max (light q 123 + (y 10 - light q 123)) 1e-12 = y 10
        rw [show light q 123 + (y 10 - light q 123) = y 10 by ring,
          max_eq_left (hy 10)]
    refine ⟨p, ?_⟩
    funext i
    fin_cases i
    · exact hlight 0
    · exact hlight 1
    · exact hlight 2
    · exact hmiddle 0
    · exact hmiddle 1
    · exact hmiddle 2
    · exact hmiddle 3
    · exact hmiddle 4
    · exact hheavy 0
    · exact hheavy 1
    · exact hheavy 2

end ReyesMath.V18Forward
