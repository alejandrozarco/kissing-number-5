import Mathlib
import Kissing5.Cert.Check  -- build order only: keeps `lake build` sequential on a shared machine

-- Adapted from `Kissing4.TwentyFour` (this repository's dimension-4 lower bound): five coordinates instead of four,
-- and the points scaled by `√2`.

/-!
# Forty kissing balls in `ℝ⁵`

The forty roots of `D₅`, the vectors `v` with two coordinates `±1` and three coordinates `0`, scaled by `√2`. Each
point `√2 v` is at distance `2` from the origin (`‖v‖² = 2`), and two different ones are at least `2` apart
(`‖v - w‖² ≥ 2`). Both facts are checked in integer arithmetic on the vectors `v`.
-/

namespace Kissing5
namespace Forty

/-- The integer vector `v` of the `i`-th point. -/
def P : Fin 40 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0],
    ![1, -1, 0, 0, 0],
    ![-1, 1, 0, 0, 0],
    ![-1, -1, 0, 0, 0],
    ![1, 0, 1, 0, 0],
    ![1, 0, -1, 0, 0],
    ![-1, 0, 1, 0, 0],
    ![-1, 0, -1, 0, 0],
    ![1, 0, 0, 1, 0],
    ![1, 0, 0, -1, 0],
    ![-1, 0, 0, 1, 0],
    ![-1, 0, 0, -1, 0],
    ![1, 0, 0, 0, 1],
    ![1, 0, 0, 0, -1],
    ![-1, 0, 0, 0, 1],
    ![-1, 0, 0, 0, -1],
    ![0, 1, 1, 0, 0],
    ![0, 1, -1, 0, 0],
    ![0, -1, 1, 0, 0],
    ![0, -1, -1, 0, 0],
    ![0, 1, 0, 1, 0],
    ![0, 1, 0, -1, 0],
    ![0, -1, 0, 1, 0],
    ![0, -1, 0, -1, 0],
    ![0, 1, 0, 0, 1],
    ![0, 1, 0, 0, -1],
    ![0, -1, 0, 0, 1],
    ![0, -1, 0, 0, -1],
    ![0, 0, 1, 1, 0],
    ![0, 0, 1, -1, 0],
    ![0, 0, -1, 1, 0],
    ![0, 0, -1, -1, 0],
    ![0, 0, 1, 0, 1],
    ![0, 0, 1, 0, -1],
    ![0, 0, -1, 0, 1],
    ![0, 0, -1, 0, -1],
    ![0, 0, 0, 1, 1],
    ![0, 0, 0, 1, -1],
    ![0, 0, 0, -1, 1],
    ![0, 0, 0, -1, -1]]

theorem P_norm : ∀ i, P i 0 ^ 2 + P i 1 ^ 2 + P i 2 ^ 2 + P i 3 ^ 2 + P i 4 ^ 2 = 2 := by
  decide +kernel

theorem P_sep : ∀ i j, i ≠ j →
    2 ≤ (P i 0 - P j 0) ^ 2 + (P i 1 - P j 1) ^ 2 + (P i 2 - P j 2) ^ 2 + (P i 3 - P j 3) ^ 2
      + (P i 4 - P j 4) ^ 2 := by
  decide +kernel

/-- The `i`-th point, `√2 · P i`. -/
noncomputable def pt (i : Fin 40) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 fun k => √2 * (P i k : ℝ)

/-- A point of `ℝ⁵` whose squared coordinates sum to `4` has norm `2`. -/
lemma norm_eq_two {x : EuclideanSpace ℝ (Fin 5)}
    (h : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 = 4) : ‖x‖ = 2 := by
  have hs : ‖x‖ ^ 2 = 4 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_five]
    exact h
  nlinarith [norm_nonneg x]

/-- Two points of `ℝ⁵` whose squared coordinate differences sum to at least `4` are at least `2` apart. -/
lemma two_le_dist {x y : EuclideanSpace ℝ (Fin 5)}
    (h : 4 ≤ (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 + (x 3 - y 3) ^ 2 + (x 4 - y 4) ^ 2) :
    2 ≤ dist x y := by
  rw [dist_eq_norm]
  have hs : 4 ≤ ‖x - y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_five]
    simpa only [PiLp.sub_apply] using h
  nlinarith [norm_nonneg (x - y)]

lemma sq_sqrt_two : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)

theorem norm_pt (i : Fin 40) : ‖pt i‖ = 2 := by
  apply norm_eq_two
  simp only [pt, PiLp.toLp_apply, mul_pow, sq_sqrt_two]
  have h : (P i 0 : ℝ) ^ 2 + (P i 1 : ℝ) ^ 2 + (P i 2 : ℝ) ^ 2 + (P i 3 : ℝ) ^ 2 + (P i 4 : ℝ) ^ 2 = 2 := by
    exact_mod_cast P_norm i
  linarith

theorem dist_pt (i j : Fin 40) (hij : i ≠ j) : 2 ≤ dist (pt i) (pt j) := by
  apply two_le_dist
  simp only [pt, PiLp.toLp_apply, ← mul_sub, mul_pow, sq_sqrt_two]
  have h : 2 ≤ ((P i 0 : ℝ) - P j 0) ^ 2 + ((P i 1 : ℝ) - P j 1) ^ 2 + ((P i 2 : ℝ) - P j 2) ^ 2
      + ((P i 3 : ℝ) - P j 3) ^ 2 + ((P i 4 : ℝ) - P j 4) ^ 2 := by
    exact_mod_cast P_sep i j hij
  linarith

theorem pt_injective : Function.Injective pt := by
  intro i j h
  by_contra hij
  have := dist_pt i j hij
  rw [h, dist_self] at this
  norm_num at this

end Forty
end Kissing5
