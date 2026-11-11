import Kissing8.Positivity

/-!
# The two-point (Delsarte) bound in `ℝ⁸`: at most 240 unit vectors with inner products `≤ 1/2`

The polynomial `fL t = (t + 1) (t + 1/2)² t² (t - 1/2)` of Levenshtein and of Odlyzko and Sloane (1979)

* is `≤ 0` on `[-1, 1/2]` (`fL_nonpos`: a product of nonnegative factors and `t - 1/2 ≤ 0`);
* is a nonnegative combination `∑_{k ≤ 6} alpha k · Zg 8 k t 1 1` of the Gegenbauer polynomials of `S⁷`
  (`fL_eq`), with `alpha 0 = 3/320`;
* has `fL 1 = 9/4`.

For unit vectors `x₁, …, x_N` of `ℝ⁸` with `⟪xᵢ, xⱼ⟫ ≤ 1/2` (`i ≠ j`), the sum `S = ∑ i j, fL ⟪xᵢ, xⱼ⟫` is at most
`N · 9/4` (only the diagonal terms can be positive) and at least `3/320 · N²` (the `k = 0` term; the others are
`≥ 0` by positive semidefiniteness, `psd8`). Hence `N ≤ (9/4) / (3/320) = 240` (`card_le_240`).
-/

namespace Kissing8

open Finset
open scoped RealInnerProductSpace

/-- The polynomial of the two-point bound. -/
noncomputable def fL (t : ℝ) : ℝ := (t + 1) * (t + 1 / 2) ^ 2 * t ^ 2 * (t - 1 / 2)

/-- Its coefficients in the `k!`-scaled Gegenbauer polynomials `Zg 8 k t 1 1` of `S⁷`. -/
noncomputable def alpha : ℕ → ℝ
  | 0 => 3 / 320
  | 1 => 1 / 80
  | 2 => 5 / 896
  | 3 => 13 / 8960
  | 4 => 19 / 92160
  | 5 => 1 / 53760
  | 6 => 1 / 1290240
  | _ => 0

theorem alpha_nonneg (k : ℕ) : 0 ≤ alpha k := by
  unfold alpha
  split <;> norm_num

theorem fL_eq (t : ℝ) : fL t = ∑ k ∈ range 7, alpha k * Zg 8 k t 1 1 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, alpha, Zg, fL]
  push_cast
  ring

theorem fL_nonpos {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1 / 2) : fL t ≤ 0 := by
  unfold fL
  have h : 0 ≤ (t + 1) * (t + 1 / 2) ^ 2 * t ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (sq_nonneg _)
  exact mul_nonpos_of_nonneg_of_nonpos h (by linarith)

theorem fL_one : fL 1 = 9 / 4 := by
  unfold fL
  norm_num

/-- Positive semidefiniteness for unit vectors of `ℝ⁸`, with all weights `1`. -/
theorem psd8_unit (k : ℕ) (hk : k ≤ 6) {N : ℕ} (x : Fin N → EuclideanSpace ℝ (Fin 8))
    (hx : ∀ i, ‖x i‖ = 1) : 0 ≤ ∑ i, ∑ j, Zg 8 k ⟪x i, x j⟫ 1 1 := by
  have h := psd8 k hk N (fun i l => x i l) (fun _ => 1)
  have hd : ∀ i j, dot (fun l => x i l) (fun l => x j l) = ⟪x i, x j⟫ := by
    intro i j
    simp [dot, PiLp.inner_apply, mul_comm]
  have h1 : ∀ i, ⟪x i, x i⟫ = 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq, hx i]
    norm_num
  simpa [hd, h1, hx] using h

/-- **The two-point bound.** At most 240 unit vectors of `ℝ⁸` have pairwise inner products `≤ 1/2`. -/
theorem card_le_240 {N : ℕ} (x : Fin N → EuclideanSpace ℝ (Fin 8)) (hx : ∀ i, ‖x i‖ = 1)
    (hxy : ∀ i j, i ≠ j → ⟪x i, x j⟫ ≤ 1 / 2) : N ≤ 240 := by
  have h1 : ∀ i, ⟪x i, x i⟫ = 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq, hx i]
    norm_num
  have hlow1 : ∀ i j, -1 ≤ ⟪x i, x j⟫ := by
    intro i j
    have h := abs_real_inner_le_norm (x i) (x j)
    rw [hx i, hx j] at h
    linarith [neg_abs_le ⟪x i, x j⟫]
  set S := ∑ i, ∑ j, fL ⟪x i, x j⟫ with hS
  -- `S ≤ N · 9/4`: only the diagonal terms can be positive
  have hup : S ≤ N * (9 / 4) := by
    have hrow : ∀ i, ∑ j, fL ⟪x i, x j⟫ ≤ 9 / 4 := by
      intro i
      rw [← Finset.add_sum_erase _ _ (mem_univ i), h1 i, fL_one]
      have hrest : ∑ j ∈ univ.erase i, fL ⟪x i, x j⟫ ≤ 0 :=
        sum_nonpos fun j hj => fL_nonpos (hlow1 i j) (hxy i j (ne_of_mem_erase hj).symm)
      linarith
    calc S ≤ ∑ _i : Fin N, (9 / 4 : ℝ) := sum_le_sum fun i _ => hrow i
      _ = N * (9 / 4) := by simp
  -- `S ≥ 3/320 · N²`: the constant term, plus nonnegative terms
  have hswap : ∀ F : ℕ → Fin N → Fin N → ℝ,
      ∑ i, ∑ j, ∑ k ∈ range 7, F k i j = ∑ k ∈ range 7, ∑ i, ∑ j, F k i j := by
    intro F
    calc ∑ i, ∑ j, ∑ k ∈ range 7, F k i j = ∑ i, ∑ k ∈ range 7, ∑ j, F k i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k ∈ range 7, ∑ i, ∑ j, F k i j := Finset.sum_comm
  have hexp : S = ∑ k ∈ range 7, alpha k * ∑ i, ∑ j, Zg 8 k ⟪x i, x j⟫ 1 1 := by
    simp_rw [hS, fL_eq, Finset.mul_sum]
    exact hswap _
  have hlow : 3 / 320 * (N : ℝ) ^ 2 ≤ S := by
    rw [hexp, Finset.sum_range_succ']
    have h0 : alpha 0 * ∑ i : Fin N, ∑ j : Fin N, Zg 8 0 ⟪x i, x j⟫ 1 1 = 3 / 320 * (N : ℝ) ^ 2 := by
      simp [alpha, Zg]
      ring
    have hrest : 0 ≤ ∑ k ∈ range 6, alpha (k + 1) * ∑ i, ∑ j, Zg 8 (k + 1) ⟪x i, x j⟫ 1 1 :=
      sum_nonneg fun k hk => mul_nonneg (alpha_nonneg _)
        (psd8_unit (k + 1) (by rw [Finset.mem_range] at hk; omega) x hx)
    linarith
  have hN : (N : ℝ) ≤ 240 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · have hpos : (0 : ℝ) < N := by exact_mod_cast h
      nlinarith
  exact_mod_cast hN

end Kissing8
