import ThomsonGen.ThreePoint

-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7),
-- via lean/Kissing4/Kernel.lean of this package: `Q5` from `ThreePoint.Q3`, `Y5` from `ThreePoint.Y3`,
-- `S5` from `ThreePoint.S3`, `S5_swap12` from `ThreePoint.S3_swap12`, `S5_swap23` from `ThreePoint.S3_swap23`,
-- `inner_coords5` from `ThreePoint.inner_coords`, `normsq_coords5` from `ThreePoint.normsq_coords`,
-- `gram_det_nonneg5` from `ThreePoint.gram_det_nonneg`, `gramOK_inner5` from `ThreePoint.gramOK_inner`,
-- `Rk5` from `ThreePoint.Rk`, `matDot_Rk5` from `ThreePoint.matDot_Rk`,
-- `sum_matDot_Rk5` from `ThreePoint.sum_matDot_Rk`, `three_point_identity5` from `ThreePoint.three_point_identity`.

/-!
# Kernels of the sphere `S⁴` and the three-point identity in `ℝ⁵`

The upstream three-point development (`ThomsonN7.ThreePoint`) treats unit vectors of `ℝ³` and the kernels
`Q3`, `S3` of `S²`. This file supplies the `ℝ⁵` / `S⁴` counterparts of everything that depends on the
dimension or on the kernel: the Gegenbauer-type recursion `Q5`, its block matrices `Y5`, `S5`, the reduced
kernel `Rk5`, the Gram-determinant bound for three unit vectors of `ℝ⁵`, and the exact three-point identity.
All dimension-free combinatorics (`dsum`, `Rs`, `GramOK`, `matDot`, ...) is imported unchanged.
-/

open scoped RealInnerProductSpace

namespace Kissing5

open ThomsonN7 ThomsonN7.ThreePoint

/-- Five-dimensional Euclidean space. -/
abbrev R5 := EuclideanSpace ℝ (Fin 5)

/-- The kernel entering the three-point matrices of `S⁴`, built from the Gegenbauer kernel of the tangent `S³`:
where `(1-u²)(1-v²) > 0`, `Q5 k u v t = (k+1)! · ((1-u²)(1-v²))^{k/2} U_k(s)/(k+1)` with `s = (t-uv)/√((1-u²)(1-v²))`
and `U_k` the Chebyshev polynomial of the second kind; in general it is the polynomial in `u, v, t` defined by
`Q5 0 = 1`, `Q5 1 = 2 (t - uv)` and the three-term recursion coded below. It is `Kissing8.Zg 4 k` evaluated at
`(t - uv, 1 - u², 1 - v²)` (`Q5_eq_Zg` in `Kissing5.Positivity`). -/
noncomputable def Q5 : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, _, _, _ => 1
  | 1, u, v, t => 2 * (t - u * v)
  | k + 2, u, v, t =>
      (2 * (k : ℝ) + 4) * (t - u * v) * Q5 (k + 1) u v t
        - ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((1 - u ^ 2) * (1 - v ^ 2)) * Q5 k u v t

/-- Block matrix `(a, b) ↦ uᵃ vᵇ Q5 k u v t` of size `m × m`. -/
noncomputable def Y5 (m k : ℕ) (u v t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a b => u ^ (a : ℕ) * v ^ (b : ℕ) * Q5 k u v t

/-- Average of `Y5` over the six orderings of its three arguments. -/
noncomputable def S5 (m k : ℕ) (u v t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (1 / 6 : ℝ) •
    (Y5 m k u v t + Y5 m k u t v + Y5 m k v u t + Y5 m k v t u + Y5 m k t u v + Y5 m k t v u)

theorem S5_swap12 (m k : ℕ) (u v t : ℝ) : S5 m k u v t = S5 m k v u t := by
  ext i j
  simp only [S5, Y5, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul]
  ring

theorem S5_swap23 (m k : ℕ) (u v t : ℝ) : S5 m k u v t = S5 m k u t v := by
  ext i j
  simp only [S5, Y5, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul]
  ring

/-- The reduced matrix kernel for `n` points, built from `S5`. -/
noncomputable def Rk5 (n m k : ℕ) (u v t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  ((n : ℝ) - 2) • S5 m k u v t + (S5 m k u u 1 + S5 m k v v 1 + S5 m k t t 1)
    + (1 / ((n : ℝ) - 1)) • S5 m k 1 1 1

theorem matDot_Rk5 {m : ℕ} (F : Matrix (Fin m) (Fin m) ℝ) (n k : ℕ) (u v t : ℝ) :
    matDot F (Rk5 n m k u v t) = Rs (fun u v t => matDot F (S5 m k u v t)) n u v t := by
  simp only [Rk5, Rs, matDot_add, matDot_smul]
  ring

theorem sum_matDot_Rk5 (K n : ℕ) (m : ℕ → ℕ)
    (F : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ) (u v t : ℝ) :
    ∑ k ∈ Finset.range K, matDot (F k) (Rk5 n (m k) k u v t)
      = Rs (fun u v t => ∑ k ∈ Finset.range K, matDot (F k) (S5 (m k) k u v t)) n u v t := by
  simp only [matDot_Rk5, Rs, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]

/-! ### Gram determinant in `ℝ⁵` -/

/-- The inner product of two vectors of `ℝ⁵` in coordinates. -/
theorem inner_coords5 (x y : R5) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4 := by
  simp [PiLp.inner_apply, Fin.sum_univ_five, mul_comm]

/-- A unit vector of `ℝ⁵` has coordinates of squared sum `1`. -/
theorem normsq_coords5 (x : R5) (hx : ‖x‖ = 1) :
    x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 = 1 := by
  have := real_inner_self_eq_norm_sq x
  rw [hx, inner_coords5] at this
  nlinarith [this]

/-- Cauchy–Binet for a `3 × 5` matrix: the Gram determinant is the sum of the squares of the ten
`3 × 3` minors. -/
theorem gram_det_eq_minors5 (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 z0 z1 z2 z3 z4 : ℝ) :
    (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) * (y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 + y4 ^ 2)
        * (z0 ^ 2 + z1 ^ 2 + z2 ^ 2 + z3 ^ 2 + z4 ^ 2)
      + 2 * (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4) * (x0 * z0 + x1 * z1 + x2 * z2 + x3 * z3 + x4 * z4)
        * (y0 * z0 + y1 * z1 + y2 * z2 + y3 * z3 + y4 * z4)
      - (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) * (y0 * z0 + y1 * z1 + y2 * z2 + y3 * z3 + y4 * z4) ^ 2
      - (y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 + y4 ^ 2) * (x0 * z0 + x1 * z1 + x2 * z2 + x3 * z3 + x4 * z4) ^ 2
      - (z0 ^ 2 + z1 ^ 2 + z2 ^ 2 + z3 ^ 2 + z4 ^ 2) * (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4) ^ 2
    = (x0 * (y1 * z2 - y2 * z1) - x1 * (y0 * z2 - y2 * z0) + x2 * (y0 * z1 - y1 * z0)) ^ 2
      + (x0 * (y1 * z3 - y3 * z1) - x1 * (y0 * z3 - y3 * z0) + x3 * (y0 * z1 - y1 * z0)) ^ 2
      + (x0 * (y1 * z4 - y4 * z1) - x1 * (y0 * z4 - y4 * z0) + x4 * (y0 * z1 - y1 * z0)) ^ 2
      + (x0 * (y2 * z3 - y3 * z2) - x2 * (y0 * z3 - y3 * z0) + x3 * (y0 * z2 - y2 * z0)) ^ 2
      + (x0 * (y2 * z4 - y4 * z2) - x2 * (y0 * z4 - y4 * z0) + x4 * (y0 * z2 - y2 * z0)) ^ 2
      + (x0 * (y3 * z4 - y4 * z3) - x3 * (y0 * z4 - y4 * z0) + x4 * (y0 * z3 - y3 * z0)) ^ 2
      + (x1 * (y2 * z3 - y3 * z2) - x2 * (y1 * z3 - y3 * z1) + x3 * (y1 * z2 - y2 * z1)) ^ 2
      + (x1 * (y2 * z4 - y4 * z2) - x2 * (y1 * z4 - y4 * z1) + x4 * (y1 * z2 - y2 * z1)) ^ 2
      + (x1 * (y3 * z4 - y4 * z3) - x3 * (y1 * z4 - y4 * z1) + x4 * (y1 * z3 - y3 * z1)) ^ 2
      + (x2 * (y3 * z4 - y4 * z3) - x3 * (y2 * z4 - y4 * z2) + x4 * (y2 * z3 - y3 * z2)) ^ 2 := by
  ring

/-- The Gram determinant of three unit vectors of `ℝ⁵` is nonnegative. -/
theorem gram_det_nonneg5 (x y z : R5) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    0 ≤ 1 + 2 * ⟪x, y⟫ * ⟪x, z⟫ * ⟪y, z⟫ - ⟪x, y⟫ ^ 2 - ⟪x, z⟫ ^ 2 - ⟪y, z⟫ ^ 2 := by
  have hx' := normsq_coords5 x hx
  have hy' := normsq_coords5 y hy
  have hz' := normsq_coords5 z hz
  have h := gram_det_eq_minors5 (x 0) (x 1) (x 2) (x 3) (x 4) (y 0) (y 1) (y 2) (y 3) (y 4) (z 0) (z 1) (z 2) (z 3) (z 4)
  rw [hx', hy', hz'] at h
  rw [inner_coords5, inner_coords5, inner_coords5]
  have hsq : 0 ≤ (x 0 * (y 1 * z 2 - y 2 * z 1) - x 1 * (y 0 * z 2 - y 2 * z 0) + x 2 * (y 0 * z 1 - y 1 * z 0)) ^ 2
      + (x 0 * (y 1 * z 3 - y 3 * z 1) - x 1 * (y 0 * z 3 - y 3 * z 0) + x 3 * (y 0 * z 1 - y 1 * z 0)) ^ 2
      + (x 0 * (y 1 * z 4 - y 4 * z 1) - x 1 * (y 0 * z 4 - y 4 * z 0) + x 4 * (y 0 * z 1 - y 1 * z 0)) ^ 2
      + (x 0 * (y 2 * z 3 - y 3 * z 2) - x 2 * (y 0 * z 3 - y 3 * z 0) + x 3 * (y 0 * z 2 - y 2 * z 0)) ^ 2
      + (x 0 * (y 2 * z 4 - y 4 * z 2) - x 2 * (y 0 * z 4 - y 4 * z 0) + x 4 * (y 0 * z 2 - y 2 * z 0)) ^ 2
      + (x 0 * (y 3 * z 4 - y 4 * z 3) - x 3 * (y 0 * z 4 - y 4 * z 0) + x 4 * (y 0 * z 3 - y 3 * z 0)) ^ 2
      + (x 1 * (y 2 * z 3 - y 3 * z 2) - x 2 * (y 1 * z 3 - y 3 * z 1) + x 3 * (y 1 * z 2 - y 2 * z 1)) ^ 2
      + (x 1 * (y 2 * z 4 - y 4 * z 2) - x 2 * (y 1 * z 4 - y 4 * z 1) + x 4 * (y 1 * z 2 - y 2 * z 1)) ^ 2
      + (x 1 * (y 3 * z 4 - y 4 * z 3) - x 3 * (y 1 * z 4 - y 4 * z 1) + x 4 * (y 1 * z 3 - y 3 * z 1)) ^ 2
      + (x 2 * (y 3 * z 4 - y 4 * z 3) - x 3 * (y 2 * z 4 - y 4 * z 2) + x 4 * (y 2 * z 3 - y 3 * z 2)) ^ 2 := by positivity
  linarith

/-- Three unit vectors of `ℝ⁵` have a Gram triple in the region `GramOK`. -/
theorem gramOK_inner5 (x y z : R5) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    GramOK ⟪x, y⟫ ⟪x, z⟫ ⟪y, z⟫ := by
  have h1 : ∀ a b : R5, ‖a‖ = 1 → ‖b‖ = 1 → ⟪a, b⟫ ^ 2 ≤ 1 := by
    intro a b ha hb
    have := abs_real_inner_le_norm a b
    rw [ha, hb, mul_one] at this
    exact (sq_le_one_iff_abs_le_one _).mpr this
  refine ⟨h1 x y hx hy, h1 x z hx hz, h1 y z hy hz, ?_⟩
  have := gram_det_nonneg5 x y z hx hy hz
  linarith

/-- The exact three-point identity for `n ≥ 3` unit vectors of `ℝ⁵`, for any symmetric kernel `s`. -/
theorem three_point_identity5 {n : ℕ} (hn : 3 ≤ n) (s : ℝ → ℝ → ℝ → ℝ)
    (hs12 : ∀ u v t, s u v t = s v u t) (hs23 : ∀ u v t, s u v t = s u t v)
    (H : ℝ → ℝ) (e : ℝ) (x : Fin n → R5) (hx : ∀ i, ‖x i‖ = 1) :
    dsum (fun i j l => ((H ⟪x i, x j⟫ + H ⟪x i, x l⟫ + H ⟪x j, x l⟫) / 3
        - e / (n.choose 2 : ℝ)) - Rs s n ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫)
      + ((n : ℝ) - 2) * ∑ i, ∑ j, ∑ l, s ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫
    = 2 * ((n : ℝ) - 2) * (∑ i, ∑ j ∈ Finset.Ioi i, H ⟪x i, x j⟫ - e) := by
  have hsymm : ∀ i j, ⟪x i, x j⟫ = ⟪x j, x i⟫ := fun i j => (real_inner_comm _ _).symm
  have hdiag : ∀ i, ⟪x i, x i⟫ = 1 := fun i => by
    rw [real_inner_self_eq_norm_sq, hx i]; norm_num
  rw [dsum_sub, dsum_Rs hn s hs12 hs23 (fun i j => ⟪x i, x j⟫) hsymm hdiag,
    dsum_H hn H (e / (n.choose 2 : ℝ)) (fun i j => ⟪x i, x j⟫) hsymm]
  have hc : (n.choose 2 : ℝ) = n * (n - 1) / 2 := Nat.cast_choose_two ℝ n
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by intro h; linarith
  have hn0 : (n : ℝ) ≠ 0 := by intro h; linarith
  rw [hc]
  field_simp
  ring

end Kissing5
