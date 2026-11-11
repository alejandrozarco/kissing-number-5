import Mathlib

/-!
# Solid Gegenbauer kernels and positive semidefiniteness, one dimension at a time

The two-point (Delsarte) bound in `ℝ⁸` needs, for `k ≤ 6`, that the Gegenbauer kernel of the sphere `S⁷` is positive
semidefinite: `∑ i j, cᵢ cⱼ C_k(⟪xᵢ, xⱼ⟫) ≥ 0` for unit vectors `xᵢ`. This file sets up the induction on the dimension
that proves it.

* `Zg d k s p q`: the `k!`-scaled solid Gegenbauer kernel of `ℝ^d` (`d ≥ 3`) in `s = ⟪x, x'⟫`, `p = ‖x‖²`,
  `q = ‖x'‖²`, by its three-term recursion. On unit vectors (`p = q = 1`) it is `k!` times the Gegenbauer polynomial
  `C_k^{(d-2)/2}(s)`.
* `Zc m s p q`: the solid Chebyshev kernel of `ℝ²`, `Re((y₀ + i y₁)^m (y₀' - i y₁')^m)` (`Zc_eq_re`).
* `PSD d Z`: the kernel `Z` is positive semidefinite on all finite families of vectors of `ℝ^d` (coordinates
  `Fin d → ℝ`, inner product `dot`).
* `psd_Zc`: the base case in `ℝ²`, a squared modulus.
* `psd_step`: if a kernel of `ℝ^(d+1)` splits, along the first coordinate, as a nonnegative combination of products
  `B(a) B(a') Z_m(y, y')` with kernels `Z_m` that are positive semidefinite on `ℝ^d`, then it is positive
  semidefinite on `ℝ^(d+1)`. The splittings themselves are the generated identities `Kissing8.Addition3` …
  `Kissing8.Addition8`.
-/

namespace Kissing8

open Finset

/-- The `k!`-scaled solid Gegenbauer kernel of `ℝ^d` (`d ≥ 3`) in `s = ⟪x, x'⟫`, `p = ‖x‖²`, `q = ‖x'‖²`. -/
noncomputable def Zg (d : ℕ) : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, _, _, _ => 1
  | 1, s, _, _ => ((d : ℝ) - 2) * s
  | k + 2, s, p, q => (2 * (k : ℝ) + d) * s * Zg d (k + 1) s p q
      - ((k : ℝ) + 1) * ((k : ℝ) + d - 2) * (p * q) * Zg d k s p q

/-- The solid Chebyshev kernel of `ℝ²` in `s = ⟪y, y'⟫`, `p = ‖y‖²`, `q = ‖y'‖²`. -/
noncomputable def Zc : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, _, _, _ => 1
  | 1, s, _, _ => s
  | m + 2, s, p, q => 2 * s * Zc (m + 1) s p q - (p * q) * Zc m s p q

/-- The standard inner product of coordinate vectors. -/
def dot {d : ℕ} (u v : Fin d → ℝ) : ℝ := ∑ l, u l * v l

/-- `Z` is a positive semidefinite kernel on `ℝ^d`: for all vectors `yᵢ` and weights `cᵢ`,
`∑ i j, cᵢ cⱼ Z(⟪yᵢ, yⱼ⟫, ‖yᵢ‖², ‖yⱼ‖²) ≥ 0`. -/
def PSD (d : ℕ) (Z : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (y : Fin n → Fin d → ℝ) (c : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j * Z (dot (y i) (y j)) (dot (y i) (y i)) (dot (y j) (y j))

theorem dot_succ {d : ℕ} (u v : Fin (d + 1) → ℝ) :
    dot u v = u 0 * v 0 + dot (Fin.tail u) (Fin.tail v) := by
  simp [dot, Fin.sum_univ_succ, Fin.tail]

/-- The Chebyshev kernel is the real part of `(z z̄')^m`. -/
theorem Zc_eq_re (m : ℕ) (z z' : ℂ) :
    Zc m (z * (starRingEnd ℂ) z').re (Complex.normSq z) (Complex.normSq z') =
      ((z * (starRingEnd ℂ) z') ^ m).re := by
  set w := z * (starRingEnd ℂ) z' with hw
  have hn : Complex.normSq z * Complex.normSq z' = Complex.normSq w := by
    simp [hw, Complex.normSq_mul, Complex.normSq_conj]
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => simp [Zc]
    | 1 => simp [Zc]
    | m + 2 =>
      have h2 : w ^ 2 = ((2 * w.re : ℝ) : ℂ) * w - ((Complex.normSq w : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [pow_two, Complex.normSq_apply] <;> ring
      have key : w ^ (m + 2) = ((2 * w.re : ℝ) : ℂ) * w ^ (m + 1) - ((Complex.normSq w : ℝ) : ℂ) * w ^ m := by
        calc w ^ (m + 2) = w ^ 2 * w ^ m := by ring
          _ = _ := by rw [h2]; ring
      rw [Zc, ih (m + 1) (by omega), ih m (by omega), hn, key, Complex.sub_re, Complex.re_ofReal_mul,
        Complex.re_ofReal_mul]

/-- Base case: the Chebyshev kernels are positive semidefinite on `ℝ²`. -/
theorem psd_Zc (m : ℕ) : PSD 2 (Zc m) := by
  intro n y c
  let z : Fin n → ℂ := fun i => ⟨y i 0, y i 1⟩
  let u : Fin n → ℂ := fun i => (c i : ℂ) * z i ^ m
  have hdot : ∀ i j, dot (y i) (y j) = (z i * (starRingEnd ℂ) (z j)).re := by
    intro i j
    simp [dot, Fin.sum_univ_two, z, Complex.mul_re]
  have hns : ∀ i, dot (y i) (y i) = Complex.normSq (z i) := by
    intro i
    simp [dot, Fin.sum_univ_two, z, Complex.normSq_apply]
  have hterm : ∀ i j, c i * c j * Zc m (dot (y i) (y j)) (dot (y i) (y i)) (dot (y j) (y j)) =
      (u i * (starRingEnd ℂ) (u j)).re := by
    intro i j
    rw [hdot, hns, hns, Zc_eq_re]
    simp only [u, map_mul, map_pow, Complex.conj_ofReal, mul_pow]
    rw [show (c i : ℂ) * z i ^ m * ((c j : ℂ) * (starRingEnd ℂ) (z j) ^ m) =
        ((c i * c j : ℝ) : ℂ) * (z i ^ m * (starRingEnd ℂ) (z j) ^ m) by push_cast; ring,
      Complex.re_ofReal_mul]
  have hsum : ∑ i, ∑ j, (u i * (starRingEnd ℂ) (u j)).re =
      Complex.normSq (∑ i, u i) := by
    have h := congrArg Complex.re (Complex.mul_conj (∑ i, u i))
    rw [Complex.ofReal_re] at h
    rw [← h, map_sum, Finset.sum_mul, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Complex.re_sum]
  simp_rw [hterm]
  rw [hsum]
  exact Complex.normSq_nonneg _

/-- Induction step on the dimension: a kernel of `ℝ^(d+1)` that splits along the first coordinate as a
nonnegative combination of products `B(a) B(a') Z_m` of kernels `Z_m` that are positive semidefinite on `ℝ^d` is
positive semidefinite on `ℝ^(d+1)`. -/
theorem psd_step {d K : ℕ} (Z : ℝ → ℝ → ℝ → ℝ) (Zp : ℕ → ℝ → ℝ → ℝ → ℝ) (cf : ℕ → ℝ)
    (B : ℕ → ℝ → ℝ → ℝ) (hc : ∀ m, 0 ≤ cf m) (hp : ∀ m ∈ range (K + 1), PSD d (Zp m))
    (hid : ∀ a a' w P Q, Z (a * a' + w) (a * a + P) (a' * a' + Q) =
      ∑ m ∈ range (K + 1), cf m * B m a (a * a + P) * B m a' (a' * a' + Q) * Zp m w P Q) :
    PSD (d + 1) Z := by
  intro n y c
  set t : Fin n → Fin d → ℝ := fun i => Fin.tail (y i)
  set W : ℕ → Fin n → ℝ := fun m i => c i * B m (y i 0) (dot (y i) (y i))
  have key : ∀ i j, c i * c j * Z (dot (y i) (y j)) (dot (y i) (y i)) (dot (y j) (y j)) =
      ∑ m ∈ range (K + 1), cf m * (W m i * W m j * Zp m (dot (t i) (t j)) (dot (t i) (t i)) (dot (t j) (t j))) := by
    intro i j
    have hi : dot (y i) (y i) = y i 0 * y i 0 + dot (t i) (t i) := dot_succ _ _
    have hj : dot (y j) (y j) = y j 0 * y j 0 + dot (t j) (t j) := dot_succ _ _
    have hij : dot (y i) (y j) = y i 0 * y j 0 + dot (t i) (t j) := dot_succ _ _
    simp only [W]
    rw [hij, hi, hj, hid, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hswap : ∀ F : ℕ → Fin n → Fin n → ℝ,
      ∑ i, ∑ j, ∑ m ∈ range (K + 1), F m i j = ∑ m ∈ range (K + 1), ∑ i, ∑ j, F m i j := by
    intro F
    calc ∑ i, ∑ j, ∑ m ∈ range (K + 1), F m i j = ∑ i, ∑ m ∈ range (K + 1), ∑ j, F m i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ m ∈ range (K + 1), ∑ i, ∑ j, F m i j := Finset.sum_comm
  simp_rw [key]
  rw [hswap]
  refine Finset.sum_nonneg fun m hm => ?_
  simp_rw [← Finset.mul_sum]
  exact mul_nonneg (hc m) (hp m hm n t (W m))

end Kissing8
