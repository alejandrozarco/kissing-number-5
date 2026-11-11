import Kissing5.Kernel
import Kissing5.Psd

-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7),
-- via lean/Kissing4/Positivity.lean of this package: `quad_Y5_nonneg` from `ThreePoint.quad_Y3_nonneg`;
-- `sum_S5_eq_sum_Y5` from `ThreePoint.sum_S3_eq_sum_Y3`; `exists_tangent_frame5` from
-- `ThreePoint.exists_tangent_frame`; `bv_positivity5` from `ThreePoint.bv_positivity`;
-- `matDot_moment_nonneg5` from `ThreePoint.matDot_moment_nonneg`.

/-!
# Bachoc–Vallentin positivity on `S⁴` (degrees `k ≤ 8`)

For unit vectors `x i` of `ℝ⁵` and every `k ≤ 8`, the moment matrix `∑_{i,j,l} S5_k(⟨xᵢ,xⱼ⟩, ⟨xᵢ,x_l⟩, ⟨xⱼ,x_l⟩)`
is positive semidefinite. As on `S²` and `S³`: fix the first index `i` and write the other points in an orthonormal
frame of the orthogonal complement of `xᵢ` (now four-dimensional). In these coordinates the kernel `Q5 k` is the
solid Gegenbauer kernel `Kissing8.Zg 4 k` of `ℝ⁴` (`Q5_eq_Zg`), which is positive semidefinite on `ℝ⁴` (`psd4`, by
induction on the dimension from `ℝ²`); so the inner double sum is nonnegative (`quad_Y5_nonneg`).
-/

open ThomsonN7 ThomsonN7.ThreePoint Kissing8
open scoped RealInnerProductSpace

namespace Kissing5

/-! ## The kernel in tangent coordinates -/

/-- `Q5` is the solid Gegenbauer kernel of `ℝ⁴` at `(t - uv, 1 - u², 1 - v²)`. -/
theorem Q5_eq_Zg (k : ℕ) (u v t : ℝ) : Q5 k u v t = Zg 4 k (t - u * v) (1 - u ^ 2) (1 - v ^ 2) := by
  have key : ∀ k, Q5 k u v t = Zg 4 k (t - u * v) (1 - u ^ 2) (1 - v ^ 2) ∧
      Q5 (k + 1) u v t = Zg 4 (k + 1) (t - u * v) (1 - u ^ 2) (1 - v ^ 2) := by
    intro k
    induction k with
    | zero => exact ⟨rfl, by simp only [Q5, Zg]; push_cast; ring⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      calc Q5 (k + 2) u v t
          = (2 * (k : ℝ) + 4) * (t - u * v) * Q5 (k + 1) u v t
            - ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((1 - u ^ 2) * (1 - v ^ 2)) * Q5 k u v t := rfl
        _ = (2 * (k : ℝ) + ((4 : ℕ) : ℝ)) * (t - u * v) * Zg 4 (k + 1) (t - u * v) (1 - u ^ 2) (1 - v ^ 2)
            - ((k : ℝ) + 1) * ((k : ℝ) + ((4 : ℕ) : ℝ) - 2) * ((1 - u ^ 2) * (1 - v ^ 2))
              * Zg 4 k (t - u * v) (1 - u ^ 2) (1 - v ^ 2) := by
          rw [ih.1, ih.2]; push_cast; ring
        _ = Zg 4 (k + 2) (t - u * v) (1 - u ^ 2) (1 - v ^ 2) := rfl
  exact (key k).1

/-! ## The quadratic form at a fixed centre -/

/-- **The quadratic form of `∑_{j,l} Y5_k` at a fixed centre is nonnegative** (`k ≤ 8`), given tangent coordinates
`y j ∈ ℝ⁴` of the other points. -/
theorem quad_Y5_nonneg (m k : ℕ) (hk : k ≤ 8) {N : ℕ} (u : Fin N → ℝ) (t : Fin N → Fin N → ℝ)
    (y : Fin N → Fin 4 → ℝ) (hu : ∀ j, 1 - u j ^ 2 = Kissing8.dot (y j) (y j))
    (ht : ∀ j l, t j l - u j * u l = Kissing8.dot (y j) (y l)) (w : Fin m → ℝ) :
    0 ≤ ∑ j, ∑ l, w ⬝ᵥ (Y5 m k (u j) (u l) (t j l)).mulVec w := by
  set p : Fin N → ℝ := fun j => ∑ q, w q * u j ^ (q : ℕ) with hp
  have key : ∀ j l, w ⬝ᵥ (Y5 m k (u j) (u l) (t j l)).mulVec w
      = p j * p l * Zg 4 k (Kissing8.dot (y j) (y l)) (Kissing8.dot (y j) (y j)) (Kissing8.dot (y l) (y l)) := by
    intro j l
    rw [← ht j l, ← hu j, ← hu l]
    simp only [hp, dotProduct, Matrix.mulVec, Y5, Matrix.of_apply, Q5_eq_Zg]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  simp only [key]
  exact Kissing5.psd4 k hk N y p

/-! ## Symmetrisation, tangent frames and positivity -/

/-- The symmetrised triple sum equals the unsymmetrised one. -/
theorem sum_S5_eq_sum_Y5 (m k : ℕ) {n : ℕ} (t : Fin n → Fin n → ℝ) (hsym : ∀ i j, t j i = t i j)
    (w : Fin m → ℝ) :
    ∑ i, ∑ j, ∑ l, w ⬝ᵥ (S5 m k (t i j) (t i l) (t j l)).mulVec w
      = ∑ i, ∑ j, ∑ l, w ⬝ᵥ (Y5 m k (t i j) (t i l) (t j l)).mulVec w := by
  set Φ : Fin n → Fin n → Fin n → ℝ :=
    fun i j l => w ⬝ᵥ (Y5 m k (t i j) (t i l) (t j l)).mulVec w with hΦ
  have expand : ∀ i j l, w ⬝ᵥ (S5 m k (t i j) (t i l) (t j l)).mulVec w
      = (1 / 6 : ℝ) * (Φ i j l + Φ j i l + Φ i l j + Φ l i j + Φ j l i + Φ l j i) := by
    intro i j l
    simp only [S5, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add,
      smul_eq_mul, hΦ, hsym]
  have e1 : ∑ i, ∑ j, ∑ l, Φ j i l = ∑ i, ∑ j, ∑ l, Φ i j l := (tsum_swap12 Φ).symm
  have e2 : ∑ i, ∑ j, ∑ l, Φ i l j = ∑ i, ∑ j, ∑ l, Φ i j l := (tsum_swap23 Φ).symm
  have e3 : ∑ i, ∑ j, ∑ l, Φ l i j = ∑ i, ∑ j, ∑ l, Φ i j l := by
    rw [tsum_swap23 (fun i j l => Φ l i j)]; exact (tsum_swap12 Φ).symm
  have e4 : ∑ i, ∑ j, ∑ l, Φ j l i = ∑ i, ∑ j, ∑ l, Φ i j l := by
    rw [tsum_swap12 (fun i j l => Φ j l i)]; exact (tsum_swap23 Φ).symm
  have e5 : ∑ i, ∑ j, ∑ l, Φ l j i = ∑ i, ∑ j, ∑ l, Φ i j l := by
    rw [tsum_swap12 (fun i j l => Φ l j i), tsum_swap23 (fun i j l => Φ l i j)]
    exact (tsum_swap12 Φ).symm
  simp only [expand, ← Finset.mul_sum, Finset.sum_add_distrib, e1, e2, e3, e4, e5]
  ring

/-- Every unit vector of `ℝ⁵` has an orthonormal frame `e₁, …, e₄` of its orthogonal complement, with
Parseval's identity for the tangent components. -/
theorem exists_tangent_frame5 (x : R5) (hx : ‖x‖ = 1) :
    ∃ e₁ e₂ e₃ e₄ : R5, ∀ y z : R5, ‖y‖ = 1 → ‖z‖ = 1 →
      (1 - ⟪x, y⟫ ^ 2 = ⟪e₁, y⟫ ^ 2 + ⟪e₂, y⟫ ^ 2 + ⟪e₃, y⟫ ^ 2 + ⟪e₄, y⟫ ^ 2) ∧
      (⟪y, z⟫ - ⟪x, y⟫ * ⟪x, z⟫
        = ⟪e₁, y⟫ * ⟪e₁, z⟫ + ⟪e₂, y⟫ * ⟪e₂, z⟫ + ⟪e₃, y⟫ * ⟪e₃, z⟫ + ⟪e₄, y⟫ * ⟪e₄, z⟫) := by
  have hcard : Module.finrank ℝ R5 = Fintype.card (Fin 5) := by simp
  let v : Fin 5 → R5 := fun _ => x
  have hv : Orthonormal ℝ (({0} : Set (Fin 5)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (by
      have hi := i.2; have hj := j.2
      simp only [Set.mem_singleton_iff] at hi hj
      rw [hi, hj])
    subst hij
    simp [Set.domRestrict, v, hx]
  obtain ⟨B, hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hv
  have hB0 : B 0 = x := hB 0 (Set.mem_singleton 0)
  refine ⟨B 1, B 2, B 3, B 4, fun y z hy hz => ?_⟩
  have P := B.sum_inner_mul_inner y z
  have Py := B.sum_inner_mul_inner y y
  rw [Fin.sum_univ_five, hB0] at P Py
  rw [real_inner_self_eq_norm_sq, hy] at Py
  have c1 : ⟪y, x⟫ = ⟪x, y⟫ := real_inner_comm _ _
  have c2 : ⟪y, B 1⟫ = ⟪B 1, y⟫ := real_inner_comm _ _
  have c3 : ⟪y, B 2⟫ = ⟪B 2, y⟫ := real_inner_comm _ _
  have c4 : ⟪y, B 3⟫ = ⟪B 3, y⟫ := real_inner_comm _ _
  have c5 : ⟪y, B 4⟫ = ⟪B 4, y⟫ := real_inner_comm _ _
  rw [c1, c2, c3, c4, c5] at P Py
  constructor
  · linear_combination -Py
  · linear_combination -P

/-- **Bachoc–Vallentin positivity for `S⁴`** (`k ≤ 8`). -/
theorem bv_positivity5 (m k : ℕ) (hk : k ≤ 8) {n : ℕ} (x : Fin n → R5) (hx : ∀ i, ‖x i‖ = 1)
    (w : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, ∑ l, w ⬝ᵥ (S5 m k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫).mulVec w := by
  have hsym : ∀ i j, ⟪x j, x i⟫ = ⟪x i, x j⟫ := fun i j => real_inner_comm _ _
  have e := sum_S5_eq_sum_Y5 m k (fun i j => ⟪x i, x j⟫) hsym w
  beta_reduce at e
  rw [e]
  refine Finset.sum_nonneg fun i _ => ?_
  obtain ⟨e₁, e₂, e₃, e₄, hfr⟩ := exists_tangent_frame5 (x i) (hx i)
  have hdot : ∀ j l, Kissing8.dot (![⟪e₁, x j⟫, ⟪e₂, x j⟫, ⟪e₃, x j⟫, ⟪e₄, x j⟫] : Fin 4 → ℝ)
      ![⟪e₁, x l⟫, ⟪e₂, x l⟫, ⟪e₃, x l⟫, ⟪e₄, x l⟫]
      = ⟪e₁, x j⟫ * ⟪e₁, x l⟫ + ⟪e₂, x j⟫ * ⟪e₂, x l⟫ + ⟪e₃, x j⟫ * ⟪e₃, x l⟫ + ⟪e₄, x j⟫ * ⟪e₄, x l⟫ := by
    intro j l
    simp [Kissing8.dot, Fin.sum_univ_four]
  exact quad_Y5_nonneg m k hk (fun j => ⟪x i, x j⟫) (fun j l => ⟪x j, x l⟫)
    (fun j => ![⟪e₁, x j⟫, ⟪e₂, x j⟫, ⟪e₃, x j⟫, ⟪e₄, x j⟫])
    (fun j => by rw [hdot, (hfr (x j) (x j) (hx j) (hx j)).1]; ring)
    (fun j l => by rw [hdot]; exact (hfr (x j) (x l) (hx j) (hx l)).2) w

/-- Pairing of a PSD matrix with the moment matrix is nonnegative (`k ≤ 8`). -/
theorem matDot_moment_nonneg5 (m k : ℕ) (hk : k ≤ 8) {n : ℕ} (x : Fin n → R5) (hx : ∀ i, ‖x i‖ = 1)
    (F : Matrix (Fin m) (Fin m) ℝ) (hF : F.PosSemidef) :
    0 ≤ ∑ i, ∑ j, ∑ l, matDot F (S5 m k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫) := by
  obtain ⟨r, v, hFv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hF
  have key3 : ∀ X : Fin m → Fin m → Fin r → ℝ,
      ∑ a, ∑ b, ∑ s, X a b s = ∑ s, ∑ a, ∑ b, X a b s := by
    intro X
    calc ∑ a, ∑ b, ∑ s, X a b s = ∑ a, ∑ s, ∑ b, X a b s :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ s, ∑ a, ∑ b, X a b s := Finset.sum_comm
  have hdot : ∀ M : Matrix (Fin m) (Fin m) ℝ, matDot F M = ∑ s, v s ⬝ᵥ M.mulVec (v s) := by
    intro M
    rw [hFv]
    simp only [matDot, Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial,
      dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [key3 (fun a b s => v s a * v s b * M a b)]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring
  have hswap : ∀ f : Fin n → Fin n → Fin n → Fin r → ℝ,
      ∑ i, ∑ j, ∑ l, ∑ s, f i j l s = ∑ s, ∑ i, ∑ j, ∑ l, f i j l s := by
    intro f
    calc ∑ i, ∑ j, ∑ l, ∑ s, f i j l s
        = ∑ i, ∑ j, ∑ s, ∑ l, f i j l s :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ i, ∑ s, ∑ j, ∑ l, f i j l s := Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ s, ∑ i, ∑ j, ∑ l, f i j l s := Finset.sum_comm
  simp only [hdot]
  rw [hswap]
  exact Finset.sum_nonneg fun s _ => bv_positivity5 m k hk x hx (v s)

end Kissing5
