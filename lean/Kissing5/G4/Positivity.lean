import Kissing5.Positivity
import Kissing5.G4.Psd

-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7),
-- via lean/Kissing5/Positivity.lean of this package: `matDot_moment_nonneg5_of` and `matDot_moment_nonneg5` from
-- `ThreePoint.matDot_moment_nonneg`.

/-!
# Bachoc–Vallentin positivity on `S⁴` for degrees `k ≤ 16`

`Kissing5.Positivity` proves the positivity of the moment matrices for `k ≤ 8`, from `Kissing5.psd4` (addition
identities proved by `ring`). The same proofs give it for every degree `k` with `PSD 4 (Zg 4 k)`; here they are
stated with that hypothesis (`quad_Y5_nonneg_of`, `bv_positivity5_of`, `matDot_moment_nonneg5_of`) and instantiated
for `k ≤ 16` with `Kissing5.G4.psd4` (addition identities checked by Kronecker substitution). The degree-independent
lemmas (`Q5_eq_Zg`, `sum_S5_eq_sum_Y5`, `exists_tangent_frame5`) are reused; `Kissing5.Positivity` is not changed.
-/

open ThomsonN7 ThomsonN7.ThreePoint Kissing8
open scoped RealInnerProductSpace

namespace Kissing5.G4

/-- The quadratic form of `∑_{j,l} Y5_k` at a fixed centre is nonnegative when `Zg 4 k` is positive semidefinite on
`ℝ⁴`, given tangent coordinates `y j ∈ ℝ⁴` of the other points (as `Kissing5.quad_Y5_nonneg`). -/
theorem quad_Y5_nonneg_of (m k : ℕ) (hpsd : PSD 4 (Zg 4 k)) {N : ℕ} (u : Fin N → ℝ) (t : Fin N → Fin N → ℝ)
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
  exact hpsd N y p

/-- Bachoc–Vallentin positivity for `S⁴` in every degree `k` with `PSD 4 (Zg 4 k)` (as
`Kissing5.bv_positivity5`). -/
theorem bv_positivity5_of (m k : ℕ) (hpsd : PSD 4 (Zg 4 k)) {n : ℕ} (x : Fin n → R5) (hx : ∀ i, ‖x i‖ = 1)
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
  exact quad_Y5_nonneg_of m k hpsd (fun j => ⟪x i, x j⟫) (fun j l => ⟪x j, x l⟫)
    (fun j => ![⟪e₁, x j⟫, ⟪e₂, x j⟫, ⟪e₃, x j⟫, ⟪e₄, x j⟫])
    (fun j => by rw [hdot, (hfr (x j) (x j) (hx j) (hx j)).1]; ring)
    (fun j l => by rw [hdot]; exact (hfr (x j) (x l) (hx j) (hx l)).2) w

/-- Pairing of a PSD matrix with the moment matrix is nonnegative in every degree `k` with `PSD 4 (Zg 4 k)` (as
`Kissing5.matDot_moment_nonneg5`). -/
theorem matDot_moment_nonneg5_of (m k : ℕ) (hpsd : PSD 4 (Zg 4 k)) {n : ℕ} (x : Fin n → R5)
    (hx : ∀ i, ‖x i‖ = 1) (F : Matrix (Fin m) (Fin m) ℝ) (hF : F.PosSemidef) :
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
  exact Finset.sum_nonneg fun s _ => bv_positivity5_of m k hpsd x hx (v s)

/-- **Bachoc–Vallentin positivity for `S⁴`** (`k ≤ 16`). -/
theorem bv_positivity5 (m k : ℕ) (hk : k ≤ 16) {n : ℕ} (x : Fin n → R5) (hx : ∀ i, ‖x i‖ = 1)
    (w : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, ∑ l, w ⬝ᵥ (S5 m k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫).mulVec w :=
  bv_positivity5_of m k (Kissing5.G4.psd4 k hk) x hx w

/-- Pairing of a PSD matrix with the moment matrix is nonnegative (`k ≤ 16`). -/
theorem matDot_moment_nonneg5 (m k : ℕ) (hk : k ≤ 16) {n : ℕ} (x : Fin n → R5) (hx : ∀ i, ‖x i‖ = 1)
    (F : Matrix (Fin m) (Fin m) ℝ) (hF : F.PosSemidef) :
    0 ≤ ∑ i, ∑ j, ∑ l, matDot F (S5 m k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫) :=
  matDot_moment_nonneg5_of m k (Kissing5.G4.psd4 k hk) x hx F hF

end Kissing5.G4
