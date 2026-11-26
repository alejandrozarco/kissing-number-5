import Mathlib
import Kissing5.Cert44.Check

/-!
# Every kissing arrangement in `ℝ⁵` has at most 44 balls

The definitions repeat those of `Kissing5/Statement.lean` (in the namespace `Kissing5.K44`, so that this file does
not depend on the released `κ(5) ≤ 45` certificate chain).

Forty-five points of a kissing arrangement, scaled to unit vectors, would have pairwise inner products `≤ 1/2`; the
exact three-point certificate `Kissing5.Cert44.cf` for `S⁴` at degree 32 (tree-encoded SOS blocks, checked by
`decide +kernel` in chunks; `Kissing5.Tree.CertK5T.no_config5T`) rules that out.
-/

namespace Kissing5.K44

/-- Points of `ℝ^d` with the usual (Euclidean) distance. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- `S` is a kissing arrangement in `ℝ^d`: `S` is a set of centres of unit balls, each touching the
central unit ball at the origin (`‖x‖ = 2`), with no two overlapping (`2 ≤ dist x y` for `x ≠ y`). -/
def IsKissing {d : ℕ} (S : Set (E d)) : Prop :=
  (∀ x ∈ S, ‖x‖ = 2) ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 ≤ dist x y

/-- The kissing number of `ℝ^d`: the supremum of the sizes of kissing arrangements, in `ℕ∞`. -/
noncomputable def kissingNumber (d : ℕ) : ℕ∞ :=
  ⨆ (S : Set (E d)) (_ : IsKissing S), S.encard

open scoped RealInnerProductSpace

/-- Forty-five points of a kissing arrangement in `ℝ⁵` cannot exist: halved, they would be unit vectors with
pairwise inner products `≤ 1/2`, which the certificate excludes. -/
lemma no_fortyFive (S : Set (E 5)) (hS : IsKissing S) (x : Fin 45 → E 5) (hxS : ∀ i, x i ∈ S)
    (hxinj : Function.Injective x) : False := by
  set y : Fin 45 → E 5 := fun i => (1 / 2 : ℝ) • x i with hydef
  have hy : ∀ i, ‖y i‖ = 1 := by
    intro i
    simp only [hydef, norm_smul, hS.1 _ (hxS i)]
    norm_num
  have hyy : ∀ i j, i ≠ j → ⟪y i, y j⟫ ≤ 1 / 2 := by
    intro i j hij
    have hd := hS.2 _ (hxS i) _ (hxS j) fun h => hij (hxinj h)
    rw [dist_eq_norm] at hd
    have h1 := norm_sub_sq_real (x i) (x j)
    rw [hS.1 _ (hxS i), hS.1 _ (hxS j)] at h1
    have h2 : 4 ≤ ‖x i - x j‖ ^ 2 := by nlinarith [norm_nonneg (x i - x j)]
    simp only [hydef, real_inner_smul_left, real_inner_smul_right]
    nlinarith
  exact Kissing5.Tree.CertK5T.no_config5T Cert44.cf Cert44.cf_ok Cert44.cf_eps_pos
    (fun i => y (Fin.cast Cert44.cf_n i)) (fun i => hy _) fun i j hij => hyy _ _ fun h => hij (Fin.cast_injective _ h)

/-- **Upper bound.** Every kissing arrangement in `ℝ⁵` has at most 44 balls (in particular it is finite). -/
theorem encard_le_fortyFour_of_isKissing (S : Set (E 5)) (hS : IsKissing S) : S.encard ≤ 44 := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have h45 : ((45 : ℕ) : ℕ∞) ≤ S.encard := by
    have := Order.add_one_le_of_lt hlt
    norm_num at this ⊢
    exact this
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq h45
  have htf : t.Finite := Set.finite_of_encard_eq_coe htc
  have hcard : htf.toFinset.card = 45 := by
    have h := htf.encard_eq_coe_toFinset_card
    rw [htc] at h
    exact_mod_cast h.symm
  set e := Finset.equivFinOfCardEq hcard
  exact no_fortyFive S hS (fun i => ((e.symm i : htf.toFinset) : E 5))
    (fun i => hts ((Set.Finite.mem_toFinset htf).mp (e.symm i).2))
    fun i j h => e.symm.injective (Subtype.ext h)

/-- **The kissing number in dimension 5 is at most 44.** -/
theorem kissingNumber_five_le_fortyFour : kissingNumber 5 ≤ 44 := by
  unfold kissingNumber
  exact iSup₂_le fun S hS => encard_le_fortyFour_of_isKissing S hS

end Kissing5.K44
