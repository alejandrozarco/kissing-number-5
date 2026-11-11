import Mathlib
import Kissing8.TwoForty
import Kissing8.Delsarte

/-!
# The kissing number in dimension 8 is 240: proofs

The definitions below repeat `Kissing8/Statement.lean` verbatim; the theorems carry the same names and statements,
now with proofs (Comparator checks this, with the package's Comparator configuration).

* Lower bound: the 240 roots of `E₈` in the integer model `√2 E₈` (Construction A of the extended Hamming code),
  of norm 2 and pairwise distance at least 2 (`Kissing8.TwoForty`).
* Upper bound: 241 points of a kissing arrangement, scaled to unit vectors, would have pairwise inner products
  `≤ 1/2`; the two-point (Delsarte) bound rules that out (`Kissing8.card_le_240`).
-/

namespace Kissing8

/-- Points of `ℝ^d` with the usual (Euclidean) distance. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- `S` is a kissing arrangement in `ℝ^d`: `S` is a set of centres of unit balls, each touching the
central unit ball at the origin (`‖x‖ = 2`), with no two overlapping (`2 ≤ dist x y` for `x ≠ y`).
`S` may be infinite here; the theorems below rule that out in dimension 8. -/
def IsKissing {d : ℕ} (S : Set (E d)) : Prop :=
  (∀ x ∈ S, ‖x‖ = 2) ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 ≤ dist x y

/-- The kissing number of `ℝ^d`: the supremum of the sizes of kissing arrangements. Sizes are counted
in `ℕ∞` (`Set.encard`), so an infinite arrangement would make it `⊤`; nothing is truncated. -/
noncomputable def kissingNumber (d : ℕ) : ℕ∞ :=
  ⨆ (S : Set (E d)) (_ : IsKissing S), S.encard

open scoped RealInnerProductSpace

/-! ## Main results -/

/-- **Lower bound.** There is a kissing arrangement of 240 balls in `ℝ⁸` (the 240 roots of `E₈`, scaled to
radius 2). -/
theorem exists_isKissing_encard_eq_twoHundredForty : ∃ S : Set (E 8), IsKissing S ∧ S.encard = 240 := by
  refine ⟨Set.range TwoForty.pt, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact TwoForty.norm_pt i
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact TwoForty.dist_pt i j fun h => hij (h ▸ rfl)
  · rw [← Set.image_univ, TwoForty.pt_injective.encard_image, Set.encard_univ]
    simp

/-- 241 points of a kissing arrangement in `ℝ⁸` cannot exist: halved, they would be unit vectors with pairwise
inner products `≤ 1/2`, and the two-point bound `Kissing8.card_le_240` allows at most 240 of those. -/
lemma no_twoHundredFortyOne (S : Set (E 8)) (hS : IsKissing S) (x : Fin 241 → E 8) (hxS : ∀ i, x i ∈ S)
    (hxinj : Function.Injective x) : False := by
  set y : Fin 241 → E 8 := fun i => (1 / 2 : ℝ) • x i with hydef
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
  have := card_le_240 y hy hyy
  omega

/-- **Upper bound.** Every kissing arrangement in `ℝ⁸` has at most 240 balls (in particular it is
finite). -/
theorem encard_le_twoHundredForty_of_isKissing (S : Set (E 8)) (hS : IsKissing S) : S.encard ≤ 240 := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have h241 : ((241 : ℕ) : ℕ∞) ≤ S.encard := by
    have := Order.add_one_le_of_lt hlt
    norm_num at this ⊢
    exact this
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq h241
  have htf : t.Finite := Set.finite_of_encard_eq_coe htc
  have hcard : htf.toFinset.card = 241 := by
    have h := htf.encard_eq_coe_toFinset_card
    rw [htc] at h
    exact_mod_cast h.symm
  set e := Finset.equivFinOfCardEq hcard
  exact no_twoHundredFortyOne S hS (fun i => ((e.symm i : htf.toFinset) : E 8))
    (fun i => hts ((Set.Finite.mem_toFinset htf).mp (e.symm i).2))
    fun i j h => e.symm.injective (Subtype.ext h)

/-- **The kissing number in dimension 8 is 240.** -/
theorem kissingNumber_eight : kissingNumber 8 = 240 := by
  unfold kissingNumber
  apply le_antisymm
  · exact iSup₂_le fun S hS => encard_le_twoHundredForty_of_isKissing S hS
  · obtain ⟨S, hS, hc⟩ := exists_isKissing_encard_eq_twoHundredForty
    calc (240 : ℕ∞) = S.encard := hc.symm
      _ ≤ ⨆ (S : Set (E 8)) (_ : IsKissing S), S.encard :=
        le_iSup₂ (f := fun (S : Set (E 8)) (_ : IsKissing S) => S.encard) S hS

/-! ## Sanity checks of the definition (unit tests for the statement)

These are not used by the main results. They check that `IsKissing` is neither vacuous nor too weak:
the `E₈` roots above already show it can hold for 240 points; the tests below show that it holds for
two opposite balls, fails for two overlapping ones, and fails for a ball that does not touch the central one. -/

/-- Two balls on opposite sides of the central ball form a kissing arrangement. -/
theorem isKissing_antipodal :
    IsKissing ({EuclideanSpace.single 0 2, EuclideanSpace.single 0 (-2)} : Set (E 8)) := by
  constructor
  · intro x hx
    rcases hx with rfl | rfl <;> apply TwoForty.norm_eq_two <;> simp <;> norm_num
  · intro x hx y hy hxy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · apply TwoForty.two_le_dist; simp; norm_num
    · apply TwoForty.two_le_dist; simp; norm_num
    · exact absurd rfl hxy

/-- Two balls touching the central ball at 30° from each other overlap, so they do not form a kissing
arrangement: their centres `(2, 0, …, 0)` and `(√3, 1, 0, …, 0)` are about `1.04 < 2` apart. -/
theorem not_isKissing_close :
    ¬ IsKissing ({!₂[2, 0, 0, 0, 0, 0, 0, 0], !₂[√3, 1, 0, 0, 0, 0, 0, 0]} : Set (E 8)) := by
  intro h
  have hne : (!₂[2, 0, 0, 0, 0, 0, 0, 0] : E 8) ≠ !₂[√3, 1, 0, 0, 0, 0, 0, 0] := by
    intro he
    have := congrArg (fun z : E 8 => z 1) he
    simp at this
  have hd := h.2 _ (Set.mem_insert _ _) _ (Set.mem_insert_of_mem _ rfl) hne
  rw [dist_eq_norm] at hd
  have hs : ‖(!₂[2, 0, 0, 0, 0, 0, 0, 0] : E 8) - !₂[√3, 1, 0, 0, 0, 0, 0, 0]‖ ^ 2 = (2 - √3) ^ 2 + 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_eight]
    simp
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : 1 < √3 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith [norm_nonneg ((!₂[2, 0, 0, 0, 0, 0, 0, 0] : E 8) - !₂[√3, 1, 0, 0, 0, 0, 0, 0])]

/-- A ball whose centre is at distance `3` from the origin does not touch the central ball, so it does not
form a kissing arrangement. -/
theorem not_isKissing_far : ¬ IsKissing ({EuclideanSpace.single 0 3} : Set (E 8)) := by
  intro h
  have h1 := h.1 _ (Set.mem_singleton _)
  norm_num at h1

end Kissing8
