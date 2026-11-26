import Mathlib

/-!
# Every kissing arrangement in dimension 5 has at most 44 balls: statement

This file holds the claims only, with every proof replaced by `sorry`. It is the reference (challenge) file
for Comparator (`comparator44.json`): `Kissing5/Solution44.lean` must prove these exact statements. The
definitions are those of `Kissing5/Statement.lean`, word for word, in the namespace `Kissing5.K44`, so that the
proof of this bound does not depend on the certificate chain of the bound 45. This file depends on Mathlib only.

Picture: a central ball of radius 1 at the origin of `ℝ⁵`, and other balls of radius 1 around it. Each one
touches the central ball, so its centre is at distance 2 from the origin. No two of them overlap, so their
centres are at least 2 apart (touching is allowed). The kissing number is the largest possible number of such
outer balls. This file states that it is at most 44 in dimension 5. The lower bound 40 is
`Kissing5.exists_isKissing_encard_eq_forty` (`Kissing5/Statement.lean`).
-/

namespace Kissing5.K44

/-- Points of `ℝ^d` with the usual (Euclidean) distance. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- `S` is a kissing arrangement in `ℝ^d`: `S` is a set of centres of unit balls, each touching the
central unit ball at the origin (`‖x‖ = 2`), with no two overlapping (`2 ≤ dist x y` for `x ≠ y`).
`S` may be infinite here; the theorems below rule that out in dimension 5. -/
def IsKissing {d : ℕ} (S : Set (E d)) : Prop :=
  (∀ x ∈ S, ‖x‖ = 2) ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 ≤ dist x y

/-- The kissing number of `ℝ^d`: the supremum of the sizes of kissing arrangements. Sizes are counted
in `ℕ∞` (`Set.encard`), so an infinite arrangement would make it `⊤`; nothing is truncated. -/
noncomputable def kissingNumber (d : ℕ) : ℕ∞ :=
  ⨆ (S : Set (E d)) (_ : IsKissing S), S.encard

/-! ## Main results -/

/-- **Upper bound.** Every kissing arrangement in `ℝ⁵` has at most 44 balls (in particular it is
finite). -/
theorem encard_le_fortyFour_of_isKissing (S : Set (E 5)) (hS : IsKissing S) : S.encard ≤ 44 := by
  sorry

/-- **The kissing number in dimension 5 is at most 44.** -/
theorem kissingNumber_five_le_fortyFour : kissingNumber 5 ≤ 44 := by
  sorry

end Kissing5.K44
