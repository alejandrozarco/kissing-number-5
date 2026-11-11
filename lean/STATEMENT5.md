# What the dimension-5 Lean statement says, in plain English

File: `lean/Kissing5/Statement.lean`. It holds the claims only: its proofs are `sorry`, and the proof files supply them.
It uses the same definitions as the dimension-3 statement (`lean/Kissing/Statement.lean` in this package, published in
the repository `kissing-number-3`; the file's own comment names that repository), with `d = 5`, repeated so that the
file depends on Mathlib only.
It compiles, and its only warnings are the `sorry`s.

The exact kissing number in dimension 5 is not known. This statement gives bounds, not a value.

| Lean | Plain English |
|---|---|
| `E d := EuclideanSpace ℝ (Fin d)` | Ordinary d-dimensional space with ordinary distance. |
| `IsKissing S`: `∀ x ∈ S, ‖x‖ = 2` | Every outer ball (radius 1, centre `x`) touches the central ball (radius 1, centre 0): the centres are 2 apart. |
| `IsKissing S`: `∀ x y ∈ S, x ≠ y → 2 ≤ dist x y` | No two outer balls overlap: their centres are at least 2 apart (touching is allowed). |
| `kissingNumber d := ⨆ (S : Set (E d)) (_ : IsKissing S), S.encard` | The kissing number is the largest number of outer balls that fit. Infinite counts are allowed, so nothing is cut off silently. |
| `exists_isKissing_encard_eq_forty` | 40 balls fit around one in 5D: the 40 vectors with two coordinates `±1` and three coordinates `0` (the root system D5), scaled to radius 2. |
| `encard_le_fortyFive_of_isKissing` | Any arrangement in 5D has at most 45 balls. Infinite arrangements are covered and ruled out too. |
| `kissingNumber_five_bounds : 40 ≤ kissingNumber 5 ∧ kissingNumber 5 ≤ 45` | The kissing number in 5D is at least 40 and at most 45. |
| `isKissing_antipodal` (test) | Two balls on opposite sides do count as an arrangement, so the definition is not impossible to satisfy. |
| `not_isKissing_close` (test) | Two balls only $`30^\circ`$ apart (in 5D) overlap and do not count, so the distance rule really bites. |
| `not_isKissing_far` (test) | A ball whose centre is 3 away does not touch the central ball and does not count, so the touching rule bites too. |

Points worth a second look:
- The definition counts sets of centres. "Ball" and "sphere" do not matter here: touching unit balls and touching unit
  spheres give the same condition.
- The upper bound is not new mathematics. 45 is weaker than the best published bound, 44 (Mittelmann and Vallentin,
  2010). The aim here is a machine-checked proof of a bound of this kind, not a new record.
- The proof uses the equivalent form "unit vectors with pairwise inner products at most $`1/2`$" (divide the centres by 2).
  That conversion is proved in Lean; it is not assumed.
- The upper bound comes from a three-point (Bachoc–Vallentin) certificate with exact rational numbers, for exactly 46
  points (more than 45 balls would contain 46). Lean checks every
  number of it in the kernel (`decide +kernel`). Nothing is taken from floating-point output.
