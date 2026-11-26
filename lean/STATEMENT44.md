# What the Lean statement of κ(5) ≤ 44 says, in plain English

File: `lean/Kissing5/Statement44.lean`. It holds the claims only: its proofs are `sorry`, and
`lean/Kissing5/Solution44.lean` supplies them. Its definitions are those of `lean/Kissing5/Statement.lean` (see
`STATEMENT5.md`), word for word, in the namespace `Kissing5.K44` instead of `Kissing5`. The separate namespace keeps the
proof of 44 independent of the certificate of 45. The file depends on Mathlib only.
It compiles, and its only warnings are the `sorry`s.

The exact kissing number in dimension 5 is not known. This statement gives an upper bound, not a value; the lower
bound 40 is `Kissing5.exists_isKissing_encard_eq_forty` in `Statement.lean`.

| Lean | Plain English |
|---|---|
| `E d := EuclideanSpace ℝ (Fin d)` | Ordinary d-dimensional space with ordinary distance. |
| `IsKissing S`: `∀ x ∈ S, ‖x‖ = 2` | Every outer ball (radius 1, centre `x`) touches the central ball (radius 1, centre 0): the centres are 2 apart. |
| `IsKissing S`: `∀ x y ∈ S, x ≠ y → 2 ≤ dist x y` | No two outer balls overlap: their centres are at least 2 apart (touching is allowed). |
| `kissingNumber d := ⨆ (S : Set (E d)) (_ : IsKissing S), S.encard` | The kissing number is the largest number of outer balls that fit. Infinite counts are allowed, so nothing is cut off silently. |
| `encard_le_fortyFour_of_isKissing` | Any arrangement in 5D has at most 44 balls. Infinite arrangements are covered and ruled out too. |
| `kissingNumber_five_le_fortyFour : kissingNumber 5 ≤ 44` | The kissing number in 5D is at most 44. |

Points worth a second look:
- The definitions are the same text as in `Statement.lean`, so the tests there apply to them too: two opposite balls
  form an arrangement, two balls $`30^\circ`$ apart do not, and a ball at distance 3 does not. Those tests are proved
  for the `Kissing5` copy of the definitions. Comparator checks each statement file against its own proof file.
- The definition counts sets of centres. "Ball" and "sphere" do not matter here: touching unit balls and touching unit
  spheres give the same condition.
- The bound is not new mathematics, and it is not the best known one. Mittelmann and Vallentin (2010) obtained 44
  from a high-precision floating-point computation; Tomar (2026, preprint) proves 43, with Lean proofs that assume the
  positivity of zonal kernels built from data files. What is added here is an exact three-point certificate for 44
  and a Lean proof that uses no such hypothesis (only Lean's standard axioms).
- The proof uses the equivalent form "unit vectors with pairwise inner products at most $`1/2`$" (divide the centres by 2).
  That conversion is proved in Lean; it is not assumed.
- The bound comes from a three-point (Bachoc–Vallentin) certificate with exact rational numbers, for exactly 45
  points (more than 44 balls would contain 45). Lean checks every number of it in the kernel (`decide +kernel`).
  Nothing is taken from floating-point output.
