/-!
# Tree-shaped row checks (core Lean only)

Definitions for the kernel checks of large SOS blocks, in core Lean without Mathlib, so that the generated row modules
import only this file. Their meaning (statistics of `ThomsonN7.Kron.Ex` expressions, and positivity) is proved in
`Kissing5.Tree.Sound`.

* A sparse linear form is a binary tree `T` of signed terms `± m x^a y^b z^d` (`m : Nat`).
* `St` holds the statistics the Kronecker check needs, `(ℓ¹, deg x, deg y, deg z)`, and the Kronecker value in the
  relative form `2^e (P - N)` with `P N : Nat`. `comb` adds two statistics, keeping the value relative to the smaller
  base exponent: when the terms of a tree are sorted by exponent, the values on one level of the tree have disjoint
  exponent ranges, so a whole row costs `O(N log r)` bits of intermediate values for an `N`-bit result.
* `sqRow w D q t` is the statistic of `q · (Σ t)²`; `pairRow w D a b d di t` that of
  `di z² + Σ_j |e_j| (z + sgn(e_j) z_j)²` with `z = x^a y^b z^d` and `t` the signed terms `e_j z_j`; `dRow` that of
  `di z²`. These are the summands of an SOS block written as `L D Lᵀ` and a remainder that is diagonally dominant,
  in pair-square form; each is a nonnegative multiple of a square, or a sum of such.
* `PRow`, `PRow.st`: a remainder row (`dRow` or `pairRow`), as the SOS blocks list them.
* `cat k lo hi = lo + hi · 2^k` writes large right-hand sides as balanced trees of small literals.
-/

namespace Kissing5.Tree

/-- A sparse linear form as a binary tree of signed terms `± m x^a y^b z^d`. -/
inductive T where
  | pos (a b d m : Nat)
  | neg (a b d m : Nat)
  | nd (l r : T)

/-- `(ℓ¹, deg x, deg y, deg z, e, P, N)`: statistics with the Kronecker value `2^e (P - N)`. -/
structure St where
  l : Nat
  dx : Nat
  dy : Nat
  dz : Nat
  e : Nat
  P : Nat
  N : Nat
deriving DecidableEq

/-- The statistics of a sum, with the value kept relative to the smaller base exponent. -/
def comb (s t : St) : St :=
  if s.e ≤ t.e then
    ⟨s.l + t.l, max s.dx t.dx, max s.dy t.dy, max s.dz t.dz, s.e,
      s.P + (t.P <<< (t.e - s.e)), s.N + (t.N <<< (t.e - s.e))⟩
  else
    ⟨s.l + t.l, max s.dx t.dx, max s.dy t.dy, max s.dz t.dz, t.e,
      t.P + (s.P <<< (s.e - t.e)), t.N + (s.N <<< (s.e - t.e))⟩

/-- The Kronecker exponent of `x^a y^b z^d`. -/
def ex (w D a b d : Nat) : Nat := w * (a + D * b + D * D * d)

/-- Statistics of the sum of the terms of `t`. -/
def T.ev (w D : Nat) : T → St
  | .pos a b d m => ⟨m, a, b, d, ex w D a b d, m, 0⟩
  | .neg a b d m => ⟨m, a, b, d, ex w D a b d, 0, m⟩
  | .nd l r => comb (T.ev w D l) (T.ev w D r)

/-- Statistics of `Σ |m| (x^a y^b z^d)²` over the terms of `t`. -/
def T.ev2 (w D : Nat) : T → St
  | .pos a b d m => ⟨m, a + a, b + b, d + d, 2 * ex w D a b d, m, 0⟩
  | .neg a b d m => ⟨m, a + a, b + b, d + d, 2 * ex w D a b d, m, 0⟩
  | .nd l r => comb (T.ev2 w D l) (T.ev2 w D r)

/-- Statistics of `q · (Σ t)²`. -/
def sqRow (w D q : Nat) (t : T) : St :=
  let s := T.ev w D t
  let v := if s.N ≤ s.P then s.P - s.N else s.N - s.P
  ⟨q * (s.l * s.l), s.dx + s.dx, s.dy + s.dy, s.dz + s.dz, s.e + s.e, q * (v * v), 0⟩

/-- Statistics of `di z² + Σ_j |e_j| (z + sgn(e_j) z_j)²`, `z = x^a y^b z^d`, `t` = the signed terms `e_j z_j`,
computed as `(di + A) z² + Σ_j |e_j| z_j² + 2 z Σ_j e_j z_j` with `A = Σ_j |e_j|`. -/
def pairRow (w D a b d di : Nat) (t : T) : St :=
  let s1 := T.ev w D t
  let E := ex w D a b d
  comb (comb ⟨di + s1.l, a + a, b + b, d + d, E + E, di + s1.l, 0⟩ (T.ev2 w D t))
    ⟨2 * s1.l, a + s1.dx, b + s1.dy, d + s1.dz, E + 1 + s1.e, s1.P, s1.N⟩

/-- Statistics of `di z²`, `z = x^a y^b z^d` (a remainder row without pairs). -/
def dRow (w D a b d di : Nat) : St :=
  ⟨di, a + a, b + b, d + d, ex w D a b d + ex w D a b d, di, 0⟩

/-- The statistics of a nonempty list of statistics. -/
def sumSt : List St → St
  | [] => ⟨0, 0, 0, 0, 0, 0, 0⟩
  | [s] => s
  | s :: ss => comb s (sumSt ss)

/-- A remainder row: `di z²` with `z = x^a y^b z^d`, plus the pair squares of `t` if there is one. -/
structure PRow where
  a : Nat
  b : Nat
  d : Nat
  di : Nat
  t : Option T

/-- The statistics of a remainder row. -/
def PRow.st (w D : Nat) (p : PRow) : St :=
  match p.t with
  | none => dRow w D p.a p.b p.d p.di
  | some t => pairRow w D p.a p.b p.d p.di t

/-- `lo + hi · 2^k`: right-hand sides as balanced trees of small literals. -/
def cat (k lo hi : Nat) : Nat := lo + (hi <<< k)

end Kissing5.Tree
