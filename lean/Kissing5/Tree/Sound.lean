import ThomsonGen.Case1Stat
import Kissing5.Tree.Core

/-!
# Soundness of the tree-shaped row checks

The core-only computations of `Kissing5.Tree.Core` compute the statistics `ThomsonN7.Case1.c1Stat` (ℓ¹-norm, the three
degrees, the Kronecker value) of explicit `ThomsonN7.Kron.Ex` expressions:

* `St.toC1` reads a relative statistic `2^e (P - N)` as a `C1Stat`; `comb_toC1`: `comb` is `c1Add`;
* `ev_toC1`: `T.ev` is `c1Stat` of `T.toEx`, the sum of the signed terms;
* `sqRow_toC1`, `pairRow_toC1`, `dRow_toC1`: the row statistics are `c1Stat` of `sqEx`, `pairRowEx`, `dEx`;
* `sumSt_toC1`: `sumSt` is `c1Sum`;
* `sqEx_nonneg`, `pairRowEx_nonneg`, `dEx_nonneg`: these expressions are nonnegative at every real point.
-/

namespace Kissing5.Tree

open ThomsonN7 ThomsonN7.Kron ThomsonN7.Case1

/-- The Kronecker value `2^e (P - N)` of a relative statistic. -/
def St.kv (s : St) : ℤ := ((2 ^ s.e : ℕ) : ℤ) * ((s.P : ℤ) - (s.N : ℤ))

/-- A relative statistic as a `C1Stat`. -/
def St.toC1 (s : St) : C1Stat := (s.l, s.dx, s.dy, s.dz, s.kv)

/-! ## `comb` -/

theorem comb_l (s t : St) : (comb s t).l = s.l + t.l := by
  unfold comb; split_ifs <;> rfl

theorem comb_dx (s t : St) : (comb s t).dx = max s.dx t.dx := by
  unfold comb; split_ifs <;> rfl

theorem comb_dy (s t : St) : (comb s t).dy = max s.dy t.dy := by
  unfold comb; split_ifs <;> rfl

theorem comb_dz (s t : St) : (comb s t).dz = max s.dz t.dz := by
  unfold comb; split_ifs <;> rfl

theorem comb_kv (s t : St) : (comb s t).kv = s.kv + t.kv := by
  unfold comb
  split_ifs with h
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    simp only [St.kv, hk, Nat.add_sub_cancel_left, Nat.shiftLeft_eq]
    push_cast
    ring
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_le h))
    simp only [St.kv, hk, Nat.add_sub_cancel_left, Nat.shiftLeft_eq]
    push_cast
    ring

theorem comb_toC1 (s t : St) : (comb s t).toC1 = c1Add s.toC1 t.toC1 := by
  simp only [St.toC1, c1Add, comb_l, comb_dx, comb_dy, comb_dz, comb_kv]

/-! ## Sums of terms -/

/-- The sum of the signed terms of a tree. -/
def T.toEx : T → Ex
  | .pos a b d m => Ex.smul (m : ℤ) (.mon a b d)
  | .neg a b d m => Ex.smul (-(m : ℤ)) (.mon a b d)
  | .nd l r => .add l.toEx r.toEx

theorem ev_toC1 (w D : ℕ) (t : T) : (t.ev w D).toC1 = c1Stat w D t.toEx := by
  induction t with
  | pos a b d m =>
    simp only [T.ev, T.toEx, Ex.smul, c1Stat, c1Mul, c1C, St.toC1, St.kv, ex]
    simp
    ring
  | neg a b d m =>
    simp only [T.ev, T.toEx, Ex.smul, c1Stat, c1Mul, c1C, St.toC1, St.kv, ex]
    simp
    ring
  | nd l r ihl ihr =>
    simp only [T.ev, T.toEx, c1Stat]
    rw [comb_toC1, ihl, ihr]

/-- `Σ |m| (x^a y^b z^d)²` over the terms of a tree. -/
def T.sq2Ex : T → Ex
  | .pos a b d m => Ex.smul (m : ℤ) (Ex.sq (.mon a b d))
  | .neg a b d m => Ex.smul (m : ℤ) (Ex.sq (.mon a b d))
  | .nd l r => .add l.sq2Ex r.sq2Ex

theorem ev2_toC1 (w D : ℕ) (t : T) : (t.ev2 w D).toC1 = c1Stat w D t.sq2Ex := by
  induction t with
  | pos a b d m =>
    simp only [T.ev2, T.sq2Ex, Ex.smul, Ex.sq, c1Stat, c1Mul, c1C, St.toC1, St.kv, ex]
    simp only [Int.natAbs_natCast, mul_one, zero_add, Nat.cast_zero, sub_zero, Prod.mk.injEq, true_and]
    push_cast
    ring
  | neg a b d m =>
    simp only [T.ev2, T.sq2Ex, Ex.smul, Ex.sq, c1Stat, c1Mul, c1C, St.toC1, St.kv, ex]
    simp only [Int.natAbs_natCast, mul_one, zero_add, Nat.cast_zero, sub_zero, Prod.mk.injEq, true_and]
    push_cast
    ring
  | nd l r ihl ihr =>
    simp only [T.ev2, T.sq2Ex, c1Stat]
    rw [comb_toC1, ihl, ihr]

theorem ev2_l (w D : ℕ) (t : T) : (t.ev2 w D).l = (t.ev w D).l := by
  induction t with
  | pos => rfl
  | neg => rfl
  | nd l r ihl ihr => simp only [T.ev2, T.ev, comb_l, ihl, ihr]

theorem ev2_dx (w D : ℕ) (t : T) : (t.ev2 w D).dx = (t.ev w D).dx + (t.ev w D).dx := by
  induction t with
  | pos => rfl
  | neg => rfl
  | nd l r ihl ihr => simp only [T.ev2, T.ev, comb_dx, ihl, ihr]; omega

theorem ev2_dy (w D : ℕ) (t : T) : (t.ev2 w D).dy = (t.ev w D).dy + (t.ev w D).dy := by
  induction t with
  | pos => rfl
  | neg => rfl
  | nd l r ihl ihr => simp only [T.ev2, T.ev, comb_dy, ihl, ihr]; omega

theorem ev2_dz (w D : ℕ) (t : T) : (t.ev2 w D).dz = (t.ev w D).dz + (t.ev w D).dz := by
  induction t with
  | pos => rfl
  | neg => rfl
  | nd l r ihl ihr => simp only [T.ev2, T.ev, comb_dz, ihl, ihr]; omega

/-! ## Rows -/

/-- `q · (Σ t)²`. -/
def sqEx (q : ℕ) (t : T) : Ex := Ex.smul (q : ℤ) (Ex.sq t.toEx)

theorem sqRow_toC1 (w D q : ℕ) (t : T) : (sqRow w D q t).toC1 = c1Stat w D (sqEx q t) := by
  have h := ev_toC1 w D t
  simp only [sqEx, Ex.smul, Ex.sq, c1Stat]
  rw [← h]
  simp only [sqRow, St.toC1, St.kv, c1Mul, c1C, Int.natAbs_natCast, zero_add, Prod.mk.injEq, true_and,
    Nat.cast_zero, sub_zero]
  split_ifs with hNP
  · push_cast [Nat.cast_sub hNP]
    ring
  · push_cast [Nat.cast_sub (Nat.le_of_lt (Nat.lt_of_not_le hNP))]
    ring

/-- The pair squares `Σ_j |e_j| (z + sgn(e_j) z_j)²` of the signed terms `e_j z_j` of a tree, `z = x^a y^b z^d`. -/
def T.pairEx (a b d : ℕ) : T → Ex
  | .pos a' b' d' m => Ex.smul (m : ℤ) (Ex.sq (.add (.mon a b d) (.mon a' b' d')))
  | .neg a' b' d' m => Ex.smul (m : ℤ) (Ex.sq (.add (.mon a b d) (Ex.smul (-1) (.mon a' b' d'))))
  | .nd l r => .add (l.pairEx a b d) (r.pairEx a b d)

/-- The statistics of the pair squares, from the two passes `T.ev`, `T.ev2`. -/
theorem pairEx_stat (w D a b d : ℕ) (t : T) :
    c1Stat w D (t.pairEx a b d) =
      (4 * (t.ev w D).l, max (a + a) ((t.ev w D).dx + (t.ev w D).dx),
        max (b + b) ((t.ev w D).dy + (t.ev w D).dy), max (d + d) ((t.ev w D).dz + (t.ev w D).dz),
        ((t.ev w D).l : ℤ) * ((2 ^ (ex w D a b d + ex w D a b d) : ℕ) : ℤ) + (t.ev2 w D).kv +
          2 * ((2 ^ ex w D a b d : ℕ) : ℤ) * (t.ev w D).kv) := by
  induction t with
  | pos a' b' d' m =>
    simp only [T.pairEx, T.ev, T.ev2, Ex.smul, Ex.sq, c1Stat, c1Add, c1Mul, c1C, St.kv, ex,
      Int.natAbs_natCast, zero_add, Prod.mk.injEq]
    refine ⟨by ring, by omega, by omega, by omega, ?_⟩
    push_cast
    ring
  | neg a' b' d' m =>
    simp only [T.pairEx, T.ev, T.ev2, Ex.smul, Ex.sq, c1Stat, c1Add, c1Mul, c1C, St.kv, ex,
      Int.natAbs_natCast, zero_add, Prod.mk.injEq]
    refine ⟨by simp; ring, by omega, by omega, by omega, ?_⟩
    push_cast
    ring
  | nd l r ihl ihr =>
    simp only [T.pairEx, c1Stat, ihl, ihr, c1Add, T.ev, T.ev2, comb_l, comb_dx, comb_dy, comb_dz,
      comb_kv, Prod.mk.injEq]
    refine ⟨by ring, by omega, by omega, by omega, ?_⟩
    push_cast
    ring

/-- `di z² + Σ_j |e_j| (z + sgn(e_j) z_j)²`, `z = x^a y^b z^d`. -/
def pairRowEx (a b d di : ℕ) (t : T) : Ex :=
  .add (Ex.smul (di : ℤ) (Ex.sq (.mon a b d))) (t.pairEx a b d)

theorem pairRow_toC1 (w D a b d di : ℕ) (t : T) :
    (pairRow w D a b d di t).toC1 = c1Stat w D (pairRowEx a b d di t) := by
  simp only [pairRow, comb_toC1, pairRowEx, c1Stat, pairEx_stat]
  simp only [St.toC1, c1Add, Ex.smul, Ex.sq, c1Stat, c1Mul, c1C, Int.natAbs_natCast, zero_add, Prod.mk.injEq,
    ev2_l, ev2_dx, ev2_dy, ev2_dz, St.kv, ex]
  refine ⟨by ring, by omega, by omega, by omega, ?_⟩
  push_cast
  ring

/-- `di z²`, `z = x^a y^b z^d`. -/
def dEx (a b d di : ℕ) : Ex := Ex.smul (di : ℤ) (Ex.sq (.mon a b d))

theorem dRow_toC1 (w D a b d di : ℕ) : (dRow w D a b d di).toC1 = c1Stat w D (dEx a b d di) := by
  simp only [dRow, dEx, St.toC1, St.kv, Ex.smul, Ex.sq, c1Stat, c1Mul, c1C, ex, Int.natAbs_natCast, zero_add,
    Prod.mk.injEq, mul_one, true_and, Nat.cast_zero, sub_zero]
  push_cast
  ring

/-! ## Lists of rows -/

theorem c1Add_c1C_zero' (s : C1Stat) : c1Add s (c1C 0) = s := by
  obtain ⟨a, b, c, d, e⟩ := s
  simp [c1Add, c1C]

theorem sumSt_toC1 : ∀ (s : St) (ss : List St),
    (sumSt (s :: ss)).toC1 = c1Sum ((s :: ss).map St.toC1)
  | s, [] => by simp [sumSt, c1Sum, c1Add_c1C_zero']
  | s, s' :: ss => by
    have ih := sumSt_toC1 s' ss
    show (comb s (sumSt (s' :: ss))).toC1 = c1Add s.toC1 (c1Sum ((s' :: ss).map St.toC1))
    rw [comb_toC1, ih]

/-! ## Positivity -/

theorem sqEx_nonneg (q : ℕ) (t : T) (u v x : ℝ) : 0 ≤ (sqEx q t).ev u v x := by
  simp only [sqEx, Ex.smul, Ex.sq, Ex.ev]
  push_cast
  exact mul_nonneg (Nat.cast_nonneg q) (mul_self_nonneg _)

theorem pairEx_nonneg (a b d : ℕ) (t : T) (u v x : ℝ) : 0 ≤ (t.pairEx a b d).ev u v x := by
  induction t with
  | pos a' b' d' m =>
    simp only [T.pairEx, Ex.smul, Ex.sq, Ex.ev]
    push_cast
    exact mul_nonneg (Nat.cast_nonneg m) (mul_self_nonneg _)
  | neg a' b' d' m =>
    simp only [T.pairEx, Ex.smul, Ex.sq, Ex.ev]
    push_cast
    exact mul_nonneg (Nat.cast_nonneg m) (mul_self_nonneg _)
  | nd l r ihl ihr =>
    simp only [T.pairEx, Ex.ev]
    exact add_nonneg ihl ihr

theorem dEx_nonneg (a b d di : ℕ) (u v x : ℝ) : 0 ≤ (dEx a b d di).ev u v x := by
  simp only [dEx, Ex.smul, Ex.sq, Ex.ev]
  push_cast
  exact mul_nonneg (Nat.cast_nonneg di) (mul_self_nonneg _)

theorem pairRowEx_nonneg (a b d di : ℕ) (t : T) (u v x : ℝ) : 0 ≤ (pairRowEx a b d di t).ev u v x := by
  simp only [pairRowEx, Ex.ev]
  exact add_nonneg (dEx_nonneg a b d di u v x) (pairEx_nonneg a b d t u v x)

end Kissing5.Tree
