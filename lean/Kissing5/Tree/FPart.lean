import Kissing5.CertK
import Kissing5.Tree.Sound

/-!
# The `F`-part of the identity with balanced sums and relative statistics

At degree 32 the Kronecker values have about `8 · 10⁶` bits. `Kissing5.fk5E` builds the quadratic form of an
`F`-block from right-folded sums (`sumRange`), so each partial sum is a full-size value, and the kernel keeps all of
them (under each of the 16 variable substitutions of `c1FtotK`) until the declaration ends: about 4 GB for the
largest block. Here the same polynomials are written so that the kernel check is cheap:

* `fpB r b`: the quadratic form `Σ_{a,c} ent_ac uᵃ vᶜ` of a block, with the entries `Blk.ent` (as `ev_fpE` states it)
  in balanced sums `bs`; `ev_fpB`, and `ev_fkB : (fkB r b k).ev = (fk5E r b k).ev`;
* `rst w D e`: the statistics `c1Stat w D e` (`rst_toC1`), with the Kronecker value kept as `2^e (P - N)` as in
  `Kissing5.Tree.Core` (`comb` for sums, `mulSt` for products), so that a term `x^a y^b z^d` costs `O(1)` and a
  balanced sum of terms with nearby exponents stays small;
* `c1Stat_c1FtotK`: the statistics of `c1FtotK n e` from those of its five six-fold sums `sixE`, so that each of
  these can be its own declaration.
-/

namespace Kissing5.Tree

open ThomsonN7 ThomsonN7.Kron ThomsonN7.Kron.Ex ThomsonN7.Cert ThomsonN7.Case1 Kissing Kissing5

/-! ## Relative statistics of an expression -/

/-- The statistics of a product, in relative form: `2^(e+e') ((P P' + N N') - (P N' + N P'))`. -/
def mulSt (s t : St) : St :=
  ⟨s.l * t.l, s.dx + t.dx, s.dy + t.dy, s.dz + t.dz, s.e + t.e, s.P * t.P + s.N * t.N, s.P * t.N + s.N * t.P⟩

/-- `c1Stat` with the Kronecker value in relative form. -/
def rst (w D : ℕ) : Ex → St
  | .c n => ⟨n.natAbs, 0, 0, 0, 0, n.toNat, (-n).toNat⟩
  | .mon a b d => ⟨1, a, b, d, ex w D a b d, 1, 0⟩
  | .add p q => comb (rst w D p) (rst w D q)
  | .mul p q => mulSt (rst w D p) (rst w D q)

theorem mulSt_toC1 (s t : St) : (mulSt s t).toC1 = c1Mul s.toC1 t.toC1 := by
  simp only [mulSt, St.toC1, St.kv, c1Mul, pow_add, Nat.cast_mul, Nat.cast_add]
  congr 4
  ring

theorem rst_toC1 (w D : ℕ) : ∀ e : Ex, (rst w D e).toC1 = c1Stat w D e
  | .c n => by
    simp only [rst, St.toC1, St.kv, c1Stat, c1C, pow_zero, Nat.cast_one, one_mul, Prod.mk.injEq, true_and]
    omega
  | .mon a b d => by simp [rst, St.toC1, St.kv, c1Stat, ex]
  | .add p q => by rw [rst, comb_toC1, rst_toC1 w D p, rst_toC1 w D q]; rfl
  | .mul p q => by rw [rst, mulSt_toC1, rst_toC1 w D p, rst_toC1 w D q]; rfl

/-! ## Balanced sums -/

/-- `Σ_{i < n} f (lo + i)` as a balanced tree of `add`s, with fuel `d` (for `d = 0` the plain `sumRange`). -/
def bs (f : ℕ → Ex) : ℕ → ℕ → ℕ → Ex
  | 0, lo, n => sumRange n fun i => f (lo + i)
  | d + 1, lo, n =>
    if n ≤ 1 then (if n = 0 then c 0 else f lo)
    else add (bs f d lo (n / 2)) (bs f d (lo + n / 2) (n - n / 2))

theorem ev_bs (f : ℕ → Ex) (u v t : ℝ) :
    ∀ d lo n, (bs f d lo n).ev u v t = ∑ i ∈ Finset.range n, (f (lo + i)).ev u v t
  | 0, lo, n => by rw [bs, ev_sumRange]
  | d + 1, lo, n => by
    rw [bs]
    split_ifs with h1 h0
    · subst h0; simp [ev_c]
    · obtain rfl : n = 1 := by omega
      simp
    · rw [ev_add, ev_bs f u v t d lo (n / 2), ev_bs f u v t d (lo + n / 2) (n - n / 2)]
      have hn : n = n / 2 + (n - n / 2) := by omega
      conv_rhs => rw [hn, Finset.sum_range_add]
      simp only [Nat.add_assoc]

/-! ## The `F`-blocks -/

/-- `Λ · Fp(u, v) = Σ_{a,c} ent_ac uᵃ vᶜ` for a block, in balanced sums. -/
def fpB (r : ℕ) (b : Blk) : Ex :=
  bs (fun a => bs (fun c => smul (b.ent r a c) (mon a c 0)) 64 0 r) 64 0 r

theorem ev_fpB (r : ℕ) (b : Blk) (u v t : ℝ) :
    (fpB r b).ev u v t
      = ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range r, (b.ent r a c : ℝ) * u ^ a * v ^ c := by
  simp only [fpB, ev_bs, ev_smul, ev_mon, zero_add, pow_zero, mul_one, mul_assoc]

/-- `Λ · Fp_k(u, v, t)` for the `S⁴` kernel, as `Kissing5.fk5E` with `fpB` for `fpE`. -/
def fkB (r : ℕ) (b : Blk) (k : ℕ) : Ex := mul (fpB r b) (q5E k)

theorem ev_fkB (r : ℕ) (b : Blk) (k : ℕ) (u v t : ℝ) : (fkB r b k).ev u v t = (fk5E r b k).ev u v t := by
  rw [fkB, fk5E, ev_mul, ev_mul, ev_fpB, ev_fpE]

/-- The statistics of the `F`-summand `c1FtotK n e`, from those of its five six-fold sums. -/
theorem c1Stat_c1FtotK (w D n : ℕ) (e : Ex) :
    c1Stat w D (c1FtotK n e) =
      c1Add (c1Add (c1Smul (((n : ℤ) - 1) * ((n : ℤ) - 2)) (c1Stat w D (sixE 0 1 2 e)))
          (c1Smul ((n : ℤ) - 1) (c1Add (c1Add (c1Stat w D (sixE 0 0 3 e)) (c1Stat w D (sixE 1 1 3 e)))
            (c1Stat w D (sixE 2 2 3 e)))))
        (c1Stat w D (sixE 3 3 3 e)) := rfl

end Kissing5.Tree
