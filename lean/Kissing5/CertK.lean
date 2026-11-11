import Kissing.CertK
import Kissing5.Positivity
import Kissing5.Bound

-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7):
-- `q5E` from `Cert.q3E`, `ev_q5E` from `Cert.ev_q3E`, `fk5E` from `Cert.fkE`, `ev_fk5E` from `Cert.ev_fkE`,
-- `matDot_fmat_Y5` from `Cert.matDot_fmat_Y3`, `matDot_S5` from `Cert.matDot_S3`, `key_F5` from `Cert.key_F`,
-- `CertK5` from `Cert.Cert3` (via `Kissing.CertK`), `CertK5.blk` from `Cert.Cert3.blk`,
-- `CertK5.m` from `Cert.Cert3.m`, `CertK5.K` from `Cert.Cert3.K`, `CertK5.Fm` from `Cert.Cert3.Fm`,
-- `CertK5.idE` from `Cert.Cert3.idE`, `CertK5.check` from `Cert.Cert3.check`,
-- `CertK5.check_parts` from `Cert.Cert3.check_parts`, `CertK5.hpt5` from `Cert.Cert3.hpt_gramCut`,
-- `kStat_idE5` from `Case1.c1Stat_idE`.

/-!
# An exact three-point certificate checker for kissing configurations in `ℝ⁵`

This is the five-dimensional counterpart of `Kissing.CertK`. The region `GramHalf`, the multiplier table
`codeK`, the SOS blocks `KBlk` and the data-independent machinery (`Kron.Ex`, `Cert.chk`, `Cert.Blk`, `Cert.sqfE`,
`Cert.ftotE`, `Case1.c1Stat`) are reused from there. What changes is the kernel: the `F`-part of the identity is
built from the `S⁴` kernel `Q5`, so this file adds its polynomial expression `q5E`, the block expressions `fk5E`,
and the link `key_F5` between `Rk5` and `ftotTerm`.

A certificate `cf : CertK5` has the same shape as in dimension 3, but its check additionally requires
`cf.K ≤ 9`: Bachoc–Vallentin positivity on `S⁴` is proved for degrees `k ≤ 8` only
(`Kissing5.matDot_moment_nonneg5`), and `no_config5` feeds it to `Kissing5.three_point_bound_of_forall5`.
A checked certificate with positive margin excludes `n` unit vectors of `ℝ⁵` with all pairwise inner products
at most `1/2`.
-/

open Real
open scoped RealInnerProductSpace

namespace Kissing5

open ThomsonN7 ThomsonN7.ThreePoint ThomsonN7.Kron ThomsonN7.Kron.Ex ThomsonN7.Cert
open Kissing

/-! ## The kernel `Q5` as a polynomial expression -/

/-- `Q5 k` as an expression with integer coefficients. -/
def q5E : ℕ → Ex
  | 0 => c 1
  | 1 => smul 2 (sub T (mul U V))
  | k + 2 => sub (smul (2 * (k : ℤ) + 4) (mul (sub T (mul U V)) (q5E (k + 1))))
      (smul (((k : ℤ) + 1) * ((k : ℤ) + 2)) (mul (mul (sub (c 1) (Ex.sq U)) (sub (c 1) (Ex.sq V))) (q5E k)))

lemma ev_q5E (u v t : ℝ) : ∀ k, (q5E k).ev u v t = Q5 k u v t
  | 0 => by simp [q5E, Q5]
  | 1 => by simp [q5E, Q5, ev_smul]
  | k + 2 => by
    simp only [q5E, Q5, ev_sub, ev_mul, ev_smul, ev_T, ev_U, ev_V, ev_c, ev_sq,
      ev_q5E u v t (k + 1), ev_q5E u v t k]
    push_cast
    ring

/-! ## `F`-blocks against the kernel `Q5` -/

/-- `Λ · Fp_k(u,v,t)` for the `S⁴` kernel, where `Fp_k = ∑_{ab} F_{ab} uᵃ vᵇ Q5_k`. -/
def fk5E (r : ℕ) (b : Blk) (k : ℕ) : Ex := mul (fpE r b) (q5E k)

lemma ev_fk5E (r : ℕ) (b : Blk) (k : ℕ) (u v t : ℝ) :
    (fk5E r b k).ev u v t = ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range r,
      (b.ent r a c : ℝ) * (u ^ a * v ^ c * Q5 k u v t) := by
  rw [fk5E, ev_mul, ev_fpE, ev_q5E, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma matDot_fmat_Y5 (r Lam : ℕ) (b : Blk) (k : ℕ) (u v t : ℝ) :
    matDot (fmat r Lam b) (Y5 r k u v t) = (fk5E r b k).ev u v t / Lam := by
  have h := sum_fin_eq_range r
    (fun a c => (b.ent r a c : ℝ) / Lam * (u ^ a * v ^ c * Q5 k u v t))
  simp only [matDot, fmat, Y5, Matrix.of_apply]
  refine h.trans ?_
  rw [ev_fk5E, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma matDot_S5 {m : ℕ} (F : Matrix (Fin m) (Fin m) ℝ) (k : ℕ) (x y z : ℝ) :
    matDot F (S5 m k x y z) = (1 / 6) * six (fun a b c => matDot F (Y5 m k a b c)) x y z := by
  simp only [S5, matDot_smul, matDot_add, six]

lemma key_F5 {r Lam : ℕ} (b : Blk) (k n : ℕ) (hL : (Lam : ℝ) ≠ 0) (hn : (n : ℝ) - 1 ≠ 0)
    (u v t : ℝ) :
    6 * ((n : ℝ) - 1) * Lam * matDot (fmat r Lam b) (Rk5 n r k u v t)
      = ftotTerm n (fun a b' c => (fk5E r b k).ev a b' c) u v t := by
  rw [matDot_Rk5]
  simp only [Rs, matDot_S5, matDot_fmat_Y5, six, ftotTerm]
  field_simp

/-! ## The certificate -/

/-- A kissing certificate for `n` points of `ℝ⁵`: margin `e = eps / Λ`, kernel blocks `F_k` (in the basis
`uᵃ vᵇ Q5_k`, `F_k = ent / Λ`) and SOS blocks, over the common denominator `Λ = Lam`. -/
structure CertK5 where
  n : ℕ
  Lam : ℕ
  eps : ℤ
  F : List Blk
  S : List Kissing.KBlk

namespace CertK5

/-- The `k`-th `F`-block. -/
def blk (cf : CertK5) (k : ℕ) : Blk := cf.F.getD k Blk.empty

/-- The size of the `k`-th `F`-block. -/
def m (cf : CertK5) (k : ℕ) : ℕ := (cf.blk k).Δ.length

/-- The number of `F`-blocks. -/
def K (cf : CertK5) : ℕ := cf.F.length

/-- The `k`-th `F`-matrix. -/
noncomputable def Fm (cf : CertK5) (k : ℕ) : Matrix (Fin (cf.m k)) (Fin (cf.m k)) ℝ :=
  fmat (cf.m k) cf.Lam (cf.blk k)

/-- The polynomial identity, scaled by `6 (n-1) C(n,2) Λ`, as an expression. -/
def idE (cf : CertK5) : Ex :=
  sub (sub (c (-(6 * ((cf.n : ℤ) - 1) * cf.eps)))
      (smul (cf.n.choose 2 : ℕ) (ftotE cf.n cf.K fun k => fk5E (cf.m k) (cf.blk k) k)))
    (smul (6 * ((cf.n : ℤ) - 1) * (cf.n.choose 2 : ℕ)) (sumE (cf.S.map kblkE)))

/-- The computable check; the bound `K ≤ 9` is the range of degrees for which positivity on `S⁴` is proved. -/
def check (cf : CertK5) : Bool :=
  decide (3 ≤ cf.n) && decide (0 < cf.Lam) && decide (cf.K ≤ 9) &&
  (List.range cf.K).all (fun k => (cf.blk k).ok (cf.m k)) &&
  cf.S.all (fun s => s.B.ok s.z.length) && chk cf.idE

lemma check_parts {cf : CertK5} (h : cf.check = true) :
    3 ≤ cf.n ∧ 0 < cf.Lam ∧ cf.K ≤ 9 ∧ (∀ k < cf.K, (cf.blk k).ok (cf.m k) = true) ∧
    (cf.S.all (fun s => s.B.ok s.z.length) = true) ∧ chk cf.idE = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, hK⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, hK, fun k hk => ?_, h4, h5⟩
  exact (List.all_eq_true.mp h3) k (List.mem_range.mpr hk)

/-- The pointwise inequality on `GramHalf`. -/
lemma hpt5 (cf : CertK5) (hc : cf.check = true) {u v t : ℝ} (hg : GramHalf u v t) :
    ∑ k ∈ Finset.range cf.K, matDot (cf.Fm k) (Rk5 cf.n (cf.m k) k u v t)
      ≤ ((0 : ℝ) + 0 + 0) / 3 - ((cf.eps : ℝ) / cf.Lam) / (cf.n.choose 2 : ℕ) := by
  obtain ⟨hn, hL, hK, hF, hS, hz⟩ := check_parts hc
  have hev := chk_sound hz u v t
  simp only [idE, ev_sub, ev_smul, ev_c, ev_ftotE, ev_sumE] at hev
  have hnr : (3 : ℝ) ≤ cf.n := by exact_mod_cast hn
  have hn1 : (cf.n : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (cf.n : ℝ) - 1 := by linarith
    exact this.ne'
  have hLpos : (0 : ℝ) < cf.Lam := by exact_mod_cast hL
  have hC : (0 : ℝ) < (cf.n.choose 2 : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hFp : ∑ k ∈ Finset.range cf.K,
        ftotTerm cf.n (fun a b c => (fk5E (cf.m k) (cf.blk k) k).ev a b c) u v t
      = 6 * ((cf.n : ℝ) - 1) * cf.Lam
        * ∑ k ∈ Finset.range cf.K, matDot (cf.Fm k) (Rk5 cf.n (cf.m k) k u v t) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => (key_F5 (cf.blk k) k cf.n hLpos.ne' hn1 u v t).symm
  rw [hFp] at hev
  push_cast at hev
  exact Kissing.CertK.final_le hnr hC hLpos (kblk_sum_nonneg cf.S hS hg) hev

/-- **Soundness.** A checked certificate with positive margin excludes every configuration of `n` unit vectors in
`ℝ⁵` with all pairwise inner products at most `1/2`. -/
theorem no_config5 (cf : CertK5) (hc : cf.check = true) (heps : 0 < cf.eps) (x : Fin cf.n → R5)
    (hx : ∀ i, ‖x i‖ = 1) (hhalf : ∀ i j, i ≠ j → ⟪x i, x j⟫ ≤ 1 / 2) : False := by
  obtain ⟨hn, hL, hK, hF, hS, hz⟩ := check_parts hc
  have hb := three_point_bound_of_forall5 hn (fun s => 2 * s ≤ 1) cf.K cf.m cf.Fm
    (fun _ => 0) ((cf.eps : ℝ) / cf.Lam)
    (fun u v t hg hu hv ht => hpt5 cf hc ⟨hg, hu, hv, ht⟩) x hx
    (fun k hk => matDot_moment_nonneg5 (cf.m k) k (by omega) x hx (cf.Fm k)
      (fmat_psd cf.Lam (hF k hk)))
    (fun i j hij => by have := hhalf i j hij; linarith)
  simp only [Finset.sum_const_zero] at hb
  have hpos : (0 : ℝ) < (cf.eps : ℝ) / cf.Lam :=
    div_pos (by exact_mod_cast heps) (by exact_mod_cast hL)
  linarith

end CertK5

/-! ## Chunked statistics of the identity (for the Kronecker check) -/

open ThomsonN7.Case1 in
/-- The statistics of `cf.idE`, in terms of those of its pieces (cf. upstream `Case1.c1Stat_idE`). -/
lemma kStat_idE5 (cf : CertK5) (w D : ℕ) :
    c1Stat w D cf.idE =
      c1Sub (c1Sub (c1C (-(6 * ((cf.n : ℤ) - 1) * cf.eps)))
        (c1Smul (cf.n.choose 2 : ℕ) (c1Sum ((List.range cf.K).map fun k =>
          c1Stat w D (c1FtotK cf.n (fk5E (cf.m k) (cf.blk k) k))))))
        (c1Smul (6 * ((cf.n : ℤ) - 1) * (cf.n.choose 2 : ℕ))
          (c1Sum (cf.S.map fun s => c1Stat w D (kblkE s)))) := by
  simp only [CertK5.idE, c1Stat_sub, c1Stat_smul, c1Stat_c, c1_ftotE_eq, c1Stat_sumRange,
    c1Stat_sumE, List.map_map]
  rfl

end Kissing5
