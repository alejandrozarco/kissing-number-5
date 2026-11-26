import Kissing5.CertK
import Kissing5.Tree.Sound
import Kissing5.Tree.FPart
import Kissing5.G4.Positivity

-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7),
-- via lean/Kissing5/CertK.lean of this package: `CertK5T.blk` from `Cert.Cert3.blk`, `CertK5T.m` from
-- `Cert.Cert3.m`, `CertK5T.K` from `Cert.Cert3.K`, `CertK5T.Fm` from `Cert.Cert3.Fm`, `CertK5T.idE` from
-- `Cert.Cert3.idE`, `CertK5T.check_parts` from `Cert.Cert3.check_parts`, `CertK5T.hpt5` from
-- `Cert.Cert3.hpt_gramCut`, `kStat_idE5T` from `Case1.c1Stat_idE`.

/-!
# A certificate checker with tree-encoded SOS blocks

`CertK5T` is `Kissing5.CertK5` with the SOS blocks given as explicit sums of squares (`TBlk`) instead of
`(basis, L D Lᵀ + Δ)` data (`Kissing.KBlk`):

* a block is a multiplier `gKE g` (nonnegative on `GramHalf`) times a sum of rows `q · (Σ t)²` (`sqEx`) and
  remainder rows `di z² + Σ_j |e_j| (z ± z_j)²` (`pairRowEx`, or `dEx` without pairs);
* every row is a nonnegative multiple of a square or a sum of such, so no positive-semidefiniteness check is needed
  (`tblkE_nonneg`): `check` drops the `Blk.ok` test of the SOS blocks and keeps everything else;
* `c1Stat_tblkE`: the Kronecker statistics of a block are those of its rows, which the core-only row checks
  (`Kissing5.Tree.Core`) compute (`sqRow_toC1`, `PRow.st_toC1`).

The soundness proof `no_config5T` is that of `Kissing5.CertK5.no_config5`, with `tblk_sum_nonneg` in place of
`kblk_sum_nonneg`, and with positivity on `S⁴` for degrees `k ≤ 16` (`Kissing5.G4.matDot_moment_nonneg5`, addition
identities checked by Kronecker substitution) in place of `k ≤ 8`: `check` requires `K ≤ 17`.

The `F`-part of the identity uses `fkB` (`Kissing5.Tree.FPart`: the same polynomial as `Kissing5.fk5E`, `ev_fkB`, in
balanced sums) so that its Kronecker statistics can be checked at degree 32. For certificates whose SOS rows are
checked in chunks, `c1Stat_tblkE_chunks` gives the statistics of a block from the chunk sums, summed in groups
(`toC1_sumSt_groups`).
-/

open Real
open scoped RealInnerProductSpace

namespace Kissing5.Tree

open ThomsonN7 ThomsonN7.ThreePoint ThomsonN7.Kron ThomsonN7.Cert ThomsonN7.Case1
open Kissing Kissing5

/-! ## Rows and blocks -/

/-- The polynomial of a remainder row. -/
def PRow.toEx (p : PRow) : Ex :=
  match p.t with
  | none => dEx p.a p.b p.d p.di
  | some t => pairRowEx p.a p.b p.d p.di t

theorem PRow.st_toC1 (w D : ℕ) (p : PRow) : (p.st w D).toC1 = c1Stat w D p.toEx := by
  rcases p with ⟨a, b, d, di, _ | t⟩
  · exact dRow_toC1 w D a b d di
  · exact pairRow_toC1 w D a b d di t

theorem PRow.toEx_nonneg (p : PRow) (u v x : ℝ) : 0 ≤ p.toEx.ev u v x := by
  rcases p with ⟨a, b, d, di, _ | t⟩
  · exact dEx_nonneg a b d di u v x
  · exact pairRowEx_nonneg a b d di t u v x

/-- A tree-encoded SOS block: multiplier codes `g`, squares `q · (Σ t)²`, remainder rows. -/
structure TBlk where
  g : List ℕ
  sq : List (ℕ × Kissing5.Tree.T)
  pr : List PRow

/-- The sum of squares of a block (without its multiplier). -/
def TBlk.sosE (s : TBlk) : Ex :=
  Ex.add (Ex.sumE (s.sq.map fun x => sqEx x.1 x.2)) (Ex.sumE (s.pr.map PRow.toEx))

/-- The polynomial `g · (sum of squares)` of a block. -/
def tblkE (s : TBlk) : Ex := Ex.mul (gKE s.g) s.sosE

theorem TBlk.sosE_nonneg (s : TBlk) (u v x : ℝ) : 0 ≤ s.sosE.ev u v x := by
  simp only [TBlk.sosE, Ex.ev_add, Ex.ev_sumE]
  refine add_nonneg (List.sum_nonneg fun y hy => ?_) (List.sum_nonneg fun y hy => ?_)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 he
    exact sqEx_nonneg _ _ u v x
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 he
    exact p.toEx_nonneg u v x

theorem tblkE_nonneg (s : TBlk) {u v x : ℝ} (hg : GramHalf u v x) : 0 ≤ (tblkE s).ev u v x := by
  rw [tblkE, Ex.ev_mul]
  exact mul_nonneg (gKE_nonneg s.g hg) (s.sosE_nonneg u v x)

theorem tblk_sum_nonneg (S : List TBlk) {u v x : ℝ} (hg : GramHalf u v x) :
    0 ≤ ((S.map tblkE).map fun e => e.ev u v x).sum := by
  refine List.sum_nonneg fun y hy => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 he
  exact tblkE_nonneg s hg

/-- The Kronecker statistics of a block, from the core-only row statistics. -/
theorem c1Stat_tblkE (w D : ℕ) (s : TBlk) :
    c1Stat w D (tblkE s) =
      c1Mul (c1Stat w D (gKE s.g))
        (c1Add (c1Sum (s.sq.map fun x => (sqRow w D x.1 x.2).toC1))
          (c1Sum (s.pr.map fun p => (p.st w D).toC1))) := by
  have h1 : (s.sq.map fun x => (sqRow w D x.1 x.2).toC1) =
      (s.sq.map fun x => sqEx x.1 x.2).map (c1Stat w D) := by
    rw [List.map_map]
    exact List.map_congr_left fun x _ => sqRow_toC1 w D x.1 x.2
  have h2 : (s.pr.map fun p => (p.st w D).toC1) = (s.pr.map PRow.toEx).map (c1Stat w D) := by
    rw [List.map_map]
    exact List.map_congr_left fun p _ => p.st_toC1 w D
  rw [h1, h2, ← c1Stat_sumE, ← c1Stat_sumE]
  rfl

/-! ## Blocks checked in chunks -/

theorem toC1_sumSt (l : List St) : (sumSt l).toC1 = c1Sum (l.map St.toC1) := by
  cases l with
  | nil => simp [sumSt, St.toC1, St.kv, c1Sum, c1C]
  | cons s ss => exact sumSt_toC1 s ss

theorem c1Add_zero_left (s : C1Stat) : c1Add (c1C 0) s = s := by
  obtain ⟨a, b, c, d, e⟩ := s
  simp [c1Add, c1C]

theorem c1Add_assoc (s t r : C1Stat) : c1Add (c1Add s t) r = c1Add s (c1Add t r) := by
  obtain ⟨a, b, c, d, e⟩ := s
  obtain ⟨a', b', c', d', e'⟩ := t
  obtain ⟨a'', b'', c'', d'', e''⟩ := r
  simp only [c1Add, Prod.mk.injEq]
  exact ⟨Nat.add_assoc _ _ _, Nat.max_assoc _ _ _, Nat.max_assoc _ _ _, Nat.max_assoc _ _ _, Int.add_assoc _ _ _⟩

theorem c1Sum_append (a b : List C1Stat) : c1Sum (a ++ b) = c1Add (c1Sum a) (c1Sum b) := by
  induction a with
  | nil => exact (c1Add_zero_left _).symm
  | cons x a ih =>
    show c1Add x (c1Sum (a ++ b)) = c1Add (c1Add x (c1Sum a)) (c1Sum b)
    rw [ih, c1Add_assoc]

/-- The statistics of the rows of a block given as a list of chunks: the sum of the chunk sums. -/
theorem c1Sum_flatten {α : Type} (f : α → St) (L : List (List α)) :
    c1Sum ((L.flatten).map fun a => (f a).toC1) = (sumSt (L.map fun c => sumSt (c.map f))).toC1 := by
  rw [toC1_sumSt, List.map_map]
  induction L with
  | nil => rfl
  | cons c L ih =>
    rw [List.flatten_cons, List.map_append, c1Sum_append, ih, List.map_cons]
    show c1Add _ _ = c1Add _ _
    congr 1
    rw [Function.comp_apply, toC1_sumSt, List.map_map]
    rfl

/-- A list of statistics summed in groups: `sumSt (G.flatten)` and `sumSt (G.map sumSt)` have the same `C1Stat`. -/
theorem toC1_sumSt_groups (G : List (List St)) (V U : List St) (W : St) (hG : G.flatten = V)
    (hU : G.map sumSt = U) (hW : sumSt U = W) : (sumSt V).toC1 = W.toC1 := by
  have h := c1Sum_flatten (fun s : St => s) G
  simp only [List.map_id'] at h
  rw [← hG, toC1_sumSt, h, hU, hW]

/-- The statistics of a block whose squares and remainder rows are given in chunks `Q`, `P`, from the chunk sums
`VQ`, `VP` (checked one chunk at a time), summed in groups `GQ`, `GP` (group sums `UQ`, `UP`, one check per group)
and then over the groups (`WQ`, `WP`). -/
theorem c1Stat_tblkE_chunks (w D : ℕ) (g : List ℕ) (Q : List (List (ℕ × Kissing5.Tree.T)))
    (P : List (List PRow)) (VQ VP : List St) (GQ GP : List (List St)) (UQ UP : List St) (WQ WP : St)
    (hVQ : Q.map (fun c => sumSt (c.map fun x => sqRow w D x.1 x.2)) = VQ) (hGQ : GQ.flatten = VQ)
    (hUQ : GQ.map sumSt = UQ) (hWQ : sumSt UQ = WQ)
    (hVP : P.map (fun c => sumSt (c.map fun p => p.st w D)) = VP) (hGP : GP.flatten = VP)
    (hUP : GP.map sumSt = UP) (hWP : sumSt UP = WP) :
    c1Stat w D (tblkE ⟨g, Q.flatten, P.flatten⟩) = c1Mul (c1Stat w D (gKE g)) (c1Add WQ.toC1 WP.toC1) := by
  rw [c1Stat_tblkE]
  have h1 := c1Sum_flatten (fun x : ℕ × Kissing5.Tree.T => sqRow w D x.1 x.2) Q
  have h2 := c1Sum_flatten (fun p : PRow => p.st w D) P
  rw [hVQ, toC1_sumSt_groups GQ VQ UQ WQ hGQ hUQ hWQ] at h1
  rw [hVP, toC1_sumSt_groups GP VP UP WP hGP hUP hWP] at h2
  simp only at h1 h2 ⊢
  rw [h1, h2]

/-! ## The certificate -/

/-- A kissing certificate for `n` points of `ℝ⁵` with tree-encoded SOS blocks: margin `e = eps / Λ`, kernel blocks
`F_k` (as in `Kissing5.CertK5`) and SOS blocks `S`, over the common denominator `Λ = Lam`. -/
structure CertK5T where
  n : ℕ
  Lam : ℕ
  eps : ℤ
  F : List Blk
  S : List TBlk

namespace CertK5T

/-- The `k`-th `F`-block. -/
def blk (cf : CertK5T) (k : ℕ) : Blk := cf.F.getD k Blk.empty

/-- The size of the `k`-th `F`-block. -/
def m (cf : CertK5T) (k : ℕ) : ℕ := (cf.blk k).Δ.length

/-- The number of `F`-blocks. -/
def K (cf : CertK5T) : ℕ := cf.F.length

/-- The `k`-th `F`-matrix. -/
noncomputable def Fm (cf : CertK5T) (k : ℕ) : Matrix (Fin (cf.m k)) (Fin (cf.m k)) ℝ :=
  fmat (cf.m k) cf.Lam (cf.blk k)

/-- The polynomial identity, scaled by `6 (n-1) C(n,2) Λ`, as an expression. -/
def idE (cf : CertK5T) : Ex :=
  Ex.sub (Ex.sub (Ex.c (-(6 * ((cf.n : ℤ) - 1) * cf.eps)))
      (Ex.smul (cf.n.choose 2 : ℕ) (ftotE cf.n cf.K fun k => fkB (cf.m k) (cf.blk k) k)))
    (Ex.smul (6 * ((cf.n : ℤ) - 1) * (cf.n.choose 2 : ℕ)) (Ex.sumE (cf.S.map tblkE)))

/-- The computable check: as `Kissing5.CertK5.check`, without a test of the SOS blocks (nonnegative by
construction). -/
def check (cf : CertK5T) : Bool :=
  decide (3 ≤ cf.n) && decide (0 < cf.Lam) && decide (cf.K ≤ 17) &&
  (List.range cf.K).all (fun k => (cf.blk k).ok (cf.m k)) && chk cf.idE

lemma check_parts {cf : CertK5T} (h : cf.check = true) :
    3 ≤ cf.n ∧ 0 < cf.Lam ∧ cf.K ≤ 17 ∧ (∀ k < cf.K, (cf.blk k).ok (cf.m k) = true) ∧
    chk cf.idE = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, hK⟩, h3⟩, h5⟩ := h
  refine ⟨h1, h2, hK, fun k hk => ?_, h5⟩
  exact (List.all_eq_true.mp h3) k (List.mem_range.mpr hk)

/-- The pointwise inequality on `GramHalf`. -/
lemma hpt5 (cf : CertK5T) (hc : cf.check = true) {u v t : ℝ} (hg : GramHalf u v t) :
    ∑ k ∈ Finset.range cf.K, matDot (cf.Fm k) (Rk5 cf.n (cf.m k) k u v t)
      ≤ ((0 : ℝ) + 0 + 0) / 3 - ((cf.eps : ℝ) / cf.Lam) / (cf.n.choose 2 : ℕ) := by
  obtain ⟨hn, hL, hK, hF, hz⟩ := check_parts hc
  have hev := chk_sound hz u v t
  simp only [idE, Ex.ev_sub, Ex.ev_smul, Ex.ev_c, ev_ftotE, Ex.ev_sumE] at hev
  have hnr : (3 : ℝ) ≤ cf.n := by exact_mod_cast hn
  have hn1 : (cf.n : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (cf.n : ℝ) - 1 := by linarith
    exact this.ne'
  have hLpos : (0 : ℝ) < cf.Lam := by exact_mod_cast hL
  have hC : (0 : ℝ) < (cf.n.choose 2 : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hFp : ∑ k ∈ Finset.range cf.K,
        ftotTerm cf.n (fun a b c => (fkB (cf.m k) (cf.blk k) k).ev a b c) u v t
      = 6 * ((cf.n : ℝ) - 1) * cf.Lam
        * ∑ k ∈ Finset.range cf.K, matDot (cf.Fm k) (Rk5 cf.n (cf.m k) k u v t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hf : (fun a b c => (fkB (cf.m k) (cf.blk k) k).ev a b c)
        = (fun a b c => (fk5E (cf.m k) (cf.blk k) k).ev a b c) := by
      funext a b c; exact ev_fkB _ _ _ a b c
    rw [hf]
    exact (key_F5 (cf.blk k) k cf.n hLpos.ne' hn1 u v t).symm
  rw [hFp] at hev
  push_cast at hev
  exact Kissing.CertK.final_le hnr hC hLpos (tblk_sum_nonneg cf.S hg) hev

/-- **Soundness.** A checked certificate with positive margin excludes every configuration of `n` unit vectors in
`ℝ⁵` with all pairwise inner products at most `1/2`. -/
theorem no_config5T (cf : CertK5T) (hc : cf.check = true) (heps : 0 < cf.eps) (x : Fin cf.n → R5)
    (hx : ∀ i, ‖x i‖ = 1) (hhalf : ∀ i j, i ≠ j → ⟪x i, x j⟫ ≤ 1 / 2) : False := by
  obtain ⟨hn, hL, hK, hF, hz⟩ := check_parts hc
  have hb := three_point_bound_of_forall5 hn (fun s => 2 * s ≤ 1) cf.K cf.m cf.Fm
    (fun _ => 0) ((cf.eps : ℝ) / cf.Lam)
    (fun u v t hg hu hv ht => hpt5 cf hc ⟨hg, hu, hv, ht⟩) x hx
    (fun k hk => Kissing5.G4.matDot_moment_nonneg5 (cf.m k) k (by omega) x hx (cf.Fm k)
      (fmat_psd cf.Lam (hF k hk)))
    (fun i j hij => by have := hhalf i j hij; linarith)
  simp only [Finset.sum_const_zero] at hb
  have hpos : (0 : ℝ) < (cf.eps : ℝ) / cf.Lam :=
    div_pos (by exact_mod_cast heps) (by exact_mod_cast hL)
  linarith

end CertK5T

/-- The statistics of `cf.idE`, in terms of those of its pieces (as `Kissing5.kStat_idE5`). -/
lemma kStat_idE5T (cf : CertK5T) (w D : ℕ) :
    c1Stat w D cf.idE =
      c1Sub (c1Sub (c1C (-(6 * ((cf.n : ℤ) - 1) * cf.eps)))
        (c1Smul (cf.n.choose 2 : ℕ) (c1Sum ((List.range cf.K).map fun k =>
          c1Stat w D (c1FtotK cf.n (fkB (cf.m k) (cf.blk k) k))))))
        (c1Smul (6 * ((cf.n : ℤ) - 1) * (cf.n.choose 2 : ℕ))
          (c1Sum (cf.S.map fun s => c1Stat w D (tblkE s)))) := by
  simp only [CertK5T.idE, c1Stat_sub, c1Stat_smul, c1Stat_c, c1_ftotE_eq, c1Stat_sumRange,
    c1Stat_sumE, List.map_map]
  rfl

end Kissing5.Tree
