import ThomsonGen.Case1Stat
import Kissing8.Kernel

/-!
# Gegenbauer addition identities by Kronecker substitution (any degree)

The positivity of the Bachoc–Vallentin kernels on `S⁴` rests on `PSD 4 (Zg 4 k)`, proved by induction on the
dimension (`Kissing8.psd_step`) from the solid addition identities from `ℝ^d` to `ℝ^(d-1)`:
`Zg d k (a a' + w) (a² + P) (a'² + Q) = ∑_{m ≤ k} c_m · B_m(a) · B_m(a') · Zp_m(w, P, Q)` with
`B_m(a) = Zg (d + 2m) (k - m) a (a² + P) 1`. Proving each identity by `ring` costs too much memory beyond `k = 8`.
Here an identity is reduced to a polynomial identity in three variables, checked by Kronecker substitution
(`ThomsonN7.Kron.Ex.ev_eq_zero_of_kev`) with kernel integer arithmetic:

* `zgE2`, `zcE2`: the kernels as expression trees `ThomsonN7.Kron.Ex`, by their recursions (`zgE2_ev`, `zcE2_ev`);
  `zgS2`, `zcS2`: their statistics `c1Stat`, by the same recursions (`zgE2_stat`, `zcE2_stat`), so that the kernel
  computes them in linearly many steps;
* `idE d k L N`: `L · (left side) - ∑ N_m · (summand m)` at `P = Q = 1` in the variables `u = a`, `v = a'`, `t = w`;
  `chkId d k L N w D`: the Boolean check (`0 < L`, `N_m ≥ 0`, `ℓ¹ < 2^w`, degrees `< D`, Kronecker value `0`);
* `add_of_chk`: a passing check gives the identity, with coefficients `N_m / L`, for all `P, Q ≥ 0`: first at
  `P = Q = 1`, then for `P, Q > 0` by the homogeneity of the kernels (`Zg_hom`, `Zg_hom'`, …), then for `P, Q ≥ 0` by
  continuity;
* `psd_step'`: `Kissing8.psd_step` with the identity needed only for `P, Q ≥ 0`; `psd_of_chk`: `PSD d (Zg d k)`.
-/

open ThomsonN7 ThomsonN7.Kron ThomsonN7.Case1 Kissing8 Finset

namespace Kissing5.G4

/-! ## The kernels as expressions and their statistics -/

/-- `(Zg d k, Zg d (k + 1))` at the expressions `s p q`. -/
def zgE2 (d : ℕ) (s p q : Ex) : ℕ → Ex × Ex
  | 0 => (Ex.c 1, Ex.mul (Ex.c ((d : ℤ) - 2)) s)
  | k + 1 =>
    let r := zgE2 d s p q k
    (r.2, Ex.add (Ex.mul (Ex.c (2 * (k : ℤ) + d)) (Ex.mul s r.2))
      (Ex.mul (Ex.c (-(((k : ℤ) + 1) * ((k : ℤ) + d - 2)))) (Ex.mul (Ex.mul p q) r.1)))

/-- `(Zc k, Zc (k + 1))` at the expressions `s p q`. -/
def zcE2 (s p q : Ex) : ℕ → Ex × Ex
  | 0 => (Ex.c 1, s)
  | k + 1 =>
    let r := zcE2 s p q k
    (r.2, Ex.add (Ex.mul (Ex.c 2) (Ex.mul s r.2)) (Ex.mul (Ex.c (-1)) (Ex.mul (Ex.mul p q) r.1)))

/-- The statistics of `zgE2`, by the same recursion. -/
def zgS2 (d : ℕ) (s p q : C1Stat) : ℕ → C1Stat × C1Stat
  | 0 => (c1C 1, c1Mul (c1C ((d : ℤ) - 2)) s)
  | k + 1 =>
    let r := zgS2 d s p q k
    (r.2, c1Add (c1Mul (c1C (2 * (k : ℤ) + d)) (c1Mul s r.2))
      (c1Mul (c1C (-(((k : ℤ) + 1) * ((k : ℤ) + d - 2)))) (c1Mul (c1Mul p q) r.1)))

/-- The statistics of `zcE2`, by the same recursion. -/
def zcS2 (s p q : C1Stat) : ℕ → C1Stat × C1Stat
  | 0 => (c1C 1, s)
  | k + 1 =>
    let r := zcS2 s p q k
    (r.2, c1Add (c1Mul (c1C 2) (c1Mul s r.2)) (c1Mul (c1C (-1)) (c1Mul (c1Mul p q) r.1)))

theorem zgE2_stat (w D d : ℕ) (s p q : Ex) (k : ℕ) :
    zgS2 d (c1Stat w D s) (c1Stat w D p) (c1Stat w D q) k =
      (c1Stat w D (zgE2 d s p q k).1, c1Stat w D (zgE2 d s p q k).2) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [zgS2, zgE2, ih, c1Stat]

theorem zcE2_stat (w D : ℕ) (s p q : Ex) (k : ℕ) :
    zcS2 (c1Stat w D s) (c1Stat w D p) (c1Stat w D q) k =
      (c1Stat w D (zcE2 s p q k).1, c1Stat w D (zcE2 s p q k).2) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [zcS2, zcE2, ih, c1Stat]

theorem zgE2_ev (d : ℕ) (s p q : Ex) (u v t : ℝ) (k : ℕ) :
    (zgE2 d s p q k).1.ev u v t = Zg d k (s.ev u v t) (p.ev u v t) (q.ev u v t) ∧
    (zgE2 d s p q k).2.ev u v t = Zg d (k + 1) (s.ev u v t) (p.ev u v t) (q.ev u v t) := by
  induction k with
  | zero =>
    refine ⟨by simp [zgE2, Zg], ?_⟩
    simp only [zgE2, Ex.ev_mul, Ex.ev_c, Zg]
    push_cast; ring
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hz : Zg d (k + 1 + 1) (s.ev u v t) (p.ev u v t) (q.ev u v t) =
        (2 * (k : ℝ) + d) * s.ev u v t * Zg d (k + 1) (s.ev u v t) (p.ev u v t) (q.ev u v t)
          - ((k : ℝ) + 1) * ((k : ℝ) + d - 2) * (p.ev u v t * q.ev u v t)
            * Zg d k (s.ev u v t) (p.ev u v t) (q.ev u v t) := rfl
    rw [hz, ← ih.1, ← ih.2]
    simp only [zgE2, Ex.ev_add, Ex.ev_mul, Ex.ev_c]
    push_cast; ring

theorem zcE2_ev (s p q : Ex) (u v t : ℝ) (k : ℕ) :
    (zcE2 s p q k).1.ev u v t = Zc k (s.ev u v t) (p.ev u v t) (q.ev u v t) ∧
    (zcE2 s p q k).2.ev u v t = Zc (k + 1) (s.ev u v t) (p.ev u v t) (q.ev u v t) := by
  induction k with
  | zero => exact ⟨by simp [zcE2, Zc], by simp [zcE2, Zc]⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hz : Zc (k + 1 + 1) (s.ev u v t) (p.ev u v t) (q.ev u v t) =
        2 * s.ev u v t * Zc (k + 1) (s.ev u v t) (p.ev u v t) (q.ev u v t)
          - (p.ev u v t * q.ev u v t) * Zc k (s.ev u v t) (p.ev u v t) (q.ev u v t) := rfl
    rw [hz, ← ih.1, ← ih.2]
    simp only [zcE2, Ex.ev_add, Ex.ev_mul, Ex.ev_c]
    push_cast; ring

/-! ## The identity at `P = Q = 1` and its check -/

/-- The kernel of `ℝ^(d-1)` in the identity from `ℝ^d`: `Zc` for `d = 3`, `Zg (d - 1)` otherwise. -/
noncomputable def Zp (d m : ℕ) : ℝ → ℝ → ℝ → ℝ := if d = 3 then Zc m else Zg (d - 1) m

/-- `Zp d m` at the expressions `s p q`. -/
def zpE (d m : ℕ) (s p q : Ex) : Ex := if d = 3 then (zcE2 s p q m).1 else (zgE2 (d - 1) s p q m).1

/-- The statistics of `zpE`. -/
def zpS (d m : ℕ) (s p q : C1Stat) : C1Stat := if d = 3 then (zcS2 s p q m).1 else (zgS2 (d - 1) s p q m).1

theorem zpE_stat (w D d m : ℕ) (s p q : Ex) :
    zpS d m (c1Stat w D s) (c1Stat w D p) (c1Stat w D q) = c1Stat w D (zpE d m s p q) := by
  unfold zpS zpE
  split
  · rw [zcE2_stat]
  · rw [zgE2_stat]

theorem zpE_ev (d m : ℕ) (s p q : Ex) (u v t : ℝ) :
    (zpE d m s p q).ev u v t = Zp d m (s.ev u v t) (p.ev u v t) (q.ev u v t) := by
  unfold zpE Zp
  split
  · exact (zcE2_ev s p q u v t m).1
  · exact (zgE2_ev (d - 1) s p q u v t m).1

/-- `u v + t`, `u² + 1`, `v² + 1`. -/
def sE : Ex := Ex.add (Ex.mul Ex.U Ex.V) Ex.T
def pE : Ex := Ex.add (Ex.mul Ex.U Ex.U) Ex.one
def qE : Ex := Ex.add (Ex.mul Ex.V Ex.V) Ex.one

/-- The summand `m` of the identity at `P = Q = 1`, without its coefficient. -/
def termE (d k m : ℕ) : Ex :=
  Ex.mul (Ex.mul (zgE2 (d + 2 * m) Ex.U pE Ex.one (k - m)).1 (zgE2 (d + 2 * m) Ex.V qE Ex.one (k - m)).1)
    (zpE d m Ex.T Ex.one Ex.one)

/-- `L · Zg d k (u v + t) (u² + 1) (v² + 1) - ∑_{m ≤ k} N_m · (summand m)`. -/
def idE (d k : ℕ) (L : ℤ) (N : List ℤ) : Ex :=
  Ex.sub (Ex.smul L (zgE2 d sE pE qE k).1) (Ex.sumRange (k + 1) fun m => Ex.smul (N.getD m 0) (termE d k m))

/-- The statistics of `idE`, through `zgS2`, `zcS2`. -/
def idS (d k : ℕ) (L : ℤ) (N : List ℤ) (w D : ℕ) : C1Stat :=
  let u := c1Stat w D Ex.U
  let v := c1Stat w D Ex.V
  let t := c1Stat w D Ex.T
  let o := c1Stat w D Ex.one
  let p := c1Stat w D pE
  let q := c1Stat w D qE
  c1Sub (c1Smul L (zgS2 d (c1Stat w D sE) p q k).1)
    (c1Sum ((List.range (k + 1)).map fun m => c1Smul (N.getD m 0)
      (c1Mul (c1Mul (zgS2 (d + 2 * m) u p o (k - m)).1 (zgS2 (d + 2 * m) v q o (k - m)).1) (zpS d m t o o))))

theorem idE_stat (d k : ℕ) (L : ℤ) (N : List ℤ) (w D : ℕ) : c1Stat w D (idE d k L N) = idS d k L N w D := by
  simp only [idE, idS, c1Stat_sub, c1Stat_smul, c1Stat_sumRange, termE, zgE2_stat, zpE_stat]
  rfl

/-- The Boolean check of the identity at `P = Q = 1`. -/
def chkId (d k : ℕ) (L : ℤ) (N : List ℤ) (w D : ℕ) : Bool :=
  let s := idS d k L N w D
  decide (0 < L) && N.all (fun n => decide (0 ≤ n)) && decide (s.1 < 2 ^ w) && decide (s.2.1 < D) &&
    decide (s.2.2.1 < D) && decide (s.2.2.2.1 < D) && decide (s.2.2.2.2 = 0)

@[simp] theorem zgE2_ev1 (d : ℕ) (s p q : Ex) (u v t : ℝ) (k : ℕ) :
    (zgE2 d s p q k).1.ev u v t = Zg d k (s.ev u v t) (p.ev u v t) (q.ev u v t) := (zgE2_ev d s p q u v t k).1

/-- A passing check gives the identity at `P = Q = 1`, with coefficients `N_m / L`. -/
theorem add_one_of_chk {d k : ℕ} {L : ℤ} {N : List ℤ} {w D : ℕ} (h : chkId d k L N w D = true) (a a' x : ℝ) :
    Zg d k (a * a' + x) (a * a + 1) (a' * a' + 1) = ∑ m ∈ range (k + 1),
      ((N.getD m 0 : ℝ) / L) * Zg (d + 2 * m) (k - m) a (a * a + 1) 1 * Zg (d + 2 * m) (k - m) a' (a' * a' + 1) 1
        * Zp d m x 1 1 := by
  have hs := idE_stat d k L N w D
  rw [c1Stat_eq] at hs
  simp only [chkId, ← hs, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hL, -⟩, hl⟩, hx⟩, hy⟩, hz⟩, hk⟩ := h
  have h0 := Ex.ev_eq_zero_of_kev (idE d k L N) w D hx hy hz hl hk a a' x
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [idE, termE, Ex.ev_sub, Ex.ev_smul, Ex.ev_sumRange, Ex.ev_mul, zpE_ev, zgE2_ev1, sE, pE, qE,
    Ex.ev_add, Ex.ev_U, Ex.ev_V, Ex.ev_T, Ex.ev_one] at h0
  have hsum : ∑ m ∈ range (k + 1), ((N.getD m 0 : ℝ) / L) * Zg (d + 2 * m) (k - m) a (a * a + 1) 1
      * Zg (d + 2 * m) (k - m) a' (a' * a' + 1) 1 * Zp d m x 1 1
      = (∑ m ∈ range (k + 1), (N.getD m 0 : ℝ) * (Zg (d + 2 * m) (k - m) a (a * a + 1) 1
        * Zg (d + 2 * m) (k - m) a' (a' * a' + 1) 1 * Zp d m x 1 1)) / L := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun m _ => ?_
    field_simp
  rw [hsum, eq_div_iff hL']
  linarith

/-! ## Homogeneity and continuity of the kernels -/

theorem Zg_hom (d k : ℕ) (l s p q : ℝ) : Zg d k (l * s) (l ^ 2 * p) q = l ^ k * Zg d k s p q := by
  have key : ∀ k, Zg d k (l * s) (l ^ 2 * p) q = l ^ k * Zg d k s p q ∧
      Zg d (k + 1) (l * s) (l ^ 2 * p) q = l ^ (k + 1) * Zg d (k + 1) s p q := by
    intro k
    induction k with
    | zero => exact ⟨by simp [Zg], by simp only [zero_add, Zg, pow_one]; ring⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr : ∀ s p q : ℝ, Zg d (k + 1 + 1) s p q = (2 * (k : ℝ) + d) * s * Zg d (k + 1) s p q
          - ((k : ℝ) + 1) * ((k : ℝ) + d - 2) * (p * q) * Zg d k s p q := fun _ _ _ => rfl
      simp only [hr, ih.1, ih.2]
      ring
  exact (key k).1

theorem Zg_hom' (d k : ℕ) (l s p q : ℝ) : Zg d k (l * s) p (l ^ 2 * q) = l ^ k * Zg d k s p q := by
  have key : ∀ k, Zg d k (l * s) p (l ^ 2 * q) = l ^ k * Zg d k s p q ∧
      Zg d (k + 1) (l * s) p (l ^ 2 * q) = l ^ (k + 1) * Zg d (k + 1) s p q := by
    intro k
    induction k with
    | zero => exact ⟨by simp [Zg], by simp only [zero_add, Zg, pow_one]; ring⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr : ∀ s p q : ℝ, Zg d (k + 1 + 1) s p q = (2 * (k : ℝ) + d) * s * Zg d (k + 1) s p q
          - ((k : ℝ) + 1) * ((k : ℝ) + d - 2) * (p * q) * Zg d k s p q := fun _ _ _ => rfl
      simp only [hr, ih.1, ih.2]
      ring
  exact (key k).1

theorem Zc_hom (k : ℕ) (l s p q : ℝ) : Zc k (l * s) (l ^ 2 * p) q = l ^ k * Zc k s p q := by
  have key : ∀ k, Zc k (l * s) (l ^ 2 * p) q = l ^ k * Zc k s p q ∧
      Zc (k + 1) (l * s) (l ^ 2 * p) q = l ^ (k + 1) * Zc (k + 1) s p q := by
    intro k
    induction k with
    | zero => exact ⟨by simp [Zc], by simp [Zc]⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr : ∀ s p q : ℝ, Zc (k + 1 + 1) s p q = 2 * s * Zc (k + 1) s p q - (p * q) * Zc k s p q :=
        fun _ _ _ => rfl
      simp only [hr, ih.1, ih.2]
      ring
  exact (key k).1

theorem Zc_hom' (k : ℕ) (l s p q : ℝ) : Zc k (l * s) p (l ^ 2 * q) = l ^ k * Zc k s p q := by
  have key : ∀ k, Zc k (l * s) p (l ^ 2 * q) = l ^ k * Zc k s p q ∧
      Zc (k + 1) (l * s) p (l ^ 2 * q) = l ^ (k + 1) * Zc (k + 1) s p q := by
    intro k
    induction k with
    | zero => exact ⟨by simp [Zc], by simp [Zc]⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr : ∀ s p q : ℝ, Zc (k + 1 + 1) s p q = 2 * s * Zc (k + 1) s p q - (p * q) * Zc k s p q :=
        fun _ _ _ => rfl
      simp only [hr, ih.1, ih.2]
      ring
  exact (key k).1

theorem Zp_hom (d m : ℕ) (l s p q : ℝ) : Zp d m (l * s) (l ^ 2 * p) q = l ^ m * Zp d m s p q := by
  unfold Zp; split
  · exact Zc_hom m l s p q
  · exact Zg_hom (d - 1) m l s p q

theorem Zp_hom' (d m : ℕ) (l s p q : ℝ) : Zp d m (l * s) p (l ^ 2 * q) = l ^ m * Zp d m s p q := by
  unfold Zp; split
  · exact Zc_hom' m l s p q
  · exact Zg_hom' (d - 1) m l s p q

theorem Zg_cont (d k : ℕ) : Continuous fun x : ℝ × ℝ × ℝ => Zg d k x.1 x.2.1 x.2.2 := by
  have key : ∀ k, (Continuous fun x : ℝ × ℝ × ℝ => Zg d k x.1 x.2.1 x.2.2) ∧
      Continuous fun x : ℝ × ℝ × ℝ => Zg d (k + 1) x.1 x.2.1 x.2.2 := by
    intro k
    induction k with
    | zero => exact ⟨by simp only [Zg]; fun_prop, by simp only [Zg]; fun_prop⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr : ∀ s p q : ℝ, Zg d (k + 1 + 1) s p q = (2 * (k : ℝ) + d) * s * Zg d (k + 1) s p q
          - ((k : ℝ) + 1) * ((k : ℝ) + d - 2) * (p * q) * Zg d k s p q := fun _ _ _ => rfl
      simp only [hr]
      exact ((continuous_const.mul continuous_fst).mul ih.2).sub
        ((continuous_const.mul (continuous_snd.fst.mul continuous_snd.snd)).mul ih.1)
  exact (key k).1

theorem Zc_cont (k : ℕ) : Continuous fun x : ℝ × ℝ × ℝ => Zc k x.1 x.2.1 x.2.2 := by
  have key : ∀ k, (Continuous fun x : ℝ × ℝ × ℝ => Zc k x.1 x.2.1 x.2.2) ∧
      Continuous fun x : ℝ × ℝ × ℝ => Zc (k + 1) x.1 x.2.1 x.2.2 := by
    intro k
    induction k with
    | zero => exact ⟨by simp only [Zc]; fun_prop, by simp only [Zc]; fun_prop⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr : ∀ s p q : ℝ, Zc (k + 1 + 1) s p q = 2 * s * Zc (k + 1) s p q - (p * q) * Zc k s p q :=
        fun _ _ _ => rfl
      simp only [hr]
      exact ((continuous_const.mul continuous_fst).mul ih.2).sub
        ((continuous_snd.fst.mul continuous_snd.snd).mul ih.1)
  exact (key k).1

theorem Zp_cont (d m : ℕ) : Continuous fun x : ℝ × ℝ × ℝ => Zp d m x.1 x.2.1 x.2.2 := by
  unfold Zp; split
  · exact Zc_cont m
  · exact Zg_cont (d - 1) m

/-! ## The identity for all `P, Q ≥ 0` -/

/-- A passing check gives the addition identity, with coefficients `N_m / L`, for all `P, Q ≥ 0`. -/
theorem add_of_chk {d k : ℕ} {L : ℤ} {N : List ℤ} {w D : ℕ} (h : chkId d k L N w D = true)
    (a a' x P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    Zg d k (a * a' + x) (a * a + P) (a' * a' + Q) = ∑ m ∈ range (k + 1),
      ((N.getD m 0 : ℝ) / L) * Zg (d + 2 * m) (k - m) a (a * a + P) 1 * Zg (d + 2 * m) (k - m) a' (a' * a' + Q) 1
        * Zp d m x P Q := by
  -- `P, Q > 0`: scale to `P = Q = 1`
  have hpos : ∀ P Q : ℝ, 0 < P → 0 < Q →
      Zg d k (a * a' + x) (a * a + P) (a' * a' + Q) = ∑ m ∈ range (k + 1),
        ((N.getD m 0 : ℝ) / L) * Zg (d + 2 * m) (k - m) a (a * a + P) 1 * Zg (d + 2 * m) (k - m) a' (a' * a' + Q) 1
          * Zp d m x P Q := by
    intro P Q hP hQ
    set l := Real.sqrt P with hl_def
    set μ := Real.sqrt Q with hμ_def
    have hl : 0 < l := Real.sqrt_pos.mpr hP
    have hμ : 0 < μ := Real.sqrt_pos.mpr hQ
    have hl2 : l ^ 2 = P := Real.sq_sqrt hP.le
    have hμ2 : μ ^ 2 = Q := Real.sq_sqrt hQ.le
    have h1 := add_one_of_chk h (a / l) (a' / μ) (x / (l * μ))
    have e1 : l * (μ * (a / l * (a' / μ) + x / (l * μ))) = a * a' + x := by field_simp
    have e2 : l ^ 2 * (a / l * (a / l) + 1) = a * a + P := by rw [← hl2]; field_simp
    have e3 : μ ^ 2 * (a' / μ * (a' / μ) + 1) = a' * a' + Q := by rw [← hμ2]; field_simp
    have hA : l * (a / l) = a := by field_simp
    have hA' : μ * (a' / μ) = a' := by field_simp
    have hX : l * (μ * (x / (l * μ))) = x := by field_simp
    have hL : Zg d k (a * a' + x) (a * a + P) (a' * a' + Q) = l ^ k * (μ ^ k * ∑ m ∈ range (k + 1),
        ((N.getD m 0 : ℝ) / L) * Zg (d + 2 * m) (k - m) (a / l) (a / l * (a / l) + 1) 1
          * Zg (d + 2 * m) (k - m) (a' / μ) (a' / μ * (a' / μ) + 1) 1 * Zp d m (x / (l * μ)) 1 1) := by
      rw [← h1, ← Zg_hom', ← Zg_hom, e1, e2, e3]
    rw [hL, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hb : Zg (d + 2 * m) (k - m) a (a * a + P) 1
        = l ^ (k - m) * Zg (d + 2 * m) (k - m) (a / l) (a / l * (a / l) + 1) 1 := by
      rw [← Zg_hom, hA, e2]
    have hb' : Zg (d + 2 * m) (k - m) a' (a' * a' + Q) 1
        = μ ^ (k - m) * Zg (d + 2 * m) (k - m) (a' / μ) (a' / μ * (a' / μ) + 1) 1 := by
      rw [← Zg_hom, hA', e3]
    have hz : Zp d m x P Q = l ^ m * (μ ^ m * Zp d m (x / (l * μ)) 1 1) := by
      rw [← Zp_hom', ← Zp_hom, mul_one, mul_one, hX, hl2, hμ2]
    have hlk : l ^ k = l ^ (k - m) * l ^ m := by rw [← pow_add, Nat.sub_add_cancel hmk]
    have hμk : μ ^ k = μ ^ (k - m) * μ ^ m := by rw [← pow_add, Nat.sub_add_cancel hmk]
    rw [hb, hb', hz, hlk, hμk]
    ring
  -- `P, Q ≥ 0`: by continuity
  let F : ℝ × ℝ → ℝ := fun y => Zg d k (a * a' + x) (a * a + y.1) (a' * a' + y.2) - ∑ m ∈ range (k + 1),
    ((N.getD m 0 : ℝ) / L) * Zg (d + 2 * m) (k - m) a (a * a + y.1) 1 * Zg (d + 2 * m) (k - m) a' (a' * a' + y.2) 1
      * Zp d m x y.1 y.2
  have hF : Continuous F := by
    refine ((Zg_cont d k).comp (continuous_const.prodMk ((continuous_const.add continuous_fst).prodMk
      (continuous_const.add continuous_snd)))).sub (continuous_finsetSum _ fun m _ => ?_)
    refine ((continuous_const.mul ?_).mul ?_).mul ?_
    · exact (Zg_cont _ _).comp (continuous_const.prodMk ((continuous_const.add continuous_fst).prodMk
        continuous_const))
    · exact (Zg_cont _ _).comp (continuous_const.prodMk ((continuous_const.add continuous_snd).prodMk
        continuous_const))
    · exact (Zp_cont d m).comp (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))
  have hcl : IsClosed {y : ℝ × ℝ | F y = 0} := isClosed_eq hF continuous_const
  have hsub : Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) ⊆ {y : ℝ × ℝ | F y = 0} := fun y hy =>
    sub_eq_zero.mpr (hpos y.1 y.2 hy.1 hy.2)
  have hc := hcl.closure_subset_iff.mpr hsub
  rw [closure_prod_eq, closure_Ioi] at hc
  exact sub_eq_zero.mp (hc (Set.mk_mem_prod (Set.mem_Ici.mpr hP) (Set.mem_Ici.mpr hQ)))

/-! ## Positive semidefiniteness -/

theorem dot_self_nonneg' {d : ℕ} (y : Fin d → ℝ) : 0 ≤ dot y y :=
  Finset.sum_nonneg fun l _ => mul_self_nonneg (y l)

/-- `Kissing8.psd_step`, with the splitting needed only for `P, Q ≥ 0`. -/
theorem psd_step' {d K : ℕ} (Z : ℝ → ℝ → ℝ → ℝ) (Zq : ℕ → ℝ → ℝ → ℝ → ℝ) (cf : ℕ → ℝ)
    (B : ℕ → ℝ → ℝ → ℝ) (hc : ∀ m, 0 ≤ cf m) (hp : ∀ m ∈ range (K + 1), PSD d (Zq m))
    (hid : ∀ a a' w P Q, 0 ≤ P → 0 ≤ Q → Z (a * a' + w) (a * a + P) (a' * a' + Q) =
      ∑ m ∈ range (K + 1), cf m * B m a (a * a + P) * B m a' (a' * a' + Q) * Zq m w P Q) :
    PSD (d + 1) Z := by
  intro n y c
  set t : Fin n → Fin d → ℝ := fun i => Fin.tail (y i)
  set W : ℕ → Fin n → ℝ := fun m i => c i * B m (y i 0) (dot (y i) (y i))
  have key : ∀ i j, c i * c j * Z (dot (y i) (y j)) (dot (y i) (y i)) (dot (y j) (y j)) =
      ∑ m ∈ range (K + 1), cf m * (W m i * W m j * Zq m (dot (t i) (t j)) (dot (t i) (t i)) (dot (t j) (t j))) := by
    intro i j
    have hi : dot (y i) (y i) = y i 0 * y i 0 + dot (t i) (t i) := dot_succ _ _
    have hj : dot (y j) (y j) = y j 0 * y j 0 + dot (t j) (t j) := dot_succ _ _
    have hij : dot (y i) (y j) = y i 0 * y j 0 + dot (t i) (t j) := dot_succ _ _
    simp only [W]
    rw [hij, hi, hj, hid _ _ _ _ _ (dot_self_nonneg' _) (dot_self_nonneg' _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hswap : ∀ F : ℕ → Fin n → Fin n → ℝ,
      ∑ i, ∑ j, ∑ m ∈ range (K + 1), F m i j = ∑ m ∈ range (K + 1), ∑ i, ∑ j, F m i j := by
    intro F
    calc ∑ i, ∑ j, ∑ m ∈ range (K + 1), F m i j = ∑ i, ∑ m ∈ range (K + 1), ∑ j, F m i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ m ∈ range (K + 1), ∑ i, ∑ j, F m i j := Finset.sum_comm
  simp_rw [key]
  rw [hswap]
  refine Finset.sum_nonneg fun m hm => ?_
  simp_rw [← Finset.mul_sum]
  exact mul_nonneg (hc m) (hp m hm n t (W m))

theorem getD_nonneg : ∀ (N : List ℤ) (m : ℕ), (∀ n ∈ N, 0 ≤ n) → 0 ≤ N.getD m 0
  | [], _, _ => by simp
  | n :: N, 0, h => by simpa using h n (by simp)
  | n :: N, m + 1, h => by simpa using getD_nonneg N m fun x hx => h x (by simp [hx])

/-- A passing check gives `PSD (d + 1) (Zg (d + 1) k)` from the positivity of the kernels of `ℝ^d`. -/
theorem psd_of_chk {d k : ℕ} {L : ℤ} {N : List ℤ} {w D : ℕ} (h : chkId (d + 1) k L N w D = true)
    (hp : ∀ m ∈ range (k + 1), PSD d (Zp (d + 1) m)) : PSD (d + 1) (Zg (d + 1) k) := by
  have hLN : 0 < L ∧ ∀ n ∈ N, 0 ≤ n := by
    simp only [chkId, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2⟩
  refine psd_step' (Zg (d + 1) k) (Zp (d + 1)) (fun m => (N.getD m 0 : ℝ) / L)
    (fun m a r => Zg (d + 1 + 2 * m) (k - m) a r 1) (fun m => ?_) hp (fun a a' x P Q hP hQ => add_of_chk h a a' x P Q hP hQ)
  exact div_nonneg (by exact_mod_cast getD_nonneg N m hLN.2) (by exact_mod_cast hLN.1.le)

end Kissing5.G4
