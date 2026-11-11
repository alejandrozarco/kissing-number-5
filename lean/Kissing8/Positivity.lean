import Kissing8.Addition8

/-!
# Positive semidefiniteness of the Gegenbauer kernels of `ℝ⁸`, degrees `k ≤ 6`

Induction on the dimension: `psd_Zc` on `ℝ²`, then `psd_step` with the generated identities `add3_k`, …,
`add8_k` (`Kissing8.Addition3` … `Kissing8.Addition8`) gives `PSD d (Zg d k)` for `d = 3, …, 8` and `k ≤ 6`.
Each case is one application of `psd_step`; the coefficients are nonnegative by `cA{d}_nonneg`.
-/

namespace Kissing8

open Finset

theorem psd3 (k : ℕ) (hk : k ≤ 6) : PSD 3 (Zg 3 k) := by
  interval_cases k
  · exact psd_step (d := 2) (K := 0) (Zg 3 0) Zc (cA3 0)
      (fun m a r => Zg (3 + 2 * m) (0 - m) a r 1) (cA3_nonneg 0) (fun m _ => psd_Zc m) (add3_0)
  · exact psd_step (d := 2) (K := 1) (Zg 3 1) Zc (cA3 1)
      (fun m a r => Zg (3 + 2 * m) (1 - m) a r 1) (cA3_nonneg 1) (fun m _ => psd_Zc m) (add3_1)
  · exact psd_step (d := 2) (K := 2) (Zg 3 2) Zc (cA3 2)
      (fun m a r => Zg (3 + 2 * m) (2 - m) a r 1) (cA3_nonneg 2) (fun m _ => psd_Zc m) (add3_2)
  · exact psd_step (d := 2) (K := 3) (Zg 3 3) Zc (cA3 3)
      (fun m a r => Zg (3 + 2 * m) (3 - m) a r 1) (cA3_nonneg 3) (fun m _ => psd_Zc m) (add3_3)
  · exact psd_step (d := 2) (K := 4) (Zg 3 4) Zc (cA3 4)
      (fun m a r => Zg (3 + 2 * m) (4 - m) a r 1) (cA3_nonneg 4) (fun m _ => psd_Zc m) (add3_4)
  · exact psd_step (d := 2) (K := 5) (Zg 3 5) Zc (cA3 5)
      (fun m a r => Zg (3 + 2 * m) (5 - m) a r 1) (cA3_nonneg 5) (fun m _ => psd_Zc m) (add3_5)
  · exact psd_step (d := 2) (K := 6) (Zg 3 6) Zc (cA3 6)
      (fun m a r => Zg (3 + 2 * m) (6 - m) a r 1) (cA3_nonneg 6) (fun m _ => psd_Zc m) (add3_6)

theorem psd4 (k : ℕ) (hk : k ≤ 6) : PSD 4 (Zg 4 k) := by
  interval_cases k
  · exact psd_step (d := 3) (K := 0) (Zg 4 0) (Zg 3) (cA4 0)
      (fun m a r => Zg (4 + 2 * m) (0 - m) a r 1) (cA4_nonneg 0) (fun m hm => psd3 m (by rw [Finset.mem_range] at hm; omega)) (add4_0)
  · exact psd_step (d := 3) (K := 1) (Zg 4 1) (Zg 3) (cA4 1)
      (fun m a r => Zg (4 + 2 * m) (1 - m) a r 1) (cA4_nonneg 1) (fun m hm => psd3 m (by rw [Finset.mem_range] at hm; omega)) (add4_1)
  · exact psd_step (d := 3) (K := 2) (Zg 4 2) (Zg 3) (cA4 2)
      (fun m a r => Zg (4 + 2 * m) (2 - m) a r 1) (cA4_nonneg 2) (fun m hm => psd3 m (by rw [Finset.mem_range] at hm; omega)) (add4_2)
  · exact psd_step (d := 3) (K := 3) (Zg 4 3) (Zg 3) (cA4 3)
      (fun m a r => Zg (4 + 2 * m) (3 - m) a r 1) (cA4_nonneg 3) (fun m hm => psd3 m (by rw [Finset.mem_range] at hm; omega)) (add4_3)
  · exact psd_step (d := 3) (K := 4) (Zg 4 4) (Zg 3) (cA4 4)
      (fun m a r => Zg (4 + 2 * m) (4 - m) a r 1) (cA4_nonneg 4) (fun m hm => psd3 m (by rw [Finset.mem_range] at hm; omega)) (add4_4)
  · exact psd_step (d := 3) (K := 5) (Zg 4 5) (Zg 3) (cA4 5)
      (fun m a r => Zg (4 + 2 * m) (5 - m) a r 1) (cA4_nonneg 5) (fun m hm => psd3 m (by rw [Finset.mem_range] at hm; omega)) (add4_5)
  · exact psd_step (d := 3) (K := 6) (Zg 4 6) (Zg 3) (cA4 6)
      (fun m a r => Zg (4 + 2 * m) (6 - m) a r 1) (cA4_nonneg 6) (fun m hm => psd3 m (by rw [Finset.mem_range] at hm; omega)) (add4_6)

theorem psd5 (k : ℕ) (hk : k ≤ 6) : PSD 5 (Zg 5 k) := by
  interval_cases k
  · exact psd_step (d := 4) (K := 0) (Zg 5 0) (Zg 4) (cA5 0)
      (fun m a r => Zg (5 + 2 * m) (0 - m) a r 1) (cA5_nonneg 0) (fun m hm => psd4 m (by rw [Finset.mem_range] at hm; omega)) (add5_0)
  · exact psd_step (d := 4) (K := 1) (Zg 5 1) (Zg 4) (cA5 1)
      (fun m a r => Zg (5 + 2 * m) (1 - m) a r 1) (cA5_nonneg 1) (fun m hm => psd4 m (by rw [Finset.mem_range] at hm; omega)) (add5_1)
  · exact psd_step (d := 4) (K := 2) (Zg 5 2) (Zg 4) (cA5 2)
      (fun m a r => Zg (5 + 2 * m) (2 - m) a r 1) (cA5_nonneg 2) (fun m hm => psd4 m (by rw [Finset.mem_range] at hm; omega)) (add5_2)
  · exact psd_step (d := 4) (K := 3) (Zg 5 3) (Zg 4) (cA5 3)
      (fun m a r => Zg (5 + 2 * m) (3 - m) a r 1) (cA5_nonneg 3) (fun m hm => psd4 m (by rw [Finset.mem_range] at hm; omega)) (add5_3)
  · exact psd_step (d := 4) (K := 4) (Zg 5 4) (Zg 4) (cA5 4)
      (fun m a r => Zg (5 + 2 * m) (4 - m) a r 1) (cA5_nonneg 4) (fun m hm => psd4 m (by rw [Finset.mem_range] at hm; omega)) (add5_4)
  · exact psd_step (d := 4) (K := 5) (Zg 5 5) (Zg 4) (cA5 5)
      (fun m a r => Zg (5 + 2 * m) (5 - m) a r 1) (cA5_nonneg 5) (fun m hm => psd4 m (by rw [Finset.mem_range] at hm; omega)) (add5_5)
  · exact psd_step (d := 4) (K := 6) (Zg 5 6) (Zg 4) (cA5 6)
      (fun m a r => Zg (5 + 2 * m) (6 - m) a r 1) (cA5_nonneg 6) (fun m hm => psd4 m (by rw [Finset.mem_range] at hm; omega)) (add5_6)

theorem psd6 (k : ℕ) (hk : k ≤ 6) : PSD 6 (Zg 6 k) := by
  interval_cases k
  · exact psd_step (d := 5) (K := 0) (Zg 6 0) (Zg 5) (cA6 0)
      (fun m a r => Zg (6 + 2 * m) (0 - m) a r 1) (cA6_nonneg 0) (fun m hm => psd5 m (by rw [Finset.mem_range] at hm; omega)) (add6_0)
  · exact psd_step (d := 5) (K := 1) (Zg 6 1) (Zg 5) (cA6 1)
      (fun m a r => Zg (6 + 2 * m) (1 - m) a r 1) (cA6_nonneg 1) (fun m hm => psd5 m (by rw [Finset.mem_range] at hm; omega)) (add6_1)
  · exact psd_step (d := 5) (K := 2) (Zg 6 2) (Zg 5) (cA6 2)
      (fun m a r => Zg (6 + 2 * m) (2 - m) a r 1) (cA6_nonneg 2) (fun m hm => psd5 m (by rw [Finset.mem_range] at hm; omega)) (add6_2)
  · exact psd_step (d := 5) (K := 3) (Zg 6 3) (Zg 5) (cA6 3)
      (fun m a r => Zg (6 + 2 * m) (3 - m) a r 1) (cA6_nonneg 3) (fun m hm => psd5 m (by rw [Finset.mem_range] at hm; omega)) (add6_3)
  · exact psd_step (d := 5) (K := 4) (Zg 6 4) (Zg 5) (cA6 4)
      (fun m a r => Zg (6 + 2 * m) (4 - m) a r 1) (cA6_nonneg 4) (fun m hm => psd5 m (by rw [Finset.mem_range] at hm; omega)) (add6_4)
  · exact psd_step (d := 5) (K := 5) (Zg 6 5) (Zg 5) (cA6 5)
      (fun m a r => Zg (6 + 2 * m) (5 - m) a r 1) (cA6_nonneg 5) (fun m hm => psd5 m (by rw [Finset.mem_range] at hm; omega)) (add6_5)
  · exact psd_step (d := 5) (K := 6) (Zg 6 6) (Zg 5) (cA6 6)
      (fun m a r => Zg (6 + 2 * m) (6 - m) a r 1) (cA6_nonneg 6) (fun m hm => psd5 m (by rw [Finset.mem_range] at hm; omega)) (add6_6)

theorem psd7 (k : ℕ) (hk : k ≤ 6) : PSD 7 (Zg 7 k) := by
  interval_cases k
  · exact psd_step (d := 6) (K := 0) (Zg 7 0) (Zg 6) (cA7 0)
      (fun m a r => Zg (7 + 2 * m) (0 - m) a r 1) (cA7_nonneg 0) (fun m hm => psd6 m (by rw [Finset.mem_range] at hm; omega)) (add7_0)
  · exact psd_step (d := 6) (K := 1) (Zg 7 1) (Zg 6) (cA7 1)
      (fun m a r => Zg (7 + 2 * m) (1 - m) a r 1) (cA7_nonneg 1) (fun m hm => psd6 m (by rw [Finset.mem_range] at hm; omega)) (add7_1)
  · exact psd_step (d := 6) (K := 2) (Zg 7 2) (Zg 6) (cA7 2)
      (fun m a r => Zg (7 + 2 * m) (2 - m) a r 1) (cA7_nonneg 2) (fun m hm => psd6 m (by rw [Finset.mem_range] at hm; omega)) (add7_2)
  · exact psd_step (d := 6) (K := 3) (Zg 7 3) (Zg 6) (cA7 3)
      (fun m a r => Zg (7 + 2 * m) (3 - m) a r 1) (cA7_nonneg 3) (fun m hm => psd6 m (by rw [Finset.mem_range] at hm; omega)) (add7_3)
  · exact psd_step (d := 6) (K := 4) (Zg 7 4) (Zg 6) (cA7 4)
      (fun m a r => Zg (7 + 2 * m) (4 - m) a r 1) (cA7_nonneg 4) (fun m hm => psd6 m (by rw [Finset.mem_range] at hm; omega)) (add7_4)
  · exact psd_step (d := 6) (K := 5) (Zg 7 5) (Zg 6) (cA7 5)
      (fun m a r => Zg (7 + 2 * m) (5 - m) a r 1) (cA7_nonneg 5) (fun m hm => psd6 m (by rw [Finset.mem_range] at hm; omega)) (add7_5)
  · exact psd_step (d := 6) (K := 6) (Zg 7 6) (Zg 6) (cA7 6)
      (fun m a r => Zg (7 + 2 * m) (6 - m) a r 1) (cA7_nonneg 6) (fun m hm => psd6 m (by rw [Finset.mem_range] at hm; omega)) (add7_6)

theorem psd8 (k : ℕ) (hk : k ≤ 6) : PSD 8 (Zg 8 k) := by
  interval_cases k
  · exact psd_step (d := 7) (K := 0) (Zg 8 0) (Zg 7) (cA8 0)
      (fun m a r => Zg (8 + 2 * m) (0 - m) a r 1) (cA8_nonneg 0) (fun m hm => psd7 m (by rw [Finset.mem_range] at hm; omega)) (add8_0)
  · exact psd_step (d := 7) (K := 1) (Zg 8 1) (Zg 7) (cA8 1)
      (fun m a r => Zg (8 + 2 * m) (1 - m) a r 1) (cA8_nonneg 1) (fun m hm => psd7 m (by rw [Finset.mem_range] at hm; omega)) (add8_1)
  · exact psd_step (d := 7) (K := 2) (Zg 8 2) (Zg 7) (cA8 2)
      (fun m a r => Zg (8 + 2 * m) (2 - m) a r 1) (cA8_nonneg 2) (fun m hm => psd7 m (by rw [Finset.mem_range] at hm; omega)) (add8_2)
  · exact psd_step (d := 7) (K := 3) (Zg 8 3) (Zg 7) (cA8 3)
      (fun m a r => Zg (8 + 2 * m) (3 - m) a r 1) (cA8_nonneg 3) (fun m hm => psd7 m (by rw [Finset.mem_range] at hm; omega)) (add8_3)
  · exact psd_step (d := 7) (K := 4) (Zg 8 4) (Zg 7) (cA8 4)
      (fun m a r => Zg (8 + 2 * m) (4 - m) a r 1) (cA8_nonneg 4) (fun m hm => psd7 m (by rw [Finset.mem_range] at hm; omega)) (add8_4)
  · exact psd_step (d := 7) (K := 5) (Zg 8 5) (Zg 7) (cA8 5)
      (fun m a r => Zg (8 + 2 * m) (5 - m) a r 1) (cA8_nonneg 5) (fun m hm => psd7 m (by rw [Finset.mem_range] at hm; omega)) (add8_5)
  · exact psd_step (d := 7) (K := 6) (Zg 8 6) (Zg 7) (cA8 6)
      (fun m a r => Zg (8 + 2 * m) (6 - m) a r 1) (cA8_nonneg 6) (fun m hm => psd7 m (by rw [Finset.mem_range] at hm; omega)) (add8_6)

end Kissing8
