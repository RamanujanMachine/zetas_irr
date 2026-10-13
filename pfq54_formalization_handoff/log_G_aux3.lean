/-
# Auxiliary lemmas for `log_G_ge.lean`, part 3 (sorry-free)

The finite checks on the profile table (same list as `Pfq54.BP.profileRows`).
-/
import profile_aux

noncomputable section

namespace Pfq54.LG3

open Pfq54

/-- The profile table (same as `Pfq54.BP.profileRows`). -/
def rowsA : List (ℚ × ℚ × ℕ) :=
  [(1/15, 1/13, 1), (1/13, 1/12, 2), (1/12, 1/10, 3), (2/15, 2/13, 1), (2/13, 3/17, 2),
   (3/17, 2/11, 1), (2/11, 1/5, 2), (1/5, 4/15, 1), (4/15, 5/17, 3), (5/17, 3/10, 2),
   (1/3, 2/5, 2), (2/5, 4/9, 1), (5/11, 7/15, 1), (7/15, 9/19, 3), (9/19, 1/2, 2),
   (8/15, 6/11, 1), (6/11, 3/5, 2), (3/5, 2/3, 1), (2/3, 11/16, 3), (11/16, 9/13, 2),
   (9/13, 7/10, 3), (11/15, 14/19, 2), (14/19, 3/4, 1), (3/4, 4/5, 2), (4/5, 13/16, 1),
   (9/11, 16/19, 1), (13/15, 7/8, 2), (7/8, 15/17, 3), (15/17, 9/10, 2), (14/15, 17/18, 2),
   (17/18, 18/19, 1)]

/-- The exact check of the table on the subdivision. -/
theorem rowsA_tab :
    rowsA.all (fun r => PA.rowI (fun F => decide (PA.PhiF F = r.2.2)) r.1 r.2.1) = true := by
  decide +kernel

theorem rowsA_bd : ∀ r ∈ rowsA, 1 / 19 ≤ r.1 ∧ r.1 < r.2.1 ∧ r.2.1 ≤ 1 := by
  decide +kernel

/-- The rows are increasing and disjoint. -/
theorem rowsA_pw : rowsA.Pairwise fun r s => r.2.1 ≤ s.1 := by
  have hc : rowsA.IsChain fun r s => r.2.1 ≤ s.1 ∧ r.1 ≤ r.2.1 ∧ s.1 ≤ s.2.1 := by
    decide +kernel
  have : IsTrans (ℚ × ℚ × ℕ) fun r s => r.2.1 ≤ s.1 ∧ r.1 ≤ r.2.1 ∧ s.1 ≤ s.2.1 :=
    ⟨fun r s t h1 h2 => ⟨h1.1.trans (h2.2.1.trans h2.1), h1.2.1, h2.2.2⟩⟩
  exact (List.isChain_iff_pairwise.mp hc).imp fun h => h.1

/-- A checked table determines `φ` on all periods. -/
theorem table_of_check (rows : List (ℚ × ℚ × ℕ))
    (hc : rows.all (fun r => PA.rowI (fun F => decide (PA.PhiF F = r.2.2)) r.1 r.2.1) = true) :
    ∀ r ∈ rows, ∀ k : ℕ, ∀ x : ℚ, (k : ℚ) + r.1 < x → x < (k : ℚ) + r.2.1 → phi x = r.2.2 := by
  intro r hr k x h1 h2
  have ht : ∀ F G : ℤ → ℤ, (∀ d ∈ PA.dl, F d = G d) →
      decide (PA.PhiF F = r.2.2) = decide (PA.PhiF G = r.2.2) := fun F G h => by
    rw [PA.PhiF_congr F G h]
  have h := PA.rowI_sound _ ht r.1 r.2.1 (List.all_eq_true.mp hc r hr) (x - k) (by linarith)
    (by linarith)
  have e : phi x = phi (x - k) := by
    have := PA.phi_add_int (x - k) k
    rw [Int.cast_natCast, add_sub_cancel] at this
    exact this
  rw [e, PA.phi_eq_PhiF]
  exact of_decide_eq_true h

end Pfq54.LG3
