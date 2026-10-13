import cas_fast

namespace Pfq54.CF

theorem forceI_eq {α : Type} (a : Int) (k : Int → α) : forceI a k = k a := by
  cases a with
  | ofNat n => cases n <;> rfl
  | negSucc n => cases n <;> rfl

theorem V3.force_eq {α : Type} (v : V3) (k : V3 → α) : v.force k = k v := by
  obtain ⟨x0, x1, x2⟩ := v
  simp only [V3.force, forceI_eq]

theorem M3.force_eq {α : Type} (A : M3) (k : M3 → α) : A.force k = k A := by
  obtain ⟨r0, r1, r2⟩ := A
  simp only [M3.force, V3.force_eq]

theorem M3.tmulVecF_eq {α : Type} (A : M3) (v : V3) (k : V3 → α) :
    A.tmulVecF v k = k (A.tmulVec v) :=
  V3.force_eq _ _

theorem blockF_eq {α : Type} (b n : Nat) (k : M3 → α) : blockF b n k = k (blockN b n) :=
  M3.force_eq _ _

theorem blocksF_eq {α : Type} (n : Nat) (k : Blocks → α) : blocksF n k = k (blocks n) := by
  simp only [blocksF, blockF_eq, blocks]

theorem NTB_eq {α : Type} (B : Blocks) (v : V3) (k : V3 → α) : NTB B v k = k (NTspec B v) := by
  simp only [NTB, V3.force_eq, M3.tmulVecF_eq, NTspec]

theorem NT2B_eq {α : Type} (B : Blocks) (v u : V3) (k : V3 → V3 → α) :
    NT2B B v u k = k (NTspec B v) (NTspec B u) := by
  simp only [NT2B, V3.force_eq, M3.tmulVecF_eq, NTspec]

theorem PvalB_eq (n : Nat) : PvalB n (blocks n) (blocks (n + 1)) = PvalS n := by
  simp only [PvalB, NTB_eq, NT2B_eq, V3.force_eq, PvalS]

theorem loop_spec : ∀ (k n : Nat), loop k n (blocks n) = true →
    ∀ m, m < k → PvalS (n + m) = Int.ofNat (PfacN (n + m))
  | 0, _, _, _, hm => absurd hm (Nat.not_lt_zero _)
  | k + 1, n, h, m, hm => by
    simp only [loop, blocksF_eq, Bool.and_eq_true, beq_iff_eq, PvalB_eq] at h
    cases m with
    | zero => exact h.1
    | succ m =>
      rw [show n + (m + 1) = n + 1 + m by omega]
      exact loop_spec k (n + 1) h.2 m (by omega)

theorem checkCas_spec (a len : Nat) (h : checkCas a len = true) (k : Nat) (h1 : a ≤ k)
    (h2 : k < a + len) : PvalS k = Int.ofNat (PfacN k) := by
  rw [checkCas, blocksF_eq] at h
  have := loop_spec len a h (k - a) (by omega)
  rwa [show a + (k - a) = k by omega] at this

end Pfq54.CF
