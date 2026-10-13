import cas_spec
import GW_poly
import Mathlib.Tactic.LinearCombination

open Polynomial

namespace Pfq54.CF

open ZetasIrr.GW

/-! ### The data tables agree with the certificate lists -/

def posOf (l : List ℤ) : List ℕ := l.map Int.toNat

def negOf (l : List ℤ) : List ℕ := l.map fun a => (-a).toNat

theorem blockData_spec : ∀ b < 12,
    (blockData b).p00 = posOf ((cert b).N 0 0) ∧ (blockData b).n00 = negOf ((cert b).N 0 0) ∧
    (blockData b).p01 = posOf ((cert b).N 0 1) ∧ (blockData b).n01 = negOf ((cert b).N 0 1) ∧
    (blockData b).p02 = posOf ((cert b).N 0 2) ∧ (blockData b).n02 = negOf ((cert b).N 0 2) ∧
    (blockData b).p10 = posOf ((cert b).N 1 0) ∧ (blockData b).n10 = negOf ((cert b).N 1 0) ∧
    (blockData b).p11 = posOf ((cert b).N 1 1) ∧ (blockData b).n11 = negOf ((cert b).N 1 1) ∧
    (blockData b).p12 = posOf ((cert b).N 1 2) ∧ (blockData b).n12 = negOf ((cert b).N 1 2) ∧
    (blockData b).p20 = posOf ((cert b).N 2 0) ∧ (blockData b).n20 = negOf ((cert b).N 2 0) ∧
    (blockData b).p21 = posOf ((cert b).N 2 1) ∧ (blockData b).n21 = negOf ((cert b).N 2 1) ∧
    (blockData b).p22 = posOf ((cert b).N 2 2) ∧ (blockData b).n22 = negOf ((cert b).N 2 2) := by
  decide +kernel

theorem entry_eq (l : List ℤ) (n : ℕ) : entry (posOf l) (negOf l) n = peval l n := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [entry, posOf, negOf, List.map_cons, pevalNat, List.foldr_cons, Nat.add_eq,
      Nat.mul_eq, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, peval] at ih ⊢
    have h := Int.toNat_sub_toNat_neg a
    linear_combination h + (n : ℤ) * ih

def blockNZ (b : ℕ) (n : ℤ) : M3 :=
  ⟨⟨peval ((cert b).N 0 0) n, peval ((cert b).N 0 1) n, peval ((cert b).N 0 2) n⟩,
   ⟨peval ((cert b).N 1 0) n, peval ((cert b).N 1 1) n, peval ((cert b).N 1 2) n⟩,
   ⟨peval ((cert b).N 2 0) n, peval ((cert b).N 2 1) n, peval ((cert b).N 2 2) n⟩⟩

theorem blockN_eq (b : ℕ) (hb : b < 12) (n : ℕ) : blockN b n = blockNZ b n := by
  obtain ⟨h00, g00, h01, g01, h02, g02, h10, g10, h11, g11, h12, g12, h20, g20, h21, g21, h22,
    g22⟩ := blockData_spec b hb
  simp only [blockN, blockNZ, h00, g00, h01, g01, h02, g02, h10, g10, h11, g11, h12, g12, h20,
    g20, h21, g21, h22, g22, entry_eq]

def blocksZ (n : ℤ) : Blocks :=
  ⟨blockNZ 0 n, blockNZ 1 n, blockNZ 2 n, blockNZ 3 n, blockNZ 4 n, blockNZ 5 n, blockNZ 6 n,
    blockNZ 7 n, blockNZ 8 n, blockNZ 9 n, blockNZ 10 n, blockNZ 11 n⟩

theorem blocks_eq (n : ℕ) : blocks n = blocksZ n := by
  unfold blocks blocksZ
  rw [blockN_eq 0 (by norm_num), blockN_eq 1 (by norm_num), blockN_eq 2 (by norm_num),
    blockN_eq 3 (by norm_num), blockN_eq 4 (by norm_num), blockN_eq 5 (by norm_num),
    blockN_eq 6 (by norm_num), blockN_eq 7 (by norm_num), blockN_eq 8 (by norm_num),
    blockN_eq 9 (by norm_num), blockN_eq 10 (by norm_num), blockN_eq 11 (by norm_num)]

def hvZ (n : ℤ) : V3 := ⟨1, 10 * n + 1, (10 * n + 1) * (10 * n + 1)⟩

theorem hv_eq (n : ℕ) : hv n = hvZ n := rfl

def PvalZ (n : ℤ) : ℤ :=
  det3 (NTspec (blocksZ (n + 1)) (NTspec (blocksZ n) (hvZ n))) (NTspec (blocksZ (n + 1)) (hvZ (n + 1)))
    (hvZ (n + 2))

theorem PvalS_eq (n : ℕ) : PvalS n = PvalZ n := by
  simp only [PvalS, PvalZ, blocks_eq, hv_eq]
  push_cast
  rfl

/-! ### Degree bookkeeping -/

def PDV (v : ℤ → V3) (d : ℤ) : Prop :=
  PD (fun n => (v n).x0) d ∧ PD (fun n => (v n).x1) (d + 1) ∧ PD (fun n => (v n).x2) (d + 2)

def PDM (M : ℤ → M3) (d : ℤ) : Prop :=
  PDV (fun n => (M n).r0) d ∧ PDV (fun n => (M n).r1) (d - 1) ∧ PDV (fun n => (M n).r2) (d - 2)

theorem _root_.ZetasIrr.GW.PD.shift {f : ℤ → ℤ} {d : ℤ} (hf : PD f d) (c : ℤ) : PD (fun n => f (n + c)) d := by
  obtain ⟨p, hp, hpe⟩ := hf
  refine ⟨p.comp (X + C c), ?_, fun n => by show f (n + c) = _; rw [hpe, eval_comp, eval_add, eval_X, eval_C]⟩
  rcases hp with rfl | hp
  · left
    exact zero_comp
  · right
    refine le_trans ?_ hp
    exact_mod_cast natDegree_comp_le.trans (by rw [natDegree_X_add_C, mul_one])

theorem PDV.shift {v : ℤ → V3} {d : ℤ} (hv : PDV v d) (c : ℤ) : PDV (fun n => v (n + c)) d :=
  ⟨PD.shift hv.1 c, PD.shift hv.2.1 c, PD.shift hv.2.2 c⟩

theorem PDM.shift {M : ℤ → M3} {d : ℤ} (hM : PDM M d) (c : ℤ) : PDM (fun n => M (n + c)) d :=
  ⟨PDV.shift hM.1 c, PDV.shift hM.2.1 c, PDV.shift hM.2.2 c⟩

theorem PDV.tmulVec {M : ℤ → M3} {v : ℤ → V3} {a b : ℤ} (hM : PDM M a) (hv : PDV v b) :
    PDV (fun n => (M n).tmulVec (v n)) (a + b) := by
  obtain ⟨⟨m00, m01, m02⟩, ⟨m10, m11, m12⟩, ⟨m20, m21, m22⟩⟩ := hM
  obtain ⟨v0, v1, v2⟩ := hv
  simp only [PDV, M3.tmulVec]
  refine ⟨?_, ?_, ?_⟩
  · exact ((m00.mul' v0 (by omega)).add (m10.mul' v1 (by omega))).add (m20.mul' v2 (by omega))
  · exact ((m01.mul' v0 (by omega)).add (m11.mul' v1 (by omega))).add (m21.mul' v2 (by omega))
  · exact ((m02.mul' v0 (by omega)).add (m12.mul' v1 (by omega))).add (m22.mul' v2 (by omega))

theorem PDM.block (b : ℕ) (hb : b < 12) : PDM (fun n => blockNZ b n) ((cert b).deg : ℤ) := by
  simp only [PDM, PDV, blockNZ]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact (PD.certN hb 0 0 (by norm_num)).mono (by push_cast; omega)
  · exact (PD.certN hb 0 1 (by norm_num)).mono (by push_cast; omega)
  · exact (PD.certN hb 0 2 (by norm_num)).mono (by push_cast; omega)
  · exact (PD.certN hb 1 0 (by norm_num)).mono (by push_cast; omega)
  · exact (PD.certN hb 1 1 (by norm_num)).mono (by push_cast; omega)
  · exact (PD.certN hb 1 2 (by norm_num)).mono (by push_cast; omega)
  · exact (PD.certN hb 2 0 (by norm_num)).mono (by push_cast; omega)
  · exact (PD.certN hb 2 1 (by norm_num)).mono (by push_cast; omega)
  · exact (PD.certN hb 2 2 (by norm_num)).mono (by push_cast; omega)

theorem deg_sum : ((cert 0).deg : ℤ) + (cert 1).deg + (cert 2).deg + (cert 3).deg + (cert 4).deg +
    (cert 5).deg + (cert 6).deg + (cert 7).deg + (cert 8).deg + (cert 9).deg + (cert 10).deg +
    (cert 11).deg = 169 := by
  decide

theorem PDV.NT {v : ℤ → V3} {d : ℤ} (hv : PDV v d) (c : ℤ) :
    PDV (fun n => NTspec (blocksZ (n + c)) (v n)) (169 + d) := by
  have h0 := PDV.tmulVec ((PDM.block 0 (by norm_num)).shift c) hv
  have h1 := PDV.tmulVec ((PDM.block 1 (by norm_num)).shift c) h0
  have h2 := PDV.tmulVec ((PDM.block 2 (by norm_num)).shift c) h1
  have h3 := PDV.tmulVec ((PDM.block 3 (by norm_num)).shift c) h2
  have h4 := PDV.tmulVec ((PDM.block 4 (by norm_num)).shift c) h3
  have h5 := PDV.tmulVec ((PDM.block 5 (by norm_num)).shift c) h4
  have h6 := PDV.tmulVec ((PDM.block 6 (by norm_num)).shift c) h5
  have h7 := PDV.tmulVec ((PDM.block 7 (by norm_num)).shift c) h6
  have h8 := PDV.tmulVec ((PDM.block 8 (by norm_num)).shift c) h7
  have h9 := PDV.tmulVec ((PDM.block 9 (by norm_num)).shift c) h8
  have h10 := PDV.tmulVec ((PDM.block 10 (by norm_num)).shift c) h9
  have h11 := PDV.tmulVec ((PDM.block 11 (by norm_num)).shift c) h10
  have hs := deg_sum
  simp only [NTspec, blocksZ]
  refine ⟨h11.1.mono (by omega), h11.2.1.mono (by omega), h11.2.2.mono (by omega)⟩

theorem PDV_hvZ : PDV hvZ 0 := by
  simp only [PDV, hvZ]
  exact ⟨PD.const 1 le_rfl, (PD.lin 10 1).mono (by norm_num),
    ((PD.lin 10 1).mul (PD.lin 10 1)).mono (by norm_num)⟩

theorem PD.det3 {a b c : ℤ → V3} {x y z : ℤ} (ha : PDV a x) (hb : PDV b y) (hc : PDV c z) :
    PD (fun n => det3 (a n) (b n) (c n)) (x + y + z + 3) := by
  obtain ⟨a0, a1, a2⟩ := ha
  obtain ⟨b0, b1, b2⟩ := hb
  obtain ⟨c0, c1, c2⟩ := hc
  simp only [CF.det3]
  exact ((a0.mul' ((b1.mul' c2 (d := y + z + 3) (by omega)).sub (b2.mul' c1 (by omega)))
      (by omega)).sub
    (a1.mul' ((b0.mul' c2 (d := y + z + 2) (by omega)).sub (b2.mul' c0 (by omega))) (by omega))).add
    (a2.mul' ((b0.mul' c1 (d := y + z + 1) (by omega)).sub (b1.mul' c0 (by omega))) (by omega))

theorem PD_PvalZ : PD PvalZ 510 := by
  have h0 : PDV (fun n => hvZ (n + 0)) 0 := PDV_hvZ.shift 0
  have h1 := PDV.NT h0 0
  have h2 := PDV.NT h1 1
  have h3 := PDV.NT (PDV_hvZ.shift 1) 1
  have h4 := PDV_hvZ.shift 2
  have h := PD.det3 h2 h3 h4
  simp only [add_zero] at h
  exact h.mono (by norm_num)

/-! ### The factored side -/

def linProdZ (L : List LF) (n : ℤ) : ℤ :=
  L.foldr (fun t acc => ((t.a : ℤ) * n + t.b) ^ t.m * acc) 1

def GcoZ : List ℤ := Gco.map Nat.cast

def PfacZ (n : ℤ) : ℤ := content * linProdZ linFac n * peval GcoZ n

theorem linProdN_cast (L : List LF) (n : ℕ) : ((linProdN L n : ℕ) : ℤ) = linProdZ L n := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    simp only [linProdN, linProdZ, List.foldr_cons] at ih ⊢
    push_cast
    rw [ih]

theorem pevalNat_cast (l : List ℕ) (n : ℕ) :
    ((pevalNat l n : ℕ) : ℤ) = peval (l.map Nat.cast) n := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [pevalNat, List.foldr_cons, Nat.add_eq, Nat.mul_eq, List.map_cons, peval] at ih ⊢
    push_cast
    rw [ih]

theorem PfacN_cast (n : ℕ) : ((PfacN n : ℕ) : ℤ) = PfacZ n := by
  rw [PfacN, PfacZ, Nat.cast_mul, Nat.cast_mul, linProdN_cast, pevalNat_cast]
  rfl

theorem _root_.ZetasIrr.GW.PD.pow {f : ℤ → ℤ} {d : ℤ} (hf : PD f d) (m : ℕ) : PD (fun n => f n ^ m) (d * m) := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, mul_zero]
    exact PD.const 1 le_rfl
  | succ m ih =>
    simp only [pow_succ]
    exact (ih.mul hf).mono (le_of_eq (by push_cast; ring))

theorem PD.linProd (L : List LF) : PD (fun n => linProdZ L n) (((L.map LF.m).sum : ℕ) : ℤ) := by
  induction L with
  | nil =>
    simp only [linProdZ, List.foldr_nil, List.map_nil, List.sum_nil, Nat.cast_zero]
    exact PD.const 1 le_rfl
  | cons t L ih =>
    simp only [linProdZ, List.foldr_cons, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
    exact (PD.pow (PD.lin t.a t.b) t.m).mul' ih (by rw [one_mul])

theorem linFac_sum : (linFac.map LF.m).sum = 409 := by decide +kernel

theorem GcoZ_length : GcoZ.length = 102 := by decide

theorem PD_PfacZ : PD PfacZ 510 := by
  have h1 := PD.linProd linFac
  rw [linFac_sum] at h1
  have h2 := PD.pev GcoZ
  rw [GcoZ_length] at h2
  exact ((PD.const (content : ℤ) le_rfl).mul' h1 (d := 409) (by norm_num)).mul' h2 (by norm_num)

theorem content_pos : 0 < content := by decide

theorem linFac_b_pos : ∀ t ∈ linFac, 0 < t.b := by decide +kernel

theorem Gco_pos : ∀ c ∈ Gco, 0 < c := by decide

theorem linProdN_pos (L : List LF) (hL : ∀ t ∈ L, 0 < t.b) (n : ℕ) : 0 < linProdN L n := by
  induction L with
  | nil => exact Nat.one_pos
  | cons t L ih =>
    have ht : 0 < t.b := hL t List.mem_cons_self
    have h2 := ih fun s hs => hL s (List.mem_cons_of_mem t hs)
    show 0 < (t.a * n + t.b) ^ t.m * _
    exact Nat.mul_pos (pow_pos (by omega) _) h2

theorem pevalNat_pos (l : List ℕ) (hl : ∀ a ∈ l, 0 < a) (hne : l ≠ []) (n : ℕ) :
    0 < pevalNat l n := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a l =>
    have ha : 0 < a := hl a List.mem_cons_self
    exact Nat.lt_of_lt_of_le ha (Nat.le_add_right _ _)

theorem PfacN_pos (n : ℕ) : 0 < PfacN n :=
  Nat.mul_pos (Nat.mul_pos content_pos (linProdN_pos _ linFac_b_pos n))
    (pevalNat_pos _ Gco_pos (by decide) n)

/-! ### From 511 points to all `n` -/

theorem PD.eq_zero' {f : ℤ → ℤ} (hf : PD f 510) (h : ∀ k : Fin 511, f k = 0) (n : ℤ) :
    f n = 0 := by
  obtain ⟨p, hp, hpe⟩ := hf
  rcases hp with rfl | hp
  · rw [hpe, eval_zero]
  rw [hpe, eq_zero_of_natDegree_lt_card_of_eval_eq_zero p (f := fun k : Fin 511 => (k : ℤ))
    (fun a b hab => Fin.ext (by simpa using hab)) (fun k => by rw [← hpe]; exact h k)
    (by rw [Fintype.card_fin]; omega), eval_zero]

theorem PD.eq_of' {f g : ℤ → ℤ} {d : ℤ} (hf : PD f d) (hg : PD g d) (hd : d ≤ 510)
    (h : ∀ k : Fin 511, f k = g k) (n : ℤ) : f n = g n :=
  sub_eq_zero.mp (PD.eq_zero' ((hf.sub hg).mono hd) (fun k => sub_eq_zero.mpr (h k)) n)

end Pfq54.CF
