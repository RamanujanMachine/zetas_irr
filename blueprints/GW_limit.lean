/-
# The limit of the gauged transport blocks

With the gauge `H(N) = diag(1, N, N²)`, the gauged blocks `H(N) blk(block b N) H(N)⁻¹` converge to
the matrices `Lb b` of leading-coefficient ratios of the certificates, so
`H(N) blk(Wmat N) H(N+1)⁻¹ → Lq = ∏_b Lb b` (PDF Part VII §1: `H(n)B(n)H(n+1)⁻¹ = A + O(1/n)`;
here `blk (Wmat N) = -B(N)` and `Lq = -A`).
-/
import GW_bridge

open Matrix Filter Topology ZetasIrr.CMF

noncomputable section

namespace ZetasIrr.GW

def lastI (l : List ℤ) : ℤ := l.getLastD 0

def Lb (b : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.of fun i j => (lastI ((cert b).N i j) : ℚ) / lastI (cert b).D

def Lq : Matrix (Fin 3) (Fin 3) ℚ := ((List.range 12).map Lb).prod

theorem tendsto_peval (l : List ℤ) (hl : l ≠ []) :
    Tendsto (fun n : ℕ => (peval l n : ℝ) / (n : ℝ) ^ (l.length - 1)) atTop (𝓝 (lastI l : ℝ)) := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    rcases eq_or_ne l [] with rfl | hl'
    · simp [peval, lastI]
    have hlen : l.length ≠ 0 := fun h => hl' (List.length_eq_zero_iff.mp h)
    have hlast : lastI (a :: l) = lastI l := by
      cases l with
      | nil => exact absurd rfl hl'
      | cons c l' => rfl
    have h0 : Tendsto (fun n : ℕ => (a : ℝ) / (n : ℝ) ^ l.length) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop hlen |>.comp tendsto_natCast_atTop_atTop)
    rw [hlast, List.length_cons, Nat.add_sub_cancel, ← zero_add (lastI l : ℝ)]
    refine (h0.add (ih hl')).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hp : (n : ℝ) ^ l.length = n * n ^ (l.length - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hlen)]
    simp only [peval, List.foldr_cons]
    push_cast
    rw [hp]
    field_simp

theorem cert_facts : ∀ b < 12, lastI (cert b).D ≠ 0 := by decide

theorem certD_ne_nil (b : ℕ) : (cert b).D ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [Cert.D, dec_length] at this
  exact Nat.succ_ne_zero _ this

theorem certN_ne_nil (b : ℕ) (i j : ℕ) (hi : i ≤ 2) (hd : 2 ≤ (cert b).deg) : (cert b).N i j ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [Cert.N, dec_length] at this
  simp at this
  omega

def gauge (x : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => x ^ (i : ℕ) * M i j / x ^ (j : ℕ)

theorem gauge_mul {x : ℝ} (hx : x ≠ 0) (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    gauge x (A * B) = gauge x A * gauge x B := by
  ext i j
  simp only [gauge, Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp

theorem gauge_one (x : ℝ) (hx : x ≠ 0) : gauge x 1 = 1 := by
  ext i j
  simp only [gauge, Matrix.of_apply, Matrix.one_apply]
  split_ifs with h
  · subst h; field_simp
  · simp

theorem gauge_prod {x : ℝ} (hx : x ≠ 0) (l : List (Matrix (Fin 3) (Fin 3) ℝ)) :
    gauge x l.prod = (l.map (gauge x)).prod := by
  induction l with
  | nil => exact gauge_one x hx
  | cons A l ih => rw [List.prod_cons, gauge_mul hx, ih, List.map_cons, List.prod_cons]

theorem tendsto_block {b : ℕ} (hb : b < 12) :
    Tendsto (fun n : ℕ => gauge n ((blk (blockW b n)).map (Rat.cast : ℚ → ℝ))) atTop
      (𝓝 ((Lb b).map (Rat.cast : ℚ → ℝ))) := by
  have hdeg := cert_deg b hb
  have hD := tendsto_peval _ (certD_ne_nil b)
  have hD0 : (lastI (cert b).D : ℝ) ≠ 0 := by exact_mod_cast cert_facts b hb
  have hev : ∀ᶠ n : ℕ in atTop, peval (cert b).D n ≠ 0 ∧ 1 ≤ n := by
    have := hD.eventually (isOpen_ne.mem_nhds hD0)
    filter_upwards [this, eventually_ge_atTop 1] with n h1 h2
    refine ⟨fun h => h1 ?_, h2⟩
    rw [h]; simp
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hN := tendsto_peval _ (certN_ne_nil b i j (by omega) hdeg.1)
  simp only [Lb, Matrix.map_apply, Matrix.of_apply]
  push_cast
  refine (hN.div hD hD0).congr' ?_
  filter_upwards [hev] with n ⟨hn, hn1⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hDn : (peval (cert b).D n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hlN : ((cert b).N i j).length - 1 = (cert b).deg + j - i := by
    rw [Cert.N, dec_length]; omega
  have hlD : (cert b).D.length - 1 = (cert b).deg := by rw [Cert.D, dec_length]; rfl
  show (peval ((cert b).N i j) n : ℝ) / (n : ℝ) ^ (((cert b).N i j).length - 1) /
      ((peval (cert b).D n : ℝ) / (n : ℝ) ^ ((cert b).D.length - 1)) =
    (n : ℝ) ^ (i : ℕ) * ((blk (blockW b n) i j : ℚ) : ℝ) / (n : ℝ) ^ (j : ℕ)
  rw [blk_blockW n b hb i j hn, hlN, hlD, Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
  have e1 : (n : ℝ) ^ ((cert b).deg + (j : ℕ) - i) * n ^ (i : ℕ) =
      n ^ ((cert b).deg) * n ^ (j : ℕ) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  field_simp
  linear_combination -(peval ((cert b).N i j) n : ℝ) * e1

theorem map_cast_prod (l : List (Matrix (Fin 3) (Fin 3) ℚ)) :
    l.prod.map (Rat.cast : ℚ → ℝ) = (l.map fun M => M.map (Rat.cast : ℚ → ℝ)).prod := by
  induction l with
  | nil => ext i j; simp [Matrix.one_apply]; split_ifs <;> simp
  | cons A l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    ext i j
    simp [Matrix.mul_apply]

/-- **The gauged transport converges** (to `Lq = -A`). -/
theorem tendsto_gauged :
    Tendsto (fun N : ℕ => Matrix.of fun k j : Fin 3 =>
      (N : ℝ) ^ (k : ℕ) * (blk (Wmat N) k j : ℝ) / ((N : ℝ) + 1) ^ (j : ℕ)) atTop
      (𝓝 (Lq.map (Rat.cast : ℚ → ℝ))) := by
  have hprod : Tendsto (fun N : ℕ => gauge N ((blk (Wmat N)).map (Rat.cast : ℚ → ℝ))) atTop
      (𝓝 (Lq.map (Rat.cast : ℚ → ℝ))) := by
    have h := tendsto_list_prod (List.range 12) (fun b hb =>
      tendsto_block (b := b) (List.mem_range.mp hb))
    have hL : Lq.map (Rat.cast : ℚ → ℝ) =
        ((List.range 12).map fun b => (Lb b).map (Rat.cast : ℚ → ℝ)).prod := by
      rw [Lq, map_cast_prod, List.map_map]; rfl
    rw [hL]
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    rw [blk_Wmat, map_cast_prod, List.map_map, gauge_prod hN', List.map_map]
    rfl
  have hq : Tendsto (fun N : ℕ => (N : ℝ) / (N + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop 1
  refine tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun j => ?_
  have h2 := ((tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hprod k)) j).mul (hq.pow (j : ℕ))
  rw [one_pow, mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  simp only [gauge, Matrix.of_apply, Matrix.map_apply, div_pow]
  field_simp

end ZetasIrr.GW

end
