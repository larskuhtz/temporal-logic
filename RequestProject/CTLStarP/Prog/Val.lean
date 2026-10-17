module

public import RequestProject.CTLStarP.Prog.Tab

/-!
# Program fragments: the table of truth values of subformulas (second phase)

The second phase stores `val j u ℓ` (for `j, u, ℓ < n`) in memory bit `addr n j u ℓ`, above
the bits `< 2 n` used by the first phase.  Entries are computed for decreasing `j`, for
decreasing `u` and for increasing `ℓ`; every entry only depends on entries computed before.
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open HL PT

variable {w : Word} {B : ℕ} {ts : List Tok}

/-! ## Addresses -/

/-- Memory address of the entry `val j u ℓ`. -/
def addr (n a b c : ℕ) : ℕ := (n + n) + ((a * n + b) * n + c)

lemma addr_inj {n a b c a' b' c' : ℕ} (hb : b < n) (hc : c < n) (hb' : b' < n) (hc' : c' < n)
    (h : addr n a b c = addr n a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  unfold addr at h
  have h1 : (a * n + b) * n + c = (a' * n + b') * n + c' := by omega
  have hn : 0 < n := by omega
  have e1 : ((a * n + b) * n + c) % n = c := by
    rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hc]
  have e1' : ((a' * n + b') * n + c') % n = c' := by
    rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hc']
  have e2 : ((a * n + b) * n + c) / n = a * n + b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc, zero_add]
  have e2' : ((a' * n + b') * n + c') / n = a' * n + b' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc', zero_add]
  have hcc : c = c' := by rw [← e1, ← e1', h1]
  have hab : a * n + b = a' * n + b' := by rw [← e2, ← e2', h1]
  have f1 : (a * n + b) % n = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  have f1' : (a' * n + b') % n = b' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb']
  have f2 : (a * n + b) / n = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, zero_add]
  have f2' : (a' * n + b') / n = a' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb', zero_add]
  refine ⟨?_, ?_, hcc⟩
  · rw [← f2, ← f2', hab]
  · rw [← f1, ← f1', hab]

/-! ## Memory of the second phase -/

/-- Memory contents: the first-phase tables, and the entries `val a b c = true` for the
triples satisfying `D`. -/
def Mem2 (ts : List Tok) (D : ℕ → ℕ → ℕ → Prop) (x : ℕ) : Prop :=
  Mem1 ts 0 0 x ∨ ∃ a b c, a < ts.length ∧ b < ts.length ∧ c < ts.length ∧ D a b c ∧
    val ts a b c = true ∧ x = addr ts.length a b c

lemma val_ge {j : ℕ} (hj : ts.length ≤ j) (u ℓ : ℕ) : val ts j u ℓ = false := by
  rw [val, dif_pos hj]

lemma readV {mem : Finset ℕ} {D : ℕ → ℕ → ℕ → Prop} (hm : ∀ x, x ∈ mem ↔ Mem2 ts D x)
    (a b c : ℕ) (hc : c < ts.length) (hD : a < ts.length → b < ts.length → D a b c) :
    (decide (a < ts.length) && (decide (b < ts.length) &&
      decide (addr ts.length a b c ∈ mem))) = (decide (b < ts.length) && val ts a b c) := by
  by_cases ha : a < ts.length
  · by_cases hb : b < ts.length
    · have : addr ts.length a b c ∈ mem ↔ val ts a b c = true := by
        rw [hm]; unfold Mem2 Mem1
        constructor
        · rintro ((⟨h1, -⟩ | ⟨-, h1, -⟩) | ⟨a', b', c', -, hb', hc', -, hv, he⟩)
          · unfold addr at h1; omega
          · unfold addr at h1; omega
          · obtain ⟨rfl, rfl, rfl⟩ := addr_inj hb hc hb' hc' he; exact hv
        · intro hv; exact Or.inr ⟨a, b, c, ha, hb, hc, hD ha hb, hv, rfl⟩
      by_cases hv : val ts a b c = true
      · simp [ha, hb, this.2 hv, hv]
      · simp only [ha, hb, decide_true, Bool.true_and, Bool.not_eq_true] at hv ⊢
        simp only [hv, decide_eq_false_iff_not]; exact fun h' => by simp [this.1 h'] at hv
    · simp [hb]
  · simp [ha, val_ge (show ts.length ≤ a by omega)]

lemma val_lt {j : ℕ} (hj : j < ts.length) (u ℓ : ℕ) : val ts j u ℓ =
    if tc ts j = 5 then labHas ts (u + 2) (j + 1)
    else if tc ts j = 6 then true
    else if tc ts j = 7 then !val ts (j + 1) u ℓ
    else if tc ts j = 8 then val ts (j + 1) u ℓ && val ts (fend ts (j + 1)) u ℓ
    else if tc ts j = 9 then
      (if nxt ts ℓ u < ts.length then val ts (j + 1) (nxt ts ℓ u) ℓ else false)
    else if tc ts j = 10 then
      val ts (fend ts (j + 1)) u ℓ ||
        (val ts (j + 1) u ℓ &&
          (if u < nxt ts ℓ u ∧ nxt ts ℓ u < ts.length then val ts j (nxt ts ℓ u) ℓ else false))
    else if tc ts j = 11 then (List.range ts.length).any (fun ℓ' => val ts (j + 1) u ℓ')
    else false := by
  rw [val, dif_neg (by omega)]

lemma nxt_le {u : ℕ} (hu : u ≤ ts.length) (ℓ : ℕ) : nxt ts ℓ u ≤ ts.length + 1 := by
  unfold nxt
  split_ifs
  · omega
  · apply ctw_le_succ
    have := scan_le (ts := ts) upT downT (u + 1) 0; simp only [tend]; omega

/-! ## Reading the table -/

/-- The address expression. -/
def addrE (a b c : Ex M) : Ex M := (.var vN + .var vN) + ((a * .var vN + b) * .var vN + c)

/-- Guarded read of the table of truth values. -/
def rdV (a b c : Ex M) : Ex M :=
  Ex.band (Ex.lt a (.var vN)) (Ex.band (Ex.lt b (.var vN)) (Ex.mem (addrE a b c)))

lemma ev_rdV (σ : HSt M) (a b c : Ex M) :
    (rdV a b c).ev w σ = bv (decide (a.ev w σ < σ.v vN) && (decide (b.ev w σ < σ.v vN) &&
      decide (addr (σ.v vN) (a.ev w σ) (b.ev w σ) (c.ev w σ) ∈ σ.mem))) := by
  simp [rdV, addrE, addr]

lemma bnd_rdV (hc : Ctx ts w B) {σ : HSt M} (hN : σ.v vN = ts.length) {a b c : Ex M}
    (ha : a.Bnd w B σ) (hb : b.Bnd w B σ) (hcc : c.Bnd w B σ) (ha' : a.ev w σ ≤ ts.length + 1)
    (hb' : b.ev w σ ≤ ts.length + 1) (hc' : c.ev w σ ≤ ts.length + 1) :
    (rdV a b c).Bnd w B σ := by
  have hB := hc.bnd
  set n := ts.length
  have h1 : a.ev w σ * n ≤ (n + 1) * n := Nat.mul_le_mul_right _ ha'
  have h2 : (a.ev w σ * n + b.ev w σ) * n ≤ ((n + 1) * n + (n + 1)) * n :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : ((n + 1) * n + (n + 1)) * n + (n + 1) + (n + n) ≤ 16 * (n + 2) ^ 3 + 64 := by
    ring_nf; nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]
  have h4 : (n + 1) * n + (n + 1) ≤ ((n + 1) * n + (n + 1)) * n + (n + 1) + (n + n) + 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h]; simp
    · nlinarith
  unfold rdV addrE
  simp only [Ex.band, bnd_mul, bnd_lt, bnd_var, bnd_mem, bnd_add, ev_lt, ev_var, ev_mul, ev_add,
    ev_mem, hN, bv_mul_bv]
  repeat' apply And.intro
  all_goals first
    | assumption
    | exact le_trans (bv_le _) (by omega)
    | omega
    | linarith


lemma ev_rdV_val {σ : HSt M} {D : ℕ → ℕ → ℕ → Prop} (hm : ∀ x, x ∈ σ.mem ↔ Mem2 ts D x)
    (hN : σ.v vN = ts.length) {a b c : Ex M} (hc : c.ev w σ < ts.length)
    (hD : a.ev w σ < ts.length → b.ev w σ < ts.length → D (a.ev w σ) (b.ev w σ) (c.ev w σ)) :
    (rdV a b c).ev w σ = bv (decide (b.ev w σ < ts.length) && val ts (a.ev w σ) (b.ev w σ) (c.ev w σ)) := by
  rw [ev_rdV, hN, readV hm _ _ _ hc hD]

/-! ## Computing one entry -/

notation "vJ" => (31 : Fin 48)
notation "vU" => (32 : Fin 48)
notation "vL" => (33 : Fin 48)
notation "vB" => (34 : Fin 48)
notation "vT" => (35 : Fin 48)
notation "vEA" => (36 : Fin 48)
notation "vEL" => (37 : Fin 48)
notation "vR" => (38 : Fin 48)
notation "vA" => (39 : Fin 48)

/-- The entries computed before `(j, u, ℓ)`. -/
def Dn (j u ℓ : ℕ) (a b c : ℕ) : Prop := j < a ∨ (a = j ∧ (u < b ∨ (b = u ∧ c < ℓ)))

/-- Variables clobbered while computing an entry. -/
def clV : List (Fin 48) := cl 31 ++ [vB, vT, vEA, vEL]

/-- Assumptions when computing the entry `(j, u, ℓ)`. -/
structure VCtx (ts : List Tok) (w : Word) (B : ℕ) (σ : HSt M) (j u ℓ : ℕ) : Prop where
  hc : Ctx ts w B
  hN : σ.v vN = ts.length
  hJ : σ.v vJ = j
  hU : σ.v vU = u
  hL : σ.v vL = ℓ
  hj : j < ts.length
  hu : u < ts.length
  hl : ℓ < ts.length
  hm : ∀ x, x ∈ σ.mem ↔ Mem2 ts (Dn j u ℓ) x

/-- Postcondition of the computation of an entry. -/
def VPost (ts : List Tok) (σ : HSt M) (j u ℓ : ℕ) (σ' : HSt M) : Prop :=
  σ'.v vB = bv (val ts j u ℓ) ∧ Frame clV σ σ'

lemma VCtx.of_frame {σ σ' : HSt M} {j u ℓ : ℕ} (h : VCtx ts w B σ j u ℓ) (hf : Frame clV σ σ') :
    VCtx ts w B σ' j u ℓ where
  hc := h.hc
  hN := by rw [hf.1 _ (by decide), h.hN]
  hJ := by rw [hf.1 _ (by decide), h.hJ]
  hU := by rw [hf.1 _ (by decide), h.hU]
  hL := by rw [hf.1 _ (by decide), h.hL]
  hj := h.hj
  hu := h.hu
  hl := h.hl
  hm := by rw [hf.2.1]; exact h.hm

@[simp] lemma decide_pos_bv (b : Bool) : decide (0 < bv b) = b := by cases b <;> rfl

lemma rdV_le_one (σ : HSt M) (a b c : Ex M) : (rdV a b c).ev w σ ≤ 1 := by
  rw [ev_rdV]; exact bv_le _

def c5 : Hs M := .set vHP (.var vU + .const 2) ;; .set vHQ (.var vJ + .const 1) ;; labHasP ;;
  .set vB (.var vHR)
def c6 : Hs M := .set vB (.const 1)
def c7 : Hs M := .set vB (Ex.bnot (rdV (.var vJ + .const 1) (.var vU) (.var vL)))
def c8 : Hs M := fendP (.var vJ + .const 1) ;;
  .set vB (Ex.band (rdV (.var vJ + .const 1) (.var vU) (.var vL)) (rdV (.var vSR) (.var vU) (.var vL)))
def c9 : Hs M := .set vXU (.var vU) ;; .set vXL (.var vL) ;; nxtP ;;
  .set vB (rdV (.var vJ + .const 1) (.var vXR) (.var vL))
def c10 : Hs M := fendP (.var vJ + .const 1) ;; .set vT (.var vSR) ;;
  .set vXU (.var vU) ;; .set vXL (.var vL) ;; nxtP ;;
  .set vB (Ex.bor (rdV (.var vT) (.var vU) (.var vL))
    (Ex.band (rdV (.var vJ + .const 1) (.var vU) (.var vL))
      (Ex.band (Ex.lt (.var vU) (.var vXR)) (rdV (.var vJ) (.var vXR) (.var vL)))))
def c11 : Hs M := .set vEA (.const 0) ;; .set vEL (.const 0) ;;
  .loop (Ex.lt (.var vEL) (.var vN))
    (.set vEA (Ex.bor (.var vEA) (rdV (.var vJ + .const 1) (.var vU) (.var vEL))) ;;
      .set vEL (.var vEL + .const 1)) ;;
  .set vB (.var vEA)

/-- Compute `B := val J U L`. -/
def valCompute : Hs M :=
  .ite (Ex.eq (.tok (.var vJ)) (.const 5)) c5 <|
  .ite (Ex.eq (.tok (.var vJ)) (.const 6)) c6 <|
  .ite (Ex.eq (.tok (.var vJ)) (.const 7)) c7 <|
  .ite (Ex.eq (.tok (.var vJ)) (.const 8)) c8 <|
  .ite (Ex.eq (.tok (.var vJ)) (.const 9)) c9 <|
  .ite (Ex.eq (.tok (.var vJ)) (.const 10)) c10 <|
  .ite (Ex.eq (.tok (.var vJ)) (.const 11)) c11 <|
  .set vB (.const 0)

section cases

variable {σ : HSt M} {j u ℓ : ℕ}

lemma hach_c5 (h : VCtx ts w B σ j u ℓ) (ht : tc ts j = 5) :
    HAch w B c5 σ (VPost ts σ j u ℓ) := by
  have hB64 := h.hc.b64
  have hBn := h.hc.bn
  have hl := h.hl; have hu := h.hu; have hj := h.hj
  refine hach_seq (hach_set (by simp [h.hU]; omega) (hach_seq (hach_set
    (by simp [h.hJ]; omega) ?_)))
  refine hach_seq ((hach_labHasP h.hc _ (by simp [h.hN])
    (by simp [h.hU]; omega)
    (by simp [h.hJ]; omega)).mono ?_)
  rintro σ3 ⟨hR, hf3⟩
  simp only [HSt.set_v, Function.update_apply, ev_add, ev_var, ev_const, h.hU, h.hJ] at hR
  simp only [Fin.reduceEq, if_true, if_false] at hR
  refine hach_set (by simp [hR]; have := bv_le (labHas ts (u + 2) (j + 1)); omega) ⟨?_, ?_⟩
  · simp [hR, val_lt hj, ht]
  · exact ((((Frame.refl _ _).set (by decide) _).set (by decide) _).trans
      (hf3.mono (by decide))).set (by decide) _

lemma hach_c6 (h : VCtx ts w B σ j u ℓ) (ht : tc ts j = 6) :
    HAch w B c6 σ (VPost ts σ j u ℓ) := by
  have hB64 := h.hc.b64
  have hBn := h.hc.bn
  refine hach_set (by simp; omega) ⟨?_, (Frame.refl _ _).set (by decide) _⟩
  simp [val_lt h.hj, ht]

lemma hach_c7 (h : VCtx ts w B σ j u ℓ) (ht : tc ts j = 7) :
    HAch w B c7 σ (VPost ts σ j u ℓ) := by
  have hB64 := h.hc.b64
  have hBn := h.hc.bn
  have hl := h.hl; have hu := h.hu; have hj := h.hj
  refine hach_set (bnd_bnot' (bnd_rdV h.hc h.hN (by simp [h.hJ]; omega) (by simp [h.hU]; omega)
    (by simp [h.hL]; omega) (by simp [h.hJ]; omega) (by simp [h.hU]; omega)
    (by simp [h.hL]; omega)) (by omega)) ⟨?_, (Frame.refl _ _).set (by decide) _⟩
  rw [HSt.set_v, Function.update_self, ev_bnot', ev_rdV_val h.hm h.hN (by simp [h.hL]; omega)
    (fun _ _ => by simp [h.hJ, Dn])]
  simp [val_lt h.hj, ht, h.hJ, h.hU, h.hL, hu]

lemma hach_c8 (h : VCtx ts w B σ j u ℓ) (ht : tc ts j = 8) :
    HAch w B c8 σ (VPost ts σ j u ℓ) := by
  have hB64 := h.hc.b64
  have hBn := h.hc.bn
  have hl := h.hl; have hu := h.hu; have hj := h.hj
  refine hach_seq ((hach_fendP h.hc σ h.hN _ (by simp [h.hJ]; omega)
    (by simp [h.hJ]; omega)).mono ?_)
  rintro σ2 ⟨hF, hf2⟩
  have h2 := h.of_frame (hf2.mono (by decide))
  simp only [ev_add, ev_var, ev_const, h.hJ] at hF
  have hFl := fend_le (ts := ts) (p := j + 1) (by omega)
  have hFg := le_fend (ts := ts) (j + 1)
  refine hach_set (bnd_band' (bnd_rdV h.hc h2.hN (by simp [h2.hJ]; omega)
    (by simp [h2.hU]; omega) (by simp [h2.hL]; omega) (by simp [h2.hJ]; omega)
    (by simp [h2.hU]; omega) (by simp [h2.hL]; omega))
    (bnd_rdV h.hc h2.hN (by simp [hF]; omega)
    (by simp [h2.hU]; omega) (by simp [h2.hL]; omega) (by simp [hF]; omega)
    (by simp [h2.hU]; omega) (by simp [h2.hL]; omega)) (rdV_le_one _ _ _ _)
    (rdV_le_one _ _ _ _) (by omega)) ⟨?_, (hf2.mono (by decide)).set (by decide) _⟩
  rw [HSt.set_v, Function.update_self, ev_band',
    ev_rdV_val h2.hm h2.hN (by simp [h2.hL]; omega) (fun _ _ => by simp [h2.hJ, Dn]),
    ev_rdV_val h2.hm h2.hN (by simp [h2.hL]; omega) (fun _ _ => by simp [hF, Dn]; omega)]
  simp [val_lt h.hj, ht, h2.hJ, h2.hU, h2.hL, hu, hF]

lemma hach_c9 (h : VCtx ts w B σ j u ℓ) (ht : tc ts j = 9) :
    HAch w B c9 σ (VPost ts σ j u ℓ) := by
  have hB64 := h.hc.b64
  have hBn := h.hc.bn
  have hl := h.hl; have hu := h.hu; have hj := h.hj
  refine hach_seq (hach_set (by simp [h.hU]; omega) (hach_seq (hach_set
    (by simp [h.hL]; omega) ?_)))
  have hf1 : Frame clV σ ((σ.set vXU ((Ex.var vU).ev w σ)).set vXL
      ((Ex.var vL).ev w (σ.set vXU ((Ex.var vU).ev w σ)))) :=
    (((Frame.refl _ _).set (by decide) _).set (by decide) _)
  have e1U : ((σ.set vXU ((Ex.var vU).ev w σ)).set vXL
      ((Ex.var vL).ev w (σ.set vXU ((Ex.var vU).ev w σ)))).v vXU = u := by
    simp [h.hU]
  have e1L : ((σ.set vXU ((Ex.var vU).ev w σ)).set vXL
      ((Ex.var vL).ev w (σ.set vXU ((Ex.var vU).ev w σ)))).v vXL = ℓ := by
    simp [h.hL]
  generalize (σ.set vXU ((Ex.var vU).ev w σ)).set vXL
      ((Ex.var vL).ev w (σ.set vXU ((Ex.var vU).ev w σ))) = σ1 at hf1 e1U e1L ⊢
  have h1 := h.of_frame hf1
  refine hach_seq ((hach_nxtP h.hc σ1 h1.hN (by omega) (by omega)).mono ?_)
  rintro σ2 ⟨hX, hf2⟩
  rw [e1U, e1L] at hX
  have hf2' : Frame clV σ σ2 := hf1.trans (hf2.mono (by decide))
  have h2 := h.of_frame hf2'
  have hXl := nxt_le (ts := ts) (u := u) (by omega) ℓ
  refine hach_set (bnd_rdV h.hc h2.hN (by simp [h2.hJ]; omega)
    (by simp [hX]; omega) (by simp [h2.hL]; omega) (by simp [h2.hJ]; omega)
    (by simp [hX]; omega) (by simp [h2.hL]; omega)) ⟨?_, hf2'.set (by decide) _⟩
  rw [HSt.set_v, Function.update_self,
    ev_rdV_val h2.hm h2.hN (by simp [h2.hL]; omega) (fun _ _ => by simp [h2.hJ, Dn])]
  rw [val_lt hj u ℓ]
  simp only [ev_add, ev_var, ev_const, h2.hJ, hX, h2.hL, ht]
  by_cases hn : nxt ts ℓ u < ts.length <;> simp [hn]

lemma hach_c10 (h : VCtx ts w B σ j u ℓ) (ht : tc ts j = 10) :
    HAch w B c10 σ (VPost ts σ j u ℓ) := by
  have hB64 := h.hc.b64
  have hBn := h.hc.bn
  have hl := h.hl; have hu := h.hu; have hj := h.hj
  refine hach_seq ((hach_fendP h.hc σ h.hN _ (by simp [h.hJ]; omega)
    (by simp [h.hJ]; omega)).mono ?_)
  rintro σ2 ⟨hF, hf2⟩
  have hf2' : Frame clV σ σ2 := hf2.mono (by decide)
  have h2 := h.of_frame hf2'
  simp only [ev_add, ev_var, ev_const, h.hJ] at hF
  have hFl := fend_le (ts := ts) (p := j + 1) (by omega)
  have hFg := le_fend (ts := ts) (j + 1)
  refine hach_seq (hach_set (by simp [hF]; omega) (hach_seq (hach_set (by simp [h2.hU]; omega)
    (hach_seq (hach_set (by simp [h2.hL]; omega) ?_)))))
  have hf3 : Frame clV σ (((σ2.set vT ((Ex.var vSR).ev w σ2)).set vXU
      ((Ex.var vU).ev w (σ2.set vT ((Ex.var vSR).ev w σ2)))).set vXL
      ((Ex.var vL).ev w ((σ2.set vT ((Ex.var vSR).ev w σ2)).set vXU
      ((Ex.var vU).ev w (σ2.set vT ((Ex.var vSR).ev w σ2)))))) :=
    ((hf2'.set (by decide) _).set (by decide) _).set (by decide) _
  have e3T : (((σ2.set vT ((Ex.var vSR).ev w σ2)).set vXU
      ((Ex.var vU).ev w (σ2.set vT ((Ex.var vSR).ev w σ2)))).set vXL
      ((Ex.var vL).ev w ((σ2.set vT ((Ex.var vSR).ev w σ2)).set vXU
      ((Ex.var vU).ev w (σ2.set vT ((Ex.var vSR).ev w σ2)))))).v vT = fend ts (j + 1) := by
    simp [hF]
  have e3U : (((σ2.set vT ((Ex.var vSR).ev w σ2)).set vXU
      ((Ex.var vU).ev w (σ2.set vT ((Ex.var vSR).ev w σ2)))).set vXL
      ((Ex.var vL).ev w ((σ2.set vT ((Ex.var vSR).ev w σ2)).set vXU
      ((Ex.var vU).ev w (σ2.set vT ((Ex.var vSR).ev w σ2)))))).v vXU = u := by
    simp [h2.hU]
  have e3L : (((σ2.set vT ((Ex.var vSR).ev w σ2)).set vXU
      ((Ex.var vU).ev w (σ2.set vT ((Ex.var vSR).ev w σ2)))).set vXL
      ((Ex.var vL).ev w ((σ2.set vT ((Ex.var vSR).ev w σ2)).set vXU
      ((Ex.var vU).ev w (σ2.set vT ((Ex.var vSR).ev w σ2)))))).v vXL = ℓ := by
    simp [h2.hL]
  generalize (((σ2.set vT ((Ex.var vSR).ev w σ2)).set vXU
      ((Ex.var vU).ev w (σ2.set vT ((Ex.var vSR).ev w σ2)))).set vXL
      ((Ex.var vL).ev w ((σ2.set vT ((Ex.var vSR).ev w σ2)).set vXU
      ((Ex.var vU).ev w (σ2.set vT ((Ex.var vSR).ev w σ2)))))) = σ3 at hf3 e3T e3U e3L ⊢
  have h3 := h.of_frame hf3
  refine hach_seq ((hach_nxtP h.hc σ3 h3.hN (by omega) (by omega)).mono ?_)
  rintro σ4 ⟨hX, hf4⟩
  rw [e3U, e3L] at hX
  have hf4' : Frame clV σ σ4 := hf3.trans (hf4.mono (by decide))
  have h4 := h.of_frame hf4'
  have e4T : σ4.v vT = fend ts (j + 1) := by rw [hf4.1 _ (by decide), e3T]
  have hXl := nxt_le (ts := ts) (u := u) (by omega) ℓ
  have b1 := bnd_rdV (a := .var vT) (b := .var vU) (c := .var vL) h.hc h4.hN
    (by simp [e4T]; omega) (by simp [h4.hU]; omega) (by simp [h4.hL]; omega)
    (by simp [e4T]; omega) (by simp [h4.hU]; omega) (by simp [h4.hL]; omega)
  have b2 := bnd_rdV (a := .var vJ + .const 1) (b := .var vU) (c := .var vL) h.hc h4.hN
    (by simp [h4.hJ]; omega) (by simp [h4.hU]; omega) (by simp [h4.hL]; omega)
    (by simp [h4.hJ]; omega) (by simp [h4.hU]; omega) (by simp [h4.hL]; omega)
  have b3 := bnd_rdV (a := .var vJ) (b := .var vXR) (c := .var vL) h.hc h4.hN
    (by simp [h4.hJ]; omega) (by simp [hX]; omega) (by simp [h4.hL]; omega)
    (by simp [h4.hJ]; omega) (by simp [hX]; omega) (by simp [h4.hL]; omega)
  have b4 : (Ex.lt (.var vU) (.var vXR) : Ex M).Bnd w B σ4 :=
    bnd_lt' (by simp [h4.hU]; omega) (by simp [hX]; omega)
  have l4 : (Ex.lt (.var vU) (.var vXR) : Ex M).ev w σ4 ≤ 1 := by rw [ev_lt]; exact bv_le _
  have r1 := rdV_le_one (w := w) σ4 (.var vT) (.var vU) (.var vL)
  have r2 := rdV_le_one (w := w) σ4 (.var vJ + .const 1) (.var vU) (.var vL)
  have r3 := rdV_le_one (w := w) σ4 (.var vJ) (.var vXR) (.var vL)
  have m1 : (Ex.band (Ex.lt (.var vU) (.var vXR)) (rdV (.var vJ) (.var vXR) (.var vL))).ev w σ4
      ≤ 1 := by rw [ev_band']; nlinarith
  have m2 : (Ex.band (rdV (.var vJ + .const 1) (.var vU) (.var vL))
      (Ex.band (Ex.lt (.var vU) (.var vXR)) (rdV (.var vJ) (.var vXR) (.var vL)))).ev w σ4 ≤ 1 := by
    rw [ev_band']; nlinarith
  have bb1 := bnd_band' b4 b3 l4 r3 (by omega)
  have bb2 := bnd_band' b2 bb1 r2 m1 (by omega)
  refine hach_set (bnd_bor' b1 bb2 r1 m2 (by omega)) ⟨?_, hf4'.set (by decide) _⟩
  rw [HSt.set_v, Function.update_self, ev_bor', ev_band', ev_band',
    ev_rdV_val h4.hm h4.hN (by simp [h4.hL]; omega) (fun _ _ => by simp [e4T, Dn]; omega),
    ev_rdV_val h4.hm h4.hN (by simp [h4.hL]; omega) (fun _ _ => by simp [h4.hJ, Dn]), ev_lt]
  rw [val_lt hj u ℓ]
  simp only [ev_add, ev_var, ev_const, h4.hJ, hX, h4.hL, h4.hU, e4T, ht]
  by_cases hun : u < nxt ts ℓ u
  · rw [ev_rdV_val h4.hm h4.hN (by simp [h4.hL]; omega)
      (fun _ _ => by simp [h4.hJ, hX, Dn]; omega)]
    simp only [ev_var, h4.hJ, hX, h4.hL]
    by_cases hn : nxt ts ℓ u < ts.length <;> simp [hn, hun, hu]
  · simp [hun, hu]

lemma hach_c11 (h : VCtx ts w B σ j u ℓ) (ht : tc ts j = 11) :
    HAch w B c11 σ (VPost ts σ j u ℓ) := by
  have hB64 := h.hc.b64
  have hBn := h.hc.bn
  have hl := h.hl; have hu := h.hu; have hj := h.hj
  refine hach_seq (hach_set (bnd_const' (by omega)) (hach_seq (hach_set (bnd_const' (by omega))
    (hach_seq ?_))))
  let I : ℕ → HSt M → Prop := fun p σ1 => Frame clV σ σ1 ∧
    σ1.v vEA = bv ((List.range p).any fun ℓ' => val ts (j + 1) u ℓ')
  refine (hach_forUp vEL vN (by decide) ts.length (by omega) I ?_ 0 (by omega) _
    ⟨((Frame.refl _ _).set (by decide) _).set (by decide) _, by simp⟩ (by simp)
    (by simp [h.hN])).mono ?_
  · intro p σ1 hp ⟨hf1, hA⟩ hP hN1
    have h1 := h.of_frame hf1
    have r := rdV_le_one (w := w) σ1 (.var vJ + .const 1) (.var vU) (.var vEL)
    have hA1 := bv_le ((List.range p).any fun ℓ' => val ts (j + 1) u ℓ')
    refine hach_set (bnd_bor' (by simp [hA]; omega) (bnd_rdV h.hc h1.hN (by simp [h1.hJ]; omega)
      (by simp [h1.hU]; omega) (by simp [hP]; omega) (by simp [h1.hJ]; omega)
      (by simp [h1.hU]; omega) (by simp [hP]; omega)) (by simp [hA]) r (by omega))
      ⟨by simp [hP], by simp [hN1], ?_, ?_⟩
    · exact (hf1.set (by decide) _).set (by decide) _
    · simp only [HSt.set_v, Function.update_apply, Fin.reduceEq, if_false, if_true]
      rw [ev_bor', ev_rdV_val h1.hm h1.hN (by simp [hP]; omega)
        (fun _ _ => by simp [h1.hJ, Dn])]
      simp [hA, h1.hJ, h1.hU, hP, hu, List.range_succ, List.any_append]
  · rintro σ2 ⟨⟨hf2, hA⟩, -, -⟩
    refine hach_set (by simp [hA]; have := bv_le ((List.range ts.length).any fun ℓ' =>
      val ts (j + 1) u ℓ'); omega) ⟨?_, hf2.set (by decide) _⟩
    rw [val_lt hj u ℓ]
    simp [hA, ht]

lemma hach_c0 (h : VCtx ts w B σ j u ℓ) (ht : tc ts j ∉ [5, 6, 7, 8, 9, 10, 11]) :
    HAch w B (.set vB (.const 0)) σ (VPost ts σ j u ℓ) := by
  have hB64 := h.hc.b64
  have hBn := h.hc.bn
  refine hach_set (bnd_const' (by omega)) ⟨?_, (Frame.refl _ _).set (by decide) _⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ht
  simp [val_lt h.hj, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1,
    ht.2.2.2.2.2.2]

theorem hach_valCompute (h : VCtx ts w B σ j u ℓ) :
    HAch w B valCompute σ (VPost ts σ j u ℓ) := by
  have hB64 := h.hc.b64
  have hBn := h.hc.bn
  have hBn := h.hc.bn
  have hj := h.hj
  have hb : ∀ k ≤ 11, (Ex.eq (.tok (.var vJ)) (.const k) : Ex M).Bnd w B σ := fun k hk =>
    bnd_eq' (by simp [h.hJ]; omega) (by simp; omega) (by omega)
  have he : ∀ k, (Ex.eq (.tok (.var vJ)) (.const k) : Ex M).ev w σ = bv (decide (tc ts j = k)) :=
    fun k => by simp [h.hJ, h.hc.tok]
  unfold valCompute
  refine hach_ite (hb 5 (by omega)) ?_
  rw [he]
  by_cases h5 : tc ts j = 5
  · rw [if_pos (by simp [h5])]; exact hach_c5 h h5
  rw [if_neg (by simp [h5])]
  refine hach_ite (hb 6 (by omega)) ?_
  rw [he]
  by_cases h6 : tc ts j = 6
  · rw [if_pos (by simp [h6])]; exact hach_c6 h h6
  rw [if_neg (by simp [h6])]
  refine hach_ite (hb 7 (by omega)) ?_
  rw [he]
  by_cases h7 : tc ts j = 7
  · rw [if_pos (by simp [h7])]; exact hach_c7 h h7
  rw [if_neg (by simp [h7])]
  refine hach_ite (hb 8 (by omega)) ?_
  rw [he]
  by_cases h8 : tc ts j = 8
  · rw [if_pos (by simp [h8])]; exact hach_c8 h h8
  rw [if_neg (by simp [h8])]
  refine hach_ite (hb 9 (by omega)) ?_
  rw [he]
  by_cases h9 : tc ts j = 9
  · rw [if_pos (by simp [h9])]; exact hach_c9 h h9
  rw [if_neg (by simp [h9])]
  refine hach_ite (hb 10 (by omega)) ?_
  rw [he]
  by_cases h10 : tc ts j = 10
  · rw [if_pos (by simp [h10])]; exact hach_c10 h h10
  rw [if_neg (by simp [h10])]
  refine hach_ite (hb 11 (by omega)) ?_
  rw [he]
  by_cases h11 : tc ts j = 11
  · rw [if_pos (by simp [h11])]; exact hach_c11 h h11
  rw [if_neg (by simp [h11])]
  exact hach_c0 h (by simp [h5, h6, h7, h8, h9, h10, h11])

end cases

end CTLP

end PathChecking
