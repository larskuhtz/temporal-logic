module

public import RequestProject.MCVP.Num

/-!
# Parsing one gate of a circuit

`gateStep` reads the encoding of one gate from the input and checks that its arguments refer
to earlier gates (their indices are smaller than the counter `rN`).  On malformed input the
`ok` register is cleared.
-/

@[expose] public section

namespace PathChecking

namespace MCVPReduction

open LS
open scoped LS

variable {w : Word} {B : ℕ}

/-! ## Uniqueness of numbers and gates on the input -/

lemma NumAt.unique {p : ℕ} {ds ds' : List Bool} (h1 : NumAt w p ds) (h2 : NumAt w p ds') :
    ds = ds' := by
  rcases At.toks_compat h1 h2 with ⟨vs, hvs⟩ | ⟨vs, hvs⟩
  · exact (digits_sep_eq (l := vs) (l' := []) (by simpa using hvs.symm)).1
  · exact (digits_sep_eq (l := []) (l' := vs) (by simpa using hvs)).1

lemma numAt_natToks {p i : ℕ} : At w p (encodeToks (natToks i)) ↔ NumAt w p (Nat.bits i) := by
  rw [NumAt, natToks_eq]

lemma natToks_at_unique {p i j : ℕ} (h1 : At w p (encodeToks (natToks i)))
    (h2 : At w p (encodeToks (natToks j))) : i = j :=
  bits_injective (NumAt.unique (numAt_natToks.1 h1) (numAt_natToks.1 h2))

/-- Gates whose arguments are smaller than `k`. -/
def GateOk : MGate → ℕ → Prop
  | .input _, _ => True
  | .and i j, k => i < k ∧ j < k
  | .or i j, k => i < k ∧ j < k

lemma natToks_length (n : ℕ) : (natToks n).length = (Nat.bits n).length + 1 := by
  simp [natToks]

/-- What a gate found at `p` looks like, given the token found at `p`. -/
lemma gate_at_cases {p : ℕ} {G : MGate} {t : Tok} (hG : At w p (encodeToks G.toks))
    (ht : At w p t.bits) :
    (t = .tag 0 ∧ G = .input false) ∨ (t = .tag 1 ∧ G = .input true) ∨
    (t = .tag 2 ∧ ∃ i j, G = .and i j ∧ At w (p + 5) (encodeToks (natToks i ++ natToks j))) ∨
    (t = .tag 3 ∧ ∃ i j, G = .or i j ∧ At w (p + 5) (encodeToks (natToks i ++ natToks j))) := by
  cases G with
  | input b =>
    cases b
    · left; refine ⟨At.tok_eq ht (At.toks_cons.1 hG).1, rfl⟩
    · right; left; refine ⟨At.tok_eq ht (At.toks_cons.1 hG).1, rfl⟩
  | and i j =>
    right; right; left
    have := At.toks_cons.1 hG
    exact ⟨At.tok_eq ht this.1, i, j, rfl, this.2⟩
  | or i j =>
    right; right; right
    have := At.toks_cons.1 hG
    exact ⟨At.tok_eq ht this.1, i, j, rfl, this.2⟩

/-! ## Checking an argument -/

/-- Read a number and check that it is the canonical encoding of an index `< rN`. -/
def checkNum : Stmt 20 :=
  cmpNum rN ⨟ .ite (.zero rLt) (clear rOk) .skip ⨟ .ite (.zero rLast) (clear rOk) .skip

lemma rN_not_mem_cmpClob : rN ∉ cmpClob := by decide

lemma ach_checkNum (σ : St 20) (Q : St 20 → Prop)
    (hp1 : 1 ≤ σ.pos) (hp2 : σ.pos ≤ w.length + 1) (hyB : σ.reg rN ≤ B) (hB : 1 ≤ B)
    (h : ∀ τ : St 20, τ.out = σ.out → 1 ≤ τ.pos → τ.pos ≤ w.length + 1 →
      (∀ x, x ∉ cmpClob → τ.reg x = σ.reg x) →
      ((∃ i, i < σ.reg rN ∧ At w σ.pos (encodeToks (natToks i)) ∧
          τ.pos = σ.pos + 5 * (natToks i).length ∧ τ.reg rOk = σ.reg rOk) ∨
        (τ.reg rOk = 0 ∧ ∀ i, i < σ.reg rN → ¬ At w σ.pos (encodeToks (natToks i)))) → Q τ) :
    Ach w B checkNum σ Q := by
  unfold checkNum
  refine ach_seq (ach_cmpNum rN rN_not_mem_cmpClob σ _ hp1 hp2 hyB hB ?_)
  intro τ ho hq1 hq2 hfr hres
  -- the two checks
  have fail : ∀ τ' : St 20, τ'.out = σ.out → τ'.pos = τ.pos → τ'.reg rOk = 0 →
      (∀ x, x ≠ rOk → τ'.reg x = τ.reg x) →
      (∀ i, i < σ.reg rN → ¬ At w σ.pos (encodeToks (natToks i))) → Q τ' := by
    intro τ' h1 h2 h3 h4 h5
    refine h τ' h1 (by omega) (by omega) ?_ (Or.inr ⟨h3, h5⟩)
    intro x hx
    rw [h4 x (by rintro rfl; exact hx (by decide))]; exact hfr x hx
  rcases hres with ⟨ds, hnum, hpos, hok, hlt, -, hlast⟩ | ⟨hok, hno⟩
  · have hno : ¬ (ofBits ds < σ.reg rN ∧ Canon ds) →
        ∀ i, i < σ.reg rN → ¬ At w σ.pos (encodeToks (natToks i)) := by
      intro hn i hi hAt
      have := NumAt.unique hnum (numAt_natToks.1 hAt)
      subst this
      exact hn ⟨by rwa [ofBits_bits], canon_bits i⟩
    by_cases h1 : τ.reg rLt = 0
    · refine ach_seq (ach_iteT (by simp [Cond.eval, h1]) (ach_clear _ _ _ (ach_ite ?_)))
      split_ifs
      · exact ach_clear _ _ _ (fail _ (by simp [ho]) (by simp) (by simp [St.setReg_apply])
          (fun x hx => by simp [St.setReg_apply, hx]) (hno (by rw [← hlt]; simp [h1])))
      · exact ach_skip (fail _ (by simp [ho]) (by simp) (by simp [St.setReg_apply])
          (fun x hx => by simp [St.setReg_apply, hx]) (hno (by rw [← hlt]; simp [h1])))
    · refine ach_seq (ach_iteF (by simp [Cond.eval, h1]) (ach_skip ?_))
      by_cases h2 : τ.reg rLast = 0
      · refine ach_iteT (by simp [Cond.eval, h2]) (ach_clear _ _ _ ?_)
        exact fail _ (by simp [ho]) (by simp) (by simp [St.setReg_apply])
          (fun x hx => by simp [St.setReg_apply, hx]) (hno (by rw [← hlast]; simp [h2]))
      · refine ach_iteF (by simp [Cond.eval, h2]) (ach_skip ?_)
        have hc : Canon ds := hlast.1 h2
        have hl : ofBits ds < σ.reg rN := hlt.1 h1
        refine h τ ho hq1 hq2 hfr (Or.inl ⟨ofBits ds, hl, ?_, ?_, hok⟩)
        · rw [numAt_natToks, bits_ofBits hc]; exact hnum
        · rw [hpos, natToks_length, bits_ofBits hc]
  · refine ach_seq (ach_ite ?_)
    split_ifs
    · refine ach_clear _ _ _ (ach_ite ?_)
      split_ifs
      · exact ach_clear _ _ _ (fail _ (by simp [ho]) (by simp) (by simp [St.setReg_apply])
          (fun x hx => by simp [St.setReg_apply, hx]) (fun i _ hAt =>
            hno _ (numAt_natToks.1 hAt)))
      · exact ach_skip (fail _ (by simp [ho]) (by simp) (by simp [St.setReg_apply])
          (fun x hx => by simp [St.setReg_apply, hx]) (fun i _ hAt =>
            hno _ (numAt_natToks.1 hAt)))
    · refine ach_skip (ach_ite ?_)
      split_ifs
      · exact ach_clear _ _ _ (fail _ (by simp [ho]) (by simp) (by simp [St.setReg_apply])
          (fun x hx => by simp [St.setReg_apply, hx]) (fun i _ hAt =>
            hno _ (numAt_natToks.1 hAt)))
      · exact ach_skip (fail _ ho rfl hok (fun _ _ => rfl) (fun i _ hAt =>
            hno _ (numAt_natToks.1 hAt)))

/-! ## Parsing a gate -/

lemma gate_fail_none {p : ℕ} (hno : ∀ t : Tok, ¬ At w p t.bits) (G : MGate) :
    ¬ At w p (encodeToks G.toks) := by
  intro hG
  cases G with
  | input b => cases b <;> exact hno _ (At.toks_cons.1 hG).1
  | and i j => exact hno _ (At.toks_cons.1 hG).1
  | or i j => exact hno _ (At.toks_cons.1 hG).1

lemma gate_fail_tok {p : ℕ} {t : Tok} (ht : At w p t.bits)
    (htag : ¬ (t = .tag 0 ∨ t = .tag 1 ∨ t = .tag 2 ∨ t = .tag 3)) (G : MGate) :
    ¬ At w p (encodeToks G.toks) := by
  intro hG
  rcases gate_at_cases hG ht with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp_all

lemma gate_fail_arg1 {p k : ℕ} {t : Tok} (ht : At w p t.bits) (htag : t = .tag 2 ∨ t = .tag 3)
    (hno : ∀ i, i < k → ¬ At w (p + 5) (encodeToks (natToks i))) (G : MGate) (hG : GateOk G k) :
    ¬ At w p (encodeToks G.toks) := by
  intro hAt
  rcases gate_at_cases hAt ht with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, i, j, rfl, h⟩ | ⟨-, i, j, rfl, h⟩
  · rcases htag with rfl | rfl <;> simp at h1
  · rcases htag with rfl | rfl <;> simp at h1
  · exact hno i hG.1 (At.toks_append.1 h).1
  · exact hno i hG.1 (At.toks_append.1 h).1

lemma gate_fail_arg2 {p k i : ℕ} {t : Tok} (ht : At w p t.bits) (htag : t = .tag 2 ∨ t = .tag 3)
    (hi : At w (p + 5) (encodeToks (natToks i)))
    (hno : ∀ j, j < k → ¬ At w (p + 5 + 5 * (natToks i).length) (encodeToks (natToks j)))
    (G : MGate) (hG : GateOk G k) : ¬ At w p (encodeToks G.toks) := by
  intro hAt
  rcases gate_at_cases hAt ht with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, i', j, rfl, h⟩ | ⟨-, i', j, rfl, h⟩
  · rcases htag with rfl | rfl <;> simp at h1
  · rcases htag with rfl | rfl <;> simp at h1
  · have h' := At.toks_append.1 h
    obtain rfl := natToks_at_unique h'.1 hi
    exact hno j hG.2 h'.2
  · have h' := At.toks_append.1 h
    obtain rfl := natToks_at_unique h'.1 hi
    exact hno j hG.2 h'.2

/-- Action on the first token of a gate. -/
def gateTok (t : Tok) : Stmt 20 :=
  if t = .tag 0 ∨ t = .tag 1 then .inc rN
  else if t = .tag 2 ∨ t = .tag 3 then
    checkNum ⨟ .ite (.zero rOk) .skip (checkNum ⨟ .ite (.zero rOk) .skip (.inc rN))
  else clear rOk

/-- Parse one gate, checking that its arguments are `< rN`, and increment `rN`. -/
def gateStep : Stmt 20 := caseTok gateTok (clear rOk)

/-- Registers modified by `gateStep`. -/
def gateClob : List (Fin 20) := rN :: cmpClob

lemma gateClob_of_cmpClob : ∀ x, x ∉ gateClob → x ∉ cmpClob := by decide

/-- Result of `gateStep`. -/
def GateRes (w : Word) (σ τ : St 20) : Prop :=
  (∃ G, GateOk G (σ.reg rN) ∧ At w σ.pos (encodeToks G.toks) ∧
      τ.pos = σ.pos + 5 * G.toks.length ∧ τ.reg rOk ≠ 0 ∧ τ.reg rN = σ.reg rN + 1) ∨
  (τ.reg rOk = 0 ∧ ∀ G, GateOk G (σ.reg rN) → ¬ At w σ.pos (encodeToks G.toks))

lemma ach_gateStep (σ : St 20) (Q : St 20 → Prop)
    (hp1 : 1 ≤ σ.pos) (hp2 : σ.pos ≤ w.length + 1) (hok : σ.reg rOk ≠ 0) (hN : σ.reg rN < B)
    (hB : 1 ≤ B)
    (h : ∀ τ : St 20, τ.out = σ.out → 1 ≤ τ.pos → τ.pos ≤ w.length + 1 →
      (∀ x, x ∉ gateClob → τ.reg x = σ.reg x) → GateRes w σ τ → Q τ) :
    Ach w B gateStep σ Q := by
  unfold gateStep
  refine ach_caseTok_fail gateTok (clear rOk) Q σ hp1 hp2 ?_ ?_
  · intro t ht
    have hle := ht.le
    rw [Tok.bits_length] at hle
    by_cases h01 : t = .tag 0 ∨ t = .tag 1
    · rw [gateTok, if_pos h01]
      refine ach_inc (by simpa using hN) (h _ (by simp) (by simp) (by simp; omega) ?_ ?_)
      · intro x hx
        have : x ≠ rN := by rintro rfl; exact hx (by decide)
        simp [St.setReg_apply, this]
      · left
        refine ⟨if t = .tag 0 then .input false else .input true, ?_, ?_, ?_, ?_, ?_⟩
        · split_ifs <;> trivial
        · rcases h01 with rfl | rfl <;> simpa [MGate.toks, encodeToks] using ht
        · split_ifs <;> simp [MGate.toks]
        · simpa [St.setReg_apply] using hok
        · simp [St.setReg_apply]
    · by_cases h23 : t = .tag 2 ∨ t = .tag 3
      · rw [gateTok, if_neg h01, if_pos h23]
        set σ₁ : St 20 := { σ with pos := σ.pos + 5 } with hσ₁
        refine ach_seq (ach_checkNum σ₁ _ (by simp [σ₁]) (by simp [σ₁]; omega)
          (by simp [σ₁]; omega) hB ?_)
        intro τ ho hq1 hq2 hfr hres
        have hNτ : τ.reg rN = σ.reg rN := hfr rN rN_not_mem_cmpClob
        rcases hres with ⟨i, hi, hiAt, hpos, hok'⟩ | ⟨hok', hno⟩
        · refine ach_iteF (by simp [Cond.eval, hok', σ₁, hok]) ?_
          refine ach_seq (ach_checkNum τ _ hq1 hq2 (by omega) hB ?_)
          intro τ' ho' hq1' hq2' hfr' hres'
          have hNτ' : τ'.reg rN = σ.reg rN := (hfr' rN rN_not_mem_cmpClob).trans hNτ
          rcases hres' with ⟨j, hj, hjAt, hpos', hok''⟩ | ⟨hok'', hno'⟩
          · refine ach_iteF (by simp [Cond.eval, hok'', hok', σ₁, hok]) ?_
            refine ach_inc (by omega) (h _ (by simp [ho', ho, σ₁]) (by simp; omega)
              (by simp; omega) ?_ ?_)
            · intro x hx
              have : x ≠ rN := by rintro rfl; exact hx (by decide)
              simp only [St.setReg_apply, this, if_false]
              rw [hfr' x (gateClob_of_cmpClob x hx), hfr x (gateClob_of_cmpClob x hx)]
            · left
              have hG : ∃ G : MGate, GateOk G (σ.reg rN) ∧ G.toks = t :: (natToks i ++ natToks j) := by
                rcases h23 with rfl | rfl
                · exact ⟨.and i j, ⟨by omega, by omega⟩, rfl⟩
                · exact ⟨.or i j, ⟨by omega, by omega⟩, rfl⟩
              obtain ⟨G, hGok, hGt⟩ := hG
              refine ⟨G, hGok, ?_, ?_, ?_, ?_⟩
              · rw [hGt, At.toks_cons, At.toks_append]
                refine ⟨ht, by simpa [σ₁] using hiAt, ?_⟩
                rw [hpos] at hjAt; simpa [σ₁] using hjAt
              · simp only [St.setReg_pos]; rw [hpos', hpos, hGt]; simp [σ₁]; ring
              · simp [St.setReg_apply, hok'', hok', σ₁, hok]
              · simp [St.setReg_apply, hNτ']
          · refine ach_iteT (by simp [Cond.eval, hok'']) (ach_skip ?_)
            refine h _ (by simp [ho', ho, σ₁]) hq1' hq2' ?_ (Or.inr ⟨hok'', ?_⟩)
            · intro x hx
              rw [hfr' x (gateClob_of_cmpClob x hx), hfr x (gateClob_of_cmpClob x hx)]
            · refine gate_fail_arg2 ht h23 (by simpa [σ₁] using hiAt) ?_
              intro j hj hAt
              refine hno' j (by omega) ?_
              rw [hpos]; simpa [σ₁] using hAt
        · refine ach_iteT (by simp [Cond.eval, hok']) (ach_skip ?_)
          refine h _ (by simp [ho, σ₁]) hq1 hq2 ?_ (Or.inr ⟨hok', ?_⟩)
          · intro x hx
            rw [hfr x (gateClob_of_cmpClob x hx)]
          · refine gate_fail_arg1 ht h23 ?_
            intro i hi hAt
            exact hno i (by simpa [σ₁] using hi) (by simpa [σ₁] using hAt)
      · rw [gateTok, if_neg h01, if_neg h23]
        refine ach_clear _ _ _ (h _ (by simp) (by simp) (by simp; omega) ?_
          (Or.inr ⟨by simp [St.setReg_apply], fun G _ => gate_fail_tok ht ?_ G⟩))
        · intro x hx
          have : x ≠ rOk := by rintro rfl; exact hx (by decide)
          simp [St.setReg_apply, this]
        · simp only [not_or] at h01 h23 ⊢
          exact ⟨h01.1, h01.2, h23.1, h23.2⟩
  · intro p h1 h2 hno
    refine ach_clear _ _ _ (h _ (by simp) (by simpa using h1) (by simpa using h2) ?_
      (Or.inr ⟨by simp [St.setReg_apply], fun G _ => gate_fail_none hno G⟩))
    intro x hx
    have : x ≠ rOk := by rintro rfl; exact hx (by decide)
    simp [St.setReg_apply, this]

end MCVPReduction

end PathChecking
