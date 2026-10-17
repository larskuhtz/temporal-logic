module

public import RequestProject.MCVP.Read

/-!
# Comparing a binary number on the input with a register

The register file of the reduction program, and the subroutine `cmpNum y`, which reads a
binary number (least significant digit first, terminated by `sep`) from the input and
compares it with the contents of register `y`.
-/

@[expose] public section

namespace PathChecking

namespace MCVPReduction

open LS
open scoped LS

variable {w : Word} {B : ℕ}

/-! ## Registers -/

/-- Validity flag. -/
scoped notation "rOk" => (0 : Fin 20)
/-- Number of gates. -/
scoped notation "rN" => (1 : Fin 20)
/-- Main loop counter. -/
scoped notation "rK" => (2 : Fin 20)
/-- Second loop counter. -/
scoped notation "rG" => (3 : Fin 20)
/-- Temporaries of `cmpNum`. -/
scoped notation "rT" => (4 : Fin 20)
scoped notation "rQ" => (5 : Fin 20)
scoped notation "rB" => (6 : Fin 20)
/-- Flags computed by `cmpNum`. -/
scoped notation "rLt" => (7 : Fin 20)
scoped notation "rEq" => (8 : Fin 20)
scoped notation "rLast" => (9 : Fin 20)
/-- Loop control. -/
scoped notation "rGo" => (10 : Fin 20)
/-- Further temporaries. -/
scoped notation "rLoc" => (11 : Fin 20)
scoped notation "rFl" => (12 : Fin 20)
scoped notation "rCnt" => (13 : Fin 20)
scoped notation "rT2" => (14 : Fin 20)
scoped notation "rV" => (15 : Fin 20)
scoped notation "rTmp" => (16 : Fin 20)
scoped notation "rE1" => (17 : Fin 20)
scoped notation "rE2" => (18 : Fin 20)
scoped notation "rCnt2" => (19 : Fin 20)

/-- `r := 1`. -/
def setOne (r : Fin 20) : Stmt 20 := clear r ⨟ .inc r

lemma ach_setOne (r : Fin 20) (σ : St 20) (Q : St 20 → Prop) (hB : 1 ≤ B)
    (h : Q (σ.setReg r 1)) : Ach w B (setOne r) σ Q := by
  refine ach_seq (ach_clear r σ _ (ach_inc (by simp [St.setReg_apply]; omega) ?_))
  convert h using 1; st_tac

/-! ## One digit -/

/-- Process one digit `d` of the number being compared. -/
def digitStep (d : Bool) : Stmt 20 :=
  halve rT rQ rB ⨟
  (if d then .ite (.zero rB) (clear rLt ⨟ clear rEq) .skip
    else .ite (.zero rB) .skip (setOne rLt ⨟ clear rEq)) ⨟
  addTo rQ rT ⨟
  (if d then setOne rLast else clear rLast)

/-- Registers modified by `digitStep`. -/
def digitClob : List (Fin 20) := [rT, rQ, rB, rLt, rEq, rLast]

lemma ach_digitStep (d : Bool) (τ : St 20) (Q : St 20 → Prop) (hB : 1 ≤ B)
    (hT : τ.reg rT ≤ B)
    (h : ∀ τ' : St 20, τ'.pos = τ.pos → τ'.out = τ.out →
      (∀ x, x ∉ digitClob → τ'.reg x = τ.reg x) →
      τ'.reg rT = τ.reg rT / 2 →
      (τ'.reg rLt ≠ 0 ↔ (d.toNat < τ.reg rT % 2 ∨ (d.toNat = τ.reg rT % 2 ∧ τ.reg rLt ≠ 0))) →
      (τ'.reg rEq ≠ 0 ↔ (d.toNat = τ.reg rT % 2 ∧ τ.reg rEq ≠ 0)) →
      (τ'.reg rLast ≠ 0 ↔ d = true) → Q τ') :
    Ach w B (digitStep d) τ Q := by
  unfold digitStep
  refine ach_seq (ach_halve rT rQ rB (by decide) (by decide) (by decide) τ _ (by omega) hB ?_)
  set τ₁ := ((τ.setReg rT 0).setReg rQ (τ.reg rT / 2)).setReg rB (τ.reg rT % 2) with hτ₁
  have hb : τ.reg rT % 2 < 2 := Nat.mod_lt _ (by norm_num)
  -- the final two steps
  have fin : ∀ τ₂ : St 20, τ₂.pos = τ.pos → τ₂.out = τ.out →
      (∀ x, x ≠ rLt → x ≠ rEq → τ₂.reg x = τ₁.reg x) →
      (τ₂.reg rLt ≠ 0 ↔ (d.toNat < τ.reg rT % 2 ∨ (d.toNat = τ.reg rT % 2 ∧ τ.reg rLt ≠ 0))) →
      (τ₂.reg rEq ≠ 0 ↔ (d.toNat = τ.reg rT % 2 ∧ τ.reg rEq ≠ 0)) →
      Ach w B (addTo rQ rT ⨟ (if d then setOne rLast else clear rLast)) τ₂ Q := by
    intro τ₂ hp ho hfr hlt heq
    have hQ2 : τ₂.reg rQ = τ.reg rT / 2 := by rw [hfr _ (by decide) (by decide)]; simp [τ₁, St.setReg_apply]
    have hT2 : τ₂.reg rT = 0 := by rw [hfr _ (by decide) (by decide)]; simp [τ₁, St.setReg_apply]
    refine ach_seq (ach_addTo rQ rT (by decide) τ₂ _ (by omega) ?_)
    have hfin : ∀ τ₃ : St 20, τ₃.pos = τ.pos → τ₃.out = τ.out →
        (∀ x, x ≠ rLast → τ₃.reg x = ((τ₂.setReg rQ 0).setReg rT (τ₂.reg rT + τ₂.reg rQ)).reg x) →
        (τ₃.reg rLast ≠ 0 ↔ d = true) → Q τ₃ := by
      intro τ₃ h1 h2 h3 h4
      refine h τ₃ h1 h2 ?_ ?_ ?_ ?_ h4
      · intro x hx
        simp only [digitClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        rw [h3 x (by simpa using hx.2.2.2.2.2)]
        simp only [St.setReg_apply]
        rw [if_neg (by simpa using hx.1), if_neg (by simpa using hx.2.1)]
        rw [hfr x (by simpa using hx.2.2.2.1) (by simpa using hx.2.2.2.2.1)]
        simp only [τ₁, St.setReg_apply]
        rw [if_neg (by simpa using hx.2.2.1), if_neg (by simpa using hx.2.1),
          if_neg (by simpa using hx.1)]
      · rw [h3 _ (by decide)]; simp [St.setReg_apply, hT2, hQ2]
      · rw [h3 _ (by decide)]; simpa [St.setReg_apply] using hlt
      · rw [h3 _ (by decide)]; simpa [St.setReg_apply] using heq
    cases d
    · exact ach_clear _ _ _ (hfin _ (by simp [hp]) (by simp [ho])
        (fun x hx => by simp [St.setReg_apply, hx]) (by simp [St.setReg_apply]))
    · exact ach_setOne _ _ _ hB (hfin _ (by simp [hp]) (by simp [ho])
        (fun x hx => by simp [St.setReg_apply, hx]) (by simp [St.setReg_apply]))
  have hB1 : τ₁.reg rB = τ.reg rT % 2 := by simp [τ₁, St.setReg_apply]
  refine ach_seq ?_
  cases d <;> simp only [Bool.false_eq_true, if_false, if_true] <;> refine ach_ite ?_
  · by_cases h0 : τ.reg rT % 2 = 0
    · rw [if_pos (by simp [Cond.eval, hB1, h0])]
      exact ach_skip (fin τ₁ (by simp [τ₁]) (by simp [τ₁]) (fun _ _ _ => rfl)
        (by simp [τ₁, St.setReg_apply, h0]) (by simp [τ₁, St.setReg_apply, h0]))
    · rw [if_neg (by simp [Cond.eval, hB1, h0])]
      have h1 : τ.reg rT % 2 = 1 := by omega
      refine ach_seq (ach_setOne _ _ _ hB (ach_clear _ _ _ (fin _ (by simp [τ₁])
        (by simp [τ₁]) (fun x h1 h2 => by simp [St.setReg_apply, h1, h2]) ?_ ?_)))
      · simp [St.setReg_apply, h1]
      · simp [St.setReg_apply, h1]
  · by_cases h0 : τ.reg rT % 2 = 0
    · rw [if_pos (by simp [Cond.eval, hB1, h0])]
      refine ach_seq (ach_clear _ _ _ (ach_clear _ _ _ (fin _ (by simp [τ₁])
        (by simp [τ₁]) (fun x h1 h2 => by simp [St.setReg_apply, h1, h2]) ?_ ?_)))
      · simp [St.setReg_apply, h0]
      · simp [St.setReg_apply, h0]
    · rw [if_neg (by simp [Cond.eval, hB1, h0])]
      have h1 : τ.reg rT % 2 = 1 := by omega
      exact ach_skip (fin τ₁ (by simp [τ₁]) (by simp [τ₁]) (fun _ _ _ => rfl)
        (by simp [τ₁, St.setReg_apply, h1]) (by simp [τ₁, St.setReg_apply, h1]))

/-! ## Comparing a number -/

/-- Malformed input: clear the validity flag and stop the loop. -/
def failS : Stmt 20 := clear rOk ⨟ clear rGo

/-- Action on the token read by `cmpNum`. -/
def cmpTok (t : Tok) : Stmt 20 :=
  if t = Tok.zero then digitStep false else if t = Tok.one then digitStep true
  else if t = Tok.sep then clear rGo else failS

/-- Read a binary number from the input and compare it with register `y`: afterwards
`rLt`/`rEq` tell whether the number is `<`/`=` the contents of `y`, and `rLast` whether its
digit string is canonical. -/
def cmpNum (y : Fin 20) : Stmt 20 :=
  copy y rT rQ ⨟ clear rLt ⨟ setOne rEq ⨟ setOne rLast ⨟ setOne rGo ⨟
  whileNZ rGo (caseTok cmpTok failS) ⨟
  .ite (.zero rT) .skip (setOne rLt ⨟ clear rEq)

/-- Registers modified by `cmpNum`. -/
def cmpClob : List (Fin 20) := [rT, rQ, rB, rLt, rEq, rLast, rGo, rOk]

/-- A binary number with digits `ds` (least significant first) is found at position `p`. -/
def NumAt (w : Word) (p : ℕ) (ds : List Bool) : Prop :=
  At w p (encodeToks (ds.map digitTok ++ [.sep]))

/-- Result of `cmpNum`. -/
def CmpRes (w : Word) (p y : ℕ) (σ τ : St 20) : Prop :=
  (∃ ds, NumAt w p ds ∧ τ.pos = p + 5 * (ds.length + 1) ∧ τ.reg rOk = σ.reg rOk ∧
    (τ.reg rLt ≠ 0 ↔ ofBits ds < y) ∧ (τ.reg rEq ≠ 0 ↔ ofBits ds = y) ∧
    (τ.reg rLast ≠ 0 ↔ Canon ds)) ∨
  (τ.reg rOk = 0 ∧ ∀ ds, ¬ NumAt w p ds)

/-- Partial comparison after reading the digits `ds`. -/
def DigInv (y : ℕ) (ds : List Bool) (τ : St 20) : Prop :=
  τ.reg rT = y / 2 ^ ds.length ∧ (τ.reg rLt ≠ 0 ↔ ofBits ds < y % 2 ^ ds.length) ∧
    (τ.reg rEq ≠ 0 ↔ ofBits ds = y % 2 ^ ds.length) ∧ (τ.reg rLast ≠ 0 ↔ Canon ds)

/-- Loop invariant of `cmpNum`. -/
def CmpInv (w : Word) (σ : St 20) (y n : ℕ) (τ : St 20) : Prop :=
  τ.out = σ.out ∧ 1 ≤ τ.pos ∧ τ.pos ≤ w.length + 1 ∧ (∀ x, x ∉ cmpClob → τ.reg x = σ.reg x) ∧
  (τ.reg rGo ≠ 0 → τ.reg rOk = σ.reg rOk ∧ n = w.length + 2 - τ.pos ∧
    ∃ ds, At w σ.pos (encodeToks (ds.map digitTok)) ∧ τ.pos = σ.pos + 5 * ds.length ∧
      DigInv y ds τ) ∧
  (τ.reg rGo = 0 → n = 0 ∧
    ((τ.reg rOk = σ.reg rOk ∧ ∃ ds, NumAt w σ.pos ds ∧ τ.pos = σ.pos + 5 * (ds.length + 1) ∧
      DigInv y ds τ) ∨ (τ.reg rOk = 0 ∧ ∀ ds, ¬ NumAt w σ.pos ds)))

lemma digitClob_sub : ∀ x, x ∉ cmpClob → x ∉ digitClob := by decide

lemma digitTok_ne_sep (d : Bool) : digitTok d ≠ .sep := by cases d <;> simp [digitTok]

lemma sep_not_mem_digits (ds : List Bool) : Tok.sep ∉ ds.map digitTok := by
  simp only [List.mem_map, not_exists, not_and]
  intro d _ h; exact digitTok_ne_sep d h

/-- If digits `ds` are found at `p` and a number is found at `p`, then a digit or `sep` is
found right after `ds`. -/
lemma digits_next {p : ℕ} {ds ds' : List Bool} (h0 : At w p (encodeToks (ds.map digitTok)))
    (h : NumAt w p ds') :
    ∃ v : Tok, (v = .zero ∨ v = .one ∨ v = .sep) ∧ At w (p + 5 * ds.length) v.bits := by
  by_cases hl : ds.length < ds'.length + 1
  · obtain ⟨v, hv, hAt⟩ := At.next_tok h0 h (by simpa using hl)
    refine ⟨v, ?_, by simpa using hAt⟩
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hv
    rcases hv with ⟨d, -, rfl⟩ | rfl
    · cases d <;> simp [digitTok]
    · simp
  · exfalso
    rcases At.toks_compat h0 h with ⟨vs, hvs⟩ | ⟨vs, hvs⟩
    · have := congrArg List.length hvs
      simp at this
      have hvs0 : vs = [] := by rw [← List.length_eq_zero_iff]; omega
      subst hvs0
      have : Tok.sep ∈ ds.map digitTok := by rw [← List.append_nil (ds.map digitTok), ← hvs]; simp
      exact sep_not_mem_digits ds this
    · have : Tok.sep ∈ ds.map digitTok := by rw [hvs]; simp
      exact sep_not_mem_digits ds this

lemma digInv_step (y : ℕ) (ds : List Bool) (d : Bool) (τ τ' : St 20) (h : DigInv y ds τ)
    (hT : τ'.reg rT = τ.reg rT / 2)
    (hlt : τ'.reg rLt ≠ 0 ↔ (d.toNat < τ.reg rT % 2 ∨ (d.toNat = τ.reg rT % 2 ∧ τ.reg rLt ≠ 0)))
    (heq : τ'.reg rEq ≠ 0 ↔ (d.toNat = τ.reg rT % 2 ∧ τ.reg rEq ≠ 0))
    (hlast : τ'.reg rLast ≠ 0 ↔ d = true) : DigInv y (ds ++ [d]) τ' := by
  obtain ⟨h1, h2, h3, -⟩ := h
  have hs := cmp_step y ds.length (ofBits ds) (ofBits_lt ds) d
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hT, h1, Nat.div_div_eq_div_mul, List.length_append, List.length_singleton, pow_succ]
  · rw [hlt, ofBits_append_single, List.length_append, List.length_singleton, hs.1, h1, h2]
  · rw [heq, ofBits_append_single, List.length_append, List.length_singleton, hs.2, h1, h3]
  · rw [hlast, canon_append_single]

lemma ach_cmpNum (y : Fin 20) (hy : y ∉ cmpClob) (σ : St 20) (Q : St 20 → Prop)
    (hp1 : 1 ≤ σ.pos) (hp2 : σ.pos ≤ w.length + 1) (hyB : σ.reg y ≤ B) (hB : 1 ≤ B)
    (h : ∀ τ : St 20, τ.out = σ.out → 1 ≤ τ.pos → τ.pos ≤ w.length + 1 →
      (∀ x, x ∉ cmpClob → τ.reg x = σ.reg x) → CmpRes w σ.pos (σ.reg y) σ τ → Q τ) :
    Ach w B (cmpNum y) σ Q := by
  simp only [cmpClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6, hy7, hy8⟩ := hy
  set v := σ.reg y with hv
  unfold cmpNum whileNZ
  refine ach_seq (ach_copy y rT rQ hy1 hy2 (by decide) σ _ hyB ?_)
  refine ach_seq (ach_clear _ _ _ (ach_seq (ach_setOne _ _ _ hB (ach_seq (ach_setOne _ _ _ hB
    (ach_seq (ach_setOne _ _ _ hB ?_)))))))
  refine ach_seq (Ach.mono (ach_loop (CmpInv w σ v) (fun τ => CmpInv w σ v 0 τ ∧ τ.reg rGo = 0) ?_
    (w.length + 2 - σ.pos) _ ?_) ?_)
  · -- loop step
    intro n τ hI
    obtain ⟨ho, hq1, hq2, hfr, hgo, hstop⟩ := hI
    by_cases hg : τ.reg rGo = 0
    · left
      exact ⟨by simp [Cond.eval, hg], ⟨ho, hq1, hq2, hfr, fun h' => absurd hg h',
        fun h' => ⟨rfl, (hstop h').2⟩⟩, hg⟩
    · right
      obtain ⟨hok, hn, ds, hds, hpos, hdi⟩ := hgo hg
      refine ⟨by simp [Cond.eval, hg], ?_⟩
      have hTB : τ.reg rT ≤ B := by
        rw [hdi.1]; exact (Nat.div_le_self _ _).trans hyB
      -- failure: no number at σ.pos
      have hfail : ∀ p', 1 ≤ p' → p' ≤ w.length + 1 → (∀ ds', ¬ NumAt w σ.pos ds') →
          Ach w B failS { τ with pos := p' } (fun σ' => ∃ m < n, CmpInv w σ v m σ') := by
        intro p' h1 h2 hno
        refine ach_seq (ach_clear _ _ _ (ach_clear _ _ _ ⟨0, by omega, ?_⟩))
        refine ⟨by simp [ho], by simp [h1], by simp [h2], ?_, ?_, ?_⟩
        · intro x hx
          simp only [cmpClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          simp [St.setReg_apply, hx.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2, hfr x (by simpa [cmpClob])]
        · intro h'; simp [St.setReg_apply] at h'
        · intro _; exact ⟨rfl, Or.inr ⟨by simp [St.setReg_apply], hno⟩⟩
      refine ach_caseTok_fail cmpTok failS _ τ hq1 hq2 ?_ ?_
      · intro t ht
        have hle := ht.le
        rw [Tok.bits_length] at hle
        by_cases h0 : t = .zero ∨ t = .one
        · -- a digit
          obtain ⟨d, hd⟩ : ∃ d, t = digitTok d := by
            rcases h0 with rfl | rfl
            · exact ⟨false, rfl⟩
            · exact ⟨true, rfl⟩
          have hct : cmpTok t = digitStep d := by
            subst hd; cases d <;> simp [cmpTok, digitTok]
          rw [hct]
          refine ach_digitStep d _ _ hB hTB ?_
          intro τ' h1 h2 h3 h4 h5 h6 h7
          refine ⟨w.length + 2 - (τ.pos + 5), by omega, ?_⟩
          have hgo' : τ'.reg rGo = τ.reg rGo := h3 _ (by decide)
          have hok' : τ'.reg rOk = τ.reg rOk := h3 _ (by decide)
          refine ⟨by simp [h2, ho], by simp [h1], by simp [h1]; omega, ?_, ?_, ?_⟩
          · intro x hx
            rw [h3 x (digitClob_sub x hx)]; exact hfr x hx
          · intro _
            refine ⟨by rw [hok', hok], by simp [h1], ds ++ [d], ?_, ?_,
              digInv_step v ds d τ τ' hdi h4 h5 h6 h7⟩
            · rw [List.map_append, At.toks_append]
              refine ⟨hds, ?_⟩
              rw [List.length_map, ← hpos]
              simpa [encodeToks, ← hd] using ht
            · simp [h1, hpos]; ring
          · intro h'; exact absurd (hgo'.symm.trans h') hg
        · by_cases hs : t = .sep
          · -- end of the number
            subst hs
            have hct : cmpTok Tok.sep = clear rGo := by simp [cmpTok]
            rw [hct]
            refine ach_clear _ _ _ ⟨0, by omega, ?_⟩
            refine ⟨by simp [ho], by simp, by simp; omega, ?_, ?_, ?_⟩
            · intro x hx
              simp only [cmpClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
              simp [St.setReg_apply, hx.2.2.2.2.2.2.1, hfr x (by simpa [cmpClob])]
            · intro h'; simp [St.setReg_apply] at h'
            · intro _
              refine ⟨rfl, Or.inl ⟨by simp [St.setReg_apply, hok], ds, ?_, by simp [hpos]; ring,
                ?_⟩⟩
              · unfold NumAt
                rw [At.toks_append]
                refine ⟨hds, ?_⟩
                rw [List.length_map, ← hpos]
                simpa [encodeToks] using ht
              · obtain ⟨d1, d2, d3, d4⟩ := hdi
                refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa [St.setReg_apply]
          · -- an unexpected token
            have hct : cmpTok t = failS := by
              simp only [not_or] at h0
              simp [cmpTok, h0.1, h0.2, hs]
            rw [hct]
            refine hfail _ (by omega) (by omega) ?_
            intro ds' hnum
            obtain ⟨u, hu, hAt⟩ := digits_next hds hnum
            rw [← hpos] at hAt
            have := At.tok_eq ht hAt
            subst this
            rcases hu with rfl | rfl | rfl <;> simp_all
      · intro p' h1 h2 hno
        refine hfail p' h1 h2 ?_
        intro ds' hnum
        obtain ⟨u, -, hAt⟩ := digits_next hds hnum
        rw [← hpos] at hAt
        exact hno u hAt
  · -- initial state
    refine ⟨by simp, by simpa using hp1, by simpa using hp2, ?_, ?_, ?_⟩
    · intro x hx
      simp only [cmpClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [St.setReg_apply, hx.1, hx.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1,
        hx.2.2.2.2.2.2.1]
    · intro _
      refine ⟨by simp [St.setReg_apply], rfl, [], by simpa [encodeToks] using At.nil hp1 hp2,
        by simp, ?_⟩
      refine ⟨by simp [St.setReg_apply, hv], by simp [St.setReg_apply, ofBits, Nat.mod_one],
        by simp [St.setReg_apply, ofBits, Nat.mod_one], by simp [St.setReg_apply, canon_nil]⟩
    · intro h'; simp [St.setReg_apply] at h'
  · -- after the loop
    rintro τ ⟨⟨ho, hq1, hq2, hfr, -, hstop⟩, hg⟩
    obtain ⟨-, hres⟩ := hstop hg
    refine ach_ite ?_
    rcases hres with ⟨hok, ds, hnum, hpos, hT, hlt, heq, hlast⟩ | ⟨hok, hno⟩
    · have hf := cmp_final v ds.length (ofBits ds) (ofBits_lt ds)
      by_cases hT0 : τ.reg rT = 0
      · rw [if_pos (by simp [Cond.eval, hT0])]
        refine ach_skip (h τ ho hq1 hq2 hfr (Or.inl ⟨ds, hnum, hpos, hok, ?_, ?_, hlast⟩))
        · rw [hlt, hf.1]; rw [hT] at hT0; simp [hT0]
        · rw [heq, hf.2]; rw [hT] at hT0; simp [hT0]
      · rw [if_neg (by simp [Cond.eval, hT0])]
        refine ach_seq (ach_setOne _ _ _ hB (ach_clear _ _ _ (h _ (by simp [ho]) (by simpa using hq1)
          (by simpa using hq2) ?_ (Or.inl ⟨ds, hnum, by simpa using hpos, ?_, ?_, ?_, ?_⟩))))
        · intro x hx
          simp only [cmpClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          simp [St.setReg_apply, hx.2.2.2.1, hx.2.2.2.2.1, hfr x (by simpa [cmpClob])]
        · simpa [St.setReg_apply] using hok
        · rw [hT] at hT0; simp only [St.setReg_apply, hf.1]; simp [hT0]
        · rw [hT] at hT0; simp only [St.setReg_apply, hf.2]; simp [hT0]
        · simpa [St.setReg_apply] using hlast
    · by_cases hT0 : τ.reg rT = 0
      · rw [if_pos (by simp [Cond.eval, hT0])]
        exact ach_skip (h τ ho hq1 hq2 hfr (Or.inr ⟨hok, hno⟩))
      · rw [if_neg (by simp [Cond.eval, hT0])]
        refine ach_seq (ach_setOne _ _ _ hB (ach_clear _ _ _ (h _ (by simp [ho]) (by simpa using hq1)
          (by simpa using hq2) ?_ (Or.inr ⟨by simpa [St.setReg_apply] using hok, hno⟩))))
        intro x hx
        simp only [cmpClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp [St.setReg_apply, hx.2.2.2.1, hx.2.2.2.2.1, hfr x (by simpa [cmpClob])]

end MCVPReduction

end PathChecking
