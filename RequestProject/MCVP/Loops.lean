module

public import RequestProject.MCVP.OutToks

/-!
# Program fragments for the output phase

Counting loops, skipping numbers and gates on a valid input, locating the `k`-th gate, and
emitting numbers `4k + c` and fixed item lists.
-/

@[expose] public section

namespace PathChecking

namespace MCVPReduction

open LS
open scoped LS

variable {w : Word} {B : ℕ}

/-! ## Counting loops -/

/-- `while r ≠ 0 do (r := r - 1; body)`. -/
def forDown (r : Fin 20) (body : Stmt 20) : Stmt 20 := whileNZ r (.dec r ⨟ body)

lemma ach_forDown (r : Fin 20) (body : Stmt 20) (P : ℕ → St 20 → Prop) (Q : St 20 → Prop)
    (m : ℕ) (σ : St 20) (hσ : P m σ) (hr : σ.reg r = m)
    (hstep : ∀ j, j < m → ∀ τ : St 20, P (j + 1) τ → τ.reg r = j + 1 →
      Ach w B body (τ.setReg r j) (fun τ' => τ'.reg r = j ∧ P j τ'))
    (hQ : ∀ τ : St 20, P 0 τ → τ.reg r = 0 → Q τ) : Ach w B (forDown r body) σ Q := by
  refine ach_loop (fun n τ => n ≤ m ∧ τ.reg r = n ∧ P n τ) Q ?_ m σ ⟨le_rfl, hr, hσ⟩
  rintro n τ ⟨hn, hrn, hP⟩
  rcases n with _ | j
  · left; exact ⟨by simp [Cond.eval, hrn], hQ τ hP hrn⟩
  · right
    refine ⟨by simp [Cond.eval, hrn], ach_seq (ach_dec ?_)⟩
    have := hstep j (by omega) τ hP hrn
    simp only [hrn, Nat.add_sub_cancel]
    exact this.mono (fun τ' ⟨h1, h2⟩ => ⟨j, by omega, by omega, h1, h2⟩)

/-- `while c ≠ 0 do (body; i := i + 1; c := c - 1)`. -/
def forUp (i c : Fin 20) (body : Stmt 20) : Stmt 20 := whileNZ c (body ⨟ .inc i ⨟ .dec c)

lemma ach_forUp (i c : Fin 20) (hic : i ≠ c) (body : Stmt 20) (P : ℕ → St 20 → Prop)
    (Q : St 20 → Prop) (m : ℕ) (σ : St 20) (hσ : P 0 σ) (hi : σ.reg i = 0) (hc : σ.reg c = m)
    (hmB : m ≤ B)
    (hstep : ∀ j, j < m → ∀ τ : St 20, P j τ → τ.reg i = j → τ.reg c = m - j →
      Ach w B body τ (fun τ' => τ'.reg i = j ∧ τ'.reg c = m - j ∧
        P (j + 1) ((τ'.setReg i (j + 1)).setReg c (m - j - 1))))
    (hQ : ∀ τ : St 20, P m τ → Q τ) : Ach w B (forUp i c body) σ Q := by
  refine ach_loop (fun n τ => n ≤ m ∧ τ.reg c = n ∧ τ.reg i = m - n ∧ P (m - n) τ) Q ?_ m σ
    ⟨le_rfl, hc, by simp [hi], by simpa using hσ⟩
  rintro n τ ⟨hn, hcn, hin, hP⟩
  rcases n with _ | n
  · left; exact ⟨by simp [Cond.eval, hcn], hQ τ (by simpa using hP)⟩
  · right
    refine ⟨by simp [Cond.eval, hcn], ach_seq ?_⟩
    have := hstep (m - (n + 1)) (by omega) τ hP hin (by omega)
    refine this.mono ?_
    rintro τ' ⟨h1, h2, h3⟩
    refine ach_seq (ach_inc (by omega) (ach_dec ⟨n, by omega, by omega, ?_, ?_, ?_⟩))
    · simp [St.setReg_apply, Ne.symm hic, h2]; omega
    · simp [St.setReg_apply, hic, Ne.symm hic, h1]; omega
    · convert h3 using 1
      · omega
      · ext x <;> simp [St.setReg_apply, h1, h2]
        split_ifs <;> omega

/-! ## Reading a valid input -/

lemma At.toks_drop {p j : ℕ} {ts : List Tok} (h : At w p (encodeToks ts)) (hj : j ≤ ts.length) :
    At w (p + 5 * j) (encodeToks (ts.drop j)) := by
  have := At.toks_append.1 (by rwa [List.take_append_drop] : At w p (encodeToks (ts.take j ++ ts.drop j)))
  rw [List.length_take, min_eq_left hj] at this
  exact this.2

/-- Skip a number. -/
def skipNum : Stmt 20 :=
  setOne rGo ⨟ whileNZ rGo (caseTok (fun t => if t = Tok.sep then clear rGo else .skip) (clear rGo))

lemma ach_skipNum (σ : St 20) (Q : St 20 → Prop) (i : ℕ) (hB : 1 ≤ B)
    (hAt : At w σ.pos (encodeToks (natToks i)))
    (h : ∀ τ : St 20, τ.pos = σ.pos + 5 * (natToks i).length → τ.out = σ.out →
      (∀ x, x ≠ rGo → τ.reg x = σ.reg x) → Q τ) :
    Ach w B skipNum σ Q := by
  set L := (Nat.bits i).length with hL
  have hlen : (natToks i).length = L + 1 := by simp [natToks, L]
  refine ach_seq (ach_setOne _ _ _ hB ?_)
  refine ach_loop (fun n τ => τ.out = σ.out ∧ (∀ x, x ≠ rGo → τ.reg x = σ.reg x) ∧
    ((τ.reg rGo ≠ 0 ∧ ∃ j ≤ L, τ.pos = σ.pos + 5 * j ∧ n = L + 1 - j) ∨
     (τ.reg rGo = 0 ∧ τ.pos = σ.pos + 5 * (L + 1) ∧ n = 0))) Q ?_ (L + 1) _
    ⟨rfl, fun x hx => by simp [St.setReg_apply, hx],
      Or.inl ⟨by simp [St.setReg_apply], 0, by omega, by simp, by simp⟩⟩
  rintro n τ ⟨ho, hfr, (⟨hg, j, hj, hpos, hn⟩ | ⟨hg, hpos, hn⟩)⟩
  · right
    refine ⟨by simp [Cond.eval, hg], ?_⟩
    have hd := At.toks_drop hAt (j := j) (by omega)
    rw [← hpos, natToks_eq, List.drop_append_of_le_length (by simp; omega), ← List.map_drop] at hd
    cases hds : (Nat.bits i).drop j with
    | nil =>
      have hjL : j = L := by
        have := List.drop_eq_nil_iff.1 hds; omega
      rw [hds] at hd
      simp only [List.map_nil, List.nil_append] at hd
      refine ach_caseTok_pos _ _ _ τ Tok.sep (by simpa [encodeToks] using hd) ?_
      simp only [if_true]
      refine ach_clear _ _ _ ⟨0, by omega, by simp [ho], fun x hx => ?_, Or.inr ⟨by simp [St.setReg_apply],
        by simp [hpos, hjL]; ring, rfl⟩⟩
      simp [St.setReg_apply, hx, hfr x hx]
    | cons d rest =>
      have hjL : j < L := by
        have : ((Nat.bits i).drop j).length = L - j := by simp [L]
        rw [hds] at this; simp at this; omega
      rw [hds] at hd
      have hd' := (At.toks_cons.1 (by simpa using hd)).1
      refine ach_caseTok_pos _ _ _ τ (digitTok d) hd' ?_
      rw [if_neg (digitTok_ne_sep d)]
      refine ach_skip ⟨L + 1 - (j + 1), by omega, by simp [ho], fun x hx => by simp [hfr x hx],
        Or.inl ⟨by simpa using hg, j + 1, by omega, by simp [hpos]; ring, rfl⟩⟩
  · left
    refine ⟨by simp [Cond.eval, hg], h τ (by rw [hpos, hlen]) ho hfr⟩

/-- Skip a gate. -/
def skipGate : Stmt 20 :=
  caseTok (fun t => if t = .tag 2 ∨ t = .tag 3 then skipNum ⨟ skipNum else .skip) .skip

lemma ach_skipGate (σ : St 20) (Q : St 20 → Prop) (G : MGate) (hB : 1 ≤ B)
    (hAt : At w σ.pos (encodeToks G.toks))
    (h : ∀ τ : St 20, τ.pos = σ.pos + 5 * G.toks.length → τ.out = σ.out →
      (∀ x, x ≠ rGo → τ.reg x = σ.reg x) → Q τ) :
    Ach w B skipGate σ Q := by
  cases G with
  | input b =>
    cases b
    · refine ach_caseTok_pos _ _ _ σ (.tag 0) (by simpa [MGate.toks, encodeToks] using hAt) ?_
      simp only [Tok.tag.injEq]
      exact ach_skip (h _ (by simp [MGate.toks]) rfl (fun _ _ => rfl))
    · refine ach_caseTok_pos _ _ _ σ (.tag 1) (by simpa [MGate.toks, encodeToks] using hAt) ?_
      simp only [Tok.tag.injEq]
      exact ach_skip (h _ (by simp [MGate.toks]) rfl (fun _ _ => rfl))
  | and i j =>
    have hc : At w σ.pos (encodeToks (MGate.toks (.and i j))) := hAt
    simp only [MGate.toks] at hc
    obtain ⟨h1, h2⟩ := At.toks_cons.1 hc
    refine ach_caseTok_pos _ _ _ σ _ h1 ?_
    have h3 := At.toks_append.1 h2
    refine ach_seq (ach_skipNum _ _ i hB h3.1 (fun τ hp ho hf => ach_skipNum _ _ j hB ?_ ?_))
    · rw [hp]; exact h3.2
    · intro τ' hp' ho' hf'
      refine h τ' ?_ (ho'.trans ho) (fun x hx => (hf' x hx).trans (hf x hx))
      rw [hp', hp]; simp [MGate.toks]; ring
  | or i j =>
    have hc : At w σ.pos (encodeToks (MGate.toks (.or i j))) := hAt
    simp only [MGate.toks] at hc
    obtain ⟨h1, h2⟩ := At.toks_cons.1 hc
    refine ach_caseTok_pos _ _ _ σ _ h1 ?_
    have h3 := At.toks_append.1 h2
    refine ach_seq (ach_skipNum _ _ i hB h3.1 (fun τ hp ho hf => ach_skipNum _ _ j hB ?_ ?_))
    · rw [hp]; exact h3.2
    · intro τ' hp' ho' hf'
      refine h τ' ?_ (ho'.trans ho) (fun x hx => (hf' x hx).trans (hf x hx))
      rw [hp', hp]; simp [MGate.toks]; ring

/-- Position of gate `j` in the encoding of `C`. -/
def gatePos (C : List MGate) (j : ℕ) : ℕ := 1 + 5 * ((C.take j).flatMap MGate.toks).length

lemma gate_at_index {C : List MGate} (hw : w = encodeCircuit C) {j : ℕ} (hj : j < C.length) :
    At w (gatePos C j) (encodeToks (gateAt C j).toks) := by
  have h := at_self w
  conv at h => rhs; rw [hw]
  rw [encodeCircuit, ← List.take_append_drop j C, List.drop_eq_getElem_cons hj] at h
  simp only [List.flatMap_append, List.flatMap_cons] at h
  have := (At.toks_append.1 (At.toks_append.1 h).2).1
  rw [gatePos]
  have e : gateAt C j = C[j] := by simp [gateAt, List.getElem?_eq_getElem hj]
  rw [e]; exact this

lemma gatePos_succ (C : List MGate) {j : ℕ} (hj : j < C.length) :
    gatePos C (j + 1) = gatePos C j + 5 * (gateAt C j).toks.length := by
  have e : gateAt C j = C[j] := by simp [gateAt, List.getElem?_eq_getElem hj]
  rw [gatePos, gatePos, List.take_add_one, List.getElem?_eq_getElem hj, e]
  simp only [Option.toList_some, List.flatMap_append, List.flatMap_singleton, List.length_append]
  ring

lemma gatePos_le {C : List MGate} (hw : w = encodeCircuit C) {j : ℕ} :
    gatePos C j ≤ w.length + 1 := by
  have : ((C.take j).flatMap MGate.toks).length ≤ (C.flatMap MGate.toks).length := by
    have := congrArg (fun l => (l.flatMap MGate.toks).length) (List.take_append_drop j C)
    simp only [List.flatMap_append, List.length_append] at this
    omega
  rw [gatePos, hw, encodeCircuit_length]; omega

/-- Move the head to the beginning of gate number `r`. -/
def locate (r : Fin 20) : Stmt 20 :=
  rewind ⨟ copy r rLoc rTmp ⨟ whileNZ rLoc (skipGate ⨟ .dec rLoc)

/-- Registers modified by `locate`. -/
def locClob : List (Fin 20) := [rLoc, rTmp, rGo]

lemma ach_locate (r : Fin 20) (hr : r ∉ locClob) {C : List MGate} (hw : w = encodeCircuit C)
    (σ : St 20) (Q : St 20 → Prop) (hk : σ.reg r ≤ C.length) (hB : w.length + 1 ≤ B)
    (h : ∀ τ : St 20, τ.pos = gatePos C (σ.reg r) → τ.out = σ.out →
      (∀ x, x ∉ locClob → τ.reg x = σ.reg x) → Q τ) :
    Ach w B (locate r) σ Q := by
  simp only [locClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  set k := σ.reg r with hkdef
  have hCw : C.length ≤ w.length := by
    have := length_le_toks C
    have := encodeCircuit_length C
    rw [← hw] at this; omega
  unfold locate
  refine ach_seq (ach_rewind _ _ (ach_seq (ach_copy r rLoc rTmp hr.1 hr.2.1 (by decide) _ _
    (by simp; omega) ?_)))
  refine ach_loop (fun n τ => n ≤ k ∧ τ.reg rLoc = n ∧ τ.pos = gatePos C (k - n) ∧
    τ.out = σ.out ∧ ∀ x, x ∉ locClob → τ.reg x = σ.reg x) Q ?_ k _
    ⟨le_rfl, by simp [St.setReg_apply, hkdef], by simp [gatePos], by simp, ?_⟩
  · rintro n τ ⟨hn, hl, hp, ho, hf⟩
    rcases n with _ | n
    · left; exact ⟨by simp [Cond.eval, hl], h τ (by simpa using hp) ho hf⟩
    · right
      refine ⟨by simp [Cond.eval, hl], ?_⟩
      have hj : k - (n + 1) < C.length := by omega
      refine ach_seq (ach_skipGate τ _ _ (by omega) (by rw [hp]; exact gate_at_index hw hj) ?_)
      intro τ' hp' ho' hf'
      refine ach_dec ⟨n, by omega, by omega, ?_, ?_, by simpa using ho'.trans ho, ?_⟩
      · simp [St.setReg_apply, hf' rLoc (by decide), hl]
      · simp only [St.setReg_pos]
        rw [hp', hp, ← gatePos_succ C hj]; congr 1; omega
      · intro x hx
        simp only [locClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp [St.setReg_apply, hx.1, hf' x hx.2.2, hf x (by simp [locClob, hx.1, hx.2.1, hx.2.2])]
  · intro x hx
    simp only [locClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [St.setReg_apply, hx.1, hx.2.1]

/-! ## Emitting numbers and items -/

/-- Emit `natToks (4 * src + c)`. -/
def emitNum (src : Fin 20) (c : ℕ) : Stmt 20 :=
  mul4add src rV rT2 rTmp c ⨟ emitNat rV rE1 rE2 rB

/-- Registers modified by `emitNum`. -/
def numClob : List (Fin 20) := [rV, rT2, rTmp, rE1, rE2, rB]

lemma ach_emitNum (src : Fin 20) (hsrc : src ∉ numClob) (c : ℕ) (σ : St 20) (Q : St 20 → Prop)
    (hB : 4 * σ.reg src + c ≤ B) (hB1 : 1 ≤ B)
    (h : ∀ τ : St 20, τ.pos = σ.pos → τ.out = σ.out ++ encodeToks (natToks (4 * σ.reg src + c)) →
      (∀ x, x ∉ numClob → τ.reg x = σ.reg x) → Q τ) :
    Ach w B (emitNum src c) σ Q := by
  simp only [numClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hsrc
  unfold emitNum
  refine ach_seq (ach_mul4add src rV rT2 rTmp c hsrc.2.1 hsrc.2.2.1 (by decide)
    (by decide) σ _ hB ?_)
  intro τ hp ho hv hf
  refine ach_emitNat rV rE1 rE2 rB (by decide) (by decide) (by decide) (by decide)
    (by decide) τ _ (by omega) hB1 ?_
  intro τ' hp' ho' hf'
  refine h τ' (hp'.trans hp) (by rw [ho', ho, hv]) ?_
  intro x hx
  simp only [numClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  rw [hf' x hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2, hf x hx.1 hx.2.1 hx.2.2.1]

/-- Emit a list of items (numbers relative to register `src`). -/
def emitItems (src : Fin 20) : List Item → Stmt 20
  | [] => .skip
  | .lit t :: is => emitToks [t] ⨟ emitItems src is
  | .num c :: is => emitNum src c ⨟ emitItems src is

lemma ach_emitItems (src : Fin 20) (hsrc : src ∉ numClob) (items : List Item) (σ : St 20)
    (Q : St 20 → Prop) (hB : 4 * σ.reg src + 3 ≤ B) (hB1 : 1 ≤ B)
    (hc : ∀ c, Item.num c ∈ items → c ≤ 3)
    (h : ∀ τ : St 20, τ.pos = σ.pos →
      τ.out = σ.out ++ encodeToks (items.flatMap (Item.toks (σ.reg src))) →
      (∀ x, x ∉ numClob → τ.reg x = σ.reg x) → Q τ) :
    Ach w B (emitItems src items) σ Q := by
  induction items generalizing σ with
  | nil => exact ach_skip (h σ rfl (by simp [encodeToks]) (fun _ _ => rfl))
  | cons it items ih =>
    cases it with
    | lit t =>
      refine ach_seq (ach_emitToks _ _ _ (ih _ (by simpa using hB)
        (fun c hc' => hc c (by simp [hc'])) ?_))
      intro τ hp ho hf
      refine h τ (by simpa using hp) ?_ hf
      rw [ho]; simp [Item.toks, encodeToks]
    | num c =>
      have hc3 := hc c (by simp)
      refine ach_seq (ach_emitNum src hsrc c σ _ (by omega) hB1 ?_)
      intro τ hp ho hf
      have hsrc' : τ.reg src = σ.reg src := hf src hsrc
      refine ih τ (by omega) (fun c hc' => hc c (by simp [hc'])) ?_
      intro τ' hp' ho' hf'
      refine h τ' (hp'.trans hp) ?_ (fun x hx => (hf' x hx).trans (hf x hx))
      rw [ho', ho, hsrc']; simp [Item.toks, encodeToks_append]

end MCVPReduction

end PathChecking
