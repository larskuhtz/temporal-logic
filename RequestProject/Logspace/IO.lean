module

public import RequestProject.Logspace.Lib

/-!
# Verified program fragments for output and input

* emitting fixed bit strings / token lists, and the binary token encoding `natToks` of a
  register;
* moving the input head to the beginning / end of the input;
* reading a token (a 5-bit block) from the input and branching on it.
-/

@[expose] public section

namespace PathChecking

namespace LS

open scoped LS

variable {K : ℕ} {w : Word} {B : ℕ}

/-! ## Output -/

/-- Output a fixed bit string. -/
def emitBits : List Bool → Stmt K
  | [] => .skip
  | b :: bs => .out b ⨟ emitBits bs

lemma ach_emitBits (bs : List Bool) (σ : St K) (Q : St K → Prop)
    (h : Q { σ with out := σ.out ++ bs }) : Ach w B (emitBits bs) σ Q := by
  induction bs generalizing σ with
  | nil => exact ach_skip (by simpa using h)
  | cons b bs ih => exact ach_seq (ach_out (ih _ (by simpa using h)))

/-- Output a fixed list of tokens. -/
def emitToks (ts : List Tok) : Stmt K := emitBits (encodeToks ts)

lemma ach_emitToks (ts : List Tok) (σ : St K) (Q : St K → Prop)
    (h : Q { σ with out := σ.out ++ encodeToks ts }) : Ach w B (emitToks ts) σ Q :=
  ach_emitBits _ σ Q h

lemma encodeToks_append (ts us : List Tok) :
    encodeToks (ts ++ us) = encodeToks ts ++ encodeToks us := by
  simp [encodeToks]

lemma encodeToks_cons (t : Tok) (ts : List Tok) :
    encodeToks (t :: ts) = t.bits ++ encodeToks ts := by
  simp [encodeToks]

lemma Nat.bits_of_ne_zero' (n : ℕ) (h : n ≠ 0) :
    n.bits = (decide (n % 2 = 1)) :: (n / 2).bits := by
  have e : n = Nat.bit (decide (n % 2 = 1)) (n / 2) := by
    rw [Nat.bit_val]; by_cases h2 : n % 2 = 1 <;> simp [h2] <;> omega
  conv_lhs => rw [e]
  rw [Nat.bits_append_bit]
  intro h0; simp; omega

/-- The digit token of a bit. -/
def digitTok (b : Bool) : Tok := if b then .one else .zero

lemma natToks_eq (n : ℕ) : natToks n = (Nat.bits n).map digitTok ++ [.sep] := by
  simp [natToks, digitTok]

/-- Loop invariant of `emitNat`. -/
def emitNatInv (σ : St K) (t q b : Fin K) (v n : ℕ) (τ : St K) : Prop :=
  τ.reg t = n ∧ n ≤ v ∧ τ.pos = σ.pos ∧
      (∃ pre, τ.out = σ.out ++ encodeToks pre ∧ pre ++ (Nat.bits n).map digitTok =
        (Nat.bits v).map digitTok) ∧ (∀ x, x ≠ t → x ≠ q → x ≠ b → τ.reg x = σ.reg x)

/-- Output `natToks r` (the binary encoding of register `r`), using temporaries `t q b`. -/
def emitNat (r t q b : Fin K) : Stmt K :=
  copy r t q ⨟
  whileNZ t (halve t q b ⨟ .ite (.zero b) (emitToks [.zero]) (emitToks [.one]) ⨟ addTo q t) ⨟
  emitToks [.sep]

lemma ach_emitNat (r t q b : Fin K) (hrt : r ≠ t) (hrq : r ≠ q) (htq : t ≠ q)
    (htb : t ≠ b) (hqb : q ≠ b) (σ : St K) (Q : St K → Prop) (hB : σ.reg r ≤ B) (hB1 : 1 ≤ B)
    (h : ∀ σ' : St K, σ'.pos = σ.pos → σ'.out = σ.out ++ encodeToks (natToks (σ.reg r)) →
      (∀ x, x ≠ t → x ≠ q → x ≠ b → σ'.reg x = σ.reg x) → Q σ') :
    Ach w B (emitNat r t q b) σ Q := by
  set v := σ.reg r with hv
  refine ach_seq (ach_copy r t q hrt hrq htq σ _ hB ?_)
  refine ach_seq (ach_loop (emitNatInv σ t q b v) _ ?_ v _ ⟨by simp [St.setReg_apply, htq, v], le_rfl, rfl, ⟨[], by simp [encodeToks], by simp⟩,
      fun x h1 h2 h3 => by simp [St.setReg_apply, h1, h2]⟩)
  rintro n τ ⟨hn, hnv, hpos, ⟨pre, hout, hpre⟩, hfr⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · left
    refine ⟨by simp [Cond.eval, hn], ach_emitToks _ _ _ (h _ hpos ?_ hfr)⟩
    simp only [hout, List.append_assoc, natToks_eq, ← encodeToks_append]
    have : pre = (Nat.bits v).map digitTok := by simpa using hpre
    rw [this]
  · right
    refine ⟨by simp [Cond.eval, hn]; omega, ?_⟩
    refine ach_seq (ach_halve t q b htq htb hqb τ _ (by omega) hB1 (ach_seq (ach_ite ?_)))
    have hbits := Nat.bits_of_ne_zero' n (by omega)
    have key : ∀ τ' : St K, τ'.reg t = 0 → τ'.reg q = n / 2 → τ'.pos = σ.pos →
        τ'.out = σ.out ++ encodeToks (pre ++ [digitTok (decide (n % 2 = 1))]) →
        (∀ x, x ≠ t → x ≠ q → x ≠ b → τ'.reg x = σ.reg x) →
        Ach w B (addTo q t) τ' (fun σ' => ∃ m < n, emitNatInv σ t q b v m σ') := by
      intro τ' h1 h2 h3 h4 h5
      refine ach_addTo q t (Ne.symm htq) τ' _ (by omega) ⟨n / 2, by omega, ?_, by omega, by
        simp [h3], ⟨pre ++ [digitTok (decide (n % 2 = 1))], by simp [h4], ?_⟩, ?_⟩
      · simp [St.setReg_apply, h1, h2]
      · rw [List.append_assoc]; simpa [hbits] using hpre
      · intro x hx1 hx2 hx3
        simp [St.setReg_apply, hx1, hx2, h5 x hx1 hx2 hx3]
    by_cases hb : n % 2 = 0
    · rw [if_pos (by simp [Cond.eval, St.setReg_apply, hn, hb])]
      refine ach_emitToks _ _ _ (key _ (by simp [St.setReg_apply, htb, htq])
        (by simp [St.setReg_apply, hqb, hn]) (by simp [hpos]) ?_ ?_)
      · simp [hout, encodeToks_append, hb, digitTok]
      · intro x h1 h2 h3; simp [St.setReg_apply, h1, h2, h3, hfr x h1 h2 h3]
    · rw [if_neg (by simp [Cond.eval, St.setReg_apply, hn]; omega)]
      refine ach_emitToks _ _ _ (key _ (by simp [St.setReg_apply, htb, htq])
        (by simp [St.setReg_apply, hqb, hn]) (by simp [hpos]) ?_ ?_)
      · have : n % 2 = 1 := by omega
        simp [hout, encodeToks_append, this, digitTok]
      · intro x h1 h2 h3; simp [St.setReg_apply, h1, h2, h3, hfr x h1 h2 h3]

/-- Add a constant to a register. -/
def addConst (r : Fin K) : ℕ → Stmt K
  | 0 => .skip
  | c + 1 => .inc r ⨟ addConst r c

lemma ach_addConst (r : Fin K) (c : ℕ) (σ : St K) (Q : St K → Prop) (hB : σ.reg r + c ≤ B)
    (h : Q (σ.setReg r (σ.reg r + c))) : Ach w B (addConst r c) σ Q := by
  induction c generalizing σ with
  | zero => exact ach_skip (by convert h using 1; st_tac)
  | succ c ih =>
    refine ach_seq (ach_inc (by omega) (ih _ (by simp [St.setReg_apply]; omega) ?_))
    convert h using 1; st_tac

/-- `d := 4 r + c`, using temporaries `t₁ t₂`. -/
def mul4add (r d t₁ t₂ : Fin K) (c : ℕ) : Stmt K :=
  copy r t₁ t₂ ⨟ clear d ⨟ whileNZ t₁ (.dec t₁ ⨟ .inc d ⨟ .inc d ⨟ .inc d ⨟ .inc d) ⨟
  addConst d c

lemma ach_mul4add (r d t₁ t₂ : Fin K) (c : ℕ) (hr1 : r ≠ t₁) (hr2 : r ≠ t₂)
    (hd1 : d ≠ t₁) (h12 : t₁ ≠ t₂) (σ : St K) (Q : St K → Prop)
    (hB : 4 * σ.reg r + c ≤ B)
    (h : ∀ σ' : St K, σ'.pos = σ.pos → σ'.out = σ.out → σ'.reg d = 4 * σ.reg r + c →
      (∀ x, x ≠ d → x ≠ t₁ → x ≠ t₂ → σ'.reg x = σ.reg x) → Q σ') :
    Ach w B (mul4add r d t₁ t₂ c) σ Q := by
  set v := σ.reg r
  refine ach_seq (ach_copy r t₁ t₂ hr1 hr2 h12 σ _ (by omega) (ach_seq (ach_clear d _ _ ?_)))
  refine ach_seq (ach_loop (fun n τ => τ.reg t₁ = n ∧ τ.reg d = 4 * (v - n) ∧ n ≤ v ∧ τ.pos = σ.pos ∧
      τ.out = σ.out ∧ (∀ x, x ≠ d → x ≠ t₁ → x ≠ t₂ → τ.reg x = σ.reg x)) _ ?_ v _
    ⟨by simp [St.setReg_apply, Ne.symm hd1, h12, v], by simp [St.setReg_apply], le_rfl, rfl, rfl,
      fun x h1 h2 h3 => by simp [St.setReg_apply, h1, h2, h3]⟩)
  rintro n τ ⟨h1, h2, h3, h4, h5, h6⟩
  rcases n with _ | n
  · left
    refine ⟨by simp [Cond.eval, h1], ach_addConst d c τ _ (by omega) (h _ h4 h5 ?_ ?_)⟩
    · simp [St.setReg_apply, h2]
    · intro x hx1 hx2 hx3; simp [St.setReg_apply, hx1, h6 x hx1 hx2 hx3]
  · right
    refine ⟨by simp [Cond.eval, h1], ?_⟩
    refine ach_seq (ach_dec (ach_seq (ach_inc ?_ (ach_seq (ach_inc ?_ (ach_seq (ach_inc ?_
      (ach_inc ?_ ⟨n, by omega, ?_, ?_, by omega, h4, h5, ?_⟩))))))))
    all_goals simp [St.setReg_apply, hd1, Ne.symm hd1, h1, h2]
    all_goals try omega
    intro x hx1 hx2 hx3; simp [hx1, hx2, h6 x hx1 hx2 hx3]

/-! ## Input -/

/-- The bits `bs` occur on the input tape starting at position `p ≥ 1`. -/
def At (w : Word) (p : ℕ) (bs : List Bool) : Prop :=
  1 ≤ p ∧ p ≤ w.length + 1 ∧ bs <+: w.drop (p - 1)

lemma At.nil {p : ℕ} (hp : 1 ≤ p) (hp' : p ≤ w.length + 1) : At w p [] :=
  ⟨hp, hp', List.nil_prefix⟩

lemma At.sym {p : ℕ} {b : Bool} {bs : List Bool} (h : At w p (b :: bs)) :
    inputSym w p = .bit b := by
  obtain ⟨hp, -, l, hl⟩ := h
  have : w[p - 1]? = some b := by
    rw [← List.head?_drop, ← hl]; rfl
  simp [inputSym, show p ≠ 0 by omega, this]

lemma At.le {p : ℕ} {bs : List Bool} (h : At w p bs) : p + bs.length ≤ w.length + 1 := by
  obtain ⟨hp, hp', l, hl⟩ := h
  have := congrArg List.length hl
  simp at this; omega

lemma At.tail {p : ℕ} {b : Bool} {bs : List Bool} (h : At w p (b :: bs)) : At w (p + 1) bs := by
  have hle := h.le
  obtain ⟨hp, -, l, hl⟩ := h
  refine ⟨by omega, by simp at hle; omega, l, ?_⟩
  rw [show p + 1 - 1 = (p - 1) + 1 by omega, ← List.drop_drop, ← hl]; rfl

lemma At.cons {p : ℕ} {b : Bool} {bs : List Bool} (hp : 1 ≤ p)
    (h1 : _root_.PathChecking.inputSym w p = .bit b) (h2 : At w (p + 1) bs) :
    At w p (b :: bs) := by
  obtain ⟨-, -, l, hl⟩ := h2
  have hw : w[p - 1]? = some b := by
    simp only [inputSym, show p ≠ 0 by omega, if_false] at h1
    split at h1 <;> simp_all
  have hlt : p - 1 < w.length := by
    rw [List.getElem?_eq_some_iff] at hw; exact hw.1
  refine ⟨hp, by omega, l, ?_⟩
  rw [show p + 1 - 1 = (p - 1) + 1 by omega] at hl
  rw [List.drop_eq_getElem_cons hlt, ← hl]
  rw [List.getElem?_eq_some_iff] at hw
  simp [hw.2]

lemma At.append {p : ℕ} {bs cs : List Bool} :
    At w p (bs ++ cs) ↔ At w p bs ∧ At w (p + bs.length) cs := by
  induction bs generalizing p with
  | nil =>
    simp only [List.nil_append, List.length_nil, add_zero, iff_and_self]
    intro h; exact At.nil h.1 h.2.1
  | cons b bs ih =>
    constructor
    · intro h
      have h1 := h.sym
      have h2 := (ih.1 h.tail)
      exact ⟨At.cons h.1 h1 h2.1, by simpa [add_assoc, add_comm 1] using h2.2⟩
    · rintro ⟨h1, h2⟩
      exact At.cons h1.1 h1.sym (ih.2 ⟨h1.tail, by simpa [add_assoc, add_comm 1] using h2⟩)

lemma inputSym_eq_lend {p : ℕ} : inputSym w p = .lend ↔ p = 0 := by
  unfold inputSym; split_ifs with h
  · simp [h]
  · simp only [h, iff_false]; split <;> simp

lemma inputSym_eq_rend {p : ℕ} (hp : 1 ≤ p) (hp' : p ≤ w.length + 1) :
    inputSym w p = .rend ↔ p = w.length + 1 := by
  unfold inputSym; rw [if_neg (by omega)]
  constructor
  · intro h; split at h
    · simp at h
    · rename_i h'; rw [List.getElem?_eq_none_iff] at h'; omega
  · intro h; rw [List.getElem?_eq_none (by omega)]

/-- Move the input head to position `1` (the first input symbol). -/
def rewind : Stmt K := .loop (.not (.sym .lend)) .left ⨟ .right

lemma ach_rewind (σ : St K) (Q : St K → Prop) (h : Q { σ with pos := 1 }) :
    Ach w B rewind σ Q := by
  refine ach_seq (ach_loop (fun n τ => τ = { σ with pos := n }) _ ?_ σ.pos σ (by rfl))
  intro n τ hτ
  subst hτ
  rcases n with _ | n
  · left
    refine ⟨by simp [Cond.eval, inputSym_eq_lend], ach_right ?_⟩
    simpa using h
  · right
    refine ⟨by simp [Cond.eval, inputSym_eq_lend], ach_left ⟨n, by omega, by simp⟩⟩

/-- Move the input head to the right end marker. -/
def goEnd : Stmt K := .loop (.not (.sym .rend)) .right

lemma ach_goEnd (σ : St K) (Q : St K → Prop) (hpos : σ.pos ≤ w.length + 1)
    (h : Q { σ with pos := w.length + 1 }) : Ach w B goEnd σ Q := by
  refine ach_loop (fun n τ => τ = { σ with pos := w.length + 1 - n } ∧ n ≤ w.length + 1) _ ?_
    (w.length + 1 - σ.pos) σ ⟨by ext <;> simp; omega, by omega⟩
  rintro n τ ⟨hτ, hn⟩
  subst hτ
  rcases n with _ | n
  · left
    refine ⟨?_, by simpa using h⟩
    simp [Cond.eval, inputSym_eq_rend (w := w) (p := w.length + 1) (by omega) le_rfl]
  · right
    have hne : inputSym w (w.length - n) ≠ .rend := by
      rcases Nat.eq_zero_or_pos (w.length - n) with h0 | h0
      · rw [h0]; simp [inputSym]
      · rw [Ne, inputSym_eq_rend (by omega) (by omega)]; omega
    refine ⟨by simp [Cond.eval, hne], ach_right ⟨n, by omega, ?_, by omega⟩⟩
    ext <;> simp; omega

end LS

end PathChecking
