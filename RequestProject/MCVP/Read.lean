module

public import RequestProject.MCVP.Defs

/-!
# Reading the input: tokens and binary numbers

* `ach_caseTok_fail`: reading a token from an arbitrary input; if the "bad" branch is taken,
  then no token is present at the current position;
* compatibility of token strings found at the same input position;
* the register file of the reduction program;
* `cmpNum y`: read a binary number `ds` (digits followed by `sep`) from the input and compare
  it with register `y`; on malformed input the `ok` register is cleared.
-/

@[expose] public section

namespace PathChecking

namespace MCVPReduction

open LS
open scoped LS

variable {w : Word} {B : ℕ}

/-! ## Reading tokens -/

section Generic

variable {K : ℕ}

lemma ach_readBits_fail (k : List Bool → Stmt K) (bad : Stmt K) (Q : St K → Prop) :
    ∀ n acc (σ : St K), 1 ≤ σ.pos → σ.pos ≤ w.length + 1 →
      (∀ bs : List Bool, bs.length = n → At w σ.pos bs →
        Ach w B (k (acc.reverse ++ bs)) { σ with pos := σ.pos + n } Q) →
      (∀ p, 1 ≤ p → p ≤ w.length + 1 → (∀ bs : List Bool, bs.length = n → ¬ At w σ.pos bs) →
        Ach w B bad { σ with pos := p } Q) →
      Ach w B (readBits k bad n acc) σ Q := by
  intro n
  induction n with
  | zero =>
    intro acc σ hp1 hp2 hk _
    simpa [readBits] using hk [] rfl (At.nil hp1 hp2)
  | succ n ih =>
    intro acc σ hp1 hp2 hk hbad
    have step : ∀ b, inputSym w σ.pos = .bit b →
        Ach w B (Stmt.right ⨟ readBits k bad n (b :: acc)) σ Q := by
      intro b hsym
      have hp := pos_lt_of_sym_bit hsym
      refine ach_seq (ach_right ?_)
      have e : min (σ.pos + 1) (w.length + 1) = σ.pos + 1 := by omega
      refine ih (b :: acc) _ (by simp [e]) (by simp [e]; omega) ?_ ?_
      · intro bs hl hAt
        simp only [e] at hAt ⊢
        have := hk (b :: bs) (by simp [hl]) (At.cons hp1 hsym hAt)
        convert this using 2
        all_goals first | rfl | omega | simp
      · intro p h1 h2 hno
        have hno' : ∀ bs : List Bool, bs.length = n + 1 → ¬ At w σ.pos bs := by
          intro bs hl hAt
          obtain ⟨b', bs', rfl⟩ : ∃ b' bs', bs = b' :: bs' := by
            cases bs with
            | nil => simp at hl
            | cons b' bs' => exact ⟨b', bs', rfl⟩
          have h1 := hAt.sym
          rw [hsym] at h1
          cases h1
          exact hno bs' (by simpa using hl) (by simpa [e] using hAt.tail)
        simpa using hbad p h1 h2 hno'
    have hnone : (∀ b, inputSym w σ.pos ≠ .bit b) →
        ∀ bs : List Bool, bs.length = n + 1 → ¬ At w σ.pos bs := by
      intro hne bs hl hAt
      cases bs with
      | nil => simp at hl
      | cons b bs => exact hne b hAt.sym
    refine ach_ite ?_
    by_cases h0 : inputSym w σ.pos = .bit false
    · rw [if_pos (by simp [Cond.eval, h0])]; exact step false h0
    · rw [if_neg (by simp [Cond.eval, h0])]
      refine ach_ite ?_
      by_cases h1 : inputSym w σ.pos = .bit true
      · rw [if_pos (by simp [Cond.eval, h1])]; exact step true h1
      · rw [if_neg (by simp [Cond.eval, h1])]
        have hne : ∀ b, inputSym w σ.pos ≠ .bit b := by intro b; cases b <;> assumption
        simpa using hbad σ.pos hp1 hp2 (hnone hne)

lemma At.eq_of_length {p : ℕ} {xs ys : List Bool} (h1 : At w p xs) (h2 : At w p ys)
    (hl : xs.length = ys.length) : xs = ys := by
  have := List.prefix_of_prefix_length_le h1.2.2 h2.2.2 hl.le
  exact this.eq_of_length hl

/-- Reading a token from an arbitrary input; the bad branch is only taken if no token is
present at the current position. -/
lemma ach_caseTok_fail (k : Tok → Stmt K) (bad : Stmt K) (Q : St K → Prop) (σ : St K)
    (hp1 : 1 ≤ σ.pos) (hp2 : σ.pos ≤ w.length + 1)
    (hk : ∀ t : Tok, At w σ.pos t.bits → Ach w B (k t) { σ with pos := σ.pos + 5 } Q)
    (hbad : ∀ p, 1 ≤ p → p ≤ w.length + 1 → (∀ t : Tok, ¬ At w σ.pos t.bits) →
      Ach w B bad { σ with pos := p } Q) :
    Ach w B (caseTok k bad) σ Q := by
  refine ach_readBits_fail _ bad Q 5 [] σ hp1 hp2 ?_ ?_
  · intro bs hl hAt
    simp only [List.reverse_nil, List.nil_append]
    cases hd : decodeTok bs with
    | none =>
      simp only
      have := hAt.le
      have hno : ∀ t : Tok, ¬ At w σ.pos t.bits := by
        intro t ht
        have e := At.eq_of_length ht hAt (by rw [Tok.bits_length, hl])
        rw [← e, decodeTok_bits] at hd
        simp at hd
      simpa using hbad (σ.pos + 5) (by omega) (by omega) hno
    | some t =>
      simp only
      have := bits_of_decodeTok hd
      subst this
      exact hk t hAt
  · intro p h1 h2 hno
    exact hbad p h1 h2 (fun t ht => hno t.bits (Tok.bits_length t) ht)

/-- Two strings found at the same position are comparable. -/
lemma At.prefix_or {p : ℕ} {xs ys : List Bool} (h1 : At w p xs) (h2 : At w p ys) :
    xs <+: ys ∨ ys <+: xs := by
  rcases le_total xs.length ys.length with h | h
  · exact Or.inl (List.prefix_of_prefix_length_le h1.2.2 h2.2.2 h)
  · exact Or.inr (List.prefix_of_prefix_length_le h2.2.2 h1.2.2 h)

/-- Two token strings found at the same position are comparable. -/
lemma At.toks_compat {p : ℕ} {ts us : List Tok} (h1 : At w p (encodeToks ts))
    (h2 : At w p (encodeToks us)) : (∃ vs, us = ts ++ vs) ∨ (∃ vs, ts = us ++ vs) := by
  rcases le_total ts.length us.length with hl | hl
  · left
    rcases At.prefix_or h1 h2 with ⟨z, hz⟩ | ⟨z, hz⟩
    · obtain ⟨vs, hvs, -⟩ := encodeToks_append_eq (y := []) hl (by simpa using hz)
      exact ⟨vs, hvs⟩
    · have := congrArg List.length hz
      simp only [List.length_append, encodeToks_length] at this
      have hz0 : z.length = 0 := by omega
      rw [List.length_eq_zero_iff] at hz0; subst hz0
      obtain ⟨vs, hvs, -⟩ := encodeToks_append_eq (x := []) (y := []) hl (by simpa using hz.symm)
      exact ⟨vs, hvs⟩
  · right
    rcases At.prefix_or h2 h1 with ⟨z, hz⟩ | ⟨z, hz⟩
    · obtain ⟨vs, hvs, -⟩ := encodeToks_append_eq (y := []) hl (by simpa using hz)
      exact ⟨vs, hvs⟩
    · have := congrArg List.length hz
      simp only [List.length_append, encodeToks_length] at this
      have hz0 : z.length = 0 := by omega
      rw [List.length_eq_zero_iff] at hz0; subst hz0
      obtain ⟨vs, hvs, -⟩ := encodeToks_append_eq (x := []) (y := []) hl (by simpa using hz.symm)
      exact ⟨vs, hvs⟩

lemma At.toks_append {p : ℕ} {ts us : List Tok} :
    At w p (encodeToks (ts ++ us)) ↔ At w p (encodeToks ts) ∧
      At w (p + 5 * ts.length) (encodeToks us) := by
  rw [encodeToks_append, At.append, encodeToks_length]

lemma At.tok_eq {p : ℕ} {t u : Tok} (h1 : At w p t.bits) (h2 : At w p u.bits) : t = u :=
  Tok.bits_injective (At.eq_of_length h1 h2 (by simp [Tok.bits_length]))

lemma At.toks_cons {p : ℕ} {t : Tok} {ts : List Tok} :
    At w p (encodeToks (t :: ts)) ↔ At w p t.bits ∧ At w (p + 5) (encodeToks ts) := by
  rw [encodeToks_cons, At.append, Tok.bits_length]

/-- If a string of tokens is found at `p` and is longer than `ts` (also found at `p`), then
some token in it is found right after `ts`. -/
lemma At.next_tok {p : ℕ} {ts us : List Tok} (h1 : At w p (encodeToks ts))
    (h2 : At w p (encodeToks us)) (hlt : ts.length < us.length) :
    ∃ v ∈ us, At w (p + 5 * ts.length) v.bits := by
  rcases At.toks_compat h1 h2 with ⟨vs, rfl⟩ | ⟨vs, rfl⟩
  · cases vs with
    | nil => simp at hlt
    | cons v vs =>
      refine ⟨v, by simp, ?_⟩
      have := (At.toks_append.1 h2).2
      exact (At.toks_cons.1 this).1
  · simp at hlt

end Generic

/-! ## Binary numbers -/

lemma ofBits_append_single (ds : List Bool) (d : Bool) :
    ofBits (ds ++ [d]) = ofBits ds + 2 ^ ds.length * d.toNat := by
  induction ds with
  | nil => simp [ofBits]
  | cons b ds ih => simp [ofBits, ih, pow_succ]; ring

lemma ofBits_lt (ds : List Bool) : ofBits ds < 2 ^ ds.length := by
  induction ds with
  | nil => simp [ofBits]
  | cons b ds ih => simp only [ofBits, List.length_cons, pow_succ]; cases b <;> simp <;> omega

lemma canon_nil : Canon [] := Or.inl rfl

lemma canon_append_single (ds : List Bool) (d : Bool) : Canon (ds ++ [d]) ↔ d = true := by
  simp [Canon]

/-- One step of the least-significant-first comparison of a number with `y`. -/
lemma cmp_step (y n a : ℕ) (ha : a < 2 ^ n) (d : Bool) :
    (a + 2 ^ n * d.toNat < y % 2 ^ (n + 1) ↔
      (d.toNat < y / 2 ^ n % 2 ∨ (d.toNat = y / 2 ^ n % 2 ∧ a < y % 2 ^ n))) ∧
    (a + 2 ^ n * d.toNat = y % 2 ^ (n + 1) ↔ (d.toNat = y / 2 ^ n % 2 ∧ a = y % 2 ^ n)) := by
  rw [pow_succ, Nat.mod_mul]
  have h1 : y % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  have h2 : y / 2 ^ n % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize 2 ^ n = P at *
  generalize y / P % 2 = b at *
  generalize y % P = c at *
  interval_cases b <;> cases d <;> simp only [Bool.toNat_true, Bool.toNat_false]
  all_goals constructor <;> constructor <;> intro h <;> simp only [true_and, mul_zero, mul_one,
    add_zero] at h ⊢ <;> omega

/-- The final comparison. -/
lemma cmp_final (y n a : ℕ) (ha : a < 2 ^ n) :
    (a < y ↔ (y / 2 ^ n ≠ 0 ∨ a < y % 2 ^ n)) ∧ (a = y ↔ (y / 2 ^ n = 0 ∧ a = y % 2 ^ n)) := by
  have e := Nat.div_add_mod y (2 ^ n)
  have h1 : y % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  generalize 2 ^ n = P at *
  generalize y / P = q at *
  generalize y % P = c at *
  subst e
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have : P ≤ P * q := Nat.le_mul_of_pos_right P hq
    constructor <;> constructor <;> intro h <;> omega

end MCVPReduction

end PathChecking
