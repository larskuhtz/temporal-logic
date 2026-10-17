module

public import RequestProject.Logspace.IO

/-!
# Reading tokens from the input

`caseTok k bad` reads the 5-bit block under the input head; if it is the code of a token
`t`, the head ends up just after the block and `k t` is executed; otherwise (an end marker
is met or the block is not the code of a token) `bad` is executed.
-/

@[expose] public section

namespace PathChecking

namespace LS

open scoped LS

variable {K : ℕ} {w : Word} {B : ℕ}

/-- All tokens. -/
def allToks : List Tok := [.zero, .one, .sep, .lpar, .rpar] ++ (List.finRange 24).map Tok.tag

/-- Decoding a 5-bit block. -/
def decodeTok (bs : List Bool) : Option Tok := allToks.find? (fun t => decide (t.bits = bs))

lemma decodeTok_bits (t : Tok) : decodeTok t.bits = some t := by
  cases t with
  | tag k => revert k; decide
  | _ => decide

lemma bits_of_decodeTok {bs : List Bool} {t : Tok} (h : decodeTok bs = some t) : t.bits = bs := by
  unfold decodeTok at h
  have := List.find?_some h
  simpa using this

lemma Tok.bits_length (t : Tok) : t.bits.length = 5 := by simp [Tok.bits]

lemma encodeToks_length (ts : List Tok) : (encodeToks ts).length = 5 * ts.length := by
  induction ts with
  | nil => simp [encodeToks]
  | cons t ts ih => rw [encodeToks_cons, List.length_append, ih, Tok.bits_length]; simp; ring

/-- Read `n` more bits (`acc` holds the bits read so far, in reverse order). -/
def readBits (k : List Bool → Stmt K) (bad : Stmt K) : ℕ → List Bool → Stmt K
  | 0, acc => k acc.reverse
  | n + 1, acc => .ite (.sym (.bit false)) (.right ⨟ readBits k bad n (false :: acc))
      (.ite (.sym (.bit true)) (.right ⨟ readBits k bad n (true :: acc)) bad)

/-- Read a token and branch on it. -/
def caseTok (k : Tok → Stmt K) (bad : Stmt K) : Stmt K :=
  readBits (fun bs => match decodeTok bs with
    | some t => k t
    | none => bad) bad 5 []

lemma pos_lt_of_sym_bit {p : ℕ} {b : Bool} (h : inputSym w p = .bit b) : 1 ≤ p ∧ p ≤ w.length := by
  unfold inputSym at h
  split_ifs at h with h0
  split at h
  · rename_i b' hb
    rw [List.getElem?_eq_some_iff] at hb
    obtain ⟨hlt, -⟩ := hb
    exact ⟨by omega, by omega⟩
  · simp at h

lemma ach_readBits_pos (k : List Bool → Stmt K) (bad : Stmt K) (Q : St K → Prop) :
    ∀ n acc (σ : St K) (bs : List Bool), bs.length = n → At w σ.pos bs →
      Ach w B (k (acc.reverse ++ bs)) { σ with pos := σ.pos + n } Q →
      Ach w B (readBits k bad n acc) σ Q := by
  intro n
  induction n with
  | zero =>
    intro acc σ bs hl _ h
    rw [List.length_eq_zero_iff] at hl; subst hl
    simpa [readBits] using h
  | succ n ih =>
    intro acc σ bs hl hAt h
    obtain ⟨b, bs, rfl⟩ : ∃ b bs', bs = b :: bs' := by
      cases bs with
      | nil => simp at hl
      | cons b bs => exact ⟨b, bs, rfl⟩
    have hsym := hAt.sym
    have hp := pos_lt_of_sym_bit hsym
    have hnext : ∀ τ : St K, τ.pos = σ.pos → min (τ.pos + 1) (w.length + 1) = σ.pos + 1 := by
      intro τ hτ; rw [hτ]; omega
    have step : Ach w B (Stmt.right ⨟ readBits k bad n (b :: acc)) σ Q := by
      refine ach_seq (ach_right ?_)
      refine ih (b :: acc) _ bs (by simpa using hl) ?_ ?_
      · simpa [hnext σ rfl] using hAt.tail
      · simp only [hnext σ rfl]
        convert h using 2
        all_goals first | rfl | omega | simp
    cases b
    · exact ach_iteT (by simp [Cond.eval, hsym]) step
    · exact ach_iteF (by simp [Cond.eval, hsym]) (ach_iteT (by simp [Cond.eval, hsym]) step)

lemma ach_caseTok_pos (k : Tok → Stmt K) (bad : Stmt K) (Q : St K → Prop) (σ : St K) (t : Tok)
    (hAt : At w σ.pos t.bits) (h : Ach w B (k t) { σ with pos := σ.pos + 5 } Q) :
    Ach w B (caseTok k bad) σ Q := by
  refine ach_readBits_pos _ bad Q 5 [] σ t.bits (Tok.bits_length t) hAt ?_
  simpa [decodeTok_bits] using h

lemma ach_readBits_any (k : List Bool → Stmt K) (bad : Stmt K) (Q : St K → Prop) :
    ∀ n acc (σ : St K), 1 ≤ σ.pos → σ.pos ≤ w.length + 1 →
      (∀ bs : List Bool, bs.length = n → At w σ.pos bs →
        Ach w B (k (acc.reverse ++ bs)) { σ with pos := σ.pos + n } Q) →
      (∀ p, 1 ≤ p → p ≤ w.length + 1 → Ach w B bad { σ with pos := p } Q) →
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
      · intro p h1 h2; simpa using hbad p h1 h2
    refine ach_ite ?_
    by_cases h0 : inputSym w σ.pos = .bit false
    · rw [if_pos (by simp [Cond.eval, h0])]; exact step false h0
    · rw [if_neg (by simp [Cond.eval, h0])]
      refine ach_ite ?_
      by_cases h1 : inputSym w σ.pos = .bit true
      · rw [if_pos (by simp [Cond.eval, h1])]; exact step true h1
      · rw [if_neg (by simp [Cond.eval, h1])]
        simpa using hbad σ.pos hp1 hp2

/-- Reading a token from an arbitrary input: either a token `t` is present (and `k t` runs
after it), or `bad` runs (from some position on the tape). -/
lemma ach_caseTok_any (k : Tok → Stmt K) (bad : Stmt K) (Q : St K → Prop) (σ : St K)
    (hp1 : 1 ≤ σ.pos) (hp2 : σ.pos ≤ w.length + 1)
    (hk : ∀ t : Tok, At w σ.pos t.bits → Ach w B (k t) { σ with pos := σ.pos + 5 } Q)
    (hbad : ∀ p, 1 ≤ p → p ≤ w.length + 1 → Ach w B bad { σ with pos := p } Q) :
    Ach w B (caseTok k bad) σ Q := by
  refine ach_readBits_any _ bad Q 5 [] σ hp1 hp2 ?_ hbad
  intro bs hl hAt
  simp only [List.reverse_nil, List.nil_append]
  cases hd : decodeTok bs with
  | none =>
    simp only
    have := hAt.le
    simpa using hbad (σ.pos + 5) (by omega) (by omega)
  | some t =>
    simp only
    have := bits_of_decodeTok hd
    subst this
    exact hk t hAt

end LS

end PathChecking
