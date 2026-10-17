module

public import RequestProject.CTLStarP.TreePos
public import RequestProject.LTLPath.Tree

/-!
# The formula tree of an encoded LTL formula

For a token list `ts` containing the encoding of an LTL formula `φ` at position `1`, the
positional tree (`PT`) of `φ` is given by token-level functions: nodes are the positions of tag
tokens in `[1, F)` with `F = fend 1`, the kind of a node is its tag, and `fe = fend`.

Main results: unique parsing (`at_unique`), every tag position of the formula starts a
subformula (`tag_sub`), and the positional tree `tokPT` of a valid input.
-/

@[expose] public section

namespace PathChecking

open CTLP

/-- LTL formulas as CTL* formulas (same tokens). -/
def LTL.toC : LTL → CTLStar
  | .ap a => .ap a
  | .tt => .tt
  | .neg φ => .neg φ.toC
  | .and φ ψ => .and φ.toC ψ.toC
  | .X φ => .X φ.toC
  | .U φ ψ => .U φ.toC ψ.toC

lemma LTL.toks_toC (φ : LTL) : φ.toC.toks = φ.toks := by
  induction φ <;> simp_all [LTL.toC, CTLStar.toks, LTL.toks]

/-- The tag of the top operator. -/
def LTL.tag : LTL → ℕ
  | .ap _ => 0
  | .tt => 1
  | .neg _ => 2
  | .and _ _ => 3
  | .X _ => 4
  | .U _ _ => 5

lemma LTL.toks_pos (φ : LTL) : 1 ≤ φ.toks.length := by cases φ <;> simp [LTL.toks]

namespace LTok

variable {ts : List Tok}

/-- The formula `φ` is encoded at position `p`. -/
def At (ts : List Tok) (p : ℕ) (φ : LTL) : Prop := ∃ rest, ts.drop p = φ.toks ++ rest

lemma fend_at {p : ℕ} {φ : LTL} (h : At ts p φ) : fend ts p = p + φ.toks.length := by
  obtain ⟨rest, h⟩ := h
  rw [← LTL.toks_toC] at h ⊢
  exact fend_formula _ h

lemma tc_at {p : ℕ} {φ : LTL} (h : At ts p φ) : tc ts p = 5 + φ.tag := by
  obtain ⟨rest, h⟩ := h
  cases φ <;> simp only [LTL.toks, List.cons_append] at h <;> rw [tc_of_drop h] <;> rfl

lemma natToks_code (a : ℕ) : ∀ t ∈ natToks a, t.code ≤ 2 := by
  intro t ht
  simp only [natToks, List.mem_append, List.mem_map, List.mem_singleton] at ht
  rcases ht with ⟨b, -, rfl⟩ | rfl
  · cases b <;> simp [Tok.code]
  · simp [Tok.code]

lemma tc_le_two_of_natToks {p a : ℕ} {rest : List Tok} (h : ts.drop p = natToks a ++ rest)
    {q : ℕ} (hq1 : p ≤ q) (hq2 : q < p + (natToks a).length) : tc ts q ≤ 2 := by
  have : ts.drop q = (natToks a).drop (q - p) ++ rest := by
    rw [show q = p + (q - p) by omega, ← List.drop_drop, h, List.drop_append_of_le_length (by omega)]
    simp
  obtain ⟨t, l, htl⟩ : ∃ t l, (natToks a).drop (q - p) = t :: l := by
    cases e : (natToks a).drop (q - p) with
    | nil => simp at e; omega
    | cons t l => exact ⟨t, l, rfl⟩
  rw [htl, List.cons_append] at this
  rw [tc_of_drop this]
  exact natToks_code a t (List.mem_of_mem_drop (by rw [htl]; simp))

/-- **Unique parsing.** -/
theorem at_unique : ∀ (φ ψ : LTL) {p : ℕ}, At ts p φ → At ts p ψ → φ = ψ := by
  intro φ
  induction φ with
  | ap a =>
    intro ψ p h1 h2
    have t1 := tc_at h1; have t2 := tc_at h2
    cases ψ <;> simp only [LTL.tag] at t1 t2 <;> try omega
    case ap b =>
      obtain ⟨r1, h1⟩ := h1; obtain ⟨r2, h2⟩ := h2
      simp only [LTL.toks, List.cons_append] at h1 h2
      rw [natToks_unique (drop_succ_of_drop h1) (drop_succ_of_drop h2)]
  | tt =>
    intro ψ p h1 h2
    have t1 := tc_at h1; have t2 := tc_at h2
    cases ψ <;> simp only [LTL.tag] at t1 t2 <;> first | omega | rfl
  | neg φ ih =>
    intro ψ p h1 h2
    have t1 := tc_at h1; have t2 := tc_at h2
    cases ψ <;> simp only [LTL.tag] at t1 t2 <;> try omega
    case neg ψ =>
      obtain ⟨r1, h1⟩ := h1; obtain ⟨r2, h2⟩ := h2
      simp only [LTL.toks, List.cons_append] at h1 h2
      rw [ih ψ ⟨_, drop_succ_of_drop h1⟩ ⟨_, drop_succ_of_drop h2⟩]
  | X φ ih =>
    intro ψ p h1 h2
    have t1 := tc_at h1; have t2 := tc_at h2
    cases ψ <;> simp only [LTL.tag] at t1 t2 <;> try omega
    case X ψ =>
      obtain ⟨r1, h1⟩ := h1; obtain ⟨r2, h2⟩ := h2
      simp only [LTL.toks, List.cons_append] at h1 h2
      rw [ih ψ ⟨_, drop_succ_of_drop h1⟩ ⟨_, drop_succ_of_drop h2⟩]
  | and φ1 φ2 ih1 ih2 =>
    intro ψ p h1 h2
    have t1 := tc_at h1; have t2 := tc_at h2
    cases ψ <;> simp only [LTL.tag] at t1 t2 <;> try omega
    case and ψ1 ψ2 =>
      obtain ⟨r1, h1⟩ := h1; obtain ⟨r2, h2⟩ := h2
      simp only [LTL.toks, List.cons_append, List.append_assoc] at h1 h2
      have e1 := ih1 ψ1 ⟨_, drop_succ_of_drop h1⟩ ⟨_, drop_succ_of_drop h2⟩
      subst e1
      rw [ih2 ψ2 ⟨_, drop_append_of_drop (drop_succ_of_drop h1)⟩
        ⟨_, drop_append_of_drop (drop_succ_of_drop h2)⟩]
  | U φ1 φ2 ih1 ih2 =>
    intro ψ p h1 h2
    have t1 := tc_at h1; have t2 := tc_at h2
    cases ψ <;> simp only [LTL.tag] at t1 t2 <;> try omega
    case U ψ1 ψ2 =>
      obtain ⟨r1, h1⟩ := h1; obtain ⟨r2, h2⟩ := h2
      simp only [LTL.toks, List.cons_append, List.append_assoc] at h1 h2
      have e1 := ih1 ψ1 ⟨_, drop_succ_of_drop h1⟩ ⟨_, drop_succ_of_drop h2⟩
      subst e1
      rw [ih2 ψ2 ⟨_, drop_append_of_drop (drop_succ_of_drop h1)⟩
        ⟨_, drop_append_of_drop (drop_succ_of_drop h2)⟩]

/-- **Every tag position of an encoded formula starts a subformula.** -/
theorem tag_sub : ∀ (φ : LTL) {q : ℕ}, At ts q φ → ∀ p, q ≤ p → p < q + φ.toks.length →
    tc ts p ≤ 2 ∨ ∃ ψ, At ts p ψ ∧ p + ψ.toks.length ≤ q + φ.toks.length := by
  intro φ
  induction φ with
  | ap a =>
    intro q h p h1 h2
    by_cases e : p = q
    · subst e; exact Or.inr ⟨_, h, le_rfl⟩
    left
    obtain ⟨r, h⟩ := h
    simp only [LTL.toks, List.cons_append, List.length_cons] at h h2
    exact tc_le_two_of_natToks (drop_succ_of_drop h) (by omega) (by omega)
  | tt =>
    intro q h p h1 h2
    simp only [LTL.toks, List.length_singleton] at h2
    exact Or.inr ⟨_, show p = q by omega ▸ h, by simp [LTL.toks]; omega⟩
  | neg φ ih =>
    intro q h p h1 h2
    by_cases e : p = q
    · subst e; exact Or.inr ⟨_, h, le_rfl⟩
    obtain ⟨r, h'⟩ := h
    simp only [LTL.toks, List.cons_append, List.length_cons] at h' h2 ⊢
    rcases ih ⟨_, drop_succ_of_drop h'⟩ p (by omega) (by omega) with h3 | ⟨ψ, h3, h4⟩
    · exact Or.inl h3
    · exact Or.inr ⟨ψ, h3, by omega⟩
  | X φ ih =>
    intro q h p h1 h2
    by_cases e : p = q
    · subst e; exact Or.inr ⟨_, h, le_rfl⟩
    obtain ⟨r, h'⟩ := h
    simp only [LTL.toks, List.cons_append, List.length_cons] at h' h2 ⊢
    rcases ih ⟨_, drop_succ_of_drop h'⟩ p (by omega) (by omega) with h3 | ⟨ψ, h3, h4⟩
    · exact Or.inl h3
    · exact Or.inr ⟨ψ, h3, by omega⟩
  | and φ1 φ2 ih1 ih2 =>
    intro q h p h1 h2
    by_cases e : p = q
    · subst e; exact Or.inr ⟨_, h, le_rfl⟩
    obtain ⟨r, h'⟩ := h
    simp only [LTL.toks, List.cons_append, List.length_cons, List.length_append,
      List.append_assoc] at h' h2 ⊢
    by_cases hp : p < q + 1 + φ1.toks.length
    · rcases ih1 ⟨_, drop_succ_of_drop h'⟩ p (by omega) hp with h3 | ⟨ψ, h3, h4⟩
      · exact Or.inl h3
      · exact Or.inr ⟨ψ, h3, by omega⟩
    · rcases ih2 ⟨_, drop_append_of_drop (drop_succ_of_drop h')⟩ p (by omega) (by omega) with
        h3 | ⟨ψ, h3, h4⟩
      · exact Or.inl h3
      · exact Or.inr ⟨ψ, h3, by omega⟩
  | U φ1 φ2 ih1 ih2 =>
    intro q h p h1 h2
    by_cases e : p = q
    · subst e; exact Or.inr ⟨_, h, le_rfl⟩
    obtain ⟨r, h'⟩ := h
    simp only [LTL.toks, List.cons_append, List.length_cons, List.length_append,
      List.append_assoc] at h' h2 ⊢
    by_cases hp : p < q + 1 + φ1.toks.length
    · rcases ih1 ⟨_, drop_succ_of_drop h'⟩ p (by omega) hp with h3 | ⟨ψ, h3, h4⟩
      · exact Or.inl h3
      · exact Or.inr ⟨ψ, h3, by omega⟩
    · rcases ih2 ⟨_, drop_append_of_drop (drop_succ_of_drop h')⟩ p (by omega) (by omega) with
        h3 | ⟨ψ, h3, h4⟩
      · exact Or.inl h3
      · exact Or.inr ⟨ψ, h3, by omega⟩

/-! ## The positional tree of an encoded formula -/

/-- End of the formula. -/
def tF (ts : List Tok) : ℕ := fend ts 1

/-- Nodes: tag positions in `[1, F)`. -/
def tnd (ts : List Tok) (p : ℕ) : Bool := decide (1 ≤ p ∧ p < tF ts ∧ 5 ≤ tc ts p)

/-- Kind of a node: its tag. -/
def tkd (ts : List Tok) (p : ℕ) : ℕ := tc ts p - 5

/-- Arity of a node. -/
def tar (ts : List Tok) (p : ℕ) : ℕ :=
  if tkd ts p ≤ 1 then 0 else if tkd ts p = 2 ∨ tkd ts p = 4 then 1 else 2

lemma tkd_at {p : ℕ} {ψ : LTL} (h : At ts p ψ) : tkd ts p = ψ.tag := by
  unfold tkd; rw [tc_at h]; omega

section

variable {φ : LTL} (hφ : At ts 1 φ)
include hφ

lemma tF_eq : tF ts = 1 + φ.toks.length := fend_at hφ

lemma node_sub {p : ℕ} (hp : tnd ts p = true) :
    ∃ ψ, At ts p ψ ∧ p + ψ.toks.length ≤ tF ts := by
  simp only [tnd, decide_eq_true_eq] at hp
  rw [tF_eq hφ] at hp ⊢
  rcases tag_sub φ hφ p hp.1 hp.2.1 with h | h
  · omega
  · exact h

lemma tnd_of_at {p : ℕ} {ψ : LTL} (h : At ts p ψ) (h1 : 1 ≤ p) (h2 : p < tF ts) :
    tnd ts p = true := by
  simp only [tnd, decide_eq_true_eq]; exact ⟨h1, h2, by rw [tc_at h]; omega⟩

/-- **The positional tree of an encoded formula.** -/
def tokPT : PT where
  F := tF ts
  nd := tnd ts
  ar := tar ts
  fe := fend ts
  nd_one := tnd_of_at hφ hφ le_rfl (by rw [tF_eq hφ]; have := φ.toks_pos; omega)
  fe_one := rfl
  nd_ge := fun p hp => by simp only [tnd, decide_eq_true_eq] at hp; exact hp.1
  lt_fe := fun p hp => by
    obtain ⟨ψ, h1, -⟩ := node_sub hφ hp
    rw [fend_at h1]; have := ψ.toks_pos; omega
  fe_le := fun p hp => by
    obtain ⟨ψ, h1, h2⟩ := node_sub hφ hp
    rw [fend_at h1]; exact h2
  ar_le := fun p _ => by unfold tar; split_ifs <;> omega
  leaf_nd := fun p hp har q hpq hqf => by
    obtain ⟨ψ, h1, -⟩ := node_sub hφ hp
    rw [fend_at h1] at hqf
    have hk := tkd_at h1
    unfold tar at har
    cases ψ with
    | ap a =>
      obtain ⟨r, h⟩ := h1
      simp only [LTL.toks, List.cons_append, List.length_cons] at h hqf
      have := tc_le_two_of_natToks (drop_succ_of_drop h) (q := q) (by omega) (by omega)
      simp only [tnd, decide_eq_false_iff_not]; omega
    | tt => simp [LTL.toks] at hqf; omega
    | _ => simp [LTL.tag] at hk; split_ifs at har <;> omega
  un := fun p hp har => by
    obtain ⟨ψ, h1, h2⟩ := node_sub hφ hp
    have hk := tkd_at h1
    unfold tar at har
    cases ψ with
    | neg χ =>
      have h1' := h1
      obtain ⟨r, h⟩ := h1
      simp only [LTL.toks, List.cons_append, List.length_cons] at h h2
      have hc : At ts (p + 1) χ := ⟨_, drop_succ_of_drop h⟩
      have := χ.toks_pos
      refine ⟨tnd_of_at hφ hc (by omega) (by omega), ?_⟩
      rw [fend_at hc, fend_at h1']; simp [LTL.toks]; omega
    | X χ =>
      have h1' := h1
      obtain ⟨r, h⟩ := h1
      simp only [LTL.toks, List.cons_append, List.length_cons] at h h2
      have hc : At ts (p + 1) χ := ⟨_, drop_succ_of_drop h⟩
      have := χ.toks_pos
      refine ⟨tnd_of_at hφ hc (by omega) (by omega), ?_⟩
      rw [fend_at hc, fend_at h1']; simp [LTL.toks]; omega
    | _ => simp [LTL.tag] at hk; split_ifs at har <;> omega
  bin := fun p hp har => by
    obtain ⟨ψ, h1, h2⟩ := node_sub hφ hp
    have hk := tkd_at h1
    unfold tar at har
    cases ψ with
    | and χ1 χ2 =>
      have h1' := h1
      obtain ⟨r, h⟩ := h1
      simp only [LTL.toks, List.cons_append, List.length_cons, List.length_append,
        List.append_assoc] at h h2
      have hc1 : At ts (p + 1) χ1 := ⟨_, drop_succ_of_drop h⟩
      have hc2 : At ts (p + 1 + χ1.toks.length) χ2 :=
        ⟨_, drop_append_of_drop (drop_succ_of_drop h)⟩
      have := χ1.toks_pos; have := χ2.toks_pos
      refine ⟨tnd_of_at hφ hc1 (by omega) (by omega), ?_, ?_⟩
      · rw [fend_at hc1]; exact tnd_of_at hφ hc2 (by omega) (by omega)
      · rw [fend_at hc1, fend_at hc2, fend_at h1']
        simp [LTL.toks]; omega
    | U χ1 χ2 =>
      have h1' := h1
      obtain ⟨r, h⟩ := h1
      simp only [LTL.toks, List.cons_append, List.length_cons, List.length_append,
        List.append_assoc] at h h2
      have hc1 : At ts (p + 1) χ1 := ⟨_, drop_succ_of_drop h⟩
      have hc2 : At ts (p + 1 + χ1.toks.length) χ2 :=
        ⟨_, drop_append_of_drop (drop_succ_of_drop h)⟩
      have := χ1.toks_pos; have := χ2.toks_pos
      refine ⟨tnd_of_at hφ hc1 (by omega) (by omega), ?_, ?_⟩
      · rw [fend_at hc1]; exact tnd_of_at hφ hc2 (by omega) (by omega)
      · rw [fend_at hc1, fend_at hc2, fend_at h1']
        simp [LTL.toks]; omega
    | _ => simp [LTL.tag] at hk; split_ifs at har <;> omega

end

end LTok

end PathChecking
