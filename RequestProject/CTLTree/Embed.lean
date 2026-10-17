module

public import RequestProject.CTLTree.Glue
public import RequestProject.Shallow.ValidT

/-!
# Recognising CTL instances through CTL* instances

The token map `hL` replaces every tag `6` (the binary `AU` of CTL) by the two tags `6 3` (the
unary `E` of CTL* followed by a conjunction).  It maps the encoding of a CTL formula to the
encoding of a CTL* formula (`hL_toks`), and conversely every token list mapped onto the encoding
of a CTL* formula comes from a CTL formula (`parse_back`).  Hence `ts` is a CTL instance iff
`hL ts` is a CTL* instance (`recog_hL_iff`), which is recognised by `recog` with an unrestrictive
branching bound.
-/

@[expose] public section

namespace PathChecking

namespace CTLT

open CTLP ShallowP MCVPReduction

/-- The image of a token. -/
def hT (t : Tok) : List Tok := if t = Tok.tag 6 then [Tok.tag 6, Tok.tag 3] else [t]

/-- The token map. -/
def hL (l : List Tok) : List Tok := l.flatMap hT

@[simp] lemma hL_nil : hL [] = [] := rfl
lemma hL_cons (t : Tok) (l : List Tok) : hL (t :: l) = hT t ++ hL l := rfl
lemma hL_append (l l' : List Tok) : hL (l ++ l') = hL l ++ hL l' := by simp [hL]

lemma hT_ne (t : Tok) (h : t ≠ Tok.tag 6) : hT t = [t] := by simp [hT, h]

lemma hL_of_not_mem : ∀ l : List Tok, Tok.tag 6 ∉ l → hL l = l
  | [], _ => rfl
  | t :: l, h => by
    simp only [List.mem_cons, not_or] at h
    rw [hL_cons, hT_ne t (Ne.symm h.1), hL_of_not_mem l h.2]; rfl

/-- Prefixes without tag `6` are preserved. -/
lemma hL_prefix : ∀ l : List Tok, Tok.tag 6 ∉ l → ∀ s R, hL s = l ++ R →
    ∃ s', s = l ++ s' ∧ hL s' = R
  | [], _, s, R, h => ⟨s, rfl, h⟩
  | t :: l, hl, s, R, h => by
    simp only [List.mem_cons, not_or] at hl
    cases s with
    | nil => simp at h
    | cons t0 s0 =>
      rw [hL_cons] at h
      by_cases h6 : t0 = Tok.tag 6
      · subst h6
        rw [show hT (Tok.tag 6) = [Tok.tag 6, Tok.tag 3] from if_pos rfl] at h
        simp only [List.cons_append, List.cons.injEq] at h
        exact absurd h.1.symm (Ne.symm hl.1)
      · rw [hT_ne t0 h6] at h
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        obtain ⟨s', rfl, h3⟩ := hL_prefix l hl.2 s0 R h2
        exact ⟨s', rfl, h3⟩

lemma hL_head {t : Tok} (ht : t ≠ Tok.tag 6) {s rest : List Tok} (h : hL s = t :: rest) :
    ∃ s0, s = t :: s0 ∧ hL s0 = rest :=
  hL_prefix [t] (by simp [Ne.symm ht]) s rest h

lemma natToks_no6 (a : ℕ) : Tok.tag 6 ∉ natToks a := by
  simp only [natToks, List.mem_append, List.mem_map, List.mem_singleton, not_or, not_exists,
    not_and]
  refine ⟨fun b _ h => ?_, by decide⟩
  cases b <;> simp at h

lemma finsetToks_no6 (l : Finset ℕ) : Tok.tag 6 ∉ finsetToks l := by
  simp only [finsetToks, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_singleton,
    not_or, not_exists, not_and]
  exact ⟨by decide, fun a _ h => natToks_no6 a h, by decide⟩

lemma mem_toksList {tok : Tok} : ∀ {cs : List LTree}, tok ∈ LTree.toksList cs →
    ∃ c ∈ cs, tok ∈ c.toks
  | [], h => by simp [LTree.toksList] at h
  | c :: cs, h => by
    rw [LTree.toksList_cons, List.mem_append] at h
    rcases h with h | h
    · exact ⟨c, List.mem_cons_self, h⟩
    · obtain ⟨c', hc', h'⟩ := mem_toksList h
      exact ⟨c', List.mem_cons_of_mem _ hc', h'⟩

lemma len_le_toksList {c : LTree} : ∀ {cs : List LTree}, c ∈ cs →
    c.toks.length ≤ (LTree.toksList cs).length
  | [], h => by simp at h
  | d :: cs, h => by
    rw [LTree.toksList_cons, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := len_le_toksList h; omega

lemma tree_no6 : ∀ (n : ℕ) (t : LTree), t.toks.length ≤ n → Tok.tag 6 ∉ t.toks := by
  intro n
  induction n with
  | zero => intro t h; have := LTree.toks_length_pos t; omega
  | succ n ih =>
    intro t h
    obtain ⟨l, cs⟩ := t
    have hlen := node_len l cs
    simp only [LTree.toks, List.mem_cons, List.mem_append, List.mem_singleton, not_or]
    refine ⟨by decide, ⟨finsetToks_no6 l, fun hm => ?_⟩, by decide⟩
    obtain ⟨c, hc, hm'⟩ := mem_toksList hm
    have := len_le_toksList hc
    exact ih c (by omega) hm'

lemma hL_tree (t : LTree) : hL t.toks = t.toks := hL_of_not_mem _ (tree_no6 _ t le_rfl)

/-- Every tree has shallow branching for a bound at least its size. -/
lemma sb_big : ∀ (n : ℕ) (t : LTree), t.toks.length ≤ n → Shallow.ShallowBranching n t := by
  intro n
  induction n with
  | zero => intro t h; have := LTree.toks_length_pos t; omega
  | succ n ih =>
    intro t h
    obtain ⟨l, cs⟩ := t
    have hlen := node_len l cs
    exact .step fun c hc => ih c (by have := len_le_toksList hc; omega)

/-- The CTL* formula of a CTL formula under the token map. -/
def emb : CTL → CTLStar
  | .ap a => .ap a
  | .tt => .tt
  | .neg φ => .neg (emb φ)
  | .and φ ψ => .and (emb φ) (emb ψ)
  | .EX φ => .X (emb φ)
  | .EU φ ψ => .U (emb φ) (emb ψ)
  | .AU φ ψ => .E (.and (emb φ) (emb ψ))

lemma hL_toks (φ : CTL) : hL φ.toks = (emb φ).toks := by
  induction φ with
  | ap a => simp [CTL.toks, emb, CTLStar.toks, hL_cons, hT_ne (Tok.tag 0) (by decide),
      hL_of_not_mem _ (natToks_no6 a)]
  | tt => simp [CTL.toks, emb, CTLStar.toks, hL_cons, hT_ne (Tok.tag 1) (by decide)]
  | neg φ ih => simp [CTL.toks, emb, CTLStar.toks, hL_cons, hT_ne (Tok.tag 2) (by decide), ih]
  | and φ ψ ih1 ih2 => simp [CTL.toks, emb, CTLStar.toks, hL_cons, hL_append,
      hT_ne (Tok.tag 3) (by decide), ih1, ih2]
  | EX φ ih => simp [CTL.toks, emb, CTLStar.toks, hL_cons, hT_ne (Tok.tag 4) (by decide), ih]
  | EU φ ψ ih1 ih2 => simp [CTL.toks, emb, CTLStar.toks, hL_cons, hL_append,
      hT_ne (Tok.tag 5) (by decide), ih1, ih2]
  | AU φ ψ ih1 ih2 => simp [CTL.toks, emb, CTLStar.toks, hL_cons, hL_append, hT, ih1, ih2]

/-- **Parsing back.** -/
theorem parse_back : ∀ (n : ℕ) (ψ : CTLStar), ψ.toks.length ≤ n → ∀ s R, hL s = ψ.toks ++ R →
    ∃ (φ : CTL) (s' : List Tok), s = φ.toks ++ s' ∧ hL s' = R := by
  intro n
  induction n with
  | zero => intro ψ h; cases ψ <;> simp [CTLStar.toks] at h
  | succ n ih =>
    intro ψ hn s R h
    cases ψ with
    | ap a =>
      obtain ⟨s0, rfl, h0⟩ := hL_head (t := Tok.tag 0) (by decide) (by simpa [CTLStar.toks] using h)
      obtain ⟨s', rfl, h'⟩ := hL_prefix _ (natToks_no6 a) s0 R h0
      exact ⟨.ap a, s', by simp [CTL.toks], h'⟩
    | tt =>
      obtain ⟨s0, rfl, h0⟩ := hL_head (t := Tok.tag 1) (by decide) (by simpa [CTLStar.toks] using h)
      exact ⟨.tt, s0, by simp [CTL.toks], h0⟩
    | neg ψ1 =>
      obtain ⟨s0, rfl, h0⟩ := hL_head (t := Tok.tag 2) (by decide) (by simpa [CTLStar.toks] using h)
      obtain ⟨φ1, s', rfl, h'⟩ := ih ψ1 (by simp [CTLStar.toks] at hn; omega) s0 R h0
      exact ⟨.neg φ1, s', by simp [CTL.toks], h'⟩
    | and ψ1 ψ2 =>
      obtain ⟨s0, rfl, h0⟩ := hL_head (t := Tok.tag 3) (by decide) (by simpa [CTLStar.toks] using h)
      simp only [CTLStar.toks, List.length_cons, List.length_append] at hn
      obtain ⟨φ1, s1, rfl, h1⟩ := ih ψ1 (by omega) s0 (ψ2.toks ++ R) (by simpa using h0)
      obtain ⟨φ2, s', rfl, h'⟩ := ih ψ2 (by omega) s1 R h1
      exact ⟨.and φ1 φ2, s', by simp [CTL.toks], h'⟩
    | X ψ1 =>
      obtain ⟨s0, rfl, h0⟩ := hL_head (t := Tok.tag 4) (by decide) (by simpa [CTLStar.toks] using h)
      obtain ⟨φ1, s', rfl, h'⟩ := ih ψ1 (by simp [CTLStar.toks] at hn; omega) s0 R h0
      exact ⟨.EX φ1, s', by simp [CTL.toks], h'⟩
    | U ψ1 ψ2 =>
      obtain ⟨s0, rfl, h0⟩ := hL_head (t := Tok.tag 5) (by decide) (by simpa [CTLStar.toks] using h)
      simp only [CTLStar.toks, List.length_cons, List.length_append] at hn
      obtain ⟨φ1, s1, rfl, h1⟩ := ih ψ1 (by omega) s0 (ψ2.toks ++ R) (by simpa using h0)
      obtain ⟨φ2, s', rfl, h'⟩ := ih ψ2 (by omega) s1 R h1
      exact ⟨.EU φ1 φ2, s', by simp [CTL.toks], h'⟩
    | E ψ1 =>
      cases s with
      | nil => simp [CTLStar.toks] at h
      | cons t0 s0 =>
        rw [hL_cons] at h
        by_cases h6 : t0 = Tok.tag 6
        · subst h6
          rw [show hT (Tok.tag 6) = [Tok.tag 6, Tok.tag 3] from if_pos rfl] at h
          simp only [CTLStar.toks, List.cons_append, List.nil_append,
            List.cons.injEq, true_and] at h
          cases ψ1 with
          | and ψa ψb =>
            simp only [CTLStar.toks, List.cons_append, List.cons.injEq, true_and] at h
            simp only [CTLStar.toks, List.length_cons, List.length_append] at hn
            obtain ⟨φ1, s1, rfl, h1⟩ := ih ψa (by omega) s0 (ψb.toks ++ R)
              (by simpa using h)
            obtain ⟨φ2, s', rfl, h'⟩ := ih ψb (by omega) s1 R h1
            exact ⟨.AU φ1 φ2, s', by simp [CTL.toks], h'⟩
          | _ => simp [CTLStar.toks] at h
        · rw [hT_ne t0 h6] at h
          simp only [CTLStar.toks, List.cons_append, List.nil_append, List.cons.injEq] at h
          exact absurd h.1 h6

/-- **Recognition of CTL instances.** -/
theorem recog_hL_iff (ts : List Tok) :
    recog (hL ts) ((hL ts).length + 1) = true ↔ ∃ (φ : CTL) (t : LTree), ts = instC φ t := by
  rw [recog_iff]
  constructor
  · rintro ⟨ψ, t, h, -⟩
    obtain ⟨s0, rfl, h0⟩ := hL_head (by decide) h
    obtain ⟨φ, s', rfl, h'⟩ := parse_back _ ψ le_rfl s0 _ h0
    obtain ⟨s'', rfl, h''⟩ := hL_head (by decide) h'
    obtain ⟨s3, rfl, h3⟩ := hL_prefix _ (tree_no6 _ t le_rfl) s'' [] (by simpa using h'')
    have : s3 = [] := by
      cases s3 with
      | nil => rfl
      | cons t3 s3 =>
        exfalso
        rw [hL_cons] at h3
        unfold hT at h3
        split_ifs at h3 <;> simp at h3
    subst this
    exact ⟨φ, t, by simp [instC]⟩
  · rintro ⟨φ, t, rfl⟩
    refine ⟨emb φ, t, ?_, sb_big _ t ?_⟩
    · rw [instC, hL_cons, hT_ne _ (by decide), hL_append, hL_toks, hL_cons,
        hT_ne _ (by decide), hL_tree]
      rfl
    · rw [instC, hL_cons, hT_ne _ (by decide), hL_append, hL_cons, hT_ne _ (by decide), hL_tree]
      simp; omega

end CTLT

end PathChecking
