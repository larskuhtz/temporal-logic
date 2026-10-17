module

public import RequestProject.LTLPath.ValidPath

/-!
# Completeness of the local path conditions

`pathOK_complete`: the encoding of an instance satisfies `PathOK`.  The local rule `Lr` is
checked on lists of tokens with `List.IsChain`, the comparison of consecutive numbers with
`numLt_iff`.
-/

@[expose] public section

namespace PathChecking

namespace LTok

open CTLP LS MCVPReduction

variable {ts : List Tok}

/-! ## The top bit of a number -/

lemma testBit_size_pred {a : ℕ} (h : 0 < a) : a.testBit (a.size - 1) = true := by
  by_contra hc
  have hc' : a.testBit (a.size - 1) = false := by simpa using hc
  have hlt : a < 2 ^ (a.size - 1) := Nat.lt_pow_two_of_testBit a fun i hi => by
    rcases Nat.eq_or_lt_of_le hi with h' | h'
    · rw [← h']; exact hc'
    · exact testBit_size_le a (by omega)
  have hpos : 0 < a.size := Nat.size_pos.2 h
  have := pow_size_pred_le hpos
  omega

lemma natToks_split (a : ℕ) : ∃ ds : List Tok, natToks a = ds ++ [Tok.sep] ∧
    (∀ d ∈ ds, d.code ≤ 1) ∧ (∀ x ∈ ds.getLast?, x.code = 1) := by
  refine ⟨(Nat.bits a).map digitTok, natToks_eq a, ?_, ?_⟩
  · intro d hd
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hd
    cases b <;> simp [digitTok, Tok.code]
  · intro x hx
    rw [List.getLast?_map] at hx
    obtain ⟨b, hb, rfl⟩ := Option.mem_map.1 hx
    have hne : Nat.bits a ≠ [] := fun h => by simp [h] at hb
    have hlen : 0 < (Nat.bits a).length := List.length_pos_of_ne_nil hne
    rw [List.getLast?_eq_getElem?] at hb
    have hm : (Nat.bits a).length - 1 < (Nat.bits a).length := by omega
    rw [List.getElem?_eq_getElem hm, Option.mem_def, Option.some_inj] at hb
    have hg := getD_bits a ((Nat.bits a).length - 1)
    rw [List.getD_eq_getElem _ _ hm, hb, Nat.size_eq_bits_len] at hg
    have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0; simp at hlen
      · exact h0
    rw [testBit_size_pred ha] at hg
    rw [hg]; rfl

lemma Lr_false_iff (b c : ℕ) : Lr b c False ↔ c ≤ 4 ∧ (c = 3 → b = 4) ∧ (c = 4 → b = 2 ∨ b = 3) ∧
    (c ≤ 2 → b ≤ 3) ∧ (c = 2 → b ≠ 0) := by
  simp only [Lr, and_false, or_false, not_false_eq_true, and_true]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, fun h => by have := h4 h; omega, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, fun h => by have := h4 h; omega, h5⟩

@[simp] lemma code_zero : Tok.zero.code = 0 := rfl
@[simp] lemma code_one : Tok.one.code = 1 := rfl
@[simp] lemma code_sep : Tok.sep.code = 2 := rfl
@[simp] lemma code_lpar : Tok.lpar.code = 3 := rfl
@[simp] lemma code_rpar : Tok.rpar.code = 4 := rfl

/-! ## The local rule on lists -/

/-- The local rule inside a group (the previous position does not open the group). -/
def PR (x y : Tok) : Prop := Lr x.code y.code False

lemma pr_digits : ∀ (ds : List Tok) (t : Tok), t.code ≤ 3 → (∀ d ∈ ds, d.code ≤ 1) →
    List.IsChain PR (t :: ds) := by
  intro ds
  induction ds with
  | nil => intro t _ _; exact List.isChain_singleton t
  | cons d ds ih =>
    intro t ht hd
    have hd0 := hd d (by simp)
    refine List.isChain_cons_cons.2 ⟨?_, ih d (by omega) fun d' hd' => hd d' (by simp [hd'])⟩
    rw [PR, Lr_false_iff]; omega

lemma pr_natToks (a : ℕ) (t : Tok) (ht : t.code = 2 ∨ t.code = 3) (L : List Tok)
    (hL : List.IsChain PR (Tok.sep :: L)) : List.IsChain PR (t :: (natToks a ++ L)) := by
  obtain ⟨ds, hds, hd, hlast⟩ := natToks_split a
  rw [hds, show t :: (ds ++ [Tok.sep] ++ L) = (t :: ds) ++ (Tok.sep :: L) by simp]
  refine List.isChain_append.2 ⟨pr_digits ds t (by omega) hd, hL, fun x hx y hy => ?_⟩
  simp only [List.head?_cons, Option.mem_def, Option.some_inj] at hy
  subst hy
  rw [List.getLast?_cons, Option.mem_def, Option.some_inj] at hx
  have hx' : x.code = 1 ∨ x.code = 2 ∨ x.code = 3 := by
    cases hds' : ds.getLast? with
    | none => rw [hds'] at hx; simp at hx; subst hx; omega
    | some z => rw [hds'] at hx; simp at hx; subst hx; left; exact hlast z hds'
  rw [PR, Lr_false_iff, code_sep]; omega

lemma pr_nums : ∀ (xs : List ℕ) (t : Tok), (t.code = 2 ∨ t.code = 3) →
    List.IsChain PR (t :: (xs.flatMap natToks ++ [Tok.rpar])) := by
  intro xs
  induction xs with
  | nil =>
    intro t ht
    refine List.isChain_pair.2 ?_
    rw [PR, Lr_false_iff, code_rpar]; omega
  | cons a xs ih =>
    intro t ht
    rw [List.flatMap_cons, List.append_assoc]
    exact pr_natToks a t ht _ (ih Tok.sep (Or.inl rfl))

lemma pr_finset (S : Finset ℕ) : List.IsChain PR (finsetToks S) := by
  rw [finsetToks_eq]
  exact pr_nums _ Tok.lpar (Or.inr rfl)

lemma finsetToks_getLast (S : Finset ℕ) : (finsetToks S).getLast? = some Tok.rpar := by
  rw [finsetToks_eq, List.getLast?_cons, List.getLast?_append]; simp

lemma lettersToks_head : ∀ (Ls : List (Finset ℕ)), ∀ y ∈ (lettersToks Ls).head?, y = Tok.lpar := by
  intro Ls y hy
  cases Ls with
  | nil => exact absurd hy (by simp [lettersToks])
  | cons S Ls =>
    rw [lettersToks_cons, finsetToks_eq] at hy
    simp at hy; exact hy.symm

lemma pr_letters : ∀ Ls : List (Finset ℕ), List.IsChain PR (lettersToks Ls) := by
  intro Ls
  induction Ls with
  | nil => exact List.isChain_nil
  | cons S Ls ih =>
    rw [lettersToks_cons]
    refine List.isChain_append.2 ⟨pr_finset S, ih, fun x hx y hy => ?_⟩
    rw [finsetToks_getLast, Option.mem_def, Option.some_inj] at hx
    subst hx
    rw [lettersToks_head Ls y hy]
    rw [PR, Lr_false_iff, code_rpar, code_lpar]; omega

lemma lettersToks_getLast : ∀ Ls : List (Finset ℕ), ∀ x ∈ (lettersToks Ls).getLast?, x = Tok.rpar := by
  intro Ls
  induction Ls with
  | nil => simp [lettersToks]
  | cons S Ls ih =>
    intro x hx
    rw [lettersToks_cons, List.getLast?_append] at hx
    cases h : (lettersToks Ls).getLast? with
    | none => rw [h, finsetToks_getLast] at hx; simpa using hx.symm
    | some z => rw [h] at hx; simp at hx; subst hx; exact ih z h

lemma lettersToks_getElem_zero {Ls : List (Finset ℕ)} (h : 0 < (lettersToks Ls).length) :
    ((lettersToks Ls)[0]).code = 3 := by
  have := lettersToks_head Ls ((lettersToks Ls)[0]) (by simp [List.head?_eq_getElem?])
  rw [this]; rfl

lemma lettersToks_getElem_last {Ls : List (Finset ℕ)} (h : 0 < (lettersToks Ls).length) :
    ((lettersToks Ls)[(lettersToks Ls).length - 1]).code = 4 := by
  have := lettersToks_getLast Ls ((lettersToks Ls)[(lettersToks Ls).length - 1])
    (by rw [List.getLast?_eq_getElem?]; simp)
  rw [this]; rfl

/-- **The local rule inside a group.** -/
lemma group_rule {G : ℕ} {Ls : List (Finset ℕ)} {rest : List Tok}
    (h : ts.drop G = Tok.lpar :: (lettersToks Ls ++ Tok.rpar :: rest)) :
    ∀ j, G < j → j ≤ G + (lettersToks Ls).length → Lr (tc ts (j - 1)) (tc ts j) (j - 1 = G) := by
  intro j hj1 hj2
  have h' : ts.drop G = (Tok.lpar :: lettersToks Ls) ++ (Tok.rpar :: rest) := by simpa using h
  have hc : ∀ m (hm : m < (lettersToks Ls).length), tc ts (G + 1 + m) = ((lettersToks Ls)[m]).code := by
    intro m hm
    rw [show G + 1 + m = G + (m + 1) by omega, tc_seg h' (by simp; omega)]
    simp
  rcases Nat.eq_or_lt_of_le (show G ≤ j - 1 by omega) with he | he
  · have h0 : tc ts (j - 1) = 3 := by
      rw [← he, show G = G + 0 by rfl, tc_seg h' (by simp)]; rfl
    have h1 : tc ts j = 3 := by
      rw [show j = G + 1 + 0 by omega, hc 0 (by omega)]
      exact lettersToks_getElem_zero (by omega)
    rw [h0, h1]
    unfold Lr; refine ⟨by omega, fun _ => Or.inr ⟨rfl, he.symm⟩, by omega, by omega, by omega⟩
  · have hch := List.isChain_iff_getElem.1 (pr_letters Ls) (j - 1 - (G + 1)) (by omega)
    have e1 : tc ts (j - 1) = ((lettersToks Ls)[j - 1 - (G + 1)]'(by omega)).code := by
      rw [← hc _ (by omega)]; congr 1; omega
    have e2 : tc ts j = ((lettersToks Ls)[j - 1 - (G + 1) + 1]'(by omega)).code := by
      rw [← hc _ (by omega)]; congr 1; omega
    rw [e1, e2]
    exact (Lr_congr (iff_of_false id (by omega))).1 hch

/-! ## Comparison of consecutive numbers -/

lemma numOK_of_not_NS {s : ℕ} (h : ¬ NS ts s) : NumOK ts s := fun h' => absurd h' h

lemma nums_numOK : ∀ (xs : List ℕ) {o : ℕ} {rest : List Tok}, xs.Pairwise (· < ·) →
    ts.drop o = xs.flatMap natToks ++ Tok.rpar :: rest →
    ∀ s, o ≤ s → s < o + (xs.flatMap natToks).length → NumOK ts s := by
  intro xs
  induction xs with
  | nil => intro o rest _ _ s h1 h2; simp at h2; omega
  | cons a xs ih =>
    intro o rest hp h s hs1 hs2
    have ha : ts.drop o = natToks a ++ (xs.flatMap natToks ++ Tok.rpar :: rest) := by
      simpa using h
    have hlen : (natToks a).length = a.size + 1 := by simp [natToks, Nat.size_eq_bits_len]
    obtain ⟨hn1, hn2⟩ := natToks_nE ha
    have hd := drop_append_of_drop ha
    rcases Nat.eq_or_lt_of_le hs1 with hso | hso
    · rw [← hso]
      intro _ hle
      rw [hn1] at hle ⊢
      rw [hlen, ← Nat.add_assoc] at hd
      cases xs with
      | nil =>
        have : ts.drop (o + a.size + 1) = Tok.rpar :: rest := by simpa using hd
        rw [tc_of_drop this] at hle; simp at hle
      | cons x xs =>
        have hx : ts.drop (o + a.size + 1) = natToks x ++ (xs.flatMap natToks ++ Tok.rpar :: rest) := by
          simpa using hd
        exact (numLt_iff ha hx).2 ((List.pairwise_cons.1 hp).1 x (by simp))
    · by_cases hs3 : s < o + (natToks a).length
      · refine numOK_of_not_NS fun hns => ?_
        have := hn2 (s - 1 - o) (by omega)
        rw [show o + (s - 1 - o) = s - 1 by omega] at this
        have h01 : tc ts (s - 1) ≤ 1 := by rw [this]; cases a.testBit (s - 1 - o) <;> simp
        rcases hns.2 with h | h <;> omega
      · rw [List.flatMap_cons, List.length_append] at hs2
        exact ih (List.pairwise_cons.1 hp).2 hd s (by omega) (by omega)

lemma letter_numOK {u : ℕ} {S : Finset ℕ} {rest : List Tok} (h : ts.drop u = finsetToks S ++ rest) :
    ∀ s, u ≤ s → s < u + (finsetToks S).length → NumOK ts s := by
  intro s hs1 hs2
  have h' : ts.drop u = Tok.lpar :: ((S.sort (· ≤ ·)).flatMap natToks ++ Tok.rpar :: rest) := by
    simpa [finsetToks_eq] using h
  have hlen : (finsetToks S).length = ((S.sort (· ≤ ·)).flatMap natToks).length + 2 := by
    simp [finsetToks_eq]
  rcases Nat.eq_or_lt_of_le hs1 with he | he
  · subst he
    refine numOK_of_not_NS fun hns => ?_
    have := tc_of_drop h'; simp [Tok.code] at this; have := hns.1; omega
  · have h1 := drop_succ_of_drop h'
    by_cases hs3 : s < u + 1 + ((S.sort (· ≤ ·)).flatMap natToks).length
    · have hs : (S.sort (· ≤ ·)).Pairwise (· < ·) :=
        (Finset.pairwise_sort S (· ≤ ·)).imp₂ (fun a b hab hne => lt_of_le_of_ne hab hne)
          (Finset.sort_nodup S (· ≤ ·))
      exact nums_numOK _ hs h1 s (by omega) hs3
    · refine numOK_of_not_NS fun hns => ?_
      have hd := drop_append_of_drop h1
      have hs' : s = u + 1 + ((S.sort (· ≤ ·)).flatMap natToks).length := by omega
      rw [← hs'] at hd
      have := tc_of_drop hd; simp [Tok.code] at this; have := hns.1; omega

lemma letters_numOK : ∀ (Ls : List (Finset ℕ)) {u : ℕ} {rest : List Tok},
    ts.drop u = lettersToks Ls ++ rest →
    ∀ s, u ≤ s → s < u + (lettersToks Ls).length → NumOK ts s := by
  intro Ls
  induction Ls with
  | nil => intro u rest _ s h1 h2; simp [lettersToks] at h2; omega
  | cons S Ls ih =>
    intro u rest h s hs1 hs2
    rw [lettersToks_cons, List.append_assoc] at h
    by_cases hs3 : s < u + (finsetToks S).length
    · exact letter_numOK h s hs1 hs3
    · exact ih (drop_append_of_drop h) s (by omega)
        (by rw [lettersToks_cons, List.length_append] at hs2; omega)

/-! ## Paths -/

variable {φ : LTL} {p : LassoPath}

/-- **Completeness of the path conditions.** -/
theorem pathOK_complete (h : Enc ts φ p) : PathOK ts := by
  have h1 := enc_drop_tP' h
  have hsE : sE ts = tP ts + 1 + (lettersToks p.stem).length := enc_sE h
  have hst := enc_drop_stem h
  have hdsE : ts.drop (sE ts) = Tok.rpar :: Tok.lpar :: ((lettersToks p.loop) ++ [Tok.rpar]) := by
    rw [hsE]; exact drop_append_of_drop hst
  have hdG : ts.drop (sE ts + 1) = Tok.lpar :: ((lettersToks p.loop) ++ Tok.rpar :: []) := drop_succ_of_drop hdsE
  have hlen : ts.length = sE ts + 2 + (lettersToks p.loop).length + 1 := by rw [enc_length h]; rfl
  have hLL2 : 2 ≤ (lettersToks p.loop).length := by
    obtain ⟨S, L, hSL⟩ := List.exists_cons_of_ne_nil p.loop_ne
    rw [hSL, lettersToks_cons, List.length_append]
    have := finsetToks_len S; omega
  have hdL : ts.drop (sE ts + 2) = (lettersToks p.loop) ++ [Tok.rpar] := drop_succ_of_drop hdG
  have hdL2 : ts.drop (sE ts + 2) = (lettersToks p.loop ++ [Tok.rpar]) ++ [] := by simp [hdL]
  have hdS : ts.drop (tP ts + 1) = (lettersToks p.stem) ++ (Tok.rpar :: Tok.lpar :: ((lettersToks p.loop) ++ [Tok.rpar])) := hst
  refine ⟨?_, by omega, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · rw [tc_of_drop h1]; rfl
  · rw [tc_of_drop hdsE]; rfl
  · rcases Nat.eq_zero_or_pos (lettersToks p.stem).length with h0 | h0
    · right; omega
    · left
      rw [show sE ts - 1 = tP ts + 1 + ((lettersToks p.stem).length - 1) by omega, tc_seg hdS (m := (lettersToks p.stem).length - 1) (by omega)]
      exact lettersToks_getElem_last h0
  · rw [tc_of_drop hdG]; rfl
  · rw [show sE ts + 2 = sE ts + 2 + 0 by rfl, tc_seg hdL (m := 0) (by omega)]
    exact lettersToks_getElem_zero (by omega)
  · rw [show ts.length - 1 = sE ts + 2 + (lettersToks p.loop).length by omega, tc_seg hdL2 (m := (lettersToks p.loop).length) (by simp)]
    simp
  · rw [show ts.length - 2 = sE ts + 2 + ((lettersToks p.loop).length - 1) by omega, tc_seg hdL (m := (lettersToks p.loop).length - 1) (by omega)]
    exact lettersToks_getElem_last (by omega)
  · intro j hj1 hj2 hj3 hj4
    by_cases hjs : j < sE ts
    · exact (Lr_congr (by omega)).1 (group_rule h1 j hj2 (by omega))
    · exact (Lr_congr (by omega)).1 (group_rule hdG j (by omega) (by omega))
  · intro s hs1 hs2
    by_cases hss : s < sE ts
    · exact letters_numOK p.stem hdS s (by omega) (by omega)
    · by_cases hs3 : s < sE ts + 2
      · refine numOK_of_not_NS fun hns => ?_
        have := hns.1
        rcases (show s = sE ts ∨ s = sE ts + 1 by omega) with rfl | rfl
        · rw [tc_of_drop hdsE] at this; simp [Tok.code] at this
        · rw [tc_of_drop hdG] at this; simp [Tok.code] at this
      · by_cases hs4 : s < ts.length - 1
        · exact letters_numOK p.loop hdL s (by omega) (by omega)
        · refine numOK_of_not_NS fun hns => ?_
          have := hns.1
          rw [show s = sE ts + 2 + (lettersToks p.loop).length by omega, tc_seg hdL2 (m := (lettersToks p.loop).length) (by simp)] at this
          simp [Tok.code] at this

end LTok

end PathChecking
