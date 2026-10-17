module

public import RequestProject.LTLPath.ValidTok

/-!
# Local recognition of encoded instances: paths

`PathOK ts` is a conjunction of conditions on the token codes after the formula, each of which
only inspects a bounded number of positions (found by bounded search) and is therefore easy to
check in logarithmic space:

* the bracket structure of the two groups (stem and loop) is fixed by `sE` (the closing bracket
  of the stem);
* consecutive codes satisfy the local rule `Lr` (letters are bracketed lists of numbers, numbers
  are canonical);
* consecutive numbers of a letter are strictly increasing (`NumOK`, compared bitwise by `NumLt`).

`pathOK_sound`: if `PathOK ts` holds, then the tokens from `tP ts` on are the encoding of a lasso
path.
-/

@[expose] public section

namespace PathChecking

namespace LTok

open CTLP LS MCVPReduction

variable (ts : List Tok)

/-- Local rule for consecutive codes `b c` of the path part; `g` says that the previous position
opens a group. -/
def Lr (b c : ℕ) (g : Prop) : Prop :=
  c ≤ 4 ∧ (c = 3 → b = 4 ∨ (b = 3 ∧ g)) ∧ (c = 4 → b = 2 ∨ (b = 3 ∧ ¬ g)) ∧
    (c ≤ 2 → b ≤ 2 ∨ (b = 3 ∧ ¬ g)) ∧ (c = 2 → b ≠ 0)

/-- Position of the first `sep` at or after `s`. -/
def nE (s : ℕ) : ℕ := ffind (fun u => tc ts u == 2) s ts.length

/-- The number starting at `s` is smaller than the number starting at `t` (bitwise comparison:
shorter, or of the same length and smaller at the most significant differing bit). -/
def NumLt (s t : ℕ) : Prop :=
  nE ts s - s < nE ts t - t ∨ (nE ts s - s = nE ts t - t ∧ ∃ m < nE ts s - s,
    tc ts (s + m) = 0 ∧ tc ts (t + m) = 1 ∧
      ∀ k < nE ts s - s, m < k → tc ts (s + k) = tc ts (t + k))

/-- A number starts at `s`. -/
def NS (s : ℕ) : Prop := tc ts s ≤ 2 ∧ (tc ts (s - 1) = 2 ∨ tc ts (s - 1) = 3)

/-- If a number starts at `s` and another number follows it, then the second one is larger. -/
def NumOK (s : ℕ) : Prop := NS ts s → tc ts (nE ts s + 1) ≤ 2 → NumLt ts s (nE ts s + 1)

/-- The path part of the input is well formed. -/
def PathOK : Prop :=
  tc ts (tP ts) = 3 ∧ tP ts < sE ts ∧ tc ts (sE ts) = 4 ∧
    (tc ts (sE ts - 1) = 4 ∨ sE ts - 1 = tP ts) ∧
    tc ts (sE ts + 1) = 3 ∧ tc ts (sE ts + 2) = 3 ∧ sE ts + 5 ≤ ts.length ∧
    tc ts (ts.length - 1) = 4 ∧ tc ts (ts.length - 2) = 4 ∧
    (∀ j < ts.length - 1, tP ts < j → j ≠ sE ts → j ≠ sE ts + 1 →
      Lr (tc ts (j - 1)) (tc ts j) (j - 1 = tP ts ∨ j - 1 = sE ts + 1)) ∧
    (∀ s < ts.length, tP ts < s → NumOK ts s)

variable {ts}

/-! ## Comparing numbers bitwise -/

lemma pow_size_pred_le {b : ℕ} (hb : 0 < b.size) : 2 ^ (b.size - 1) ≤ b :=
  Nat.lt_size.1 (by omega)

lemma testBit_size_le (a : ℕ) {k : ℕ} (hk : a.size ≤ k) : a.testBit k = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Nat.lt_size_self a)
    (Nat.pow_le_pow_right (by norm_num) hk))

lemma lt_iff_size_bits (a b : ℕ) : a < b ↔ a.size < b.size ∨ (a.size = b.size ∧
    ∃ m < a.size, a.testBit m = false ∧ b.testBit m = true ∧
      ∀ k < a.size, m < k → a.testBit k = b.testBit k) := by
  constructor
  · intro hab
    rcases lt_trichotomy a.size b.size with h | h | h
    · left; exact h
    · right
      refine ⟨h, ?_⟩
      have hex : ∃ m, m < a.size ∧ a.testBit m ≠ b.testBit m := by
        by_contra hc
        push_neg at hc
        apply hab.ne
        apply Nat.eq_of_testBit_eq
        intro i
        by_cases hi : i < a.size
        · exact hc i hi
        · rw [testBit_size_le a (by omega), testBit_size_le b (by omega)]
      classical
      obtain ⟨m0, hm0, hd0⟩ := hex
      set m := Nat.findGreatest (fun m => m < a.size ∧ a.testBit m ≠ b.testBit m) a.size with hm
      have hspec : m < a.size ∧ a.testBit m ≠ b.testBit m :=
        Nat.findGreatest_spec (P := fun m => m < a.size ∧ a.testBit m ≠ b.testBit m) (m := m0)
          hm0.le ⟨hm0, hd0⟩
      have hmax : ∀ k < a.size, m < k → a.testBit k = b.testBit k := by
        intro k hk hmk
        by_contra hc
        have := Nat.le_findGreatest (P := fun m => m < a.size ∧ a.testBit m ≠ b.testBit m)
          hk.le ⟨hk, hc⟩
        omega
      have hmax' : ∀ k, m < k → b.testBit k = a.testBit k := by
        intro k hmk
        by_cases hk : k < a.size
        · exact (hmax k hk hmk).symm
        · rw [testBit_size_le a (by omega), testBit_size_le b (by omega)]
      refine ⟨m, hspec.1, ?_, ?_, hmax⟩
      · by_contra hc
        have ha : a.testBit m = true := by simpa using hc
        have hb : b.testBit m = false := by
          have := hspec.2; rw [ha] at this; simpa using this.symm
        exact absurd (Nat.lt_of_testBit m hb ha hmax') (by omega)
      · by_contra hc
        have hb : b.testBit m = false := by simpa using hc
        have ha : a.testBit m = true := by
          have := hspec.2; rw [hb] at this; simpa using this
        exact absurd (Nat.lt_of_testBit m hb ha hmax') (by omega)
    · exfalso
      have h1 := Nat.lt_size_self b
      have h2 := pow_size_pred_le (b := a) (by omega)
      have h3 : 2 ^ b.size ≤ 2 ^ (a.size - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  · rintro (h | ⟨h, m, hm, ha, hb, hk⟩)
    · have h1 := Nat.lt_size_self a
      have h2 := pow_size_pred_le (b := b) (by omega)
      have h3 : 2 ^ a.size ≤ 2 ^ (b.size - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · refine Nat.lt_of_testBit m ha hb fun j hj => ?_
      by_cases hja : j < a.size
      · exact hk j hja hj
      · rw [testBit_size_le a (by omega), testBit_size_le b (by omega)]

lemma natToks_getElem_digit (a m : ℕ) (hm : m < a.size) :
    ((natToks a)[m]'(by simp [natToks, Nat.size_eq_bits_len]; omega)).code = (a.testBit m).toNat := by
  have hm' : m < (Nat.bits a).length := by rw [Nat.size_eq_bits_len]; exact hm
  simp only [natToks]
  rw [List.getElem_append_left (by simpa using hm')]
  simp only [List.getElem_map]
  have := getD_bits a m
  rw [List.getD_eq_getElem _ _ hm'] at this
  rw [this]
  cases a.testBit m <;> rfl

lemma natToks_nE {s a : ℕ} {r : List Tok} (h : ts.drop s = natToks a ++ r) :
    nE ts s = s + a.size ∧ ∀ m < a.size, tc ts (s + m) = (a.testBit m).toNat := by
  have hlen : (natToks a).length = a.size + 1 := by
    simp [natToks, Nat.size_eq_bits_len]
  have hd : ∀ m < a.size, tc ts (s + m) = (a.testBit m).toNat := fun m hm => by
    rw [tc_seg h (by omega), natToks_getElem_digit a m hm]
  refine ⟨?_, hd⟩
  have hsep : tc ts (s + a.size) = 2 := by
    rw [tc_seg h (by omega)]
    have := natToks_last a
    simp only [hlen, Nat.add_sub_cancel] at this
    exact this
  apply ffind_eq (by omega) (lt_of_tc_ne (by omega)) (by simp [hsep])
  intro j hj1 hj2
  have := hd (j - s) (by omega)
  rw [show s + (j - s) = j by omega] at this
  rw [this]; cases a.testBit (j - s) <;> simp

/-- **Comparison of encoded numbers.** -/
lemma numLt_iff {s t a b : ℕ} {r r' : List Tok} (hs : ts.drop s = natToks a ++ r)
    (ht : ts.drop t = natToks b ++ r') : NumLt ts s t ↔ a < b := by
  obtain ⟨hs1, hs2⟩ := natToks_nE hs
  obtain ⟨ht1, ht2⟩ := natToks_nE ht
  unfold NumLt
  rw [hs1, ht1, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, lt_iff_size_bits a b]
  apply or_congr Iff.rfl
  apply and_congr_right
  intro hab
  apply exists_congr
  intro m
  apply and_congr_right
  intro hm
  rw [hs2 m hm, ht2 m (by omega)]
  have hk : ∀ k < a.size, (tc ts (s + k) = tc ts (t + k) ↔ a.testBit k = b.testBit k) := by
    intro k hk
    rw [hs2 k hk, ht2 k (by omega)]
    cases a.testBit k <;> cases b.testBit k <;> simp
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, fun k hk1 hk2 => (hk k hk1).1 (h3 k hk1 hk2)⟩
    · cases h : a.testBit m <;> simp_all
    · cases h : b.testBit m <;> simp_all
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by simp [h1], by simp [h2], fun k hk1 hk2 => (hk k hk1).2 (h3 k hk1 hk2)⟩

/-! ## Letters -/

section Letter

variable {j v : ℕ} (hj : tc ts j = 3) (hv : tc ts v = 4)
  (hin : ∀ k, j < k → k < v → tc ts k ≤ 2)
  (hsep : ∀ k, j < k → k < v → tc ts k = 2 → tc ts (k - 1) ≠ 0)
  (hv1 : tc ts (v - 1) = 2 ∨ tc ts (v - 1) = 3)
  (hN : ∀ s, j < s → s < v → NumOK ts s)
include hj hv hin hsep hv1 hN

/-- **The numbers of a letter.** -/
theorem nums_parse : ∀ m k, v - k = m → j < k → k ≤ v → (k = j + 1 ∨ tc ts (k - 1) = 2) →
    ∃ xs : List ℕ, xs.Pairwise (· < ·) ∧ ts.drop k = xs.flatMap natToks ++ ts.drop v := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hm hjk hkv hk1
    rcases Nat.eq_or_lt_of_le hkv with hkv' | hkv'
    · exact ⟨[], by simp, by rw [hkv']; simp⟩
    have hvn : v < ts.length := lt_of_tc_ne (by omega)
    have htk := hin k hjk hkv'
    have hv2 : tc ts (v - 1) = 2 := by
      rcases hv1 with h | h
      · exact h
      · have := hin (v - 1) (by omega) (by omega); omega
    obtain ⟨he1, he2, he3, he4⟩ := ffind_spec (fun u => tc ts u == 2) (show k ≤ ts.length by omega)
    set e := ffind (fun u => tc ts u == 2) k ts.length with he
    have hev : e < v := by
      by_contra hc
      have := he4 (v - 1) (by omega) (by omega)
      simp [hv2] at this
    have hte : tc ts e = 2 := by have := he3 (by omega); simpa using this
    have hdig : ∀ u, k ≤ u → u < e → tc ts u ≤ 1 := fun u h1 h2 => by
      have := he4 u h1 h2
      have := hin u (by omega) (by omega)
      simp at *; omega
    have hcan : e = k ∨ tc ts (e - 1) = 1 := by
      rcases Nat.eq_or_lt_of_le he1 with h | h
      · left; exact h.symm
      · right
        have := hdig (e - 1) (by omega) (by omega)
        have := hsep e (by omega) hev hte
        omega
    obtain ⟨a, ha, -, -, -⟩ := digits_parse he1 hdig hte hcan
    obtain ⟨xs, hxs, hd⟩ := ih (v - (e + 1)) (by omega) (e + 1) rfl (by omega) (by omega)
      (by right; simpa using hte)
    refine ⟨a :: xs, ?_, by rw [ha, hd]; simp⟩
    rw [List.pairwise_cons]
    refine ⟨?_, hxs⟩
    cases xs with
    | nil => simp
    | cons x xs =>
      have hx : ts.drop (e + 1) = natToks x ++ (xs.flatMap natToks ++ ts.drop v) := by
        simpa using hd
      have hev1 : e + 1 < v := by
        by_contra hc
        have hle : e + 1 = v := by omega
        rw [hle] at hx
        have := congrArg List.length hx
        simp [natToks] at this
        omega
      have hax : a < x := by
        have hok := hN k hjk hkv' ⟨htk, by
          rcases hk1 with h | h
          · right; rw [h, Nat.add_sub_cancel]; exact hj
          · left; exact h⟩ (hin (e + 1) (by omega) hev1)
        exact (numLt_iff ha hx).1 hok
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hax
      · exact lt_trans hax ((List.pairwise_cons.1 hxs).1 y hy)

/-- **Letters.** -/
theorem letter_parse (hjv : j < v) : ∃ S : Finset ℕ, ts.drop j = finsetToks S ++ ts.drop (v + 1) := by
  obtain ⟨xs, hxs, hd⟩ := nums_parse hj hv hin hsep hv1 hN _ (j + 1) rfl (by omega) (by omega)
    (Or.inl rfl)
  have hnd : xs.Nodup := hxs.imp (fun h => ne_of_lt h)
  refine ⟨xs.toFinset, ?_⟩
  have hvn : v < ts.length := lt_of_tc_ne (by omega)
  rw [drop_of_tc (t := Tok.lpar) hj, hd, drop_of_tc (t := Tok.rpar) hv, finsetToks,
    (List.toFinset_sort (· ≤ ·) hnd).2 (hxs.imp le_of_lt)]
  simp

end Letter

/-! ## Groups -/

lemma Lr_congr {b c : ℕ} {g g' : Prop} (h : g ↔ g') : Lr b c g ↔ Lr b c g' := by
  unfold Lr; rw [h]

/-- **Groups of letters.** -/
theorem group_parse {G E : ℕ} (hG : tc ts G = 3) (hGE : G < E) (hE : tc ts E = 4)
    (hE1 : tc ts (E - 1) = 4 ∨ E - 1 = G)
    (hL : ∀ k, G < k → k < E → Lr (tc ts (k - 1)) (tc ts k) (k - 1 = G))
    (hN : ∀ s, G < s → s < E → NumOK ts s) :
    ∃ Ls : List (Finset ℕ), ts.drop G = Tok.lpar :: (lettersToks Ls ++ Tok.rpar :: ts.drop (E + 1)) := by
  have hEn : E < ts.length := lt_of_tc_ne (by omega)
  have claim : ∀ m k, E - k = m → G < k → k ≤ E → (tc ts (k - 1) = 4 ∨ k - 1 = G) →
      ∃ Ls : List (Finset ℕ), ts.drop k = lettersToks Ls ++ ts.drop E := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hm hGk hkE hk1
      rcases Nat.eq_or_lt_of_le hkE with hkE' | hkE'
      · exact ⟨[], by rw [hkE']; rfl⟩
      obtain ⟨hc4, hc3, hc4', hc2, -⟩ := hL k hGk hkE'
      have hb : tc ts (k - 1) = 4 ∨ (tc ts (k - 1) = 3 ∧ k - 1 = G) := by
        rcases hk1 with h | h
        · left; exact h
        · right; exact ⟨by rw [h]; exact hG, h⟩
      have htk : tc ts k = 3 := by
        by_contra hne
        rcases (show tc ts k = 4 ∨ tc ts k ≤ 2 by omega) with h | h
        · rcases hc4' h with h' | ⟨h', h''⟩ <;> rcases hb with hb | ⟨hb, hb'⟩ <;> omega
        · rcases hc2 h with h' | ⟨h', h''⟩ <;> rcases hb with hb | ⟨hb, hb'⟩ <;> omega
      obtain ⟨hv1', hv2', hv3', hv4'⟩ :=
        ffind_spec (fun u => tc ts u == 4) (show k + 1 ≤ ts.length by omega)
      set v := ffind (fun u => tc ts u == 4) (k + 1) ts.length with hvdef
      have hvE : v ≤ E := by
        by_contra hc
        have := hv4' E (by omega) (by omega)
        simp [hE] at this
      have hvn : v < ts.length := by omega
      have htv : tc ts v = 4 := by have := hv3' hvn; simpa using this
      have hin : ∀ u, k < u → u < v → tc ts u ≤ 2 := by
        intro u
        induction u using Nat.strong_induction_on with
        | _ u ihu =>
          intro hku huv
          have h4 : tc ts u ≠ 4 := by have := hv4' u (by omega) huv; simpa using this
          obtain ⟨hu4, hu3, -, -, -⟩ := hL u (by omega) (by omega)
          by_contra hc
          have h3 : tc ts u = 3 := by omega
          have hprev : tc ts (u - 1) ≤ 3 := by
            rcases Nat.eq_or_lt_of_le (show k ≤ u - 1 by omega) with h | h
            · rw [← h, htk]
            · have := ihu (u - 1) (by omega) h (by omega); omega
          rcases hu3 h3 with h' | ⟨-, h'⟩ <;> omega
      have hvE' : v < E := by
        rcases Nat.eq_or_lt_of_le hvE with h | h
        · exfalso
          rw [← h] at hE1
          rcases hE1 with h' | h'
          · rcases Nat.eq_or_lt_of_le (show k ≤ v - 1 by omega) with h'' | h''
            · rw [← h''] at h'; omega
            · have := hin (v - 1) h'' (by omega); omega
          · omega
        · exact h
      obtain ⟨S, hS⟩ := letter_parse htk htv hin
        (fun u h1 h2 h3 => by have := (hL u (by omega) (by omega)).2.2.2.2; exact this h3)
        (by
          obtain ⟨-, -, h4, -, -⟩ := hL v (by omega) hvE'
          rcases h4 htv with h | ⟨h, -⟩
          · left; exact h
          · right; exact h)
        (fun s h1 h2 => hN s (by omega) (by omega)) (by omega)
      obtain ⟨Ls, hLs⟩ := ih (E - (v + 1)) (by omega) (v + 1) rfl (by omega) (by omega)
        (by left; simpa using htv)
      exact ⟨S :: Ls, by rw [hS, hLs, lettersToks_cons, List.append_assoc]⟩
  obtain ⟨Ls, hLs⟩ := claim _ (G + 1) rfl (by omega) (by omega) (by right; simp)
  refine ⟨Ls, ?_⟩
  rw [drop_of_tc (t := Tok.lpar) hG, hLs, drop_of_tc (t := Tok.rpar) hE]

/-! ## Paths -/

/-- **Soundness of the path conditions.** -/
theorem pathOK_sound (h : PathOK ts) : ∃ p : LassoPath, ts.drop (tP ts) = p.toks := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hL, hN⟩ := h
  obtain ⟨S, hS⟩ := group_parse h1 h2 h3 h4
    (fun k hk1 hk2 => (Lr_congr (by omega)).1 (hL k (by omega) hk1 (by omega) (by omega)))
    (fun s hs1 hs2 => hN s (by omega) hs1)
  obtain ⟨L, hL'⟩ := group_parse (G := sE ts + 1) (E := ts.length - 1) h5 (by omega) h8
    (by left; rw [show ts.length - 1 - 1 = ts.length - 2 by omega]; exact h9)
    (fun k hk1 hk2 => (Lr_congr (by omega)).1 (hL k hk2 (by omega) (by omega) (by omega)))
    (fun s hs1 hs2 => hN s (by omega) (by omega))
  rw [show ts.length - 1 + 1 = ts.length by omega, List.drop_length] at hL'
  have hne : L ≠ [] := by
    rintro rfl
    have : ts.drop (sE ts + 1 + 1) = Tok.rpar :: [] := by
      simpa using drop_succ_of_drop hL'
    have := tc_of_drop this
    rw [show sE ts + 1 + 1 = sE ts + 2 by omega, h6] at this
    simp [Tok.code] at this
  refine ⟨⟨S, L, hne⟩, ?_⟩
  rw [lassoPath_toks, hS, hL']

end LTok

end PathChecking
