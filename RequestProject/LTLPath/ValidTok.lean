module

public import RequestProject.LTLPath.TokFT
public import RequestProject.CTLStarP.ValidProof
public import RequestProject.LTLPath.FDLib

/-!
# Local recognition of encoded instances: formulas

`RF prev cur` is a condition on consecutive token codes of the formula part.  If it holds at all
positions of `[1, tF)`, the formula part parses as a formula (`form_sound`).
-/

@[expose] public section

namespace PathChecking

namespace LTok

open CTLP LS MCVPReduction

variable {ts : List Tok}

lemma getD_bits (a m : ℕ) : (Nat.bits a).getD m false = a.testBit m := by
  induction a using Nat.binaryRec generalizing m with
  | zero => simp
  | bit b n ih =>
    by_cases h : n = 0 ∧ b = false
    · obtain ⟨rfl, rfl⟩ := h; simp
    · rw [Nat.bits_append_bit _ _ (fun hn => by subst hn; cases b <;> simp_all)]
      cases m with
      | zero => simp
      | succ m => simp [Nat.testBit_bit_succ, ← ih, List.getD_eq_getElem?_getD]

lemma ffind_spec (P : ℕ → Bool) {a n : ℕ} (han : a ≤ n) :
    a ≤ ffind P a n ∧ ffind P a n ≤ n ∧ (ffind P a n < n → P (ffind P a n) = true) ∧
      ∀ j, a ≤ j → j < ffind P a n → P j = false := by
  unfold ffind
  obtain ⟨h1, h2⟩ := FD.findF_spec (n - a) (fun m => if P (a + m) then 1 else 0)
  have h3 := FE.findF_le (n - a) (fun m => if P (a + m) then 1 else 0)
  refine ⟨by omega, by omega, fun h => ?_, fun j hj1 hj2 => ?_⟩
  · have := h1 (by omega); simpa using this
  · have := h2 (j - a) (by omega) (by omega)
    simp only [show a + (j - a) = j by omega] at this
    simpa using this

/-- A run of digits. -/
lemma drop_digits : ∀ k s, (∀ u, s ≤ u → u < s + k → tc ts u ≤ 1) →
    ts.drop s = (List.range k).map (fun m => digitTok (decide (tc ts (s + m) = 1))) ++
      ts.drop (s + k) := by
  intro k
  induction k with
  | zero => intro s _; simp
  | succ k ih =>
    intro s hd
    have h0 := hd s le_rfl (by omega)
    have hlt : s < ts.length := lt_of_tc_ne (by omega)
    have e : ts.drop s = digitTok (decide (tc ts s = 1)) :: ts.drop (s + 1) := by
      apply drop_of_tc
      rcases (show tc ts s = 0 ∨ tc ts s = 1 by omega) with h | h <;> simp [h, digitTok, Tok.code]
    rw [e, ih (s + 1) (fun u h1 h2 => hd u (by omega) (by omega)), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero, List.cons_append]
    congr 2
    · simp only [Function.comp_def]
      exact List.map_congr_left fun m _ => by rw [Nat.add_assoc, Nat.add_comm 1 m]
    · rw [show s + 1 + k = s + (k + 1) by omega]

/-- **Canonical numbers.** -/
lemma digits_parse {s e : ℕ} (hse : s ≤ e) (hd : ∀ u, s ≤ u → u < e → tc ts u ≤ 1)
    (he : tc ts e = 2) (hc : e = s ∨ tc ts (e - 1) = 1) :
    ∃ a, ts.drop s = natToks a ++ ts.drop (e + 1) ∧ (natToks a).length = e + 1 - s ∧
      (∀ m, m < e - s → tc ts (s + m) = (a.testBit m).toNat) ∧
      (∀ m, e - s ≤ m → a.testBit m = false) := by
  set bs := (List.range (e - s)).map (fun m => decide (tc ts (s + m) = 1))
  have hcan : Canon bs := by
    by_cases hes : e = s
    · left; simp [bs, hes]
    · right
      have h : tc ts (e - 1) = 1 := hc.resolve_left hes
      obtain ⟨k, hk⟩ : ∃ k, e - s = k + 1 := ⟨e - s - 1, by omega⟩
      simp only [bs, hk, List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.getLast?_append, List.getLast?_singleton]
      simp [show s + k = e - 1 by omega, h]
  have hdrop := drop_digits (e - s) s (fun u h1 h2 => hd u h1 (by omega))
  rw [show s + (e - s) = e by omega] at hdrop
  have he' : ts.drop e = Tok.sep :: ts.drop (e + 1) := drop_of_tc (by rw [he]; rfl)
  refine ⟨ofBits bs, ?_, ?_, ?_, ?_⟩
  · rw [natToks_eq, bits_ofBits hcan, hdrop, he']
    simp [bs, List.map_map, Function.comp_def]
  · rw [natToks_eq, bits_ofBits hcan]; simp [bs]; omega
  · intro m hm
    rw [← getD_bits, bits_ofBits hcan]
    simp only [bs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm,
      Option.map_some, Option.getD_some]
    have := hd (s + m) (by omega) (by omega)
    rcases (show tc ts (s + m) = 0 ∨ tc ts (s + m) = 1 by omega) with h | h <;> simp [h]
  · intro m hm
    rw [← getD_bits, bits_ofBits hcan]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [bs]; omega)]; rfl

/-! ## Formulas -/

/-- Condition on consecutive codes inside the formula. -/
def RF (prev cur : ℕ) : Prop :=
  (cur ≤ 1 ∧ (prev ≤ 1 ∨ prev = 5)) ∨ (cur = 2 ∧ (prev = 1 ∨ prev = 5)) ∨
    (5 ≤ cur ∧ cur ≤ 10 ∧ ¬ (prev ≤ 1 ∨ prev = 5))

/-- Code of `Tok.tag k`. -/
lemma tc_tag {p k : ℕ} (hk : k < 24) (h : tc ts p = 5 + k) :
    ts.drop p = Tok.tag ⟨k, hk⟩ :: ts.drop (p + 1) := drop_of_tc (by rw [h]; rfl)

section

variable {F : ℕ} (hFn : F < ts.length) (hF4 : tc ts F = 4)
  (hFe : ¬ (tc ts (F - 1) ≤ 1 ∨ tc ts (F - 1) = 5))
  (hR : ∀ j, 1 ≤ j → j < F → RF (tc ts (j - 1)) (tc ts j))
include hFn hF4 hFe hR

/-- **Parsing the formula part.** -/
theorem form_parse : ∀ m j c, F - j = m → 1 ≤ j → 1 ≤ c → scan ts upF downF j c = F →
    ¬ (tc ts (j - 1) ≤ 1 ∨ tc ts (j - 1) = 5) →
    ∃ fs : List LTL, fs.length = c ∧ ts.drop j = fs.flatMap LTL.toks ++ ts.drop F := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro j c hm hj hc hs hinv
    have hjn : j < ts.length := by
      by_contra h
      rw [scan_eq, if_pos (by omega)] at hs; omega
    have hjF : j < F := by have := lt_scan (ts := ts) upF downF c hjn; omega
    have hr := hR j hj hjF
    rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, -⟩
    · exact absurd h2 hinv
    · exact absurd (by omega) hinv
    obtain ⟨k, hk⟩ : ∃ k, tc ts j = 5 + k := ⟨tc ts j - 5, by omega⟩
    have hk6 : k ≤ 5 := by omega
    have hdj := tc_tag (show k < 24 by omega) hk
    interval_cases k
    · -- ap
      have hfs := ffind_spec (fun u => decide (1 < tc ts u)) (show j + 1 ≤ ts.length by omega)
      set e := ffind (fun u => decide (1 < tc ts u)) (j + 1) ts.length
      obtain ⟨he1, he2, he3, he4⟩ := hfs
      have hdig : ∀ u, j + 1 ≤ u → u < e → tc ts u ≤ 1 := fun u h1 h2 => by
        have := he4 u h1 h2; simpa using this
      have heF : e < F := by
        by_contra hcon
        rcases Nat.eq_or_lt_of_le (show j + 1 ≤ F by omega) with h' | h'
        · rw [← h', Nat.add_sub_cancel, hk] at hFe; simp at hFe
        · exact hFe (Or.inl (hdig (F - 1) (by omega) (by omega)))
      have hte : 1 < tc ts e := by have := he3 (by omega); simpa using this
      have hre := hR e (by omega) heF
      have hprev : tc ts (e - 1) ≤ 1 ∨ tc ts (e - 1) = 5 := by
        rcases Nat.eq_or_lt_of_le he1 with h' | h'
        · right; rw [← h', Nat.add_sub_cancel, hk]
        · left; exact hdig (e - 1) (by omega) (by omega)
      have hte2 : tc ts e = 2 ∧ (tc ts (e - 1) = 1 ∨ tc ts (e - 1) = 5) := by
        rcases hre with ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨_, _, h3⟩
        · omega
        · exact ⟨h1, h2⟩
        · exact absurd hprev h3
      have hcan : e = j + 1 ∨ tc ts (e - 1) = 1 := by
        rcases hte2.2 with h | h
        · right; exact h
        · left; by_contra hne; have := hdig (e - 1) (by omega) (by omega); omega
      obtain ⟨a, ha, hal, -, -⟩ := digits_parse he1 hdig hte2.1 hcan
      rw [scan_neutral (by omega) hjn (by rw [hk]; rfl) (by rw [hk]; rfl)] at hs
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      rw [scan_natToks a (digits_neutral_F _) rfl rfl ha, hal,
        show j + 1 + (e + 1 - (j + 1)) = e + 1 by omega] at hs
      split_ifs at hs with hc'
      · subst hc'
        refine ⟨[LTL.ap a], rfl, ?_⟩
        rw [hdj, ha, hs]; simp [LTL.toks]
      · obtain ⟨fs, hl, he⟩ := ih _ (by omega) (e + 1) c' rfl (by omega) (by omega) hs
          (by simp [hte2.1])
        refine ⟨LTL.ap a :: fs, by simp [hl], ?_⟩
        rw [hdj, ha, he]; simp [LTL.toks]
    · -- tt
      have hd : downF (tc ts j) = true := by rw [hk]; rfl
      have hu : upF (tc ts j) = false := by rw [hk]; rfl
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      rw [scan_down hjn hu hd] at hs
      split_ifs at hs with hc'
      · subst hc'
        exact ⟨[LTL.tt], rfl, by rw [hdj, ← hs]; rfl⟩
      · obtain ⟨fs, hl, he⟩ := ih _ (by omega) (j + 1) c' rfl (by omega) (by omega) hs
          (by simp [hk])
        exact ⟨LTL.tt :: fs, by simp [hl], by rw [hdj, he]; rfl⟩
    · -- neg
      rw [scan_neutral (by omega) hjn (by rw [hk]; rfl) (by rw [hk]; rfl)] at hs
      obtain ⟨fs, hl, he⟩ := ih _ (by omega) (j + 1) c rfl (by omega) hc hs (by simp [hk])
      obtain ⟨f, fs', rfl⟩ : ∃ f fs', fs = f :: fs' := by
        cases fs with
        | nil => simp at hl; omega
        | cons f fs' => exact ⟨f, fs', rfl⟩
      exact ⟨LTL.neg f :: fs', by simpa using hl, by rw [hdj, he]; rfl⟩
    · -- and
      rw [scan_up hjn (by rw [hk]; rfl)] at hs
      obtain ⟨fs, hl, he⟩ := ih _ (by omega) (j + 1) (c + 1) rfl (by omega) (by omega) hs
        (by simp [hk])
      obtain ⟨f, g, fs', rfl⟩ : ∃ f g fs', fs = f :: g :: fs' := by
        rcases fs with _ | ⟨f, _ | ⟨g, fs'⟩⟩
        · simp at hl
        · simp at hl; omega
        · exact ⟨f, g, fs', rfl⟩
      exact ⟨LTL.and f g :: fs', by simp at hl ⊢; omega, by rw [hdj, he]; simp [LTL.toks]⟩
    · -- X
      rw [scan_neutral (by omega) hjn (by rw [hk]; rfl) (by rw [hk]; rfl)] at hs
      obtain ⟨fs, hl, he⟩ := ih _ (by omega) (j + 1) c rfl (by omega) hc hs (by simp [hk])
      obtain ⟨f, fs', rfl⟩ : ∃ f fs', fs = f :: fs' := by
        cases fs with
        | nil => simp at hl; omega
        | cons f fs' => exact ⟨f, fs', rfl⟩
      exact ⟨LTL.X f :: fs', by simpa using hl, by rw [hdj, he]; rfl⟩
    · -- U
      rw [scan_up hjn (by rw [hk]; rfl)] at hs
      obtain ⟨fs, hl, he⟩ := ih _ (by omega) (j + 1) (c + 1) rfl (by omega) (by omega) hs
        (by simp [hk])
      obtain ⟨f, g, fs', rfl⟩ : ∃ f g fs', fs = f :: g :: fs' := by
        rcases fs with _ | ⟨f, _ | ⟨g, fs'⟩⟩
        · simp at hl
        · simp at hl; omega
        · exact ⟨f, g, fs', rfl⟩
      exact ⟨LTL.U f g :: fs', by simp at hl ⊢; omega, by rw [hdj, he]; simp [LTL.toks]⟩

end

end LTok

end PathChecking
