module

public import RequestProject.LTLPath.TokFT

/-!
# The formula tree of an encoded instance and its semantics

`tokFT h` is the formula tree with path data of an encoding `ts = ( φ ) p` (given by
`h : Enc ts φ p`), defined by the token-level functions of `TokFT.lean`.  `tokSat` is the
semantics of the subformulas: `tokSat q i` is the truth value at path position `i` of the
subformula encoded at position `q`.  `tokFT_sem` shows that it is a semantics of `tokFT h`, the
root has polarity `false` and `tokSat 1 0` is the truth value of `φ` on `p`.
-/

@[expose] public section

namespace PathChecking

open CTLP

namespace LTok

variable {ts : List Tok} {φ : LTL} {p : LassoPath}

lemma enc_kd_le (h : Enc ts φ p) {q : ℕ} (hq : tnd ts q = true) : tkd ts q ≤ 5 := by
  obtain ⟨ψ, h1, -⟩ := node_sub (enc_at h) hq
  rw [tkd_at h1]; cases ψ <;> simp [LTL.tag]

lemma enc_tF_le (h : Enc ts φ p) : tF ts ≤ ts.length := by
  rw [enc_length h, lB, enc_sE h, tP]; omega

lemma enc_lLen_pos (h : Enc ts φ p) : 1 ≤ lLen ts := by
  rw [enc_lLen h]; exact List.length_pos_iff.2 p.loop_ne

/-- **The formula tree with path data of an encoded instance.** -/
def tokFT (h : Enc ts φ p) : FT where
  toPT := tokPT (enc_at h)
  kd := tkd ts
  lv := lvTok ts
  pol := polTok ts
  s := sLen ts
  ℓ := lLen ts
  N := ts.length
  kd_le := fun _ hq => enc_kd_le h hq
  ar_kd := fun _ _ => rfl
  hℓ := enc_lLen_pos h
  hN := enc_tF_le h

open Classical in
/-- Semantics of the subformula encoded at position `q`. -/
noncomputable def tokSat (ts : List Tok) (p : LassoPath) (q i : ℕ) : Bool :=
  if hq : ∃ ψ, At ts q ψ then decide (LTL.Sat p.letter (Classical.choose hq) i) else false

open Classical in
lemma tokSat_at {q : ℕ} {ψ : LTL} (hq : At ts q ψ) (i : ℕ) :
    tokSat ts p q i = true ↔ LTL.Sat p.letter ψ i := by
  have hex : ∃ ψ, At ts q ψ := ⟨ψ, hq⟩
  have e := at_unique _ _ (Classical.choose_spec hex) hq
  unfold tokSat
  rw [dif_pos hex, decide_eq_true_iff, e]

/-! ## Polarities -/

lemma negAbove_eq (q : ℕ) : negAbove ts q =
    (List.range q).countP (fun r => tnd ts r && tkd ts r == 2 && decide (q < fend ts r)) := by
  unfold negAbove; rw [List.countP_eq_length_filter]

lemma countP_range_succ (P : ℕ → Bool) (q : ℕ) :
    (List.range (q + 1)).countP P = (List.range q).countP P + if P q then 1 else 0 := by
  rw [List.range_succ, List.countP_append]; simp

lemma countP_range_add (P : ℕ → Bool) (a b : ℕ) :
    (List.range (a + b)).countP P = (List.range a).countP P +
      (List.range b).countP (fun r => P (a + r)) := by
  rw [List.range_add, List.countP_append, List.countP_map]; rfl

lemma countP_range_congr {P Q : ℕ → Bool} {q : ℕ} (h : ∀ r < q, P r = Q r) :
    (List.range q).countP P = (List.range q).countP Q :=
  List.countP_congr fun r hr => by rw [h r (List.mem_range.1 hr)]

section

variable (h : Enc ts φ p)
include h

lemma neg_child1 {q : ℕ} (hq : tnd ts q = true) (har : 1 ≤ tar ts q) :
    negAbove ts (q + 1) = negAbove ts q + if tkd ts q = 2 then 1 else 0 := by
  set T := tokPT (enc_at h)
  have hfe : ∀ r, T.fe r = fend ts r := fun _ => rfl
  have hc : q + 1 < fend ts q := by
    rcases (show tar ts q = 1 ∨ tar ts q = 2 by have := T.ar_le q hq; exact (by
      change tar ts q ≤ 2 at this; omega)) with e | e
    · obtain ⟨a, b⟩ := T.un q hq e
      have := T.lt_fe (q + 1) a
      rw [hfe, hfe] at b; rw [hfe] at this; omega
    · obtain ⟨a, b, c⟩ := T.bin q hq e
      have l1 := T.lt_fe (q + 1) a
      have l2 := T.lt_fe _ b
      simp only [PT.c2, hfe] at c l1 l2
      omega
  rw [negAbove_eq, negAbove_eq, countP_range_succ]
  congr 1
  · refine countP_range_congr fun r hr => ?_
    by_cases hr1 : tnd ts r = true
    · have key : (q + 1 < fend ts r ↔ q < fend ts r) := by
        constructor
        · intro h1; omega
        · intro h1
          have := T.fe_le_fe (p := r) (q := q) hr1 hq hr.le h1
          rw [hfe, hfe] at this
          omega
      simp only [hr1, Bool.true_and, key]
    · simp [hr1]
  · simp [hq, hc]

lemma neg_child2 {q : ℕ} (hq : tnd ts q = true) (har : tar ts q = 2) :
    negAbove ts (fend ts (q + 1)) = negAbove ts q := by
  set T := tokPT (enc_at h)
  have hfe : ∀ r, T.fe r = fend ts r := fun _ => rfl
  obtain ⟨a, b, c⟩ := T.bin q hq har
  have l1 := T.lt_fe (q + 1) a
  have l2 := T.lt_fe _ b
  simp only [PT.c2, hfe] at b c l1 l2
  set c2 := fend ts (q + 1)
  have hk : (tkd ts q == 2) = false := by
    unfold tar at har; split_ifs at har <;> simp <;> omega
  rw [negAbove_eq, negAbove_eq, show c2 = (q + 1) + (c2 - (q + 1)) by omega, countP_range_add,
    countP_range_succ]
  rw [show (List.range (c2 - (q + 1))).countP (fun r => tnd ts (q + 1 + r) && tkd ts (q + 1 + r) == 2 &&
      decide (q + 1 + (c2 - (q + 1)) < fend ts (q + 1 + r))) = 0 by
    refine List.countP_eq_zero.2 fun r hr => ?_
    simp only [List.mem_range] at hr
    by_cases hr1 : tnd ts (q + 1 + r) = true
    · have := T.fe_le_fe (p := q + 1) (q := q + 1 + r) a hr1 (by omega) (by rw [hfe]; omega)
      rw [hfe, hfe] at this
      simp [hr1]; omega
    · simp [hr1]]
  simp only [hk, Bool.and_false, Bool.false_and, Bool.false_eq_true, if_false, add_zero]
  refine countP_range_congr fun r hr => ?_
  by_cases hr1 : tnd ts r = true
  · have key : (q + 1 + (c2 - (q + 1)) < fend ts r ↔ q < fend ts r) := by
      constructor
      · intro h1; omega
      · intro h1
        have := T.fe_le_fe (p := r) (q := q) hr1 hq hr.le h1
        rw [hfe, hfe] at this
        omega
    simp only [hr1, Bool.true_and, key]
  · simp [hr1]

end

/-! ## Periodicity -/

lemma letter_periodic (p : LassoPath) {i : ℕ} (hi : p.stem.length ≤ i) :
    p.letter (i + p.loop.length) = p.letter i := by
  rw [letter_eq, letter_eq, if_neg (by omega), if_neg (by omega),
    show i + p.loop.length - p.stem.length = (i - p.stem.length) + p.loop.length by omega,
    Nat.add_mod_right]

lemma sat_periodic (p : LassoPath) : ∀ (ψ : LTL) {i : ℕ}, p.stem.length ≤ i →
    (LTL.Sat p.letter ψ (i + p.loop.length) ↔ LTL.Sat p.letter ψ i) := by
  intro ψ
  induction ψ with
  | ap a => intro i hi; simp only [LTL.Sat, letter_periodic p hi]
  | tt => intro i _; simp [LTL.Sat]
  | neg ψ ih => intro i hi; simp only [LTL.Sat, ih hi]
  | and ψ1 ψ2 ih1 ih2 => intro i hi; simp only [LTL.Sat, ih1 hi, ih2 hi]
  | X ψ ih =>
    intro i hi
    simp only [LTL.Sat]
    rw [show i + p.loop.length + 1 = (i + 1) + p.loop.length by omega, ih (by omega)]
  | U ψ1 ψ2 ih1 ih2 =>
    intro i hi
    simp only [LTL.Sat]
    constructor
    · rintro ⟨k, hk1, hk2⟩
      refine ⟨k, ?_, fun j hj => ?_⟩
      · rw [← ih2 (by omega), show i + k + p.loop.length = i + p.loop.length + k by omega]
        exact hk1
      · rw [← ih1 (by omega), show i + j + p.loop.length = i + p.loop.length + j by omega]
        exact hk2 j hj
    · rintro ⟨k, hk1, hk2⟩
      refine ⟨k, ?_, fun j hj => ?_⟩
      · rw [show i + p.loop.length + k = i + k + p.loop.length by omega, ih2 (by omega)]
        exact hk1
      · rw [show i + p.loop.length + j = i + j + p.loop.length by omega, ih1 (by omega)]
        exact hk2 j hj

/-! ## The semantics -/

lemma at_children {q : ℕ} {ψ : LTL} (hq : At ts q ψ) :
    (∀ χ, ψ = .neg χ ∨ ψ = .X χ → At ts (q + 1) χ) ∧
    (∀ χ1 χ2, ψ = .and χ1 χ2 ∨ ψ = .U χ1 χ2 → At ts (q + 1) χ1 ∧ At ts (fend ts (q + 1)) χ2) := by
  obtain ⟨r, hr⟩ := hq
  refine ⟨fun χ hχ => ?_, fun χ1 χ2 hχ => ?_⟩
  · rcases hχ with rfl | rfl <;>
    · simp only [LTL.toks, List.cons_append] at hr
      exact ⟨_, drop_succ_of_drop hr⟩
  · rcases hχ with rfl | rfl <;>
    · simp only [LTL.toks, List.cons_append, List.append_assoc] at hr
      have hc1 : At ts (q + 1) χ1 := ⟨_, drop_succ_of_drop hr⟩
      refine ⟨hc1, ?_⟩
      rw [fend_at hc1]
      exact ⟨_, drop_append_of_drop (drop_succ_of_drop hr)⟩

/-- **The semantics of the subformulas is a semantics of the formula tree.** -/
theorem tokFT_sem (h : Enc ts φ p) : (tokFT h).Sem (tokSat ts p) := by
  have hφ := enc_at h
  have node : ∀ q, tnd ts q = true → ∃ ψ, At ts q ψ := fun q hq =>
    (node_sub hφ hq).imp fun _ h => h.1
  have bool_iff : ∀ {a b : Bool}, (a = true ↔ b = true) → a = b := fun h => Bool.eq_iff_iff.2 h
  constructor
  · intro q hq har
    show polTok ts (q + 1) = (polTok ts q ^^ decide (tkd ts q = 2))
    unfold polTok
    rw [neg_child1 h hq har]
    by_cases hk : tkd ts q = 2
    · simp only [hk, if_true, decide_true, Bool.xor_true]
      rcases Nat.mod_two_eq_zero_or_one (negAbove ts q) with e | e <;> simp [Nat.add_mod, e]
    · simp [hk]
  · intro q hq har
    show polTok ts (fend ts (q + 1)) = polTok ts q
    unfold polTok; rw [neg_child2 h hq har]
  · intro q i hq hk
    obtain ⟨ψ, hψ⟩ := node q hq
    have hk' : ψ.tag ≤ 1 := by have := tkd_at hψ; change tkd ts q ≤ 1 at hk; omega
    exact bool_iff ((tokSat_at hψ i).trans (enc_lvTok h hψ hk' i).symm)
  · intro q i hq hk
    obtain ⟨ψ, hψ⟩ := node q hq
    have ht := tkd_at hψ
    change tkd ts q = 2 at hk
    cases ψ with
    | neg χ =>
      have hc := (at_children hψ).1 χ (Or.inl rfl)
      have e1 := tokSat_at (p := p) hψ i
      have e2 := tokSat_at (p := p) hc i
      simp only [LTL.Sat] at e1
      cases h1 : tokSat ts p q i <;> cases h2 : tokSat ts p (q + 1) i <;> simp_all
    | _ => simp [LTL.tag] at ht; omega
  · intro q i hq hk
    obtain ⟨ψ, hψ⟩ := node q hq
    have ht := tkd_at hψ
    change tkd ts q = 3 at hk
    cases ψ with
    | and χ1 χ2 =>
      obtain ⟨hc1, hc2⟩ := (at_children hψ).2 χ1 χ2 (Or.inl rfl)
      refine bool_iff ?_
      show _ ↔ (tokSat ts p (q + 1) i && tokSat ts p (fend ts (q + 1)) i) = true
      rw [Bool.and_eq_true, tokSat_at hψ, tokSat_at hc1, tokSat_at hc2]
      rfl
    | _ => simp [LTL.tag] at ht; omega
  · intro q i hq hk
    obtain ⟨ψ, hψ⟩ := node q hq
    have ht := tkd_at hψ
    change tkd ts q = 4 at hk
    cases ψ with
    | X χ =>
      have hc := (at_children hψ).1 χ (Or.inr rfl)
      refine bool_iff ?_
      rw [tokSat_at hψ, tokSat_at hc]
      rfl
    | _ => simp [LTL.tag] at ht; omega
  · intro q i hq hk
    obtain ⟨ψ, hψ⟩ := node q hq
    have ht := tkd_at hψ
    change tkd ts q = 5 at hk
    cases ψ with
    | U χ1 χ2 =>
      obtain ⟨hc1, hc2⟩ := (at_children hψ).2 χ1 χ2 (Or.inr rfl)
      rw [tokSat_at hψ]
      show _ ↔ ∃ k, tokSat ts p (fend ts (q + 1)) (i + k) = true ∧ ∀ j < k, tokSat ts p (q + 1) (i + j) = true
      simp only [tokSat_at hc1, tokSat_at hc2]
      rfl
    | _ => simp [LTL.tag] at ht; omega
  · intro q i hq hi
    obtain ⟨ψ, hψ⟩ := node q hq
    change sLen ts ≤ i at hi
    show tokSat ts p q (i + lLen ts) = tokSat ts p q i
    rw [enc_sLen h] at hi
    refine bool_iff ?_
    rw [tokSat_at hψ, tokSat_at hψ, enc_lLen h]
    exact sat_periodic p ψ hi

lemma tokFT_pol_one (h : Enc ts φ p) : (tokFT h).pol 1 = false := by
  show polTok ts 1 = false
  simp [polTok, negAbove, tnd]

lemma tokSat_root (h : Enc ts φ p) : tokSat ts p 1 0 = true ↔ LTL.Sat p.letter φ 0 :=
  tokSat_at (enc_at h) 0

end LTok

end PathChecking
