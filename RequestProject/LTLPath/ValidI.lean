module

public import RequestProject.LTLPath.ValidComp

/-!
# Local recognition of encoded instances

`ValidI ts` (formula conditions `FormOK` and path conditions `PathOK`) holds iff `ts` is the
token encoding `( φ ) p` of an LTL formula `φ` and a lasso path `p` (`validI_iff`).
-/

@[expose] public section

namespace PathChecking

namespace LTok

open CTLP LS MCVPReduction

variable (ts : List Tok)

/-- The formula part of the input is well formed. -/
def FormOK : Prop :=
  tc ts 0 = 3 ∧ tF ts < ts.length ∧ tc ts (tF ts) = 4 ∧
    ¬ (tc ts (tF ts - 1) ≤ 1 ∨ tc ts (tF ts - 1) = 5) ∧
    ∀ j < tF ts, 1 ≤ j → RF (tc ts (j - 1)) (tc ts j)

/-- The input is the encoding of an instance (checked locally). -/
def ValidI : Prop := FormOK ts ∧ PathOK ts

variable {ts}

/-! ## Soundness -/

theorem formOK_sound (h : FormOK ts) : ∃ φ : LTL, ts.drop 1 = φ.toks ++ ts.drop (tF ts) := by
  obtain ⟨h0, hn, h4, he, hR⟩ := h
  obtain ⟨fs, hl, hd⟩ := form_parse hn he (fun j h1 h2 => hR j h2 h1) _ 1 1 rfl le_rfl le_rfl rfl
    (by simp [h0])
  obtain ⟨φ, rfl⟩ : ∃ φ, fs = [φ] := by
    rcases fs with _ | ⟨φ, _ | ⟨ψ, fs⟩⟩
    · simp at hl
    · exact ⟨φ, rfl⟩
    · simp at hl
  exact ⟨φ, by simpa using hd⟩

theorem validI_sound (h : ValidI ts) : ∃ (φ : LTL) (p : LassoPath), Enc ts φ p := by
  obtain ⟨hf, hp⟩ := h
  obtain ⟨φ, hφ⟩ := formOK_sound hf
  obtain ⟨p, hpd⟩ := pathOK_sound hp
  refine ⟨φ, p, ?_⟩
  have hts : ts = ts.drop 0 := rfl
  rw [Enc, hts, drop_of_tc (t := Tok.lpar) hf.1, hφ, drop_of_tc (t := Tok.rpar) hf.2.2.1]
  rw [show tF ts + 1 = tP ts from rfl, hpd]

/-! ## Completeness -/

/-- A code that may precede a tag. -/
def Gd (c : ℕ) : Prop := ¬ (c ≤ 1 ∨ c = 5)

/-- The relation `RF` on tokens. -/
def FR (x y : Tok) : Prop := RF x.code y.code

/-- Chain property of the encoding of a formula. -/
def FP (l : List Tok) : Prop :=
  l ≠ [] ∧ ∀ t : Tok, Gd t.code → List.IsChain FR (t :: l) ∧ ∀ x ∈ l.getLast?, Gd x.code

lemma fp_digits : ∀ (ds : List Tok) (t : Tok), (t.code ≤ 1 ∨ t.code = 5) → (∀ d ∈ ds, d.code ≤ 1) →
    List.IsChain FR (t :: ds) := by
  intro ds
  induction ds with
  | nil => intro t _ _; exact List.isChain_singleton t
  | cons d ds ih =>
    intro t ht hd
    have hd0 := hd d (by simp)
    refine List.isChain_cons_cons.2 ⟨?_, ih d (by omega) fun d' hd' => hd d' (by simp [hd'])⟩
    unfold FR RF; omega

lemma fp_ap (a : ℕ) : FP (Tok.tag 0 :: natToks a) := by
  obtain ⟨ds, hds, hd, hlast⟩ := natToks_split a
  refine ⟨by simp, fun t ht => ⟨?_, ?_⟩⟩
  · rw [hds, show t :: Tok.tag 0 :: (ds ++ [Tok.sep]) = t :: ((Tok.tag 0 :: ds) ++ [Tok.sep]) by simp]
    refine List.isChain_cons_cons.2 ⟨?_, ?_⟩
    · have e : (Tok.tag 0).code = 5 := rfl
      unfold FR RF; unfold Gd at ht; rw [e]; omega
    · refine List.isChain_append.2 ⟨fp_digits ds _ (by simp [Tok.code]) hd,
        List.isChain_singleton _, fun x hx y hy => ?_⟩
      simp only [List.head?_cons, Option.mem_def, Option.some_inj] at hy
      subst hy
      rw [List.getLast?_cons, Option.mem_def, Option.some_inj] at hx
      have hx' : x.code = 1 ∨ x.code = 5 := by
        cases hds' : ds.getLast? with
        | none => rw [hds'] at hx; simp at hx; subst hx; right; rfl
        | some z => rw [hds'] at hx; simp at hx; subst hx; left; exact hlast z hds'
      unfold FR RF; rw [code_sep]; omega
  · intro x hx
    rw [hds, List.getLast?_cons, List.getLast?_append] at hx
    simp at hx; subst hx
    unfold Gd; simp

lemma fp_unary (k : Fin 24) (hk : Gd (Tok.tag k).code) (hk2 : (Tok.tag k).code ≤ 10) {l : List Tok}
    (hl : FP l) : FP (Tok.tag k :: l) := by
  obtain ⟨hne, hl⟩ := hl
  refine ⟨by simp, fun t ht => ⟨?_, ?_⟩⟩
  · refine List.isChain_cons_cons.2 ⟨?_, (hl _ hk).1⟩
    unfold FR RF; unfold Gd at ht hk; simp only [Tok.code] at *; omega
  · intro x hx
    rw [List.getLast?_cons] at hx
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 (mt List.getLast?_eq_none_iff.1 hne)
    rw [hz] at hx; simp at hx; subst hx
    exact (hl _ hk).2 _ hz

lemma fp_binary (k : Fin 24) (hk : Gd (Tok.tag k).code) (hk2 : (Tok.tag k).code ≤ 10)
    {l₁ l₂ : List Tok} (h₁ : FP l₁) (h₂ : FP l₂) : FP (Tok.tag k :: (l₁ ++ l₂)) := by
  obtain ⟨hne₁, h₁⟩ := h₁
  obtain ⟨hne₂, h₂⟩ := h₂
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 (mt List.getLast?_eq_none_iff.1 hne₁)
  have hzg : Gd z.code := (h₁ _ hk).2 z hz
  have hc2 := (h₂ z hzg).1
  refine ⟨by simp, fun t ht => ⟨?_, ?_⟩⟩
  · rw [show t :: Tok.tag k :: (l₁ ++ l₂) = (t :: Tok.tag k :: l₁) ++ l₂ by simp]
    refine List.isChain_append.2 ⟨List.isChain_cons_cons.2 ⟨?_, (h₁ _ hk).1⟩,
      (List.isChain_cons.1 hc2).2, fun x hx y hy => ?_⟩
    · unfold FR RF; unfold Gd at ht hk; simp only [Tok.code] at *; omega
    · rw [List.getLast?_cons, List.getLast?_cons, hz] at hx
      simp at hx; subst hx
      exact (List.isChain_cons.1 hc2).1 y hy
  · intro x hx
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 (mt List.getLast?_eq_none_iff.1 hne₂)
    rw [List.getLast?_cons, List.getLast?_append, hw] at hx
    simp at hx; subst hx
    exact (h₂ z hzg).2 _ hw

lemma fp_toks : ∀ φ : LTL, FP φ.toks := by
  intro φ
  induction φ with
  | ap a => exact fp_ap a
  | tt =>
    refine ⟨by simp [LTL.toks], fun t ht => ⟨List.isChain_pair.2 ?_, ?_⟩⟩
    · unfold FR RF; unfold Gd at ht; simp only [Tok.code] at *; omega
    · intro x hx; simp [LTL.toks] at hx; subst hx; unfold Gd; simp [Tok.code]
  | neg φ ih => exact fp_unary 2 (by unfold Gd; simp [Tok.code]) (by simp [Tok.code]) ih
  | and φ ψ ih₁ ih₂ => exact fp_binary 3 (by unfold Gd; simp [Tok.code]) (by simp [Tok.code]) ih₁ ih₂
  | X φ ih => exact fp_unary 4 (by unfold Gd; simp [Tok.code]) (by simp [Tok.code]) ih
  | U φ ψ ih₁ ih₂ => exact fp_binary 5 (by unfold Gd; simp [Tok.code]) (by simp [Tok.code]) ih₁ ih₂

variable {φ : LTL} {p : LassoPath}

theorem formOK_complete (h : Enc ts φ p) : FormOK ts := by
  have hF := enc_tF h
  have hd : ts.drop 0 = (Tok.lpar :: φ.toks) ++ (Tok.rpar :: p.toks) := by rw [h]; simp
  have hlen : ts.length = φ.toks.length + 2 + p.toks.length := by rw [h]; simp; omega
  obtain ⟨hne, hfp⟩ := fp_toks φ
  have hch := (hfp Tok.lpar (by unfold Gd; simp)).1
  have hφ := φ.toks_pos
  refine ⟨?_, by omega, enc_tc_tF h, ?_, fun j hj1 hj2 => ?_⟩
  · rw [show (0 : ℕ) = 0 + 0 from rfl, tc_seg hd (m := 0) (by simp)]; rfl
  · rw [show tF ts - 1 = 0 + φ.toks.length by omega, tc_seg hd (m := φ.toks.length) (by simp)]
    have e : (Tok.lpar :: φ.toks)[φ.toks.length]'(by simp) = φ.toks.getLast hne := by
      rw [List.getLast_eq_getElem]
      obtain ⟨k, hk⟩ : ∃ k, φ.toks.length = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hφ).symm⟩
      simp [hk]
    rw [e]
    exact (hfp Tok.lpar (by unfold Gd; simp)).2 _ (by simp [List.getLast?_eq_some_getLast hne])
  · have e1 := tc_seg hd (m := j - 1) (by simp; omega)
    have e2 := tc_seg hd (m := j) (by simp; omega)
    simp only [Nat.zero_add] at e1 e2
    rw [e1, e2]
    have := List.isChain_iff_getElem.1 hch (j - 1) (by simp; omega)
    simpa [show j - 1 + 1 = j by omega] using this

/-- **Local recognition of instances.** -/
theorem validI_iff : ValidI ts ↔ ∃ (φ : LTL) (p : LassoPath), Enc ts φ p := by
  constructor
  · exact validI_sound
  · rintro ⟨φ, p, h⟩
    exact ⟨formOK_complete h, pathOK_complete h⟩

end LTok

end PathChecking
