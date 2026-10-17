module

public import RequestProject.PTime.HLComp

/-!
# Compiling statements

`cs_correct`: the compiled code of a structured program simulates its runs.
`polytimeComputable_of_hl`: a structured program that computes `f` while all its values stay
polynomially bounded yields a polynomial-time computation of `f`.
-/

@[expose] public section

namespace PathChecking

namespace HL

open PT LS
open scoped LS

variable {N : ℕ} {w : Word} {B : ℕ} {m : ℕ}

/-- Compiled code of a statement. -/
def cs (N : ℕ) : Hs m → PStmt (N + 1)
  | .skip => .skip
  | .set i e => .seq (cx N e m) (clear (rg N i) ⨟ addTo (rg N m) (rg N i)).lift
  | .mset e => .seq (cx N e m) (.seq (copy (rg N m) (rg N (m + 1)) (rg N (m + 2))).lift
      (.seq (curR (rg N (m + 1))) (.seq .mset (curL (rg N m)))))
  | .out b => .out b
  | .seq s t => .seq (cs N s) (cs N t)
  | .ite e s t => .seq (cx N e m) (.ite (.not (.zero (rg N m))) (cs N s) (cs N t))
  | .loop e s => .seq (cx N e m) (.loop (.not (.zero (rg N m))) (.seq (cs N s) (cx N e m)))

/-- Number of temporary registers needed by a statement. -/
def Hs.need : Hs m → ℕ
  | .skip => 0
  | .out _ => 0
  | .set _ e => e.need
  | .mset e => max e.need 3
  | .seq s t => max s.need t.need
  | .ite e s t => max e.need (max s.need t.need)
  | .loop e s => max e.need s.need

lemma cx_run {τ : HSt m} (hB : 31 ≤ B) {e : Ex m} (hn : m + e.need ≤ N + 1) {σ : PSt (N + 1)}
    (hR : Rel N τ σ) (hb : e.Bnd w B τ) : ∃ σ', PEval w B (cx N e m) σ σ' ∧
      σ'.base.reg (rg N m) = e.ev w τ ∧ Rel N τ σ' := by
  obtain ⟨σ', hev, h1, hx, hc, hm, ho⟩ := cx_correct τ hB e m σ le_rfl hn hR hb
  have := Ex.one_le_need e
  exact ⟨σ', hev, h1, hR.of_agree le_rfl (by omega) hx hc hm ho⟩

theorem cs_correct (hB : 31 ≤ B) {s : Hs m} {τ τ' : HSt m} (h : HEval w B s τ τ') :
    m + s.need ≤ N + 1 → ∀ σ : PSt (N + 1), Rel N τ σ →
      ∃ σ', PEval w B (cs N s) σ σ' ∧ Rel N τ' σ' := by
  induction h with
  | skip τ => intro _ σ hR; exact ⟨σ, PEval.skip σ, hR⟩
  | set τ i e hb =>
    intro hN σ hR
    simp only [Hs.need] at hN
    have h1n := Ex.one_le_need e
    obtain ⟨σ1, ev1, h1, hR1⟩ := cx_run hB hN hR hb
    have hi : (i : ℕ) < m := i.isLt
    have hne : rg N m ≠ rg N i := rg_ne (by omega) (by omega) (by omega)
    have H : PAch w B (clear (rg N i) ⨟ addTo (rg N m) (rg N i)).lift σ1 (fun σ2 =>
        σ2.base.reg (rg N i) = e.ev w τ ∧
        (∀ j : Fin m, j ≠ i → σ2.base.reg (rg N j) = σ1.base.reg (rg N j)) ∧ σ2.cur = σ1.cur ∧
        σ2.mem = σ1.mem ∧ σ2.base.out = σ1.base.out) := by
      refine pach_lift (ach_seq (ach_clear _ _ _ (ach_addTo _ _ hne _ _ ?_
        ⟨?_, fun j hj => ?_, rfl, rfl, rfl⟩)))
      · simp [St.setReg_apply, hne, h1]; exact Ex.ev_le hb (by omega)
      · simp [St.setReg_apply, hne, h1]
      · have hj' : rg N j ≠ rg N i := rg_ne (by omega) (by omega) (fun e => hj (Fin.ext e))
        have hj'' : rg N j ≠ rg N m := rg_ne (by omega) (by omega) (by omega)
        simp [St.setReg_apply, hj', hj'']
    obtain ⟨σ2, ev2, h2⟩ := H
    refine ⟨σ2, PEval.seq ev1 ev2, ⟨fun j => ?_, ?_, ?_, ?_⟩⟩
    · by_cases hj : j = i
      · subst hj; rw [h2.1]; simp
      · rw [h2.2.1 j hj, hR1.reg j]; simp [hj]
    · rw [h2.2.2.1, hR1.cur]
    · rw [h2.2.2.2.1, hR1.mem]; rfl
    · rw [h2.2.2.2.2, hR1.out]; rfl
  | mset τ e hb =>
    intro hN σ hR
    simp only [Hs.need] at hN
    obtain ⟨σ1, ev1, h1, hR1⟩ := cx_run hB (by omega) hR hb
    have hva := Ex.ev_le hb (by omega)
    have n01 : rg N m ≠ rg N (m + 1) := rg_ne (by omega) (by omega) (by omega)
    have n02 : rg N m ≠ rg N (m + 2) := rg_ne (by omega) (by omega) (by omega)
    have n12 : rg N (m + 1) ≠ rg N (m + 2) := rg_ne (by omega) (by omega) (by omega)
    have lt1 : ∀ j : Fin m, rg N j ≠ rg N (m + 1) := fun j => rg_ne (by omega) (by omega) (by omega)
    have lt2 : ∀ j : Fin m, rg N j ≠ rg N (m + 2) := fun j => rg_ne (by omega) (by omega) (by omega)
    have lt0 : ∀ j : Fin m, rg N j ≠ rg N m := fun j => rg_ne (by omega) (by omega) (by omega)
    have H : PAch w B (.seq (copy (rg N m) (rg N (m + 1)) (rg N (m + 2))).lift
        (.seq (curR (rg N (m + 1))) (.seq .mset (curL (rg N m))))) σ1 (Rel N { τ with mem := insert (e.ev w τ) τ.mem }) := by
      refine pach_seq (pach_lift (ach_copy _ _ _ n01 n02 n12 _ _ (by rw [h1]; exact hva) ?_))
      refine pach_seq (pach_curR _ _ _ ?_ fun τ2 e1 e2 e3 => ?_)
      · simp [St.setReg_apply, n12, h1, hR1.cur]; exact hva
      refine pach_seq (pach_mset (pach_curL _ _ _ fun τ3 f1 f2 f3 => ⟨fun j => ?_, ?_, ?_, ?_⟩))
      · rw [f1, e1]; simp [St.setReg_apply, lt0 j, lt1 j, lt2 j, hR1.reg j]
      · rw [f2, e2, e1]; simp [St.setReg_apply, n01, n02, n12, h1, hR1.cur]
      · rw [f3, e2, e3]; simp [St.setReg_apply, n12, h1, hR1.cur, hR1.mem]
      · rw [f1, e1]; simp [hR1.out]
    obtain ⟨σ2, ev2, hR2⟩ := H
    exact ⟨σ2, PEval.seq ev1 ev2, hR2⟩
  | out τ b =>
    intro _ σ hR
    exact ⟨_, PEval.out σ b, ⟨fun j => hR.reg j, hR.cur, hR.mem, by simp [hR.out]⟩⟩
  | seq _ _ ih1 ih2 =>
    intro hN σ hR
    simp only [Hs.need] at hN
    obtain ⟨σ1, ev1, hR1⟩ := ih1 (by omega) σ hR
    obtain ⟨σ2, ev2, hR2⟩ := ih2 (by omega) σ1 hR1
    exact ⟨σ2, PEval.seq ev1 ev2, hR2⟩
  | iteT hb hc _ ih =>
    intro hN σ hR
    simp only [Hs.need] at hN
    obtain ⟨σ1, ev1, h1, hR1⟩ := cx_run hB (by omega) hR hb
    obtain ⟨σ2, ev2, hR2⟩ := ih (by omega) σ1 hR1
    exact ⟨σ2, PEval.seq ev1 (PEval.iteT (by simp [PCond.eval, h1, hc]) ev2), hR2⟩
  | iteF hb hc _ ih =>
    intro hN σ hR
    simp only [Hs.need] at hN
    obtain ⟨σ1, ev1, h1, hR1⟩ := cx_run hB (by omega) hR hb
    obtain ⟨σ2, ev2, hR2⟩ := ih (by omega) σ1 hR1
    exact ⟨σ2, PEval.seq ev1 (PEval.iteF (by simp [PCond.eval, h1, hc]) ev2), hR2⟩
  | loopT hb hc _ _ ihs ihl =>
    intro hN σ hR
    have hN' := hN
    simp only [Hs.need] at hN'
    obtain ⟨σa, eva, ha, hRa⟩ := cx_run hB (by omega) hR hb
    obtain ⟨σb, evb, hRb⟩ := ihs (by omega) σa hRa
    obtain ⟨σ', ev', hR'⟩ := ihl hN σb hRb
    simp only [cs] at ev'
    cases ev' with
    | seq evc evl =>
      exact ⟨σ', PEval.seq eva (PEval.loopT (by simp [PCond.eval, ha, hc]) (PEval.seq evb evc) evl),
        hR'⟩
  | loopF hb hc =>
    intro hN σ hR
    simp only [Hs.need] at hN
    obtain ⟨σa, eva, ha, hRa⟩ := cx_run hB (by omega) hR hb
    exact ⟨σa, PEval.seq eva (PEval.loopF (by simp [PCond.eval, ha, hc])), hRa⟩

/-- Initial state of structured programs. -/
def HSt.init (m : ℕ) : HSt m := ⟨fun _ => 0, ∅, []⟩

lemma rel_init : Rel N (HSt.init m) (PSt.init (N + 1)) :=
  ⟨fun _ => rfl, rfl, rfl, rfl⟩

/-- **Structured programs with polynomially bounded values compute polynomial-time
functions.** -/
theorem polytimeComputable_of_hl (s : Hs m) (f : Word → Word) (B : Word → ℕ) (c : ℕ)
    (hB : ∀ w, B w ≤ c * (w.length + 1) ^ c) (hB31 : ∀ w, 31 ≤ B w)
    (hs : ∀ w, ∃ τ', HEval w (B w) s (HSt.init m) τ' ∧ τ'.out = f w) :
    PolytimeComputable f := by
  refine polytimeComputable_of_pprog (cs (m + s.need) s) f B c hB fun w => ?_
  obtain ⟨τ', hev, hout⟩ := hs w
  obtain ⟨σ', ev', hR'⟩ := cs_correct (N := m + s.need) (hB31 w) hev (by omega) _ rel_init
  exact ⟨σ', ev', by rw [hR'.out, hout]⟩

end HL

end PathChecking
