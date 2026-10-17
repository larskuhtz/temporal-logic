module

public import RequestProject.PTime.HL
public import RequestProject.PTime.PAch

/-!
# Compiling structured programs into register programs with memory

Variable `i` of a program over `m` variables is kept in register `i`; registers `m, m+1, …`
are temporaries used to evaluate expressions.  `cs_correct`: every run of a program is simulated
by its compiled code.
-/

@[expose] public section

namespace PathChecking

namespace HL

open PT LS
open scoped LS

/-- Register number `i` (meaningful for `i ≤ N`). -/
def rg (N i : ℕ) : Fin (N + 1) := ⟨min i N, by omega⟩

variable {N : ℕ} {w : Word} {B : ℕ} {m : ℕ}

lemma rg_val {i : ℕ} (h : i ≤ N) : (rg N i).val = i := by simp [rg]; omega

lemma rg_ne {i j : ℕ} (hi : i ≤ N) (hj : j ≤ N) (h : i ≠ j) : rg N i ≠ rg N j := by
  intro e; apply h; have := congrArg Fin.val e; rwa [rg_val hi, rg_val hj] at this

lemma ne_rg_of_lt {x : Fin (N + 1)} {i : ℕ} (hx : x.val < i) (hi : i ≤ N) : x ≠ rg N i := by
  intro e; rw [e, rg_val hi] at hx; omega

/-! ## Expressions -/

/-- Code evaluating `e` into register `t` (using registers above `t` as temporaries). -/
def cx (N : ℕ) : Ex m → ℕ → PStmt (N + 1)
  | .var i, t => (copy (rg N i) (rg N t) (rg N (t + 1))).lift
  | .const k, t => (setC (rg N t) k).lift
  | .add a b, t => .seq (cx N a t) (.seq (cx N b (t + 1)) (addTo (rg N (t + 1)) (rg N t)).lift)
  | .sub a b, t => .seq (cx N a t) (.seq (cx N b (t + 1)) (subFrom (rg N t) (rg N (t + 1))).lift)
  | .mul a b, t => .seq (cx N a t) (.seq (cx N b (t + 1))
      (mulInto (rg N t) (rg N (t + 1)) (rg N (t + 2)) (rg N (t + 3)) (rg N (t + 4))).lift)
  | .lt a b, t => .seq (cx N a t) (.seq (cx N b (t + 1)) (ltInto (rg N t) (rg N (t + 1))).lift)
  | .tok a, t => .seq (cx N a t) (readTok (rg N t) (rg N (t + 1)) ⨟ addTo (rg N (t + 1)) (rg N t)).lift
  | .mem a, t => .seq (cx N a t) (.seq (copy (rg N t) (rg N (t + 1)) (rg N (t + 2))).lift
      (.seq (curR (rg N (t + 1))) (.seq (.ite .mem (setC (rg N (t + 1)) 1).lift
        (clear (rg N (t + 1))).lift) (.seq (curL (rg N t)) (addTo (rg N (t + 1)) (rg N t)).lift))))

/-- Number of registers needed to evaluate an expression. -/
def Ex.need : Ex m → ℕ
  | .var _ => 2
  | .const _ => 1
  | .add a b => max (max a.need (b.need + 1)) 2
  | .sub a b => max (max a.need (b.need + 1)) 2
  | .lt a b => max (max a.need (b.need + 1)) 2
  | .mul a b => max (max a.need (b.need + 1)) 5
  | .tok a => max a.need 2
  | .mem a => max a.need 3

lemma Ex.one_le_need (e : Ex m) : 1 ≤ e.need := by
  cases e <;> simp [Ex.need]

lemma Ex.ev_le {σ : HSt m} {e : Ex m} (hb : e.Bnd w B σ) (hB : 30 ≤ B) : e.ev w σ ≤ B := by
  induction e with
  | var i => exact hb
  | const k => exact hb
  | add a b _ _ => exact hb.2.2
  | sub a b iha _ => have := iha hb.1; simp only [Ex.ev]; omega
  | mul a b _ _ => exact hb.2.2
  | lt a b _ _ => simp only [Ex.ev]; split_ifs <;> omega
  | tok a _ => have := rtok_le w (a.ev w σ); simp only [Ex.ev]; omega
  | mem a _ => simp only [Ex.ev]; split_ifs <;> omega

/-- Simulation relation between program states and register states. -/
structure Rel (N : ℕ) (τ : HSt m) (σ : PSt (N + 1)) : Prop where
  reg : ∀ i : Fin m, σ.base.reg (rg N i) = τ.v i
  cur : σ.cur = 0
  mem : σ.mem = τ.mem
  out : σ.base.out = τ.out

/-- Effect of evaluating an expression into register `t`. -/
def Post (N t v : ℕ) (σ σ' : PSt (N + 1)) : Prop :=
  σ'.base.reg (rg N t) = v ∧ (∀ x : Fin (N + 1), x.val < t → σ'.base.reg x = σ.base.reg x) ∧
    σ'.cur = σ.cur ∧ σ'.mem = σ.mem ∧ σ'.base.out = σ.base.out

lemma Rel.of_agree {τ : HSt m} {σ σ' : PSt (N + 1)} (hR : Rel N τ σ) {t : ℕ} (ht : m ≤ t)
    (htN : t ≤ N) (hx : ∀ x : Fin (N + 1), x.val < t → σ'.base.reg x = σ.base.reg x)
    (hc : σ'.cur = σ.cur) (hm : σ'.mem = σ.mem) (ho : σ'.base.out = σ.base.out) :
    Rel N τ σ' :=
  ⟨fun i => by rw [hx _ (by rw [rg_val (by omega)]; omega), hR.reg i],
    by rw [hc, hR.cur], by rw [hm, hR.mem], by rw [ho, hR.out]⟩

/-- Two subexpressions evaluated into `t` and `t + 1`, then a final step. -/
lemma pach_bin {σ : PSt (N + 1)} {t va vb : ℕ} {sa sb fin : PStmt (N + 1)}
    {Q : PSt (N + 1) → Prop} (ht : t + 1 ≤ N)
    (ha : PAch w B sa σ (Post N t va σ))
    (hb : ∀ σ₁, Post N t va σ σ₁ → PAch w B sb σ₁ (Post N (t + 1) vb σ₁))
    (hfin : ∀ σ₂ : PSt (N + 1), σ₂.base.reg (rg N t) = va → σ₂.base.reg (rg N (t + 1)) = vb →
      (∀ x : Fin (N + 1), x.val < t → σ₂.base.reg x = σ.base.reg x) → σ₂.cur = σ.cur →
      σ₂.mem = σ.mem → σ₂.base.out = σ.base.out → PAch w B fin σ₂ Q) :
    PAch w B (.seq sa (.seq sb fin)) σ Q := by
  refine pach_seq (ha.mono fun σ₁ h1 => pach_seq ((hb σ₁ h1).mono fun σ₂ h2 => ?_))
  obtain ⟨h1v, h1x, h1c, h1m, h1o⟩ := h1
  obtain ⟨h2v, h2x, h2c, h2m, h2o⟩ := h2
  refine hfin σ₂ ?_ h2v (fun x hx => by rw [h2x x (by omega), h1x x hx]) (by rw [h2c, h1c])
    (by rw [h2m, h1m]) (by rw [h2o, h1o])
  rw [h2x _ (by rw [rg_val (by omega)]; omega), h1v]

/-- A final register-only step. -/
lemma pach_fin {σ σ₂ : PSt (N + 1)} {t v : ℕ} {s : Stmt (N + 1)}
    (hx : ∀ x : Fin (N + 1), x.val < t → σ₂.base.reg x = σ.base.reg x) (hc : σ₂.cur = σ.cur)
    (hm : σ₂.mem = σ.mem) (ho : σ₂.base.out = σ.base.out)
    (h : Ach w B s σ₂.base (fun b => b.reg (rg N t) = v ∧
      (∀ x : Fin (N + 1), x.val < t → b.reg x = σ₂.base.reg x) ∧ b.out = σ₂.base.out)) :
    PAch w B s.lift σ₂ (Post N t v σ) := by
  refine pach_lift (h.mono fun b ⟨h1, h2, h3⟩ => ⟨h1, fun x hx' => ?_, hc, hm, ?_⟩)
  · simp only; rw [h2 x hx', hx x hx']
  · simp only; rw [h3, ho]

/-- Close register goals. -/
macro "rg_tac" : tactic => `(tactic| (simp (disch := omega) [St.setReg_apply, rg_ne, ne_rg_of_lt, *]))

theorem cx_correct (τ : HSt m) (hB : 31 ≤ B) (e : Ex m) : ∀ (t : ℕ) (σ : PSt (N + 1)),
    m ≤ t → t + e.need ≤ N + 1 → Rel N τ σ → e.Bnd w B τ →
    PAch w B (cx N e t) σ (Post N t (e.ev w τ) σ) := by
  induction e with
  | var i =>
    intro t σ ht hn hR hb
    simp only [Ex.need] at hn
    have hi : (i : ℕ) < t := by omega
    refine pach_lift (ach_copy _ _ _ (rg_ne (by omega) (by omega) (by omega))
      (rg_ne (by omega) (by omega) (by omega)) (rg_ne (by omega) (by omega) (by omega)) _ _
      (by rw [hR.reg i]; exact hb) ⟨?_, fun x hx => ?_, rfl, rfl, rfl⟩)
    · simp [St.setReg_apply, rg_ne (show t ≤ N by omega) (show t + 1 ≤ N by omega) (by omega),
        hR.reg i, Ex.ev]
    · simp [St.setReg_apply, ne_rg_of_lt hx (show t ≤ N by omega),
        ne_rg_of_lt (show x.val < t + 1 by omega) (show t + 1 ≤ N by omega)]
  | const k =>
    intro t σ ht hn hR hb
    simp only [Ex.need] at hn
    refine pach_lift (ach_setC _ _ _ _ hb ⟨by simp [Ex.ev], fun x hx => ?_, rfl, rfl, rfl⟩)
    simp [St.setReg_apply, ne_rg_of_lt hx (show t ≤ N by omega)]
  | add a b iha ihb =>
    intro t σ ht hn hR hb
    simp only [Ex.need] at hn
    obtain ⟨hba, hbb, hsum⟩ := hb
    refine pach_bin (by omega) (iha t σ ht (by omega) hR hba) (fun σ₁ h1 => ihb (t + 1) σ₁
      (by omega) (by omega) (hR.of_agree ht (by omega) h1.2.1 h1.2.2.1 h1.2.2.2.1 h1.2.2.2.2) hbb)
      (fun σ₂ h1 h2 hx hc hm ho => pach_fin hx hc hm ho ?_)
    have hne : rg N (t + 1) ≠ rg N t := rg_ne (by omega) (by omega) (by omega)
    refine ach_addTo _ _ hne _ _ (by rw [h1, h2]; exact hsum) ⟨?_, fun x hx => ?_, rfl⟩
    · simp [St.setReg_apply, h1, h2, Ex.ev]
    · simp [St.setReg_apply, ne_rg_of_lt hx (show t ≤ N by omega),
        ne_rg_of_lt (show x.val < t + 1 by omega) (show t + 1 ≤ N by omega)]
  | sub a b iha ihb =>
    intro t σ ht hn hR hb
    simp only [Ex.need] at hn
    obtain ⟨hba, hbb⟩ := hb
    refine pach_bin (by omega) (iha t σ ht (by omega) hR hba) (fun σ₁ h1 => ihb (t + 1) σ₁
      (by omega) (by omega) (hR.of_agree ht (by omega) h1.2.1 h1.2.2.1 h1.2.2.2.1 h1.2.2.2.2) hbb)
      (fun σ₂ h1 h2 hx hc hm ho => pach_fin hx hc hm ho ?_)
    have hne : rg N t ≠ rg N (t + 1) := rg_ne (by omega) (by omega) (by omega)
    refine ach_subFrom _ _ hne _ _ ⟨?_, fun x hx => ?_, rfl⟩
    · simp [St.setReg_apply, hne, h1, h2, Ex.ev]
    · simp [St.setReg_apply, ne_rg_of_lt hx (show t ≤ N by omega),
        ne_rg_of_lt (show x.val < t + 1 by omega) (show t + 1 ≤ N by omega)]
  | mul a b iha ihb =>
    intro t σ ht hn hR hb
    simp only [Ex.need] at hn
    obtain ⟨hba, hbb, hprod⟩ := hb
    refine pach_bin (by omega) (iha t σ ht (by omega) hR hba) (fun σ₁ h1 => ihb (t + 1) σ₁
      (by omega) (by omega) (hR.of_agree ht (by omega) h1.2.1 h1.2.2.1 h1.2.2.2.1 h1.2.2.2.2) hbb)
      (fun σ₂ h1 h2 hx hc hm ho => pach_fin hx hc hm ho ?_)
    refine ach_mulInto _ _ _ _ _ (rg_ne (by omega) (by omega) (by omega))
      (rg_ne (by omega) (by omega) (by omega)) (rg_ne (by omega) (by omega) (by omega))
      (rg_ne (by omega) (by omega) (by omega)) (rg_ne (by omega) (by omega) (by omega))
      (rg_ne (by omega) (by omega) (by omega)) (rg_ne (by omega) (by omega) (by omega))
      (rg_ne (by omega) (by omega) (by omega)) (rg_ne (by omega) (by omega) (by omega))
      (rg_ne (by omega) (by omega) (by omega)) _ _
      (by rw [h1]; exact Ex.ev_le hba (by omega)) (by rw [h1, h2]; exact hprod) ?_
    intro b e1 e2 e3
    refine ⟨by rw [e1, h1, h2]; rfl, fun x hx => ?_, e2⟩
    exact e3 x (ne_rg_of_lt hx (by omega)) (ne_rg_of_lt (by omega) (by omega))
      (ne_rg_of_lt (by omega) (by omega)) (ne_rg_of_lt (by omega) (by omega))
      (ne_rg_of_lt (by omega) (by omega))
  | lt a b iha ihb =>
    intro t σ ht hn hR hb
    simp only [Ex.need] at hn
    obtain ⟨hba, hbb⟩ := hb
    refine pach_bin (by omega) (iha t σ ht (by omega) hR hba) (fun σ₁ h1 => ihb (t + 1) σ₁
      (by omega) (by omega) (hR.of_agree ht (by omega) h1.2.1 h1.2.2.1 h1.2.2.2.1 h1.2.2.2.2) hbb)
      (fun σ₂ h1 h2 hx hc hm ho => pach_fin hx hc hm ho ?_)
    have hne : rg N t ≠ rg N (t + 1) := rg_ne (by omega) (by omega) (by omega)
    refine ach_ltInto _ _ hne _ _ (by omega) ⟨?_, fun x hx => ?_, rfl⟩
    · simp [St.setReg_apply, hne, h1, h2, Ex.ev]
    · simp [St.setReg_apply, ne_rg_of_lt hx (show t ≤ N by omega),
        ne_rg_of_lt (show x.val < t + 1 by omega) (show t + 1 ≤ N by omega)]
  | tok a iha =>
    intro t σ ht hn hR hb
    simp only [Ex.need] at hn
    refine pach_seq ((iha t σ ht (by omega) hR hb).mono fun σ₁ ⟨h1, hx, hc, hm, ho⟩ =>
      pach_fin hx hc hm ho ?_)
    have hne : rg N t ≠ rg N (t + 1) := rg_ne (by omega) (by omega) (by omega)
    refine ach_seq (ach_readTok _ _ _ _ (by omega) fun pos => ?_)
    refine ach_addTo _ _ (Ne.symm hne) _ _ ?_ ⟨?_, fun x hx => ?_, rfl⟩
    · simp [St.setReg_apply, hne]; have := rtok_le w (σ₁.base.reg (rg N t)); omega
    · simp [St.setReg_apply, hne, h1, Ex.ev]
    · simp [St.setReg_apply, ne_rg_of_lt hx (show t ≤ N by omega),
        ne_rg_of_lt (show x.val < t + 1 by omega) (show t + 1 ≤ N by omega)]
  | mem a iha =>
    intro t σ ht hn hR hb
    simp only [Ex.need] at hn
    have hb' : a.Bnd w B τ := hb
    have hva := Ex.ev_le hb' (by omega)
    set va := a.ev w τ
    have n01 : (rg N t) ≠ (rg N (t + 1)) := rg_ne (by omega) (by omega) (by omega)
    have n02 : (rg N t) ≠ (rg N (t + 2)) := rg_ne (by omega) (by omega) (by omega)
    have n12 : (rg N (t + 1)) ≠ (rg N (t + 2)) := rg_ne (by omega) (by omega) (by omega)
    have lt0 : ∀ x : Fin (N + 1), x.val < t → x ≠ (rg N t) := fun x hx => ne_rg_of_lt hx (by omega)
    have lt1 : ∀ x : Fin (N + 1), x.val < t → x ≠ (rg N (t + 1)) := fun x hx => ne_rg_of_lt (by omega) (by omega)
    have lt2 : ∀ x : Fin (N + 1), x.val < t → x ≠ (rg N (t + 2)) := fun x hx => ne_rg_of_lt (by omega) (by omega)
    refine pach_seq ((iha t σ ht (by omega) hR hb').mono fun σ₁ ⟨h1, hx, hc, hm, ho⟩ => ?_)
    refine pach_seq (pach_lift (ach_copy _ _ _ n01 n02 n12 _ _ (by rw [h1]; exact hva) ?_))
    refine pach_seq (pach_curR _ _ _ ?_ fun τ2 e1 e2 e3 => ?_)
    · simp [St.setReg_apply, n12, h1, hc, hR.cur]; exact hva
    have g0 : τ2.base.reg (rg N t) = va := by
      rw [e1]; simp [St.setReg_apply, n01, n02, h1]
    have gx : ∀ x : Fin (N + 1), x.val < t → τ2.base.reg x = σ.base.reg x := by
      intro x hx'; rw [e1]; simp [St.setReg_apply, lt1 x hx', lt2 x hx', hx x hx']
    have gc : τ2.cur = va := by
      rw [e2]; simp [St.setReg_apply, n12, h1, hc, hR.cur]
    have gm : τ2.mem = σ.mem := by rw [e3, hm]
    have go : τ2.base.out = σ.base.out := by rw [e1]; simp [ho]
    have cont : ∀ v : ℕ, v = (if va ∈ τ.mem then 1 else 0) →
        PAch w B (.seq (curL (rg N t)) (addTo (rg N (t + 1)) (rg N t)).lift) ⟨τ2.base.setReg (rg N (t + 1)) v, τ2.cur, τ2.mem⟩
          (Post N t (Ex.ev w τ (.mem a)) σ) := by
      intro v hv
      refine pach_seq (pach_curL _ _ _ fun τ3 f1 f2 f3 => ?_)
      have k0 : τ3.base.reg (rg N t) = 0 := by rw [f1]; simp
      have k1 : τ3.base.reg (rg N (t + 1)) = v := by rw [f1]; simp [St.setReg_apply, Ne.symm n01]
      refine pach_lift (ach_addTo _ _ (Ne.symm n01) _ _ ?_ ⟨?_, fun x hx' => ?_, ?_, ?_, ?_⟩)
      · rw [k0, k1, hv]; split_ifs <;> omega
      · simp [St.setReg_apply, k0, k1, hv, Ex.ev, va]
      · simp only [St.setReg_apply, if_neg (lt0 x hx'), if_neg (lt1 x hx'), f1]
        simp [gx x hx']
      · simp only; rw [f2]; simp [gc, St.setReg_apply, g0, hR.cur, n01]
      · simp only; rw [f3, gm]
      · simp only; rw [f1]; simp [go]
    refine pach_seq (pach_ite ?_)
    by_cases hin : va ∈ τ.mem
    · rw [if_pos (by simp [PCond.eval, gc, gm, hR.mem, hin])]
      exact pach_lift (ach_setC _ _ _ _ (by omega) (cont 1 (by simp [hin])))
    · rw [if_neg (by simp [PCond.eval, gc, gm, hR.mem, hin])]
      exact pach_lift (ach_clear _ _ _ (cont 0 (by simp [hin])))

end HL

end PathChecking
