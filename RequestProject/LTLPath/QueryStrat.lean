module

public import RequestProject.LTLPath.LGridP
public import RequestProject.LTLPath.QueryOIF

/-!
# The query circuits drawn as stratified circuits

Fix a round with leaf set `S`, queried regions `Qd` and statuses `st` satisfying the closure
invariant.  The query system `qsysR S Qd st h0 β` with the coordinates of
`RequestProject/LTLPath/QueryOIF.lean` (row `QY`, column `QX`) is a layered system
(`FT.qLS_ok`): live gates in the rows `≥ 1` of the region of `h0`, arguments in the same row at
the next column, in the row below at a column in `[QX - 1, QX + 3]`, or frontier constants of the
bottom row; wires between two rows do not cross.

`FT.stratQ` is its grid drawing (`RequestProject/LTLPath/LGrid.lean`).  It is a stratified
monotone planar circuit (`FT.query_strat`) whose value is the value of `h0` in the query system
(`FT.query_strat_eval`).
-/

@[expose] public section

namespace PathChecking

namespace FT

variable {T : FT}

open Classical

/-- The query system as a layered system. -/
noncomputable def qLS (T : FT) (S Qd : ℕ → Prop) (st : ℕ → Option Bool) (h0 : ℕ) (β : Bool) :
    LG.LSys :=
  ⟨T.qsysR S Qd st h0 β, T.live S Qd st h0, T.QX S Qd st h0, fun h => (T.QY S Qd st h0 h).toNat⟩

/-- Bound on the rows. -/
def sM (T : FT) : ℕ := T.N + 1

/-- Bound on the columns. -/
def sC (T : FT) : ℕ := 4 * T.Wm + 2 * T.N + 6

/-- **The stratified query circuit** for gate `h0` and the value `β` of unknown non-live
gates. -/
noncomputable def stratQ (T : FT) (S Qd : ℕ → Prop) (st : ℕ → Option Bool) (h0 : ℕ) (β : Bool) :
    Circuit :=
  (T.qLS S Qd st h0 β).circ T.sM T.sC h0

variable {S Qd : ℕ → Prop} {st : ℕ → Option Bool} {h0 : ℕ} {β : Bool}

lemma depth_le_F (y : ℕ) : T.depth y ≤ T.F := by
  unfold PT.depth
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma qsysR_live {h : ℕ} (hl : T.live S Qd st h0 h = true) :
    T.qsysR S Qd st h0 β h = ⟨(T.gate h).kind, (T.gate h).args.filter (T.keep S st h)⟩ := by
  unfold qsysR GS.qsys; rw [if_pos hl]

lemma qsysR_dead {h : ℕ} (hl : T.live S Qd st h0 h = false) :
    T.qsysR S Qd st h0 β h = ⟨.const ((st h).getD β), []⟩ := by
  unfold qsysR GS.qsys; rw [if_neg (by simp [hl])]

lemma QY_toNat {h : ℕ} (hl : T.live S Qd st h0 h = true) :
    ((T.QY S Qd st h0 h).toNat : ℤ) = T.QY S Qd st h0 h := by
  have := QY_nonneg (T := T) (S := S) (Qd := Qd) (st := st) (h0 := h0) h
  omega

lemma qLS_bd : (T.qLS S Qd st h0 β).Bd T.sM T.sC := by
  intro h hl
  simp only [qLS] at hl ⊢
  have hA := (live_spec hl).1
  obtain ⟨hh, -, -, -, -⟩ := gate_AO hA
  obtain ⟨-, -, hix, hty⟩ := idx_decode hh
  have hY : (T.QY S Qd st h0 h).toNat ≤ T.N + 1 := by
    rw [QY_live hl]
    unfold lvl
    have := depth_le_F (T := T) (T.rd S h0)
    have := T.hN
    split_ifs <;> omega
  refine ⟨hY, ?_⟩
  unfold LG.LSys.col sC sM
  simp only
  rw [QX_live hl]
  omega

theorem qLS_ok (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) :
    (T.qLS S Qd st h0 β).OK := by
  have hYeq : ∀ a b, T.live S Qd st h0 a = true → T.live S Qd st h0 b = true →
      (T.QY S Qd st h0 a).toNat = (T.QY S Qd st h0 b).toNat →
      T.QY S Qd st h0 a = T.QY S Qd st h0 b := by
    intro a b ha hb e
    have := QY_toNat (T := T) (S := S) (Qd := Qd) (st := st) (h0 := h0) ha
    have := QY_toNat (T := T) (S := S) (Qd := Qd) (st := st) (h0 := h0) hb
    omega
  have hYsucc : ∀ a b, T.live S Qd st h0 a = true → T.live S Qd st h0 b = true →
      ((T.QY S Qd st h0 a).toNat + 1 = (T.QY S Qd st h0 b).toNat ↔
        T.QY S Qd st h0 b = T.QY S Qd st h0 a + 1) := by
    intro a b ha hb
    have := QY_toNat (T := T) (S := S) (Qd := Qd) (st := st) (h0 := h0) ha
    have := QY_toNat (T := T) (S := S) (Qd := Qd) (st := st) (h0 := h0) hb
    omega
  refine ⟨GS.qsys_ordered gate_ordered st _ _ β, fun h hl => ?_, fun h hl => ?_, fun h hl => ?_,
    fun h hl => ?_, fun h hl => ?_, fun h hl x hx => ?_, fun a b ha hb hy hx => ?_,
    fun a a' b b' ha hb ha' hb' hla' hlb' hya hyb hab hx => ?_,
    fun a b ha hb hy hx => ?_⟩
  · simp only [qLS] at hl ⊢
    rw [qsysR_live hl]; exact live_kind S Qd st h0 h hl
  · simp only [qLS] at hl ⊢
    rw [qsysR_live hl]
    obtain ⟨hA, hu, hr⟩ := live_spec hl
    obtain ⟨x, hx, hx'⟩ := (hcl h hA hu hr.1).2
    have hk : T.keep S st h x = true := by
      rcases hx' with h1 | h1 <;> simp [keep, h1]
    exact List.ne_nil_of_mem (List.mem_filter.2 ⟨hx, hk⟩)
  · simp only [qLS] at hl ⊢
    rw [qsysR_live hl]
    exact le_trans (List.length_filter_le _ _) (gate_args_le h)
  · simp only [qLS] at hl ⊢
    exact ⟨_, qsysR_dead hl⟩
  · simp only [qLS] at hl ⊢
    have := lvl_pos hl
    rw [QY_live hl]; omega
  · simp only [qLS] at hl hx ⊢
    have he : T.QE S Qd st h0 h x := mem_qsysR_args.1 hx
    rcases edge_shape hck hd hcl he with ⟨hlx, ⟨e, hyy⟩ | ⟨hc, hyy⟩⟩ | ⟨hlx, -, hy1, -, -⟩
    · left
      exact ⟨hlx, by rw [hyy], same_row_X he hlx e⟩
    · right; left
      refine ⟨hlx, (hYsucc x h hlx hl).2 (by omega), ?_⟩
      obtain ⟨hix, h1, h2, -⟩ := child_X hck hd hcl he (fun e => by have := hc.lt; omega)
      rw [QX_live hl]
      have := ty_le h
      split_ifs at hix <;> omega
    · right; right
      exact ⟨hlx, by rw [hy1]; rfl⟩
  · simp only [qLS] at ha hb hy hx
    exact Q_inj hck hd hcl hx (hYeq a b ha hb hy)
  · simp only [qLS] at ha hb ha' hb' hla' hlb' hya hyb hab hx ⊢
    exact Q_cross hck hd hcl (mem_qsysR_args.1 ha') (mem_qsysR_args.1 hb')
      ((hYsucc a' a hla' ha).1 hya) ((hYsucc b' b hlb' hb).1 hyb) (hYeq a b ha hb hab) hx
  · simp only [qLS] at ha hb hy hx
    have hy' := hYeq a b ha hb hy
    rw [QY_live ha, QY_live hb] at hy'
    have hp := pos_eq_of_lvl ha hb hy'
    rw [QX_live ha, QX_live hb] at hx
    obtain ⟨ea, -, hia, hta⟩ := idx_decode (gate_AO (live_spec ha).1).1
    obtain ⟨eb, -, hib, htb⟩ := idx_decode (gate_AO (live_spec hb).1).1
    rw [← ea, ← eb, hp]
    unfold idx
    generalize (T.N - 1 - T.pos b) * T.Wm = P
    omega

/-- **The stratified query circuits are instances of the stratified monotone planar circuit
value problem.** -/
theorem query_strat (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) :
    StratMCVPInstance (T.stratQ S Qd st h0 β) :=
  LG.LSys.circ_strat (qLS_ok hck hd hcl) qLS_bd h0

/-- **The stratified query circuit computes the value of `h0` in the query system.** -/
theorem query_strat_eval (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) :
    (T.stratQ S Qd st h0 β).eval ∅ [] = GS.val (T.qsysR S Qd st h0 β) h0 :=
  LG.LSys.circ_eval (qLS_ok hck hd hcl) qLS_bd h0

end FT

end PathChecking
