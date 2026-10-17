module

public import RequestProject.LTLPath.FDLGO
public import RequestProject.LTLPath.AssemblyStrat

/-!
# The query function with stratified query circuits

`qProgS` is the output program of the query function of the round algorithm with stratified
queries: it computes the global values of the formula tree, the round number, and then either a
tick circuit or the stratified query circuit `FT.stratQ` of gate `h0` with value `β` for unknown
non-live gates.  The per-gate quantities of the layered query system (`qLC`, `qSem`) are computed
from the terms of the one-input-face query function.  `qFunS_spec` proves the specification
`QSpecS`, and `qFunS_logspace` that the query function is logspace computable.
-/

@[expose] public section

namespace PathChecking

lemma card_filter_range (F : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range F).filter P).card = (List.range F).countP (fun i => decide (P i)) := by
  induction F with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert, List.range_succ, List.countP_append]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), ih]; simp [h]
    · rw [ih]; simp [h]

lemma filter_take_two' (u v n : ℕ) (f : ℕ → Bool) :
    ([u, v].take n).filter f =
      (if (decide (0 < n) && f u) = true then [u] else []) ++
        (if (decide (1 < n) && f v) = true then [v] else []) := by
  rcases n with _ | _ | n
  · simp
  · by_cases hu : f u = true <;> simp [List.filter, hu]
  · by_cases hu : f u = true <;> by_cases hv : f v = true <;> simp [List.filter, hu, hv]

namespace FT

open Classical

/-- The per-gate quantities of the layered query system. -/
noncomputable def qSem (T : FT) (S : ℕ → Prop) (st : ℕ → Option Bool) (h0 : ℕ) (β : Bool) :
    LG.LSem where
  X := fun h => 2 * T.ix h + 1 - ty h
  Y := fun h => T.depth (T.rd S h0) + (if T.leaf (T.rd S h0) = true then 0 else 1) -
    T.depth (T.pos h)
  kc := fun h => kcode (T.gate h).kind
  k0 := fun h => decide (0 < naOf (T.hcase h)) && T.keep S st h (T.a0Of (T.hcase h) (T.pos h) (T.ix h))
  a0 := fun h => T.a0Of (T.hcase h) (T.pos h) (T.ix h)
  k1 := fun h => decide (1 < naOf (T.hcase h)) && T.keep S st h (T.a1Of (T.hcase h) (T.pos h) (T.ix h))
  a1 := fun h => T.a1Of (T.hcase h) (T.pos h) (T.ix h)
  cv := fun h => if oc (st h) = 0 then β.toNat else oc (st h) - 1

variable {T : FT} {S Qd : ℕ → Prop} {st : ℕ → Option Bool} {h0 : ℕ} {β : Bool}

/-- **The quantities describe the layered query system.** -/
theorem qSem_agree : LG.Agree (T.qLS S Qd st h0 β) (T.qSem S st h0 β) T.Ng where
  X := fun h hl => by
    simp only [qLS, qSem] at hl ⊢; rw [QX_live hl]
  Y := fun h hl => by
    simp only [qLS, qSem] at hl ⊢
    have h1 := lvl_pos hl
    rw [QY_live hl]
    unfold lvl at h1 ⊢
    split_ifs at h1 ⊢ <;> omega
  kc := fun h hl => by
    simp only [qLS, qSem] at hl ⊢; rw [qsysR_live hl]
  args := fun h hl => by
    simp only [qLS, qSem] at hl ⊢
    rw [qsysR_live hl]
    simp only
    rw [show (T.gate h).args = _ from (congrArg Gate.args (T.gate_eq h)).trans
      (T.args_gOfCase _ _ _), filter_take_two']
  cv := fun h hl => by
    simp only [qLS, qSem] at hl ⊢
    rw [qsysR_dead hl]
    rcases st h with _ | b <;> simp [oc, LG.cval]
  ng := fun h hl => (gate_AO (live_spec hl).1).1
  kind := fun h hl => by
    simp only [qLS] at hl ⊢; rw [qsysR_live hl]; exact live_kind S Qd st h0 h hl

end FT

namespace FD

open FE LL CTLP LTok Classical

variable {x : Word} {Γ : Ctx} {ts : List Tok} {q : ℕ} {a : List Bool} {g : Gl}

/-- Depth of a node of the formula tree. -/
def depthT (g : Gl) (y : T) : T := countT g.F fun z => AncT g z y

/-- Term builders for the per-gate quantities of the layered query system. -/
def qLC (g : Gl) (St : T → T) (dd q0 K tt β : T) : LC where
  live := fun h => liveT g St dd q0 K tt h
  X := fun h => subT (addT (mulT (cT 2) (ixT g h)) (cT 1)) (tyT h)
  Y := fun h => subT (addT (depthT g dd) (iteT (leafT g dd) (cT 0) (cT 1))) (depthT g (posT g h))
  kc := fun h => kcT g h
  k0 := fun h => andT (ltT (cT 0) (naOfT (hcaseT g h)))
    (keepT g St K tt h (a0OfT g (hcaseT g h) (posT g h) (ixT g h)))
  a0 := fun h => a0OfT g (hcaseT g h) (posT g h) (ixT g h)
  k1 := fun h => andT (ltT (cT 1) (naOfT (hcaseT g h)))
    (keepT g St K tt h (a1OfT g (hcaseT g h) (posT g h) (ixT g h)))
  a1 := fun h => a1OfT g (hcaseT g h) (posT g h) (ixT g h)
  cv := fun h => iteT (eqT (stT g K tt h) (cT 0)) β (subT (stT g K tt h) (cT 1))
  Ng := NgT g

section

variable {φ : LTL} {p : LassoPath} (hE : Enc ts φ p)
  (hx : x = pack (encodeToks ts) q a) (hg : Gl.Ok x Γ ts g)
include hE hx hg

lemma den_depth {y : T} {Y : ℕ} (hy : Den x Γ y Y) :
    Den x Γ (depthT g y) ((tokFT hE).depth Y) := by
  have := den_count (body := fun z => AncT g z y) (f := fun z => bv ((tokFT hE).Anc z Y)) hg.F
    fun k i _ => den_Anc hE hx (hg.cons _) den_var0 (hy.cons _)
  refine this.of_eq ?_
  rw [cntU_bv]
  unfold PT.depth
  rw [card_filter_range]
  rfl

/-- **The term builders compute the per-gate quantities.** -/
theorem qLC_ok (hq : q ≤ a.length) {St : T → T} {S Qd : ℕ → Prop} (hS : DenS x Γ St S)
    {dd q0 K tt β : T} {H0 KV TT : ℕ} {B : Bool} (hK : Den x Γ K KV) (ht : Den x Γ tt TT)
    (hd : Den x Γ dd ((tokFT hE).down S ((tokFT hE).pos H0)))
    (hq0 : Den x Γ q0 (bv (Qd ((tokFT hE).down S ((tokFT hE).pos H0)) ∧
      (tokFT hE).InR S ((tokFT hE).down S ((tokFT hE).pos H0)) ((tokFT hE).pos H0))))
    (hβ : Den x Γ β B.toNat) :
    (qLC g St dd q0 K tt β).Ok x Γ ((tokFT hE).qLS S Qd (stA (tokFT hE) KV TT a) H0 B)
      ((tokFT hE).qSem S (stA (tokFT hE) KV TT a) H0 B) (tokFT hE).Ng where
  live := fun Γ' hΓ t v hv =>
    den_live hE hx (hg.mono hΓ) hq (hS.mono hΓ) (hK.mono hΓ) (ht.mono hΓ) (hd.mono hΓ)
      (hq0.mono hΓ) hv
  X := fun Γ' hΓ t v hv =>
    den_sub (den_add (den_mul (den_c 2) (den_ix hE (hg.mono hΓ) hv)) (den_c 1)) (den_mod hv (den_c 2))
  Y := fun Γ' hΓ t v hv => by
    have hl : Den x Γ' (leafT g dd) ((tokFT hE).leaf ((tokFT hE).down S ((tokFT hE).pos H0))).toNat :=
      den_leaf hx (hg.mono hΓ) (hd.mono hΓ)
    refine den_sub (den_add (den_depth hE hx (hg.mono hΓ) (hd.mono hΓ))
      (den_ite_eq hl (fun h1 => (den_c 0).of_eq ?_) (fun h1 => (den_c 1).of_eq ?_)))
      (den_depth hE hx (hg.mono hΓ) (den_pos hE (hg.mono hΓ) hv))
    · rw [if_pos (by unfold FT.rd; revert h1; cases (tokFT hE).leaf ((tokFT hE).down S ((tokFT hE).pos H0)) <;> simp)]
    · rw [if_neg (by unfold FT.rd; revert h1; cases (tokFT hE).leaf ((tokFT hE).down S ((tokFT hE).pos H0)) <;> simp)]
  kc := fun Γ' hΓ t v hv => den_kc hE hx (hg.mono hΓ) hv
  k0 := fun Γ' hΓ t v hv =>
    den_andB (den_ltB (den_c 0) (den_naOf (den_hcase hE hx (hg.mono hΓ) hv)))
      (den_keep hE hx (hg.mono hΓ) hq (hS.mono hΓ) (hK.mono hΓ) (ht.mono hΓ) hv
        (den_a0Of hE hx (hg.mono hΓ) (den_hcase hE hx (hg.mono hΓ) hv)
          (den_pos hE (hg.mono hΓ) hv) (den_ix hE (hg.mono hΓ) hv)))
  a0 := fun Γ' hΓ t v hv =>
    den_a0Of hE hx (hg.mono hΓ) (den_hcase hE hx (hg.mono hΓ) hv)
      (den_pos hE (hg.mono hΓ) hv) (den_ix hE (hg.mono hΓ) hv)
  k1 := fun Γ' hΓ t v hv =>
    den_andB (den_ltB (den_c 1) (den_naOf (den_hcase hE hx (hg.mono hΓ) hv)))
      (den_keep hE hx (hg.mono hΓ) hq (hS.mono hΓ) (hK.mono hΓ) (ht.mono hΓ) hv
        (den_a1Of hE hx (hg.mono hΓ) (den_hcase hE hx (hg.mono hΓ) hv)
          (den_pos hE (hg.mono hΓ) hv) (den_ix hE (hg.mono hΓ) hv)))
  a1 := fun Γ' hΓ t v hv =>
    den_a1Of hE hx (hg.mono hΓ) (den_hcase hE hx (hg.mono hΓ) hv)
      (den_pos hE (hg.mono hΓ) hv) (den_ix hE (hg.mono hΓ) hv)
  cv := fun Γ' hΓ t v hv => by
    have hs := den_st hE hx (hg.mono hΓ) hq (hK.mono hΓ) (ht.mono hΓ) hv
    refine (den_ite (den_eq' hs (den_c 0)) (fun _ => hβ.mono hΓ)
      (fun _ => den_sub hs (den_c 1))).of_eq ?_
    simp only [FT.qSem, ne_eq, bv_eq_zero, not_not]
  Ng := den_Ng hE hg
  ag := FT.qSem_agree

end

end FD

end PathChecking
