module

public import RequestProject.LTLPath.FDStrat

/-!
# The query function with stratified query circuits

`qProgS` is the output program of the query function: it computes the global values of the
formula tree, the round number `t` (the number of ticks answered `true`), and then either a tick
circuit or the stratified query circuit of gate `h0` with value `β` for unknown non-live gates.
`qFunS_spec` proves the specification `QSpecS`, and `qFunS_logspace` that the query function is
logspace computable.
-/

@[expose] public section

namespace PathChecking

namespace FD

open FE LL CTLP LTok Classical

variable {x : Word} {Γ : Ctx} {ts : List Tok} {q : ℕ} {a : List Bool} {g : Gl}

/-- The query program after the global values. -/
def qInnerS (g : Gl) (K tt qi : T) : TO :=
  iteO (ltT qi K) (tickO (leT qi tt))
    (lettO (cp2T (divT (subT tt (cT 1)) (cT 4)) g.L) fun d0 =>
     lettO (cp2T (addT (divT (subT tt (cT 1)) (cT 4)) (cT 1)) g.L) fun d1 =>
     lettO (cp2T (cT 0) g.L) fun dz =>
     lettO (divT (subT qi K) (cT 2)) fun h0 =>
     lettO (downT g (rST g tt d0 d1 dz) (posT g h0)) fun dd =>
     lettO (andT (rQT g tt d0 dd) (InRT g (rST g tt d0 d1 dz) dd (posT g h0))) fun q0 =>
       circO (qLC g (rST g tt d0 d1 dz) dd q0 K tt (modT (subT qi K) (cT 2)))
         (addT g.N (cT 1)) (addT (addT (mulT (cT 4) g.Wm) (mulT (cT 2) g.N)) (cT 6)) h0)

/-- The query program. -/
def qProgS : TO :=
  lettO nT fun N => lettO tFT fun F => lettO (sET F) fun sE => lettO (sLenT F sE) fun s =>
  lettO (lLenT sE N) fun l => lettO (addT s (mulT (addT N (cT 1)) l)) fun Wm =>
  lettO (lixT ⟨F, s, l, sE, N, Wm, F⟩ F) fun L =>
  lettO (mulT (cT 5) (addT nwT (cT 1))) fun K =>
  lettO (tcountT K) fun tt => lettO qT fun qi =>
  qInnerS ⟨F, s, l, sE, N, Wm, L⟩ K tt qi

/-- The value of the query program on valid inputs. -/
noncomputable def qValS {φ : LTL} {p : LassoPath} (hE : Enc ts φ p) (a : List Bool) (q : ℕ) :
    Word :=
  if q < nTicks (encodeToks ts) then
    (constCirc (decide (q ≤ tcount (nTicks (encodeToks ts)) a))).encode
  else
    ((tokFT hE).stratQ ((tokFT hE).rS (tcount (nTicks (encodeToks ts)) a))
      ((tokFT hE).rQ (tcount (nTicks (encodeToks ts)) a))
      (stA (tokFT hE) (nTicks (encodeToks ts)) (tcount (nTicks (encodeToks ts)) a) a)
      ((q - nTicks (encodeToks ts)) / 2) (decide ((q - nTicks (encodeToks ts)) % 2 = 1))).encode

section

variable {φ : LTL} {p : LassoPath} (hE : Enc ts φ p) (hx : x = pack (encodeToks ts) q a)
include hE hx

lemma deno_qInnerS (hg : Gl.Ok x Γ ts g) (hq : q ≤ a.length) {K tt qi : T}
    (hK : Den x Γ K (nTicks (encodeToks ts)))
    (ht : Den x Γ tt (tcount (nTicks (encodeToks ts)) a)) (hqi : Den x Γ qi q) :
    DenO x Γ (qInnerS g K tt qi) (qValS hE a q) := by
  unfold qInnerS qValS
  refine deno_ite_eq (den_lt' hqi hK) (fun h => ?_) (fun h => ?_)
  · simp only [ne_eq, bv_eq_zero, not_not] at h
    rw [if_pos h]; exact deno_tick (den_leB hqi ht)
  · simp only [bv_eq_zero] at h
    rw [if_neg h]
    set KV := nTicks (encodeToks ts)
    set TT := tcount KV a
    set 𝒯 := tokFT hE
    have hL : Den x Γ g.L 𝒯.L := hg.L
    refine deno_lett (den_cp2 (den_div (den_sub ht (den_c 1)) (den_c 4)) hL) fun k0 => ?_
    refine deno_lett (den_cp2 (den_add (den_div (den_sub (ht.cons _) (den_c 1)) (den_c 4))
      (den_c 1)) (hL.cons _)) fun k1 => ?_
    refine deno_lett (den_cp2 (den_c 0) ((hL.cons _).cons _)) fun kz => ?_
    set Γ3 := (kz, cp2 0 𝒯.L) :: (k1, cp2 ((TT - 1) / 4 + 1) 𝒯.L) ::
      (k0, cp2 ((TT - 1) / 4) 𝒯.L) :: Γ
    have s3 : Γ ⊆ Γ3 := fun y hy => by simp [Γ3, hy]
    have hg3 := hg.mono s3
    have hS : DenS x Γ3 (rST g tt (varT k0) (varT k1) (varT kz)) (𝒯.rS TT) :=
      den_rS hE hx hg3 (ht.mono s3) (den_var (by simp [Γ3])) (den_var (by simp [Γ3]))
        (den_var (by simp [Γ3]))
    have hQd : DenS x Γ3 (rQT g tt (varT k0)) (𝒯.rQ TT) :=
      den_rQ hE hx hg3 (ht.mono s3) (den_var (by simp [Γ3]))
    refine deno_lett (den_div (den_sub (hqi.mono s3) (hK.mono s3)) (den_c 2)) fun kh => ?_
    set H0 := (q - KV) / 2
    have hh0 : Den x ((kh, H0) :: Γ3) (varT kh) H0 := den_var0
    have s4 : Γ3 ⊆ (kh, H0) :: Γ3 := List.subset_cons_self _ _
    refine deno_lett (den_down hE hx (hg3.mono s4) (hS.mono s4) (den_pos hE (hg3.mono s4) hh0))
      fun kd => ?_
    set D0 := 𝒯.down (𝒯.rS TT) (𝒯.pos H0)
    set Γ5 := (kd, D0) :: (kh, H0) :: Γ3
    have s5 : Γ3 ⊆ Γ5 := fun y hy => by simp [Γ5, hy]
    have hd : Den x Γ5 (varT kd) D0 := den_var0
    refine deno_lett (den_and ((hQd.mono s5).app hd) (den_InR hE hx (hg3.mono s5) (hS.mono s5) hd
      (den_pos hE (hg3.mono s5) ((hh0.cons _))))) fun kq => ?_
    set Γ6 := (kq, bv (𝒯.rQ TT D0 ∧ 𝒯.InR (𝒯.rS TT) D0 (𝒯.pos H0))) :: Γ5
    have s6 : Γ3 ⊆ Γ6 := fun y hy => by simp [Γ6, Γ5, hy]
    have s6' : Γ ⊆ Γ6 := s3.trans s6
    have hq0 : Den x Γ6 (varT kq) (bv (𝒯.rQ TT D0 ∧ 𝒯.InR (𝒯.rS TT) D0 (𝒯.pos H0))) := den_var0
    have hβ : Den x Γ6 (modT (subT qi K) (cT 2)) (decide ((q - KV) % 2 = 1)).toNat :=
      (den_mod (den_sub (hqi.mono s6') (hK.mono s6')) (den_c 2)).of_eq (by
          rcases Nat.mod_two_eq_zero_or_one (q - KV) with e | e <;> simp [e])
    have hok := qLC_ok hE hx (hg.mono s6') hq (hS.mono s6) (hK.mono s6') (ht.mono s6')
      (hd.cons _) hq0 hβ (Qd := 𝒯.rQ TT)
    have hM : Den x Γ6 (addT g.N (cT 1)) 𝒯.sM := den_add (hg.mono s6').N (den_c 1)
    have hC : Den x Γ6 (addT (addT (mulT (cT 4) g.Wm) (mulT (cT 2) g.N)) (cT 6)) 𝒯.sC :=
      den_add (den_add (den_mul (den_c 4) (hg.mono s6').Wm) (den_mul (den_c 2) (hg.mono s6').N))
        (den_c 6)
    unfold FT.stratQ
    exact hok.deno_circO hM hC FT.qLS_bd ((hh0.cons _).cons _)

/-- **The query program on valid inputs.** -/
theorem deno_qProgS (hq : q ≤ a.length) : DenO x [] qProgS (qValS hE a q) := by
  unfold qProgS
  refine deno_lett (den_n hx) fun kN => ?_
  refine deno_lett (den_tF hx) fun kF => ?_
  refine deno_lett (den_sE hx den_var0) fun kE => ?_
  refine deno_lett (den_sLen hx (den_var (by simp)) den_var0) fun ks => ?_
  refine deno_lett (den_lLen hx (den_var (by simp)) (den_var (by simp))) fun kl => ?_
  refine deno_lett (den_add (den_var (k := ks) (v := sLen ts) (by simp))
    (den_mul (den_add (den_var (k := kN) (v := ts.length) (by simp)) (den_c 1)) den_var0))
    fun kW => ?_
  refine deno_lett (den_lixF hx (g := ⟨varT kF, varT ks, varT kl, varT kE, varT kN, varT kW,
    varT kF⟩) (den_var (by simp)) (den_var (v := tF ts) (by simp))) fun kL => ?_
  refine deno_lett (den_mul (den_c 5) (den_add (den_nw hx) (den_c 1))) fun kK => ?_
  refine deno_lett (den_tcount hx hq den_var0) fun kt => ?_
  refine deno_lett (den_q hx hq) fun kq => ?_
  exact deno_qInnerS hE hx ⟨den_var (by simp), den_var (by simp), den_var (by simp),
    den_var (by simp), den_var (by simp), den_var (by simp), den_var (by simp)⟩ hq
    (den_var (by simp [nTicks])) (den_var (by simp [nTicks])) den_var0

end

end FD

open FD

/-- The query function of the round algorithm with stratified queries. -/
def qFunS (x : Word) : Word := FE.evO x 0 (fun _ => 0) (qProgS 0)

/-- The query function is logspace computable. -/
theorem qFunS_logspace : LogspaceComputable qFunS :=
  FE.logspaceComputable_of_O (qProgS 0) (by decide +kernel) qFunS fun _ => rfl

/-- **The query function meets its specification.** -/
theorem qFunS_spec : QSpecS qFunS := by
  intro φ p a ha
  have hE := instToks_enc φ p
  have hb := instFT_bounds φ p
  have key : ∀ q, q < nQ (encodeToks (instToks φ p)) →
      qFunS (pack (encodeToks (instToks φ p)) q a) = qValS hE a q := fun q hq =>
    deno_qProgS hE rfl (by omega) 0 _ (fun _ h => absurd h (by simp))
  refine ⟨fun q hq => ?_, fun h0 hh0 β => ?_⟩
  · rw [key q (by omega), qValS, if_pos hq]
  · rw [key _ (by cases β <;> (simp; try omega)), qValS, if_neg (by omega)]
    have e1 : (nTicks (encodeToks (instToks φ p)) + 2 * h0 + β.toNat -
        nTicks (encodeToks (instToks φ p))) / 2 = h0 := by cases β <;> (simp; try omega)
    have e2 : decide ((nTicks (encodeToks (instToks φ p)) + 2 * h0 + β.toNat -
        nTicks (encodeToks (instToks φ p))) % 2 = 1) = β := by cases β <;> (simp; try omega)
    rw [e1, e2]
    rfl

end PathChecking
