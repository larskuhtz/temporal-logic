module

public import RequestProject.LTLPath.FDSched
public import RequestProject.LTLPath.Assembly

/-!
# Terms for one round: round sets, statuses, live gates and kept arguments

Statuses `Option Bool` are coded by numbers (`oc`: `none ↦ 0`, `some b ↦ b + 1`).
-/

@[expose] public section

namespace PathChecking

/-- Code of a status. -/
def oc : Option Bool → ℕ
  | none => 0
  | some b => b.toNat + 1

namespace FD

open FE LL CTLP LTok Classical

variable {x : Word} {Γ : Ctx} {ts : List Tok} {q : ℕ} {a : List Bool} {g : Gl}

/-! ## Terms -/

/-- Number of ticks answered `true`. -/
def tcountT (K : T) : T := countT K fun j => ansT j

/-- Leaf set of round `tt` (`d0`, `d1`, `dz`: capped powers for `(tt-1)/4`, `(tt-1)/4+1`, `0`). -/
def rST (g : Gl) (tt d0 d1 dz : T) (k : T) : T :=
  iteT (eqT tt (cT 0)) (S0T g dz k) (lettT (modT (subT tt (cT 1)) (cT 4)) fun m =>
    iteT (eqT m (cT 0)) (S0T g d0 k)
      (iteT (orT (eqT m (cT 1)) (eqT m (cT 2))) (S1T g d0 k) (S0T g d1 k)))

/-- Queried regions of round `tt`. -/
def rQT (g : Gl) (tt d0 : T) (p : T) : T :=
  iteT (eqT tt (cT 0)) (cT 1) (lettT (modT (subT tt (cT 1)) (cT 4)) fun m =>
    iteT (eqT m (cT 0)) (PSetT g (S0T g d0) (DLT g d0) p)
      (iteT (eqT m (cT 2)) (PSetT g (S1T g d0) (DRT g d0) p) (cT 1)))

/-- Kind code of gate `h`. -/
def kcT (g : Gl) (h : T) : T :=
  kcOfT (hcaseT g h) (lvTokT g (posT g h) (ixT g h)) (polTokT g (posT g h))

/-- Initial status code of gate `h`. -/
def initT (g : Gl) (h : T) : T :=
  lettT (kcT g h) fun k => iteT (isT 1 k) (cT 1) (iteT (isT 2 k) (cT 2) (cT 0))

/-- Decoding of two answers. -/
def decT (u v : T) : T := iteT (eqT u v) (addT u (cT 1)) (cT 0)

/-- Status code of gate `h` before round `tt`. -/
def stT (g : Gl) (K tt h : T) : T :=
  iteT (eqT tt (cT 0)) (initT g h)
    (iteT (ltT h (NgT g)) (decT (ansT (addT K (mulT (cT 2) h)))
      (ansT (addT (addT K (mulT (cT 2) h)) (cT 1)))) (initT g h))

/-- `AND`/`OR` gates. -/
def aoT (g : Gl) (h : T) : T := lettT (hcaseT g h) fun c => andT (leT (cT 2) c) (leT c (cT 7))

/-- Live gates of the query of `h0` (`d0 = down (pos h0)`, `q0`: the region of `h0` is queried). -/
def liveT (g : Gl) (St : T → T) (d0 q0 K tt h : T) : T :=
  andT q0 (andT (isT 0 (stT g K tt h)) (andT (aoT g h) (InRT g St d0 (posT g h))))

/-- Kept arguments. -/
def keepT (g : Gl) (St : T → T) (K tt h y : T) : T :=
  lettT (kcT g h) fun k =>
    notT (andT (eqT (stT g K tt y) (addT (isT 4 k) (cT 1))) (NFT g St (posT g h) (posT g y)))

/-! ## Denotations -/

lemma den_tcount (hx : x = pack (encodeToks ts) q a) (hq : q ≤ a.length) {K : T} {KV : ℕ}
    (hK : Den x Γ K KV) : Den x Γ (tcountT K) (tcount KV a) := by
  refine (den_count (body := fun j => ansT j) (f := fun j => (a.getD j false).toNat) hK
    fun k i _ => den_ans hx hq den_var0).of_eq ?_
  unfold cntU tcount
  exact List.countP_congr fun i _ => by
    cases h : a.getD i false <;> simp only [h] <;> decide

section

variable {φ : LTL} {p : LassoPath} (hE : Enc ts φ p)
  (hx : x = pack (encodeToks ts) q a) (hg : Gl.Ok x Γ ts g)
include hE hx hg

omit hx hg in
lemma rS_lt (t k : ℕ) (h : (tokFT hE).rS t k) : k < (tokFT hE).L := by
  cases t with
  | zero => exact h.1
  | succ u =>
    simp only [FT.rS] at h
    split_ifs at h
    · exact h.1
    · exact h.1.1
    · exact h.1

lemma den_rS {tt d0 d1 dz : T} {TT : ℕ} (ht : Den x Γ tt TT)
    (hd0 : Den x Γ d0 (cp2 ((TT - 1) / 4) (tokFT hE).L))
    (hd1 : Den x Γ d1 (cp2 ((TT - 1) / 4 + 1) (tokFT hE).L))
    (hdz : Den x Γ dz (cp2 0 (tokFT hE).L)) :
    DenS x Γ (rST g tt d0 d1 dz) ((tokFT hE).rS TT) := fun Γ' hΓ t v hv => by
  have hg' := hg.mono hΓ
  refine den_ite_eq (den_eq' (ht.mono hΓ) (den_c 0)) (fun h => ?_) (fun h => ?_)
  · simp at h; subst h
    exact (den_S0 hE hg' (hdz.mono hΓ)).app hv
  · simp at h
    obtain ⟨u, rfl⟩ : ∃ u, TT = u + 1 := ⟨TT - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hd0 hd1
    refine den_lett (den_mod (den_sub (ht.mono hΓ) (den_c 1)) (den_c 4)) fun km => ?_
    have hsub : Γ' ⊆ (km, (u + 1 - 1) % 4) :: Γ' := List.subset_cons_self _ _
    have hm : Den x ((km, (u + 1 - 1) % 4) :: Γ') (varT km) ((u + 1 - 1) % 4) := den_var0
    simp only [Nat.add_sub_cancel] at hm
    have hg'' := hg'.mono hsub
    have hd0' := (hd0.mono hΓ).mono hsub
    have hd1' := (hd1.mono hΓ).mono hsub
    have hv' := hv.mono hsub
    simp only [FT.rS]
    refine den_ite_eq (den_eq' hm (den_c 0)) (fun h0 => ?_) (fun h0 => ?_)
    · simp at h0; rw [if_pos h0]; exact (den_S0 hE hg'' hd0').app hv'
    · simp at h0; rw [if_neg h0]
      refine den_ite_eq (den_or (den_eq' hm (den_c 1)) (den_eq' hm (den_c 2))) (fun h1 => ?_)
        (fun h1 => ?_)
      · simp at h1; rw [if_pos (by omega)]; exact (den_S1 hE hx hg'' hd0').app hv'
      · simp at h1; rw [if_neg (by omega)]; exact (den_S0 hE hg'' hd1').app hv'

lemma den_rQ {tt d0 : T} {TT : ℕ} (ht : Den x Γ tt TT)
    (hd0 : Den x Γ d0 (cp2 ((TT - 1) / 4) (tokFT hE).L)) :
    DenS x Γ (rQT g tt d0) ((tokFT hE).rQ TT) := fun Γ' hΓ t v hv => by
  have hg' := hg.mono hΓ
  refine den_ite_eq (den_eq' (ht.mono hΓ) (den_c 0)) (fun h => ?_) (fun h => ?_)
  · simp at h; subst h
    exact (den_c 1).of_eq (by simp [FT.rQ, bv])
  · simp at h
    obtain ⟨u, rfl⟩ : ∃ u, TT = u + 1 := ⟨TT - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hd0
    refine den_lett (den_mod (den_sub (ht.mono hΓ) (den_c 1)) (den_c 4)) fun km => ?_
    have hsub : Γ' ⊆ (km, (u + 1 - 1) % 4) :: Γ' := List.subset_cons_self _ _
    have hm : Den x ((km, (u + 1 - 1) % 4) :: Γ') (varT km) ((u + 1 - 1) % 4) := den_var0
    simp only [Nat.add_sub_cancel] at hm
    have hg'' := hg'.mono hsub
    have hd0' := (hd0.mono hΓ).mono hsub
    have hv' := hv.mono hsub
    have hS0 := den_S0 hE hg'' hd0'
    have hS1 := den_S1 hE hx hg'' hd0'
    simp only [FT.rQ]
    refine den_ite_eq (den_eq' hm (den_c 0)) (fun h0 => ?_) (fun h0 => ?_)
    · simp at h0; rw [if_pos h0]
      exact (den_PSet hE hx hg'' hS0 (den_DL hE hx hg'' hd0') (fun k hk => hk.1)
        (fun k hk => hk.1.1)).app hv'
    · simp at h0; rw [if_neg h0]
      refine den_ite_eq (den_eq' hm (den_c 2)) (fun h2 => ?_) (fun h2 => ?_)
      · simp at h2; rw [if_pos h2]
        exact (den_PSet hE hx hg'' hS1 (den_DR hE hx hg'' hd0') (fun k hk => hk.1.1)
          (fun k hk => hk.1.1.1)).app hv'
      · simp at h2; rw [if_neg h2]; exact (den_c 1).of_eq (by simp [bv])

lemma den_kc {h : T} {H : ℕ} (hh : Den x Γ h H) :
    Den x Γ (kcT g h) (kcode ((tokFT hE).gate H).kind) := by
  rw [FT.gate_eq, FT.kcode_gOfCase]
  exact den_kcOf (den_hcase hE hx hg hh) (den_lvTok hx hg (den_pos hE hg hh) (den_ix hE hg hh))
    (den_polTok hx hg (den_pos hE hg hh))

lemma den_init {h : T} {H : ℕ} (hh : Den x Γ h H) :
    Den x Γ (initT g h) (oc ((tokFT hE).init H)) := by
  refine den_lett (den_kc hE hx hg hh) fun k => ?_
  have hk : Den x ((k, kcode ((tokFT hE).gate H).kind) :: Γ) (varT k)
    (kcode ((tokFT hE).gate H).kind) := den_var0
  have e : oc ((tokFT hE).init H) = if kcode ((tokFT hE).gate H).kind = 1 then 1
      else if kcode ((tokFT hE).gate H).kind = 2 then 2 else 0 := by
    unfold FT.init
    rcases ((tokFT hE).gate H).kind with _ | b | _ | _ | _ | _ <;> try cases b
    all_goals simp [kcode, oc]
  rw [e]
  refine den_ite_eq ((denP_is 1 _ (List.Subset.refl _) _ _ hk)) (fun h1 => ?_) (fun h1 => ?_)
  · simp at h1; rw [if_pos h1]; exact den_c 1
  · simp at h1; rw [if_neg h1]
    refine den_ite_eq ((denP_is 2 _ (List.Subset.refl _) _ _ hk)) (fun h2 => ?_) (fun h2 => ?_)
    · simp at h2; rw [if_pos h2]; exact den_c 2
    · simp at h2; rw [if_neg h2]; exact den_c 0

omit hE hg in
lemma den_dec (hq : q ≤ a.length) {u v : T} {U V : ℕ} (hu : Den x Γ u U) (hv : Den x Γ v V) :
    Den x Γ (decT (ansT u) (ansT v)) (oc (GS.dec (a.getD U false) (a.getD V false))) := by
  refine den_ite_eq (den_eq' (den_ans hx hq hu) (den_ans hx hq hv)) (fun h => ?_) (fun h => ?_)
  · simp only [ne_eq, bv_eq_zero, not_not] at h
    have h' : a.getD U false = a.getD V false := by
      revert h; cases a.getD U false <;> cases a.getD V false <;> simp
    refine (den_add (den_ans hx hq hu) (den_c 1)).of_eq ?_
    rw [GS.dec, if_pos h']; rfl
  · simp only [bv_eq_zero] at h
    have h' : a.getD U false ≠ a.getD V false := fun e => h (by rw [e])
    refine (den_c 0).of_eq ?_
    rw [GS.dec, if_neg h']; rfl

lemma den_st (hq : q ≤ a.length) {K tt h : T} {KV TT H : ℕ} (hK : Den x Γ K KV)
    (ht : Den x Γ tt TT) (hh : Den x Γ h H) :
    Den x Γ (stT g K tt h) (oc (stA (tokFT hE) KV TT a H)) := by
  unfold stA
  refine den_ite_eq (den_eq' ht (den_c 0)) (fun h0 => ?_) (fun h0 => ?_)
  · simp at h0; rw [if_pos h0]; exact den_init hE hx hg hh
  · simp at h0; rw [if_neg h0]
    refine den_ite_eq (den_lt' hh (den_Ng hE hg)) (fun h1 => ?_) (fun h1 => ?_)
    · simp at h1; rw [if_pos h1]
      exact den_dec hx hq (den_add hK (den_mul (den_c 2) hh))
        (den_add (den_add hK (den_mul (den_c 2) hh)) (den_c 1))
    · simp at h1; rw [if_neg (by omega)]; exact den_init hE hx hg hh

lemma den_ao {h : T} {H : ℕ} (hh : Den x Γ h H) :
    Den x Γ (aoT g h) (bv (FT.AO ((tokFT hE).gate H))) := by
  refine den_lett (den_hcase hE hx hg hh) fun k => ?_
  have hk : Den x ((k, (tokFT hE).hcase H) :: Γ) (varT k) ((tokFT hE).hcase H) := den_var0
  refine (den_and (den_le (den_c 2) hk) (den_le hk (den_c 7))).of_eq (bv_congr ?_)
  rw [FT.gate_eq, FT.AO_gOfCase_iff]

lemma den_live (hq : q ≤ a.length) {St : T → T} {S Qd : ℕ → Prop} (hS : DenS x Γ St S)
    {d0 q0 K tt h : T} {H0 KV TT H : ℕ} (hK : Den x Γ K KV) (ht : Den x Γ tt TT)
    (hd0 : Den x Γ d0 ((tokFT hE).down S ((tokFT hE).pos H0)))
    (hq0 : Den x Γ q0 (bv (Qd ((tokFT hE).down S ((tokFT hE).pos H0)) ∧
      (tokFT hE).InR S ((tokFT hE).down S ((tokFT hE).pos H0)) ((tokFT hE).pos H0))))
    (hh : Den x Γ h H) :
    Den x Γ (liveT g St d0 q0 K tt h)
      ((tokFT hE).live S Qd (stA (tokFT hE) KV TT a) H0 H).toNat := by
  refine (den_and hq0 (den_and ((denP_is 0 _ (List.Subset.refl _) _ _
    (den_st hE hx hg hq hK ht hh)).of_eq (bv_bool _)) (den_and (den_ao hE hx hg hh)
      (den_InR hE hx hg hS hd0 (den_pos hE hg hh))))).of_eq ?_
  rw [FT.live, bv_decide]
  apply bv_congr
  have : (oc (stA (tokFT hE) KV TT a H) == 0) = true ↔ stA (tokFT hE) KV TT a H = none := by
    cases stA (tokFT hE) KV TT a H <;> simp [oc]
  rw [this]
  tauto

lemma den_keep (hq : q ≤ a.length) {St : T → T} {S : ℕ → Prop} (hS : DenS x Γ St S)
    {K tt h y : T} {KV TT H Y : ℕ} (hK : Den x Γ K KV) (ht : Den x Γ tt TT)
    (hh : Den x Γ h H) (hy : Den x Γ y Y) :
    Den x Γ (keepT g St K tt h y) ((tokFT hE).keep S (stA (tokFT hE) KV TT a) H Y).toNat := by
  refine den_lett (den_kc hE hx hg hh) fun k => ?_
  have hsub : Γ ⊆ (k, kcode ((tokFT hE).gate H).kind) :: Γ := List.subset_cons_self _ _
  have hk : Den x ((k, kcode ((tokFT hE).gate H).kind) :: Γ) (varT k)
    (kcode ((tokFT hE).gate H).kind) := den_var0
  have hg' := hg.mono hsub
  refine (den_not (den_and (den_eq' (den_st hE hx hg' hq (hK.mono hsub) (ht.mono hsub)
    (hy.mono hsub)) (den_add (denP_is 4 _ (List.Subset.refl _) _ _ hk) (den_c 1)))
    (den_NF hE hx hg' (hS.mono hsub) (den_pos hE hg' (hh.mono hsub))
      (den_pos hE hg' (hy.mono hsub))))).of_eq ?_
  have e : (!decide (stA (tokFT hE) KV TT a Y = some (GS.neutral ((tokFT hE).gate H).kind) ∧
      (tokFT hE).NF S ((tokFT hE).pos H) ((tokFT hE).pos Y))).toNat =
      bv (¬ (stA (tokFT hE) KV TT a Y = some (GS.neutral ((tokFT hE).gate H).kind) ∧
      (tokFT hE).NF S ((tokFT hE).pos H) ((tokFT hE).pos Y))) :=
    toNat_eq_bv (by rw [Bool.not_eq_true', decide_eq_false_iff_not])
  rw [FT.keep, e]
  apply bv_congr
  have : oc (stA (tokFT hE) KV TT a Y) = (kcode ((tokFT hE).gate H).kind == 4).toNat + 1 ↔
      stA (tokFT hE) KV TT a Y = some (GS.neutral ((tokFT hE).gate H).kind) := by
    rcases ((tokFT hE).gate H).kind with _ | b | _ | _ | _ | _ <;>
      cases stA (tokFT hE) KV TT a Y <;> (try cases b) <;> simp [oc, kcode, GS.neutral]
  rw [this]

end

end FD

end PathChecking
