module

public import RequestProject.LTLPath.FDQ
public import RequestProject.LTLPath.LGridC

/-!
# Output programs for grid drawings of layered systems

`circO c M Cmax h0` is an output program writing the encoding of the grid drawing
`LSys.circ M Cmax h0` of a layered system, given term builders `c : LC` for the per-gate
quantities of the system (`RequestProject/LTLPath/LGridC.lean`).  `deno_circO` proves its
denotation.
-/

@[expose] public section

namespace PathChecking

namespace FD

open FE LL Classical LG Grid

/-- Term builders for the per-gate quantities of a layered system. -/
structure LC where
  live : T → T
  X : T → T
  Y : T → T
  kc : T → T
  k0 : T → T
  a0 : T → T
  k1 : T → T
  a1 : T → T
  cv : T → T
  Ng : T

variable {x : Word} {Γ : Ctx}

/-- The term builders compute quantities `s` agreeing with the system `L`. -/
structure LC.Ok (x : Word) (Γ : Ctx) (c : LC) (L : LSys) (s : LSem) (NG : ℕ) : Prop where
  live : DenF x Γ c.live fun h => (L.live h).toNat
  X : DenF x Γ c.X s.X
  Y : DenF x Γ c.Y s.Y
  kc : DenF x Γ c.kc s.kc
  k0 : DenF x Γ c.k0 fun h => (s.k0 h).toNat
  a0 : DenF x Γ c.a0 s.a0
  k1 : DenF x Γ c.k1 fun h => (s.k1 h).toNat
  a1 : DenF x Γ c.a1 s.a1
  cv : DenF x Γ c.cv s.cv
  Ng : Den x Γ c.Ng NG
  ag : Agree L s NG

lemma DenF.mono' {f : T → T} {F : ℕ → ℕ} (h : DenF x Γ f F) {Γ' : Ctx} (hΓ : Γ ⊆ Γ') :
    DenF x Γ' f F :=
  fun Γ'' h' t v ht => h Γ'' (hΓ.trans h') t v ht

/-! ## Terms -/

section Terms

variable (c : LC)

def isRT (h y : T) : T := andT (c.live y) (eqT (c.Y y) (c.Y h))
def r0T (h : T) : T := andT (c.k0 h) (notT (isRT c h (c.a0 h)))
def r1T (h : T) : T := andT (c.k1 h) (notT (isRT c h (c.a1 h)))
def sST (h : T) : T := orT (r0T c h) (r1T c h)
def sVT (h : T) : T :=
  iteT (andT (r0T c h) (r1T c h)) (maxT (c.a0 h) (c.a1 h)) (iteT (r0T c h) (c.a0 h) (c.a1 h))
def dST (h : T) : T := andT (andT (r0T c h) (r1T c h)) (notT (eqT (c.a0 h) (c.a1 h)))
def dVT (h : T) : T := minT (c.a0 h) (c.a1 h)
def hasRT (h : T) : T :=
  orT (andT (c.k0 h) (isRT c h (c.a0 h))) (andT (c.k1 h) (isRT c h (c.a1 h)))
def colT (M h : T) : T := mulT (cT 2) (subT (addT (c.X h) M) (c.Y h))
def timT (M Cm h : T) : T := subT (addT (mulT (cT 10) (c.Y h)) Cm) (colT c M h)
def slotT (M h y : T) : T :=
  iteT (andT (sST c h) (eqT (sVT c h) y)) (colT c M h) (addT (colT c M h) (cT 1))
def gAtT (M b cc h : T) : T := andT (c.live h) (andT (eqT (c.Y h) b) (eqT (colT c M h) cc))
def wireT (M b ph cc h y : T) : T :=
  andT (c.live y) (andT (eqT (c.Y y) b) (andT (eqT (addT (c.Y y) (cT 1)) (c.Y h))
    (andT (eqT (colT c M y) (addT cc ph)) (leT (addT (slotT c M h y) ph) (colT c M y)))))
def DDesT (M b ph cc : T) : T :=
  exT c.Ng fun h => andT (c.live h) (orT (andT (c.k0 h) (wireT c M b ph cc h (c.a0 h)))
    (andT (c.k1 h) (wireT c M b ph cc h (c.a1 h))))
def colConstT (M cc : T) : T :=
  orT (exT c.Ng fun h => andT (gAtT c M (cT 1) cc h) (andT (sST c h)
      (andT (notT (c.live (sVT c h))) (neT (c.cv (sVT c h)) (cT 0)))))
    (exT c.Ng fun h => andT (gAtT c M (cT 1) (subT cc (cT 1)) h) (andT (eqT (modT cc (cT 2)) (cT 1))
      (andT (dST c h) (andT (notT (c.live (dVT c h))) (neT (c.cv (dVT c h)) (cT 0))))))
def exGRT (M b cc : T) : T := exT c.Ng fun h => andT (gAtT c M b cc h) (hasRT c h)

/-- Band of a node. -/
def bndT (Cm cc t : T) : T := divT (subT (addT t cc) Cm) (cT 10)
/-- Phase of a node. -/
def phT (Cm cc t : T) : T := modT (subT (addT t cc) Cm) (cT 10)

/-- Kind code of the node at column `cc` and time `t`. -/
def nodeKT (M Cm cc t : T) : T :=
  iteT (eqT t (cT 0)) (addT (cT 1) (colConstT c M cc))
    (iteT (ltT (addT t cc) Cm) (cT 4)
      (iteT (eqT (phT Cm cc t) (cT 0))
        (iteT (eqT (modT cc (cT 2)) (cT 0))
          (iteT (exT c.Ng (gAtT c M (bndT Cm cc t) cc))
            (c.kc (findT c.Ng (gAtT c M (bndT Cm cc t) cc))) (cT 4))
          (cT 4))
        (cT 4)))

/-- Straight flag of the node at column `cc` and time `t`. -/
def nodeST (M Cm cc t : T) : T :=
  iteT (eqT t (cT 0)) (cT 0)
    (iteT (ltT (addT t cc) Cm) (cT 1)
      (iteT (eqT (phT Cm cc t) (cT 0))
        (iteT (eqT (modT cc (cT 2)) (cT 0))
          (iteT (exT c.Ng (gAtT c M (bndT Cm cc t) cc))
            (sST c (findT c.Ng (gAtT c M (bndT Cm cc t) cc))) (cT 1))
          (iteT (exGRT c M (bndT Cm cc t) (subT cc (cT 1))) (cT 0) (cT 1)))
        (iteT (DDesT c M (bndT Cm cc t) (phT Cm cc t) cc) (cT 0) (cT 1))))

/-- Diagonal flag of the node at column `cc` and time `t`. -/
def nodeDT (M Cm cc t : T) : T :=
  iteT (eqT t (cT 0)) (cT 0)
    (iteT (ltT (addT t cc) Cm) (cT 0)
      (iteT (eqT (phT Cm cc t) (cT 0))
        (iteT (eqT (modT cc (cT 2)) (cT 0))
          (iteT (exT c.Ng (gAtT c M (bndT Cm cc t) cc))
            (orT (hasRT c (findT c.Ng (gAtT c M (bndT Cm cc t) cc)))
              (dST c (findT c.Ng (gAtT c M (bndT Cm cc t) cc)))) (cT 0))
          (iteT (exGRT c M (bndT Cm cc t) (subT cc (cT 1))) (cT 1) (cT 0)))
        (iteT (DDesT c M (bndT Cm cc t) (phT Cm cc t) cc) (cT 1) (cT 0))))

/-- Index of a grid node. -/
def gidxT (W t j : T) : T := addT (mulT t W) (subT (subT W (cT 1)) j)

/-- Output of the grid gate with index `n`. -/
def gateNO (M Cm c0 W n : T) : TO :=
  lettO (divT n W) fun t => lettO (subT (subT W (cT 1)) (modT n W)) fun j =>
    seqO (tokO (addT (cT 5) (nodeKT c M Cm (addT c0 j) t))) (seqO (tokO (cT 3))
      (seqO (seqO
        (iteO (nodeDT c M Cm (addT c0 j) t) (natO (gidxT W (subT t (cT 1)) (addT j (cT 1)))) nilO)
        (iteO (nodeST c M Cm (addT c0 j) t) (natO (gidxT W (subT t (cT 1)) j)) nilO))
        (tokO (cT 4))))

/-- Output of the grid drawing with output gate `h0`. -/
def circO (M Cm h0 : T) : TO :=
  iteO (c.live h0)
    (lettO (colT c M h0) fun c0 => lettO (subT (addT Cm (cT 1)) c0) fun W =>
      loopO (mulT (addT (timT c M Cm h0) (cT 1)) W) fun n => gateNO c M Cm c0 W n)
    (tickO (c.cv h0))

end Terms

/-! ## Denotations -/

namespace LC.Ok

variable {c : LC} {L : LSys} {s : LSem} {NG : ℕ}

lemma mono (hc : c.Ok x Γ L s NG) {Γ' : Ctx} (hΓ : Γ ⊆ Γ') : c.Ok x Γ' L s NG :=
  ⟨hc.live.mono' hΓ, hc.X.mono' hΓ, hc.Y.mono' hΓ, hc.kc.mono' hΓ, hc.k0.mono' hΓ,
    hc.a0.mono' hΓ, hc.k1.mono' hΓ, hc.a1.mono' hΓ, hc.cv.mono' hΓ, hc.Ng.mono hΓ, hc.ag⟩

lemma cons (hc : c.Ok x Γ L s NG) (kv : ℕ × ℕ) : c.Ok x (kv :: Γ) L s NG :=
  hc.mono (List.subset_cons_self _ _)

variable (hc : c.Ok x Γ L s NG)
include hc

lemma dlive {t : T} {v : ℕ} (ht : Den x Γ t v) : Den x Γ (c.live t) (bv (L.live v = true)) :=
  (hc.live Γ (List.Subset.refl _) t v ht).of_eq (bv_bool _)
lemma dliveN {t : T} {v : ℕ} (ht : Den x Γ t v) : Den x Γ (c.live t) (L.live v).toNat :=
  hc.live Γ (List.Subset.refl _) t v ht
lemma dX {t : T} {v : ℕ} (ht : Den x Γ t v) : Den x Γ (c.X t) (s.X v) :=
  hc.X Γ (List.Subset.refl _) t v ht
lemma dY {t : T} {v : ℕ} (ht : Den x Γ t v) : Den x Γ (c.Y t) (s.Y v) :=
  hc.Y Γ (List.Subset.refl _) t v ht
lemma dkc {t : T} {v : ℕ} (ht : Den x Γ t v) : Den x Γ (c.kc t) (s.kc v) :=
  hc.kc Γ (List.Subset.refl _) t v ht
lemma dk0 {t : T} {v : ℕ} (ht : Den x Γ t v) : Den x Γ (c.k0 t) (bv (s.k0 v = true)) :=
  (hc.k0 Γ (List.Subset.refl _) t v ht).of_eq (bv_bool _)
lemma dk1 {t : T} {v : ℕ} (ht : Den x Γ t v) : Den x Γ (c.k1 t) (bv (s.k1 v = true)) :=
  (hc.k1 Γ (List.Subset.refl _) t v ht).of_eq (bv_bool _)
lemma da0 {t : T} {v : ℕ} (ht : Den x Γ t v) : Den x Γ (c.a0 t) (s.a0 v) :=
  hc.a0 Γ (List.Subset.refl _) t v ht
lemma da1 {t : T} {v : ℕ} (ht : Den x Γ t v) : Den x Γ (c.a1 t) (s.a1 v) :=
  hc.a1 Γ (List.Subset.refl _) t v ht
lemma dcv {t : T} {v : ℕ} (ht : Den x Γ t v) : Den x Γ (c.cv t) (s.cv v) :=
  hc.cv Γ (List.Subset.refl _) t v ht

lemma den_isR {h y : T} {H Y : ℕ} (hh : Den x Γ h H) (hy : Den x Γ y Y) :
    Den x Γ (isRT c h y) (bv (s.isR L H Y = true)) :=
  (den_and (hc.dlive hy) (den_eq' (hc.dY hy) (hc.dY hh))).of_eq (bv_congr (by simp [LSem.isR]))

lemma den_r0 {h : T} {H : ℕ} (hh : Den x Γ h H) : Den x Γ (r0T c h) (bv (s.r0 L H = true)) :=
  (den_and (hc.dk0 hh) (den_not (hc.den_isR hh (hc.da0 hh)))).of_eq
    (bv_congr (by simp [LSem.r0]))

lemma den_r1 {h : T} {H : ℕ} (hh : Den x Γ h H) : Den x Γ (r1T c h) (bv (s.r1 L H = true)) :=
  (den_and (hc.dk1 hh) (den_not (hc.den_isR hh (hc.da1 hh)))).of_eq
    (bv_congr (by simp [LSem.r1]))

lemma den_sS {h : T} {H : ℕ} (hh : Den x Γ h H) : Den x Γ (sST c h) (bv (s.sS L H = true)) :=
  (den_or (hc.den_r0 hh) (hc.den_r1 hh)).of_eq (bv_congr (by simp [LSem.sS]))

lemma den_sV {h : T} {H : ℕ} (hh : Den x Γ h H) : Den x Γ (sVT c h) (s.sV L H) := by
  unfold sVT LSem.sV
  refine den_ite_eq (den_and (hc.den_r0 hh) (hc.den_r1 hh)) (fun h1 => ?_) (fun h1 => ?_)
  · rw [bv_ne_zero] at h1
    rw [if_pos (by simp [h1.1, h1.2])]; exact den_max (hc.da0 hh) (hc.da1 hh)
  · rw [bv_eq_zero] at h1
    rw [if_neg (by simpa using h1)]
    refine den_ite_eq (hc.den_r0 hh) (fun h2 => ?_) (fun h2 => ?_)
    · rw [bv_ne_zero] at h2; rw [if_pos h2]; exact hc.da0 hh
    · rw [bv_eq_zero] at h2; rw [if_neg h2]; exact hc.da1 hh

lemma den_dS {h : T} {H : ℕ} (hh : Den x Γ h H) : Den x Γ (dST c h) (bv (s.dS L H = true)) :=
  (den_and (den_and (hc.den_r0 hh) (hc.den_r1 hh)) (den_not (den_eq' (hc.da0 hh) (hc.da1 hh)))).of_eq
    (bv_congr (by simp [LSem.dS]))

lemma den_dV {h : T} {H : ℕ} (hh : Den x Γ h H) : Den x Γ (dVT c h) (s.dV H) :=
  den_min (hc.da0 hh) (hc.da1 hh)

lemma den_hasR {h : T} {H : ℕ} (hh : Den x Γ h H) :
    Den x Γ (hasRT c h) (bv (s.hasR L H = true)) :=
  (den_or (den_and (hc.dk0 hh) (hc.den_isR hh (hc.da0 hh)))
    (den_and (hc.dk1 hh) (hc.den_isR hh (hc.da1 hh)))).of_eq (bv_congr (by simp [LSem.hasR]))

variable {M : T} {MV : ℕ} (hM : Den x Γ M MV)
include hM

lemma den_col {h : T} {H : ℕ} (hh : Den x Γ h H) : Den x Γ (colT c M h) (s.col MV H) :=
  den_mul (den_c 2) (den_sub (den_add (hc.dX hh) hM) (hc.dY hh))

lemma den_slot {h y : T} {H Y : ℕ} (hh : Den x Γ h H) (hy : Den x Γ y Y) :
    Den x Γ (slotT c M h y) (s.slot L MV H Y) := by
  unfold slotT LSem.slot
  refine den_ite_eq (den_and (hc.den_sS hh) (den_eq' (hc.den_sV hh) hy)) (fun h1 => ?_)
    (fun h1 => ?_)
  · rw [bv_ne_zero] at h1
    rw [if_pos (by simp [h1.1, h1.2])]; exact hc.den_col hM hh
  · rw [bv_eq_zero] at h1
    rw [if_neg (by simpa using h1)]; exact den_add (hc.den_col hM hh) (den_c 1)

lemma den_gAt {b cc h : T} {B CC H : ℕ} (hb : Den x Γ b B) (hcc : Den x Γ cc CC)
    (hh : Den x Γ h H) :
    Den x Γ (gAtT c M b cc h) (bv (L.live H = true ∧ s.Y H = B ∧ s.col MV H = CC)) :=
  den_and (hc.dlive hh) (den_and (den_eq' (hc.dY hh) hb) (den_eq' (hc.den_col hM hh) hcc))

lemma den_exG {b cc : T} {B CC : ℕ} (hb : Den x Γ b B) (hcc : Den x Γ cc CC) :
    Den x Γ (exT c.Ng (gAtT c M b cc)) (bv (∃ h, L.GateAt MV B CC h)) :=
  (den_ex hc.Ng fun _ _ _ => (hc.cons _).den_gAt (hM.cons _) (hb.cons _) (hcc.cons _)
    den_var0).of_eq (bv_congr hc.ag.ex_gateAt_iff.symm)

lemma den_findG {b cc : T} {B CC : ℕ} (hb : Den x Γ b B) (hcc : Den x Γ cc CC)
    (hg : ∃ h, L.GateAt MV B CC h) :
    Den x Γ (findT c.Ng (gAtT c M b cc)) (Nat.find hg) := by
  refine (den_find hc.Ng fun k i _ => (hc.cons _).den_gAt (hM.cons _) (hb.cons _) (hcc.cons _)
    den_var0).of_eq ?_
  have hs := hc.ag.gateAt_iff.1 (Nat.find_spec hg)
  have h1 : Nat.find hg ≤ NG := le_of_lt (hc.ag.ng _ hs.1)
  have h2 : bv (L.live (Nat.find hg) = true ∧ s.Y (Nat.find hg) = B ∧
      s.col MV (Nat.find hg) = CC) ≠ 0 := bv_ne_zero.2 hs
  have h3 : ∀ j < Nat.find hg, bv (L.live j = true ∧ s.Y j = B ∧ s.col MV j = CC) = 0 :=
    fun j hj => bv_neg fun hj' => Nat.find_min hg hj (hc.ag.gateAt_iff.2 hj')
  exact findF_eq_of_spec h1 (fun _ => h2) h3

lemma den_exGR {b cc : T} {B CC : ℕ} (hb : Den x Γ b B) (hcc : Den x Γ cc CC) :
    Den x Γ (exGRT c M b cc) (bv (∃ h, L.GateAt MV B CC h ∧ L.hasR h = true)) := by
  refine (den_ex (P := fun i => (L.live i = true ∧ s.Y i = B ∧ s.col MV i = CC) ∧
    s.hasR L i = true) hc.Ng fun k i _ => ?_).of_eq (bv_congr hc.ag.ex_gateR_iff.symm)
  have hc' := hc.cons (k, i)
  have hi : Den x ((k, i) :: Γ) (varT k) i := den_var0
  exact den_and (hc'.den_gAt (hM.cons _) (hb.cons _) (hcc.cons _) hi) (hc'.den_hasR hi)

lemma den_wire {b ph cc h y : T} {B PH CC H Y : ℕ} (hb : Den x Γ b B) (hph : Den x Γ ph PH)
    (hcc : Den x Γ cc CC) (hh : Den x Γ h H) (hy : Den x Γ y Y) :
    Den x Γ (wireT c M b ph cc h y) (bv (Agree.WireS s L MV B PH CC H Y)) :=
  den_and (hc.dlive hy) (den_and (den_eq' (hc.dY hy) hb) (den_and
    (den_eq' (den_add (hc.dY hy) (den_c 1)) (hc.dY hh)) (den_and
      (den_eq' (hc.den_col hM hy) (den_add hcc hph))
      (den_le (den_add (hc.den_slot hM hh hy) hph) (hc.den_col hM hy)))))

lemma den_DDes {b ph cc : T} {B PH CC : ℕ} (hb : Den x Γ b B) (hph : Den x Γ ph PH)
    (hcc : Den x Γ cc CC) : Den x Γ (DDesT c M b ph cc) (bv (L.DDes MV B PH CC)) := by
  refine (den_ex hc.Ng fun k i _ => ?_).of_eq (bv_congr hc.ag.DDes_iff.symm)
  have hc' := hc.cons (k, i)
  have hi : Den x ((k, i) :: Γ) (varT k) i := den_var0
  exact den_and (hc'.dlive hi) (den_or
    (den_and (hc'.dk0 hi) (hc'.den_wire (hM.cons _) (hb.cons _) (hph.cons _) (hcc.cons _) hi
      (hc'.da0 hi)))
    (den_and (hc'.dk1 hi) (hc'.den_wire (hM.cons _) (hb.cons _) (hph.cons _) (hcc.cons _) hi
      (hc'.da1 hi))))

lemma den_colConst {cc : T} {CC : ℕ} (hcc : Den x Γ cc CC) :
    Den x Γ (colConstT c M cc) (L.colConst MV CC).toNat := by
  refine den_bool_of_bv (den_or (den_ex hc.Ng fun k i _ => ?_) (den_ex hc.Ng fun k i _ => ?_))
    hc.ag.colConst_iff
  · have hc' := hc.cons (k, i)
    have hi : Den x ((k, i) :: Γ) (varT k) i := den_var0
    exact den_and (hc'.den_gAt (hM.cons _) (den_c 1) (hcc.cons _) hi) (den_and (hc'.den_sS hi)
      (den_and ((den_not (hc'.dlive (hc'.den_sV hi))).of_eq (bv_congr (by simp)))
        (den_ne (hc'.dcv (hc'.den_sV hi)) (den_c 0))))
  · have hc' := hc.cons (k, i)
    have hi : Den x ((k, i) :: Γ) (varT k) i := den_var0
    exact den_and (hc'.den_gAt (hM.cons _) (den_c 1) (den_sub (hcc.cons _) (den_c 1)) hi)
      (den_and (den_eq' (den_mod (hcc.cons _) (den_c 2)) (den_c 1)) (den_and (hc'.den_dS hi)
        (den_and ((den_not (hc'.dlive (hc'.den_dV hi))).of_eq (bv_congr (by simp)))
          (den_ne (hc'.dcv (hc'.den_dV hi)) (den_c 0)))))

end LC.Ok

end FD

end PathChecking
