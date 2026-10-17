module

public import RequestProject.BLMS.LStep

/-!
# Classification of pairs of intervals in the loop language

`iterIP` computes `(toLC C).iterI D`, `bridgeP` and `rspanP` the tests `bridgeB` and `rspanB`,
`pstepP` one step of the simulation of a pair of intervals and `classifyP` the classification.
-/

@[expose] public section

namespace PathChecking

namespace BLMS

namespace LP

open LL

variable {C : Circuit} {w : Word} {K : ℕ}

/-- loop variable of `iterIP` -/
abbrev vIl : Var := 49
/-- result of `bridgeP` -/
abbrev vX1 : Var := 54
/-- result of `rspanP` -/
abbrev vX2 : Var := 55
/-- loop variable -/
abbrev vXk : Var := 56
/-- tag of the simulation state -/
abbrev vPt : Var := 57
/-- `ia` -/
abbrev vPa : Var := 58
/-- `ib` -/
abbrev vPb : Var := 59
/-- `ja` -/
abbrev vPc : Var := 60
/-- `jb` -/
abbrev vPd : Var := 61
/-- image of `[ia, ib)` -/
abbrev vU1 : Var := 62
/-- image of `[ia, ib)` -/
abbrev vU2 : Var := 63
/-- image of `[ja, jb)` -/
abbrev vW1 : Var := 64
/-- image of `[ja, jb)` -/
abbrev vW2 : Var := 65
/-- loop variable of `classifyP` -/
abbrev vQl : Var := 66

/-! ## Iterating the step -/

/-- `(vSa, vSb) := iterI D (vSa, vSb)`. -/
def iterIP : Pr V :=
  .loop vIl (.v vD) (.seq (.set vSl (.v vIl)) (.seq stepIP (.seq (.set vSa (.v vSo1))
    (.set vSb (.v vSo2)))))

lemma iterI_eq (c : LC) (p : ℕ × ℕ) (k : ℕ) :
    c.iterI k p = (List.range k).foldl (fun q l => c.stepI l q) p := by
  induction k with
  | zero => rfl
  | succ k ih => rw [foldl_range_succ, ← ih]; rfl

lemma iterIP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ) :
    st w K iterIP ρ vSa = ((toLC C).iterI (toLC C).D (ρ vSa, ρ vSb)).1 ∧
      st w K iterIP ρ vSb = ((toLC C).iterI (toLC C).D (ρ vSa, ρ vSb)).2 := by
  have hD : (Ex.v vD : Ex V).eval w K ρ = (toLC C).D := hG.d
  have key := st_loop (w := w) (K := K) vIl (.v vD) (.seq (.set vSl (.v vIl)) (.seq stepIP
    (.seq (.set vSa (.v vSo1)) (.set vSb (.v vSo2))))) ρ (fun q l => (toLC C).stepI l q)
    (ρ vSa, ρ vSb) (fun ρ' q => ρ' vSa = q.1 ∧ ρ' vSb = q.2) ⟨rfl, rfl⟩ (by
      intro l hl ρ' q hfr ⟨h1, h2⟩
      rw [hD] at hl
      have Gq := hG.fr ρ' (fun z hz => hfr z (by revert z; decide))
      simp only [st_seq, st_set, eval_v]
      have G1 := (Gq.upd vIl (by decide) l).upd vSl (by decide) (Function.update ρ' vIl l vIl)
      obtain ⟨s1, s2⟩ := stepIP_spec hE hC _ G1 (by
        have := D_le (C := C); simp; omega)
      simp (config := {decide := true}) only [Function.update_self, Function.update_of_ne,
        ne_eq, h1, h2] at s1 s2
      refine ⟨?_, ?_⟩
      · simp (config := {decide := true}) [s1]
      · simp (config := {decide := true}) [s2])
  rw [iterI_eq]
  rw [hD] at key
  exact key

/-! ## Scanning the gates of a layer -/

/-- Read gate `vSb1 + vXk`. -/
def gbody : Pr V := .seq (.set vGi (.bin .add (.v vSb1) (.v vXk))) gateP

lemma gbody_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ)
    (l : ℕ) (hb1 : ρ vSb1 = (toLC C).bd (l + 1)) (k : ℕ) (hk : k < (toLC C).wid l) :
    GateOut C ((toLC C).bd (l + 1) + k) (st w K gbody (Function.update ρ vXk k)) ∧
      ∀ z ∉ gateP.wr, z ≠ vGi → z ≠ vXk → st w K gbody (Function.update ρ vXk k) z = ρ z := by
  have hK := hE.nK
  have hik : (toLC C).bd (l + 1) + k ≤ C.length := by
    have := bd_le (C := C) (l + 2)
    have hk' : k < (toLC C).bd (l + 2) - (toLC C).bd (l + 1) := hk
    omega
  unfold gbody
  simp only [st_seq, st_set]
  have hi : (Ex.bin .add (.v vSb1) (.v vXk) : Ex V).eval w K (Function.update ρ vXk k) =
      (toLC C).bd (l + 1) + k := by
    simp (config := {decide := true}) [hb1]; omega
  rw [hi]
  have G3 := (hG.upd vXk (by decide) k).upd vGi (by decide) ((toLC C).bd (l + 1) + k)
  have g := gateP_spec hE hC _ G3.nt G3.ng
  simp only [Function.update_self] at g
  refine ⟨g, fun z hz h1 h2 => ?_⟩
  rw [st_frame _ _ _ hz, Function.update_of_ne h1, Function.update_of_ne h2]

lemma toNat_ne_zero (b : Bool) : b.toNat ≠ 0 ↔ b = true := by cases b <;> simp

/-- `vX1 := bridgeB vSl vPa vPb vPc vPd` (needs `vSb1`, `vSw` from `layP`). -/
def bridgeP : Pr V :=
  anyRP vX1 vXk vSw gbody (andB (.v vGA) (andB (inIE (.v vPa) (.v vPb) (.v vGL))
    (inIE (.v vPc) (.v vPd) (.v vGH))))

/-- `vX2 := rspanB vSl vPa vPb vPd` (needs `vSb1`, `vSw` from `layP`). -/
def rspanP : Pr V :=
  anyRP vX2 vXk vSw gbody (andB (.v vGA) (andB (inIE (.v vPa) (.v vPb) (.v vGL))
    (notB (ltB (.v vGH) (.v vPd)))))

lemma bridgeP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ)
    (l : ℕ) (hb1 : ρ vSb1 = (toLC C).bd (l + 1)) (hw : ρ vSw = (toLC C).wid l) :
    st w K bridgeP ρ vX1 = ((toLC C).bridgeB l (ρ vPa) (ρ vPb) (ρ vPc) (ρ vPd)).toNat := by
  have hK := hE.nK
  unfold bridgeP
  rw [anyRP_spec _ _ _ _ _ ρ (fun k => (toLC C).isAnd ((toLC C).bd (l + 1) + k) &&
    LC.inI (ρ vPa) (ρ vPb) ((toLC C).lo ((toLC C).bd (l + 1) + k)) &&
    LC.inI (ρ vPc) (ρ vPd) ((toLC C).hi ((toLC C).bd (l + 1) + k))) (by decide) (by decide)
    (by decide) (by omega), hw]
  · rfl
  · intro p hp ρ' hfr
    rw [hw] at hp
    have hf : ∀ z ∈ [vNT, vNG, vTop, vN, vD, vSb1, vPa, vPb, vPc, vPd], ρ' z = ρ z := by
      intro z hz; exact hfr z (by revert z; decide) (by revert z; decide) (by revert z; decide)
    have Gq := hG.fr ρ' (fun z hz => hf z (by revert z; decide))
    obtain ⟨g, gf⟩ := gbody_spec hE hC ρ' Gq l (by rw [hf _ (by decide), hb1]) p hp
    rw [eval_andB (show (Ex.v vGA : Ex V).eval w K (st w K gbody (Function.update ρ' vXk p)) = _ from g.a) (eval_andB (eval_inIE (by omega)) (eval_inIE (by omega)) (by omega))
      (by omega), toNat_ne_zero]
    simp only [eval_v, g.l, g.h, gf vPa (by decide) (by decide) (by decide),
      gf vPb (by decide) (by decide) (by decide), gf vPc (by decide) (by decide) (by decide),
      gf vPd (by decide) (by decide) (by decide), hf vPa (by decide), hf vPb (by decide),
      hf vPc (by decide), hf vPd (by decide), Bool.and_assoc]

lemma rspanP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ)
    (l : ℕ) (hb1 : ρ vSb1 = (toLC C).bd (l + 1)) (hw : ρ vSw = (toLC C).wid l) :
    st w K rspanP ρ vX2 = ((toLC C).rspanB l (ρ vPa) (ρ vPb) (ρ vPd)).toNat := by
  have hK := hE.nK
  unfold rspanP
  rw [anyRP_spec _ _ _ _ _ ρ (fun k => (toLC C).isAnd ((toLC C).bd (l + 1) + k) &&
    LC.inI (ρ vPa) (ρ vPb) ((toLC C).lo ((toLC C).bd (l + 1) + k)) &&
    decide (ρ vPd ≤ (toLC C).hi ((toLC C).bd (l + 1) + k))) (by decide) (by decide)
    (by decide) (by omega), hw]
  · rfl
  · intro p hp ρ' hfr
    rw [hw] at hp
    have hf : ∀ z ∈ [vNT, vNG, vTop, vN, vD, vSb1, vPa, vPb, vPc, vPd], ρ' z = ρ z := by
      intro z hz; exact hfr z (by revert z; decide) (by revert z; decide) (by revert z; decide)
    have Gq := hG.fr ρ' (fun z hz => hf z (by revert z; decide))
    obtain ⟨g, gf⟩ := gbody_spec hE hC ρ' Gq l (by rw [hf _ (by decide), hb1]) p hp
    rw [eval_andB (show (Ex.v vGA : Ex V).eval w K (st w K gbody (Function.update ρ' vXk p)) = _ from g.a) (eval_andB (eval_inIE (by omega)) (eval_notB eval_ltB) (by omega))
      (by omega), toNat_ne_zero]
    simp only [eval_v, g.l, g.h, gf vPa (by decide) (by decide) (by decide),
      gf vPb (by decide) (by decide) (by decide),
      gf vPd (by decide) (by decide) (by decide), hf vPa (by decide), hf vPb (by decide),
      hf vPd (by decide), Bool.and_assoc]
    cases (toLC C).isAnd ((toLC C).bd (l + 1) + p) <;> simp

/-! ## One step of the simulation of a pair of intervals -/

/-- The run branch of `pstep`, with precomputed tests and images. -/
def decF (b1 b2 : Bool) (u v : ℕ × ℕ) : LC.PSt :=
  if b1 = true then .done .merge
  else if u.1 < u.2 ∧ v.1 < v.2 ∧ v.1 ≤ u.2 then .done .merge
  else if ¬ u.1 < u.2 ∧ ¬ v.1 < v.2 then (if b2 = true then .done .push else .done .disc)
  else if ¬ v.1 < v.2 then .done .push
  else if ¬ u.1 < u.2 then .done .disc
  else .run u.1 u.2 v.1 v.2

lemma pstep_run (c : LC) (l ia ib ja jb : ℕ) :
    c.pstep l (.run ia ib ja jb) = decF (c.bridgeB l ia ib ja jb) (c.rspanB l ia ib jb)
      (c.stepI l (ia, ib)) (c.stepI l (ja, jb)) := rfl

/-- Representation of a simulation state. -/
def PRep (ρ : Var → ℕ) : LC.PSt → Prop
  | .run a b c d => ρ vPt = 0 ∧ ρ vPa = a ∧ ρ vPb = b ∧ ρ vPc = c ∧ ρ vPd = d
  | .done .merge => ρ vPt = 1
  | .done .push => ρ vPt = 2
  | .done .disc => ρ vPt = 3

lemma PRep_fr {ρ ρ' : Var → ℕ} {s : LC.PSt} (hs : PRep ρ s)
    (h : ∀ z ∈ [vPt, vPa, vPb, vPc, vPd], ρ' z = ρ z) : PRep ρ' s := by
  rcases s with ⟨a, b, c, d⟩ | ⟨_ | _ | _⟩ <;>
    simp only [PRep, h vPt (by decide), h vPa (by decide), h vPb (by decide), h vPc (by decide),
      h vPd (by decide)] at hs ⊢ <;> exact hs

/-- The decision of `pstepP`. -/
def decP : Pr V :=
  .ite (.v vX1) (.set vPt (.c 1))
   (.ite (andB (ltB (.v vU1) (.v vU2)) (andB (ltB (.v vW1) (.v vW2)) (notB (ltB (.v vU2) (.v vW1)))))
      (.set vPt (.c 1))
    (.ite (andB (notB (ltB (.v vU1) (.v vU2))) (notB (ltB (.v vW1) (.v vW2))))
      (.ite (.v vX2) (.set vPt (.c 2)) (.set vPt (.c 3)))
     (.ite (notB (ltB (.v vW1) (.v vW2))) (.set vPt (.c 2))
      (.ite (notB (ltB (.v vU1) (.v vU2))) (.set vPt (.c 3))
        (.seq (.set vPa (.v vU1)) (.seq (.set vPb (.v vU2)) (.seq (.set vPc (.v vW1))
          (.set vPd (.v vW2)))))))))

lemma decP_spec (ρ : Var → ℕ) (hK : 3 ≤ K) (b1 b2 : Bool) (u v : ℕ × ℕ) (h0 : ρ vPt = 0)
    (h1 : ρ vX1 = b1.toNat) (h2 : ρ vX2 = b2.toNat) (hu1 : ρ vU1 = u.1) (hu2 : ρ vU2 = u.2)
    (hv1 : ρ vW1 = v.1) (hv2 : ρ vW2 = v.2) :
    PRep (st w K decP ρ) (decF b1 b2 u v) := by
  have hK1 : 1 ≤ K := by omega
  have c2 : (andB (ltB (.v vU1) (.v vU2)) (andB (ltB (.v vW1) (.v vW2))
      (notB (ltB (.v vU2) (.v vW1)))) : Ex V).eval w K ρ =
      (decide (u.1 < u.2) && (decide (v.1 < v.2) && !decide (u.2 < v.1))).toNat := by
    rw [eval_andB eval_ltB (eval_andB eval_ltB (eval_notB eval_ltB) hK1) hK1]
    simp [hu1, hu2, hv1, hv2]
  have c3 : (andB (notB (ltB (.v vU1) (.v vU2))) (notB (ltB (.v vW1) (.v vW2))) : Ex V).eval w K ρ
      = (!decide (u.1 < u.2) && !decide (v.1 < v.2)).toNat := by
    rw [eval_andB (eval_notB eval_ltB) (eval_notB eval_ltB) hK1]
    simp [hu1, hu2, hv1, hv2]
  have c4 : (notB (ltB (.v vW1) (.v vW2)) : Ex V).eval w K ρ = (!decide (v.1 < v.2)).toNat := by
    rw [eval_notB eval_ltB]; simp [hv1, hv2]
  have c5 : (notB (ltB (.v vU1) (.v vU2)) : Ex V).eval w K ρ = (!decide (u.1 < u.2)).toNat := by
    rw [eval_notB eval_ltB]; simp [hu1, hu2]
  have hx1 : (Ex.v vX1 : Ex V).eval w K ρ = b1.toNat := h1
  have hx2 : (Ex.v vX2 : Ex V).eval w K ρ = b2.toNat := h2
  unfold decP decF
  simp only [st_ite, hx1, hx2, c2, c3, c4, c5, toNat_ne_zero]
  by_cases hb1 : b1 = true
  · simp [hb1, PRep, min_eq_left hK1]
  by_cases hu : u.1 < u.2 <;> by_cases hv : v.1 < v.2 <;> by_cases hvu : v.1 ≤ u.2 <;>
    by_cases hb2 : b2 = true <;>
    simp (config := {decide := true}) [hb1, hb2, hu, hv, hvu, PRep, min_eq_left hK1,
      min_eq_left (show 2 ≤ K by omega), min_eq_left hK, h0, hu1, hu2, hv1, hv2]

/-- `x, y := stepI vSl (ra, rb)`. -/
def imgP (x y ra rb : Var) : Pr V :=
  .seq (.set vSa (.v ra)) (.seq (.set vSb (.v rb)) (.seq stepIP (.seq (.set x (.v vSo1))
    (.set y (.v vSo2)))))

lemma imgP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ)
    (hl : ρ vSl ≤ C.length) (x y ra rb : Var) (hxy : x ≠ y) (hx : vSo2 ≠ x) (hrb : rb ≠ vSa) :
    st w K (imgP x y ra rb) ρ x = ((toLC C).stepI (ρ vSl) (ρ ra, ρ rb)).1 ∧
      st w K (imgP x y ra rb) ρ y = ((toLC C).stepI (ρ vSl) (ρ ra, ρ rb)).2 := by
  unfold imgP
  simp only [st_seq, st_set, eval_v, Function.update_of_ne hrb]
  have G1 := (hG.upd vSa (by decide) (ρ ra)).upd vSb (by decide) (ρ rb)
  obtain ⟨s1, s2⟩ := stepIP_spec hE hC _ G1 (by simpa using hl)
  simp (config := {decide := true}) only [Function.update_self, Function.update_of_ne, ne_eq]
    at s1 s2
  refine ⟨?_, ?_⟩
  · simp only [Function.update_of_ne hxy, Function.update_self, s1]
  · simp only [Function.update_self, Function.update_of_ne hx, s2]

/-- The run branch of `pstepP`. -/
def runStepP : Pr V :=
  .seq layP (.seq bridgeP (.seq rspanP (.seq (imgP vU1 vU2 vPa vPb)
    (.seq (imgP vW1 vW2 vPc vPd) decP))))

/-- One step of the simulation of a pair of intervals at layer `vSl`. -/
def pstepP : Pr V := .ite (.bin .eq (.v vPt) (.c 0)) runStepP .skip

lemma pstepP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ)
    (hl : ρ vSl ≤ C.length) (s : LC.PSt) (hs : PRep ρ s) :
    PRep (st w K pstepP ρ) ((toLC C).pstep (ρ vSl) s) := by
  have hK := hE.nK
  unfold pstepP
  rcases s with ⟨a, b, c, d⟩ | ⟨_ | _ | _⟩
  · obtain ⟨h0, ha, hb, hc, hd⟩ := hs
    rw [st_ite_pos (by simp [h0]), pstep_run]
    unfold runStepP
    simp only [st_seq]
    obtain ⟨e1, e2⟩ := layP_spec hE hC ρ hG hl
    have f1 : ∀ z ∉ layP.wr, st w K layP ρ z = ρ z := fun z hz => st_frame _ _ _ hz
    have G1 := hG.st (w := w) (K := K) layP (globs_disj _ (by decide))
    generalize st w K layP ρ = ρ1 at e1 e2 f1 G1
    have x1 := bridgeP_spec hE hC ρ1 G1 _ e1 e2
    have f2 : ∀ z ∉ bridgeP.wr, st w K bridgeP ρ1 z = ρ1 z := fun z hz => st_frame _ _ _ hz
    have G2 := G1.st (w := w) (K := K) bridgeP (globs_disj _ (by decide))
    generalize st w K bridgeP ρ1 = ρ2 at x1 f2 G2
    have x2 := rspanP_spec hE hC ρ2 G2 (ρ vSl) (by rw [f2 _ (by decide), e1])
      (by rw [f2 _ (by decide), e2])
    have f3 : ∀ z ∉ rspanP.wr, st w K rspanP ρ2 z = ρ2 z := fun z hz => st_frame _ _ _ hz
    have G3 := G2.st (w := w) (K := K) rspanP (globs_disj _ (by decide))
    generalize st w K rspanP ρ2 = ρ3 at x2 f3 G3
    have hl3 : ρ3 vSl = ρ vSl := by
      rw [f3 _ (by decide), f2 _ (by decide), f1 _ (by decide)]
    obtain ⟨u1, u2⟩ := imgP_spec hE hC ρ3 G3 (by omega) vU1 vU2 vPa vPb (by decide)
      (by decide) (by decide)
    have f4 : ∀ z ∉ (imgP vU1 vU2 vPa vPb).wr, st w K (imgP vU1 vU2 vPa vPb) ρ3 z = ρ3 z :=
      fun z hz => st_frame _ _ _ hz
    have G4 := G3.st (w := w) (K := K) (imgP vU1 vU2 vPa vPb) (globs_disj _ (by decide))
    generalize st w K (imgP vU1 vU2 vPa vPb) ρ3 = ρ4 at u1 u2 f4 G4
    have hl4 : ρ4 vSl = ρ vSl := by rw [f4 _ (by decide), hl3]
    obtain ⟨v1, v2⟩ := imgP_spec hE hC ρ4 G4 (by omega) vW1 vW2 vPc vPd (by decide)
      (by decide) (by decide)
    have f5 : ∀ z ∉ (imgP vW1 vW2 vPc vPd).wr, st w K (imgP vW1 vW2 vPc vPd) ρ4 z = ρ4 z :=
      fun z hz => st_frame _ _ _ hz
    generalize st w K (imgP vW1 vW2 vPc vPd) ρ4 = ρ5 at v1 v2 f5
    have q : ∀ z ∈ [vPa, vPb, vPc, vPd, vPt], ρ3 z = ρ z := by
      intro z hz
      rw [f3 _ (by revert z; decide), f2 _ (by revert z; decide), f1 _ (by revert z; decide)]
    have p1 : ∀ z ∈ [vPa, vPb, vPc, vPd, vPt], ρ1 z = ρ z := by
      intro z hz; rw [f1 _ (by revert z; decide)]
    have p2 : ∀ z ∈ [vPa, vPb, vPc, vPd, vPt], ρ2 z = ρ z := by
      intro z hz; rw [f2 _ (by revert z; decide), f1 _ (by revert z; decide)]
    rw [hl4, f4 _ (by decide), f4 _ (by decide), q _ (by decide), q _ (by decide), hc, hd] at v1 v2
    rw [hl3, q _ (by decide), q _ (by decide), ha, hb] at u1 u2
    rw [p1 vPa (by decide), p1 vPb (by decide), p1 vPc (by decide), p1 vPd (by decide),
      ha, hb, hc, hd] at x1
    rw [p2 vPa (by decide), p2 vPb (by decide), p2 vPd (by decide), ha, hb, hd] at x2
    apply decP_spec (w := w) (K := K) ρ5 (by have := hE.lenK; omega)
    · rw [f5 _ (by decide), f4 _ (by decide), q _ (by decide), h0]
    · rw [f5 _ (by decide), f4 _ (by decide), f3 _ (by decide), x1]
    · rw [f5 _ (by decide), f4 _ (by decide), x2]
    · rw [f5 _ (by decide), u1]
    · rw [f5 _ (by decide), u2]
    · exact v1
    · exact v2
  · rw [st_ite_neg (by simp [show ρ vPt = 1 from hs])]; exact hs
  · rw [st_ite_neg (by simp [show ρ vPt = 2 from hs])]; exact hs
  · rw [st_ite_neg (by simp [show ρ vPt = 3 from hs])]; exact hs

/-- `vPt := ` the code of `classify (vPa, vPb) (vPc, vPd)` (`1` merge, `2` push, else disc). -/
def classifyP : Pr V :=
  .seq (.set vPt (.c 0)) (.loop vQl (.v vD) (.seq (.set vSl (.v vQl)) pstepP))

set_option maxRecDepth 100000 in
lemma classifyP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ) :
    PRep (st w K classifyP ρ) ((toLC C).pfold (toLC C).D (ρ vPa, ρ vPb) (ρ vPc, ρ vPd)) := by
  unfold classifyP
  simp only [st_seq, st_set, eval_c, min_eq_left (Nat.zero_le K)]
  have G1 := hG.upd vPt (by decide) 0
  have hD : (Ex.v vD : Ex V).eval w K (Function.update ρ vPt 0) = (toLC C).D := G1.d
  have key := st_loop (w := w) (K := K) vQl (.v vD) (.seq (.set vSl (.v vQl)) pstepP)
    (Function.update ρ vPt 0) (fun s l => (toLC C).pstep l s) (.run (ρ vPa) (ρ vPb) (ρ vPc) (ρ vPd))
    (fun ρ' s => PRep ρ' s) (by simp (config := {decide := true}) [PRep]) (by
      intro l hl ρ' s hfr hs
      rw [hD] at hl
      have Gq := G1.fr ρ' (fun z hz => hfr z (globs_disj _ (by decide) z hz))
      simp only [st_seq, st_set, eval_v, Function.update_self]
      have G2 := (Gq.upd vQl (by decide) l).upd vSl (by decide) l
      have := pstepP_spec hE hC _ G2 (by have := D_le (C := C); simp; omega) s
        (PRep_fr hs (fun z hz => by
          rw [Function.update_of_ne, Function.update_of_ne] <;>
            (intro e; subst e; revert hz; decide)))
      simpa using this)
  rw [hD] at key
  exact key

end LP

end BLMS

end PathChecking
