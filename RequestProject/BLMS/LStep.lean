module

public import RequestProject.BLMS.LLay

/-!
# One evaluation step on intervals in the loop language

`stepIP` computes `(toLC C).stepI l (a, b)`: the first and last true gate of layer `l + 1` when
exactly the gates of `[a, b)` of layer `l` are true.  The global variables (number of tokens,
gates, top layer, `N`, `D`) are described by `Glob`.
-/

@[expose] public section

namespace PathChecking

namespace BLMS

namespace LP

open LL

variable {C : Circuit} {w : Word} {K : ℕ}

/-! ## Boolean expressions -/

/-- conjunction of `0`/`1` values -/
def andB (a b : Ex V) : Ex V := .bin .mul a b
/-- disjunction of `0`/`1` values -/
def orB (a b : Ex V) : Ex V := .bin .lt (.c 0) (.bin .add a b)
/-- negation of a `0`/`1` value -/
def notB (a : Ex V) : Ex V := .bin .eq a (.c 0)
/-- `[a < b]` -/
def ltB (a b : Ex V) : Ex V := .bin .lt a b
/-- `[x ∈ [a, b)]` -/
def inIE (a b x : Ex V) : Ex V := andB (notB (ltB x a)) (ltB x b)

section
variable {ρ : Var → ℕ} {a b x : Ex V} {p q : Bool}

lemma eval_andB (ha : a.eval w K ρ = p.toNat) (hb : b.eval w K ρ = q.toNat) (hK : 1 ≤ K) :
    (andB a b).eval w K ρ = (p && q).toNat := by
  simp only [andB, eval_bin, ap_mul, ha, hb]
  cases p <;> cases q <;> simp <;> omega

lemma eval_orB (ha : a.eval w K ρ = p.toNat) (hb : b.eval w K ρ = q.toNat) (hK : 1 ≤ K) :
    (orB a b).eval w K ρ = (p || q).toNat := by
  simp only [orB, eval_bin, ap_lt, ap_add, eval_c, ha, hb, min_eq_left (Nat.zero_le K)]
  cases p <;> cases q <;> simp <;> omega

lemma eval_notB (ha : a.eval w K ρ = p.toNat) : (notB a).eval w K ρ = (!p).toNat := by
  simp only [notB, eval_bin, ap_eq, eval_c, ha, min_eq_left (Nat.zero_le K)]
  cases p <;> simp

lemma eval_ltB : (ltB a b).eval w K ρ = (decide (a.eval w K ρ < b.eval w K ρ)).toNat := by
  simp only [ltB, eval_bin, ap_lt]
  by_cases h : a.eval w K ρ < b.eval w K ρ <;> simp [h]

lemma eval_inIE (hK : 1 ≤ K) :
    (inIE a b x).eval w K ρ = (LC.inI (a.eval w K ρ) (b.eval w K ρ) (x.eval w K ρ)).toNat := by
  rw [inIE, eval_andB (eval_notB eval_ltB) eval_ltB hK]
  simp only [LC.inI]
  congr 1
  by_cases h1 : x.eval w K ρ < a.eval w K ρ <;> by_cases h2 : x.eval w K ρ < b.eval w K ρ <;>
    simp [h1, h2] <;> omega

end

/-! ## Global variables -/

/-- The global variables. -/
structure Glob (C : Circuit) (ρ : Var → ℕ) : Prop where
  nt : ρ vNT = (gts C).length
  ng : ρ vNG = C.length
  top : ρ vTop = Conc.top C
  n : ρ vN = (toLC C).N
  d : ρ vD = (toLC C).D

/-- The global variables. -/
def globs : List Var := [vNT, vNG, vTop, vN, vD]

lemma Glob.fr {ρ : Var → ℕ} (h : Glob C ρ) (ρ' : Var → ℕ) (hfr : ∀ z ∈ globs, ρ' z = ρ z) :
    Glob C ρ' :=
  ⟨by rw [hfr _ (by decide), h.nt], by rw [hfr _ (by decide), h.ng],
    by rw [hfr _ (by decide), h.top], by rw [hfr _ (by decide), h.n],
    by rw [hfr _ (by decide), h.d]⟩

lemma Glob.st {ρ : Var → ℕ} (h : Glob C ρ) (P : Pr V) (hP : ∀ z ∈ globs, z ∉ P.wr) :
    Glob C (st w K P ρ) :=
  h.fr _ (fun z hz => st_frame _ _ _ (hP z hz))

lemma Glob.upd {ρ : Var → ℕ} (h : Glob C ρ) (x : Var) (hx : x ∉ globs) (v : ℕ) :
    Glob C (Function.update ρ x v) :=
  h.fr _ (fun z hz => Function.update_of_ne (fun e => hx (by rw [← e]; exact hz)) _ _)

lemma globs_disj (P : Pr V) (h : (globs.all fun z => !(P.wr.contains z)) = true) :
    ∀ z ∈ globs, z ∉ P.wr := by
  intro z hz hm
  rw [List.all_eq_true] at h
  have := h z hz
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not]
    at this
  exact this hm

/-! ## Bounds -/

lemma bd_le (l : ℕ) : (toLC C).bd l ≤ C.length + 1 := by
  show firstF _ _ ≤ _
  rcases firstF_spec (fun i => decide (l ≤ Conc.lyr C i)) (C.length + 1) with ⟨h, -⟩ | ⟨h, -⟩ <;>
    omega

lemma N_le : (toLC C).N ≤ C.length + 1 := bd_le 1

lemma D_le : (toLC C).D ≤ C.length + 1 := by
  show Conc.top C + 1 ≤ _
  have := dep_le (C := C) (C.length - 1)
  unfold Conc.top; omega

/-! ## The step -/

/-- layer `l` of `stepIP` -/
abbrev vSl : Var := 40
/-- left end of the interval -/
abbrev vSa : Var := 41
/-- right end of the interval -/
abbrev vSb : Var := 42
/-- first true gate of the image -/
abbrev vSo1 : Var := 43
/-- last true gate of the image, plus one -/
abbrev vSo2 : Var := 44
/-- first gate of layer `l + 1` -/
abbrev vSb1 : Var := 45
/-- width of layer `l + 1` -/
abbrev vSw : Var := 46
/-- loop variable -/
abbrev vSk : Var := 47
/-- value of the current gate -/
abbrev vSg : Var := 48

/-- `vSb1 := bd (l + 1)`, `vSw := wid l`. -/
def layP : Pr V :=
  .seq (.set vBl (.bin .add (.v vSl) (.c 1))) (.seq bdP (.seq (.set vSb1 (.v vBd))
    (.seq (.set vBl (.bin .add (.v vSl) (.c 2))) (.seq bdP
      (.set vSw (.bin .sub (.v vBd) (.v vSb1)))))))

lemma layP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ)
    (hl : ρ vSl ≤ C.length) :
    st w K layP ρ vSb1 = (toLC C).bd (ρ vSl + 1) ∧ st w K layP ρ vSw = (toLC C).wid (ρ vSl) := by
  have hK := hE.nK
  unfold layP
  simp only [st_seq, st_set]
  have G1 := hG.upd vBl (by decide) ((Ex.bin .add (.v vSl) (.c 1) : Ex V).eval w K ρ)
  have e1 := bdP_spec hE hC _ G1.nt G1.ng G1.top
  have f1 : ∀ z ∉ bdP.wr, st w K bdP (Function.update ρ vBl
      ((Ex.bin .add (.v vSl) (.c 1) : Ex V).eval w K ρ)) z = Function.update ρ vBl
      ((Ex.bin .add (.v vSl) (.c 1) : Ex V).eval w K ρ) z := fun z hz => st_frame _ _ _ hz
  have G2 := G1.st (w := w) (K := K) bdP (globs_disj _ (by decide))
  generalize st w K bdP (Function.update ρ vBl
      ((Ex.bin .add (.v vSl) (.c 1) : Ex V).eval w K ρ)) = ρ2 at e1 f1 G2
  simp only [Function.update_self, eval_bin, ap_add, eval_v, eval_c,
    min_eq_left (show 1 ≤ K by omega), min_eq_left (show ρ vSl + 1 ≤ K by omega)] at e1
  have h2l : ρ2 vSl = ρ vSl := by rw [f1 _ (by decide)]; simp (config := {decide := true})
  have G3 := (G2.upd vSb1 (by decide) (ρ2 vBd)).upd vBl (by decide)
    ((Ex.bin .add (.v vSl) (.c 2) : Ex V).eval w K (Function.update ρ2 vSb1 (ρ2 vBd)))
  have e2 := bdP_spec hE hC _ G3.nt G3.ng G3.top
  have f2 : ∀ z ∉ bdP.wr, st w K bdP (Function.update (Function.update ρ2 vSb1 (ρ2 vBd)) vBl
      ((Ex.bin .add (.v vSl) (.c 2) : Ex V).eval w K (Function.update ρ2 vSb1 (ρ2 vBd)))) z =
      Function.update (Function.update ρ2 vSb1 (ρ2 vBd)) vBl
      ((Ex.bin .add (.v vSl) (.c 2) : Ex V).eval w K (Function.update ρ2 vSb1 (ρ2 vBd))) z :=
    fun z hz => st_frame _ _ _ hz
  simp only [eval_v]
  generalize st w K bdP (Function.update (Function.update ρ2 vSb1 (ρ2 vBd)) vBl
      ((Ex.bin .add (.v vSl) (.c 2) : Ex V).eval w K (Function.update ρ2 vSb1 (ρ2 vBd)))) = ρ5
    at e2 f2
  simp (config := {decide := true}) only [Function.update_self, Function.update_of_ne, ne_eq,
    eval_bin, ap_add, eval_v, eval_c, h2l, min_eq_left (show 2 ≤ K by omega),
    min_eq_left (show ρ vSl + 2 ≤ K by omega)] at e2
  have h5 : ρ5 vSb1 = ρ2 vBd := by
    rw [f2 _ (by decide)]; simp (config := {decide := true})
  refine ⟨?_, ?_⟩
  · simp (config := {decide := true}) only [Function.update_of_ne, ne_eq, h5, e1]
  · simp only [Function.update_self, eval_bin, ap_sub, eval_v, h5, e2, e1, LC.wid]

/-- The value of the current gate on `[vSa, vSb)`. -/
def gvalE : Ex V :=
  orB (andB (.v vGA) (andB (inIE (.v vSa) (.v vSb) (.v vGL)) (inIE (.v vSa) (.v vSb) (.v vGH))))
    (andB (notB (.v vGA)) (orB (inIE (.v vSa) (.v vSb) (.v vGL)) (inIE (.v vSa) (.v vSb) (.v vGH))))

lemma eval_gvalE {ρ : Var → ℕ} {i : ℕ} (hg : GateOut C i ρ) (hK : 1 ≤ K) :
    gvalE.eval w K ρ = ((toLC C).gvalB (ρ vSa) (ρ vSb) i).toNat := by
  have hA : (Ex.v vGA : Ex V).eval w K ρ = ((toLC C).isAnd i).toNat := hg.a
  rw [gvalE, eval_orB (eval_andB hA (eval_andB (eval_inIE hK) (eval_inIE hK) hK) hK)
    (eval_andB (eval_notB hA) (eval_orB (eval_inIE hK) (eval_inIE hK) hK) hK) hK]
  simp only [eval_v, hg.l, hg.h, LC.gvalB]
  cases (toLC C).isAnd i <;> simp

/-- Body of the scan of `stepIP`. -/
def scanBody : Pr V :=
  .seq (.set vGi (.bin .add (.v vSb1) (.v vSk))) (.seq gateP (.seq (.set vSg gvalE)
    (.ite (.v vSg) (.ite (.bin .lt (.v vSo1) (.v vSo2)) (.set vSo2 (.bin .add (.v vGi) (.c 1)))
      (.seq (.set vSo1 (.v vGi)) (.set vSo2 (.bin .add (.v vGi) (.c 1))))) .skip)))

/-- `(vSo1, vSo2) := stepI vSl (vSa, vSb)`. -/
def stepIP : Pr V :=
  .seq layP (.seq (.set vSo1 (.c 0)) (.seq (.set vSo2 (.c 0)) (.loop vSk (.v vSw) scanBody)))

lemma stepIP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ)
    (hl : ρ vSl ≤ C.length) :
    st w K stepIP ρ vSo1 = ((toLC C).stepI (ρ vSl) (ρ vSa, ρ vSb)).1 ∧
      st w K stepIP ρ vSo2 = ((toLC C).stepI (ρ vSl) (ρ vSa, ρ vSb)).2 := by
  have hK := hE.nK
  obtain ⟨e1, e2⟩ := layP_spec hE hC ρ hG hl
  have f1 : ∀ z ∉ layP.wr, st w K layP ρ z = ρ z := fun z hz => st_frame _ _ _ hz
  have G1 := hG.st (w := w) (K := K) layP (globs_disj _ (by decide))
  unfold stepIP
  simp only [st_seq, st_set, eval_c, min_eq_left (Nat.zero_le K)]
  generalize st w K layP ρ = ρ1 at e1 e2 f1 G1
  set ρ2 := Function.update (Function.update ρ1 vSo1 0) vSo2 0 with hρ2
  have hw : (Ex.v vSw : Ex V).eval w K ρ2 = (toLC C).wid (ρ vSl) := by
    simp (config := {decide := true}) [ρ2, e2]
  have key := st_loop (w := w) (K := K) vSk (.v vSw) scanBody ρ2
    (fun q k => (toLC C).scanStep (ρ vSa, ρ vSb) q ((toLC C).bd (ρ vSl + 1) + k)) (0, 0)
    (fun ρ' q => ρ' vSo1 = q.1 ∧ ρ' vSo2 = q.2)
    ⟨by simp (config := {decide := true}) [ρ2], by simp [ρ2]⟩ (by
      intro k hk ρ' q hfr ⟨h1, h2⟩
      rw [hw] at hk
      have hfr' : ∀ z, z ∉ (Pr.loop vSk (.v vSw) scanBody).wr → ρ' z = ρ1 z := by
        intro z hz; rw [hfr z hz, hρ2, Function.update_of_ne, Function.update_of_ne]
        · intro e; subst e; exact hz (by decide)
        · intro e; subst e; exact hz (by decide)
      have Gq := G1.fr ρ' (fun z hz => hfr' z (by revert z; decide))
      have hb1 : ρ' vSb1 = (toLC C).bd (ρ vSl + 1) := by rw [hfr' _ (by decide), e1]
      have ha : ρ' vSa = ρ vSa := by rw [hfr' _ (by decide), f1 _ (by decide)]
      have hb : ρ' vSb = ρ vSb := by rw [hfr' _ (by decide), f1 _ (by decide)]
      have hik : (toLC C).bd (ρ vSl + 1) + k ≤ C.length := by
        have := bd_le (C := C) (ρ vSl + 2)
        have hk' : k < (toLC C).bd (ρ vSl + 2) - (toLC C).bd (ρ vSl + 1) := hk
        omega
      unfold scanBody
      simp only [st_seq, st_set]
      have hi : (Ex.bin .add (.v vSb1) (.v vSk) : Ex V).eval w K (Function.update ρ' vSk k) =
          (toLC C).bd (ρ vSl + 1) + k := by
        simp (config := {decide := true}) [hb1]; omega
      rw [hi]
      set i := (toLC C).bd (ρ vSl + 1) + k
      set ρ3 := Function.update (Function.update ρ' vSk k) vGi i
      have G3 := (Gq.upd vSk (by decide) k).upd vGi (by decide) i
      have g := gateP_spec hE hC ρ3 G3.nt G3.ng
      have hgi : ρ3 vGi = i := by simp [ρ3]
      rw [hgi] at g
      have f3 : ∀ z ∉ gateP.wr, st w K gateP ρ3 z = ρ3 z := fun z hz => st_frame _ _ _ hz
      generalize st w K gateP ρ3 = ρ4 at g f3
      have ha4 : ρ4 vSa = ρ vSa := by
        rw [f3 _ (by decide)]; simp (config := {decide := true}) [ρ3, ha]
      have hb4 : ρ4 vSb = ρ vSb := by
        rw [f3 _ (by decide)]; simp (config := {decide := true}) [ρ3, hb]
      have hgv := eval_gvalE (w := w) (K := K) g (by omega)
      rw [ha4, hb4] at hgv
      rw [hgv]
      have h14 : ρ4 vSo1 = q.1 := by
        rw [f3 _ (by decide)]; simp (config := {decide := true}) [ρ3, h1]
      have h24 : ρ4 vSo2 = q.2 := by
        rw [f3 _ (by decide)]; simp (config := {decide := true}) [ρ3, h2]
      have hi4 : ρ4 vGi = i := by
        rw [f3 _ (by decide)]; simp (config := {decide := true}) [ρ3]
      rw [st_ite]
      unfold LC.scanStep
      by_cases hgb : (toLC C).gvalB (ρ vSa) (ρ vSb) i = true
      · rw [if_pos (by simp [hgb]), if_pos hgb, st_ite]
        simp (config := {decide := true}) only [eval_bin, ap_lt, eval_v, Function.update_of_ne,
          ne_eq, h14, h24]
        by_cases hq : q.1 < q.2
        · rw [if_pos (by simp [hq]), if_pos hq]
          simp (config := {decide := true}) [h14, hi4, min_eq_left (show i + 1 ≤ K by omega),
            min_eq_left (show 1 ≤ K by omega)]
        · rw [if_neg (by simp [hq]), if_neg hq]
          simp (config := {decide := true}) [hi4, min_eq_left (show i + 1 ≤ K by omega),
            min_eq_left (show 1 ≤ K by omega)]
      · rw [if_neg (by simp at hgb; simp [hgb]), if_neg hgb]
        simp (config := {decide := true}) [h14, h24])
  rw [hw] at key
  exact key

end LP

end BLMS

end PathChecking
