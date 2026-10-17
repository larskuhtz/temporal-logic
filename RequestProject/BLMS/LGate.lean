module

public import RequestProject.BLMS.LTok

/-!
# Reading gates in the loop language

`gateP` reads gate `vGi` of the input circuit and stores whether it is an `AND` gate, its first
and last argument, whether it is a constant and whether it is the constant `true` (for the
extra gate `C.length` and beyond: the values of `toLC C`).
-/

@[expose] public section

namespace PathChecking

namespace BLMS

namespace LP

open LL

/-! ## Variables -/

/-- number of tokens -/
abbrev vNT : Var := 0
/-- number of gates -/
abbrev vNG : Var := 1
/-- gate to read -/
abbrev vGi : Var := 10
/-- `AND` gate -/
abbrev vGA : Var := 11
/-- first argument -/
abbrev vGL : Var := 12
/-- last argument -/
abbrev vGH : Var := 13
/-- constant -/
abbrev vGC : Var := 14
/-- constant `true` -/
abbrev vGT : Var := 15
/-- start of the gate -/
abbrev vGS : Var := 16
/-- tag counter -/
abbrev vGcnt : Var := 17
/-- loop variable -/
abbrev vGp : Var := 18
/-- start of a number -/
abbrev vRq : Var := 19
/-- end of a number -/
abbrev vRe : Var := 20
/-- value of a number -/
abbrev vRv : Var := 21
/-- loop variable -/
abbrev vRj : Var := 22
/-- loop variable -/
abbrev vRp : Var := 23
/-- tag code -/
abbrev vTg : Var := 24
/-- end of the first argument -/
abbrev vE1 : Var := 25

/-- The environment: the input encodes `C` and the cap is large. -/
structure Env (C : Circuit) (w : Word) (K : ℕ) : Prop where
  hw : w = encodeToks (gts C)
  hK : 4 * (w.length + 2) ^ 2 + 100 ≤ K

variable {C : Circuit} {w : Word} {K : ℕ}

lemma Env.len (hE : Env C w K) : w.length = 5 * (gts C).length := by
  rw [hE.hw]; exact SQ.encodeToks_length _

lemma Env.gts_le (hE : Env C w K) : (gts C).length ≤ w.length := by
  have := hE.len; omega

lemma Env.K_ge (hE : Env C w K) : 4 * (w.length + 2) ^ 2 + 100 ≤ K := hE.hK

lemma Env.lenK (hE : Env C w K) : w.length + 40 ≤ K := by
  have := hE.hK; nlinarith

lemma Env.tok (hE : Env C w K) (ρ : Var → ℕ) (p : Ex V) (hp : p.eval w K ρ < (gts C).length) :
    (tokE p).eval w K ρ = tc C (p.eval w K ρ) := by
  rw [eval_tokE (gts C) hE.hw ρ p hp hE.lenK, tc_eq hp]

lemma Env.n_le (hE : Env C w K) : C.length ≤ (gts C).length := by
  rw [gts_length]
  have : ∀ i ≤ C.length, i ≤ offs C i := by
    intro i
    induction i with
    | zero => intro _; omega
    | succ i ih =>
      intro hi
      rw [offs_succ (by omega)]
      have := toks_pos C[i]
      have := ih (by omega)
      omega
  exact this _ le_rfl

/-! ## Finding the start of a gate -/

/-- Body of the scan for the start of a gate. -/
def gsBody : Pr V :=
  .ite (.bin .lt (.c 4) (tokE (.v vGp)))
    (.seq (.ite (.bin .eq (.v vGcnt) (.v vGi)) (.set vGS (.v vGp)) .skip)
      (.set vGcnt (.bin .add (.v vGcnt) (.c 1))))
    .skip

/-- Scan for the start of gate `vGi` (and count the gates). -/
def gstartP : Pr V :=
  .seq (.set vGS (.c 0)) (.seq (.set vGcnt (.c 0)) (.loop vGp (.v vNT) gsBody))

lemma gsBody_spec (hE : Env C w K) (ρ' : Var → ℕ) (p : ℕ) (hp : p < (gts C).length)
    (a : ℕ × ℕ) (h1 : ρ' vGS = a.1) (h2 : ρ' vGcnt = a.2) (h3 : a.2 ≤ p) :
    st w K gsBody (Function.update ρ' vGp p) vGS = (gsF C (ρ' vGi) a p).1 ∧
    st w K gsBody (Function.update ρ' vGp p) vGcnt = (gsF C (ρ' vGi) a p).2 := by
  have hK := hE.lenK
  have hg := hE.gts_le
  have htok : (tokE (.v vGp) : Ex V).eval w K (Function.update ρ' vGp p) = tc C p := by
    rw [hE.tok _ _ (by simpa using hp)]; simp
  unfold gsBody gsF
  rw [st_ite]
  simp only [eval_bin, ap_lt, htok, eval_c]
  rw [min_eq_left (show 4 ≤ K by omega)]
  by_cases ht : 4 < tc C p
  · rw [if_pos ht, if_pos (by simp), if_pos (by omega)]
    simp only [st_seq, st_set, eval_bin, ap_add, eval_v, eval_c]
    rw [st_ite]
    simp (config := {decide := true}) only [eval_bin, ap_eq, eval_v, Function.update_of_ne,
      ne_eq, h2]
    by_cases hc : a.2 = ρ' vGi
    · rw [if_pos hc, if_pos (by simp), if_pos hc]
      simp (config := {decide := true}) only [st_set, eval_v, Function.update_self,
        Function.update_of_ne, ne_eq, h2]
      refine ⟨by simp, ?_⟩
      rw [min_eq_left (by omega), min_eq_left (by omega)]
    · rw [if_neg hc, if_neg (by simp), if_neg hc]
      simp (config := {decide := true}) only [st_skip, Function.update_self,
        Function.update_of_ne, ne_eq, h2, h1]
      refine ⟨by simp, ?_⟩
      rw [min_eq_left (by omega), min_eq_left (by omega)]
  · rw [if_neg ht, if_neg (by simp), if_neg (by omega)]
    simp (config := {decide := true}) only [st_skip, Function.update_of_ne, ne_eq,
      h1, h2]

lemma gstart_spec (hE : Env C w K) (ρ : Var → ℕ) (hNT : ρ vNT = (gts C).length) :
    st w K gstartP ρ vGS = gStart C (ρ vGi) ∧ st w K gstartP ρ vGcnt = C.length := by
  unfold gstartP
  simp only [st_seq, st_set, eval_c]
  set ρ1 := Function.update (Function.update ρ vGS (min 0 K)) vGcnt (min 0 K)
  have hb : (Ex.v vNT : Ex V).eval w K ρ1 = (gts C).length := by
    simp (config := {decide := true}) [ρ1, hNT]
  have key := st_loopI (w := w) (K := K) vGp (.v vNT) gsBody ρ1 (gsF C (ρ vGi)) (0, 0)
    (fun q ρ' a => ρ' vGS = a.1 ∧ ρ' vGcnt = a.2 ∧ a.2 ≤ q ∧ ρ' vGi = ρ vGi)
    ⟨by simp (config := {decide := true}) [ρ1], by simp [ρ1], le_rfl,
      by simp (config := {decide := true}) [ρ1]⟩ (by
      intro p hp ρ' a hfr ⟨h1, h2, h3, h4⟩
      rw [hb] at hp
      obtain ⟨k1, k2⟩ := gsBody_spec hE ρ' p hp a h1 h2 h3
      rw [h4] at k1 k2
      refine ⟨k1, k2, ?_, ?_⟩
      · unfold gsF; split_ifs <;> (try simp) <;> omega
      · rw [st_frame _ _ _ (by decide)]
        simp (config := {decide := true}) [h4])
  rw [hb] at key
  obtain ⟨k1, k2, -, -⟩ := key
  refine ⟨k1, ?_⟩
  rw [k2, gs_fold_aux (ρ vGi) _ le_rfl, List.take_length]
  have := tagCount_offs (C := C) le_rfl
  rwa [← gts_length, List.take_length] at this

/-! ## Reading numbers -/

/-- Predicate of the search for the end of a number. -/
def sepPred : Ex V :=
  andE (.bin .eq (.bin .lt (.v vRp) (.v vRq)) (.c 0)) (.bin .eq (tokE (.v vRp)) (.c 2))

/-- Body of the loop computing the value of a number. -/
def numBody : Pr V :=
  .set vRv (.bin .add (.bin .mul (.c 2) (.v vRv))
    (tokE (.bin .sub (.bin .sub (.v vRe) (.c 1)) (.v vRj))))

/-- Read the number starting at token `vRq`: its end in `vRe`, its value in `vRv`. -/
def readP : Pr V :=
  .seq (firstFP vRe vRp vNT .skip sepPred)
    (.seq (.set vRv (.c 0)) (.loop vRj (.bin .sub (.v vRe) (.v vRq)) numBody))

lemma readE_le (q : ℕ) : readE C q ≤ (gts C).length := by
  unfold readE
  rcases firstF_spec (sepF C q) (gts C).length with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega

lemma readE_ge {q : ℕ} (h : readE C q < (gts C).length) : q ≤ readE C q := by
  unfold readE at *
  rcases firstF_spec (sepF C q) (gts C).length with ⟨h1, -⟩ | ⟨h1, h2, -⟩
  · omega
  · simp only [sepF, Bool.and_eq_true, decide_eq_true_eq] at h2; exact h2.1

lemma readP_spec (hE : Env C w K) (ρ : Var → ℕ) (hNT : ρ vNT = (gts C).length) :
    st w K readP ρ vRe = readE C (ρ vRq) ∧ st w K readP ρ vRv = min (readV C (ρ vRq)) K ∧
      st w K readP ρ vRq = ρ vRq := by
  have hK := hE.lenK
  unfold readP
  simp only [st_seq, st_set]
  have h1 : st w K (firstFP vRe vRp vNT .skip sepPred) ρ vRe = readE C (ρ vRq) := by
    rw [firstFP_spec vRe vRp vNT .skip sepPred ρ (sepF C (ρ vRq)) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by omega), hNT]
    · rfl
    · intro p hp ρ' hfr
      rw [hNT] at hp
      have hq : ρ' vRq = ρ vRq := hfr vRq (by decide) (by decide) (by decide)
      simp only [st_skip, sepPred]
      rw [eval_andE _ _ _ (by omega)]
      simp only [eval_bin]
      rw [hE.tok (Function.update ρ' vRp p) (.v vRp) (by simpa using hp)]
      simp (config := {decide := true}) [sepF, hq, min_eq_left (show 2 ≤ K by omega)]
  have hq1 : st w K (firstFP vRe vRp vNT .skip sepPred) ρ vRq = ρ vRq :=
    st_frame _ _ _ (by decide)
  set ρ1 := st w K (firstFP vRe vRp vNT .skip sepPred) ρ
  set ρ2 := Function.update ρ1 vRv ((Ex.c 0 : Ex V).eval w K ρ1)
  have hb : (Ex.bin .sub (.v vRe) (.v vRq) : Ex V).eval w K ρ2 = readE C (ρ vRq) - ρ vRq := by
    simp (config := {decide := true}) [ρ2, h1, hq1]
  have key := st_loop (w := w) (K := K) vRj (.bin .sub (.v vRe) (.v vRq)) numBody ρ2
    (numF C (readE C (ρ vRq))) 0 (fun ρ' v => ρ' vRv = min v K) (by simp [ρ2]) (by
      intro j hj ρ' v hfr hv
      rw [hb] at hj
      have he : ρ' vRe = readE C (ρ vRq) := by
        rw [hfr vRe (by decide)]; simp (config := {decide := true}) [ρ2, h1]
      have hle := readE_le (C := C) (ρ vRq)
      have hidx : (Ex.bin .sub (.bin .sub (.v vRe) (.c 1)) (.v vRj) : Ex V).eval w K
          (Function.update ρ' vRj j) = readE C (ρ vRq) - 1 - j := by
        simp (config := {decide := true}) [he, min_eq_left (show 1 ≤ K by omega)]
      unfold numBody
      simp only [st_set, Function.update_self]
      simp only [eval_bin, ap_add, ap_mul, eval_c, eval_v]
      rw [show (tokE (.bin .sub (.bin .sub (.v vRe) (.c 1)) (.v vRj)) : Ex V) =
        tokE (.bin .sub (.bin .sub (.v vRe) (.c 1)) (.v vRj)) from rfl,
        hE.tok _ _ (by rw [hidx]; omega), hidx]
      simp (config := {decide := true}) only [Function.update_of_ne, ne_eq, hv, numF]
      rw [min_eq_left (show 2 ≤ K by omega)]
      have := CTLP.Tok.code_lt
      omega)
  rw [hb] at key
  refine ⟨?_, ?_, ?_⟩
  · rw [st_frame _ _ _ (by decide)]; simp (config := {decide := true}) [ρ2, h1]
  · rw [key]; rfl
  · rw [st_frame _ _ _ (by decide)]; simp (config := {decide := true}) [ρ2, hq1]

/-! ## Reading a gate -/

/-- `[a ≠ 0 ∨ b ≠ 0]` -/
def orE (a b : Ex V) : Ex V := .bin .lt (.c 0) (.bin .add a b)

/-- Read the arguments of a non-constant gate starting at `vGS`. -/
def argsP : Pr V :=
  .seq (.set vRq (.bin .add (.v vGS) (.c 2))) (.seq readP (.seq (.set vGL (.v vRv))
    (.seq (.set vE1 (.v vRe)) (.ite (.bin .eq (tokE (.bin .add (.v vE1) (.c 1))) (.c 4))
      (.set vGH (.v vGL))
      (.seq (.set vRq (.bin .add (.v vE1) (.c 1))) (.seq readP (.set vGH (.v vRv))))))))

/-- Read gate `vGi < vNG`. -/
def gateIn : Pr V :=
  .seq gstartP (.seq (.set vTg (tokE (.v vGS))) (.seq (.set vGA (.bin .eq (.v vTg) (.c 9)))
    (.seq (.set vGT (.bin .eq (.v vTg) (.c 7)))
      (.seq (.set vGC (orE (.bin .eq (.v vTg) (.c 6)) (.bin .eq (.v vTg) (.c 7))))
        (.ite (.v vGC) (.seq (.set vGL (.c 0)) (.set vGH (.c 0))) argsP)))))

/-- The extra gates `vGi ≥ vNG`. -/
def gateOut : Pr V :=
  .seq (.set vGA (.c 1)) (.seq (.set vGL (.bin .sub (.v vNG) (.c 1)))
    (.seq (.set vGH (.bin .sub (.v vNG) (.c 1))) (.seq (.set vGC (.c 1)) (.set vGT (.c 0)))))

/-- Read gate `vGi`. -/
def gateP : Pr V := .ite (.bin .lt (.v vGi) (.v vNG)) gateIn gateOut

/-- The values computed by `gateP`. -/
structure GateOut (C : Circuit) (i : ℕ) (ρ : Var → ℕ) : Prop where
  a : ρ vGA = ((toLC C).isAnd i).toNat
  l : ρ vGL = (toLC C).lo i
  h : ρ vGH = (toLC C).hi i
  c : ρ vGC = (Conc.isC C i).toNat
  t : ρ vGT = (Conc.inp C i).toNat

lemma argsP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ)
    (hNT : ρ vNT = (gts C).length) {i : ℕ} (hi : i < C.length) (hgs : ρ vGS = gStart C i)
    (hc : pIsC C i = false) :
    st w K argsP ρ vGL = Conc.lo C i ∧ st w K argsP ρ vGH = Conc.hi C i := by
  obtain ⟨hW, hM, -⟩ := hC
  have hK := hE.lenK
  have hg := hE.gts_le
  have hnK : C.length ≤ K := by have := hE.n_le; have := hE.gts_le; omega
  obtain ⟨hlo, hhi⟩ := parse_ok hW hM hi
  have hlon := lo_lt_n hW hi
  have hhin := hi_lt_n hW hi
  have he1 := e1_lt hM hi hc
  have hgsl : gStart C i + 2 < (gts C).length := by
    have := readE_ge (C := C) (q := gStart C i + 2) (by omega); omega
  unfold argsP
  simp only [st_seq, st_set]
  set ρa := Function.update ρ vRq ((Ex.bin .add (.v vGS) (.c 2) : Ex V).eval w K ρ)
  have hqa : ρa vRq = gStart C i + 2 := by
    simp [ρa, hgs, min_eq_left (show 2 ≤ K by omega), min_eq_left (show gStart C i + 2 ≤ K by omega)]
  obtain ⟨r1, r2, -⟩ := readP_spec hE ρa (by simp (config := {decide := true}) [ρa, hNT])
  rw [hqa] at r1 r2
  have hrv : readV C (gStart C i + 2) = Conc.lo C i := by
    rw [← hlo]; simp [pLo, hc]
  rw [hrv, min_eq_left (by omega)] at r2
  set ρb := st w K readP ρa
  set ρc := Function.update ρb vGL ((Ex.v vRv : Ex V).eval w K ρb)
  set ρd := Function.update ρc vE1 ((Ex.v vRe : Ex V).eval w K ρc)
  have hd1 : ρd vE1 = readE C (gStart C i + 2) := by
    simp (config := {decide := true}) [ρd, ρc, r1]
  have hdl : ρd vGL = Conc.lo C i := by simp (config := {decide := true}) [ρd, ρc, r2]
  have htk : (tokE (.bin .add (.v vE1) (.c 1)) : Ex V).eval w K ρd =
      tc C (readE C (gStart C i + 2) + 1) := by
    have e : (Ex.bin .add (.v vE1) (.c 1) : Ex V).eval w K ρd = readE C (gStart C i + 2) + 1 := by
      simp [hd1, min_eq_left (show 1 ≤ K by omega)]; omega
    rw [hE.tok _ _ (by rw [e]; exact he1), e]
  rw [st_ite]
  simp only [eval_bin, ap_eq, htk, eval_c, min_eq_left (show 4 ≤ K by omega)]
  by_cases h4 : tc C (readE C (gStart C i + 2) + 1) = 4
  · rw [if_pos (by simp [h4])]
    simp only [st_set, Function.update_self, eval_v]
    refine ⟨by simp (config := {decide := true}) [hdl], ?_⟩
    rw [hdl, ← hhi, ← hlo]
    simp [pLo, pHi, hc, h4]
  · rw [if_neg (by simp [h4])]
    simp only [st_seq, st_set]
    set ρe := Function.update ρd vRq ((Ex.bin .add (.v vE1) (.c 1) : Ex V).eval w K ρd)
    have hqe : ρe vRq = readE C (gStart C i + 2) + 1 := by
      simp [ρe, hd1, min_eq_left (show 1 ≤ K by omega)]; omega
    obtain ⟨s1, s2, -⟩ := readP_spec hE ρe (by
      simp (config := {decide := true}) [ρe, ρd, ρc]
      change st w K readP ρa vNT = _
      rw [st_frame _ _ _ (by decide)]; simp (config := {decide := true}) [ρa, hNT])
    rw [hqe] at s2
    have hrv2 : readV C (readE C (gStart C i + 2) + 1) = Conc.hi C i := by
      rw [← hhi]; simp [pHi, hc, h4]
    rw [hrv2, min_eq_left (by omega)] at s2
    refine ⟨?_, by simp [s2]⟩
    simp (config := {decide := true}) only [Function.update_of_ne, ne_eq]
    rw [st_frame _ _ _ (by decide)]
    simp (config := {decide := true}) [ρe, hdl]

lemma gateP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ)
    (hNT : ρ vNT = (gts C).length) (hNG : ρ vNG = C.length) :
    GateOut C (ρ vGi) (st w K gateP ρ) := by
  have hK := hE.lenK
  have hg := hE.gts_le
  have hnK : C.length ≤ K := by have := hE.n_le; have := hE.gts_le; omega
  unfold gateP
  rw [st_ite]
  simp only [eval_bin, ap_lt, eval_v, hNG]
  by_cases hi : ρ vGi < C.length
  · rw [if_pos (by simp [hi])]
    set i := ρ vGi
    unfold gateIn
    simp only [st_seq, st_set]
    obtain ⟨g1, -⟩ := gstart_spec hE ρ hNT
    set ρ1 := st w K gstartP ρ
    have h1NT : ρ1 vNT = (gts C).length := by
      change st w K gstartP ρ vNT = _
      rw [st_frame _ _ _ (by decide)]; exact hNT
    have hgs : gStart C i < (gts C).length := by
      rw [gStart_eq hi]
      have := offs_mono (C := C) (show i + 1 ≤ C.length by omega)
      rw [offs_succ hi, ← gts_length] at this; have := toks_pos C[i]; omega
    have htg : (tokE (.v vGS) : Ex V).eval w K ρ1 = pTag C i := by
      rw [hE.tok _ _ (by simpa [g1] using hgs)]; simp only [eval_v, g1, pTag]; rfl
    simp only [htg]
    set ρ2 := Function.update ρ1 vTg (pTag C i)
    have hA : ∀ ρ' : Var → ℕ, ρ' vGA = (if pTag C i = 9 then 1 else 0) →
        ρ' vGA = ((toLC C).isAnd i).toNat := by
      intro ρ' h; rw [h]; simp only [toLC, hi, dif_pos, kindAnd_iff hi]; split_ifs <;> simp_all
    have hT : ∀ ρ' : Var → ℕ, ρ' vGT = (if pTag C i = 7 then 1 else 0) →
        ρ' vGT = (Conc.inp C i).toNat := by
      intro ρ' h; rw [h]
      simp only [Conc.inp, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some,
        kindTrue_iff hi]
      split_ifs <;> simp_all
    have hCc : (Conc.isC C i).toNat = (pIsC C i).toNat := by
      simp [Conc.isC, List.getElem?_eq_getElem hi, kindConst_iff hi]
    set ρ3 := Function.update ρ2 vGA ((Ex.bin .eq (.v vTg) (.c 9) : Ex V).eval w K ρ2)
    set ρ4 := Function.update ρ3 vGT ((Ex.bin .eq (.v vTg) (.c 7) : Ex V).eval w K ρ3)
    set ρ5 := Function.update ρ4 vGC ((orE (.bin .eq (.v vTg) (.c 6)) (.bin .eq (.v vTg) (.c 7)) :
      Ex V).eval w K ρ4)
    have h5A : ρ5 vGA = (if pTag C i = 9 then 1 else 0) := by
      simp (config := {decide := true}) [ρ5, ρ4, ρ3, ρ2, min_eq_left (show 9 ≤ K by omega)]
    have h5T : ρ5 vGT = (if pTag C i = 7 then 1 else 0) := by
      simp (config := {decide := true}) [ρ5, ρ4, ρ3, ρ2, min_eq_left (show 7 ≤ K by omega)]
    have h5C : ρ5 vGC = (pIsC C i).toNat := by
      simp (config := {decide := true}) [ρ5, ρ4, ρ3, ρ2, orE, pIsC,
        min_eq_left (show 7 ≤ K by omega), min_eq_left (show 6 ≤ K by omega)]
      by_cases h6 : pTag C i = 6
      · simp [h6, show K ≠ 0 by omega]
      · by_cases h7 : pTag C i = 7
        · simp [h7, show K ≠ 0 by omega]
        · simp [h6, h7]
    rw [st_ite]
    simp only [eval_v, h5C]
    by_cases hc : pIsC C i = true
    · rw [if_pos (by simp [hc])]
      obtain ⟨hlo, hhi⟩ := parse_ok hC.1 hC.2.1 hi
      simp only [st_seq, st_set, eval_c, min_eq_left (Nat.zero_le K)]
      refine ⟨hA _ (by simp (config := {decide := true}) [h5A]), ?_, ?_, ?_,
        hT _ (by simp (config := {decide := true}) [h5T])⟩
      · simp (config := {decide := true}) only [Function.update_of_ne, Function.update_self, ne_eq]
        show 0 = Conc.lo C i
        rw [← hlo]; simp [pLo, hc]
      · simp only [Function.update_self]
        show 0 = Conc.hi C i
        rw [← hhi]; simp [pHi, hc]
      · simp (config := {decide := true}) [hCc, h5C]
    · rw [if_neg (by simp at hc; simp [hc])]
      have hc' : pIsC C i = false := by simpa using hc
      obtain ⟨a1, a2⟩ := argsP_spec hE hC ρ5 (by simp (config := {decide := true}) [ρ5, ρ4, ρ3, ρ2, h1NT])
        hi (by simp (config := {decide := true}) [ρ5, ρ4, ρ3, ρ2, g1]; rfl) hc'
      refine ⟨hA _ (by rw [st_frame _ _ _ (by decide)]; exact h5A), a1, a2, ?_,
        hT _ (by rw [st_frame _ _ _ (by decide)]; exact h5T)⟩
      rw [st_frame _ _ _ (by decide), h5C, hCc]
  · rw [if_neg (by simp [hi])]
    unfold gateOut
    simp only [st_seq, st_set]
    have hn := List.length_pos_of_ne_nil hC.1.1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp (config := {decide := true}) [toLC, hi, min_eq_left (show 1 ≤ K by omega)]
    · simp (config := {decide := true}) [toLC, Conc.lo, hi, hNG, min_eq_left (show 1 ≤ K by omega)]
    · simp (config := {decide := true}) [toLC, Conc.hi, hi, hNG, min_eq_left (show 1 ≤ K by omega)]
    · simp (config := {decide := true}) [Conc.isC, List.getElem?_eq_none (show C.length ≤ ρ vGi by omega),
        min_eq_left (show 1 ≤ K by omega)]
    · simp (config := {decide := true}) [Conc.inp, List.getElem?_eq_none (show C.length ≤ ρ vGi by omega)]

end LP

end BLMS

end PathChecking
