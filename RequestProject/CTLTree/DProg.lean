module

public import RequestProject.CTLTree.FQ3
public import RequestProject.CTLTree.Embed
public import RequestProject.CTLTree.DRecog
public import RequestProject.Logspace.Concat
public import RequestProject.Logspace.Compose

/-!
# The decision function of the CTL round algorithm

The decision function combines three logspace functions:

* `aFun`: the input decodes into tokens `ts` and the answer for the root and the main formula
  (pair `(rootC ts, 1)`) is true;
* `hFun`: the packed input `pack (encodeToks (hL ts)) 0 []` of the CTL* recognizer, where `hL`
  maps CTL instances to CTL* instances;
* `SQ.recProg`: the recognizer of CTL* instances.

`dFunC x = gFun (aFun x ++ recProg (hFun x))` takes the conjunction of the two bits; it is
logspace computable and meets `DSpecC`.
-/

@[expose] public section

namespace PathChecking

namespace CTLF

open FE LL CTLP LTok FD CTLT ShallowP

variable {x : Word} {Γ : Ctx} {ts : List Tok} {q : ℕ} {a : List Bool}

/-! ## The answer bit -/

/-- The answer bit. -/
def aProg : TO :=
  bitO (iteT wdecT (ansCT (addT nT (cT 1)) (addT (fendCT (cT 1)) (cT 1)) (cT 1)) (cT 0))

/-- The value of the answer bit. -/
def AVal (w : Word) (a : List Bool) : Prop :=
  ∃ ts : List Tok, w = encodeToks ts ∧ ansC (ts.length + 1) a (rootC ts) 1 = true

lemma deno_aProg {w : Word} (hx : x = pack w 0 a) :
    DenO x [] aProg [decide (bv (AVal w a) ≠ 0)] := by
  refine deno_bit (den_ite_eq (den_wdec hx) (fun h => ?_) (fun h => ?_))
  · simp only [ne_eq, bv_eq_zero, not_not] at h
    obtain ⟨ts, rfl⟩ := decode_of_DecW h
    refine (den_ansC hx (Nat.zero_le _) (den_add (den_n hx) (den_c 1))
      (den_add (den_fendC hx (den_c 1)) (den_c 1)) (den_c 1)).of_eq ?_
    refine (bv_bool _).trans (bv_congr ⟨fun h => ⟨ts, rfl, h⟩, ?_⟩)
    rintro ⟨us, hus, h⟩
    rw [MCVPReduction.encodeToks_injective hus]; exact h
  · simp only [bv_eq_zero] at h
    refine (den_c 0).of_eq (bv_neg ?_).symm
    rintro ⟨ts, rfl, -⟩
    exact h (DecW_encode ts)

/-! ## The input of the recognizer -/

lemma flatMap_range {α β : Type*} (f : α → List β) : ∀ l : List α,
    l.flatMap f = (List.range l.length).flatMap fun i => (l[i]?.map f).getD []
  | [] => rfl
  | t :: l => by
    rw [List.flatMap_cons, flatMap_range f l, List.length_cons, List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map]
    simp

lemma replicate_flatMap {α : Type*} (b : Bool) (h : α → Word) : ∀ l : List α,
    List.replicate (l.flatMap h).length b = l.flatMap fun i => List.replicate (h i).length b
  | [] => rfl
  | t :: l => by
    rw [List.flatMap_cons, List.length_append, List.replicate_add, replicate_flatMap b h l,
      List.flatMap_cons]

/-- The encoding of the image of the token at `i`. -/
def hTW (ts : List Tok) (i : ℕ) : Word := encodeToks ((ts[i]?.map hT).getD [])

lemma encodeToks_hL (ts : List Tok) :
    encodeToks (hL ts) = (List.range ts.length).flatMap (hTW ts) := by
  rw [hL, flatMap_range hT ts, encodeToks_flatMap]; rfl

lemma code_eq_11 {t : Tok} : t.code = 11 ↔ t = Tok.tag 6 := by
  constructor
  · intro h
    cases t with
    | tag k =>
      simp only [Tok.code] at h
      have : k = 6 := Fin.ext (by simp; omega)
      rw [this]
    | _ => simp [Tok.code] at h
  · rintro rfl; rfl

lemma hTW_eq {i : ℕ} (hi : i < ts.length) :
    hTW ts i = if tc ts i = 11 then cbits 11 ++ cbits 8 else cbits (tc ts i) := by
  have hs : ts[i]? = some ts[i] := List.getElem?_eq_getElem hi
  have htc : tc ts i = ts[i].code := by simp [tc, hs]
  rw [hTW, hs, htc]
  simp only [Option.map_some, Option.getD_some, hT]
  by_cases h6 : ts[i] = Tok.tag 6
  · rw [if_pos h6, if_pos (code_eq_11.2 h6)]; rfl
  · rw [if_neg h6, if_neg (fun h => h6 (code_eq_11.1 h)), encodeToks_single]

/-- The program producing the input of the recognizer. -/
def hProg : TO :=
  seqO (loopO nT fun i => iteO (isT 11 (tcT i)) (repO (cT 10) (bitO (cT 1)))
      (repO (cT 5) (bitO (cT 1))))
    (seqO (bitO (cT 0)) (loopO nT fun i => iteO (isT 11 (tcT i))
      (seqO (tokO (cT 11)) (tokO (cT 8))) (tokO (tcT i))))

lemma pack_nil (w : Word) : pack w 0 [] = List.replicate w.length true ++ [false] ++ w := by
  simp [pack]

lemma deno_hProg (hx : x = pack (encodeToks ts) q a) :
    DenO x [] hProg (pack (encodeToks (hL ts)) 0 []) := by
  rw [pack_nil, encodeToks_hL, replicate_flatMap, List.append_assoc]
  refine deno_seq (deno_loop (den_n hx) fun k i hi => ?_) (deno_seq ((deno_bit (den_c 0)).of_eq
    (by simp)) (deno_loop (den_n hx) fun k i hi => ?_))
  · rw [hTW_eq hi, show List.replicate (if tc ts i = 11 then cbits 11 ++ cbits 8
        else cbits (tc ts i)).length true = if tc ts i = 11 then
        List.replicate (cbits 11 ++ cbits 8).length true
        else List.replicate (cbits (tc ts i)).length true by split <;> rfl]
    refine deno_ite_is (den_tc hx den_var0) (fun h => ?_) (fun h => ?_)
    · refine (deno_rep (den_c 10) fun _ _ => deno_bit (den_c 1)).of_eq ?_
      simp [cbits]
      decide
    · refine (deno_rep (den_c 5) fun _ _ => deno_bit (den_c 1)).of_eq ?_
      simp [cbits]
      decide
  · rw [hTW_eq hi]
    refine deno_ite_is (den_tc hx den_var0) (fun h => ?_) (fun h => ?_)
    · exact deno_seq (deno_tok (den_c 11)) (deno_tok (den_c 8))
    · exact deno_tok (den_tc hx den_var0)

/-! ## The conjunction -/

/-- Conjunction of the first two bits. -/
def gProg : TO := bitO (andT (eqT (inpT (cT 1)) (cT 1)) (eqT (inpT (cT 2)) (cT 1)))

lemma deno_gProg_false (y : Word) : DenO (false :: y) [] gProg [false] := by
  have h1 : Den (false :: y) [] (eqT (inpT (cT 1)) (cT 1)) (bv False) :=
    (den_eq' (den_inp (den_c 1)) (den_c 1)).of_eq (bv_congr (by
      rw [show (1 : ℕ) = 0 + 1 from rfl, SQ.symNum_some (false :: y) 0 false rfl]; simp))
  exact (deno_bit (den_and h1 (den_eq' (den_inp (den_c 2)) (den_c 1)))).of_eq (by simp)

lemma deno_gProg_true (b : Bool) : DenO [true, b] [] gProg [b] := by
  have h1 : Den [true, b] [] (eqT (inpT (cT 1)) (cT 1)) (bv True) :=
    (den_eq' (den_inp (den_c 1)) (den_c 1)).of_eq (bv_congr (by
      rw [show (1 : ℕ) = 0 + 1 from rfl, SQ.symNum_some [true, b] 0 true rfl]; simp))
  have h2 : Den [true, b] [] (eqT (inpT (cT 2)) (cT 1)) (bv (b = true)) :=
    (den_eq' (den_inp (den_c 2)) (den_c 1)).of_eq (bv_congr (by
      rw [show (2 : ℕ) = 1 + 1 from rfl, SQ.symNum_some [true, b] 1 b rfl]; cases b <;> simp))
  exact (deno_bit (den_and h1 h2)).of_eq (by cases b <;> simp)

end CTLF

open FE FD CTLF

/-- The answer function. -/
def aFun (x : Word) : Word := FE.evO x 0 (fun _ => 0) (aProg 0)
/-- The input of the recognizer. -/
def hFun (x : Word) : Word := FE.evO x 0 (fun _ => 0) (hProg 0)
/-- The conjunction. -/
def gFun (x : Word) : Word := FE.evO x 0 (fun _ => 0) (gProg 0)

/-- The decision function. -/
def dFunC (x : Word) : Word := gFun (aFun x ++ SQ.recProg.output 4 (hFun x))

/-- The decision function is logspace computable. -/
theorem dFunC_logspace : LogspaceComputable dFunC := by
  have ha : LogspaceComputable aFun :=
    FE.logspaceComputable_of_O (aProg 0) (by decide +kernel) aFun fun _ => rfl
  have hh : LogspaceComputable hFun :=
    FE.logspaceComputable_of_O (hProg 0) (by decide +kernel) hFun fun _ => rfl
  have hg : LogspaceComputable gFun :=
    FE.logspaceComputable_of_O (gProg 0) (by decide +kernel) gFun fun _ => rfl
  exact LogspaceComputable.comp (LogspaceComputable.append ha
    (LogspaceComputable.comp hh SQ.recProg_logspace)) hg

/-- **The decision function meets its specification.** -/
theorem dFunC_spec : CTLT.DSpecC dFunC := by
  intro w a _
  have hA : aFun (pack w 0 a) = [decide (bv (AVal w a) ≠ 0)] :=
    deno_aProg rfl 0 _ (fun _ h => absurd h (by simp))
  rw [dFunC, hA]
  by_cases hv : AVal w a
  · obtain ⟨ts, rfl, hans⟩ := hv
    have hH : hFun (pack (encodeToks ts) 0 a) = pack (encodeToks (CTLT.hL ts)) 0 [] :=
      deno_hProg rfl 0 _ (fun _ h => absurd h (by simp))
    obtain ⟨b, hb, hbi⟩ := SQ.recProg_spec (encodeToks (CTLT.hL ts))
    rw [hH, hb, show decide (bv (AVal (encodeToks ts) a) ≠ 0) = true by
      simp only [ne_eq, bv_eq_zero, not_not, decide_eq_true_eq]; exact ⟨ts, rfl, hans⟩]
    have hg : gFun [true, b] = [b] := deno_gProg_true b 0 _ (fun _ h => absurd h (by simp))
    rw [show [true] ++ [b] = [true, b] from rfl, hg]
    simp only [List.cons.injEq, and_true]
    rw [hbi]
    constructor
    · rintro ⟨us, hus, -, hr⟩
      rw [← MCVPReduction.encodeToks_injective hus] at hr
      obtain ⟨φ, t, rfl⟩ := (CTLT.recog_hL_iff ts).1 hr
      exact ⟨φ, t, rfl, hans⟩
    · rintro ⟨φ, t, hw, -⟩
      have hts := MCVPReduction.encodeToks_injective hw
      refine ⟨CTLT.hL ts, rfl, ?_, (CTLT.recog_hL_iff ts).2 ⟨φ, t, hts⟩⟩
      rw [hts, CTLT.instC, CTLT.hL_cons, CTLT.hT_ne Tok.lpar (by decide)]; simp
  · rw [show decide (bv (AVal w a) ≠ 0) = false by simpa using hv]
    have hg : gFun (false :: SQ.recProg.output 4 (hFun (pack w 0 a))) = [false] :=
      deno_gProg_false (SQ.recProg.output 4 (hFun (pack w 0 a))) 0 (fun _ => 0)
        (fun _ h => absurd h (by simp))
    rw [show [false] ++ SQ.recProg.output 4 (hFun (pack w 0 a)) =
      false :: SQ.recProg.output 4 (hFun (pack w 0 a)) from rfl]
    rw [hg]
    simp only [List.cons.injEq, Bool.false_eq_true, and_true, false_iff, not_exists, not_and]
    intro φ t hw hans
    exact hv ⟨_, hw, hans⟩

end PathChecking
