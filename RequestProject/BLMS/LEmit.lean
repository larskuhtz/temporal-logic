module

public import RequestProject.BLMS.LAct
public import RequestProject.BLMS.Word

/-!
# Emitting the table of the code machine in the loop language

`entryP` emits the entry of the table for the codes `vAI`, `vAJ`, `roundP` a whole round.
-/

@[expose] public section

namespace PathChecking

namespace BLMS

namespace LP

open LL PD

variable {C : Circuit} {w : Word} {K : ℕ}

/-- code to emit -/
abbrev vEc : Var := 80
/-- loop variable of `emitCode` -/
abbrev vEk : Var := 81
/-- loop variable over rounds -/
abbrev vT : Var := 82
/-- loop variable over rows -/
abbrev vRJ : Var := 83
/-- loop variable over entries -/
abbrev vRI : Var := 84
/-- number of codes `M` -/
abbrev vM : Var := 85
/-- number of rounds `T` -/
abbrev vTT : Var := 86

lemma run_seq_of {s t : Pr V} {ρ ρ1 : Var → ℕ} {o1 : List Bool} (h : s.run w K ρ = (ρ1, o1)) :
    (Pr.seq s t).run w K ρ = ((t.run w K ρ1).1, o1 ++ (t.run w K ρ1).2) := by
  rw [run_seq, h]

lemma run_eq_st' {P : Pr V} (h : P.silent = true) (ρ : Var → ℕ) :
    P.run w K ρ = (st w K P ρ, []) := run_eq_st h ρ

/-- Output rule for loops with a frame invariant. -/
lemma run_loop_out (x : Var) (e : Ex V) (s : Pr V) (ρ : Var → ℕ) (O : ℕ → List Bool)
    (hs : ∀ i < e.eval w K ρ, ∀ ρ', (∀ z, z ∉ (Pr.loop x e s).wr → ρ' z = ρ z) →
      (s.run w K (Function.update ρ' x i)).2 = O i) :
    ((Pr.loop x e s).run w K ρ).2 = (List.range (e.eval w K ρ)).flatMap O := by
  refine (run_loop_spec x e s ρ (fun _ ρ' => ∀ z, z ∉ (Pr.loop x e s).wr → ρ' z = ρ z) O
    (fun _ _ => rfl) (fun i hi ρ' h => ⟨fun z hz => ?_, hs i hi ρ' h⟩)).2
  simp only [Pr.wr, List.mem_cons, not_or] at hz
  rw [Pr.run_frame _ _ _ hz.2, Function.update_of_ne hz.1, h z (by simp [Pr.wr, hz.1, hz.2])]

lemma flatMap_const_range (k : ℕ) (b : List Bool) (s : Sym) (hb : b = s.bits) :
    (List.range k).flatMap (fun _ => b) = wordOf (List.replicate k s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ', wordOf_append]
    simp [wordOf, hb]

lemma wordOf_flatMap {α : Type} (l : List α) (f : α → List Sym) :
    wordOf (l.flatMap f) = l.flatMap (fun a => wordOf (f a)) := by
  simp [wordOf, List.flatMap_assoc]

/-! ## Emitting codes -/

/-- Emit `S X^{ρ x}`. -/
def emitCode (x : Var) : Pr V := .seq (outW Sym.S.bits) (.loop vEk (.v x) (outW Sym.X.bits))

lemma run_emitCode (x : Var) (ρ : Var → ℕ) :
    (emitCode x).run w K ρ = (st w K (emitCode x) ρ, wordOf (.S :: List.replicate (ρ x) .X)) := by
  refine Prod.ext rfl ?_
  unfold emitCode
  rw [run_seq, run_outW, run_loop_out _ _ _ _ (fun _ => Sym.X.bits) (fun i _ ρ' _ => by
    rw [run_outW])]
  rw [flatMap_const_range _ _ .X rfl, wordOf_cons]
  rfl

lemma emitCode_frame (x : Var) (ρ : Var → ℕ) (z : Var) (hz : z ≠ vEk) :
    st w K (emitCode x) ρ z = ρ z :=
  st_frame _ _ _ (by simp [emitCode, Pr.wr, hz])

/-- `x := code (a, b)`. -/
def setCode (x a b : Var) : Pr V :=
  .set x (.bin .add (.bin .mul (.v a) (.bin .add (.v vN) (.c 1))) (.v b))

lemma Env.MK (hE : Env C w K) : ((toLC C).N + 1) * ((toLC C).N + 1) ≤ K := by
  have h1 := N_le (C := C)
  have h2 := length_le_gts (C := C)
  have h3 := hE.gts_le
  have h4 := hE.K_ge
  have : (toLC C).N + 1 ≤ w.length + 2 := by omega
  nlinarith

lemma setCode_spec (hE : Env C w K) (ρ : Var → ℕ) (hG : Glob C ρ) (x a b : Var)
    (ha : ρ a ≤ (toLC C).N) (hb : ρ b ≤ (toLC C).N) :
    st w K (setCode x a b) ρ x = (toLC C).code (ρ a, ρ b) := by
  have hM := hE.MK
  have hK := hE.nK
  have h1 : ρ a * ((toLC C).N + 1) ≤ (toLC C).N * ((toLC C).N + 1) := Nat.mul_le_mul_right _ ha
  simp only [setCode, st_set, Function.update_self, eval_bin, ap_add, ap_mul, eval_v, eval_c,
    hG.n, LC.code]
  rw [min_eq_left (show 1 ≤ K by omega), min_eq_left (show (toLC C).N + 1 ≤ K by nlinarith),
    min_eq_left (show ρ a * ((toLC C).N + 1) ≤ K by nlinarith),
    min_eq_left (show ρ a * ((toLC C).N + 1) + ρ b ≤ K by nlinarith)]

/-! ## Entries -/

/-- `[ρ a = k]` -/
def eqc (a : Var) (k : ℕ) : Ex V := .bin .eq (.v a) (.c k)

lemma eqc_eval {ρ : Var → ℕ} {a : Var} {k : ℕ} (hk : k ≤ K) :
    (eqc a k).eval w K ρ ≠ 0 ↔ ρ a = k := by
  simp [eqc, min_eq_left hk]

/-- The push entry. -/
def pushP : Pr V :=
  .seq (emitCode vAI) (.seq (emitCode vAJ) (.seq (.set vNd (.v vJb)) (.seq nextRunP
    (.seq (setCode vEc vNa vNb) (emitCode vEc)))))

/-- Emit the entry of the table for the codes `vAI`, `vAJ` (after `actionP`). -/
def entryP : Pr V :=
  .ite (eqc vAc 0) (outW Sym.A.bits)
   (.ite (eqc vAc 1) (outW Sym.R.bits)
    (.ite (eqc vAc 2) (.seq (setCode vEc vIa vJb) (emitCode vEc))
     (.ite (eqc vAc 3) pushP (emitCode vAJ))))

lemma entryP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ)
    (hI : ρ vAI < (toLC C).M) (hJ : ρ vAJ < (toLC C).M)
    (hAc : ρ vAc = actCode ((toLC C).action ((toLC C).dec (ρ vAI)) ((toLC C).dec (ρ vAJ))))
    (hIa : ρ vIa = ((toLC C).dec (ρ vAI)).1) (hJb : ρ vJb = ((toLC C).dec (ρ vAJ)).2) :
    (entryP.run w K ρ).2 = wordOf (entry ((toLC C).tab (Conc.inp C) (ρ vAI) (ρ vAJ))) := by
  have hK : 4 ≤ K := by have := hE.lenK; omega
  have dI := LC.dec_le hI
  have dJ := LC.dec_le hJ
  unfold entryP LC.tab
  generalize (toLC C).action ((toLC C).dec (ρ vAI)) ((toLC C).dec (ρ vAJ)) = act at hAc ⊢
  rcases act with _ | _ | _ | _ | _ <;> simp only [actCode] at hAc
  · rw [run_ite_pos (by simpa [eqc_eval (show 0 ≤ K by omega)] using hAc)]
    simp [entry, wordOf]
  · rw [run_ite_neg (by simp [eqc, hAc]),
      run_ite_pos (by simpa [eqc_eval (show 1 ≤ K by omega)] using hAc)]
    simp [entry, wordOf]
  · rw [run_ite_neg (by simp [eqc, hAc]),
      run_ite_neg (by simp [eqc, hAc, min_eq_left (show 1 ≤ K by omega)]),
      run_ite_pos (by simpa [eqc_eval (show 2 ≤ K by omega)] using hAc)]
    rw [run_seq_of (run_eq_st' (by rfl) ρ), run_emitCode, List.nil_append,
      setCode_spec hE ρ hG vEc vIa vJb (by rw [hIa]; exact dI.1) (by rw [hJb]; exact dJ.2), hIa,
      hJb]
    simp [entry, wordOf]
  · rw [run_ite_neg (by simp [eqc, hAc]),
      run_ite_neg (by simp [eqc, hAc, min_eq_left (show 1 ≤ K by omega)]),
      run_ite_neg (by simp [eqc, hAc, min_eq_left (show 2 ≤ K by omega)]),
      run_ite_pos (by simpa [eqc_eval (show 3 ≤ K by omega)] using hAc)]
    unfold pushP
    rw [run_seq_of (run_emitCode vAI ρ)]
    set ρ1 := st w K (emitCode vAI) ρ
    have f1 : ∀ z, z ≠ vEk → ρ1 z = ρ z := fun z hz => emitCode_frame _ _ _ hz
    rw [run_seq_of (run_emitCode vAJ ρ1)]
    set ρ2 := st w K (emitCode vAJ) ρ1
    have f2 : ∀ z, z ≠ vEk → ρ2 z = ρ z := fun z hz => by
      change st w K (emitCode vAJ) ρ1 z = ρ z
      rw [emitCode_frame _ _ _ hz, f1 z hz]
    rw [run_seq_of (run_eq_st' (by rfl) ρ2), run_seq_of (run_eq_st' (by rfl) _),
      run_seq_of (run_eq_st' (by rfl) _), run_emitCode]
    simp only [st_set, eval_v]
    have e : ρ2 vJb = ((toLC C).dec (ρ vAJ)).2 := by rw [f2 _ (by decide), hJb]
    rw [e]
    have G3 := (hG.fr ρ2 (fun z hz => f2 z (by revert z; decide))).upd vNd (by decide)
      ((toLC C).dec (ρ vAJ)).2
    obtain ⟨n1, n2⟩ := nextRunP_spec hE hC _ G3
    have G4 := G3.st (w := w) (K := K) nextRunP (globs_disj _ (by decide))
    simp only [Function.update_self] at n1 n2
    have hb := LC.nextRun_le (c := toLC C) (inp := Conc.inp C) ((toLC C).dec (ρ vAJ)).2
    rw [setCode_spec hE _ G4 vEc vNa vNb (by rw [n1]; exact hb.1) (by rw [n2]; exact hb.2), n1, n2]
    simp only [f1 vAJ (by decide), List.nil_append]
    simp [entry, wordOf]
  · rw [run_ite_neg (by simp [eqc, hAc]),
      run_ite_neg (by simp [eqc, hAc, min_eq_left (show 1 ≤ K by omega)]),
      run_ite_neg (by simp [eqc, hAc, min_eq_left (show 2 ≤ K by omega)]),
      run_ite_neg (by simp [eqc, hAc, min_eq_left (show 3 ≤ K by omega)]), run_emitCode]
    simp [entry, wordOf]

/-! ## Rounds -/

/-- Emit the entry for `vRI`, `vRJ` followed by `E1`. -/
def cellP : Pr V :=
  .seq (.set vAI (.v vRI)) (.seq (.set vAJ (.v vRJ)) (.seq actionP (.seq entryP (outW Sym.E1.bits))))

set_option maxRecDepth 100000 in
lemma cellP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ)
    (hI : ρ vRI < (toLC C).M) (hJ : ρ vRJ < (toLC C).M) :
    (cellP.run w K ρ).2 =
      wordOf (entry ((toLC C).tab (Conc.inp C) (ρ vRI) (ρ vRJ)) ++ [.E1]) := by
  unfold cellP
  rw [run_seq_of (run_eq_st' (by rfl) ρ), run_seq_of (run_eq_st' (by rfl) _),
    run_seq_of (run_eq_st' (by rfl) _), run_seq, run_outW]
  simp only [st_set, eval_v]
  have G1 := (hG.upd vAI (by decide) (ρ vRI)).upd vAJ (by decide)
    (Function.update ρ vAI (ρ vRI) vRJ)
  have e : Function.update ρ vAI (ρ vRI) vRJ = ρ vRJ := by simp (config := {decide := true})
  rw [e] at G1 ⊢
  obtain ⟨a1, a2, -, -, a5⟩ := actionP_spec hE hC _ G1
  have G2 := G1.st (w := w) (K := K) actionP (globs_disj _ (by decide))
  have hAI : st w K actionP (Function.update (Function.update ρ vAI (ρ vRI)) vAJ (ρ vRJ)) vAI =
      ρ vRI := by rw [st_frame _ _ _ (by decide)]; simp (config := {decide := true})
  have hAJ : st w K actionP (Function.update (Function.update ρ vAI (ρ vRI)) vAJ (ρ vRJ)) vAJ =
      ρ vRJ := by rw [st_frame _ _ _ (by decide)]; simp (config := {decide := true})
  simp (config := {decide := true}) only [Function.update_self, Function.update_of_ne, ne_eq]
    at a1 a2 a5
  rw [entryP_spec hE hC _ G2 (by rw [hAI]; exact hI) (by rw [hAJ]; exact hJ)
    (by rw [a1, hAI, hAJ]) (by rw [a2, hAI]) (by rw [a5, hAJ]), hAI, hAJ, wordOf_append]
  simp [wordOf]

/-- A row of the table. -/
def rowP : Pr V := .seq (.loop vRI (.v vM) cellP) (outW Sym.E2.bits)

set_option maxRecDepth 100000 in
lemma rowP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ)
    (hM : ρ vM = (toLC C).M) (hJ : ρ vRJ < (toLC C).M) :
    (rowP.run w K ρ).2 = wordOf (rowSyms ((toLC C).tab (Conc.inp C)) (toLC C).M (ρ vRJ) ++ [.E2]) := by
  unfold rowP
  rw [run_seq, run_outW, run_loop_out _ _ _ _
    (fun i => wordOf (entry ((toLC C).tab (Conc.inp C) i (ρ vRJ)) ++ [.E1])) (by
      intro i hi ρ' hfr
      simp only [eval_v, hM] at hi
      have Gq := hG.fr ρ' (fun z hz => hfr z (globs_disj _ (by decide) z hz))
      rw [cellP_spec hE hC _ (Gq.upd vRI (by decide) i) (by simpa using hi)
        (by simp (config := {decide := true}) [hfr vRJ (by decide), hJ])]
      simp (config := {decide := true}) [hfr vRJ (by decide)])]
  simp only [eval_v, hM, rowSyms, wordOf_append, wordOf_flatMap]
  simp [wordOf]

/-- A round: the whole table. -/
def roundP : Pr V := .seq (.loop vRJ (.v vM) rowP) (outW Sym.E3.bits)

set_option maxRecDepth 100000 in
lemma roundP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ)
    (hM : ρ vM = (toLC C).M) :
    (roundP.run w K ρ).2 = wordOf (PD.round ((toLC C).tab (Conc.inp C)) (toLC C).M) := by
  unfold roundP
  rw [run_seq, run_outW, run_loop_out _ _ _ _
    (fun j => wordOf (rowSyms ((toLC C).tab (Conc.inp C)) (toLC C).M j ++ [.E2])) (by
      intro j hj ρ' hfr
      simp only [eval_v, hM] at hj
      have Gq := hG.fr ρ' (fun z hz => hfr z (globs_disj _ (by decide) z hz))
      rw [rowP_spec hE hC _ (Gq.upd vRJ (by decide) j)
        (by simp (config := {decide := true}) [hfr vM (by decide), hM]) (by simpa using hj)]
      simp)]
  simp only [eval_v, hM, PD.round, wordOf_append, wordOf_flatMap]
  simp [wordOf]

end LP

end BLMS

end PathChecking
