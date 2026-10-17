module

public import RequestProject.BLMS.LEmit
public import RequestProject.LogLang.Defs

/-!
# The reduction is computed by a loop program

`LP.mainP` computes the global values (number of tokens and gates, the top layer, `N` and `D`),
emits the initial configuration of the code machine and then `T` copies of its table.  Its output
on (the encoding of) a stratified circuit `C` is `circWord C` (`circProg_output`).
-/

@[expose] public section

namespace PathChecking

namespace BLMS

namespace LP

open LL PD

variable {C : Circuit} {w : Word} {K : ℕ}

/-- Computation of the global variables. -/
def initP : Pr V :=
  .seq (.set vNT (.bin .div .len (.c 5))) (.seq gstartP (.seq (.set vNG (.v vGcnt))
    (.seq (.set vDi (.bin .sub (.v vNG) (.c 1))) (.seq depP (.seq (.set vTop (.v vDcnt))
      (.seq (.set vBl (.c 1)) (.seq bdP (.seq (.set vN (.v vBd))
        (.set vD (.bin .add (.v vTop) (.c 1)))))))))))

lemma initP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) :
    Glob C (st w K initP ρ) := by
  have hK := hE.nK
  have hl := hE.lenK
  have hlen := hE.len
  unfold initP
  simp only [st_seq, st_set, eval_bin, ap_div, eval_len, eval_c, min_eq_left (show 5 ≤ K by omega),
    min_eq_left (show w.length ≤ K by omega)]
  have h1 : w.length / 5 = (gts C).length := by omega
  rw [h1]
  obtain ⟨-, g2⟩ := gstart_spec hE (Function.update ρ vNT (gts C).length) (by simp)
  have f2 : ∀ z ∉ gstartP.wr, st w K gstartP (Function.update ρ vNT (gts C).length) z =
      Function.update ρ vNT (gts C).length z := fun z hz => st_frame _ _ _ hz
  generalize st w K gstartP (Function.update ρ vNT (gts C).length) = ρ2 at g2 f2
  have nt2 : ρ2 vNT = (gts C).length := by rw [f2 _ (by decide)]; simp
  simp only [eval_v, g2, ap_sub, min_eq_left (show 1 ≤ K by omega)]
  have d := depP_spec hE hC (Function.update (Function.update ρ2 vNG C.length) vDi
    (Function.update ρ2 vNG C.length vNG - 1)) (by simp (config := {decide := true}) [nt2])
    (by simp (config := {decide := true}))
  have f5 : ∀ z ∉ depP.wr, st w K depP (Function.update (Function.update ρ2 vNG C.length) vDi
      (Function.update ρ2 vNG C.length vNG - 1)) z = Function.update (Function.update ρ2 vNG
      C.length) vDi (Function.update ρ2 vNG C.length vNG - 1) z := fun z hz => st_frame _ _ _ hz
  generalize st w K depP (Function.update (Function.update ρ2 vNG C.length) vDi
    (Function.update ρ2 vNG C.length vNG - 1)) = ρ5 at d f5
  simp only [Function.update_self] at d
  have nt5 : ρ5 vNT = (gts C).length := by
    rw [f5 _ (by decide)]; simp (config := {decide := true}) [nt2]
  have ng5 : ρ5 vNG = C.length := by
    rw [f5 _ (by decide)]; simp (config := {decide := true})
  have e5 : ρ5 vDcnt = Conc.top C := d
  simp only [e5]
  have b := bdP_spec hE hC (Function.update (Function.update ρ5 vTop (Conc.top C)) vBl 1)
    (by simp (config := {decide := true}) [nt5]) (by simp (config := {decide := true}) [ng5])
    (by simp (config := {decide := true}))
  have f8 : ∀ z ∉ bdP.wr, st w K bdP (Function.update (Function.update ρ5 vTop (Conc.top C)) vBl 1) z
      = Function.update (Function.update ρ5 vTop (Conc.top C)) vBl 1 z :=
    fun z hz => st_frame _ _ _ hz
  generalize st w K bdP (Function.update (Function.update ρ5 vTop (Conc.top C)) vBl 1) = ρ8 at b f8
  simp only [Function.update_self] at b
  have top8 : ρ8 vTop = Conc.top C := by
    rw [f8 _ (by decide)]; simp (config := {decide := true})
  have htop : Conc.top C + 1 ≤ K := by have := dep_le (C := C) (C.length - 1); unfold Conc.top; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [Function.update_of_ne, ne_eq]
    rw [f8 _ (by decide)]; simp (config := {decide := true}) [nt5]
  · simp (config := {decide := true}) only [Function.update_of_ne, ne_eq]
    rw [f8 _ (by decide)]; simp (config := {decide := true}) [ng5]
  · simp (config := {decide := true}) only [Function.update_of_ne, ne_eq, top8]
  · simp (config := {decide := true}) only [Function.update_of_ne, ne_eq, Function.update_self, b]
    rfl
  · simp (config := {decide := true}) only [Function.update_self, Function.update_of_ne, ne_eq,
      top8]
    rw [ap_add, min_eq_left htop]
    rfl

/-- The whole program. -/
def mainP : Pr V :=
  .seq initP (.seq (.set vEc (.c 0)) (.seq (emitCode vEc) (.seq (.set vNd (.c 0))
    (.seq nextRunP (.seq (setCode vEc vNa vNb) (.seq (emitCode vEc) (.seq (outW Sym.E1.bits)
      (.seq (outW Sym.E3.bits)
        (.seq (.set vM (.bin .mul (.bin .add (.v vN) (.c 1)) (.bin .add (.v vN) (.c 1))))
          (.seq (.set vTT (.bin .add (.bin .mul (.c 3) (.v vN)) (.c 3)))
            (.loop vT (.v vTT) roundP)))))))))))

lemma wordOf_replicate_flatten (T : ℕ) (u : List Sym) :
    wordOf (List.replicate T u).flatten = (List.range T).flatMap (fun _ => wordOf u) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [List.range_succ, List.flatMap_append, ← ih, List.replicate_succ', List.flatten_append,
      wordOf_append]
    simp

set_option maxRecDepth 100000 in
lemma mainP_output (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) :
    (mainP.run w K ρ).2 = circWord C := by
  have hK := hE.nK
  have hM := hE.MK
  have hN := N_le (C := C)
  have G0 := initP_spec hE hC ρ
  unfold mainP
  rw [run_seq_of (run_eq_st' (by rfl) ρ), run_seq_of (run_eq_st' (by rfl) _),
    run_seq_of (run_emitCode _ _)]
  generalize st w K initP ρ = ρ0 at G0
  simp only [st_set, eval_c, min_eq_left (Nat.zero_le K), Function.update_self]
  set ρ1 := st w K (emitCode vEc) (Function.update ρ0 vEc 0)
  have G1 : Glob C ρ1 := G0.upd vEc (by decide) 0 |>.st (w := w) (K := K) (emitCode vEc)
    (globs_disj _ (by decide))
  rw [run_seq_of (run_eq_st' (by rfl) _), run_seq_of (run_eq_st' (by rfl) _),
    run_seq_of (run_eq_st' (by rfl) _), run_seq_of (run_emitCode _ _)]
  simp only [st_set, eval_c, min_eq_left (Nat.zero_le K)]
  have G2 := G1.upd vNd (by decide) 0
  obtain ⟨n1, n2⟩ := nextRunP_spec hE hC _ G2
  simp only [Function.update_self] at n1 n2
  have G3 := G2.st (w := w) (K := K) nextRunP (globs_disj _ (by decide))
  have hb := LC.nextRun_le (c := toLC C) (inp := Conc.inp C) 0
  rw [setCode_spec hE _ G3 vEc vNa vNb (by rw [n1]; exact hb.1) (by rw [n2]; exact hb.2), n1, n2]
  set ρ4 := st w K (emitCode vEc) (st w K (setCode vEc vNa vNb)
    (st w K nextRunP (Function.update ρ1 vNd 0)))
  have G4 : Glob C ρ4 := (G3.st (w := w) (K := K) (setCode vEc vNa vNb) (globs_disj _ (by decide))).st
    (w := w) (K := K) (emitCode vEc) (globs_disj _ (by decide))
  rw [run_seq_of (run_outW _ _), run_seq_of (run_outW _ _), run_seq_of (run_eq_st' (by rfl) _),
    run_seq_of (run_eq_st' (by rfl) _)]
  simp only [st_set]
  have hMv : (Ex.bin .mul (.bin .add (.v vN) (.c 1)) (.bin .add (.v vN) (.c 1)) : Ex V).eval w K ρ4
      = (toLC C).M := by
    simp only [eval_bin, ap_mul, ap_add, eval_v, eval_c, G4.n, min_eq_left (show 1 ≤ K by omega),
      min_eq_left (show (toLC C).N + 1 ≤ K by omega), LC.M]
    rw [min_eq_left hM]
  rw [hMv]
  set ρ5 := Function.update ρ4 vM (toLC C).M
  have G5 : Glob C ρ5 := G4.upd vM (by decide) _
  have hT : (Ex.bin .add (.bin .mul (.c 3) (.v vN)) (.c 3) : Ex V).eval w K ρ5 = (toLC C).T := by
    have : 3 * (toLC C).N + 3 ≤ K := by have := hE.K_ge; have := length_le_gts (C := C); have := hE.gts_le; nlinarith
    simp only [eval_bin, ap_mul, ap_add, eval_v, eval_c, G5.n, LC.T,
      min_eq_left (show 3 ≤ K by omega), min_eq_left (show 3 * (toLC C).N ≤ K by omega),
      min_eq_left this]
  rw [run_loop_out _ _ _ _ (fun _ => wordOf (PD.round ((toLC C).tab (Conc.inp C)) (toLC C).M))
    (by
      intro i _ ρ' hfr
      have Gq : Glob C (Function.update ρ5 vTT ((Ex.bin .add (.bin .mul (.c 3) (.v vN)) (.c 3) :
          Ex V).eval w K ρ5)) := G5.upd vTT (by decide) _
      have Gq' := Gq.fr ρ' (fun z hz => hfr z (globs_disj _ (by decide) z hz))
      exact roundP_spec hE hC _ (Gq'.upd vT (by decide) i)
        (by simp (config := {decide := true}) [hfr vM (by decide), ρ5]))]
  simp only [eval_v, Function.update_self]
  rw [show (Ex.bin .add (.bin .mul (.c 3) (.v vN)) (.c 3) : Ex V).eval w K ρ5 = (toLC C).T from hT]
  unfold circWord LC.specWord
  simp only [entry, List.flatMap_cons, List.flatMap_nil, List.append_nil, wordOf_append,
    wordOf_cons, wordOf_replicate_flatten, List.nil_append, List.append_assoc]
  simp [LC.code, LC.vL]

end LP

theorem circProg_output : ∃ (V E : ℕ) (P : LL.Pr V), ∀ C : Circuit, StratMCVPInstance C →
    P.output E C.encode = circWord C := by
  refine ⟨LP.V, 5, LP.mainP, fun C hC => ?_⟩
  unfold LL.Pr.output
  have hn : 0 < (LP.gts C).length := by
    have hne := hC.1.1
    obtain ⟨g, gs, rfl⟩ := List.exists_cons_of_ne_nil hne
    have := LP.toks_pos g
    simp [LP.gts]; omega
  have hlen : C.encode.length = 5 * (LP.gts C).length := SQ.encodeToks_length _
  refine LP.mainP_output ⟨rfl, ?_⟩ hC _
  unfold LL.capOf
  set x := C.encode.length + 2
  have hx : 3 ≤ x := by omega
  have h3 : 27 ≤ x ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
  have : x ^ 5 = x ^ 2 * x ^ 3 := by ring
  have h2 : 9 ≤ x ^ 2 := by nlinarith
  change 4 * x ^ 2 + 100 ≤ x ^ 5 + 3
  nlinarith

end BLMS

end PathChecking
