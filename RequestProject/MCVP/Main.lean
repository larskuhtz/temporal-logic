module

public import RequestProject.MCVP.OutTree
public import RequestProject.Logspace.Machine
public import RequestProject.Logspace.Compose

/-!
# The reduction from MCVP to CTL* tree checking is logspace computable

`redProg` is a register program (20 registers, all bounded by `4|w| + 4`) that first validates
its input and then streams the CTL* instance.  Compiling it with
`logspaceComputable_of_prog` yields a logspace transducer for the reduction map `redFun`.

Main results:

* `redFun_logspaceComputable : LogspaceComputable redFun`;
* `MCVP_logspaceReducible_CTLStar : LogspaceReducible MCVP CTLStarTreeChecking`;
* `CTLStarTreeChecking_PHard_of_MCVP`: if MCVP is `P`-hard, then CTL* tree checking is
  `P`-hard (using `LogspaceReducible.trans` from `RequestProject/Logspace/Compose.lean`).

## References

P-hardness of MCVP: Goldschlager [Gol77] (see also Ladner [Lad75]). Composition of logspace
reductions: Jones [Jon75]. We know of no published source for the reduction from MCVP to CTL*
tree checking given here and have not checked the literature for one. Full entries are in
`REFERENCES.md`.
-/

@[expose] public section

namespace PathChecking

namespace MCVPReduction

open LS
open scoped LS

variable {w : Word} {B : ℕ}

/-- Output phase: stream `( Φ_n ) t` for the (valid) input circuit. -/
def outputProg : Stmt 20 :=
  emitToks [.lpar] ⨟ formulaLoop ⨟ emitToks ((CTLStar.ap aInit).toks ++ [.rpar]) ⨟
  treeLoop ⨟ closeLoop

/-- **The reduction program**: validate the input, and if it is valid, stream the instance. -/
def redProg : Stmt 20 := validate ⨟ .ite (.zero rOk) .skip outputProg

/-- Register bound of `redProg`. -/
def redBound (w : Word) : ℕ := 4 * w.length + 4

lemma rN_not_mem_flClob : rN ∉ flClob := by decide
lemma rN_not_mem_tlClob : rN ∉ tlClob := by decide

lemma ach_outputProg {C : List MGate} (hw : w = encodeCircuit C) (hC : C ≠ [])
    (hwf : WellFormed C) (σ : St 20) (hN : σ.reg rN = C.length) (hB : 4 * w.length + 4 ≤ B) :
    Ach w B outputProg σ (fun τ => τ.out = σ.out ++ instanceWord C) := by
  have hCw := length_le_word hw
  unfold outputProg
  refine ach_seq (ach_emitToks _ _ _ (ach_seq (ach_formulaLoop hw _ _ (by simpa using hN) hB ?_)))
  intro τ₁ ho₁ hf₁
  have hN1 : τ₁.reg rN = C.length := (hf₁ rN rN_not_mem_flClob).trans (by simpa using hN)
  refine ach_seq (ach_emitToks _ _ _ (ach_seq (ach_treeLoop hw hwf _ _ (by simpa using hN1) hB ?_)))
  intro τ₂ ho₂ hf₂
  have hN2 : τ₂.reg rN = C.length := (hf₂ rN rN_not_mem_tlClob).trans (by simpa using hN1)
  refine ach_closeLoop τ₂ _ C.length hN2 (by omega) ?_
  intro τ₃ ho₃
  rw [ho₃, ho₂]
  simp only [ho₁, instanceWord, reductionFormula, levelFormula_toks, reductionTree_toks C hC]
  simp only [← encodeToks_append, List.append_assoc]
  simp

lemma ach_redProg (w : Word) :
    Ach w (redBound w) redProg (St.init 20) (fun τ => τ.out = redFun w) := by
  unfold redProg
  refine ach_seq (ach_validate _ _ (by simp [redBound]; omega) ?_)
  intro τ ho _ hok hN
  refine ach_ite ?_
  by_cases h0 : τ.reg rOk = 0
  · rw [if_pos (by simp [Cond.eval, h0])]
    refine ach_skip ?_
    have hnv : ¬ ValidCode w := fun h' => (hok.2 h') h0
    rw [ho, redFun_invalid hnv]; rfl
  · rw [if_neg (by simp [Cond.eval, h0])]
    obtain ⟨C, hC, hwf, hw⟩ := hok.1 h0
    refine (ach_outputProg hw hC hwf τ (hN C hw h0) (by simp [redBound])).mono ?_
    intro τ' h'
    rw [h', ho, hw, redFun_encode hC hwf]; rfl

lemma redBound_lt (w : Word) : redBound w < 2 ^ (4 * (Nat.log 2 w.length + 1)) := by
  set L := Nat.log 2 w.length + 1
  have h1 : w.length < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : 2 ^ (L + 2) < 2 ^ (4 * L) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (L + 2) = 4 * 2 ^ L := by rw [pow_add]; ring
  unfold redBound; omega

/-- **The reduction map is logspace computable** (for the actual binary encodings of circuits
and of CTL* instances). -/
theorem redFun_logspaceComputable : LogspaceComputable redFun := by
  refine logspaceComputable_of_prog redProg redFun redBound 4 redBound_lt ?_
  intro w
  obtain ⟨σ', h1, h2⟩ := ach_redProg w
  exact ⟨σ', h1, h2⟩

/-- **MCVP is logspace many-one reducible to CTL* tree checking.** -/
theorem MCVP_logspaceReducible_CTLStar : LogspaceReducible MCVP CTLStarTreeChecking :=
  ⟨redFun, redFun_logspaceComputable, redFun_correct⟩

/-- **P-hardness of CTL* tree checking, conditionally**: if the monotone circuit value
problem (with the encoding `encodeCircuit`) is `P`-hard, then CTL* tree checking is `P`-hard.
Transitivity of logspace reductions is proved in `RequestProject/Logspace/Compose.lean`
(`LogspaceReducible.trans`). -/
theorem CTLStarTreeChecking_PHard_of_MCVP (hMCVP : PHard MCVP) : PHard CTLStarTreeChecking :=
  fun A hA => (hMCVP A hA).trans MCVP_logspaceReducible_CTLStar

end MCVPReduction

end PathChecking
