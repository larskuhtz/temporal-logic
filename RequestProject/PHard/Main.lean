module

public import RequestProject.PHard.Run

/-!
# P-hardness of the monotone circuit value problem

Every language in `P` (in the Turing machine model of `Complexity.lean`) is logspace
many-one reducible to `MCVP`: the reduction maps `w` to the tableau circuit
`tabCircuit M c w` of a polynomial-time machine `M` deciding the language.

## References

* R. E. Ladner, *The Circuit Value Problem is Log Space Complete for P*, SIGACT News 7(1), 1975
  [Lad75];
* L. M. Goldschlager, *The Monotone and Planar Circuit Value Problems are Log Space Complete for
  P*, SIGACT News 9(2), 1977 [Gol77];
* R. Greenlaw, H. J. Hoover, W. L. Ruzzo, *Limits to Parallel Computation: P-Completeness
  Theory*, Oxford University Press, 1995 [GHR95].

The proof here follows the classical tableau construction, adapted to the Turing machine
model of `Complexity.lean`. Full entries are in `REFERENCES.md`.
-/

@[expose] public section

namespace PathChecking

namespace PHardness

open Classical MCVPReduction

lemma tabRed_logspaceComputable (M : TM) (c : ℕ) : LogspaceComputable (tabRed M c) :=
  tabRed_logspaceComputable' M c

lemma tabRed_mem_MCVP (M : TM) (c : ℕ) (w : Word) :
    tabRed M c w ∈ MCVP ↔ eval (tabCircuit M c w) = true := by
  constructor
  · rintro ⟨C, -, -, hw, hC⟩
    rw [encodeCircuit_injective hw]; exact hC
  · intro h
    exact ⟨_, tabCircuit_ne_nil M c w, tabCircuit_wellFormed M c w, rfl, h⟩

/-- **MCVP is `P`-hard** under logspace many-one reductions. -/
theorem MCVP_PHard : PHard MCVP := by
  intro A hA
  obtain ⟨M, c, hM⟩ := hA
  refine ⟨tabRed M c, tabRed_logspaceComputable M c, fun w => ?_⟩
  rw [tabRed_mem_MCVP, tabCircuit_eval]
  obtain ⟨t, ht, hH⟩ := hM w
  have hrun : M.run w (Tb c w.length) = M.run w t := TM.run_halted' _ _ hH.1 ht
  rw [hrun, hH.2]
  simp only [hH.1, true_and, charWord]
  by_cases h : w ∈ A <;> simp [h, absO]

end PHardness

end PathChecking
