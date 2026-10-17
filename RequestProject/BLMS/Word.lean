module

public import RequestProject.BLMS.DPDA
public import RequestProject.BLMS.Concrete

/-!
# The input word of the pushdown automaton

`LC.specWord c inp`: the initial configuration of the code machine followed by `3 N + 3` copies of
the table of the machine.  The automaton `PD.pda` accepts it iff the layered circuit accepts the
input (`LC.specWord_accepts`).  For a stratified circuit `C` we take the layered circuit
`toLC C` (`circWord_accepts`).
-/

@[expose] public section

namespace PathChecking

namespace BLMS

open LC (TRes MRes)

namespace LC

variable (c : LC) (inp : ℕ → Bool)

/-- Number of codes. -/
def M : ℕ := (c.N + 1) * (c.N + 1)

/-- Number of rounds. -/
def T : ℕ := 3 * c.N + 3

/-- The input word of the automaton. -/
def specWord : Word :=
  PD.wordOf (PD.entry (.scr [c.code vL, c.code (c.nextRun inp 0)]) ++ .E1 :: .E3 ::
    (List.replicate c.T (PD.round (c.tab inp) c.M)).flatten)

variable {c inp}

lemma mstep_eq (l : List ℕ) : c.mstep inp l = PD.gstep (c.tab inp) l := by
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> rfl

lemma mrun_eq : ∀ k r, c.mrun inp k r = PD.grun (c.tab inp) k r := by
  intro k
  induction k with
  | zero => intro r; rfl
  | succ k ih =>
    intro r
    rcases r with _ | _ | l
    · rfl
    · rfl
    · simp only [mrun, PD.grun, mstep_eq, ih]

lemma code_lt {p : ℕ × ℕ} (h1 : p.1 ≤ c.N) (h2 : p.2 ≤ c.N) : c.code p < c.M := by
  unfold code M
  nlinarith

lemma dec_le {k : ℕ} (hk : k < c.M) : (c.dec k).1 ≤ c.N ∧ (c.dec k).2 ≤ c.N := by
  unfold dec M at *
  refine ⟨?_, Nat.lt_succ_iff.1 (Nat.mod_lt _ (by omega))⟩
  have := Nat.div_lt_of_lt_mul hk
  simp only
  omega

lemma nextRun_le (d : ℕ) : (c.nextRun inp d).1 ≤ c.N ∧ (c.nextRun inp d).2 ≤ c.N := by
  obtain ⟨h1, -, h3, -⟩ := nextRun_spec (c := c) (inp := inp) (d := d)
  rcases h3 with h | h
  · rw [h]; simp [vR]
  · exact ⟨by omega, h1⟩

lemma tab_lt (cI cJ : ℕ) (hI : cI < c.M) (hJ : cJ < c.M) (s : List ℕ)
    (hs : c.tab inp cI cJ = .scr s) : ∀ k ∈ s, k < c.M := by
  have dI := dec_le hI
  have dJ := dec_le hJ
  unfold tab at hs
  split at hs
  · cases hs
  · cases hs
  · cases hs
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    subst hk
    exact code_lt (p := ((c.dec cI).1, (c.dec cJ).2)) dI.1 dJ.2
  · cases hs
    have := nextRun_le (c := c) (inp := inp) (c.dec cJ).2
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact hI
    · exact hJ
    · exact code_lt this.1 this.2
  · cases hs; simpa using hJ

/-- **The automaton decides the layered circuit.** -/
theorem specWord_accepts (hP : c.Planar) : PD.pda.Accepts (c.specWord inp) ↔ c.out (c.X0 inp) := by
  have hT : 3 * c.N + 3 ≤ c.T := le_rfl
  obtain ⟨ha, hr⟩ := mrun_correct (c := c) (inp := inp) hP hT
  have hcfg : c.cfg [] (c.nextRun inp 0) = [c.code (c.nextRun inp 0), c.code vL] := rfl
  rw [hcfg, mrun_eq] at ha hr
  have hb := nextRun_le (c := c) (inp := inp) 0
  have h := PD.accepts_iff (c.tab inp) c.M (tab_lt (c := c) (inp := inp))
    (a := c.code vL) (b := c.code (c.nextRun inp 0)) (code_lt (by simp [vL]) (by simp [vL]))
    (code_lt hb.1 hb.2) c.T (by
      by_cases ho : c.out (c.X0 inp)
      · exact Or.inl (ha ho)
      · exact Or.inr (hr ho))
  unfold specWord
  rw [h]
  constructor
  · intro h'
    by_contra ho
    rw [hr ho] at h'
    cases h'
  · exact ha

end LC

/-- The input word of the automaton for a circuit. -/
def circWord (C : Circuit) : Word := (toLC C).specWord (Conc.inp C)

/-- **The automaton decides stratified monotone planar circuits.** -/
theorem circWord_accepts {C : Circuit} (h : StratMCVPInstance C) :
    PD.pda.Accepts (circWord C) ↔ C.eval ∅ [] = true := by
  obtain ⟨hP, ho⟩ := Conc.toLC_correct h
  rw [circWord, LC.specWord_accepts hP, ho]

end BLMS

end PathChecking
