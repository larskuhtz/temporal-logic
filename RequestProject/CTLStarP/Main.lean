module

public import RequestProject.CTLStarP.Prog.Phase2

/-!
# CTL* tree checking is in `P`: the decision procedure

The decision procedure, as a structured program:

1. count the input tokens (`countP`); if the input is not a sequence of token codes, reject;
2. first phase: tables of well-formed subformulas and lists of subtrees (`tabStep`), then the
   check that the input encodes an instance `( φ ) t` (`topP`);
3. second phase: the table of truth values `val j u ℓ` (`phase2`);
4. final check: `φ` holds on all paths from the root (`finalP`).

All values stay below `16 (|w| + 2)^3 + 64`, so `polytimeComputable_of_hl` turns the program into a
polynomial-time Turing machine; this is done in Theorem 3 (`CTLStarTreeChecking_mem_P`,
`RequestProject/Statements.lean`).  Correctness is `decideCTL_iff`, and `CTLP.main_correct`
states it for the program.

## References

This program and its proof were written for this project. We have not checked whether a
published source states that CTL* tree checking is in `P`, so we give no attribution. Full
entries for the references used elsewhere are in `REFERENCES.md`.
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open HL PT MCVPReduction LS

/-! ## Decoding the input into tokens -/

lemma rtok_lt_29 {w : Word} {p : ℕ} (h : rtok w p < 29) :
    ∃ t : Tok, At w (5 * p + 1) t.bits := by
  unfold rtok at h
  split_ifs at h with h1 h2
  · omega
  · exact h2
  · omega

lemma rtok_eq_29 {w : Word} {p : ℕ} (h : rtok w p = 29) : w.length ≤ 5 * p := by
  unfold rtok at h
  split_ifs at h with h1 h2
  · exact h1
  · have := Tok.code_lt h2.choose; omega
  · omega

lemma decode_prefix (w : Word) : ∀ n, (∀ p < n, rtok w p < 29) →
    ∃ ts : List Tok, ts.length = n ∧ At w 1 (encodeToks ts) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨[], rfl, At.nil le_rfl (by omega)⟩
  | succ n ih =>
    intro h
    obtain ⟨ts, hl, hts⟩ := ih (fun p hp => h p (by omega))
    obtain ⟨t, ht⟩ := rtok_lt_29 (h n (by omega))
    refine ⟨ts ++ [t], by simp [hl], At.toks_append.2 ⟨hts, ?_⟩⟩
    rw [hl, show 1 + 5 * n = 5 * n + 1 by omega, encodeToks_cons]
    simpa [encodeToks] using ht

lemma decode_eq {w : Word} {n : ℕ} (hlt : ∀ p < n, rtok w p < 29) (h29 : rtok w n = 29) :
    ∃ ts : List Tok, ts.length = n ∧ w = encodeToks ts := by
  obtain ⟨ts, hl, -, -, hp⟩ := decode_prefix w n hlt
  refine ⟨ts, hl, ?_⟩
  have hle := rtok_eq_29 h29
  simp only [Nat.sub_self, List.drop_zero] at hp
  have := hp.length_le
  rw [encodeToks_length, hl] at this
  exact (hp.eq_of_length (by rw [encodeToks_length, hl]; omega)).symm

lemma rtok_ne_30 {ts : List Tok} (p : ℕ) : rtok (encodeToks ts) p ≠ 30 := by
  rw [rtok_encode]; have := tc_le ts p; omega

/-! ## Counting the tokens -/

/-- `N :=` the number of tokens (the first position whose code is `≥ 29`). -/
def countP : Hs M :=
  .set vN (.const 0) ;;
  .loop (Ex.lt (.tok (.var vN)) (.const 29)) (.set vN (.var vN + .const 1))

theorem hach_countP {w : Word} {B : ℕ} (hB : w.length + 64 ≤ B) (σ : HSt M) :
    HAch w B countP σ (fun σ' => σ'.mem = σ.mem ∧ σ'.out = σ.out ∧
      (∀ p < σ'.v vN, rtok w p < 29) ∧ 29 ≤ rtok w (σ'.v vN) ∧ σ'.v vN ≤ w.length) := by
  refine hach_seq (hach_set (bnd_const' (by omega)) ?_)
  refine hach_while (fun σ1 => σ1.mem = σ.mem ∧ σ1.out = σ.out ∧
      (∀ p < σ1.v vN, rtok w p < 29) ∧ σ1.v vN ≤ w.length) (fun σ1 => w.length - σ1.v vN) _
    ?_ ?_ ?_ _ ⟨rfl, rfl, fun p hp => by simp at hp, by simp⟩
  · rintro σ1 ⟨-, -, -, h⟩
    exact bnd_lt' (bnd_tok' (by simp; omega)) (bnd_const' (by omega))
  · rintro σ1 ⟨h1, h2, h3, h4⟩ hc
    simp only [ev_lt, ev_tok, ev_var, ev_const, bv_eq_zero, decide_eq_false_iff_not,
      not_lt] at hc
    exact ⟨h1, h2, h3, hc, h4⟩
  · rintro σ1 ⟨h1, h2, h3, h4⟩ hc
    simp only [ev_lt, ev_tok, ev_var, ev_const, ne_eq, bv_eq_zero, decide_eq_false_iff_not,
      not_lt, not_le] at hc
    have hlt : σ1.v vN < w.length := by
      by_contra hge
      rw [rtok_end (by omega)] at hc; omega
    refine hach_set (by simp; omega) ⟨⟨by simp [h1], by simp [h2], fun p hp => ?_, by simp; omega⟩, ?_⟩
    · simp only [HSt.set_v, Function.update_self, ev_add, ev_var, ev_const] at hp
      rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
      · exact h3 p hp
      · exact hc
    · simp; omega

/-! ## The whole program -/

/-- First phase: fill the tables. -/
def phase1 : Hs M :=
  .set vTP (.var vN) ;; .loop (Ex.lt (.const 0) (.var vTP)) (.set vTP (.var vTP - .const 1) ;; tabStep)

/-- The decision procedure. -/
def mainP : Hs M :=
  countP ;;
  .ite (Ex.eq (.tok (.var vN)) (.const 29))
    (phase1 ;; topP ;; .ite (.var vVT) (phase2 ;; finalP) (.out false))
    (.out false)

variable {w : Word} {B : ℕ} {ts : List Tok}

theorem hach_phase1 (hc : Ctx ts w B) (σ : HSt M) (hN : σ.v vN = ts.length)
    (hm : σ.mem = ∅) :
    HAch w B phase1 σ (fun σ' => σ'.v vN = ts.length ∧ σ'.out = σ.out ∧
      ∀ x, x ∈ σ'.mem ↔ Mem1 ts 0 0 x) := by
  have hB64 := hc.b64
  have hBn := hc.bn
  refine hach_seq (hach_set (by simp [hN]; omega) ?_)
  let I : ℕ → HSt M → Prop := fun k σ1 => k ≤ ts.length ∧ σ1.v vN = ts.length ∧
    σ1.out = σ.out ∧ ∀ x, x ∈ σ1.mem ↔ Mem1 ts k k x
  refine (hach_forDown (by omega) vTP I ?_ ts.length (by omega)
    (σ.set vTP ((Ex.var vN : Ex M).ev w σ))
    ⟨le_rfl, by simp [hN], rfl, fun x => by simp [hm, Mem1]; omega⟩ (by simp [hN])).mono ?_
  · intro p σ1 ⟨hp, hN1, ho1, hm1⟩ hP
    refine (hach_tabStep hc (σ1.set vTP p) p (by omega) (by simp [hN1]) (by simp) hm1).mono ?_
    rintro σ2 ⟨h2N, h2P, h2o, h2m⟩
    exact ⟨⟨by omega, h2N, by rw [h2o, HSt.set_out, ho1], h2m⟩, h2P⟩
  · rintro σ' ⟨⟨-, hN', ho, hm'⟩, -⟩
    exact ⟨hN', ho, hm'⟩

/-- On an encoding of a token list, the program outputs the decision of `decideCTL`. -/
theorem hach_main_tokens (hc : Ctx ts w B) (σ : HSt M) (hN : σ.v vN = ts.length)
    (hm : σ.mem = ∅) :
    HAch w B (phase1 ;; topP ;; .ite (.var vVT) (phase2 ;; finalP) (.out false)) σ
      (fun σ' => σ'.out = σ.out ++ [decideCTL ts]) := by
  have hB64 := hc.b64
  refine hach_seq ((hach_phase1 hc σ hN hm).mono ?_)
  rintro σ2 ⟨h2N, h2o, h2m⟩
  refine hach_seq ((hach_topP hc σ2 h2N h2m).mono ?_)
  rintro σ3 ⟨h3V, hf3⟩
  have h3N : σ3.v vN = ts.length := by rw [hf3.1 _ (by decide), h2N]
  have h3m : ∀ x, x ∈ σ3.mem ↔ Mem1 ts 0 0 x := by rw [hf3.2.1]; exact h2m
  have hb := bv_le (validTop ts)
  refine hach_ite (by simp [h3V]; omega) ?_
  cases hv : validTop ts
  · rw [if_neg (by simp [h3V, hv])]
    refine hach_out ?_
    simp [hf3.2.2, h2o, decideCTL, hv]
  · rw [if_pos (by simp [h3V, hv])]
    refine hach_seq ((hach_phase2 hc h3N h3m).mono ?_)
    rintro σ4 ⟨h4v, h4o, h4m⟩
    refine (hach_finalP hc (by rw [h4v _ (by decide), h3N]) hv h4m).mono ?_
    intro σ5 h5
    rw [h5, h4o, hf3.2.2, h2o]

/-- The bound on all values. -/
def bound (w : Word) : ℕ := 16 * (w.length + 2) ^ 3 + 64

lemma mem_iff_decideCTL (ts : List Tok) :
    encodeToks ts ∈ CTLStarTreeChecking ↔ decideCTL ts = true := by
  rw [decideCTL_iff]
  constructor
  · rintro ⟨φ, t, he, hs⟩
    exact ⟨φ, t, encodeToks_injective he, hs⟩
  · rintro ⟨φ, t, rfl, hs⟩
    exact ⟨φ, t, rfl, hs⟩

open Classical in
theorem main_correct (w : Word) :
    ∃ τ', HEval w (bound w) mainP (HSt.init M) τ' ∧
      τ'.out = [decide (w ∈ CTLStarTreeChecking)] := by
  have hB : w.length + 64 ≤ bound w := by
    unfold bound
    have : w.length ≤ (w.length + 2) ^ 3 := by
      calc w.length ≤ w.length + 2 := by omega
        _ = (w.length + 2) ^ 1 := by ring
        _ ≤ (w.length + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  suffices h : HAch w (bound w) mainP (HSt.init M)
      (fun τ' => τ'.out = [decide (w ∈ CTLStarTreeChecking)]) from h
  refine hach_seq ((hach_countP hB _).mono ?_)
  rintro σ ⟨hm, ho, hlt, hge, hle⟩
  refine hach_ite (bnd_eq' (bnd_tok' (by simp; omega)) (bnd_const' (by omega)) (by omega)) ?_
  simp only [ev_eq, ev_tok, ev_var, ev_const, ne_eq, bv_eq_zero, decide_eq_false_iff_not,
    not_not]
  have hm0 : σ.mem = ∅ := by rw [hm]; rfl
  have ho0 : σ.out = [] := by rw [ho]; rfl
  split_ifs with h29
  · obtain ⟨ts, hl, rfl⟩ := decode_eq hlt h29
    have hc : Ctx ts (encodeToks ts) (bound (encodeToks ts)) := by
      refine ⟨rtok_encode ts, ?_⟩
      unfold bound
      rw [encodeToks_length]
      have : ts.length + 2 ≤ 5 * ts.length + 2 := by omega
      have := Nat.pow_le_pow_left this 3
      omega
    refine (hach_main_tokens hc σ hl.symm hm0).mono ?_
    intro τ hτ
    rw [hτ, ho0]
    simp [mem_iff_decideCTL]
  · refine hach_out ?_
    rw [ho0]
    have h30 : rtok w (σ.v vN) = 30 := by have := rtok_le w (σ.v vN); omega
    have hnot : w ∉ CTLStarTreeChecking := by
      rintro ⟨φ, t, rfl, -⟩
      exact rtok_ne_30 _ h30
    simp [hnot]

end CTLP

end PathChecking
