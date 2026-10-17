module

public import RequestProject.ACRound.Gen.Params

/-!
# A token transducer copying a circuit with offsets

`GenC.stepTok` is a streaming transducer on token codes.  Run on the token codes of the
encoding of a circuit `CB`, it outputs the tokens of `CB.map (copyGate b0 g0)`
(`GenC.runToks_gates`).  It is implemented by a program of the loop language in
`RequestProject/ACRound/Gen/CopyProg.lean`; the arithmetic is clamped at a cap `C` exactly as in
that language.
-/

@[expose] public section

namespace PathChecking

namespace GenC

open LS

/-- State of the transducer. -/
structure CS where
  /-- inside an input gate -/
  mode : Bool
  /-- the current gate is an oracle gate -/
  orc : Bool
  /-- number being read -/
  num : ℕ
  /-- weight of the next digit -/
  pw : ℕ
  /-- index of the input gate being read -/
  inp : ℕ
  /-- number of gates read -/
  gc : ℕ

/-- The token with code `c` (`5 ≤ c < 29`). -/
def codeTok (c : ℕ) : Tok := if h : 5 ≤ c ∧ c < 29 then .tag ⟨c - 5, by omega⟩ else .zero

lemma codeTok_tag (k : Fin 24) : codeTok (Tok.tag k).code = .tag k := by
  have e : (Tok.tag k).code = k.val + 5 := by simp only [Tok.code]; omega
  unfold codeTok
  rw [dif_pos (by omega)]
  congr 1; ext; simp [e]

/-- One step of the transducer on the token code `c`. -/
def stepTok (C b0 g0 : ℕ) (s : CS) (c : ℕ) : CS × List Tok :=
  if c < 2 then
    ({s with num := if c = 1 then min (s.num + s.pw) C else s.num, pw := min (s.pw + s.pw) C}, [])
  else if c = 2 then
    if s.mode then ({s with inp := s.num, num := 0, pw := 1}, [])
    else ({s with num := 0, pw := 1}, natToks (min (b0 + s.num) C))
  else if c = 3 then
    (s, if s.mode then [] else Tok.lpar :: (if s.orc then natToks 0 else []))
  else if c = 4 then
    ({s with mode := false, gc := min (s.gc + 1) C},
      if s.mode then [Tok.tag 5, Tok.lpar] ++ natToks (min (g0 + s.inp) C) ++ [Tok.rpar]
      else [Tok.rpar])
  else if c = 5 then ({s with mode := true}, [])
  else ({s with mode := false, orc := decide (c = 11)}, [codeTok c])

/-- Running the transducer on a list of codes. -/
def runToks (C b0 g0 : ℕ) : CS → List ℕ → CS × List Tok
  | s, [] => (s, [])
  | s, c :: cs =>
    let r := stepTok C b0 g0 s c
    let r' := runToks C b0 g0 r.1 cs
    (r'.1, r.2 ++ r'.2)

lemma runToks_append (C b0 g0 : ℕ) (s : CS) (cs ds : List ℕ) :
    runToks C b0 g0 s (cs ++ ds) =
      ((runToks C b0 g0 (runToks C b0 g0 s cs).1 ds).1,
        (runToks C b0 g0 s cs).2 ++ (runToks C b0 g0 (runToks C b0 g0 s cs).1 ds).2) := by
  induction cs generalizing s with
  | nil => simp [runToks]
  | cons c cs ih => simp [runToks, ih]

lemma two_pow_bits_le (m : ℕ) : 2 ^ (Nat.bits m).length ≤ 2 * m + 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [LS.Nat.bits_of_ne_zero' m (by omega), List.length_cons, pow_succ]
      rcases Nat.eq_zero_or_pos (m / 2) with h0 | h0
      · rw [h0]; simp; omega
      · have := ih (m / 2) (by omega)
        have h2 : 2 ^ (Nat.bits (m / 2)).length ≤ 2 * (m / 2) := by
          rcases Nat.lt_or_ge (2 ^ (Nat.bits (m / 2)).length) (2 * (m / 2) + 1) with h | h
          · omega
          · have : 2 ^ (Nat.bits (m / 2)).length = 2 * (m / 2) + 1 := by omega
            have hev : 2 ∣ 2 ^ (Nat.bits (m / 2)).length := by
              have hl : (Nat.bits (m / 2)).length ≠ 0 := by
                rw [LS.Nat.bits_of_ne_zero' (m / 2) (by omega)]; simp
              exact dvd_pow_self 2 hl
            omega
        omega

/-- Reading the digits of a number. -/
lemma runToks_digits (C b0 g0 : ℕ) (m : ℕ) : ∀ (s : CS),
    s.num + s.pw * m ≤ C → s.pw * 2 ^ (Nat.bits m).length ≤ C →
    runToks C b0 g0 s ((Nat.bits m).map (Tok.code ∘ digitTok)) =
      ({s with num := s.num + s.pw * m, pw := s.pw * 2 ^ (Nat.bits m).length}, []) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro s h1 h2
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [runToks]
    · rw [LS.Nat.bits_of_ne_zero' m (by omega), List.map_cons]
      rw [LS.Nat.bits_of_ne_zero' m (by omega), List.length_cons, pow_succ] at h2
      have hd : (digitTok (decide (m % 2 = 1))).code < 2 := by
        unfold digitTok; split <;> simp [Tok.code]
      have hpos : 1 ≤ 2 ^ (Nat.bits (m / 2)).length := Nat.one_le_two_pow
      have hpw : s.pw + s.pw ≤ C := by nlinarith
      simp only [runToks, Function.comp_apply, stepTok, if_pos hd]
      set s' : CS := {s with
        num := (if (digitTok (decide (m % 2 = 1))).code = 1 then min (s.num + s.pw) C else s.num)
        pw := min (s.pw + s.pw) C}
      have hnum : s'.num = s.num + s.pw * (m % 2) := by
        simp only [s']
        by_cases hm2 : m % 2 = 1
        · simp only [hm2, decide_true, digitTok, if_true, Tok.code]
          rw [min_eq_left (by nlinarith)]; ring
        · have : m % 2 = 0 := by omega
          simp [this, digitTok, Tok.code]
      have hpw' : s'.pw = 2 * s.pw := by simp only [s']; rw [min_eq_left hpw]; ring
      have hm' : m = m % 2 + 2 * (m / 2) := by omega
      rw [ih (m / 2) (by omega) s' (by rw [hnum, hpw']; nlinarith)
        (by rw [hpw']; nlinarith)]
      simp only [List.nil_append, Prod.mk.injEq, and_true]
      rw [hnum, hpw']
      have e1 : s.num + s.pw * (m % 2) + 2 * s.pw * (m / 2) = s.num + s.pw * m := by
        conv_rhs => rw [hm']
        ring
      rw [e1, List.length_cons, pow_succ]
      simp only [s']
      congr 1
      ring

/-- Bounds needed to copy a gate. -/
def GateOk (C b0 g0 : ℕ) (g : Gate) : Prop :=
  (∀ i, g.kind = .input i → g.args = [] ∧ 2 * i + 2 ≤ C ∧ g0 + i ≤ C) ∧
    ∀ a ∈ g.args, 2 * a + 2 ≤ C ∧ b0 + a ≤ C

/-- A canonical state between gates. -/
def Canon (s : CS) : Prop := s.mode = false ∧ s.num = 0 ∧ s.pw = 1

lemma runToks_natToks (C b0 g0 : ℕ) (m : ℕ) (s : CS) (hs : s.num = 0) (hp : s.pw = 1)
    (hm : 2 * m + 2 ≤ C) :
    runToks C b0 g0 s ((natToks m).map Tok.code) =
      ({s with num := 0, pw := 1, inp := if s.mode then m else s.inp},
        if s.mode then [] else natToks (min (b0 + m) C)) := by
  rw [natToks_eq, List.map_append, List.map_map, runToks_append,
    runToks_digits C b0 g0 m s (by rw [hs, hp]; omega)
      (by rw [hp]; have := two_pow_bits_le m; omega)]
  have h2 : Tok.code .sep = 2 := rfl
  cases hmode : s.mode <;>
    simp [runToks, stepTok, h2, hs, hp]

lemma runToks_args (C b0 g0 : ℕ) (args : List ℕ) (s : CS) (hc : Canon s)
    (ha : ∀ a ∈ args, 2 * a + 2 ≤ C ∧ b0 + a ≤ C) :
    runToks C b0 g0 s ((args.flatMap natToks).map Tok.code) =
      (s, (args.map (b0 + ·)).flatMap natToks) := by
  induction args generalizing s with
  | nil => simp [runToks]
  | cons a args ih =>
    obtain ⟨h1, h2, h3⟩ := hc
    rw [List.flatMap_cons, List.map_append, runToks_append,
      runToks_natToks C b0 g0 a s h2 h3 (ha a (by simp)).1]
    have hs : ({s with num := 0, pw := 1, inp := if s.mode then a else s.inp} : CS) = s := by
      cases s; simp_all
    rw [hs, ih s ⟨h1, h2, h3⟩ (fun a' ha' => ha a' (by simp [ha']))]
    simp [h1, min_eq_left (ha a (by simp)).2]

/-- Copying one gate. -/
lemma runToks_gate (C b0 g0 : ℕ) (g : Gate) (s : CS) (hc : Canon s) (hg : GateOk C b0 g0 g)
    (hgc : s.gc + 1 ≤ C) :
    ∃ s', Canon s' ∧ s'.gc = s.gc + 1 ∧
      runToks C b0 g0 s (g.toks.map Tok.code) = (s', (Lay.copyGate b0 g0 g).toks) := by
  obtain ⟨hm, hn, hp⟩ := hc
  obtain ⟨hin, harg⟩ := hg
  have e3 : Tok.code .lpar = 3 := rfl
  have e4 : Tok.code .rpar = 4 := rfl
  -- the common tail `lpar args rpar`
  have tail : ∀ (s : CS), Canon s → s.gc + 1 ≤ C →
      runToks C b0 g0 s ((Tok.lpar :: (g.args.flatMap natToks ++ [Tok.rpar])).map Tok.code) =
        ({s with gc := s.gc + 1},
          Tok.lpar :: ((if s.orc then natToks 0 else []) ++
            ((g.args.map (b0 + ·)).flatMap natToks ++ [Tok.rpar]))) := by
    intro s hs hgc'
    obtain ⟨h1, h2, h3⟩ := hs
    rw [List.map_cons, List.map_append]
    simp only [runToks]
    simp only [stepTok, e3, show ¬ (3 < 2) by omega, show (3 = 2) = False by simp, if_false,
      if_true, h1, Bool.false_eq_true]
    rw [runToks_append, runToks_args C b0 g0 _ s ⟨h1, h2, h3⟩ harg]
    simp [runToks, stepTok, e4, h1, min_eq_left hgc']
  have tagCase : ∀ k : Fin 24, k.val ≠ 0 →
      g.toks = Tok.tag k :: (Tok.lpar :: (g.args.flatMap natToks ++ [Tok.rpar])) →
      (Lay.copyGate b0 g0 g).toks = Tok.tag k :: (Tok.lpar ::
        ((if k.val = 6 then natToks 0 else []) ++
          ((g.args.map (b0 + ·)).flatMap natToks ++ [Tok.rpar]))) →
      ∃ s', Canon s' ∧ s'.gc = s.gc + 1 ∧
        runToks C b0 g0 s (g.toks.map Tok.code) = (s', (Lay.copyGate b0 g0 g).toks) := by
    intro k hk0 ht hct
    have ek : (Tok.tag k).code = k.val + 5 := by simp [Tok.code]; omega
    refine ⟨{s with mode := false, orc := decide (k.val + 5 = 11), gc := s.gc + 1},
      ⟨rfl, hn, hp⟩, rfl, ?_⟩
    rw [ht, hct, List.map_cons]
    simp only [runToks, stepTok, ek]
    simp only [show ¬ (k.val + 5 < 2) by omega, show ¬ (k.val + 5 = 2) by omega,
      show ¬ (k.val + 5 = 3) by omega, show ¬ (k.val + 5 = 4) by omega,
      show ¬ (k.val + 5 = 5) by omega, if_false]
    rw [tail {s with mode := false, orc := decide (k.val + 5 = 11)} ⟨rfl, hn, hp⟩ hgc]
    have : codeTok (k.val + 5) = Tok.tag k := by rw [← ek]; exact codeTok_tag k
    simp [this, show (k.val + 5 = 11) ↔ k.val = 6 by omega]
  rcases hk : g.kind with i | b | _ | _ | _ | _
  · -- input gate
    obtain ⟨hargs, hi1, hi2⟩ := hin i hk
    have ht : g.toks = Tok.tag 0 :: (natToks i ++ Tok.lpar :: ([] ++ [Tok.rpar])) := by
      simp [Gate.toks, hk, hargs]
    rw [ht]
    have e5 : (Tok.tag 0).code = 5 := rfl
    simp only [List.map_cons, List.map_append, runToks, stepTok, e5]
    simp only [show ¬ (5 < 2) by omega, show ¬ (5 = 2) by omega, show ¬ (5 = 3) by omega,
      show ¬ (5 = 4) by omega, if_false, if_true]
    rw [runToks_append, runToks_natToks C b0 g0 i {s with mode := true} hn hp hi1]
    refine ⟨{s with mode := false, num := 0, pw := 1, inp := i, gc := s.gc + 1},
      ⟨rfl, rfl, rfl⟩, rfl, ?_⟩
    simp [runToks, stepTok, e3, e4, min_eq_left hgc, min_eq_left hi2, Lay.copyGate, hk,
      Gate.toks]
  · cases b
    · exact tagCase 1 (by decide) (by simp [Gate.toks, hk]) (by simp [Lay.copyGate, hk, Gate.toks])
    · exact tagCase 2 (by decide) (by simp [Gate.toks, hk]) (by simp [Lay.copyGate, hk, Gate.toks])
  · exact tagCase 3 (by decide) (by simp [Gate.toks, hk]) (by simp [Lay.copyGate, hk, Gate.toks])
  · exact tagCase 4 (by decide) (by simp [Gate.toks, hk]) (by simp [Lay.copyGate, hk, Gate.toks])
  · exact tagCase 5 (by decide) (by simp [Gate.toks, hk]) (by simp [Lay.copyGate, hk, Gate.toks])
  · exact tagCase 6 (by decide) (by simp [Gate.toks, hk])
      (by simp [Lay.copyGate, hk, Gate.toks])


/-- **Copying a list of gates.** -/
lemma runToks_gates (C b0 g0 : ℕ) (gs : List Gate) (s : CS) (hc : Canon s)
    (hg : ∀ g ∈ gs, GateOk C b0 g0 g) (hgc : s.gc + gs.length ≤ C) :
    ∃ s', Canon s' ∧ s'.gc = s.gc + gs.length ∧
      runToks C b0 g0 s ((gs.flatMap Gate.toks).map Tok.code) =
        (s', gs.flatMap fun g => (Lay.copyGate b0 g0 g).toks) := by
  induction gs generalizing s with
  | nil => exact ⟨s, hc, rfl, by simp [runToks]⟩
  | cons g gs ih =>
    obtain ⟨s1, hc1, hgc1, h1⟩ := runToks_gate C b0 g0 g s hc (hg g (by simp))
      (by simp at hgc; omega)
    obtain ⟨s2, hc2, hgc2, h2⟩ := ih s1 hc1 (fun g' hg' => hg g' (by simp [hg']))
      (by simp at hgc; omega)
    refine ⟨s2, hc2, by simp [hgc2, hgc1]; omega, ?_⟩
    rw [List.flatMap_cons, List.map_append, runToks_append, h1, h2]
    simp

end GenC

end PathChecking
