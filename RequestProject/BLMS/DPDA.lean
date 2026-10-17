module

public import RequestProject.BLMS.Algo
public import RequestProject.Complexity

/-!
# The pushdown automaton of the algorithm

A fixed deterministic pushdown automaton `PD.pda` that runs the code machine of
`RequestProject/BLMS/Algo.lean` when the input contains the table of the machine.

The input is a word over the symbols `X, S, E1, E2, E3, A, R` (`PD.Sym`), each encoded by the
prefix code `1^k 0`.  The stack holds a list of codes `[c₀, c₁, …]` as `x^{c₀} # x^{c₁} # … ⊥`.
A *round* lists, for every code `cJ < M` (row) and every code `cI < M` (entry), the action of the
machine on top codes `cJ, cI`: `A` (accept), `R` (reject) or a script `S x^{k₁} S x^{k₂} …` of codes
to push; entries end with `E1`, rows with `E2`, and the round with `E3`.

In a round the automaton pops the `x`s of `cJ` while skipping rows, then the `x`s of `cI` while
skipping entries, and then executes the selected entry; afterwards it skips to the end of the
round.  So each round performs one step of the code machine (`PD.accepts_iff`).
-/

@[expose] public section

namespace PathChecking

namespace BLMS

namespace PD

open LC (TRes MRes)

/-- Phases of the automaton. -/
inductive Ph
  | skJ
  | skI
  | row
  | ent
  | rest
  | exec
  | acc
  | rej
  deriving DecidableEq, Fintype

/-- Stack symbols. -/
inductive SS
  | x
  | sep
  | bot
  deriving DecidableEq, Fintype

/-- Input symbols. -/
inductive Sym
  | X
  | S
  | E1
  | E2
  | E3
  | A
  | R
  deriving DecidableEq

/-- The number of `1`s of the code of a symbol. -/
def Sym.code : Sym → ℕ
  | .X => 0
  | .S => 1
  | .E1 => 2
  | .E2 => 3
  | .E3 => 4
  | .A => 5
  | .R => 6

/-- Binary code of a symbol. -/
def Sym.bits (s : Sym) : Word := List.replicate s.code true ++ [false]

/-- Binary code of a word of symbols. -/
def wordOf (u : List Sym) : Word := u.flatMap Sym.bits

/-- Processing a complete symbol (with `k` ones) in a reading phase. -/
def proc : Ph → ℕ → SS → (Ph × Fin 7) × List SS
  | .row, k, Z => (if k = 3 then (.skJ, 0) else (.row, 0), [Z])
  | .ent, k, Z => (if k = 2 then (.skI, 0) else (.ent, 0), [Z])
  | .rest, k, Z => (if k = 4 then (.skJ, 0) else (.rest, 0), [Z])
  | .exec, k, Z =>
    if k = 0 then ((.exec, 0), [.x, Z])
    else if k = 1 then ((.exec, 0), [.sep, Z])
    else if k = 2 then ((.rest, 0), [Z])
    else if k = 5 then ((.acc, 0), [Z])
    else ((.rej, 0), [Z])
  | .acc, _, Z => ((.acc, 0), [Z])
  | _, _, Z => ((.rej, 0), [Z])

/-- Popping phases. -/
def popT : Ph → SS → (Ph × Fin 7) × List SS
  | .skJ, .x => ((.row, 0), [])
  | .skJ, .sep => ((.skI, 0), [])
  | .skI, .x => ((.ent, 0), [])
  | .skI, .sep => ((.exec, 0), [])
  | _, Z => ((.rej, 0), [Z])

/-- Phases with ε-moves. -/
def isPop : Ph → Bool
  | .skJ => true
  | .skI => true
  | _ => false

/-- The transition function. -/
def tr (q : Ph × Fin 7) (a : Option Bool) (Z : SS) : Option ((Ph × Fin 7) × List SS) :=
  if isPop q.1 then (if a.isNone then some (popT q.1 Z) else none)
  else match a with
    | none => none
    | some true => if h : q.2.val + 1 < 7 then some ((q.1, ⟨q.2.val + 1, h⟩), [Z]) else none
    | some false => some (proc q.1 q.2.val Z)

/-- The automaton. -/
def pda : DPDA where
  Q := Ph × Fin 7
  S := SS
  start := (.exec, 0)
  bottom := .bot
  accept := {q | q.1 = .acc}
  δ := tr
  deterministic := by
    intro q Z h a
    unfold tr at h ⊢
    by_cases hp : isPop q.1 = true
    · simp [hp]
    · simp only [hp, Bool.false_eq_true, if_false] at h
      simp at h

/-- Reachability. -/
abbrev Reach (c d : pda.Cfg) : Prop := Relation.ReflTransGen pda.Step c d

/-- Stack encoding of a list of codes. -/
def enc : List ℕ → List SS
  | [] => [.bot]
  | k :: l => List.replicate k .x ++ .sep :: enc l

lemma enc_ne_nil (l : List ℕ) : ∃ Z γ, enc l = Z :: γ := by
  rcases l with _ | ⟨k, l⟩
  · exact ⟨_, _, rfl⟩
  · rcases k with _ | k
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩

lemma rep_ne_nil (n : ℕ) (τ : List SS) : ∃ Z γ, List.replicate n SS.x ++ SS.sep :: τ = Z :: γ := by
  rcases n with _ | n
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

@[simp] lemma wordOf_nil : wordOf [] = [] := rfl

lemma wordOf_cons (s : Sym) (u : List Sym) : wordOf (s :: u) = s.bits ++ wordOf u := rfl

lemma wordOf_append (u v : List Sym) : wordOf (u ++ v) = wordOf u ++ wordOf v := by
  simp [wordOf]

/-! ## Basic moves -/

lemma read_ones {ph : Ph} (hph : isPop ph = false) (Z : SS) (γ : List SS) (w : Word) :
    ∀ j k (hk : k + j < 7), Reach ⟨(ph, ⟨k, by omega⟩), List.replicate j true ++ w, Z :: γ⟩
      ⟨(ph, ⟨k + j, hk⟩), w, Z :: γ⟩ := by
  intro j
  induction j with
  | zero => intro k hk; exact Relation.ReflTransGen.refl
  | succ j ih =>
    intro k hk
    refine Relation.ReflTransGen.head ?_ (by
      have := ih (k + 1) (by omega)
      simp only [show k + 1 + j = k + (j + 1) by omega] at this
      exact this)
    have : pda.δ (ph, ⟨k, by omega⟩) (some true) Z = some ((ph, ⟨k + 1, by omega⟩), [Z]) := by
      simp [pda, tr, hph, show k + 1 < 7 by omega]
    simpa using DPDA.Step.read (M := pda) (w := List.replicate j true ++ w) (γ := γ) this

lemma read_sym {ph : Ph} (hph : isPop ph = false) (s : Sym) (Z : SS) (γ : List SS) (w : Word) :
    Reach ⟨(ph, 0), s.bits ++ w, Z :: γ⟩
      ⟨(proc ph s.code Z).1, w, (proc ph s.code Z).2 ++ γ⟩ := by
  have hs : s.code < 7 := by cases s <;> simp [Sym.code]
  have h1 := read_ones hph Z γ (false :: w) s.code 0 (by omega)
  simp only [Nat.zero_add] at h1
  refine Relation.ReflTransGen.tail (by simpa [Sym.bits] using h1) ?_
  have : pda.δ (ph, ⟨s.code, hs⟩) (some false) Z = some (proc ph s.code Z) := by
    simp [pda, tr, hph]
  exact DPDA.Step.read this

lemma pop_step {ph : Ph} (hph : isPop ph = true) (k : Fin 7) (Z : SS) (γ : List SS) (w : Word) :
    pda.Step ⟨(ph, k), w, Z :: γ⟩ ⟨(popT ph Z).1, w, (popT ph Z).2 ++ γ⟩ := by
  have : pda.δ (ph, k) none Z = some (popT ph Z) := by simp [pda, tr, hph]
  exact DPDA.Step.eps this

/-- Skipping symbols up to a terminator. -/
lemma skip_gen {ph : Ph} (hph : isPop ph = false) (t : Sym) (q' : Ph × Fin 7)
    (hstay : ∀ s : Sym, s ≠ t → ∀ Z, proc ph s.code Z = ((ph, 0), [Z]))
    (hend : ∀ Z, proc ph t.code Z = (q', [Z])) (Z : SS) (γ : List SS) (v : List Sym) :
    ∀ u : List Sym, t ∉ u → Reach ⟨(ph, 0), wordOf (u ++ t :: v), Z :: γ⟩ ⟨q', wordOf v, Z :: γ⟩ := by
  intro u
  induction u with
  | nil =>
    intro _
    have := read_sym hph t Z γ (wordOf v)
    rw [hend] at this
    simpa [wordOf_cons] using this
  | cons s u ih =>
    intro hu
    have hs : s ≠ t := fun h => hu (h ▸ List.mem_cons_self)
    have h1 := read_sym hph s Z γ (wordOf (u ++ t :: v))
    rw [hstay s hs] at h1
    rw [List.cons_append, wordOf_cons]
    exact h1.trans (ih (fun h => hu (List.mem_cons_of_mem _ h)))

lemma sink_acc (Z : SS) (γ : List SS) :
    ∀ u : List Sym, Reach ⟨(.acc, 0), wordOf u, Z :: γ⟩ ⟨(.acc, 0), [], Z :: γ⟩ := by
  intro u
  induction u with
  | nil => exact Relation.ReflTransGen.refl
  | cons s u ih =>
    have h1 := read_sym (ph := .acc) rfl s Z γ (wordOf u)
    simp only [proc] at h1
    rw [wordOf_cons]
    exact h1.trans ih

lemma sink_rej (Z : SS) (γ : List SS) :
    ∀ u : List Sym, Reach ⟨(.rej, 0), wordOf u, Z :: γ⟩ ⟨(.rej, 0), [], Z :: γ⟩ := by
  intro u
  induction u with
  | nil => exact Relation.ReflTransGen.refl
  | cons s u ih =>
    have h1 := read_sym (ph := .rej) rfl s Z γ (wordOf u)
    simp only [proc] at h1
    rw [wordOf_cons]
    exact h1.trans ih

/-! ## Rounds -/

/-- Entries of the table. -/
def entry : TRes → List Sym
  | .acc => [.A]
  | .rej => [.R]
  | .scr s => s.flatMap (fun k => .S :: List.replicate k .X)

/-- A row of the table. -/
def rowSyms (tabF : ℕ → ℕ → TRes) (M cJ : ℕ) : List Sym :=
  (List.range M).flatMap (fun cI => entry (tabF cI cJ) ++ [.E1])

/-- A round: the whole table. -/
def round (tabF : ℕ → ℕ → TRes) (M : ℕ) : List Sym :=
  (List.range M).flatMap (fun cJ => rowSyms tabF M cJ ++ [.E2]) ++ [.E3]

/-- The generic code machine (as `LC.mstep`). -/
def gstep (tabF : ℕ → ℕ → TRes) : List ℕ → MRes
  | cJ :: cI :: rest =>
    match tabF cI cJ with
    | .acc => .acc
    | .rej => .rej
    | .scr s => .cont (s.reverse ++ rest)
  | _ => .rej

/-- Iteration of `gstep`. -/
def grun (tabF : ℕ → ℕ → TRes) : ℕ → MRes → MRes
  | 0, r => r
  | k + 1, .cont l => grun tabF k (gstep tabF l)
  | _ + 1, r => r

lemma skip_rows (τ : List SS) (v : List Sym) :
    ∀ bs : List (List Sym), (∀ b ∈ bs, Sym.E2 ∉ b) →
      Reach ⟨(.skJ, 0), wordOf (bs.flatMap (· ++ [.E2]) ++ v), List.replicate bs.length .x ++
        .sep :: τ⟩ ⟨(.skI, 0), wordOf v, τ⟩ := by
  intro bs
  induction bs with
  | nil =>
    intro _
    exact Relation.ReflTransGen.single (by simpa using pop_step (ph := .skJ) rfl 0 .sep τ _)
  | cons b bs ih =>
    intro hb
    refine Relation.ReflTransGen.head (by
      simpa [List.replicate_succ] using pop_step (ph := .skJ) rfl 0 .x
        (List.replicate bs.length .x ++ .sep :: τ) _) ?_
    obtain ⟨Z, γ, e⟩ := rep_ne_nil bs.length τ
    show Reach ⟨(.row, 0), wordOf (b ++ Sym.E2 :: (List.flatMap (fun x => x ++ [Sym.E2]) bs ++ v)),
      List.replicate bs.length SS.x ++ SS.sep :: τ⟩ _
    rw [e]
    refine (skip_gen (ph := .row) rfl .E2 (.skJ, 0) (fun s hs Z => ?_) (fun Z => rfl) Z γ _ b
      (hb b List.mem_cons_self)).trans ?_
    · cases s <;> simp_all [proc, Sym.code]
    · rw [← e]
      exact ih (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb'))

lemma skip_ents (τ : List SS) (v : List Sym) :
    ∀ bs : List (List Sym), (∀ b ∈ bs, Sym.E1 ∉ b) →
      Reach ⟨(.skI, 0), wordOf (bs.flatMap (· ++ [.E1]) ++ v), List.replicate bs.length .x ++
        .sep :: τ⟩ ⟨(.exec, 0), wordOf v, τ⟩ := by
  intro bs
  induction bs with
  | nil =>
    intro _
    exact Relation.ReflTransGen.single (by simpa using pop_step (ph := .skI) rfl 0 .sep τ _)
  | cons b bs ih =>
    intro hb
    refine Relation.ReflTransGen.head (by
      simpa [List.replicate_succ] using pop_step (ph := .skI) rfl 0 .x
        (List.replicate bs.length .x ++ .sep :: τ) _) ?_
    obtain ⟨Z, γ, e⟩ := rep_ne_nil bs.length τ
    show Reach ⟨(.ent, 0), wordOf (b ++ Sym.E1 :: (List.flatMap (fun x => x ++ [Sym.E1]) bs ++ v)),
      List.replicate bs.length SS.x ++ SS.sep :: τ⟩ _
    rw [e]
    refine (skip_gen (ph := .ent) rfl .E1 (.skI, 0) (fun s hs Z => ?_) (fun Z => rfl) Z γ _ b
      (hb b List.mem_cons_self)).trans ?_
    · cases s <;> simp_all [proc, Sym.code]
    · rw [← e]
      exact ih (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb'))

lemma exec_xs (v : List Sym) :
    ∀ k (σ : List SS), σ ≠ [] → Reach ⟨(.exec, 0), wordOf (List.replicate k .X ++ v), σ⟩
      ⟨(.exec, 0), wordOf v, List.replicate k .x ++ σ⟩ := by
  intro k
  induction k with
  | zero => intro σ _; exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro σ hσ
    obtain ⟨Z, γ, rfl⟩ := List.exists_cons_of_ne_nil hσ
    have h1 := read_sym (ph := .exec) rfl .X Z γ (wordOf (List.replicate k .X ++ v))
    simp only [proc, Sym.code, if_true] at h1
    rw [List.replicate_succ, List.cons_append, wordOf_cons]
    refine h1.trans ?_
    have := ih (.x :: Z :: γ) (by simp)
    rwa [List.replicate_succ', List.append_assoc, List.singleton_append]

lemma exec_script (v : List Sym) :
    ∀ (s rest : List ℕ), Reach ⟨(.exec, 0), wordOf (entry (.scr s) ++ v), enc rest⟩
      ⟨(.exec, 0), wordOf v, enc (s.reverse ++ rest)⟩ := by
  intro s
  induction s with
  | nil => intro rest; simpa [entry] using Relation.ReflTransGen.refl
  | cons k s ih =>
    intro rest
    obtain ⟨Z, γ, e⟩ := enc_ne_nil rest
    have h1 := read_sym (ph := .exec) rfl .S Z γ
      (wordOf (List.replicate k .X ++ (entry (.scr s) ++ v)))
    simp only [proc, Sym.code] at h1
    have e2 : entry (.scr (k :: s)) ++ v = .S :: (List.replicate k .X ++ (entry (.scr s) ++ v)) := by
      simp [entry]
    rw [e2, wordOf_cons, e]
    refine h1.trans ?_
    have h2 := exec_xs (entry (.scr s) ++ v) k (.sep :: Z :: γ) (by simp)
    refine h2.trans ?_
    have := ih (k :: rest)
    simp only [enc] at this
    rw [e] at this
    simpa using this

lemma range_split {c M : ℕ} (h : c < M) :
    List.range M = List.range c ++ c :: List.range' (c + 1) (M - c - 1) := by
  rw [List.range_eq_range', List.range_eq_range']
  have : M = c + (1 + (M - c - 1)) := by omega
  conv_lhs => rw [this]
  rw [← List.range'_append, ← List.range'_append]
  simp

lemma mem_entry {s : Sym} {t : TRes} (h : s ∈ entry t) :
    s = .X ∨ s = .S ∨ s = .A ∨ s = .R := by
  rcases t with _ | _ | l
  · simp [entry] at h; simp [h]
  · simp [entry] at h; simp [h]
  · simp only [entry, List.mem_flatMap, List.mem_cons, List.mem_replicate] at h
    obtain ⟨_, _, h | ⟨_, h⟩⟩ := h <;> simp [h]

lemma E1_not_mem_entry (t : TRes) : Sym.E1 ∉ entry t := fun h => by
  rcases mem_entry h with h | h | h | h <;> cases h

lemma not_mem_rowSyms {s : Sym} (hs : s = .E2 ∨ s = .E3) (tabF : ℕ → ℕ → TRes) (M c : ℕ) :
    s ∉ rowSyms tabF M c := by
  intro h
  simp only [rowSyms, List.mem_flatMap, List.mem_append, List.mem_singleton] at h
  obtain ⟨_, _, h | h⟩ := h
  · rcases mem_entry h with h' | h' | h' | h' <;> subst h' <;> simp at hs
  · subst h; simp at hs

variable (tabF : ℕ → ℕ → TRes) (M : ℕ)

lemma round_to_exec {cJ cI : ℕ} (hJ : cJ < M) (hI : cI < M) (rest : List ℕ) (u : List Sym) :
    ∃ V, Sym.E3 ∉ V ∧ Reach ⟨(.skJ, 0), wordOf (round tabF M ++ u), enc (cJ :: cI :: rest)⟩
      ⟨(.exec, 0), wordOf (entry (tabF cI cJ) ++ .E1 :: (V ++ .E3 :: u)), enc rest⟩ := by
  set tailR := (List.range' (cJ + 1) (M - cJ - 1)).flatMap (fun c => rowSyms tabF M c ++ [.E2])
  set tailE := (List.range' (cI + 1) (M - cI - 1)).flatMap
    (fun c => entry (tabF c cJ) ++ [.E1])
  refine ⟨tailE ++ .E2 :: tailR, ?_, ?_⟩
  · simp only [List.mem_append, List.mem_cons, tailE, tailR, List.mem_flatMap,
      not_or]
    refine ⟨?_, by simp, ?_⟩
    · rintro ⟨c, -, h⟩
      rcases h with h | h
      · rcases mem_entry h with h' | h' | h' | h' <;> cases h'
      · simp at h
    · rintro ⟨c, -, h⟩
      rcases h with h | h
      · exact not_mem_rowSyms (Or.inr rfl) tabF M c h
      · simp at h
  have e1 : round tabF M ++ u = ((List.range cJ).map (rowSyms tabF M)).flatMap (· ++ [.E2]) ++
      (rowSyms tabF M cJ ++ .E2 :: (tailR ++ .E3 :: u)) := by
    simp only [round, range_split hJ, List.flatMap_append, List.flatMap_cons, List.flatMap_map,
      tailR, List.append_assoc, List.cons_append, List.nil_append]
  have e2 : rowSyms tabF M cJ ++ .E2 :: (tailR ++ .E3 :: u) =
      ((List.range cI).map (fun c => entry (tabF c cJ))).flatMap (· ++ [.E1]) ++
      (entry (tabF cI cJ) ++ .E1 :: ((tailE ++ .E2 :: tailR) ++ .E3 :: u)) := by
    simp only [rowSyms, range_split hI, List.flatMap_append, List.flatMap_cons, List.flatMap_map,
      tailE, List.append_assoc, List.cons_append, List.nil_append]
  rw [e1]
  have h1 := skip_rows (enc (cI :: rest)) (rowSyms tabF M cJ ++ .E2 :: (tailR ++ .E3 :: u))
    ((List.range cJ).map (rowSyms tabF M)) (by
      intro b hb
      simp only [List.mem_map, List.mem_range] at hb
      obtain ⟨c, -, rfl⟩ := hb
      exact not_mem_rowSyms (Or.inl rfl) tabF M c)
  simp only [List.length_map, List.length_range] at h1
  refine h1.trans ?_
  rw [e2]
  have h2 := skip_ents (enc rest) (entry (tabF cI cJ) ++ .E1 :: ((tailE ++ .E2 :: tailR) ++ .E3 :: u))
    ((List.range cI).map (fun c => entry (tabF c cJ))) (by
      intro b hb
      simp only [List.mem_map, List.mem_range] at hb
      obtain ⟨c, -, rfl⟩ := hb
      exact E1_not_mem_entry _)
  simp only [List.length_map, List.length_range] at h2
  exact h2

lemma round_scr {cJ cI : ℕ} (hJ : cJ < M) (hI : cI < M) (rest : List ℕ) (u : List Sym)
    {s : List ℕ} (hs : tabF cI cJ = .scr s) :
    Reach ⟨(.skJ, 0), wordOf (round tabF M ++ u), enc (cJ :: cI :: rest)⟩
      ⟨(.skJ, 0), wordOf u, enc (s.reverse ++ rest)⟩ := by
  obtain ⟨V, hV, h1⟩ := round_to_exec tabF M hJ hI rest u
  refine h1.trans ?_
  rw [hs]
  refine (exec_script _ s rest).trans ?_
  obtain ⟨Z, γ, e⟩ := enc_ne_nil (s.reverse ++ rest)
  rw [e, wordOf_cons]
  have h2 := read_sym (ph := .exec) rfl .E1 Z γ (wordOf (V ++ .E3 :: u))
  simp only [proc, Sym.code] at h2
  refine h2.trans ?_
  exact skip_gen (ph := .rest) rfl .E3 (.skJ, 0) (fun s hs Z => by
    cases s <;> simp_all [proc, Sym.code]) (fun Z => rfl) Z γ u V hV

lemma round_acc {cJ cI : ℕ} (hJ : cJ < M) (hI : cI < M) (rest : List ℕ) (u : List Sym)
    (hs : tabF cI cJ = .acc) :
    ∃ γ, Reach ⟨(.skJ, 0), wordOf (round tabF M ++ u), enc (cJ :: cI :: rest)⟩
      ⟨(.acc, 0), [], γ⟩ := by
  obtain ⟨V, hV, h1⟩ := round_to_exec tabF M hJ hI rest u
  obtain ⟨Z, γ, e⟩ := enc_ne_nil rest
  refine ⟨Z :: γ, h1.trans ?_⟩
  rw [hs, e]
  simp only [entry, List.singleton_append, wordOf_cons]
  have h2 := read_sym (ph := .exec) rfl .A Z γ (wordOf (.E1 :: (V ++ .E3 :: u)))
  simp only [proc, Sym.code] at h2
  rw [← wordOf_cons]
  exact h2.trans (sink_acc Z γ _)

lemma round_rej {cJ cI : ℕ} (hJ : cJ < M) (hI : cI < M) (rest : List ℕ) (u : List Sym)
    (hs : tabF cI cJ = .rej) :
    ∃ γ, Reach ⟨(.skJ, 0), wordOf (round tabF M ++ u), enc (cJ :: cI :: rest)⟩
      ⟨(.rej, 0), [], γ⟩ := by
  obtain ⟨V, hV, h1⟩ := round_to_exec tabF M hJ hI rest u
  obtain ⟨Z, γ, e⟩ := enc_ne_nil rest
  refine ⟨Z :: γ, h1.trans ?_⟩
  rw [hs, e]
  simp only [entry, List.singleton_append, wordOf_cons]
  have h2 := read_sym (ph := .exec) rfl .R Z γ (wordOf (.E1 :: (V ++ .E3 :: u)))
  simp only [proc, Sym.code] at h2
  rw [← wordOf_cons]
  exact h2.trans (sink_rej Z γ _)

lemma round_short (l : List ℕ) (hl : l.length < 2) (hlt : ∀ c ∈ l, c < M) (u : List Sym) :
    ∃ γ, Reach ⟨(.skJ, 0), wordOf (round tabF M ++ u), enc l⟩ ⟨(.rej, 0), [], γ⟩ := by
  rcases l with _ | ⟨cJ, _ | ⟨_, _⟩⟩
  · refine ⟨[.bot], Relation.ReflTransGen.head (pop_step (ph := .skJ) rfl 0 .bot [] _) ?_⟩
    exact sink_rej .bot [] _
  · have hJ := hlt cJ List.mem_cons_self
    have e1 : round tabF M ++ u = ((List.range cJ).map (rowSyms tabF M)).flatMap (· ++ [.E2]) ++
        (rowSyms tabF M cJ ++ .E2 :: ((List.range' (cJ + 1) (M - cJ - 1)).flatMap
          (fun c => rowSyms tabF M c ++ [.E2]) ++ .E3 :: u)) := by
      simp only [round, range_split hJ, List.flatMap_append, List.flatMap_cons, List.flatMap_map,
        List.append_assoc, List.cons_append, List.nil_append]
    rw [e1]
    have h1 := skip_rows (enc []) (rowSyms tabF M cJ ++ .E2 :: ((List.range' (cJ + 1) (M - cJ - 1)).flatMap
          (fun c => rowSyms tabF M c ++ [.E2]) ++ .E3 :: u)) ((List.range cJ).map (rowSyms tabF M)) (by
        intro b hb
        simp only [List.mem_map, List.mem_range] at hb
        obtain ⟨c, -, rfl⟩ := hb
        exact not_mem_rowSyms (Or.inl rfl) tabF M c)
    simp only [List.length_map, List.length_range] at h1
    refine ⟨[.bot], h1.trans (Relation.ReflTransGen.head
      (pop_step (ph := .skI) rfl 0 .bot [] _) ?_)⟩
    exact sink_rej .bot [] _
  · simp only [List.length_cons] at hl; omega

lemma grun_acc' (k : ℕ) : grun tabF k .acc = .acc := by cases k <;> rfl
lemma grun_rej' (k : ℕ) : grun tabF k .rej = .rej := by cases k <;> rfl

lemma grun_sim (htab : ∀ cI cJ, cI < M → cJ < M → ∀ s, tabF cI cJ = .scr s → ∀ k ∈ s, k < M) :
    ∀ k (l : List ℕ) (u : List Sym), (∀ c ∈ l, c < M) →
      (grun tabF k (.cont l) = .acc → ∃ γ, Reach ⟨(.skJ, 0),
        wordOf ((List.replicate k (round tabF M)).flatten ++ u), enc l⟩ ⟨(.acc, 0), [], γ⟩) ∧
      (grun tabF k (.cont l) = .rej → ∃ γ, Reach ⟨(.skJ, 0),
        wordOf ((List.replicate k (round tabF M)).flatten ++ u), enc l⟩ ⟨(.rej, 0), [], γ⟩) := by
  intro k
  induction k with
  | zero => intro l u _; exact ⟨fun h => (by cases h), fun h => by cases h⟩
  | succ k ih =>
    intro l u hl
    simp only [grun, List.replicate_succ, List.flatten_cons, List.append_assoc]
    rcases l with _ | ⟨cJ, _ | ⟨cI, rest⟩⟩
    · simp only [gstep, grun_rej']
      exact ⟨fun h => (by cases h), fun _ => round_short tabF M [] (by simp) hl _⟩
    · simp only [gstep, grun_rej']
      exact ⟨fun h => (by cases h), fun _ => round_short tabF M [cJ] (by simp) hl _⟩
    · have hJ := hl cJ (by simp)
      have hI := hl cI (by simp)
      simp only [gstep]
      rcases ht : tabF cI cJ with _ | _ | s
      · simp only [grun_acc']
        exact ⟨fun _ => round_acc tabF M hJ hI rest _ ht, fun h => by cases h⟩
      · simp only [grun_rej']
        exact ⟨fun h => (by cases h), fun _ => round_rej tabF M hJ hI rest _ ht⟩
      · have hs' : ∀ c ∈ s.reverse ++ rest, c < M := by
          intro c hc
          rcases List.mem_append.1 hc with hc | hc
          · exact htab cI cJ hI hJ s ht c (List.mem_reverse.1 hc)
          · exact hl c (by simp [hc])
        have h1 := round_scr tabF M hJ hI rest
          ((List.replicate k (round tabF M)).flatten ++ u) ht
        obtain ⟨ia, ir⟩ := ih (s.reverse ++ rest) u hs'
        exact ⟨fun h => (ia h).imp fun _ h' => h1.trans h',
          fun h => (ir h).imp fun _ h' => h1.trans h'⟩

/-! ## Determinism -/

lemma step_det {c d₁ d₂ : pda.Cfg} (h₁ : pda.Step c d₁) (h₂ : pda.Step c d₂) : d₁ = d₂ := by
  cases h₁ with
  | read hδ₁ =>
    cases h₂ with
    | read hδ₂ => rw [hδ₁] at hδ₂; cases hδ₂; rfl
    | eps hδ₂ =>
      have := pda.deterministic _ _ (by rw [hδ₂]; rfl)
      rw [this] at hδ₁; cases hδ₁
  | eps hδ₁ =>
    cases h₂ with
    | read hδ₂ =>
      have := pda.deterministic _ _ (by rw [hδ₁]; rfl)
      rw [this] at hδ₂; cases hδ₂
    | eps hδ₂ => rw [hδ₁] at hδ₂; cases hδ₂; rfl

lemma no_step {ph : Ph} (hph : isPop ph = false) (k : Fin 7) (γ : List SS) (d : pda.Cfg) :
    ¬ pda.Step ⟨(ph, k), [], γ⟩ d := by
  intro h
  cases h with
  | eps hδ =>
    change tr (ph, k) none _ = _ at hδ
    simp [tr, hph] at hδ

lemma reach_terminal {ph : Ph} (hph : isPop ph = false) {k : Fin 7} {γ : List SS} {d : pda.Cfg}
    (h : Reach ⟨(ph, k), [], γ⟩ d) : d = ⟨(ph, k), [], γ⟩ := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hs, -⟩
  · exact h.symm
  · exact absurd hs (no_step hph k γ c)

/-- **The automaton runs the code machine.** -/
theorem accepts_iff (htab : ∀ cI cJ, cI < M → cJ < M → ∀ s, tabF cI cJ = .scr s → ∀ k ∈ s, k < M)
    {a b : ℕ} (ha : a < M) (hb : b < M) (T : ℕ)
    (hT : grun tabF T (.cont [b, a]) = .acc ∨ grun tabF T (.cont [b, a]) = .rej) :
    pda.Accepts (wordOf (entry (.scr [a, b]) ++ .E1 :: .E3 ::
      (List.replicate T (round tabF M)).flatten)) ↔ grun tabF T (.cont [b, a]) = .acc := by
  have hinit : Reach ⟨(.exec, 0), wordOf (entry (.scr [a, b]) ++ .E1 :: .E3 ::
      (List.replicate T (round tabF M)).flatten), [.bot]⟩
      ⟨(.skJ, 0), wordOf ((List.replicate T (round tabF M)).flatten ++ []), enc [b, a]⟩ := by
    refine (exec_script _ [a, b] []).trans ?_
    obtain ⟨Z, γ, e⟩ := enc_ne_nil [b, a]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_nil]
    rw [e, wordOf_cons]
    have h2 := read_sym (ph := .exec) rfl .E1 Z γ (wordOf (.E3 ::
      (List.replicate T (round tabF M)).flatten))
    simp only [proc, Sym.code] at h2
    refine h2.trans ?_
    rw [wordOf_cons]
    have h3 := read_sym (ph := .rest) rfl .E3 Z γ (wordOf
      (List.replicate T (round tabF M)).flatten)
    simpa [proc, Sym.code] using h3
  obtain ⟨ia, ir⟩ := grun_sim tabF M htab T [b, a] [] (by simp [ha, hb])
  constructor
  · intro hacc
    rcases hT with h | h
    · exact h
    exfalso
    obtain ⟨γ, hr⟩ := ir h
    obtain ⟨q, γ', hq, hacc⟩ := hacc
    have hr' := hinit.trans hr
    rcases Relation.ReflTransGen.total_of_right_unique (r := pda.Step)
      (fun _ _ _ h1 h2 => step_det h1 h2) hacc hr' with
      h1 | h1
    · obtain ⟨ph, k⟩ := q
      change ph = .acc at hq
      subst hq
      have := reach_terminal rfl h1
      simp only [DPDA.Cfg.mk.injEq] at this
      have := congrArg Prod.fst this.1
      cases this
    · have := reach_terminal rfl h1
      simp only [DPDA.Cfg.mk.injEq] at this
      obtain ⟨rfl, -, -⟩ := this
      cases hq
  · intro h
    obtain ⟨γ, hr⟩ := ia h
    exact ⟨_, γ, rfl, hinit.trans hr⟩

end PD

end BLMS

end PathChecking
