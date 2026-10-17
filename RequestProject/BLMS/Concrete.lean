module

public import RequestProject.BLMS.Algo
public import RequestProject.ACRound.Circ
public import RequestProject.LTLPath.Strat

/-!
# From stratified circuits to layered circuits

For a circuit `C` of the project we define the layered circuit `toLC C`: gates of `C` keep their
index, the layer of a gate is computed by following first arguments down to a constant
(`dep`), and one extra `COPY` gate (index `C.length`) is added on top of the output gate, so that
the output gate is the only gate whose value matters for the last layer.  For instances of the
stratified monotone planar circuit value problem, `toLC C` is planar and accepts the set of true
constant gates iff `C` evaluates to `true` (`toLC_correct`).
-/

@[expose] public section

namespace PathChecking

namespace BLMS

open Set

namespace Conc

variable (C : Circuit)

/-- `AND` gate. -/
def kindAnd (g : Gate) : Bool := match g.kind with | .and => true | _ => false

/-- Constant gate. -/
def kindConst (g : Gate) : Bool := match g.kind with | .const _ => true | _ => false

/-- Constant `true` gate. -/
def kindTrue (g : Gate) : Bool := match g.kind with | .const true => true | _ => false

/-- Gate `i` is a constant (or does not exist). -/
def isC (i : ℕ) : Bool := (C[i]?.map kindConst).getD true

/-- First argument (the extra gate `C.length` copies the output gate). -/
def lo (i : ℕ) : ℕ := if h : i < C.length then C[i].args.headD 0 else C.length - 1

/-- Last argument. -/
def hi (i : ℕ) : ℕ := if h : i < C.length then C[i].args.getLastD 0 else C.length - 1

/-- One step down the chain of first arguments, counting the steps. -/
def chG (p : ℕ × ℕ) : ℕ × ℕ := if isC C p.1 then p else (lo C p.1, p.2 + 1)

/-- `chG`, as a fold step. -/
def chStep (p : ℕ × ℕ) (_ : ℕ) : ℕ × ℕ := chG C p

/-- The layer of a gate: the length of the chain of first arguments down to a constant. -/
def dep (i : ℕ) : ℕ := ((List.range C.length).foldl (chStep C) (i, 0)).2

/-- The layer of the output gate. -/
def top : ℕ := dep C (C.length - 1)

/-- Layers, including the extra gate. -/
def lyr (i : ℕ) : ℕ := if i < C.length then dep C i else top C + 1

/-- Constant `true` gates. -/
def inp (p : ℕ) : Bool := (C[p]?.map kindTrue).getD false

end Conc

/-- The layered circuit of a circuit. -/
def toLC (C : Circuit) : LC where
  isAnd i := if h : i < C.length then Conc.kindAnd C[i] else true
  lo := Conc.lo C
  hi := Conc.hi C
  bd l := firstF (fun i => decide (l ≤ Conc.lyr C i)) (C.length + 1)
  D := Conc.top C + 1

namespace Conc

variable {C : Circuit}

lemma foldl_const_iter {α : Type} (g : α → α) (l : List ℕ) (a : α) :
    l.foldl (fun p _ => g p) a = g^[l.length] a := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => simp [ih, Function.iterate_succ_apply]

section Layering

variable {lay : ℕ → ℕ} (hW : C.WellFormed 0) (hM : C.MonotoneFanin2) (hL : C.StratLayering lay)
include hW hM hL

lemma isC_iff {j : ℕ} (hj : j < C.length) : isC C j = true ↔ lay j = 0 := by
  rw [← hL.input_iff j hj]
  have hw := (hW.2 j hj).2
  simp only [isC, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some, kindConst,
    Gate.IsInput]
  rcases hk : C[j].kind with k | b | _ | _ | _ | _ <;> simp_all

lemma args_ne {j : ℕ} (hj : j < C.length) (h : lay j ≠ 0) :
    (C[j].kind = .and ∨ C[j].kind = .or) ∧ 1 ≤ C[j].args.length ∧ C[j].args.length ≤ 2 := by
  rcases hM C[j] (List.getElem_mem hj) with ⟨b, hb, -⟩ | h'
  · exact absurd ((hL.input_iff j hj).1 (by simp [Gate.IsInput, hb])) h
  · exact h'

lemma lo_mem {j : ℕ} (hj : j < C.length) (h : lay j ≠ 0) : lo C j ∈ C[j].args := by
  obtain ⟨-, h1, -⟩ := args_ne hW hM hL hj h
  simp only [lo, hj, dif_pos]
  rcases hh : C[j].args with _ | ⟨a, l⟩
  · simp [hh] at h1
  · simp

lemma hi_mem {j : ℕ} (hj : j < C.length) (h : lay j ≠ 0) : hi C j ∈ C[j].args := by
  obtain ⟨-, h1, -⟩ := args_ne hW hM hL hj h
  simp only [hi, hj, dif_pos]
  rw [List.getLastD_eq_getLast?]
  rcases hh : C[j].args.getLast? with _ | a
  · simp at hh; simp [hh] at h1
  · simpa using List.mem_of_getLast? hh

lemma lay_le : ∀ j, j < C.length → lay j ≤ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases h : lay j = 0
    · omega
    · have hm := lo_mem hW hM hL hj h
      have h1 := (hW.2 j hj).1 _ hm
      have h2 := hL.args_prev j hj _ hm
      have := ih _ h1 (by omega)
      omega

lemma chain_iter : ∀ k j c, j < C.length → lay j ≤ k →
    ((chG C)^[k] (j, c)).2 = c + lay j := by
  intro k
  induction k with
  | zero =>
    intro j c hj hk
    simp only [Function.iterate_zero, id_eq]
    omega
  | succ k ih =>
    intro j c hj hk
    rw [Function.iterate_succ_apply]
    by_cases h : lay j = 0
    · have hc : isC C j = true := (isC_iff hW hM hL hj).2 h
      have hfix : ∀ m, (chG C)^[m] (j, c) = (j, c) := by
        intro m
        induction m with
        | zero => rfl
        | succ m ihm => rw [Function.iterate_succ_apply', ihm]; simp [chG, hc]
      have e : chG C (j, c) = (j, c) := by simp [chG, hc]
      rw [e, hfix, h]; rfl
    · have hc : isC C j = false := by
        have := (isC_iff hW hM hL hj).not.2 h; simpa using this
      have e : chG C (j, c) = (lo C j, c + 1) := by simp [chG, hc]
      rw [e]
      have hm := lo_mem hW hM hL hj h
      have h1 := (hW.2 j hj).1 _ hm
      have h2 := hL.args_prev j hj _ hm
      rw [ih (lo C j) (c + 1) (by omega) (by omega)]
      omega

lemma dep_eq {j : ℕ} (hj : j < C.length) : dep C j = lay j := by
  unfold dep
  have e : chStep C = fun p _ => chG C p := by funext p x; rfl
  rw [e, foldl_const_iter (chG C), List.length_range,
    chain_iter hW hM hL _ j 0 hj (le_trans (lay_le hW hM hL j hj) hj.le)]
  omega


/-- Values of the gates of `C`. -/
noncomputable def val (C : Circuit) (j : ℕ) : Bool := (C.values ∅ []).getD j false

lemma val_spec {j : ℕ} (hj : j < C.length) : val C j = C[j].evalFn ∅ [] (val C) := by
  have ht : (C.values ∅ []).take j = (List.range j).map (val C) := by
    apply List.ext_getElem
    · simp [Circuit.values_length]; omega
    · intro k h1 h2
      simp only [List.getElem_take, List.getElem_map, List.getElem_range, val]
      rw [List.getD_eq_getElem]
  unfold val
  rw [List.getD_eq_getElem _ _ (by simp [Circuit.values_length, hj]),
    Circuit.values_getElem _ _ _ _ hj, ht, Gate.eval_range_map _ _ _ _ _ ((hW.2 j hj).1)]
  rfl

lemma val_const {j : ℕ} (hj : j < C.length) (h : lay j = 0) :
    ∃ b, C[j].kind = .const b ∧ val C j = b := by
  have hc := (isC_iff hW hM hL hj).2 h
  simp only [isC, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some,
    kindConst] at hc
  rcases hk : C[j].kind with k | b | _ | _ | _ | _ <;> rw [hk] at hc <;> try simp at hc
  exact ⟨b, rfl, by rw [val_spec hW hM hL hj]; simp [Gate.evalFn, hk]⟩

lemma ne_nil : C ≠ [] := hW.1

lemma len_pos : 0 < C.length := List.length_pos_of_ne_nil hW.1

lemma top_eq : top C = lay (C.length - 1) := by
  have := len_pos hW hM hL
  exact dep_eq hW hM hL (by omega)

lemma lyr_lt {i : ℕ} (hi : i < C.length) : lyr C i = lay i := by
  simp [lyr, hi, dep_eq hW hM hL hi]

lemma lyr_n : lyr C C.length = lay (C.length - 1) + 1 := by
  simp [lyr, top_eq hW hM hL]

lemma lay_le_top {i : ℕ} (hi : i < C.length) : lay i ≤ lay (C.length - 1) :=
  hL.mono _ _ (by omega) (by have := len_pos hW hM hL; omega)

lemma lyr_mono {i j : ℕ} (hij : i ≤ j) (hj : j < C.length + 1) : lyr C i ≤ lyr C j := by
  rcases Nat.lt_or_ge j C.length with h | h
  · rw [lyr_lt hW hM hL h, lyr_lt hW hM hL (by omega)]
    exact hL.mono _ _ hij h
  · have : j = C.length := by omega
    subst this
    rcases Nat.lt_or_ge i C.length with h' | h'
    · rw [lyr_lt hW hM hL h', lyr_n hW hM hL]
      have := lay_le_top hW hM hL h'
      omega
    · have : i = C.length := by omega
      subst this; rfl

end Layering

lemma firstF_mono_iff (f : ℕ → ℕ) (m l : ℕ) (hmono : ∀ i j, i ≤ j → j < m → f i ≤ f j) :
    firstF (fun i => decide (l ≤ f i)) m ≤ m ∧
      ∀ i < m, (firstF (fun i => decide (l ≤ f i)) m ≤ i ↔ l ≤ f i) := by
  rcases firstF_spec (fun i => decide (l ≤ f i)) m with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · refine ⟨h1.le, fun i hi => ?_⟩
    rw [h1]
    have := h2 i hi
    simp only [decide_eq_false_iff_not] at this
    constructor
    · intro h; omega
    · intro h; exact absurd h this
  · refine ⟨h1.le, fun i hi => ?_⟩
    simp only [decide_eq_true_eq] at h2
    constructor
    · intro h; exact le_trans h2 (hmono _ _ h hi)
    · intro h
      by_contra h'
      have := h3 i (by omega)
      simp only [decide_eq_false_iff_not] at this
      exact this h

section Layering

variable {lay : ℕ → ℕ} (hW : C.WellFormed 0) (hM : C.MonotoneFanin2) (hL : C.StratLayering lay)
include hW hM hL

lemma bd_spec (l : ℕ) : (toLC C).bd l ≤ C.length + 1 ∧
    ∀ i < C.length + 1, ((toLC C).bd l ≤ i ↔ l ≤ lyr C i) :=
  firstF_mono_iff (lyr C) (C.length + 1) l (fun _ _ h1 h2 => lyr_mono hW hM hL h1 h2)

lemma mem_gates (l i : ℕ) : i ∈ (toLC C).gates l ↔ i < C.length + 1 ∧ lyr C i = l + 1 := by
  obtain ⟨b1, s1⟩ := bd_spec hW hM hL (l + 1)
  obtain ⟨b2, s2⟩ := bd_spec hW hM hL (l + 2)
  simp only [LC.gates, mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    have hi : i < C.length + 1 := by omega
    have := (s1 i hi).1 h1
    have := (s2 i hi).not.1 (by omega)
    exact ⟨hi, by omega⟩
  · rintro ⟨hi, h⟩
    exact ⟨(s1 i hi).2 (by omega), by have := (s2 i hi).not.2 (by omega); omega⟩

lemma mem_gates' {l i : ℕ} (hl : l < lay (C.length - 1)) :
    i ∈ (toLC C).gates l ↔ i < C.length ∧ lay i = l + 1 := by
  rw [mem_gates hW hM hL]
  constructor
  · rintro ⟨hi, h⟩
    rcases Nat.lt_or_ge i C.length with h' | h'
    · exact ⟨h', by rw [← lyr_lt hW hM hL h']; exact h⟩
    · have : i = C.length := by omega
      subst this; rw [lyr_n hW hM hL] at h; omega
  · rintro ⟨hi, h⟩
    exact ⟨by omega, by rw [lyr_lt hW hM hL hi]; exact h⟩

lemma mem_gates_top {i : ℕ} : i ∈ (toLC C).gates (lay (C.length - 1)) ↔ i = C.length := by
  rw [mem_gates hW hM hL]
  constructor
  · rintro ⟨hi, h⟩
    rcases Nat.lt_or_ge i C.length with h' | h'
    · rw [lyr_lt hW hM hL h'] at h; have := lay_le_top hW hM hL h'; omega
    · omega
  · rintro rfl; exact ⟨by omega, lyr_n hW hM hL⟩

lemma lt_N_iff (i : ℕ) : i < (toLC C).N ↔ i < C.length ∧ lay i = 0 := by
  obtain ⟨b1, s1⟩ := bd_spec hW hM hL 1
  show i < (toLC C).bd 1 ↔ _
  constructor
  · intro h
    have hi : i < C.length + 1 := by omega
    have := (s1 i hi).not.1 (by omega)
    rcases Nat.lt_or_ge i C.length with h' | h'
    · exact ⟨h', by rw [← lyr_lt hW hM hL h']; omega⟩
    · have : i = C.length := by omega
      subst this; rw [lyr_n hW hM hL] at this; omega
  · rintro ⟨hi, h⟩
    have := (s1 i (by omega)).not.2 (by rw [lyr_lt hW hM hL hi]; omega)
    omega

/-- Value of a non-constant gate from the membership of its arguments in a set. -/
lemma gval_iff {i : ℕ} (hiC : i < C.length) (h0 : lay i ≠ 0) {S : Set ℕ}
    (hS : ∀ a ∈ C[i].args, (a ∈ S ↔ val C a = true)) :
    (toLC C).gval S i ↔ val C i = true := by
  obtain ⟨hk, h1, h2⟩ := args_ne hW hM hL hiC h0
  rw [val_spec hW hM hL hiC]
  have hlo := lo_mem hW hM hL hiC h0
  have hhi := hi_mem hW hM hL hiC h0
  simp only [LC.gval, toLC, hiC, dif_pos]
  simp only [lo, Conc.hi, hiC, dif_pos] at hlo hhi ⊢
  rw [hS _ hlo, hS _ hhi]
  rcases hh : C[i].args with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp [hh] at h1
  · rcases hk with hk | hk <;> simp [Gate.evalFn, kindAnd, hk, hh]
  · rcases hk with hk | hk <;> simp [Gate.evalFn, kindAnd, hk, hh]
  · simp only [hh, List.length_cons] at h2; omega

lemma ev_eq : ∀ l ≤ lay (C.length - 1),
    (toLC C).ev l ((toLC C).X0 (inp C)) = {i | i < C.length ∧ lay i = l ∧ val C i = true} := by
  intro l
  induction l with
  | zero =>
    intro _
    ext p
    simp only [LC.ev_zero, LC.X0, mem_setOf_eq, lt_N_iff hW hM hL]
    constructor
    · rintro ⟨⟨hp, h0⟩, hi⟩
      obtain ⟨b, hb, hv⟩ := val_const hW hM hL hp h0
      refine ⟨hp, h0, ?_⟩
      simp only [inp, List.getElem?_eq_getElem hp, Option.map_some, Option.getD_some,
        kindTrue, hb] at hi
      cases b <;> simp_all
    · rintro ⟨hp, h0, hv⟩
      obtain ⟨b, hb, hv'⟩ := val_const hW hM hL hp h0
      refine ⟨⟨hp, h0⟩, ?_⟩
      simp only [inp, List.getElem?_eq_getElem hp, Option.map_some, Option.getD_some,
        kindTrue, hb]
      cases b <;> simp_all
  | succ l ih =>
    intro hl
    rw [LC.ev_succ, ih (by omega)]
    ext i
    simp only [LC.step, mem_setOf_eq, mem_gates' hW hM hL (show l < _ by omega)]
    constructor
    · rintro ⟨⟨hi, hli⟩, hg⟩
      refine ⟨hi, hli, (gval_iff hW hM hL hi (by omega) (fun a ha => ?_)).1 hg⟩
      have h1 := (hW.2 i hi).1 a ha
      have h2 := hL.args_prev i hi a ha
      simp only [mem_setOf_eq]
      constructor
      · exact fun h => h.2.2
      · exact fun h => ⟨by omega, by omega, h⟩
    · rintro ⟨hi, hli, hv⟩
      refine ⟨⟨hi, hli⟩, (gval_iff hW hM hL hi (by omega) (fun a ha => ?_)).2 hv⟩
      have h1 := (hW.2 i hi).1 a ha
      have h2 := hL.args_prev i hi a ha
      simp only [mem_setOf_eq]
      constructor
      · exact fun h => h.2.2
      · exact fun h => ⟨by omega, by omega, h⟩

lemma out_iff : (toLC C).out ((toLC C).X0 (inp C)) ↔ C.eval ∅ [] = true := by
  have hn := len_pos hW hM hL
  have hD : (toLC C).D = lay (C.length - 1) + 1 := by
    show top C + 1 = _; rw [top_eq hW hM hL]
  unfold LC.out
  rw [hD, LC.ev_succ, ev_eq hW hM hL _ le_rfl, Circuit.eval_eq_getElem _ _ _ hW.1]
  have e : (C.values ∅ [])[C.length - 1]'(by simp [Circuit.values_length]; omega) =
      val C (C.length - 1) := by
    unfold val; rw [List.getD_eq_getElem]
  rw [e]
  constructor
  · rintro ⟨i, hmem, hg⟩
    rw [mem_gates_top hW hM hL] at hmem
    subst hmem
    simp only [LC.gval, toLC, lt_irrefl, dif_neg, not_false_eq_true, if_true, lo, Conc.hi,
      mem_setOf_eq] at hg
    exact hg.1.2.2
  · intro hv
    refine ⟨C.length, (mem_gates_top hW hM hL).2 rfl, ?_⟩
    simp only [LC.gval, toLC, lt_irrefl, dif_neg, not_false_eq_true, if_true, lo, Conc.hi,
      mem_setOf_eq]
    exact ⟨⟨by omega, trivial, hv⟩, ⟨by omega, trivial, hv⟩⟩

omit hW hM hL in
lemma headD_le_getLastD {l : List ℕ} (h : l.Pairwise (· < ·)) : l.headD 0 ≤ l.getLastD 0 := by
  rcases l with _ | ⟨a, t⟩
  · simp
  · simp only [List.headD_cons]
    rw [List.getLastD_eq_getLast?, List.getLast?_cons]
    rcases ht : t.getLast? with _ | b
    · simp
    · simp only [Option.getD_some]
      have := List.mem_of_getLast? ht
      exact (List.rel_of_pairwise_cons h this).le

lemma planar : (toLC C).Planar := by
  refine ⟨fun l hl i hi => ?_, fun l hl i hi i' hi' hii' => ?_⟩
  · rw [mem_gates hW hM hL] at hi
    show lo C i ≤ Conc.hi C i
    rcases Nat.lt_or_ge i C.length with h | h
    · simp only [lo, Conc.hi, h, dif_pos]
      exact headD_le_getLastD (hL.args_sorted i h)
    · simp [lo, Conc.hi, show ¬ i < C.length by omega]
  · rw [mem_gates hW hM hL] at hi hi'
    show Conc.hi C i ≤ lo C i'
    have hin : i < C.length := by omega
    have hi'n : i' < C.length := by
      by_contra h
      have : i' = C.length := by omega
      subst this
      rw [lyr_n hW hM hL] at hi'
      rw [lyr_lt hW hM hL hin] at hi
      have := lay_le_top hW hM hL hin
      omega
    rw [lyr_lt hW hM hL hin] at hi
    rw [lyr_lt hW hM hL hi'n] at hi'
    exact hL.planar i i' hin hi'n hii' (by omega) _ (hi_mem hW hM hL hin (by omega)) _
      (lo_mem hW hM hL hi'n (by omega))

end Layering

/-- **Correctness of the translation.** -/
theorem toLC_correct (h : StratMCVPInstance C) :
    (toLC C).Planar ∧ ((toLC C).out ((toLC C).X0 (inp C)) ↔ C.eval ∅ [] = true) := by
  obtain ⟨hW, hM, lay, hL⟩ := h
  exact ⟨planar hW hM hL, out_iff hW hM hL⟩

end Conc

end BLMS

end PathChecking
