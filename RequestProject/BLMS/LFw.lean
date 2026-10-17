module

public import RequestProject.LogLang.Out
public import RequestProject.ACRound.Pack
public import RequestProject.BLMS.Classify
public import RequestProject.BLMS.Algo

/-!
# A small framework for the loop-language program of the reduction

`st w K P ρ`: the final variable assignment of a run of `P` (with cap `K`).  Silent programs are
reasoned about through `st` only; loops are simulated by folds over `List.range` (`st_loop`).
We also define the expression `tokE p` reading the code of the `p`-th token of the input.
-/

@[expose] public section

namespace PathChecking

namespace BLMS

namespace LP

open LL

/-- Number of variables. -/
abbrev V : ℕ := 96

/-- Variables. -/
abbrev Var := Fin V

variable {w : Word} {K : ℕ}

/-- Final variable assignment of a run. -/
def st (w : Word) (K : ℕ) (P : Pr V) (ρ : Var → ℕ) : Var → ℕ := (P.run w K ρ).1

@[simp] lemma st_skip (ρ : Var → ℕ) : st w K .skip ρ = ρ := rfl
@[simp] lemma st_set (x : Var) (e : Ex V) (ρ : Var → ℕ) :
    st w K (.set x e) ρ = Function.update ρ x (e.eval w K ρ) := rfl
@[simp] lemma st_seq (s t : Pr V) (ρ : Var → ℕ) : st w K (.seq s t) ρ = st w K t (st w K s ρ) :=
  rfl
lemma st_ite (e : Ex V) (s t : Pr V) (ρ : Var → ℕ) :
    st w K (.ite e s t) ρ = if e.eval w K ρ ≠ 0 then st w K s ρ else st w K t ρ := by
  unfold st; rw [run_ite]; split_ifs <;> rfl
lemma st_ite_pos {e : Ex V} {s t : Pr V} {ρ : Var → ℕ} (h : e.eval w K ρ ≠ 0) :
    st w K (.ite e s t) ρ = st w K s ρ := by rw [st_ite, if_pos h]
lemma st_ite_neg {e : Ex V} {s t : Pr V} {ρ : Var → ℕ} (h : e.eval w K ρ = 0) :
    st w K (.ite e s t) ρ = st w K t ρ := by rw [st_ite, if_neg (by simpa using h)]

lemma st_frame (P : Pr V) (ρ : Var → ℕ) (z : Var) (hz : z ∉ P.wr) : st w K P ρ z = ρ z :=
  Pr.run_frame P ρ z hz

lemma run_eq_st {P : Pr V} (h : P.silent = true) (ρ : Var → ℕ) :
    P.run w K ρ = (st w K P ρ, []) := Prod.ext rfl (Pr.run_silent P h ρ)

/-- **Loop simulation.** -/
lemma st_loop {α : Type} (x : Var) (e : Ex V) (s : Pr V) (ρ : Var → ℕ) (f : α → ℕ → α) (a0 : α)
    (R : (Var → ℕ) → α → Prop) (h0 : R ρ a0)
    (hs : ∀ i < e.eval w K ρ, ∀ ρ' a, (∀ z, z ∉ (Pr.loop x e s).wr → ρ' z = ρ z) → R ρ' a →
      R (st w K s (Function.update ρ' x i)) (f a i)) :
    R (st w K (.loop x e s) ρ) ((List.range (e.eval w K ρ)).foldl f a0) := by
  have key : ∀ j, j ≤ e.eval w K ρ →
      (∀ z, z ∉ (Pr.loop x e s).wr → ((List.range j).foldl (loopF w K x s) (ρ, [])).1 z = ρ z) ∧
      R ((List.range j).foldl (loopF w K x s) (ρ, [])).1 ((List.range j).foldl f a0) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨fun _ _ => rfl, h0⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [foldl_range_succ, foldl_range_succ]
      refine ⟨fun z hz => ?_, hs j (by omega) _ _ h1 h2⟩
      simp only [Pr.wr, List.mem_cons, not_or] at hz
      show st w K s _ z = ρ z
      rw [st_frame _ _ _ hz.2, Function.update_of_ne hz.1, h1 z (by simp [Pr.wr, hz.1, hz.2])]
  exact (key _ le_rfl).2


/-- **Loop simulation** with an indexed invariant. -/
lemma st_loopI {α : Type} (x : Var) (e : Ex V) (s : Pr V) (ρ : Var → ℕ) (f : α → ℕ → α) (a0 : α)
    (R : ℕ → (Var → ℕ) → α → Prop) (h0 : R 0 ρ a0)
    (hs : ∀ i < e.eval w K ρ, ∀ ρ' a, (∀ z, z ∉ (Pr.loop x e s).wr → ρ' z = ρ z) → R i ρ' a →
      R (i + 1) (st w K s (Function.update ρ' x i)) (f a i)) :
    R (e.eval w K ρ) (st w K (.loop x e s) ρ) ((List.range (e.eval w K ρ)).foldl f a0) := by
  have key : ∀ j, j ≤ e.eval w K ρ →
      (∀ z, z ∉ (Pr.loop x e s).wr → ((List.range j).foldl (loopF w K x s) (ρ, [])).1 z = ρ z) ∧
      R j ((List.range j).foldl (loopF w K x s) (ρ, [])).1 ((List.range j).foldl f a0) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨fun _ _ => rfl, h0⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [foldl_range_succ, foldl_range_succ]
      refine ⟨fun z hz => ?_, hs j (by omega) _ _ h1 h2⟩
      simp only [Pr.wr, List.mem_cons, not_or] at hz
      show st w K s _ z = ρ z
      rw [st_frame _ _ _ hz.2, Function.update_of_ne hz.1, h1 z (by simp [Pr.wr, hz.1, hz.2])]
  exact (key _ le_rfl).2

/-! ## Expressions -/

/-- The input bit at the `0`-based position `e` (as `0`/`1`). -/
def bitAt (e : Ex V) : Ex V := .inp (.bin .add e (.c 1))

/-- The code of the token at token position `p`. -/
def tokE (p : Ex V) : Ex V :=
  .bin .add (bitAt (.bin .mul (.c 5) p))
    (.bin .add (.bin .mul (.c 2) (bitAt (.bin .add (.bin .mul (.c 5) p) (.c 1))))
      (.bin .add (.bin .mul (.c 4) (bitAt (.bin .add (.bin .mul (.c 5) p) (.c 2))))
        (.bin .add (.bin .mul (.c 8) (bitAt (.bin .add (.bin .mul (.c 5) p) (.c 3))))
          (.bin .mul (.c 16) (bitAt (.bin .add (.bin .mul (.c 5) p) (.c 4)))))))

lemma eval_bitAt (ρ : Var → ℕ) (e : Ex V) (b : Bool) (h : w[e.eval w K ρ]? = some b)
    (hK : e.eval w K ρ + 1 ≤ K) : (bitAt e).eval w K ρ = if b then 1 else 0 := by
  simp only [bitAt, eval_inp, eval_bin, ap_add, eval_c]
  rw [min_eq_left (by have : 1 ≤ K := by omega
                      rw [min_eq_left this]; omega), min_eq_left (by omega)]
  simp only [inputSym, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, h]
  cases b <;> rfl

/-- **Reading tokens.** -/
lemma eval_tokE (ts : List Tok) (hw : w = encodeToks ts) (ρ : Var → ℕ) (p : Ex V)
    (hp : p.eval w K ρ < ts.length) (hK : w.length + 40 ≤ K) :
    (tokE p).eval w K ρ = (ts[p.eval w K ρ]'hp).code := by
  set pv := p.eval w K ρ with hpv
  change _ = (ts[pv]'hp).code
  have hlen : w.length = 5 * ts.length := by rw [hw]; exact SQ.encodeToks_length ts
  have hb : ∀ b < 5, (bitAt (.bin .add (.bin .mul (.c 5) p) (.c b))).eval w K ρ =
      if (ts[pv]).code.testBit b then 1 else 0 := by
    intro b hb5
    have e1 : (Ex.bin .add (.bin .mul (.c 5) p) (.c b) : Ex V).eval w K ρ = 5 * pv + b := by
      simp only [eval_bin, ap_add, ap_mul, eval_c]
      rw [min_eq_left (show 5 ≤ K by omega), min_eq_left (show 5 * pv ≤ K by omega),
        min_eq_left (show b ≤ K by omega), min_eq_left (show 5 * pv + b ≤ K by omega)]
    rw [eval_bitAt ρ _ ((ts[pv]).code.testBit b) (by rw [e1, hw]; exact SQ.encodeToks_getElem? ts pv b hp hb5)
      (by rw [e1]; omega)]
  have hb0 : (bitAt (.bin .mul (.c 5) p)).eval w K ρ =
      if (ts[pv]).code.testBit 0 then 1 else 0 := by
    have e1 : (Ex.bin .mul (.c 5) p : Ex V).eval w K ρ = 5 * pv + 0 := by
      simp only [eval_bin, ap_mul, eval_c]
      rw [min_eq_left (show 5 ≤ K by omega), min_eq_left (show 5 * pv ≤ K by omega)]; rfl
    rw [eval_bitAt ρ _ ((ts[pv]).code.testBit 0) (by rw [e1, hw]; exact SQ.encodeToks_getElem? ts pv 0 hp (by omega))
      (by rw [e1]; omega)]
  have hsum := SQ.code_bits_sum (ts[pv])
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil] at hsum
  have hcode := CTLP.Tok.code_lt (ts[pv])
  simp only [tokE, eval_bin, ap_add, ap_mul, eval_c, hb0, hb 1 (by omega), hb 2 (by omega),
    hb 3 (by omega), hb 4 (by omega)]
  have hx : ∀ b, (if (ts[pv]).code.testBit b = true then 1 else 0) ≤ 1 := fun b => by
    split_ifs <;> omega
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have h4 := hx 4
  generalize (if (ts[pv]).code.testBit 0 = true then 1 else 0) = x0 at hsum h0 ⊢
  generalize (if (ts[pv]).code.testBit 1 = true then 1 else 0) = x1 at hsum h1 ⊢
  generalize (if (ts[pv]).code.testBit 2 = true then 1 else 0) = x2 at hsum h2 ⊢
  generalize (if (ts[pv]).code.testBit 3 = true then 1 else 0) = x3 at hsum h3 ⊢
  generalize (if (ts[pv]).code.testBit 4 = true then 1 else 0) = x4 at hsum h4 ⊢
  norm_num at hsum
  rw [min_eq_left (show 2 ≤ K by omega), min_eq_left (show 4 ≤ K by omega),
    min_eq_left (show 8 ≤ K by omega), min_eq_left (show 16 ≤ K by omega)]
  omega

/-! ## Generic searches -/

/-- `[a ≠ 0 ∧ b ≠ 0]` -/
def andE (a b : Ex V) : Ex V := .bin .lt (.c 0) (.bin .mul a b)

lemma eval_andE (ρ : Var → ℕ) (a b : Ex V) (hK : 1 ≤ K) :
    (andE a b).eval w K ρ ≠ 0 ↔ a.eval w K ρ ≠ 0 ∧ b.eval w K ρ ≠ 0 := by
  simp only [andE, eval_bin, ap_lt, ap_mul, eval_c]
  rw [min_eq_left (Nat.zero_le K)]
  constructor
  · intro h
    split_ifs at h with h1
    · constructor <;> intro h2 <;> simp [h2] at h1
    · exact absurd rfl h
  · rintro ⟨h1, h2⟩
    rw [if_pos]
    · omega
    · have : 0 < a.eval w K ρ * b.eval w K ρ := Nat.mul_pos (by omega) (by omega)
      rcases le_total (a.eval w K ρ * b.eval w K ρ) K with h | h
      · rw [min_eq_left h]; exact this
      · rw [min_eq_right h]; omega

/-- `firstF P N` where `N` is held in `nb`, the body computes the predicate `pred`. -/
def firstFP (r i nb : Var) (body : Pr V) (pred : Ex V) : Pr V :=
  .seq (.set r (.v nb)) (.loop i (.v nb)
    (.seq body (.ite (andE (.bin .eq (.v r) (.v nb)) pred) (.set r (.v i)) .skip)))

lemma firstFP_spec (r i nb : Var) (body : Pr V) (pred : Ex V) (ρ : Var → ℕ) (P : ℕ → Bool)
    (hri : r ≠ i) (hrnb : r ≠ nb) (hinb : i ≠ nb) (hbr : r ∉ body.wr) (hbnb : nb ∉ body.wr)
    (hbi : i ∉ body.wr) (hK : 1 ≤ K)
    (hP : ∀ p < ρ nb, ∀ ρ', (∀ z, z ∉ body.wr → z ≠ r → z ≠ i → ρ' z = ρ z) →
      ((pred.eval w K (st w K body (Function.update ρ' i p)) ≠ 0) ↔ P p = true)) :
    st w K (firstFP r i nb body pred) ρ r = firstF P (ρ nb) := by
  unfold firstFP
  simp only [st_seq, st_set, eval_v]
  set ρ1 := Function.update ρ r (ρ nb)
  have hb : (Ex.v nb : Ex V).eval w K ρ1 = ρ nb := by
    simp [ρ1, Function.update_of_ne hrnb.symm]
  have key := st_loop (w := w) (K := K) i (.v nb)
    (.seq body (.ite (andE (.bin .eq (.v r) (.v nb)) pred) (.set r (.v i)) .skip)) ρ1
    (fun r' p => if r' = ρ nb ∧ P p = true then p else r') (ρ nb)
    (fun ρ' a => ρ' r = a) (by simp [ρ1]) (by
      intro p hp ρ' a hfr ha
      rw [hb] at hp
      have hfr' : ∀ z, z ∉ body.wr → z ≠ r → z ≠ i → ρ' z = ρ z := by
        intro z h1 h2 h3
        rw [hfr z (by simp [Pr.wr, h1, h2, h3])]
        exact Function.update_of_ne h2 _ _
      have hnb : ρ' nb = ρ nb := hfr' nb hbnb hrnb.symm hinb.symm
      simp only [st_seq]
      have h2r : st w K body (Function.update ρ' i p) r = a := by
        rw [st_frame _ _ _ hbr, Function.update_of_ne hri, ha]
      have h2nb : st w K body (Function.update ρ' i p) nb = ρ nb := by
        rw [st_frame _ _ _ hbnb, Function.update_of_ne hinb.symm, hnb]
      have h2i : st w K body (Function.update ρ' i p) i = p := by rw [st_frame _ _ _ hbi]; simp
      have hpred := hP p hp ρ' hfr'
      rw [st_ite]
      by_cases hc : a = ρ nb ∧ P p = true
      · rw [if_pos ((eval_andE _ _ _ hK).2 ⟨by simp [h2r, h2nb, hc.1], hpred.2 hc.2⟩),
          if_pos hc]
        simp [h2i]
      · rw [if_neg (fun h => hc ?_), if_neg hc]
        · simpa using h2r
        · obtain ⟨h1, h2⟩ := (eval_andE _ _ _ hK).1 h
          simp only [eval_bin, ap_eq, eval_v, h2r, h2nb] at h1
          exact ⟨by by_contra h'; simp [h'] at h1, hpred.1 h2⟩)
  rw [hb] at key
  exact key

lemma firstFP_wr (r i nb : Var) (body : Pr V) (pred : Ex V) :
    (firstFP r i nb body pred).wr = r :: i :: (body.wr ++ ([r] ++ [])) := rfl

/-- `anyR N P` (as `0`/`1`) where `N` is held in `nb`, the body computes the predicate `pred`. -/
def anyRP (r i nb : Var) (body : Pr V) (pred : Ex V) : Pr V :=
  .seq (.set r (.c 0)) (.loop i (.v nb) (.seq body (.ite pred (.set r (.c 1)) .skip)))

lemma anyRP_spec (r i nb : Var) (body : Pr V) (pred : Ex V) (ρ : Var → ℕ) (P : ℕ → Bool)
    (hri : r ≠ i) (hrnb : r ≠ nb) (hbr : r ∉ body.wr)
    (hK : 1 ≤ K)
    (hP : ∀ p < ρ nb, ∀ ρ', (∀ z, z ∉ body.wr → z ≠ r → z ≠ i → ρ' z = ρ z) →
      ((pred.eval w K (st w K body (Function.update ρ' i p)) ≠ 0) ↔ P p = true)) :
    st w K (anyRP r i nb body pred) ρ r = (LC.anyR (ρ nb) P).toNat := by
  unfold anyRP
  simp only [st_seq, st_set, eval_c]
  set ρ1 := Function.update ρ r (min 0 K)
  have hb : (Ex.v nb : Ex V).eval w K ρ1 = ρ nb := by
    simp [ρ1, Function.update_of_ne hrnb.symm]
  have key := st_loop (w := w) (K := K) i (.v nb) (.seq body (.ite pred (.set r (.c 1)) .skip)) ρ1
    (fun acc k => acc || P k) false
    (fun ρ' a => ρ' r = a.toNat) (by simp [ρ1]) (by
      intro p hp ρ' a hfr ha
      rw [hb] at hp
      have hfr' : ∀ z, z ∉ body.wr → z ≠ r → z ≠ i → ρ' z = ρ z := by
        intro z h1 h2 h3
        rw [hfr z (by simp [Pr.wr, h1, h2, h3])]
        exact Function.update_of_ne h2 _ _
      simp only [st_seq]
      have h2r : st w K body (Function.update ρ' i p) r = a.toNat := by
        rw [st_frame _ _ _ hbr, Function.update_of_ne hri, ha]
      have hpred := hP p hp ρ' hfr'
      rw [st_ite]
      by_cases hc : P p = true
      · rw [if_pos (hpred.2 hc)]
        simp [hc, min_eq_left hK]
      · rw [if_neg (fun h => hc (hpred.1 h))]
        simp only [st_skip, h2r]
        simp [Bool.eq_false_iff.2 hc])
  rw [hb] at key
  exact key

lemma anyR_eq (n : ℕ) (P : ℕ → Bool) : LC.anyR n P = (List.range n).foldl (fun acc k => acc || P k) false := rfl

end LP

end BLMS

end PathChecking
