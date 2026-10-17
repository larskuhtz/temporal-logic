module

public import RequestProject.ACRound.WF

/-!
# The round circuit computes the rounds of queries
-/

@[expose] public section

namespace PathChecking

open Classical

lemma Gate.eval_eq_evalFn (B : Language) (x : Word) (vals : List Bool) (val : ℕ → Bool)
    (g : Gate) (h : ∀ j ∈ g.args, vals.getD j false = val j) :
    g.eval B x vals = g.evalFn B x val := by
  have e : g.args.map (fun j => vals.getD j false) = g.args.map val :=
    List.map_congr_left fun j hj => h j hj
  unfold Gate.eval Gate.evalFn
  simp only [e]
  rcases g.kind <;> rfl

lemma Circuit.values_getD_evalFn (B : Language) (x : Word) (C : Circuit) (v : ℕ)
    (hv : v < C.length) (hargs : ∀ j ∈ C[v].args, j < v) :
    (C.values B x).getD v false = C[v].evalFn B x (fun j => (C.values B x).getD j false) := by
  rw [List.getD_eq_getElem _ _ (by simp [Circuit.values_length, hv]),
    Circuit.values_getElem B x C v hv]
  refine Gate.eval_eq_evalFn _ _ _ _ _ fun j hj => ?_
  have := hargs j hj
  simp [List.getD_eq_getElem?_getD, this]

lemma roundAns_length (B : Language) (Q : Word → Word) (Nq : ℕ) (w : Word) (r : ℕ) :
    (roundAns B Q Nq w r).length = Nq := by
  cases r <;> simp [roundAns]

lemma getD_eq_true_and_length {y : Word} :
    (y.getD 0 false && decide (y.length = 1)) = decide (y = [true]) := by
  rcases y with _ | ⟨b, _ | ⟨c, y⟩⟩ <;> simp

namespace Lay

variable (P : Lay) (B Bc : Language) (Q D : Word → Word) (w : Word)

/-- Values of the gates of a group. -/
noncomputable def grpVal (r q t : ℕ) : Bool :=
  let x := Q (pack w q (roundAns B Q P.Nq w r))
  if t < P.L + 1 then x.getD t false
  else if t < 2 * (P.L + 1) then decide (x.length = t - (P.L + 1))
  else if t < P.W - 1 then
    if (t - 2 * (P.L + 1)) % P.S < (P.CB ((t - 2 * (P.L + 1)) / P.S)).length then
      (Circuit.values Bc x (P.CB ((t - 2 * (P.L + 1)) / P.S))).getD
        ((t - 2 * (P.L + 1)) % P.S) false
    else if (t - 2 * (P.L + 1)) % P.S + 1 < P.S then false
    else decide (x.length = (t - 2 * (P.L + 1)) / P.S) &&
      (P.CB ((t - 2 * (P.L + 1)) / P.S)).eval Bc x
  else decide (x ∈ B)

/-- Values of all gates. -/
noncomputable def val (i : ℕ) : Bool :=
  if i = 0 then false else if i = 1 then true else if i < P.P0 then w.getD (i - 2) false
  else if i < P.F0 then
    P.grpVal B Bc Q w ((i - P.P0) / P.W / P.Nq) ((i - P.P0) / P.W % P.Nq) ((i - P.P0) % P.W)
  else if i = P.F0 then (D (pack w 0 (roundAns B Q P.Nq w P.R))).getD 0 false
  else if i = P.F0 + 1 then decide ((D (pack w 0 (roundAns B Q P.Nq w P.R))).length = 1)
  else decide (D (pack w 0 (roundAns B Q P.Nq w P.R)) = [true])

variable {P B Bc Q D w}

lemma P0_ge : 2 ≤ P.P0 := by simp [P0]

lemma val_gb (r q t : ℕ) (hr : r < P.R) (hq : q < P.Nq) (ht : t < P.W) :
    P.val B Bc Q D w (P.gb r q + t) = P.grpVal B Bc Q w r q t := by
  have h2 := P0_ge (P := P)
  have hge := gb_ge (P := P) r q
  have hlt : P.gb r q + t < P.F0 := by
    unfold gb F0
    have : (r * P.Nq + q + 1) * P.W ≤ P.R * P.Nq * P.W :=
      Nat.mul_le_mul_right _ (by nlinarith)
    nlinarith
  have hW := W_pos (P := P)
  have e1 : P.gb r q + t - P.P0 = (r * P.Nq + q) * P.W + t := by unfold gb; omega
  have e2 : ((r * P.Nq + q) * P.W + t) / P.W = r * P.Nq + q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt ht, Nat.zero_add]
  have e3 : ((r * P.Nq + q) * P.W + t) % P.W = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  have hN : 0 < P.Nq := by omega
  have e4 : (r * P.Nq + q) / P.Nq = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hq, Nat.zero_add]
  have e5 : (r * P.Nq + q) % P.Nq = q := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
  unfold val
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hlt, e1, e2, e3, e4, e5]

lemma grpVal_block (r q ℓ v : ℕ) (hℓ : ℓ ≤ P.L) (hv : v < P.S) :
    P.grpVal B Bc Q w r q (2 * (P.L + 1) + ℓ * P.S + v) =
      let x := Q (pack w q (roundAns B Q P.Nq w r))
      if v < (P.CB ℓ).length then (Circuit.values Bc x (P.CB ℓ)).getD v false
      else if v + 1 < P.S then false
      else decide (x.length = ℓ) && (P.CB ℓ).eval Bc x := by
  have hS : 0 < P.S := by omega
  have e1 : 2 * (P.L + 1) + ℓ * P.S + v - 2 * (P.L + 1) = ℓ * P.S + v := by omega
  have e2 : (ℓ * P.S + v) / P.S = ℓ := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hv, Nat.zero_add]
  have e3 : (ℓ * P.S + v) % P.S = v := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]
  have hlt : 2 * (P.L + 1) + ℓ * P.S + v < P.W - 1 := by
    have : ℓ * P.S + v < (P.L + 1) * P.S := by nlinarith
    unfold W; omega
  unfold grpVal
  simp only
  rw [if_neg (by omega), if_neg (by omega), if_pos hlt, e1, e2, e3]

lemma val_block (r q ℓ v : ℕ) (hr : r < P.R) (hq : q < P.Nq) (hℓ : ℓ ≤ P.L) (hv : v < P.S) :
    P.val B Bc Q D w (P.bb r q ℓ + v) =
      let x := Q (pack w q (roundAns B Q P.Nq w r))
      if v < (P.CB ℓ).length then (Circuit.values Bc x (P.CB ℓ)).getD v false
      else if v + 1 < P.S then false
      else decide (x.length = ℓ) && (P.CB ℓ).eval Bc x := by
  have hlt : 2 * (P.L + 1) + ℓ * P.S + v < P.W := by
    have : ℓ * P.S + v < (P.L + 1) * P.S := by nlinarith
    unfold W; omega
  rw [bb_eq, Nat.add_assoc, val_gb r q _ hr hq hlt,
    grpVal_block r q ℓ v hℓ hv]

lemma val_ans (r q : ℕ) (hr : r ≤ P.R) (hq : q < P.Nq) :
    P.val B Bc Q D w (P.ans r q) = (roundAns B Q P.Nq w r).getD q false := by
  rcases r with _ | r
  · simp [ans, val, roundAns]
  · have hW := W_pos (P := P)
    simp only [ans]
    rw [Nat.add_sub_assoc (by omega), val_gb r q _ (by omega) hq (by omega)]
    unfold grpVal
    have hWd : P.W = 2 * (P.L + 1) + (P.L + 1) * P.S + 1 := rfl
    simp only
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp [roundAns, hq]

lemma map_val_packArgs (hn : P.n = w.length) (r q : ℕ) (hr : r ≤ P.R) :
    (P.packArgs r q).map (P.val B Bc Q D w) = pack w q (roundAns B Q P.Nq w r) := by
  have h2 := P0_ge (P := P)
  have v0 : P.val B Bc Q D w 0 = false := by simp [val]
  have v1 : P.val B Bc Q D w 1 = true := by simp [val]
  have e1 : ((List.range P.n).map (2 + ·)).map (P.val B Bc Q D w) = w := by
    apply List.ext_getElem (by simp [hn])
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    unfold val
    rw [if_neg (by omega), if_neg (by omega), if_pos (by simp [P0]; omega)]
    simp [List.getD_eq_getElem?_getD, show i < w.length by omega]
  have e2 : ((List.range P.Nq).map (P.ans r)).map (P.val B Bc Q D w) =
      roundAns B Q P.Nq w r := by
    apply List.ext_getElem (by simp [roundAns_length])
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    rw [val_ans r i hr h1, List.getD_eq_getElem _ _ (by simp [roundAns_length, h1])]
  unfold packArgs pack
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil, e1, e2, v0, v1,
    roundAns_length, ← hn]

lemma map_val_qArgs (hn : P.n = w.length) (t b : Bool) (i r q : ℕ) (hr : r ≤ P.R) :
    (P.qArgs t b i r q).map (P.val B Bc Q D w) =
      true :: t :: b :: (List.replicate i true ++ false :: pack w q (roundAns B Q P.Nq w r)) := by
  have v0 : P.val B Bc Q D w 0 = false := by simp [val]
  have v1 : P.val B Bc Q D w 1 = true := by simp [val]
  have vb : ∀ c, P.val B Bc Q D w (bitIdx c) = c := fun c => by cases c <;> simp [bitIdx, v0, v1]
  unfold qArgs
  simp [vb, v0, v1, map_val_packArgs hn r q hr]

lemma oracle_query (t b : Bool) (i : ℕ) (u : Word) :
    decide ((true :: t :: b :: (List.replicate i true ++ false :: u)) ∈
        tagU Bc (tagU (LangF Q) (LangF D))) =
      if t then (if b then decide ((D u).length = i) else (D u).getD i false)
      else (if b then decide ((Q u).length = i) else (Q u).getD i false) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_iff, cons_mem_tagU, if_true]
  cases t <;> cases b <;> simp [mem_LangF, List.getD_eq_getElem?_getD]

/-- Copies of gates of `CB ℓ` compute the same values as the originals. -/
lemma copyGate_evalFn (O E : Language) (hO : O = tagU Bc E) (val : ℕ → Bool) (x : Word)
    (vals : List Bool) (b0 g0 ℓ v : ℕ) (g : Gate)
    (hargs : ∀ j ∈ g.args, j < v)
    (hinp : ∀ k, g.kind = .input k → k < ℓ)
    (h0 : val 0 = false) (hbit : ∀ k < ℓ, val (g0 + k) = x.getD k false)
    (hcp : ∀ j < v, val (b0 + j) = vals.getD j false) :
    (copyGate b0 g0 g).evalFn O w val = g.evalFn Bc x (fun j => vals.getD j false) := by
  have hm : g.args.map (fun j => val (b0 + j)) = g.args.map (fun j => vals.getD j false) :=
    List.map_congr_left fun j hj => hcp j (hargs j hj)
  unfold copyGate
  rcases hk : g.kind with k | c | _ | _ | _ | _ <;> simp only [Gate.evalFn, hk, List.map_map]
  · simp [hbit k (hinp k hk)]
  · simp only [Function.comp_def, hm]
  · simp only [Function.comp_def, hm]
  · simp only [Function.comp_def, hm]
  · rw [hO, Bool.eq_iff_iff]
    simp only [List.map_cons, h0, decide_eq_true_iff, cons_mem_tagU, Bool.false_eq_true, if_false]
    rw [List.map_map, show (val ∘ fun x => b0 + x) = fun j => val (b0 + j) from rfl, hm]

end Lay

end PathChecking
