module

public import RequestProject.MCVP.Validate

/-!
# The token lists produced by the reduction, in a form suitable for streaming

* the formula `Φ_n` is a concatenation of "prefix blocks", one per gate (from the last gate
  down to gate `0`), followed by `init`; each block is described by a fixed list of `Item`s,
  i.e. fixed tokens and numbers `4k + c`;
* the tree is a concatenation of blocks, one per gate (from the last gate down to gate `0`),
  followed by `2n` closing brackets;
* the label of a register node, sorted, is an explicit list.
-/

@[expose] public section

namespace PathChecking

namespace MCVPReduction

/-! ## The formula -/

/-- Items of a streamed token list: a fixed token, or the number `4k + c`. -/
inductive Item
  | lit (t : Tok)
  | num (c : ℕ)

/-- Tokens of an item (at level `k`). -/
def Item.toks (k : ℕ) : Item → List Tok
  | .lit t => [t]
  | .num c => natToks (4 * k + c)

open Item in
/-- Items of the prefix of `theta k p` (before `p`). -/
def thetaItems : List Item :=
  [lit (.tag 5), lit (.tag 0), num 1, lit (.tag 3)] ++
  [lit (.tag 2), lit (.tag 3), lit (.tag 2), lit (.tag 3), lit (.tag 4), lit (.tag 0), lit .sep,
    lit (.tag 2), lit (.tag 0), num 1, lit (.tag 2), lit (.tag 0), num 2] ++
  [lit (.tag 5)] ++
  [lit (.tag 3), lit (.tag 2), lit (.tag 4), lit (.tag 4), lit (.tag 0), lit .sep, lit (.tag 2),
    lit (.tag 0), lit .sep] ++
  [lit (.tag 3)] ++
  [lit (.tag 3), lit (.tag 3), lit (.tag 2), lit (.tag 3), lit (.tag 2), lit (.tag 4), lit (.tag 0),
    lit .sep, lit (.tag 2), lit (.tag 0), num 3, lit (.tag 2), lit (.tag 0), lit .sep,
    lit (.tag 2), lit (.tag 0), num 2]

/-- Items of the prefix of `wrap k G p` (before `p`). -/
def wrapItems : MGate → List Item
  | .input _ => []
  | .or _ _ => .lit (.tag 6) :: thetaItems
  | .and _ _ => [.lit (.tag 2), .lit (.tag 6)] ++ thetaItems ++ [.lit (.tag 2)]

lemma natToks_zero : natToks 0 = [Tok.sep] := by simp [natToks]

lemma theta_toks (k : ℕ) (p : CTLStar) :
    (theta k p).toks = thetaItems.flatMap (Item.toks k) ++ p.toks := by
  simp [theta, beta1, beta2, gamma2, cOr, CTLStar.toks, thetaItems, Item.toks, aAct, aDum, aIn,
    aSide, natToks_zero]

lemma wrap_toks (k : ℕ) (G : MGate) (p : CTLStar) :
    (wrap k G p).toks = (wrapItems G).flatMap (Item.toks k) ++ p.toks := by
  cases G with
  | input b => simp [wrap, wrapItems]
  | or i j => simp [wrap, wrapItems, CTLStar.toks, theta_toks, Item.toks]
  | and i j =>
    simp [wrap, wrapItems, CTLStar.toks, theta_toks, Item.toks]

/-- The prefix block of level `k`. -/
def formulaBlock (C : List MGate) (k : ℕ) : List Tok :=
  (wrapItems (gateAt C k)).flatMap (Item.toks k)

lemma levelFormula_toks (C : List MGate) (n : ℕ) :
    (levelFormula C n).toks =
      (List.range n).reverse.flatMap (formulaBlock C) ++ (CTLStar.ap aInit).toks := by
  induction n with
  | zero => simp [levelFormula]
  | succ n ih =>
    rw [levelFormula, wrap_toks, ih, List.range_succ, List.reverse_append]
    simp [formulaBlock]

/-! ## The tree -/

/-- The block of the tree belonging to gate `g`: the opening of `R_g`, its label, its side
leaf, and the opening of `D_g` with its label. -/
def treeBlock (C : List MGate) (g : ℕ) : List Tok :=
  [Tok.lpar] ++ finsetToks (regLabel C g) ++ sideLeaf.toks ++ [Tok.lpar] ++
    ([Tok.lpar] ++ natToks (4 * g + 2) ++ [Tok.rpar])

lemma finsetToks_singleton (a : ℕ) : finsetToks {a} = [Tok.lpar] ++ natToks a ++ [Tok.rpar] := by
  simp [finsetToks]

lemma spine_toks (C : List MGate) (g : ℕ) :
    (spine C (2 * g + 1)).toks =
      (List.range (g + 1)).reverse.flatMap (treeBlock C) ++ List.replicate (2 * (g + 1)) Tok.rpar := by
  induction g with
  | zero =>
    simp [spine, LTree.toks, LTree.toksList, treeBlock, finsetToks_singleton, aDum]
  | succ g ih =>
    have e1 : spine C (2 * (g + 1) + 1) = .node (regLabel C (g + 1)) [sideLeaf, spine C (2 * g + 2)] := by
      rw [show 2 * (g + 1) + 1 = (2 * g + 2) + 1 by ring, spine]
      rw [if_pos (by omega)]
      congr 2; omega
    have e2 : spine C (2 * g + 2) = .node {aDum (g + 1)} [spine C (2 * g + 1)] := by
      rw [show 2 * g + 2 = (2 * g + 1) + 1 by ring, spine]
      rw [if_neg (by omega)]
      congr 3; omega
    rw [e1]
    simp only [LTree.toks, LTree.toksList, e2, ih]
    rw [show List.range (g + 1 + 1) = List.range (g + 1) ++ [g + 1] from List.range_succ,
      List.reverse_append]
    have hr : List.replicate (2 * (g + 1 + 1)) Tok.rpar =
        List.replicate (2 * (g + 1)) Tok.rpar ++ [Tok.rpar, Tok.rpar] := by
      rw [show 2 * (g + 1 + 1) = 2 * (g + 1) + 2 by ring, List.replicate_add]; rfl
    rw [hr]
    simp [treeBlock, finsetToks_singleton, aDum, mul_add]

lemma reductionTree_toks (C : List MGate) (hC : C ≠ []) :
    (reductionTree C).toks =
      (List.range C.length).reverse.flatMap (treeBlock C) ++
        List.replicate (2 * C.length) Tok.rpar := by
  have : C.length - 1 + 1 = C.length := by
    have := List.length_pos_iff.2 hC; omega
  rw [reductionTree, spine_toks, this]

/-! ## Labels -/

/-- The sorted label of register `R_g`. -/
def labelList (C : List MGate) (g : ℕ) : List ℕ :=
  (if g = 0 then [aAct 0] ++ (if (gateAt C g).isTrue then [aInit] else [])
    else (if (gateAt C g).isTrue then [aInit] else []) ++ [aAct g]) ++
  ((List.range C.length).filter (fun k => decide ((gateAt C k).reads g))).map aIn

lemma reads_lt {C : List MGate} (hC : WellFormed C) {k g : ℕ} (h : (gateAt C k).reads g) :
    g < k := by
  have := gateOk_of_wellFormed hC k
  cases hk : gateAt C k with
  | input b => rw [hk] at h; exact h.elim
  | and i j =>
    rw [hk] at h this
    rcases h with rfl | rfl
    · exact this.1
    · exact this.2
  | or i j =>
    rw [hk] at h this
    rcases h with rfl | rfl
    · exact this.1
    · exact this.2

lemma labelList_pairwise {C : List MGate} (hC : WellFormed C) (g : ℕ) :
    (labelList C g).Pairwise (· < ·) := by
  unfold labelList
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · split_ifs <;> simp [aAct, aInit]
    omega
  · rw [List.pairwise_map]
    refine List.Pairwise.filter _ ?_
    refine List.Pairwise.imp ?_ (List.pairwise_lt_range)
    intro a b h; simp [aIn]; omega
  · intro a ha b hb
    simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb
    obtain ⟨k, ⟨-, hk⟩, rfl⟩ := hb
    have := reads_lt hC hk
    split_ifs at ha <;> simp [aAct, aInit] at ha <;> rcases ha with rfl | rfl <;>
      simp [aIn] <;> omega

lemma labelList_toFinset (C : List MGate) (g : ℕ) : (labelList C g).toFinset = regLabel C g := by
  ext x
  rw [List.mem_toFinset, mem_regLabel]
  unfold labelList
  simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  split_ifs with h1 h2 h2
  · subst h1; simp [h2]
    generalize (∃ a, (a < C.length ∧ (gateAt C a).reads 0) ∧ aIn a = x) = P
    tauto
  · subst h1; simp [h2]
  · simp [h2]
    generalize (∃ a, (a < C.length ∧ (gateAt C a).reads g) ∧ aIn a = x) = P
    tauto
  · simp [h2]

lemma regLabel_sort {C : List MGate} (hC : WellFormed C) (g : ℕ) :
    (regLabel C g).sort (· ≤ ·) = labelList C g := by
  have hp := labelList_pairwise hC g
  rw [← labelList_toFinset]
  exact (List.toFinset_sort (· ≤ ·) hp.nodup).2 (hp.imp le_of_lt)

lemma finsetToks_regLabel {C : List MGate} (hC : WellFormed C) (g : ℕ) :
    finsetToks (regLabel C g) = Tok.lpar :: ((labelList C g).flatMap natToks ++ [Tok.rpar]) := by
  rw [finsetToks, regLabel_sort hC]

end MCVPReduction

end PathChecking
