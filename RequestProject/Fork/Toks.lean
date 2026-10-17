module

public import RequestProject.Fork.Construction
public import RequestProject.MCVP.OutReads

/-!
# The token lists of the single-fork reduction, in a form suitable for streaming

* the formula `forkFormula C` is a concatenation of prefix blocks, one per gate (from the last
  gate down to gate `0`), followed by `init`;
* the tree `forkTree C` is a concatenation of blocks `( label(R_g)`, one per gate (from the
  last gate down to gate `0`), followed by the two leaves and `n` closing brackets.
-/

@[expose] public section

namespace PathChecking

namespace MCVPReduction

/-! ## The formula -/

lemma natToks_two : natToks 2 = [Tok.zero, Tok.one, Tok.sep] := by
  simp [natToks, Nat.bits, Nat.binaryRec]

open Item in
/-- Items of the prefix of `forkTheta k p` (before `p`). -/
def forkThetaItems : List Item :=
  [lit (.tag 3)] ++
  [lit (.tag 2), lit (.tag 3), lit (.tag 2), lit (.tag 0), num 1, lit (.tag 2),
    lit (.tag 5), lit (.tag 1), lit (.tag 0), lit .sep] ++
  [lit (.tag 5), lit (.tag 5), lit (.tag 1), lit (.tag 0), lit .zero, lit .one, lit .sep] ++
  [lit (.tag 3)] ++
  [lit (.tag 2), lit (.tag 3), lit (.tag 2), lit (.tag 0), num 3, lit (.tag 2), lit (.tag 3),
    lit (.tag 2), lit (.tag 0), num 1, lit (.tag 5), lit (.tag 1), lit (.tag 0), lit .sep]

/-- Items of the prefix of `forkWrap k G p` (before `p`). -/
def forkWrapItems : MGate → List Item
  | .input _ => []
  | .or _ _ => .lit (.tag 6) :: forkThetaItems
  | .and _ _ => [.lit (.tag 2), .lit (.tag 6)] ++ forkThetaItems ++ [.lit (.tag 2)]

lemma forkWrapItems_num_le (G : MGate) : ∀ c, Item.num c ∈ forkWrapItems G → c ≤ 3 := by
  cases G <;> simp [forkWrapItems, forkThetaItems]

lemma forkTheta_toks (k : ℕ) (p : CTLStar) :
    (forkTheta k p).toks = forkThetaItems.flatMap (Item.toks k) ++ p.toks := by
  simp [forkTheta, cOr, cF, CTLStar.toks, forkThetaItems, Item.toks, aAct, aIn, aSelf, aWalk,
    natToks_zero, natToks_two]

lemma forkWrap_toks (k : ℕ) (G : MGate) (p : CTLStar) :
    (forkWrap k G p).toks = (forkWrapItems G).flatMap (Item.toks k) ++ p.toks := by
  cases G with
  | input b => simp [forkWrap, forkWrapItems]
  | or i j => simp [forkWrap, forkWrapItems, CTLStar.toks, forkTheta_toks, Item.toks]
  | and i j => simp [forkWrap, forkWrapItems, CTLStar.toks, forkTheta_toks, Item.toks]

/-- The prefix block of level `k`. -/
def forkFormulaBlock (C : List MGate) (k : ℕ) : List Tok :=
  (forkWrapItems (gateAt C k)).flatMap (Item.toks k)

lemma forkLevel_toks (C : List MGate) (n : ℕ) :
    (forkLevel C n).toks =
      (List.range n).reverse.flatMap (forkFormulaBlock C) ++ (CTLStar.ap aInit).toks := by
  induction n with
  | zero => simp [forkLevel]
  | succ n ih =>
    rw [forkLevel, forkWrap_toks, ih, List.range_succ, List.reverse_append]
    simp [forkFormulaBlock]

/-! ## The tree -/

/-- The block of the tree belonging to gate `g`: the opening of `R_g` and its label. -/
def forkTreeBlock (C : List MGate) (g : ℕ) : List Tok := [Tok.lpar] ++ finsetToks (regLabel C g)

lemma fspine_toks (C : List MGate) (g : ℕ) :
    (fspine C g).toks =
      (List.range (g + 1)).reverse.flatMap (forkTreeBlock C) ++
        (selfLeaf.toks ++ walkLeaf.toks) ++ List.replicate (g + 1) Tok.rpar := by
  induction g with
  | zero => simp [fspine, LTree.toks, LTree.toksList, forkTreeBlock]
  | succ g ih =>
    have e : (fspine C (g + 1)).toks =
        Tok.lpar :: (finsetToks (regLabel C (g + 1)) ++ (fspine C g).toks ++ [Tok.rpar]) := by
      simp [fspine, LTree.toks, LTree.toksList]
    rw [e, ih, List.range_succ (n := g + 1), List.reverse_append,
      List.replicate_succ' (n := g + 1)]
    simp [forkTreeBlock]

lemma forkTree_toks (C : List MGate) (hC : C ≠ []) :
    (forkTree C).toks =
      (List.range C.length).reverse.flatMap (forkTreeBlock C) ++
        (selfLeaf.toks ++ walkLeaf.toks) ++ List.replicate C.length Tok.rpar := by
  have : C.length - 1 + 1 = C.length := by
    have := List.length_pos_iff.2 hC; omega
  rw [forkTree, fspine_toks, this]

lemma forkTreeBlock_eq {C : List MGate} (hC : WellFormed C) (g : ℕ) :
    forkTreeBlock C g = [Tok.lpar, Tok.lpar] ++ headToks C g ++
      (List.range C.length).flatMap (readsToks C g) ++ [Tok.rpar] := by
  rw [forkTreeBlock, finsetToks_regLabel hC, labelList_flatMap]
  simp

end MCVPReduction

end PathChecking
