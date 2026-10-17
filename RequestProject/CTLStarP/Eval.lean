module

public import RequestProject.CTLStarP.ValidTree

/-!
# Evaluating CTL* formulas on encoded trees

Pure, position-based functions on a token list `ts`, computed by the decision procedure.

A tree node is identified with the position of its opening bracket.  A path through the tree
starting at node `u` is described by a *target* position `ℓ`: at each node the path moves to the
child whose encoding contains position `ℓ` (to the last child if `ℓ` lies to the right of all
children, to the first child if it lies to the left), and it stays at a leaf forever once it
reaches one (`nxt`).  Every infinite tree path arises in this way (from the position of the
leaf it reaches).

`val j u ℓ` evaluates the formula starting at position `j` on the path from `u` towards `ℓ`.
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open LS MCVPReduction

variable (ts : List Tok)

lemma tend_gt {c : ℕ} (h : ¬ ts.length ≤ c) : c < tend ts c :=
  lt_scan upT downT 0 (by omega)

/-- Among the children starting at position `c`, the one whose encoding contains `ℓ` (or the
last one, if `ℓ` lies to the right of all of them; the first one if it lies to the left). -/
def ctw (c ℓ : ℕ) : ℕ :=
  if ts.length ≤ c then c
  else if tend ts c ≤ ℓ ∧ tc ts (tend ts c) ≠ 4 then ctw (tend ts c) ℓ else c
termination_by ts.length - c
decreasing_by have := tend_gt (c := c) ts (by assumption); omega

/-- The node at position `u` is a leaf. -/
def isLeaf (u : ℕ) : Bool := tc ts (tend ts (u + 1)) == 4

/-- One step of the path towards `ℓ`. -/
def nxt (ℓ u : ℕ) : ℕ := if isLeaf ts u then u else ctw ts (tend ts (u + 1)) ℓ

/-- The number at position `q` occurs in the list of numbers starting at `p` (closed by `)`). -/
def labHas (p q : ℕ) : Bool :=
  if ts.length ≤ p then false
  else if tc ts p = 4 then false
  else numEq ts p q || labHas (numEnd ts p) q
termination_by ts.length - p
decreasing_by have := lt_scan (ts := ts) upN downN 1 (show p < ts.length by omega); simp only [numEnd]; omega

/-- The formula at position `j` holds on the path from node `u` towards position `ℓ`. -/
def val (j u ℓ : ℕ) : Bool :=
  if h : ts.length ≤ j then false
  else if tc ts j = 5 then labHas ts (u + 2) (j + 1)
  else if tc ts j = 6 then true
  else if tc ts j = 7 then !val (j + 1) u ℓ
  else if tc ts j = 8 then val (j + 1) u ℓ && val (fend ts (j + 1)) u ℓ
  else if tc ts j = 9 then (if nxt ts ℓ u < ts.length then val (j + 1) (nxt ts ℓ u) ℓ else false)
  else if tc ts j = 10 then
    val (fend ts (j + 1)) u ℓ ||
      (val (j + 1) u ℓ &&
        (if u < nxt ts ℓ u ∧ nxt ts ℓ u < ts.length then val j (nxt ts ℓ u) ℓ else false))
  else if tc ts j = 11 then (List.range ts.length).any (fun ℓ' => val (j + 1) u ℓ')
  else false
termination_by (ts.length - j, ts.length - u)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.left; have := le_scan (ts := ts) upF downF (j + 1) 1; simp only [fend]; omega)
    | (apply Prod.Lex.right; omega)

/-- The root of the tree of an instance `( φ ) t`. -/
def root : ℕ := fend ts 1 + 1

/-- **The decision procedure** (as a pure function of the token list). -/
def decideCTL : Bool :=
  validTop ts && (List.range ts.length).all (fun ℓ => val ts 1 (root ts) ℓ)

end CTLP

end PathChecking
