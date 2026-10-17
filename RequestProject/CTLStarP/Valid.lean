module

public import RequestProject.CTLStarP.Scan

/-!
# Recognising encodings of CTL* tree checking instances

Pure, position-based checks on a token list that the decision procedure computes, and the
proof that they recognise exactly the encodings `( φ ) t` of pairs of a CTL* formula and a
tree:

* `numOK`: a canonical binary number (digits, least significant first, no trailing zero,
  followed by `sep`);
* `cmpScan`: comparison of two binary numbers by a simultaneous scan;
* `labSuf`, `validLab`: a strictly increasing list of numbers, closed by `)`;
* `kidsOK`, `validT`: trees;
* `validF`: formulas in prefix notation;
* `validTop`: the whole instance.
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open LS MCVPReduction

variable (ts : List Tok)

/-! ## Numbers -/

/-- Digits followed by `sep`; `ok` records whether the digits so far are canonical. -/
def digitsOK (p : ℕ) (ok : Bool) : Bool :=
  if ts.length ≤ p then false
  else if tc ts p = 2 then ok
  else if tc ts p = 0 then digitsOK (p + 1) false
  else if tc ts p = 1 then digitsOK (p + 1) true
  else false
termination_by ts.length - p

/-- A canonical binary number starts at `p`. -/
def numOK (p : ℕ) : Bool := digitsOK ts p true

/-- The digit at position `p`, if any. -/
def dig (p : ℕ) : Option Bool :=
  if tc ts p = 0 then some false else if tc ts p = 1 then some true else none

lemma lt_of_dig {p : ℕ} {b : Bool} (h : dig ts p = some b) : p < ts.length := by
  apply lt_of_tc_ne (ts := ts)
  intro h'; simp [dig, h'] at h

/-- Simultaneous scan of two binary numbers (least significant digit first); `acc` is the
result of comparing the lower parts. -/
def cmpScan (p q : ℕ) (acc : Bool) : Bool :=
  match hp : dig ts p, hq : dig ts q with
  | none, none => acc
  | some x, none => cmpScan (p + 1) q (if x then false else acc)
  | none, some y => cmpScan p (q + 1) (if y then true else acc)
  | some x, some y => cmpScan (p + 1) (q + 1) (if x = y then acc else y)
termination_by (ts.length - p) + (ts.length - q)
decreasing_by
  all_goals first
    | (have := lt_of_dig ts hp; omega)
    | (have := lt_of_dig ts hq; omega)

/-- `a ≤ b` for the numbers at `p` and `q`. -/
def numLe (p q : ℕ) : Bool := cmpScan ts p q true
/-- `a < b` for the numbers at `p` and `q`. -/
def numLt (p q : ℕ) : Bool := cmpScan ts p q false
/-- `a = b` for the numbers at `p` and `q`. -/
def numEq (p q : ℕ) : Bool := numLe ts p q && numLe ts q p

/-! ## Labels and trees -/

/-- A strictly increasing list of numbers followed by `)` starts at `q`. -/
def labSuf (q : ℕ) : Bool :=
  if h : ts.length ≤ q then false
  else if tc ts q = 4 then true
  else numOK ts q && (tc ts (numEnd ts q) == 4 || numLt ts q (numEnd ts q)) &&
    labSuf (numEnd ts q)
termination_by ts.length - q
decreasing_by have := lt_scan (ts := ts) upN downN 1 (show q < ts.length by omega); simp only [numEnd]; omega

/-- A label starts at `p`. -/
def validLab (p : ℕ) : Bool := tc ts p == 3 && labSuf ts (p + 1)

/-- A (possibly empty) list of trees followed by `)` starts at `c`. -/
def kidsOK (c : ℕ) : Bool :=
  if h : ts.length ≤ c then false
  else if tc ts c = 4 then true
  else tc ts c == 3 && validLab ts (c + 1) && kidsOK (tend ts (c + 1)) && kidsOK (tend ts c)
termination_by ts.length - c
decreasing_by
  all_goals simp only [tend]
  · have := le_scan (ts := ts) upT downT (c + 1) 0; omega
  · have := lt_scan (ts := ts) upT downT 0 (show c < ts.length by omega); omega

/-- A tree starts at `u`. -/
def validT (u : ℕ) : Bool := tc ts u == 3 && validLab ts (u + 1) && kidsOK ts (tend ts (u + 1))

/-- A formula starts at `j`. -/
def validF (j : ℕ) : Bool :=
  if h : ts.length ≤ j then false
  else if tc ts j = 5 then numOK ts (j + 1)
  else if tc ts j = 6 then true
  else if tc ts j = 7 ∨ tc ts j = 9 ∨ tc ts j = 11 then validF (j + 1)
  else if tc ts j = 8 ∨ tc ts j = 10 then validF (j + 1) && validF (fend ts (j + 1))
  else false
termination_by ts.length - j
decreasing_by
  all_goals first
    | omega
    | (simp only [fend]; have := le_scan (ts := ts) upF downF (j + 1) 1; omega)

/-- The whole token list is an instance `( φ ) t`. -/
def validTop : Bool :=
  tc ts 0 == 3 && validF ts 1 && tc ts (fend ts 1) == 4 && validT ts (fend ts 1 + 1) &&
    tend ts (fend ts 1 + 1) == ts.length

end CTLP

end PathChecking
