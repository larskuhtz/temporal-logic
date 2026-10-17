module

public import RequestProject.Encoding

/-!
# Temporal logics and their path / tree checking problems

* `LTL` over ultimately periodic (lasso) paths `u · v^ω`;
* `BLTLPast`: LTL extended with past operators (yesterday, since) and with bounded future
  and past operators `U[a,b]`, `S[a,b]` whose bounds are written in binary;
* `CTLStar` and its fragment `CTL` over finite trees.  A finite tree is turned into a
  (total) Kripke structure by letting every leaf loop to itself, so that every maximal
  path is infinite (it follows a branch and then stutters forever at the leaf).

Atomic propositions are natural numbers; a letter of a path / label of a tree node is the
finite set of atomic propositions that hold there.

For each logic we define the corresponding decision problem as a language over `Bool`:
the set of binary encodings of pairs (formula, path) resp. (formula, tree) such that the
path / tree satisfies the formula.

## References

Full entries are in `REFERENCES.md`.

* LTL: A. Pnueli, *The temporal logic of programs*, FOCS 1977 [Pnu77]; past operators:
  O. Lichtenstein, A. Pnueli, L. Zuck, *The glory of the past*, Logic of Programs 1985 [LPZ85].
* CTL: E. A. Emerson, E. M. Clarke, *Using branching time temporal logic to synthesize
  synchronization skeletons*, Sci. Comput. Program. 2(3), 1982 [EC82]; E. M. Clarke,
  E. A. Emerson, A. P. Sistla, ACM TOPLAS 8(2), 1986 [CES86]. CTL*: E. A. Emerson,
  J. Y. Halpern, *"Sometimes" and "not never" revisited*, J. ACM 33(1), 1986 [EH86].
* The path checking problem: N. Markey, Ph. Schnoebelen, *Model checking a path*, CONCUR 2003
  [MS03]. Its parallel complexity: L. Kuhtz, B. Finkbeiner, ICALP 2009 [KF09] and LMCS 8(4:10),
  2012 [KF12], which also treats LTL with past and bounded operators. CTL tree checking:
  L. Kuhtz, PhD thesis, Universität des Saarlandes, 2010 [Kuh10]. The known lower bound for LTL
  path checking is `NC¹` [DS02], the complexity of evaluating Boolean formulas [Bus87].

[KF09] and [KF12] work with finite paths. Ultimately periodic paths, as used here, are treated
in [Kuh10, Corollary 4]. We have not checked that the remaining choices made here (finite
trees whose leaves loop to themselves, the exact set of BLTL+Past operators) agree in every
detail with those works.
-/

@[expose] public section

namespace PathChecking

/-! ## Paths -/

/-- An ultimately periodic path `stem · loop^ω` with a non-empty loop. -/
structure LassoPath where
  stem : List (Finset ℕ)
  loop : List (Finset ℕ)
  loop_ne : loop ≠ []

/-- The letter at position `i` of a lasso path. -/
def LassoPath.letter (p : LassoPath) (i : ℕ) : Finset ℕ :=
  if i < p.stem.length then p.stem.getD i ∅
  else p.loop.getD ((i - p.stem.length) % p.loop.length) ∅

/-- Token encoding of a lasso path. -/
def LassoPath.toks (p : LassoPath) : List Tok :=
  Tok.lpar :: (p.stem.flatMap finsetToks ++
    (Tok.rpar :: Tok.lpar :: (p.loop.flatMap finsetToks ++ [Tok.rpar])))

/-! ## LTL -/

/-- Formulas of linear-time temporal logic (other operators are derived:
`F φ = U tt φ`, `G φ = neg (F (neg φ))`, ...). -/
inductive LTL
  | ap (a : ℕ)
  | tt
  | neg (φ : LTL)
  | and (φ ψ : LTL)
  /-- next -/
  | X (φ : LTL)
  /-- until -/
  | U (φ ψ : LTL)

/-- Satisfaction of an LTL formula at position `i` of an infinite word `w`. -/
def LTL.Sat (w : ℕ → Finset ℕ) : LTL → ℕ → Prop
  | .ap a, i => a ∈ w i
  | .tt, _ => True
  | .neg φ, i => ¬ LTL.Sat w φ i
  | .and φ ψ, i => LTL.Sat w φ i ∧ LTL.Sat w ψ i
  | .X φ, i => LTL.Sat w φ (i + 1)
  | .U φ ψ, i => ∃ k, LTL.Sat w ψ (i + k) ∧ ∀ j < k, LTL.Sat w φ (i + j)

/-- Token encoding of an LTL formula (prefix notation). -/
def LTL.toks : LTL → List Tok
  | .ap a => Tok.tag 0 :: natToks a
  | .tt => [Tok.tag 1]
  | .neg φ => Tok.tag 2 :: φ.toks
  | .and φ ψ => Tok.tag 3 :: (φ.toks ++ ψ.toks)
  | .X φ => Tok.tag 4 :: φ.toks
  | .U φ ψ => Tok.tag 5 :: (φ.toks ++ ψ.toks)

/-- **The path checking problem for LTL**: encodings of pairs `(φ, p)` of an LTL formula
and an ultimately periodic path such that `p ⊨ φ` (at position `0`). -/
def LTLPathChecking : Language :=
  {x | ∃ (φ : LTL) (p : LassoPath),
    x = encodeToks (Tok.lpar :: (φ.toks ++ (Tok.rpar :: p.toks))) ∧ LTL.Sat p.letter φ 0}

/-! ## BLTL+Past -/

/-- Formulas of LTL with past operators and bounded future and past operators. -/
inductive BLTLPast
  | ap (a : ℕ)
  | tt
  | neg (φ : BLTLPast)
  | and (φ ψ : BLTLPast)
  /-- next -/
  | X (φ : BLTLPast)
  /-- until -/
  | U (φ ψ : BLTLPast)
  /-- yesterday (previous) -/
  | Y (φ : BLTLPast)
  /-- since -/
  | S (φ ψ : BLTLPast)
  /-- bounded until `φ U[a,b] ψ` (bounds in binary) -/
  | UB (a b : ℕ) (φ ψ : BLTLPast)
  /-- bounded since `φ S[a,b] ψ` (bounds in binary) -/
  | SB (a b : ℕ) (φ ψ : BLTLPast)

/-- Satisfaction of a BLTL+Past formula at position `i` of an infinite word `w`. -/
def BLTLPast.Sat (w : ℕ → Finset ℕ) : BLTLPast → ℕ → Prop
  | .ap a, i => a ∈ w i
  | .tt, _ => True
  | .neg φ, i => ¬ BLTLPast.Sat w φ i
  | .and φ ψ, i => BLTLPast.Sat w φ i ∧ BLTLPast.Sat w ψ i
  | .X φ, i => BLTLPast.Sat w φ (i + 1)
  | .U φ ψ, i => ∃ k, BLTLPast.Sat w ψ (i + k) ∧ ∀ j < k, BLTLPast.Sat w φ (i + j)
  | .Y φ, i => 0 < i ∧ BLTLPast.Sat w φ (i - 1)
  | .S φ ψ, i => ∃ k ≤ i, BLTLPast.Sat w ψ (i - k) ∧ ∀ j < k, BLTLPast.Sat w φ (i - j)
  | .UB a b φ ψ, i => ∃ k, a ≤ k ∧ k ≤ b ∧
      BLTLPast.Sat w ψ (i + k) ∧ ∀ j < k, BLTLPast.Sat w φ (i + j)
  | .SB a b φ ψ, i => ∃ k ≤ i, a ≤ k ∧ k ≤ b ∧
      BLTLPast.Sat w ψ (i - k) ∧ ∀ j < k, BLTLPast.Sat w φ (i - j)

/-- Token encoding of a BLTL+Past formula (prefix notation, bounds in binary). -/
def BLTLPast.toks : BLTLPast → List Tok
  | .ap a => Tok.tag 0 :: natToks a
  | .tt => [Tok.tag 1]
  | .neg φ => Tok.tag 2 :: φ.toks
  | .and φ ψ => Tok.tag 3 :: (φ.toks ++ ψ.toks)
  | .X φ => Tok.tag 4 :: φ.toks
  | .U φ ψ => Tok.tag 5 :: (φ.toks ++ ψ.toks)
  | .Y φ => Tok.tag 6 :: φ.toks
  | .S φ ψ => Tok.tag 7 :: (φ.toks ++ ψ.toks)
  | .UB a b φ ψ => Tok.tag 8 :: (natToks a ++ natToks b ++ φ.toks ++ ψ.toks)
  | .SB a b φ ψ => Tok.tag 9 :: (natToks a ++ natToks b ++ φ.toks ++ ψ.toks)

/-- **The path checking problem for BLTL+Past**: encodings of pairs `(φ, p)` of a BLTL+Past
formula and an ultimately periodic path such that `p ⊨ φ` (at position `0`). -/
def BLTLPastPathChecking : Language :=
  {x | ∃ (φ : BLTLPast) (p : LassoPath),
    x = encodeToks (Tok.lpar :: (φ.toks ++ (Tok.rpar :: p.toks))) ∧ BLTLPast.Sat p.letter φ 0}

/-! ## Finite trees -/

/-- Finite node-labelled trees with ordered children. -/
inductive LTree
  | node (label : Finset ℕ) (children : List LTree)

/-- Label of the root. -/
def LTree.label : LTree → Finset ℕ
  | .node l _ => l

/-- Children of the root. -/
def LTree.children : LTree → List LTree
  | .node _ cs => cs

mutual
/-- Token encoding of a tree: `( label child₁ … childₘ )`. -/
def LTree.toks : LTree → List Tok
  | .node l cs => Tok.lpar :: (finsetToks l ++ LTree.toksList cs ++ [Tok.rpar])
/-- Token encoding of a list of trees. -/
def LTree.toksList : List LTree → List Tok
  | [] => []
  | t :: ts => LTree.toks t ++ LTree.toksList ts
end

/-- An infinite path through a tree, given as the sequence of visited subtrees: each step
goes to a child, except at a leaf, where the path stays forever. -/
def IsTreePath (π : ℕ → LTree) : Prop :=
  ∀ i, π (i + 1) ∈ (π i).children ∨ ((π i).children = [] ∧ π (i + 1) = π i)

/-! ## CTL* -/

/-- Formulas of CTL* (every formula is read as a path formula; `A φ = neg (E (neg φ))`). -/
inductive CTLStar
  | ap (a : ℕ)
  | tt
  | neg (φ : CTLStar)
  | and (φ ψ : CTLStar)
  /-- next -/
  | X (φ : CTLStar)
  /-- until -/
  | U (φ ψ : CTLStar)
  /-- existential path quantifier -/
  | E (φ : CTLStar)

/-- Satisfaction of a CTL* formula on a tree path `π`. -/
def CTLStar.Holds : CTLStar → (ℕ → LTree) → Prop
  | .ap a, π => a ∈ (π 0).label
  | .tt, _ => True
  | .neg φ, π => ¬ CTLStar.Holds φ π
  | .and φ ψ, π => CTLStar.Holds φ π ∧ CTLStar.Holds ψ π
  | .X φ, π => CTLStar.Holds φ (fun i => π (i + 1))
  | .U φ ψ, π => ∃ k, CTLStar.Holds ψ (fun i => π (i + k)) ∧
      ∀ j < k, CTLStar.Holds φ (fun i => π (i + j))
  | .E φ, π => ∃ π', IsTreePath π' ∧ π' 0 = π 0 ∧ CTLStar.Holds φ π'

/-- A tree satisfies a CTL* formula if every path starting at the root satisfies it
(for state formulas this is the usual satisfaction at the root). -/
def CTLStar.TreeSat (t : LTree) (φ : CTLStar) : Prop :=
  ∀ π, IsTreePath π → π 0 = t → CTLStar.Holds φ π

/-- Token encoding of a CTL* formula (prefix notation). -/
def CTLStar.toks : CTLStar → List Tok
  | .ap a => Tok.tag 0 :: natToks a
  | .tt => [Tok.tag 1]
  | .neg φ => Tok.tag 2 :: φ.toks
  | .and φ ψ => Tok.tag 3 :: (φ.toks ++ ψ.toks)
  | .X φ => Tok.tag 4 :: φ.toks
  | .U φ ψ => Tok.tag 5 :: (φ.toks ++ ψ.toks)
  | .E φ => Tok.tag 6 :: φ.toks

/-- **The tree checking problem for CTL***: encodings of pairs `(φ, t)` of a CTL* formula
and a finite tree such that `t ⊨ φ`. -/
def CTLStarTreeChecking : Language :=
  {x | ∃ (φ : CTLStar) (t : LTree),
    x = encodeToks (Tok.lpar :: (φ.toks ++ (Tok.rpar :: t.toks))) ∧ CTLStar.TreeSat t φ}

/-! ## CTL -/

/-- Formulas of CTL, over the adequate set of operators `EX`, `EU`, `AU`
(e.g. `AX φ = neg (EX (neg φ))`, `EF φ = EU tt φ`, `AG φ = neg (EF (neg φ))`,
`AF φ = AU tt φ`, `EG φ = neg (AF (neg φ))`). -/
inductive CTL
  | ap (a : ℕ)
  | tt
  | neg (φ : CTL)
  | and (φ ψ : CTL)
  | EX (φ : CTL)
  | EU (φ ψ : CTL)
  | AU (φ ψ : CTL)

/-- CTL as a fragment of CTL*. -/
def CTL.toCTLStar : CTL → CTLStar
  | .ap a => .ap a
  | .tt => .tt
  | .neg φ => .neg φ.toCTLStar
  | .and φ ψ => .and φ.toCTLStar ψ.toCTLStar
  | .EX φ => .E (.X φ.toCTLStar)
  | .EU φ ψ => .E (.U φ.toCTLStar ψ.toCTLStar)
  | .AU φ ψ => .neg (.E (.neg (.U φ.toCTLStar ψ.toCTLStar)))

/-- Satisfaction of a CTL formula at the root of a finite tree (via the CTL* semantics). -/
def CTL.TreeSat (t : LTree) (φ : CTL) : Prop :=
  CTLStar.TreeSat t φ.toCTLStar

/-- Token encoding of a CTL formula (prefix notation). -/
def CTL.toks : CTL → List Tok
  | .ap a => Tok.tag 0 :: natToks a
  | .tt => [Tok.tag 1]
  | .neg φ => Tok.tag 2 :: φ.toks
  | .and φ ψ => Tok.tag 3 :: (φ.toks ++ ψ.toks)
  | .EX φ => Tok.tag 4 :: φ.toks
  | .EU φ ψ => Tok.tag 5 :: (φ.toks ++ ψ.toks)
  | .AU φ ψ => Tok.tag 6 :: (φ.toks ++ ψ.toks)

/-- **The tree checking problem for CTL**: encodings of pairs `(φ, t)` of a CTL formula and
a finite tree such that `t ⊨ φ`. -/
def CTLTreeChecking : Language :=
  {x | ∃ (φ : CTL) (t : LTree),
    x = encodeToks (Tok.lpar :: (φ.toks ++ (Tok.rpar :: t.toks))) ∧ CTL.TreeSat t φ}

end PathChecking
