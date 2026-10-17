module

public import RequestProject.CTLTree.Emit

/-!
# The query of a round for a node and a formula position

For the node at position `u` (size `Z = sz u`) and the CTL subformula at position `j`, the query
`CQ ts m M u j A` is the LTL path checking instance consisting of the translation `trC m χ j`
and the lasso word of the chain `chainF ts Z u` (the node positions `q` inside `u` with
`Z ≤ 2 sz q`).  The node letter of `q` is its label renamed by `gm m`, the exit letter contains
`0`, `1` (at the last chain node if it is not a leaf) and `k + 2` for every position `k` with
`offv ts A Z q k` (the value of the `EX`, `EU` or `AU` subformula at `k` through the small kids
of `q`, read from the answers `A` of the previous round).
-/

@[expose] public section

namespace PathChecking

namespace CTLT

open CTLP MCVPReduction ShallowP LS

variable {ts : List Tok}

/-! ## Definitions -/

/-- `c` is a small kid of `q` (size `< Z / 2`). -/
def smallKid (ts : List Tok) (Z q c : ℕ) : Bool := kidP ts q c && decide (2 * sz ts c < Z)

/-- Some small kid of `q` satisfies `P`. -/
def anyKid (ts : List Tok) (Z q : ℕ) (P : ℕ → Bool) : Bool :=
  (List.range (sz ts q)).any fun i => smallKid ts Z q (q + i) && P (q + i)

/-- All small kids of `q` satisfy `P`. -/
def allKid (ts : List Tok) (Z q : ℕ) (P : ℕ → Bool) : Bool :=
  (List.range (sz ts q)).all fun i => !smallKid ts Z q (q + i) || P (q + i)

/-- Value of the fresh proposition `k + 2` at the exit letter of `q`. -/
def offv (ts : List Tok) (A : ℕ → ℕ → Bool) (Z q k : ℕ) : Bool :=
  if tc ts k = 9 then anyKid ts Z q (fun c => A c (k + 1))
  else if tc ts k = 10 then anyKid ts Z q (fun c => A c k)
  else if tc ts k = 11 then allKid ts Z q (fun c => A c k)
  else false

/-- Elements of the exit letter of `q`. -/
def exList (ts : List Tok) (M : ℕ) (A : ℕ → ℕ → Bool) (Z q : ℕ) (e : Bool) : List ℕ :=
  0 :: ((if e then [1] else []) ++ ((List.range M).filter (offv ts A Z q)).map (· + 2))

/-- Tokens of the exit letter of `q`. -/
def exToks (ts : List Tok) (M : ℕ) (A : ℕ → ℕ → Bool) (Z q : ℕ) (e : Bool) : List Tok :=
  Tok.lpar :: (natToks 0 ++ ((if e then natToks 1 else []) ++
    ((List.range M).flatMap (fun k => if offv ts A Z q k then natToks (k + 2) else []) ++
      [Tok.rpar])))

/-- Tokens of the node letter of `q`. -/
def ndToks (ts : List Tok) (m q : ℕ) : List Tok := Tok.lpar :: (labG ts m q ++ [Tok.rpar])

/-- Membership in the chain of `u`. -/
def inChain (ts : List Tok) (u q : ℕ) : Prop := isNode ts q = true ∧ sz ts u ≤ 2 * sz ts q

instance (u q : ℕ) : Decidable (inChain ts u q) := by unfold inChain; infer_instance

/-- The stem of the lasso. -/
def stemC (ts : List Tok) (m M : ℕ) (A : ℕ → ℕ → Bool) (u : ℕ) : List Tok :=
  rngL u (sz ts u) fun q => if inChain ts u q then
    ndToks ts m q ++ (if noBig ts (sz ts u) q then [] else exToks ts M A (sz ts u) q false)
  else []

/-- The loop of the lasso. -/
def loopC (ts : List Tok) (m M : ℕ) (A : ℕ → ℕ → Bool) (u : ℕ) : List Tok :=
  rngL u (sz ts u) fun q => if inChain ts u q then
    (if noBig ts (sz ts u) q then exToks ts M A (sz ts u) q (!isLeaf ts q) ++
      (if isLeaf ts q then ndToks ts m q else []) else [])
  else []

/-- **The query** for the node at `u` and the formula position `j`. -/
def CQ (ts : List Tok) (m M u j : ℕ) (A : ℕ → ℕ → Bool) : List Tok :=
  Tok.lpar :: (trCToks ts m j ++ Tok.rpar :: (Tok.lpar :: (stemC ts m M A u ++
    Tok.rpar :: Tok.lpar :: (loopC ts m M A u ++ [Tok.rpar]))))

/-! ## Generic lemmas -/

lemma rngL_sel {α : Type*} (a n : ℕ) (P : ℕ → Prop) [DecidablePred P] (g : ℕ → List α) :
    rngL a n (fun q => if P q then g q else []) =
      (rngL a n (fun q => if P q then [q] else [])).flatMap g := by
  unfold rngL
  rw [List.flatMap_assoc]
  refine List.flatMap_congr fun i _ => ?_
  dsimp only
  split_ifs <;> simp

lemma flatMap_pairs_getD {α β : Type*} (f g : α → β) (d : β) :
    ∀ (l : List α) (i : ℕ) (h : i < l.length),
      (l.flatMap fun q => [f q, g q]).getD (2 * i) d = f l[i] ∧
      (l.flatMap fun q => [f q, g q]).getD (2 * i + 1) d = g l[i] := by
  intro l
  induction l with
  | nil => intro i h; simp at h
  | cons x l ih =>
    intro i h
    cases i with
    | zero => simp
    | succ i =>
      have := ih i (by simpa using h)
      simp only [List.flatMap_cons, List.getD_eq_getElem?_getD] at this ⊢
      rw [show 2 * (i + 1) = 2 * i + 2 by ring, show 2 * i + 2 + 1 = 2 * i + 1 + 2 by ring]
      simp only [List.cons_append, List.getElem?_cons_succ, List.nil_append]
      simpa using this

lemma flatMap_pairs_length {α β : Type*} (f g : α → β) (l : List α) :
    (l.flatMap fun q => [f q, g q]).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]; ring

/-! ## The letters -/

/-- The node letter of `q`. -/
noncomputable def ndS (ts : List Tok) (m q : ℕ) : Finset ℕ :=
  (letterList m 0 (fun _ => false) (sub ts q).label).toFinset

/-- The exit letter of `q`. -/
def exS (ts : List Tok) (M : ℕ) (A : ℕ → ℕ → Bool) (Z q : ℕ) (e : Bool) : Finset ℕ :=
  (exList ts M A Z q e).toFinset

lemma ndToks_eq {m q : ℕ} (hm : 1 < 2 ^ m) {s : LTree} {R : List Tok}
    (h : ts.drop q = s.toks ++ R) : ndToks ts m q = finsetToks (ndS ts m q) := by
  obtain ⟨l, cs⟩ := s
  have hl := letter_toks m 0 (by simpa using hm) (fun _ => false) l
  simp only [freshToks, List.range_zero, List.flatMap_nil, List.nil_append] at hl
  rw [ndS, sub_eq h, ndToks, labG_eq m h]
  simpa [LTree.label] using hl

lemma exList_sorted (M : ℕ) (A : ℕ → ℕ → Bool) (Z q : ℕ) (e : Bool) :
    (exList ts M A Z q e).Pairwise (· < ·) := by
  unfold exList
  rw [List.pairwise_cons]
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, List.mem_map,
      List.mem_filter, List.mem_range] at ha
    rcases ha with ⟨-, rfl⟩ | ⟨k, -, rfl⟩ <;> omega
  · rw [List.pairwise_append]
    refine ⟨by split <;> simp, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact (List.pairwise_lt_range.filter _).imp (fun h => by omega)
    · intro a ha b hb
      simp only [List.mem_ite_nil_right, List.mem_singleton] at ha
      simp only [List.mem_map, List.mem_filter, List.mem_range] at hb
      obtain ⟨-, rfl⟩ := ha
      obtain ⟨k, -, rfl⟩ := hb
      omega

lemma exToks_eq (M : ℕ) (A : ℕ → ℕ → Bool) (Z q : ℕ) (e : Bool) :
    exToks ts M A Z q e = finsetToks (exS ts M A Z q e) := by
  rw [exS, finsetToks, sort_toFinset_of_sorted _ (exList_sorted M A Z q e), exToks, exList]
  simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_map, List.append_assoc]
  congr 3
  · split <;> simp
  · rw [flatMap_ite_filter]

lemma mem_exS_zero (M : ℕ) (A : ℕ → ℕ → Bool) (Z q : ℕ) (e : Bool) : 0 ∈ exS ts M A Z q e := by
  simp [exS, exList]

lemma mem_exS_one (M : ℕ) (A : ℕ → ℕ → Bool) (Z q : ℕ) (e : Bool) :
    1 ∈ exS ts M A Z q e ↔ e = true := by
  cases e <;> simp [exS, exList]

lemma mem_exS_fresh (M : ℕ) (A : ℕ → ℕ → Bool) (Z q : ℕ) (e : Bool) {k : ℕ} (hk : k < M) :
    k + 2 ∈ exS ts M A Z q e ↔ offv ts A Z q k = true := by
  cases e <;> simp [exS, exList, hk]

lemma mem_ndS_gm (m q a : ℕ) (hm : 1 < 2 ^ m) : gm m a ∈ ndS ts m q ↔ a ∈ (sub ts q).label :=
  mem_letterList_gm m 0 (by simpa using hm) _ _ a

lemma not_mem_ndS (m q n : ℕ) (hn : n + 1 < 2 ^ m) : n ∉ ndS ts m q := by
  simp only [ndS, letterList, List.range_zero, List.filter_nil, List.map_nil, List.nil_append,
    List.mem_toFinset, List.mem_map, Finset.mem_sort, not_exists, not_and]
  intro a _ he
  simp only [gm] at he
  have : 0 ≤ a * 2 ^ m := Nat.zero_le _
  omega

/-! ## The lasso -/

/-- The stem of the lasso of the chain `L` with last element `ql`. -/
noncomputable def stemL (ts : List Tok) (m M : ℕ) (A : ℕ → ℕ → Bool) (Z : ℕ) (L : List ℕ)
    (ql : ℕ) : List (Finset ℕ) :=
  L.dropLast.flatMap (fun q => [ndS ts m q, exS ts M A Z q false]) ++ [ndS ts m ql]

/-- The loop of the lasso of the chain with last element `ql`. -/
noncomputable def loopL (ts : List Tok) (m M : ℕ) (A : ℕ → ℕ → Bool) (Z ql : ℕ) :
    List (Finset ℕ) :=
  exS ts M A Z ql (!isLeaf ts ql) :: (if isLeaf ts ql then [ndS ts m ql] else [])

/-- The lasso of the chain `L` with last element `ql`. -/
noncomputable def lassoC (ts : List Tok) (m M : ℕ) (A : ℕ → ℕ → Bool) (Z : ℕ) (L : List ℕ)
    (ql : ℕ) : LassoPath :=
  ⟨stemL ts m M A Z L ql, loopL ts m M A Z ql, by simp [loopL]⟩

lemma flatMap_last {α β : Type*} (L : List α) (hne : L ≠ []) (p : α → Bool)
    (hp : ∀ i (h : i < L.length), p L[i] = true ↔ i + 1 = L.length) (f1 f2 : α → List β) :
    L.flatMap (fun q => if p q = true then f1 q else f2 q) =
      L.dropLast.flatMap f2 ++ f1 (L.getLast hne) := by
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [List.flatMap_append, List.flatMap_singleton]
  have hlast : p (L.getLast hne) = true := by
    rw [List.getLast_eq_getElem, hp]; have := List.length_pos_iff.2 hne; omega
  rw [if_pos hlast]
  congr 1
  refine List.flatMap_congr fun q hq => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
  rw [List.getElem_dropLast]
  rw [if_neg]
  rw [hp]; simp at hi; omega

lemma chainF_eq_rng (u : ℕ) :
    rngL u (sz ts u) (fun q => if inChain ts u q then [q] else []) = chainF ts (sz ts u) u := by
  unfold chainF chainSel
  rfl

lemma stemC_eq {m M : ℕ} (A : ℕ → ℕ → Bool) {u : ℕ} (hm : 1 < 2 ^ m) {L : List ℕ}
    (hL : chainF ts (sz ts u) u = L) (hne : L ≠ [])
    (hnode : ∀ q ∈ L, ∃ (s : LTree) (R : List Tok), ts.drop q = s.toks ++ R)
    (hnb : ∀ i (h : i < L.length), noBig ts (sz ts u) L[i] = true ↔ i + 1 = L.length) :
    stemC ts m M A u = (stemL ts m M A (sz ts u) L (L.getLast hne)).flatMap finsetToks ∧
    loopC ts m M A u = (loopL ts m M A (sz ts u) (L.getLast hne)).flatMap finsetToks := by
  have hnd : ∀ q ∈ L, ndToks ts m q = finsetToks (ndS ts m q) := fun q hq => by
    obtain ⟨s, R, h⟩ := hnode q hq
    exact ndToks_eq hm h
  constructor
  · rw [stemC, rngL_sel, chainF_eq_rng, hL]
    have e : ∀ q, (ndToks ts m q ++ if noBig ts (sz ts u) q = true then []
        else exToks ts M A (sz ts u) q false) = if noBig ts (sz ts u) q = true then ndToks ts m q
        else ndToks ts m q ++ exToks ts M A (sz ts u) q false := fun q => by split <;> simp
    simp only [e]
    rw [flatMap_last L hne _ hnb, stemL, List.flatMap_append, List.flatMap_assoc]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    congr 1
    · refine List.flatMap_congr fun q hq => ?_
      rw [hnd q (List.mem_of_mem_dropLast hq), exToks_eq]
    · exact hnd _ (List.getLast_mem hne)
  · rw [loopC, rngL_sel, chainF_eq_rng, hL]
    have e : ∀ q, (if noBig ts (sz ts u) q = true then exToks ts M A (sz ts u) q (!isLeaf ts q) ++
        (if isLeaf ts q = true then ndToks ts m q else []) else []) =
        if noBig ts (sz ts u) q = true then exToks ts M A (sz ts u) q (!isLeaf ts q) ++
        (if isLeaf ts q = true then ndToks ts m q else []) else [] := fun q => rfl
    rw [flatMap_last L hne _ hnb (fun q => exToks ts M A (sz ts u) q (!isLeaf ts q) ++
        (if isLeaf ts q = true then ndToks ts m q else [])) (fun _ => [])]
    rw [show L.dropLast.flatMap (fun _ => ([] : List Tok)) = [] by
      simp [List.flatMap_eq_nil_iff]]
    simp only [List.nil_append, loopL, List.flatMap_cons, exToks_eq]
    congr 1
    split
    · simp [hnd _ (List.getLast_mem hne)]
    · simp

lemma stemL_length (m M : ℕ) (A : ℕ → ℕ → Bool) (Z : ℕ) (L : List ℕ) (ql : ℕ) :
    (stemL ts m M A Z L ql).length = 2 * (L.length - 1) + 1 := by
  simp only [stemL, List.length_append, flatMap_pairs_length, List.length_dropLast,
    List.length_singleton]

lemma lassoC_letter_lt {m M : ℕ} (A : ℕ → ℕ → Bool) (Z : ℕ) (L : List ℕ) (ql : ℕ) {n : ℕ}
    (hn : n < 2 * (L.length - 1) + 1) :
    (lassoC ts m M A Z L ql).letter n = (stemL ts m M A Z L ql).getD n ∅ := by
  simp only [LassoPath.letter, lassoC, stemL_length, if_pos hn]

lemma lassoC_letter_ge {m M : ℕ} (A : ℕ → ℕ → Bool) (Z : ℕ) (L : List ℕ) (ql : ℕ) {n : ℕ}
    (hn : 2 * (L.length - 1) + 1 ≤ n) :
    (lassoC ts m M A Z L ql).letter n = (loopL ts m M A Z ql).getD
      ((n - (2 * (L.length - 1) + 1)) % (loopL ts m M A Z ql).length) ∅ := by
  simp only [LassoPath.letter, lassoC, stemL_length,
    if_neg (show ¬ n < 2 * (L.length - 1) + 1 by omega)]

lemma lassoC_node {m M : ℕ} (A : ℕ → ℕ → Bool) (Z : ℕ) (L : List ℕ) (hne : L ≠ [])
    (i : ℕ) (h : i < L.length) :
    (lassoC ts m M A Z L (L.getLast hne)).letter (2 * i) = ndS ts m L[i] ∧
    (lassoC ts m M A Z L (L.getLast hne)).letter (2 * i + 1) =
      exS ts M A Z L[i] (decide (i + 1 = L.length) && !isLeaf ts L[i]) := by
  rcases Nat.lt_or_ge (i + 1) L.length with hi | hi
  · have hd : i < L.dropLast.length := by simp; omega
    have hp := flatMap_pairs_getD (ndS ts m) (fun q => exS ts M A Z q false) ∅ L.dropLast i hd
    have hlen := flatMap_pairs_length (ndS ts m) (fun q => exS ts M A Z q false) L.dropLast
    simp only [List.length_dropLast] at hlen
    rw [lassoC_letter_lt A Z L _ (by omega), lassoC_letter_lt A Z L _ (by omega), stemL,
      List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), hp.1, hp.2,
      List.getElem_dropLast]
    simp [show i + 1 ≠ L.length by omega]
  · have hi' : i = L.length - 1 := by omega
    have hql : L.getLast hne = L[i] := by rw [List.getLast_eq_getElem]; congr 1; omega
    have hlen := flatMap_pairs_length (ndS ts m) (fun q => exS ts M A Z q false) L.dropLast
    simp only [List.length_dropLast] at hlen
    constructor
    · rw [lassoC_letter_lt A Z L _ (by omega), stemL, List.getD_append_right _ _ _ _ (by omega)]
      rw [show 2 * i - (List.flatMap (fun q => [ndS ts m q, exS ts M A Z q false])
        L.dropLast).length = 0 by omega, hql]
      simp
    · rw [lassoC_letter_ge A Z L _ (by omega), show 2 * i + 1 - (2 * (L.length - 1) + 1) = 0 by
        omega, Nat.zero_mod, hql]
      simp [loopL, show i + 1 = L.length by omega]

lemma lassoC_tail_leaf {m M : ℕ} (A : ℕ → ℕ → Bool) (Z : ℕ) (L : List ℕ) (hne : L ≠ [])
    (hl : isLeaf ts (L.getLast hne) = true) (n : ℕ) (hn : 2 * (L.length - 1) ≤ n) :
    (lassoC ts m M A Z L (L.getLast hne)).letter (n + 2) =
      (lassoC ts m M A Z L (L.getLast hne)).letter n := by
  have hll : (loopL ts m M A Z (L.getLast hne)).length = 2 := by simp [loopL, hl]
  rcases Nat.eq_or_lt_of_le hn with h | h
  · subst h
    have hS := flatMap_pairs_length (ndS ts m) (fun q => exS ts M A Z q false) L.dropLast
    simp only [List.length_dropLast] at hS
    rw [lassoC_letter_ge A Z L _ (by omega), hll, lassoC_letter_lt A Z L _ (by omega), stemL,
      List.getD_append_right _ _ _ _ (by omega), hS, Nat.sub_self,
      show 2 * (L.length - 1) + 2 - (2 * (L.length - 1) + 1) = 1 by omega]
    simp [loopL, hl]
  · rw [lassoC_letter_ge A Z L _ (by omega), lassoC_letter_ge A Z L _ (by omega), hll,
      show n + 2 - (2 * (L.length - 1) + 1) = (n - (2 * (L.length - 1) + 1)) + 2 by omega,
      Nat.add_mod_right]

lemma lassoC_tail_node {m M : ℕ} (A : ℕ → ℕ → Bool) (Z : ℕ) (L : List ℕ) (hne : L ≠ [])
    (hl : isLeaf ts (L.getLast hne) = false) (n : ℕ) (hn : 2 * (L.length - 1) + 1 ≤ n) :
    (lassoC ts m M A Z L (L.getLast hne)).letter (n + 1) =
      (lassoC ts m M A Z L (L.getLast hne)).letter n := by
  have hll : (loopL ts m M A Z (L.getLast hne)).length = 1 := by simp [loopL, hl]
  rw [lassoC_letter_ge A Z L _ (by omega), lassoC_letter_ge A Z L _ (by omega), hll,
    Nat.mod_one, Nat.mod_one]

end CTLT

end PathChecking
