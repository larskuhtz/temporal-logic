module

public import RequestProject.Shallow.FSpec

/-!
# Token-by-token production of the lassos of the queries

* `stemToks` / `leafToks`: the stem and the loop letter of the tail lasso of a linear subtree,
  obtained by copying labels;
* `labG`: the label of a node with every number `a` renamed to `gm m a`;
* `letterToks`: a letter of the cyclic word of a branching round;
* `cnt`: bracket counting, used to compute depths.
-/

@[expose] public section

namespace PathChecking

namespace ShallowP

open CTLP MCVPReduction

variable {ts : List Tok}

/-! ## Counting tokens -/

/-- Number of tokens with code `c` in positions `[a, a + n)`. -/
def cnt (ts : List Tok) (c a n : ℕ) : ℕ := ((List.range n).filter fun i => tc ts (a + i) = c).length

lemma cnt_add (c a n k : ℕ) : cnt ts c a (n + k) = cnt ts c a n + cnt ts c (a + n) k := by
  simp [cnt, List.range_add, List.filter_append, List.filter_map, Function.comp_def,
    Nat.add_assoc]

lemma cnt_list (c : ℕ) {a : ℕ} {l R : List Tok} (h : ts.drop a = l ++ R) :
    cnt ts c a l.length = (l.filter fun t => t.code = c).length := by
  induction l generalizing a with
  | nil => rfl
  | cons t l ih =>
    rw [List.length_cons, Nat.add_comm, cnt_add, ih (drop_toks_cons h)]
    have : tc ts a = t.code := tc_of_drop (by rw [h]; rfl)
    simp only [cnt, List.range_one, List.filter_cons, List.filter_nil, Nat.add_zero, this]
    by_cases ht : t.code = c <;> simp [ht, Nat.add_comm]

/-- Number of tokens with code `c` in a token list. -/
def lc (c : ℕ) (l : List Tok) : ℕ := (l.filter fun t => t.code = c).length

lemma lc_append (c : ℕ) (l l' : List Tok) : lc c (l ++ l') = lc c l + lc c l' := by
  simp [lc, List.filter_append]

lemma lc_nil (c : ℕ) : lc c [] = 0 := rfl

lemma lc_cons (c : ℕ) (t : Tok) (l : List Tok) :
    lc c (t :: l) = (if t.code = c then 1 else 0) + lc c l := by
  simp only [lc, List.filter_cons]; split_ifs <;> simp_all [Nat.add_comm]

lemma lc_nums (c : ℕ) (hc : 2 < c) (xs : List ℕ) : lc c (xs.flatMap natToks) = 0 := by
  simp only [lc, List.length_eq_zero_iff, List.filter_eq_nil_iff, List.mem_flatMap,
    decide_eq_true_eq]
  rintro t ⟨x, -, hx⟩ e
  have := natToks_code_le x t hx; omega

lemma lc_finset (c : ℕ) (hc : c = 3 ∨ c = 4) (l : Finset ℕ) : lc c (finsetToks l) = 1 := by
  simp only [finsetToks, lc_cons, lc_append, lc_nums c (by omega)]
  rcases hc with rfl | rfl <;> simp [lc, Tok.code]

mutual
lemma lc_tree : ∀ t : LTree, lc 3 t.toks = lc 4 t.toks
  | .node l cs => by
    simp only [LTree.toks, lc_cons, lc_append, lc_finset 3 (by omega), lc_finset 4 (by omega),
      lc_list cs, lc_nil, Tok.code]
    simp only [if_pos, Nat.reduceEqDiff]
    omega
lemma lc_list : ∀ cs : List LTree, lc 3 (LTree.toksList cs) = lc 4 (LTree.toksList cs)
  | [] => rfl
  | t :: cs => by
    simp only [LTree.toksList, lc_append, lc_tree t, lc_list cs]
end

lemma cnt_tree {a : ℕ} {t : LTree} {R : List Tok} (h : ts.drop a = t.toks ++ R) :
    cnt ts 3 a t.toks.length = cnt ts 4 a t.toks.length := by
  rw [cnt_list 3 h, cnt_list 4 h]; exact lc_tree t

lemma cnt_one (c a : ℕ) : cnt ts c a 1 = if tc ts a = c then 1 else 0 := by
  simp [cnt, List.range_one, List.filter_cons]; split_ifs <;> simp

lemma ctw_bal (cs : List LTree) : ∀ {c : ℕ} {R : List Tok} (ℓ : ℕ), cs ≠ [] →
    ts.drop c = LTree.toksList cs ++ Tok.rpar :: R →
    c ≤ ctw ts c ℓ ∧ cnt ts 3 c (ctw ts c ℓ - c) = cnt ts 4 c (ctw ts c ℓ - c) := by
  induction cs with
  | nil => intro c R ℓ h; exact absurd rfl h
  | cons t cs ih =>
    intro c R ℓ _ h
    rw [LTree.toksList_cons, List.append_assoc] at h
    have htp := LTree.toks_length_pos t
    obtain ⟨l0, hl0⟩ := LTree.toks_head t
    have hc : c < ts.length := lt_of_drop (t := Tok.lpar) (rest := l0 ++ _) (by rw [h, hl0]; rfl)
    have hte := tend_tree t h
    have hd := drop_append_of_drop h
    rw [← hte] at hd
    cases cs with
    | nil =>
      have hd' : ts.drop (tend ts c) = Tok.rpar :: R := by simpa [LTree.toksList] using hd
      rw [ctw_eq, if_neg (by omega), if_neg (by rw [tc_of_drop hd']; simp [Tok.code])]
      simp [cnt]
    | cons t2 cs =>
      rw [ctw_eq, if_neg (by omega)]
      split_ifs with h1
      · obtain ⟨h2, h3⟩ := ih ℓ (by simp) hd
        refine ⟨by omega, ?_⟩
        rw [show ctw ts (tend ts c) ℓ - c = t.toks.length + (ctw ts (tend ts c) ℓ - tend ts c) by
          omega, cnt_add, cnt_add, cnt_tree h, ← hte, h3]
      · simp [cnt]

/-- The next node towards `ℓ` is one level deeper. -/
lemma nxt_bal {u : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop u = (LTree.node l cs).toks ++ R) (hcs : cs ≠ []) (ℓ : ℕ) :
    u < nxt ts ℓ u ∧ cnt ts 3 u (nxt ts ℓ u - u) = cnt ts 4 u (nxt ts ℓ u - u) + 1 := by
  obtain ⟨e, hk⟩ := kids_drop h
  have hn := node_toks_drop h
  rw [nxt, if_neg (by rw [isLeaf_iff h]; exact hcs), e]
  obtain ⟨h1, h2⟩ := ctw_bal cs ℓ hcs hk
  refine ⟨by omega, ?_⟩
  have hfin : ts.drop (u + 1) = finsetToks l ++ (LTree.toksList cs ++ Tok.rpar :: R) :=
    drop_succ_of_drop hn
  rw [show ctw ts (u + 1 + (finsetToks l).length) ℓ - u = 1 + ((finsetToks l).length +
    (ctw ts (u + 1 + (finsetToks l).length) ℓ - (u + 1 + (finsetToks l).length))) by omega,
    cnt_add, cnt_add, cnt_add, cnt_add, cnt_list 3 hfin, cnt_list 4 hfin, h2, cnt_one, cnt_one,
    tc_of_drop hn]
  have e3 := lc_finset 3 (by omega) l
  have e4 := lc_finset 4 (by omega) l
  simp only [lc] at e3 e4
  rw [e3, e4]
  simp [Tok.code]
  omega

/-! ## The tail lasso -/

/-- Position `i` holds the opening bracket of a node (followed by the bracket of its label). -/
def isNode (ts : List Tok) (i : ℕ) : Bool := tc ts i == 3 && tc ts (i + 1) == 3

/-- Copy of the label of the node at position `i`. -/
def labCopy (ts : List Tok) (i : ℕ) : List Tok := rng (i + 1) (tend ts (i + 1) - (i + 1)) (cp ts)

/-- Emission for the stem of the tail lasso: labels of inner nodes. -/
def stemAt (ts : List Tok) (i : ℕ) : List Tok :=
  if isNode ts i && !isLeaf ts i then labCopy ts i else []

/-- Emission for the loop of the tail lasso: labels of leaves. -/
def leafAt (ts : List Tok) (i : ℕ) : List Tok :=
  if isNode ts i && isLeaf ts i then labCopy ts i else []

lemma finset_code (l : Finset ℕ) (i : ℕ) (hi : i < (finsetToks l).length) (h0 : 0 < i) :
    ((finsetToks l)[i]).code ≠ 3 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hm : (finsetToks l)[j + 1] ∈ ((l.sort (· ≤ ·)).flatMap natToks ++ [Tok.rpar]) := by
    simp only [finsetToks, List.getElem_cons_succ]; exact List.getElem_mem _
  simp only [List.mem_append, List.mem_flatMap, List.mem_singleton] at hm
  rcases hm with ⟨x, -, hx⟩ | hx
  · have := natToks_code_le x _ hx; omega
  · rw [hx]; simp [Tok.code]

lemma finsetToks_length (l : Finset ℕ) : 2 ≤ (finsetToks l).length := by
  simp [finsetToks]

lemma finset_noNode {p : ℕ} {l : Finset ℕ} {R : List Tok} (h : ts.drop p = finsetToks l ++ R)
    (i : ℕ) (hi : i < (finsetToks l).length) : isNode ts (p + i) = false := by
  have h2 := finsetToks_length l
  simp only [isNode, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · right
    rw [show p + 0 + 1 = p + 1 by omega, tc_of_drop_append h (by omega)]
    exact finset_code l 1 (by omega) (by omega)
  · left; rw [tc_of_drop_append h hi]; exact finset_code l i hi hi0

lemma labCopy_eq {u : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop u = (LTree.node l cs).toks ++ R) : labCopy ts u = finsetToks l := by
  have hn := node_toks_drop h
  have hs := drop_succ_of_drop hn
  rw [labCopy, tend_finset l hs, Nat.add_sub_cancel_left, rng_cp hs]

lemma isNode_node {u : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop u = (LTree.node l cs).toks ++ R) : isNode ts u = true := by
  have hn := node_toks_drop h
  have hs := drop_succ_of_drop hn
  have : ts.drop (u + 1) = Tok.lpar :: ((l.sort (· ≤ ·)).flatMap natToks ++ [Tok.rpar] ++
      (LTree.toksList cs ++ Tok.rpar :: R)) := by rw [hs]; simp [finsetToks]
  simp [isNode, tc_of_drop hn, tc_of_drop this, Tok.code]

/-- The emissions of a node in a linear tree. -/
lemma tail_emit {s : LTree} (hs : Shallow.Linear s) : ∀ {u : ℕ} {R : List Tok},
    ts.drop u = s.toks ++ R →
    rng u s.toks.length (stemAt ts) = (Shallow.tailStem s).flatMap finsetToks ∧
      rng u s.toks.length (leafAt ts) = finsetToks (Shallow.tailLeaf s) := by
  induction hs with
  | leaf l =>
    intro u R h
    have hn := node_toks_drop h
    have hs := drop_succ_of_drop hn
    have hleaf : isLeaf ts u = true := (isLeaf_iff h).2 rfl
    have hnode := isNode_node h
    have hlast : ts.drop (u + 1 + (finsetToks l).length) = Tok.rpar :: R := by
      have := drop_append_of_drop hs; simpa [LTree.toksList] using this
    have hr : isNode ts (u + 1 + (finsetToks l).length) = false := by
      simp [isNode, tc_of_drop hlast, Tok.code]
    have e : (LTree.node l []).toks.length = 1 + ((finsetToks l).length + 1) := by
      simp [LTree.toks, LTree.toksList]; omega
    rw [e, rng_add, rng_add, rng_add, rng_add]
    have hz1 : rng (u + 1) (finsetToks l).length (stemAt ts) = [] :=
      rng_nil _ _ _ fun i hi => by simp [stemAt, finset_noNode hs i hi]
    have hz2 : rng (u + 1) (finsetToks l).length (leafAt ts) = [] :=
      rng_nil _ _ _ fun i hi => by simp [leafAt, finset_noNode hs i hi]
    rw [hz1, hz2]
    simp [rng, stemAt, leafAt, hnode, hleaf, hr, labCopy_eq h, Shallow.tailStem,
      Shallow.tailLeaf]
  | cons l c hc ih =>
    intro u R h
    have hn := node_toks_drop h
    have hs := drop_succ_of_drop hn
    have hleaf : isLeaf ts u = false := by
      cases e : isLeaf ts u
      · rfl
      · exact absurd ((isLeaf_iff h).1 e) (by simp)
    have hnode := isNode_node h
    have hk : ts.drop (u + 1 + (finsetToks l).length) = c.toks ++ (Tok.rpar :: R) := by
      have := drop_append_of_drop hs; simpa [LTree.toksList] using this
    have hlast : ts.drop (u + 1 + (finsetToks l).length + c.toks.length) = Tok.rpar :: R :=
      drop_append_of_drop hk
    have hr : isNode ts (u + 1 + (finsetToks l).length + c.toks.length) = false := by
      simp [isNode, tc_of_drop hlast, Tok.code]
    have e : (LTree.node l [c]).toks.length =
        1 + ((finsetToks l).length + (c.toks.length + 1)) := by
      simp [LTree.toks, LTree.toksList]; omega
    obtain ⟨ih1, ih2⟩ := ih hk
    rw [e, rng_add, rng_add, rng_add, rng_add, rng_add, rng_add]
    have hz1 : rng (u + 1) (finsetToks l).length (stemAt ts) = [] :=
      rng_nil _ _ _ fun i hi => by simp [stemAt, finset_noNode hs i hi]
    have hz2 : rng (u + 1) (finsetToks l).length (leafAt ts) = [] :=
      rng_nil _ _ _ fun i hi => by simp [leafAt, finset_noNode hs i hi]
    have hr' : isNode ts (u + (1 + ((finsetToks l).length + c.toks.length))) = false := by
      rw [show u + (1 + ((finsetToks l).length + c.toks.length)) =
        u + 1 + (finsetToks l).length + c.toks.length by omega]; exact hr
    rw [hz1, hz2, ih1, ih2]
    simp [rng, stemAt, leafAt, hnode, hleaf, hr', labCopy_eq h, Shallow.tailStem,
      Shallow.tailLeaf, Nat.add_assoc]

/-- Tokens of the stem of the tail lasso of the subtree at `u`. -/
def stemToks (ts : List Tok) (u : ℕ) : List Tok := rng u (tend ts u - u) (stemAt ts)
/-- Tokens of the loop letter of the tail lasso of the subtree at `u`. -/
def leafToks (ts : List Tok) (u : ℕ) : List Tok := rng u (tend ts u - u) (leafAt ts)

theorem tail_toks {s : LTree} (hs : Shallow.Linear s) {u : ℕ} {R : List Tok}
    (h : ts.drop u = s.toks ++ R) :
    Tok.lpar :: (stemToks ts u ++ Tok.rpar :: Tok.lpar :: (leafToks ts u ++ [Tok.rpar])) =
      (Shallow.tailLasso s).toks := by
  rw [stemToks, leafToks, tend_tree s h, Nat.add_sub_cancel_left, (tail_emit hs h).1,
    (tail_emit hs h).2]
  simp [Shallow.tailLasso, LassoPath.toks]

/-! ## Letters of a branching round -/

/-- Emission for the renamed label: before each number, `m` digits `1` are inserted. -/
def labGAt (ts : List Tok) (m x : ℕ) : List Tok :=
  (if tc ts (x - 1) = 2 ∨ tc ts (x - 1) = 3 then List.replicate m Tok.one else []) ++ cp ts x

/-- The renamed label of the node at `u` (without brackets). -/
def labG (ts : List Tok) (m u : ℕ) : List Tok :=
  rng (u + 2) (tend ts (u + 1) - 1 - (u + 2)) (labGAt ts m)

lemma natToks_digit (x i : ℕ) (hi : i + 1 < (natToks x).length) : ((natToks x)[i]).code ≤ 1 := by
  simp only [natToks, List.length_append, List.length_map, List.length_singleton] at hi
  simp only [natToks]
  rw [List.getElem_append_left (by simpa using hi)]
  simp only [List.getElem_map]
  split <;> simp [Tok.code]

lemma labG_nums (m : ℕ) (xs : List ℕ) : ∀ {q : ℕ} {R : List Tok},
    ts.drop q = xs.flatMap natToks ++ R → 1 ≤ q → (tc ts (q - 1) = 2 ∨ tc ts (q - 1) = 3) →
    rng q (xs.flatMap natToks).length (labGAt ts m) = xs.flatMap fun a => natToks (gm m a) := by
  induction xs with
  | nil => intro q R _ _ _; rfl
  | cons x xs ih =>
    intro q R h hq hprev
    have h' : ts.drop q = natToks x ++ (xs.flatMap natToks ++ R) := by simpa using h
    have h2 := drop_append_of_drop h'
    have hlen := natToks_length_pos x
    obtain ⟨bs, hbs⟩ : ∃ bs, natToks x = bs ++ [Tok.sep] :=
      ⟨(Nat.bits x).map (fun b => if b then Tok.one else Tok.zero), rfl⟩
    have hsep : tc ts (q + (natToks x).length - 1) = 2 := by
      have := tc_of_drop_append h' (i := (natToks x).length - 1) (by omega)
      rw [show q + ((natToks x).length - 1) = q + (natToks x).length - 1 by omega] at this
      rw [this]; simp [hbs, Tok.code]
    rw [List.flatMap_cons, List.length_append, rng_add, ih h2 (by omega) (Or.inl hsep)]
    congr 1
    show _ = natToks (gm m x)
    rw [natToks_gm]
    obtain ⟨k, hk⟩ : ∃ k, (natToks x).length = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hlen).symm⟩
    rw [hk, rng_succ']
    have hfirst : labGAt ts m q = List.replicate m Tok.one ++ cp ts q := by
      simp [labGAt, hprev]
    have hrest : rng (q + 1) k (labGAt ts m) = rng (q + 1) k (cp ts) := by
      refine rng_congr _ _ _ _ fun i hi => ?_
      have hd : tc ts (q + 1 + i - 1) ≤ 1 := by
        rw [show q + 1 + i - 1 = q + i by omega, tc_of_drop_append h' (by omega)]
        exact natToks_digit x i (by omega)
      simp only [labGAt]; rw [if_neg (by omega)]; rfl
    rw [hfirst, hrest, List.append_assoc]
    congr 1
    have := rng_cp (a := q) h'
    rw [hk, rng_succ'] at this
    exact this

lemma labG_eq (m : ℕ) {u : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop u = (LTree.node l cs).toks ++ R) :
    labG ts m u = (l.sort (· ≤ ·)).flatMap fun a => natToks (gm m a) := by
  have hn := node_toks_drop h
  have hs := drop_succ_of_drop hn
  have hs' : ts.drop (u + 1) = Tok.lpar :: ((l.sort (· ≤ ·)).flatMap natToks ++
      (Tok.rpar :: (LTree.toksList cs ++ Tok.rpar :: R))) := by rw [hs]; simp [finsetToks]
  have h2 := drop_succ_of_drop hs'
  have hlen : tend ts (u + 1) - 1 - (u + 2) = ((l.sort (· ≤ ·)).flatMap natToks).length := by
    rw [tend_finset l hs]; simp [finsetToks]; omega
  rw [labG, hlen, labG_nums m _ h2 (by omega) (Or.inr (by
    rw [show u + 1 + 1 - 1 = u + 1 by omega, tc_of_drop hs']; rfl))]

/-- The names of the letter for a path: fresh names `k + 1` for the positions `k < N` with
`b k`, then the renamed label. -/
def letterList (m N : ℕ) (b : ℕ → Bool) (l : Finset ℕ) : List ℕ :=
  ((List.range N).filter b).map (· + 1) ++ (l.sort (· ≤ ·)).map (gm m)

lemma one_le_two_pow_sub (m : ℕ) : 1 ≤ 2 ^ m := Nat.one_le_two_pow

lemma gm_strictMono (m : ℕ) : StrictMono (gm m) := by
  intro a b hab
  have : a * 2 ^ m < b * 2 ^ m := Nat.mul_lt_mul_of_pos_right hab (by positivity)
  simp only [gm]; omega

lemma letterList_sorted (m N : ℕ) (hN : N + 1 < 2 ^ m) (b : ℕ → Bool) (l : Finset ℕ) :
    (letterList m N b l).Pairwise (· < ·) := by
  unfold letterList
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (List.pairwise_lt_range.filter _).imp (fun h => by omega)
  · rw [List.pairwise_map]
    exact (Finset.sortedLT_sort l).pairwise.imp (fun h => gm_strictMono m h)
  · intro x hx y hy
    simp only [List.mem_map, List.mem_filter, List.mem_range] at hx hy
    obtain ⟨k, ⟨hk, -⟩, rfl⟩ := hx
    obtain ⟨a, -, rfl⟩ := hy
    simp only [gm]
    have : 0 ≤ a * 2 ^ m := Nat.zero_le _
    omega

lemma sort_toFinset_of_sorted (L : List ℕ) (h : L.Pairwise (· < ·)) :
    (L.toFinset).sort (· ≤ ·) = L := by
  have hp : ((L.toFinset).sort (· ≤ ·)).Perm L := by
    rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) (h.imp ne_of_lt)]
    intro x; simp
  exact hp.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h1 h2) (Finset.pairwise_sort _ _)
    (h.imp le_of_lt)

lemma flatMap_ite_filter {α β : Type*} (l : List α) (b : α → Bool) (f : α → List β) :
    l.flatMap (fun k => if b k then f k else []) = (l.filter b).flatMap f := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases hb : b x <;> simp [hb, ih]

/-- Emission for the fresh names of a letter. -/
def freshToks (N : ℕ) (b : ℕ → Bool) : List Tok :=
  (List.range N).flatMap fun k => if b k then natToks (k + 1) else []

lemma letter_toks (m N : ℕ) (hN : N + 1 < 2 ^ m) (b : ℕ → Bool) (l : Finset ℕ) :
    Tok.lpar :: (freshToks N b ++ (l.sort (· ≤ ·)).flatMap (fun a => natToks (gm m a))) ++
      [Tok.rpar] = finsetToks (letterList m N b l).toFinset := by
  rw [finsetToks, sort_toFinset_of_sorted _ (letterList_sorted m N hN b l)]
  simp only [letterList, List.flatMap_append, List.flatMap_map, freshToks, List.cons_append,
    List.append_assoc]
  congr 2
  exact flatMap_ite_filter _ _ _

lemma mem_letterList_gm (m N : ℕ) (hN : N + 1 < 2 ^ m) (b : ℕ → Bool) (l : Finset ℕ) (a : ℕ) :
    gm m a ∈ (letterList m N b l).toFinset ↔ a ∈ l := by
  simp only [letterList, List.mem_toFinset, List.mem_append, List.mem_map, List.mem_filter,
    List.mem_range, Finset.mem_sort]
  constructor
  · rintro (⟨k, ⟨hk, -⟩, he⟩ | ⟨a', ha', he⟩)
    · simp only [gm] at he
      have : 0 ≤ a * 2 ^ m := Nat.zero_le _
      omega
    · rwa [← (gm_strictMono m).injective he]
  · intro ha; exact Or.inr ⟨a, ha, rfl⟩

lemma mem_letterList_fresh (m N : ℕ) (hN : N + 1 < 2 ^ m) (b : ℕ → Bool) (l : Finset ℕ)
    (k : ℕ) (hk : k < N) : k + 1 ∈ (letterList m N b l).toFinset ↔ b k = true := by
  simp only [letterList, List.mem_toFinset, List.mem_append, List.mem_map, List.mem_filter,
    List.mem_range, Finset.mem_sort]
  constructor
  · rintro (⟨k', ⟨-, hb⟩, he⟩ | ⟨a, -, he⟩)
    · rwa [show k = k' by omega]
    · simp only [gm] at he
      have : 0 ≤ a * 2 ^ m := Nat.zero_le _
      omega
  · intro hb; exact Or.inl ⟨k, ⟨hk, hb⟩, rfl⟩

end ShallowP

end PathChecking
