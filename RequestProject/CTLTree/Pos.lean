module

public import RequestProject.CTLTree.Chain
public import RequestProject.Shallow.QSpec

/-!
# Nodes, kids and chains at token positions

For an encoded tree, a *node position* is the position of the opening bracket of a node; it is
recognised locally by `isNode` (an opening bracket followed by the opening bracket of the
label).  The size `sz p = tend p - p` of a node is the length of its encoding.

* `desc`: every node position inside the encoding of a node is the position of a subtree
  whose encoding ends inside the encoding of the node (strictly, if it is not the node itself);
* `kidP_iff`: the kids (children positions) are the node positions not contained in any other
  node position in between;
* `chainF Z v`: the node positions `q` in the encoding of `v` with `Z ≤ 2 · sz q`.  If
  `sz v ≤ Z ≤ 2 sz v`, at most one kid of `v` is *big* (`Z ≤ 2 sz`), and `chainF Z v` is `v`
  followed by the chain of the big kid (`chainF_big`, `chainF_none`).
-/

@[expose] public section

namespace PathChecking

namespace CTLT

open CTLP MCVPReduction ShallowP

/-- Concatenation of `f a, f (a + 1), …, f (a + n - 1)`. -/
def rngL {α : Type*} (a n : ℕ) (f : ℕ → List α) : List α := (List.range n).flatMap fun i => f (a + i)

lemma rngL_add {α : Type*} (a n k : ℕ) (f : ℕ → List α) :
    rngL a (n + k) f = rngL a n f ++ rngL (a + n) k f := by
  simp [rngL, List.range_add, List.flatMap_append, List.flatMap_map, Nat.add_assoc]

lemma rngL_succ' {α : Type*} (a n : ℕ) (f : ℕ → List α) : rngL a (n + 1) f = f a ++ rngL (a + 1) n f := by
  rw [Nat.add_comm, rngL_add]; simp [rngL]

lemma rngL_zero {α : Type*} (a : ℕ) (f : ℕ → List α) : rngL a 0 f = [] := rfl

lemma rngL_congr {α : Type*} (a n : ℕ) (f g : ℕ → List α) (h : ∀ i < n, f (a + i) = g (a + i)) :
    rngL a n f = rngL a n g := by
  unfold rngL
  exact List.flatMap_congr fun i hi => h i (by simpa using hi)

lemma rngL_nil {α : Type*} (a n : ℕ) (f : ℕ → List α) (h : ∀ i < n, f (a + i) = []) :
    rngL a n f = [] := by
  rw [rngL_congr a n f (fun _ => []) h]; simp [rngL]

lemma mem_rngL_filter (a n : ℕ) (P : ℕ → Prop) [DecidablePred P] (q : ℕ) :
    q ∈ rngL a n (fun p => if P p then [p] else []) ↔ a ≤ q ∧ q < a + n ∧ P q := by
  simp only [rngL, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, h⟩
    split_ifs at h with hp
    · simp at h; subst h; exact ⟨by omega, by omega, hp⟩
    · simp at h
  · rintro ⟨h1, h2, h3⟩
    exact ⟨q - a, by omega, by rw [Nat.add_sub_cancel' h1]; simp [h3]⟩

variable {ts : List Tok}

/-- A node position: an opening bracket followed by the opening bracket of a label. -/
def isNode (ts : List Tok) (p : ℕ) : Bool := tc ts p == 3 && tc ts (p + 1) == 3

/-- Size of the node at position `p`. -/
def sz (ts : List Tok) (p : ℕ) : ℕ := tend ts p - p

/-- Position of kid `j` of the node `node l cs` at position `p`. -/
def kpos (l : Finset ℕ) (cs : List LTree) (p j : ℕ) : ℕ :=
  p + 1 + (finsetToks l).length + (LTree.toksList (cs.take j)).length

lemma node_len (l : Finset ℕ) (cs : List LTree) :
    (LTree.node l cs).toks.length = (finsetToks l).length + (LTree.toksList cs).length + 2 := by
  simp [LTree.toks]; omega

lemma isNode_of_drop {p : ℕ} {s : LTree} {R : List Tok} (h : ts.drop p = s.toks ++ R) :
    isNode ts p = true := by
  obtain ⟨l, cs⟩ := s
  have h' := node_toks_drop h
  have h2 := drop_succ_of_drop h'
  have h2' : ts.drop (p + 1) = Tok.lpar :: (((l.sort (· ≤ ·)).flatMap natToks ++ [Tok.rpar]) ++
      (LTree.toksList cs ++ Tok.rpar :: R)) := by rw [h2]; simp [finsetToks]
  simp [isNode, tc_of_drop h', tc_of_drop h2', Tok.code]

lemma sz_of_drop {p : ℕ} {s : LTree} {R : List Tok} (h : ts.drop p = s.toks ++ R) :
    sz ts p = s.toks.length := by
  rw [sz, tend_tree s h]; omega

lemma toksList_append (a b : List LTree) :
    LTree.toksList (a ++ b) = LTree.toksList a ++ LTree.toksList b := by
  induction a with
  | nil => simp [LTree.toksList]
  | cons t a ih => simp [LTree.toksList_cons, ih]

lemma toksList_drop (cs : List LTree) (j : ℕ) (hj : j < cs.length) :
    LTree.toksList (cs.drop j) = cs[j].toks ++ LTree.toksList (cs.drop (j + 1)) := by
  rw [List.drop_eq_getElem_cons hj, LTree.toksList_cons]

lemma kid_drop {p : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop p = (LTree.node l cs).toks ++ R) {j : ℕ} (hj : j < cs.length) :
    ts.drop (kpos l cs p j) = cs[j].toks ++ (LTree.toksList (cs.drop (j + 1)) ++ Tok.rpar :: R) := by
  obtain ⟨-, hk⟩ := kids_drop h
  have e : LTree.toksList cs = LTree.toksList (cs.take j) ++ LTree.toksList (cs.drop j) := by
    rw [← toksList_append, List.take_append_drop]
  rw [e, List.append_assoc] at hk
  have := drop_append_of_drop hk
  rw [toksList_drop cs j hj, List.append_assoc] at this
  exact this

lemma kpos_succ (l : Finset ℕ) (cs : List LTree) (p j : ℕ) (hj : j < cs.length) :
    kpos l cs p (j + 1) = kpos l cs p j + cs[j].toks.length := by
  unfold kpos
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some, toksList_append, LTree.toksList, List.append_nil,
    List.length_append]
  omega

lemma kpos_mono (l : Finset ℕ) (cs : List LTree) (p : ℕ) {i j : ℕ} (hij : i ≤ j) :
    kpos l cs p i ≤ kpos l cs p j := by
  unfold kpos
  have : (LTree.toksList (cs.take i)).length ≤ (LTree.toksList (cs.take j)).length := by
    have e : cs.take j = cs.take i ++ (cs.take j).drop i := by
      conv_lhs => rw [← List.take_append_drop i (cs.take j)]
      rw [List.take_take, min_eq_left hij]
    rw [e, toksList_append, List.length_append]; omega
  omega

lemma kpos_end (l : Finset ℕ) (cs : List LTree) (p : ℕ) :
    kpos l cs p cs.length = p + 1 + (finsetToks l).length + (LTree.toksList cs).length := by
  simp [kpos]

/-- Positions in the span of a list of trees lie in the span of one of them. -/
lemma span_kids (cs : List LTree) : ∀ (a q : ℕ), a ≤ q → q < a + (LTree.toksList cs).length →
    ∃ j, ∃ hj : j < cs.length, a + (LTree.toksList (cs.take j)).length ≤ q ∧
      q < a + (LTree.toksList (cs.take j)).length + (cs[j]'hj).toks.length := by
  induction cs with
  | nil => intro a q h1 h2; simp [LTree.toksList] at h2; omega
  | cons t cs ih =>
    intro a q h1 h2
    rw [LTree.toksList_cons, List.length_append] at h2
    by_cases hq : q < a + t.toks.length
    · exact ⟨0, by simp, by simp [LTree.toksList]; omega, by simpa [LTree.toksList] using hq⟩
    · obtain ⟨j, hj, h3, h4⟩ := ih (a + t.toks.length) q (by omega) (by omega)
      have hj' : j + 1 < (t :: cs).length := by simp; omega
      refine ⟨j + 1, hj', ?_, ?_⟩
      · simp only [List.take_succ_cons, LTree.toksList_cons, List.length_append]; omega
      · simp only [List.take_succ_cons, LTree.toksList_cons, List.length_append,
          List.getElem_cons_succ]; omega

/-- No node position inside a label. -/
lemma label_not_node {p : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop p = (LTree.node l cs).toks ++ R) {q : ℕ} (hq1 : p < q)
    (hq2 : q < p + 1 + (finsetToks l).length) : isNode ts q = false := by
  have h' := node_toks_drop h
  have h2 := drop_succ_of_drop h'
  set ns := (l.sort (· ≤ ·)).flatMap natToks with hns
  have hcode : ∀ t ∈ ns, t.code ≤ 2 := by
    intro t ht
    simp only [hns, List.mem_flatMap] at ht
    obtain ⟨a, -, ha⟩ := ht
    exact natToks_code_le a t ha
  have h2' : ts.drop (p + 1) = Tok.lpar :: (ns ++ (Tok.rpar :: (LTree.toksList cs ++
      Tok.rpar :: R))) := by rw [h2]; simp [finsetToks, hns]
  have h3 := drop_succ_of_drop h2'
  have hflen : (finsetToks l).length = ns.length + 2 := by simp [finsetToks, hns]
  -- the code at positions `p + 2 + i`
  have hc : ∀ i, i ≤ ns.length → tc ts (p + 1 + 1 + i) ≠ 3 := by
    intro i hi
    rcases Nat.lt_or_ge i ns.length with hi' | hi'
    · rw [tc_of_drop_append h3 hi']; have := hcode _ (List.getElem_mem hi'); omega
    · have e : ts.drop (p + 1 + 1 + ns.length) = Tok.rpar :: (LTree.toksList cs ++ Tok.rpar :: R) :=
        drop_append_of_drop h3
      rw [show i = ns.length by omega, tc_of_drop e]; simp [Tok.code]
  unfold isNode
  rcases Nat.eq_or_lt_of_le (show p + 1 ≤ q by omega) with rfl | hq
  · have := hc 0 (by omega)
    simp only [add_zero] at this
    simp [this]
  · have := hc (q - (p + 2)) (by omega)
    rw [show p + 1 + 1 + (q - (p + 2)) = q by omega] at this
    simp [this]

/-- **Node positions inside a node.** -/
lemma desc : ∀ (N : ℕ) (s : LTree), s.toks.length ≤ N → ∀ p R, ts.drop p = s.toks ++ R →
    ∀ q, p ≤ q → q < p + s.toks.length → isNode ts q = true →
    ∃ (t : LTree) (R' : List Tok), ts.drop q = t.toks ++ R' ∧ q + t.toks.length ≤ p + s.toks.length ∧
      (p < q → q + t.toks.length < p + s.toks.length) := by
  intro N
  induction N with
  | zero => intro s hs; have := LTree.toks_length_pos s; omega
  | succ N ih =>
    intro s hs p R h q hq1 hq2 hn
    rcases Nat.eq_or_lt_of_le hq1 with rfl | hlt
    · exact ⟨s, R, h, le_rfl, fun h => absurd h (lt_irrefl _)⟩
    obtain ⟨l, cs⟩ := s
    have hlen := node_len l cs
    by_cases hq3 : q < p + 1 + (finsetToks l).length
    · rw [label_not_node h hlt hq3] at hn; exact absurd hn (by simp)
    by_cases hq4 : q < p + 1 + (finsetToks l).length + (LTree.toksList cs).length
    · obtain ⟨j, hj, h3, h4⟩ := span_kids cs (p + 1 + (finsetToks l).length) q (by omega) hq4
      have hk := kid_drop h hj
      have hkl : cs[j].toks.length ≤ N := by
        have : kpos l cs p j + cs[j].toks.length ≤ kpos l cs p cs.length := by
          rw [← kpos_succ l cs p j hj]; exact kpos_mono l cs p (by omega)
        rw [kpos_end] at this; unfold kpos at this; omega
      obtain ⟨t, R', ht, ht2, -⟩ := ih cs[j] hkl _ _ hk q (by unfold kpos; omega)
        (by unfold kpos; omega) hn
      have : kpos l cs p j + cs[j].toks.length ≤ kpos l cs p cs.length := by
        rw [← kpos_succ l cs p j hj]; exact kpos_mono l cs p (by omega)
      rw [kpos_end] at this
      exact ⟨t, R', ht, by omega, fun _ => by omega⟩
    · -- the closing bracket
      have hq5 : q = p + 1 + (finsetToks l).length + (LTree.toksList cs).length := by omega
      have := drop_append_of_drop (kids_drop h).2
      have e : ts.drop q = Tok.rpar :: R := by rw [hq5]; exact this
      simp [isNode, tc_of_drop e, Tok.code] at hn

/-- Laminarity of node spans, in terms of `tend`. -/
lemma tend_le_of_inside {p q : ℕ} {s : LTree} {R : List Tok} (h : ts.drop p = s.toks ++ R)
    (hq1 : p < q) (hq2 : q < tend ts p) (hn : isNode ts q = true) :
    ∃ (t : LTree) (R' : List Tok), ts.drop q = t.toks ++ R' ∧ tend ts q < tend ts p := by
  rw [tend_tree s h] at hq2 ⊢
  obtain ⟨t, R', ht, -, h3⟩ := desc _ s le_rfl p R h q hq1.le hq2 hn
  exact ⟨t, R', ht, by rw [tend_tree t ht]; exact h3 hq1⟩

/-- The kid predicate. -/
def kidP (ts : List Tok) (v c : ℕ) : Bool :=
  isNode ts c && decide (v < c) && decide (c < tend ts v) &&
    (List.range (c - (v + 1))).all fun i => !isNode ts (v + 1 + i) || decide (tend ts (v + 1 + i) ≤ c)

lemma kidP_eq (v c : ℕ) : kidP ts v c = true ↔ isNode ts c = true ∧ v < c ∧ c < tend ts v ∧
    ∀ w, v < w → w < c → isNode ts w = true → tend ts w ≤ c := by
  simp only [kidP, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, h2, h3, fun w hw1 hw2 hw3 => ?_⟩
    have := h4 (w - (v + 1)) (by omega)
    rw [show v + 1 + (w - (v + 1)) = w by omega] at this
    rcases this with h | h
    · rw [hw3] at h; exact absurd h (by simp)
    · exact h
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨h1, h2⟩, h3⟩, fun i hi => ?_⟩
    by_cases hw : isNode ts (v + 1 + i) = true
    · exact Or.inr (h4 _ (by omega) (by omega) hw)
    · left; simpa using hw

/-- **The kids of a node.** -/
lemma kidP_iff {p : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop p = (LTree.node l cs).toks ++ R) (c : ℕ) :
    kidP ts p c = true ↔ ∃ j < cs.length, c = kpos l cs p j := by
  rw [kidP_eq]
  have hte := tend_tree _ h
  have hlen := node_len l cs
  constructor
  · rintro ⟨hn, h1, h2, h3⟩
    rw [hte] at h2
    by_cases hq3 : c < p + 1 + (finsetToks l).length
    · rw [label_not_node h h1 hq3] at hn; exact absurd hn (by simp)
    by_cases hq4 : c < p + 1 + (finsetToks l).length + (LTree.toksList cs).length
    · obtain ⟨j, hj, h4, h5⟩ := span_kids cs (p + 1 + (finsetToks l).length) c (by omega) hq4
      refine ⟨j, hj, ?_⟩
      by_contra hne
      have hk := kid_drop h hj
      have hlt : kpos l cs p j < c := by unfold kpos at hne ⊢; omega
      have := h3 (kpos l cs p j) (by unfold kpos; omega) hlt (isNode_of_drop hk)
      rw [tend_tree _ hk] at this
      unfold kpos at this; omega
    · have hq5 : c = p + 1 + (finsetToks l).length + (LTree.toksList cs).length := by omega
      have := drop_append_of_drop (kids_drop h).2
      have e : ts.drop c = Tok.rpar :: R := by rw [hq5]; exact this
      simp [isNode, tc_of_drop e, Tok.code] at hn
  · rintro ⟨j, hj, rfl⟩
    have hk := kid_drop h hj
    have hend : kpos l cs p j + cs[j].toks.length ≤ kpos l cs p cs.length := by
      rw [← kpos_succ l cs p j hj]; exact kpos_mono l cs p (by omega)
    rw [kpos_end] at hend
    refine ⟨isNode_of_drop hk, by unfold kpos; omega, by rw [hte]; omega, fun w hw1 hw2 hw3 => ?_⟩
    by_cases hq3 : w < p + 1 + (finsetToks l).length
    · rw [label_not_node h hw1 hq3] at hw3; exact absurd hw3 (by simp)
    obtain ⟨i, hi, h4, h5⟩ := span_kids cs (p + 1 + (finsetToks l).length) w (by omega)
      (by have := kpos_mono l cs p (show j ≤ cs.length by omega); rw [kpos_end] at this; omega)
    have hik : kpos l cs p i ≤ w := by unfold kpos; omega
    have hwk : w < kpos l cs p i + cs[i].toks.length := by unfold kpos; omega
    have hij : i < j := by
      by_contra hc
      have := kpos_mono l cs p (show j ≤ i by omega); omega
    have hki := kid_drop h hi
    obtain ⟨t, R', ht, ht2, -⟩ := desc _ cs[i] le_rfl _ _ hki w hik hwk hw3
    rw [tend_tree t ht]
    have := kpos_mono l cs p (show i + 1 ≤ j by omega)
    rw [kpos_succ l cs p i hi] at this
    omega

/-! ## Chains -/

/-- The node positions `q` inside the encoding of `v` with `Z ≤ 2 sz q`, in increasing order. -/
def chainSel (ts : List Tok) (Z q : ℕ) : List ℕ :=
  if isNode ts q = true ∧ Z ≤ 2 * sz ts q then [q] else []

/-- The node positions `q` inside the encoding of `v` with `Z ≤ 2 sz q`, in increasing order. -/
def chainF (ts : List Tok) (Z v : ℕ) : List ℕ := rngL v (sz ts v) (chainSel ts Z)

/-- The kids of `node l cs` at `p` are disjoint: two big kids are equal. -/
lemma big_kid_unique {p Z : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop p = (LTree.node l cs).toks ++ R) (hZ : sz ts p ≤ Z) {i j : ℕ}
    (hi : i < cs.length) (hj : j < cs.length) (hbi : Z ≤ 2 * sz ts (kpos l cs p i))
    (hbj : Z ≤ 2 * sz ts (kpos l cs p j)) : i = j := by
  rw [sz_of_drop (kid_drop h hi)] at hbi
  rw [sz_of_drop (kid_drop h hj)] at hbj
  rw [sz_of_drop h, node_len] at hZ
  by_contra hne
  -- the spans of two different kids are disjoint
  have key : ∀ a b, a < b → (ha : a < cs.length) → (hb : b < cs.length) →
      cs[a].toks.length + cs[b].toks.length ≤ (LTree.toksList cs).length := by
    intro a b hab ha hb
    have h1 := kpos_mono l cs p (show a + 1 ≤ b by omega)
    have h2 := kpos_mono l cs p (show b + 1 ≤ cs.length by omega)
    rw [kpos_succ l cs p a ha] at h1
    rw [kpos_succ l cs p b hb, kpos_end] at h2
    have h3 := kpos_mono l cs p (show 0 ≤ a by omega)
    simp only [kpos, List.take_zero, LTree.toksList, List.length_nil, add_zero] at h3
    simp only [kpos] at h1 h2
    omega
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := key i j hlt hi hj; omega
  · have := key j i hlt hj hi; omega

lemma chainF_kid_small {p Z : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop p = (LTree.node l cs).toks ++ R) {j : ℕ} (hj : j < cs.length)
    (hs : 2 * sz ts (kpos l cs p j) < Z) :
    rngL (kpos l cs p j) cs[j].toks.length (chainSel ts Z) = [] := by
  have hk := kid_drop h hj
  rw [sz_of_drop hk] at hs
  refine rngL_nil _ _ _ fun i hi => ?_
  rw [chainSel, if_neg]
  rintro ⟨hn, hz⟩
  obtain ⟨t, R', ht, ht2, -⟩ := desc _ cs[j] le_rfl _ _ hk _ (by omega) (by omega) hn
  rw [sz_of_drop ht] at hz
  omega

/-- Length of the encoding of kid `j` (`0` if there is none). -/
def klen (cs : List LTree) (j : ℕ) : ℕ := (LTree.toksList ((cs.drop j).take 1)).length

lemma klen_eq (cs : List LTree) (j : ℕ) (hj : j < cs.length) : klen cs j = cs[j].toks.length := by
  rw [klen, List.drop_eq_getElem_cons hj, List.take_succ_cons, List.take_zero,
    LTree.toksList_cons]
  simp [LTree.toksList]

/-- The concatenation over the span of the kids splits into the kids. -/
lemma rngL_toksList {α : Type*} (f : ℕ → List α) (cs : List LTree) : ∀ a,
    rngL a (LTree.toksList cs).length f = (List.range cs.length).flatMap fun j =>
      rngL (a + (LTree.toksList (cs.take j)).length) (klen cs j) f := by
  induction cs with
  | nil => intro a; simp [LTree.toksList, rngL]
  | cons t cs ih =>
    intro a
    rw [LTree.toksList_cons, List.length_append, rngL_add, ih, List.length_cons,
      List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp [LTree.toksList, klen, Nat.add_assoc]

lemma flatMap_range_single {α : Type*} (g : ℕ → List α) : ∀ (n j : ℕ), j < n →
    (∀ i < n, i ≠ j → g i = []) → (List.range n).flatMap g = g j := by
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj h
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_or_ge j n with hjn | hjn
    · rw [ih j hjn (fun i hi hij => h i (by omega) hij), h n (by omega) (by omega)]; simp
    · obtain rfl : j = n := by omega
      rw [List.flatMap_eq_nil_iff.2 (fun i hi => h i (by simp at hi; omega)
        (by simp at hi; omega))]
      simp

/-- The chain inside a node splits into the node and the chains inside its kids. -/
lemma chainF_eq {p Z : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop p = (LTree.node l cs).toks ++ R) (hZ : Z ≤ 2 * sz ts p) :
    chainF ts Z p = p :: (List.range cs.length).flatMap fun j => chainF ts Z (kpos l cs p j) := by
  have hlen := node_len l cs
  unfold chainF
  rw [sz_of_drop h, hlen]
  rw [show (finsetToks l).length + (LTree.toksList cs).length + 2 =
    ((finsetToks l).length + ((LTree.toksList cs).length + 1)) + 1 by omega, rngL_succ',
    rngL_add, rngL_add]
  have h1 : chainSel ts Z p = [p] := by simp [chainSel, isNode_of_drop h, hZ]
  have h2 : rngL (p + 1) (finsetToks l).length (chainSel ts Z) = [] :=
    rngL_nil _ _ _ fun i hi => by
      rw [chainSel, if_neg]; rintro ⟨hn, -⟩
      rw [label_not_node h (by omega) (by omega)] at hn; exact absurd hn (by simp)
  have h3 : rngL (p + 1 + (finsetToks l).length + (LTree.toksList cs).length) 1
      (chainSel ts Z) = [] := by
    have e := drop_append_of_drop (kids_drop h).2
    simp [rngL, chainSel, isNode, tc_of_drop e, Tok.code]
  rw [h1, h2, h3, rngL_toksList]
  simp only [List.nil_append, List.append_nil, List.cons_append, List.singleton_append]
  congr 1
  refine List.flatMap_congr fun j hj => ?_
  rw [List.mem_range] at hj
  rw [klen_eq cs j hj, ← sz_of_drop (kid_drop h hj)]
  congr 1

lemma chainF_small {p Z : ℕ} {s : LTree} {R : List Tok} (h : ts.drop p = s.toks ++ R)
    (hs : 2 * sz ts p < Z) : chainF ts Z p = [] := by
  unfold chainF
  refine rngL_nil _ _ _ fun i hi => ?_
  rw [chainSel, if_neg]
  rintro ⟨hn, hz⟩
  rw [sz_of_drop h] at hi hs
  obtain ⟨t, R', ht, ht2, -⟩ := desc _ s le_rfl _ _ h _ (by omega) (by omega) hn
  rw [sz_of_drop ht] at hz
  omega

/-- **The chain continues with the big kid.** -/
lemma chainF_big {p Z : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop p = (LTree.node l cs).toks ++ R) (hZ : Z ≤ 2 * sz ts p) (hZ' : sz ts p ≤ Z)
    {j : ℕ} (hj : j < cs.length) (hb : Z ≤ 2 * sz ts (kpos l cs p j)) :
    chainF ts Z p = p :: chainF ts Z (kpos l cs p j) := by
  rw [chainF_eq h hZ]
  congr 1
  refine flatMap_range_single _ _ _ hj fun i hi hij => chainF_small (kid_drop h hi) ?_
  by_contra hc
  exact hij (big_kid_unique h hZ' hi hj (by omega) hb)

/-- **The chain ends if there is no big kid.** -/
lemma chainF_none {p Z : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop p = (LTree.node l cs).toks ++ R) (hZ : Z ≤ 2 * sz ts p)
    (hn : ∀ j (hj : j < cs.length), 2 * sz ts (kpos l cs p j) < Z) :
    chainF ts Z p = [p] := by
  rw [chainF_eq h hZ]
  congr 1
  exact List.flatMap_eq_nil_iff.2 fun j hj =>
    chainF_small (kid_drop h (List.mem_range.1 hj)) (hn j (List.mem_range.1 hj))

end CTLT

end PathChecking

namespace PathChecking

namespace CTLT

open CTLP MCVPReduction ShallowP

variable {ts : List Tok}

/-- A node position strictly inside a node lies inside one of its kids. -/
lemma in_kid {p : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop p = (LTree.node l cs).toks ++ R) {q : ℕ} (hq1 : p < q) (hq2 : q < tend ts p)
    (hn : isNode ts q = true) :
    ∃ j, ∃ hj : j < cs.length, kpos l cs p j ≤ q ∧ q < kpos l cs p j + (cs[j]'hj).toks.length ∧
      sz ts q ≤ sz ts (kpos l cs p j) := by
  have hte := tend_tree _ h
  have hlen := node_len l cs
  rw [hte] at hq2
  by_cases hq3 : q < p + 1 + (finsetToks l).length
  · rw [label_not_node h hq1 hq3] at hn; exact absurd hn (by simp)
  by_cases hq4 : q < p + 1 + (finsetToks l).length + (LTree.toksList cs).length
  · obtain ⟨j, hj, h4, h5⟩ := span_kids cs (p + 1 + (finsetToks l).length) q (by omega) hq4
    have hk := kid_drop h hj
    obtain ⟨t, R', ht, ht2, -⟩ := desc _ cs[j] le_rfl _ _ hk q (by unfold kpos; omega)
      (by unfold kpos; omega) hn
    refine ⟨j, hj, by unfold kpos; omega, by unfold kpos; omega, ?_⟩
    rw [sz_of_drop ht, sz_of_drop hk]; unfold kpos at ht2; omega
  · have hq5 : q = p + 1 + (finsetToks l).length + (LTree.toksList cs).length := by omega
    have := drop_append_of_drop (kids_drop h).2
    have e : ts.drop q = Tok.rpar :: R := by rw [hq5]; exact this
    simp [isNode, tc_of_drop e, Tok.code] at hn

/-- No big node strictly inside `p`. -/
def noBig (ts : List Tok) (Z p : ℕ) : Bool :=
  (List.range (sz ts p)).all fun i =>
    !(decide (0 < i) && isNode ts (p + i) && decide (Z ≤ 2 * sz ts (p + i)))

lemma noBig_iff {p Z : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop p = (LTree.node l cs).toks ++ R) :
    noBig ts Z p = true ↔ ∀ j (hj : j < cs.length), 2 * sz ts (kpos l cs p j) < Z := by
  simp only [noBig, List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, not_lt, Nat.le_zero, Bool.not_eq_true]
  have hte := tend_tree _ h
  constructor
  · intro H j hj
    have hk := kid_drop h hj
    have hend : kpos l cs p j + cs[j].toks.length ≤ kpos l cs p cs.length := by
      rw [← kpos_succ l cs p j hj]; exact kpos_mono l cs p (by omega)
    rw [kpos_end] at hend
    have hlen := node_len l cs
    have := H (kpos l cs p j - p) (by rw [sz, hte]; unfold kpos at hend ⊢; omega)
    rw [Nat.add_sub_cancel' (by unfold kpos; omega)] at this
    rcases this with (h1 | h1) | h1
    · unfold kpos at h1; omega
    · rw [isNode_of_drop hk] at h1; exact absurd h1 (by simp)
    · omega
  · intro H i hi
    by_cases hi0 : i = 0
    · left; left; exact hi0
    by_cases hn : isNode ts (p + i) = true
    · right
      rw [sz] at hi
      obtain ⟨j, hj, -, -, hsz⟩ := in_kid h (by omega) (by omega) hn
      have := H j hj; omega
    · left; right; simpa using hn

/-! ## Structure of the chain -/

/-- **Structure of the chain.** -/
lemma chain_struct (Z : ℕ) : ∀ (N v : ℕ) (t : LTree) (R : List Tok), t.toks.length ≤ N →
    ts.drop v = t.toks ++ R → Z ≤ 2 * sz ts v → sz ts v ≤ Z → ∀ L, chainF ts Z v = L →
    L ≠ [] ∧ L.head? = some v ∧
    (∀ q ∈ L, (∃ (t' : LTree) (R' : List Tok), ts.drop q = t'.toks ++ R') ∧
      Z ≤ 2 * sz ts q ∧ v ≤ q ∧ q < tend ts v) ∧
    (∀ i (h : i + 1 < L.length), ∃ (l : Finset ℕ) (cs : List LTree) (R' : List Tok)
      (j : ℕ) (_ : j < cs.length), ts.drop L[i] = (LTree.node l cs).toks ++ R' ∧
      L[i + 1] = kpos l cs L[i] j) ∧
    (∀ i (h : i < L.length), noBig ts Z L[i] = true ↔ i + 1 = L.length) := by
  intro N
  induction N with
  | zero => intro v t R ht; have := LTree.toks_length_pos t; omega
  | succ N ih =>
    intro v t R hN h hZ hZ' L hL
    obtain ⟨l, cs⟩ := t
    have hte := tend_tree _ h
    have hv : v < tend ts v := by rw [hte]; have := LTree.toks_length_pos (LTree.node l cs); omega
    by_cases hb : ∃ j, ∃ hj : j < cs.length, Z ≤ 2 * sz ts (kpos l cs v j)
    · obtain ⟨j, hj, hbj⟩ := hb
      have hk := kid_drop h hj
      have hend : kpos l cs v j + cs[j].toks.length ≤ kpos l cs v cs.length := by
        rw [← kpos_succ l cs v j hj]; exact kpos_mono l cs v (by omega)
      rw [kpos_end] at hend
      have hnl := node_len l cs
      have hkl : cs[j].toks.length ≤ N := by unfold kpos at hend; omega
      have hszk : sz ts (kpos l cs v j) ≤ Z := by
        rw [sz_of_drop hk]; rw [sz_of_drop h] at hZ'
        unfold kpos at hend; omega
      obtain ⟨i1, i2, i3, i4, i5⟩ := ih _ _ _ hkl hk hbj hszk _ rfl
      have hkin : v < kpos l cs v j ∧ tend ts (kpos l cs v j) < tend ts v := by
        rw [tend_tree _ hk, hte]
        unfold kpos at hend ⊢; omega
      rw [chainF_big h hZ hZ' hj hbj] at hL
      subst hL
      refine ⟨by simp, by simp, ?_, ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact ⟨⟨_, _, h⟩, hZ, le_rfl, hv⟩
        · obtain ⟨a1, a2, a3, a4⟩ := i3 q hq
          exact ⟨a1, a2, by omega, by omega⟩
      · intro i hi
        cases i with
        | zero =>
          refine ⟨l, cs, R, j, hj, h, ?_⟩
          obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil i1
          rw [hx] at i2
          simp only [List.head?_cons, Option.some.injEq] at i2
          simp only [List.getElem_cons_succ, List.getElem_cons_zero]
          simp only [hx, List.getElem_cons_zero, i2]
        | succ i =>
          simp only [List.length_cons] at hi
          obtain ⟨l', cs', R', j', hj', e1, e2⟩ := i4 i (by omega)
          exact ⟨l', cs', R', j', hj', by simpa using e1, by simpa using e2⟩
      · intro i hi
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero, List.length_cons]
          rw [noBig_iff h]
          constructor
          · intro H; have := H j hj; omega
          · intro H; have := List.length_pos_iff.2 i1; omega
        | succ i =>
          simp only [List.getElem_cons_succ, List.length_cons]
          rw [i5 i (by simpa using hi)]
          omega
    · push_neg at hb
      rw [chainF_none h hZ hb] at hL
      subst hL
      refine ⟨by simp, by simp, ?_, ?_, ?_⟩
      · intro q hq
        rw [List.mem_singleton] at hq; subst hq
        exact ⟨⟨_, _, h⟩, hZ, le_rfl, hv⟩
      · intro i hi; simp at hi
      · intro i hi
        simp only [List.length_singleton] at hi ⊢
        obtain rfl : i = 0 := by omega
        simp only [List.getElem_singleton, zero_add, iff_true]
        exact (noBig_iff h).2 hb

end CTLT

end PathChecking
