module

public import RequestProject.CTLTree.Glue
public import RequestProject.LTLPath.FDD

/-!
# Terms for the positional functions of the CTL query

Terms of the denotational calculus of `RequestProject/LTLPath/FED.lean` for the positional
functions used by the query `CQ`: ends of groups (`tendT`), node positions (`isNodeT`), kids
(`kidPT`), the answers of the previous round (`ansCT`), and the values `offv` of the fresh
propositions (`offvT`).
-/

@[expose] public section

namespace PathChecking

namespace CTLF

open FE LL CTLP LTok FD CTLT ShallowP

variable {x : Word} {Γ : Ctx} {ts : List Tok} {q : ℕ} {a : List Bool}

/-! ## Boolean helpers -/

lemma den_allB {n : T} {body : T → T} {N : ℕ} {f : ℕ → Bool} (hn : Den x Γ n N)
    (hb : ∀ k i, i < N → Den x ((k, i) :: Γ) (body (varT k)) (f i).toNat) :
    Den x Γ (allT n body) ((List.range N).all f).toNat :=
  den_bool_of_bv (den_all hn fun k i hi => (hb k i hi).of_eq (bv_bool _))
    (by simp [List.all_eq_true])

lemma den_anyB {n : T} {body : T → T} {N : ℕ} {f : ℕ → Bool} (hn : Den x Γ n N)
    (hb : ∀ k i, i < N → Den x ((k, i) :: Γ) (body (varT k)) (f i).toNat) :
    Den x Γ (exT n body) ((List.range N).any f).toNat :=
  den_bool_of_bv (den_ex hn fun k i hi => (hb k i hi).of_eq (bv_bool _))
    (by simp [List.any_eq_true])

/-! ## Groups and nodes -/

lemma tend_eq (p : ℕ) : tend ts p =
    if ts.length ≤ p then p else if tc ts p = 3 then tend1 ts p else p + 1 := by
  unfold tend tend1
  rw [scan_eq]
  by_cases h1 : ts.length ≤ p
  · simp [h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h3 : tc ts p = 3
    · rw [if_pos h3, if_neg (by simp [cstep, upT, h3])]
      simp [cstep, upT, h3]
    · have : cstep upT downT (tc ts p) 0 = 0 := by
        unfold cstep; simp only [upT, beq_iff_eq, h3, if_false]; split_ifs <;> rfl
      rw [if_neg h3, if_pos this]

/-- End of the group at `p`. -/
def tendT (p : T) : T := iteT (leT nT p) p (iteT (isT 3 (tcT p)) (tend1T p) (addT p (cT 1)))

variable (hx : x = pack (encodeToks ts) q a)
include hx

lemma den_tend {p : T} {P : ℕ} (hp : Den x Γ p P) : Den x Γ (tendT p) (tend ts P) := by
  rw [tend_eq]
  refine den_ite_eq (den_le (den_n hx) hp) (fun h => ?_) (fun h => ?_)
  · simp only [ne_eq, bv_eq_zero, not_not] at h; rw [if_pos h]; exact hp
  · simp only [bv_eq_zero] at h
    rw [if_neg h]
    refine den_ite_eq (den_is (den_tc hx hp)) (fun h3 => ?_) (fun h3 => ?_)
    · simp only [ne_eq, bv_eq_zero, not_not] at h3; rw [if_pos h3]; exact den_tend1 hx hp
    · simp only [bv_eq_zero] at h3; rw [if_neg h3]; exact den_add hp (den_c 1)

/-- Size of the node at `p`. -/
def szT (p : T) : T := subT (tendT p) p

lemma den_sz {p : T} {P : ℕ} (hp : Den x Γ p P) : Den x Γ (szT p) (sz ts P) :=
  den_sub (den_tend hx hp) hp

/-- Node position test. -/
def isNodeT (p : T) : T := andT (isT 3 (tcT p)) (isT 3 (tcT (addT p (cT 1))))

lemma den_isNode {p : T} {P : ℕ} (hp : Den x Γ p P) : Den x Γ (isNodeT p) (CTLT.isNode ts P).toNat :=
  den_andB (den_eqB (den_tc hx hp) (den_c 3)) (den_eqB (den_tc hx (den_add hp (den_c 1))) (den_c 3))

/-- The kid predicate. -/
def kidPT (v c : T) : T :=
  andT (andT (andT (isNodeT c) (ltT v c)) (ltT c (tendT v)))
    (allT (subT c (addT v (cT 1))) fun i =>
      orT (notT (isNodeT (addT (addT v (cT 1)) i))) (leT (tendT (addT (addT v (cT 1)) i)) c))

lemma den_kidP {v c : T} {V Cc : ℕ} (hv : Den x Γ v V) (hc : Den x Γ c Cc) :
    Den x Γ (kidPT v c) (kidP ts V Cc).toNat := by
  unfold kidPT kidP
  refine den_andB (den_andB (den_andB (den_isNode hx hc) (den_ltB hv hc))
    (den_ltB hc (den_tend hx hv))) (den_allB (den_sub hc (den_add hv (den_c 1))) fun k i _ => ?_)
  have hi : Den x ((k, i) :: Γ) (addT (addT v (cT 1)) (varT k)) (V + 1 + i) :=
    den_add (den_add (hv.cons _) (den_c 1)) den_var0
  exact den_orB (den_notB (den_isNode hx hi)) (den_leB (den_tend hx hi) (hc.cons _))

/-- The test `noBig`. -/
def noBigT (Z p : T) : T :=
  allT (szT p) fun i => notT (andT (andT (ltT (cT 0) i) (isNodeT (addT p i)))
    (leT Z (mulT (cT 2) (szT (addT p i)))))

lemma den_noBig {Z p : T} {ZV P : ℕ} (hZ : Den x Γ Z ZV) (hp : Den x Γ p P) :
    Den x Γ (noBigT Z p) (noBig ts ZV P).toNat := by
  unfold noBigT noBig
  refine den_allB (den_sz hx hp) fun k i _ => ?_
  have hi : Den x ((k, i) :: Γ) (addT p (varT k)) (P + i) := den_add (hp.cons _) den_var0
  exact den_notB (den_andB (den_andB (den_ltB (den_c 0) den_var0) (den_isNode hx hi))
    (den_leB (hZ.cons _) (den_mul (den_c 2) (den_sz hx hi))))

/-- Membership in the chain of `u`. -/
def inChainT (u p : T) : T := andT (isNodeT p) (leT (szT u) (mulT (cT 2) (szT p)))

lemma den_inChain {u p : T} {U P : ℕ} (hu : Den x Γ u U) (hp : Den x Γ p P) :
    Den x Γ (inChainT u p) (bv (inChain ts U P)) :=
  den_and ((den_isNode hx hp).of_eq (bv_bool _)) (den_le (den_sz hx hu) (den_mul (den_c 2)
    (den_sz hx hp)))

/-- Leaf test. -/
def isLeafT (u : T) : T := isT 4 (tcT (tendT (addT u (cT 1))))

lemma den_isLeaf {u : T} {U : ℕ} (hu : Den x Γ u U) : Den x Γ (isLeafT u) (isLeaf ts U).toNat :=
  den_eqB (den_tc hx (den_tend hx (den_add hu (den_c 1)))) (den_c 4)

/-! ## Answers and fresh propositions -/

/-- The answer for the pair `(c, k)`. -/
def ansCT (M c k : T) : T :=
  iteT (andT (ltT c M) (ltT k M)) (ansT (addT (mulT c M) k)) (cT 0)

omit hx in
lemma den_ansC (hx : x = pack (encodeToks ts) q a) (hq : q ≤ a.length) {M c k : T}
    {MV Cc K : ℕ} (hM : Den x Γ M MV) (hc : Den x Γ c Cc) (hk : Den x Γ k K) :
    Den x Γ (ansCT M c k) (ansC MV a Cc K).toNat := by
  unfold ansCT ansC
  refine den_ite_eq (den_and (den_lt' hc hM) (den_lt' hk hM)) (fun h => ?_) (fun h => ?_)
  · simp only [ne_eq, bv_eq_zero, not_not] at h
    rw [if_pos h]; exact den_ans hx hq (den_add (den_mul hc hM) hk)
  · simp only [bv_eq_zero] at h
    rw [if_neg h]; exact den_c 0

/-- Small kids. -/
def smallKidT (Z p c : T) : T := andT (kidPT p c) (ltT (mulT (cT 2) (szT c)) Z)

lemma den_smallKid {Z p c : T} {ZV P Cc : ℕ} (hZ : Den x Γ Z ZV) (hp : Den x Γ p P)
    (hc : Den x Γ c Cc) : Den x Γ (smallKidT Z p c) (smallKid ts ZV P Cc).toNat :=
  den_andB (den_kidP hx hp hc) (den_ltB (den_mul (den_c 2) (den_sz hx hc)) hZ)

/-- Some small kid satisfies `B`. -/
def anyKidT (Z p : T) (B : T → T) : T :=
  exT (szT p) fun i => andT (smallKidT Z p (addT p i)) (B (addT p i))

/-- All small kids satisfy `B`. -/
def allKidT (Z p : T) (B : T → T) : T :=
  allT (szT p) fun i => orT (notT (smallKidT Z p (addT p i))) (B (addT p i))

lemma den_anyKid {Z p : T} {ZV P : ℕ} (hZ : Den x Γ Z ZV) (hp : Den x Γ p P) {B : T → T}
    {Bb : ℕ → Bool} (hB : DenP x Γ B Bb) : Den x Γ (anyKidT Z p B) (anyKid ts ZV P Bb).toNat := by
  unfold anyKidT anyKid
  refine den_anyB (den_sz hx hp) fun k i _ => ?_
  have hi : Den x ((k, i) :: Γ) (addT p (varT k)) (P + i) := den_add (hp.cons _) den_var0
  exact den_andB (den_smallKid hx (hZ.cons _) (hp.cons _) hi)
    (hB _ (List.subset_cons_self _ _) _ _ hi)

lemma den_allKid {Z p : T} {ZV P : ℕ} (hZ : Den x Γ Z ZV) (hp : Den x Γ p P) {B : T → T}
    {Bb : ℕ → Bool} (hB : DenP x Γ B Bb) : Den x Γ (allKidT Z p B) (allKid ts ZV P Bb).toNat := by
  unfold allKidT allKid
  refine den_allB (den_sz hx hp) fun k i _ => ?_
  have hi : Den x ((k, i) :: Γ) (addT p (varT k)) (P + i) := den_add (hp.cons _) den_var0
  exact den_orB (den_notB (den_smallKid hx (hZ.cons _) (hp.cons _) hi))
    (hB _ (List.subset_cons_self _ _) _ _ hi)

/-- The value of the fresh proposition `k + 2` at the exit letter of `p`. -/
def offvT (M Z p k : T) : T :=
  iteT (isT 9 (tcT k)) (anyKidT Z p fun c => ansCT M c (addT k (cT 1)))
    (iteT (isT 10 (tcT k)) (anyKidT Z p fun c => ansCT M c k)
      (iteT (isT 11 (tcT k)) (allKidT Z p fun c => ansCT M c k) (cT 0)))

omit hx in
lemma den_offv (hx : x = pack (encodeToks ts) q a) (hq : q ≤ a.length) {M Z p k : T}
    {MV ZV P K : ℕ} (hM : Den x Γ M MV) (hZ : Den x Γ Z ZV) (hp : Den x Γ p P)
    (hk : Den x Γ k K) :
    Den x Γ (offvT M Z p k) (offv ts (ansC MV a) ZV P K).toNat := by
  unfold offvT offv
  have hB : ∀ (k' : T) (K' : ℕ), Den x Γ k' K' →
      DenP x Γ (fun c => ansCT M c k') (fun c => ansC MV a c K') :=
    fun k' K' hk' Γ' hΓ t v ht => den_ansC hx hq (hM.mono hΓ) ht (hk'.mono hΓ)
  refine den_ite_eq (den_is (den_tc hx hk)) (fun h => ?_) (fun h => ?_)
  · simp only [ne_eq, bv_eq_zero, not_not] at h
    rw [if_pos h]; exact den_anyKid hx hZ hp (hB _ _ (den_add hk (den_c 1)))
  · simp only [bv_eq_zero] at h
    rw [if_neg h]
    refine den_ite_eq (den_is (den_tc hx hk)) (fun h' => ?_) (fun h' => ?_)
    · simp only [ne_eq, bv_eq_zero, not_not] at h'
      rw [if_pos h']; exact den_anyKid hx hZ hp (hB _ _ hk)
    · simp only [bv_eq_zero] at h'
      rw [if_neg h']
      refine den_ite_eq (den_is (den_tc hx hk)) (fun h'' => ?_) (fun h'' => ?_)
      · simp only [ne_eq, bv_eq_zero, not_not] at h''
        rw [if_pos h'']; exact den_allKid hx hZ hp (hB _ _ hk)
      · simp only [bv_eq_zero] at h''
        rw [if_neg h'']; exact den_c 0

end CTLF

end PathChecking
