module

public import RequestProject.CTLTree.FQ1

/-!
# Output programs for the lasso of the CTL query

Output terms producing the node letters (`ndO`), the exit letters (`exO`), the stem (`stemO`)
and the loop (`loopCO`) of the lasso of the query `CQ`.
-/

@[expose] public section

namespace PathChecking

namespace CTLF

open FE LL CTLP LTok FD CTLT ShallowP

variable {x : Word} {Γ : Ctx} {ts : List Tok} {q : ℕ} {a : List Bool}

/-! ## Generic output helpers -/

lemma encodeToks_flatMap {α : Type*} (l : List α) (f : α → List Tok) :
    encodeToks (l.flatMap f) = l.flatMap fun i => encodeToks (f i) := by
  simp [encodeToks, List.flatMap_assoc]

lemma encodeToks_single (t : Tok) : encodeToks [t] = cbits t.code := by
  rw [encodeToks_cons]; simp [encodeToks]

/-- Output of a fixed token list. -/
def toksO : List Tok → TO
  | [] => nilO
  | t :: l => seqO (tokO (cT t.code)) (toksO l)

lemma deno_toks (l : List Tok) : DenO x Γ (toksO l) (encodeToks l) := by
  induction l with
  | nil => exact deno_nil
  | cons t l ih => exact (deno_seq (deno_tok (den_c _)) ih).of_eq (encodeToks_cons t l).symm

/-- Repetition of an output. -/
def repO (n : T) (o : TO) : TO := loopO n fun _ => o

lemma deno_rep {n : T} {N : ℕ} {o : TO} {v : Word} (hn : Den x Γ n N)
    (ho : ∀ Γ', Γ ⊆ Γ' → DenO x Γ' o v) : DenO x Γ (repO n o) ((List.range N).flatMap fun _ => v) :=
  deno_loop hn fun _ _ _ => ho _ (List.subset_cons_self _ _)

lemma encodeToks_replicate (m : ℕ) (t : Tok) :
    encodeToks (List.replicate m t) = (List.range m).flatMap fun _ => encodeToks [t] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ', encodeToks_append, ih, List.range_succ, List.flatMap_append]
    simp

variable (hx : x = pack (encodeToks ts) q a)
include hx

/-- Copy of the token at `p`. -/
def cpO (p : T) : TO := iteO (ltT p nT) (tokO (tcT p)) nilO

lemma deno_cp {p : T} {P : ℕ} (hp : Den x Γ p P) : DenO x Γ (cpO p) (encodeToks (cp ts P)) := by
  refine deno_ite_eq (den_lt' hp (den_n hx)) (fun h => ?_) (fun h => ?_)
  · simp only [ne_eq, bv_eq_zero, not_not] at h
    refine (deno_tok (den_tc hx hp)).of_eq ?_
    have hs : ts[P]? = some ts[P] := List.getElem?_eq_getElem h
    simp [cp, hs, encodeToks_single, tc]
  · simp only [bv_eq_zero, not_lt] at h
    refine deno_nil.of_eq ?_
    simp [cp, List.getElem?_eq_none h, encodeToks]

/-! ## Node letters -/

/-- Emission of the renamed label at `p`. -/
def labGAtO (mm p : T) : TO :=
  seqO (iteO (orT (isT 2 (tcT (subT p (cT 1)))) (isT 3 (tcT (subT p (cT 1)))))
    (repO mm (tokO (cT 1))) nilO) (cpO p)

lemma deno_labGAt {mm p : T} {m P : ℕ} (hm : Den x Γ mm m) (hp : Den x Γ p P) :
    DenO x Γ (labGAtO mm p) (encodeToks (labGAt ts m P)) := by
  unfold labGAtO labGAt
  rw [encodeToks_append]
  refine deno_seq (deno_ite_eq (den_or (den_is (den_tc hx (den_sub hp (den_c 1))))
    (den_is (den_tc hx (den_sub hp (den_c 1))))) (fun h => ?_) (fun h => ?_)) (deno_cp hx hp)
  · simp only [ne_eq, bv_eq_zero, not_not] at h
    rw [if_pos h, encodeToks_replicate]
    exact deno_rep hm fun Γ' _ => (deno_tok (den_c 1)).of_eq (by rw [encodeToks_single]; rfl)
  · simp only [bv_eq_zero] at h
    rw [if_neg h]; exact deno_nil

/-- Emission of the node letter of `p`. -/
def ndO (mm p : T) : TO :=
  seqO (tokO (cT 3)) (seqO (loopO (subT (subT (tendT (addT p (cT 1))) (cT 1)) (addT p (cT 2)))
    fun i => labGAtO mm (addT (addT p (cT 2)) i)) (tokO (cT 4)))

lemma deno_nd {mm p : T} {m P : ℕ} (hm : Den x Γ mm m) (hp : Den x Γ p P) :
    DenO x Γ (ndO mm p) (encodeToks (ndToks ts m P)) := by
  unfold ndO ndToks labG rng
  rw [encodeToks_cons, encodeToks_append, encodeToks_flatMap, encodeToks_single]
  refine deno_seq (deno_tok (den_c 3)) (deno_seq (deno_loop (den_sub (den_sub (den_tend hx
    (den_add hp (den_c 1))) (den_c 1)) (den_add hp (den_c 2))) fun k i _ => ?_)
    (deno_tok (den_c 4)))
  exact deno_labGAt hx (hm.cons _) (den_add (den_add (hp.cons _) (den_c 2)) den_var0)

/-! ## Exit letters -/

/-- Emission of the exit letter of `p`. -/
def exO (MM Z p e : T) : TO :=
  seqO (tokO (cT 3)) (seqO (natO (cT 0)) (seqO (iteO e (natO (cT 1)) nilO)
    (seqO (loopO MM fun k => iteO (offvT MM Z p k) (natO (addT k (cT 2))) nilO) (tokO (cT 4)))))

omit hx in
lemma deno_ex (hx : x = pack (encodeToks ts) q a) (hq : q ≤ a.length) {MM Z p e : T}
    {M ZV P : ℕ} {E : Bool} (hM : Den x Γ MM M) (hZ : Den x Γ Z ZV) (hp : Den x Γ p P)
    (he : Den x Γ e E.toNat) :
    DenO x Γ (exO MM Z p e) (encodeToks (exToks ts M (ansC M a) ZV P E)) := by
  unfold exO exToks
  rw [encodeToks_cons, encodeToks_append, encodeToks_append, encodeToks_append,
    encodeToks_flatMap, encodeToks_single]
  refine deno_seq (deno_tok (den_c 3)) (deno_seq (deno_nat (den_c 0)) (deno_seq
    (deno_ite_eq he (fun h => ?_) (fun h => ?_)) (deno_seq (deno_loop hM fun k i _ => ?_)
      (deno_tok (den_c 4)))))
  · cases E
    · simp at h
    · simpa using deno_nat (den_c 1)
  · cases E
    · simpa [encodeToks] using deno_nil
    · simp at h
  · refine deno_ite_eq (den_offv hx hq (hM.cons _) (hZ.cons _) (hp.cons _) den_var0)
      (fun h => ?_) (fun h => ?_)
    · rw [if_pos (by cases hv : offv ts (ansC M a) ZV P i <;> simp_all)]
      exact deno_nat (den_add den_var0 (den_c 2))
    · rw [if_neg (by cases hv : offv ts (ansC M a) ZV P i <;> simp_all)]
      simpa [encodeToks] using deno_nil

/-! ## Stem and loop -/

/-- Emission of the stem. -/
def stemO (MM mm u : T) : TO :=
  loopO (szT u) fun i => iteO (inChainT u (addT u i))
    (seqO (ndO mm (addT u i)) (iteO (noBigT (szT u) (addT u i)) nilO
      (exO MM (szT u) (addT u i) (cT 0)))) nilO

omit hx in
lemma deno_stem (hx : x = pack (encodeToks ts) q a) (hq : q ≤ a.length) {MM mm u : T}
    {M m U : ℕ} (hM : Den x Γ MM M) (hm : Den x Γ mm m) (hu : Den x Γ u U) :
    DenO x Γ (stemO MM mm u) (encodeToks (stemC ts m M (ansC M a) U)) := by
  unfold stemO stemC rngL
  rw [encodeToks_flatMap]
  refine deno_loop (den_sz hx hu) fun k i _ => ?_
  dsimp only
  have hi : Den x ((k, i) :: Γ) (addT u (varT k)) (U + i) := den_add (hu.cons _) den_var0
  refine deno_ite_eq (den_inChain hx (hu.cons _) hi) (fun h => ?_) (fun h => ?_)
  · rw [if_pos (by simpa using h), encodeToks_append]
    refine deno_seq (deno_nd hx (hm.cons _) hi) (deno_ite_eq
      (den_noBig hx (den_sz hx (hu.cons _)) hi) (fun h' => ?_) (fun h' => ?_))
    · rw [if_pos (by cases hv : noBig ts (sz ts U) (U + i) <;> simp_all)]
      simpa [encodeToks] using deno_nil
    · rw [if_neg (by cases hv : noBig ts (sz ts U) (U + i) <;> simp_all)]
      exact deno_ex hx hq (hM.cons _) (den_sz hx (hu.cons _)) hi (den_c 0)
  · rw [if_neg (by simpa using h)]
    simpa [encodeToks] using deno_nil

/-- Emission of the loop. -/
def loopCO (MM mm u : T) : TO :=
  loopO (szT u) fun i => iteO (inChainT u (addT u i))
    (iteO (noBigT (szT u) (addT u i))
      (seqO (exO MM (szT u) (addT u i) (notT (isLeafT (addT u i))))
        (iteO (isLeafT (addT u i)) (ndO mm (addT u i)) nilO)) nilO) nilO

omit hx in
lemma deno_loopC (hx : x = pack (encodeToks ts) q a) (hq : q ≤ a.length) {MM mm u : T}
    {M m U : ℕ} (hM : Den x Γ MM M) (hm : Den x Γ mm m) (hu : Den x Γ u U) :
    DenO x Γ (loopCO MM mm u) (encodeToks (loopC ts m M (ansC M a) U)) := by
  unfold loopCO loopC rngL
  rw [encodeToks_flatMap]
  refine deno_loop (den_sz hx hu) fun k i _ => ?_
  dsimp only
  have hi : Den x ((k, i) :: Γ) (addT u (varT k)) (U + i) := den_add (hu.cons _) den_var0
  refine deno_ite_eq (den_inChain hx (hu.cons _) hi) (fun h => ?_) (fun h => ?_)
  · rw [if_pos (by simpa using h)]
    refine deno_ite_eq (den_noBig hx (den_sz hx (hu.cons _)) hi) (fun h' => ?_) (fun h' => ?_)
    · rw [if_pos (by cases hv : noBig ts (sz ts U) (U + i) <;> simp_all), encodeToks_append]
      refine deno_seq (deno_ex hx hq (hM.cons _) (den_sz hx (hu.cons _)) hi
        (den_notB (den_isLeaf hx hi))) (deno_ite_eq (den_isLeaf hx hi) (fun h'' => ?_)
          (fun h'' => ?_))
      · rw [if_pos (by cases hv : isLeaf ts (U + i) <;> simp_all)]
        exact deno_nd hx (hm.cons _) hi
      · rw [if_neg (by cases hv : isLeaf ts (U + i) <;> simp_all)]
        simpa [encodeToks] using deno_nil
    · rw [if_neg (by cases hv : noBig ts (sz ts U) (U + i) <;> simp_all)]
      simpa [encodeToks] using deno_nil
  · rw [if_neg (by simpa using h)]
    simpa [encodeToks] using deno_nil

end CTLF

end PathChecking
