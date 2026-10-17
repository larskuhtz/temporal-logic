module

public import RequestProject.CTLTree.FQ2

/-!
# The query function of the CTL round algorithm

Output terms producing the translated formula (`trCO`) and the whole query (`qProgC`); the query
function `qFunC` is logspace computable and meets the specification `QSpecC`.
-/

@[expose] public section

namespace PathChecking

namespace CTLF

open FE LL CTLP LTok FD CTLT ShallowP

variable {x : Word} {Γ : Ctx} {ts : List Tok} {q : ℕ} {a : List Bool}

/-! ## End of CTL formulas -/

/-- Counting predicate of CTL formulas. -/
def upCT (t : T) : T := orT (orT (isT 8 t) (isT 10 t)) (isT 11 t)

lemma denP_upC : DenP x Γ upCT upC := fun Γ' hΓ t v ht =>
  (den_orB (den_orB (den_eqB ht (den_c 8)) (den_eqB ht (den_c 10))) (den_eqB ht (den_c 11))).of_eq
    (by simp [upC])

/-- End of the CTL formula at `p`. -/
def fendCT (p : T) : T := scanFT upCT downFT p (cT 1)

lemma den_fendC (hx : x = pack (encodeToks ts) q a) {p : T} {P : ℕ} (hp : Den x Γ p P) :
    Den x Γ (fendCT p) (fendC ts P) :=
  den_scan hx (fun k => by simp [upC, downF]; omega) denP_upC denP_downF hp (den_c 1) le_rfl

/-! ## Fixed pieces -/

/-- Output of an LTL atom. -/
def apO (n : T) : TO := seqO (tokO (cT 5)) (natO n)

lemma deno_ap {n : T} {N : ℕ} (hn : Den x Γ n N) : DenO x Γ (apO n) (encodeToks (apT N)) :=
  (deno_seq (deno_tok (den_c 5)) (deno_nat hn)).of_eq (by rw [apT, encodeToks_cons]; rfl)

def preEXO (p : T) : TO :=
  seqO (toksO [Tok.tag 4, Tok.tag 2, Tok.tag 3, Tok.tag 2]) (seqO (apO (addT p (cT 2)))
    (seqO (toksO [Tok.tag 2, Tok.tag 4, Tok.tag 3, Tok.tag 2]) (apO (cT 0))))

lemma deno_preEX {p : T} {P : ℕ} (hp : Den x Γ p P) : DenO x Γ (preEXO p) (encodeToks (preEX P)) :=
  (deno_seq (deno_toks _) (deno_seq (deno_ap (den_add hp (den_c 2))) (deno_seq (deno_toks _)
    (deno_ap (den_c 0))))).of_eq (by simp only [preEX, encodeToks_append, List.append_assoc])

def secEUO (k : T) : TO :=
  seqO (toksO [Tok.tag 2, Tok.tag 3, Tok.tag 2, Tok.tag 3]) (seqO (apO (cT 0))
    (seqO (apO (addT k (cT 2))) (seqO (toksO [Tok.tag 2, Tok.tag 3, Tok.tag 2]) (apO (cT 0)))))

lemma deno_secEU {k : T} {K : ℕ} (hk : Den x Γ k K) : DenO x Γ (secEUO k) (encodeToks (secEU K)) :=
  (deno_seq (deno_toks _) (deno_seq (deno_ap (den_c 0)) (deno_seq (deno_ap (den_add hk (den_c 2)))
    (deno_seq (deno_toks _) (deno_ap (den_c 0)))))).of_eq
    (by simp only [secEU, encodeToks_append, List.append_assoc])

def secAUO (k : T) : TO :=
  seqO (toksO [Tok.tag 2, Tok.tag 3, Tok.tag 2, Tok.tag 3]) (seqO (apO (cT 0))
    (seqO (toksO [Tok.tag 3]) (seqO (apO (addT k (cT 2))) (seqO (apO (cT 1))
      (seqO (toksO [Tok.tag 2, Tok.tag 3, Tok.tag 2]) (apO (cT 0)))))))

lemma deno_secAU {k : T} {K : ℕ} (hk : Den x Γ k K) : DenO x Γ (secAUO k) (encodeToks (secAU K)) :=
  (deno_seq (deno_toks _) (deno_seq (deno_ap (den_c 0)) (deno_seq (deno_toks _)
    (deno_seq (deno_ap (den_add hk (den_c 2))) (deno_seq (deno_ap (den_c 1))
      (deno_seq (deno_toks _) (deno_ap (den_c 0)))))))).of_eq
    (by
      simp only [secAU, encodeToks_append, List.append_assoc, encodeToks_cons]
      rfl)

def preEUO : TO := toksO preEU

lemma deno_preEU : DenO x Γ preEUO (encodeToks preEU) := deno_toks _

def preAUO (p : T) : TO := seqO (toksO [Tok.tag 5]) (secEUO p)

lemma deno_preAU {p : T} {P : ℕ} (hp : Den x Γ p P) : DenO x Γ (preAUO p) (encodeToks (preAU P)) :=
  (deno_seq (deno_toks _) (deno_secEU hp)).of_eq (by rw [preAU, encodeToks_cons, encodeToks_cons]; rfl)

/-! ## The translation -/

variable (hx : x = pack (encodeToks ts) q a)
include hx

lemma deno_ite_is {k : ℕ} {t : T} {V : ℕ} (ht : Den x Γ t V) {o1 o2 : TO} {w1 w2 : Word}
    (h1 : V = k → DenO x Γ o1 w1) (h2 : V ≠ k → DenO x Γ o2 w2) :
    DenO x Γ (iteO (isT k t) o1 o2) (if V = k then w1 else w2) := by
  refine deno_ite_eq (den_is ht) (fun h => ?_) (fun h => ?_)
  · simp only [ne_eq, bv_eq_zero, not_not] at h; rw [if_pos h]; exact h1 h
  · simp only [bv_eq_zero] at h; rw [if_neg h]; exact h2 h

/-- Emission of the body at position `p`. -/
def trBodyO (mm p : T) : TO :=
  iteO (isT 5 (tcT p)) (seqO (toksO [Tok.tag 0]) (repO mm (tokO (cT 1))))
    (iteO (isT 6 (tcT p)) (toksO [Tok.tag 1])
      (iteO (isT 7 (tcT p)) (toksO [Tok.tag 2])
        (iteO (isT 8 (tcT p)) (toksO [Tok.tag 3])
          (iteO (isT 9 (tcT p)) (preEXO p)
            (iteO (isT 10 (tcT p)) preEUO
              (iteO (isT 11 (tcT p)) (preAUO p) (cpO p)))))))

lemma deno_trBody {mm p : T} {m P : ℕ} (hm : Den x Γ mm m) (hp : Den x Γ p P) :
    DenO x Γ (trBodyO mm p) (encodeToks (trBodyC ts m P)) := by
  have htc := den_tc hx hp
  unfold trBodyO trBodyC
  have e : ∀ (c : Prop) [Decidable c] (l1 l2 : List Tok),
      encodeToks (if c then l1 else l2) = if c then encodeToks l1 else encodeToks l2 :=
    fun c _ l1 l2 => by split <;> rfl
  simp only [e]
  refine deno_ite_is hx htc (fun _ => ?_) fun _ => deno_ite_is hx htc (fun _ => deno_toks _)
    fun _ => deno_ite_is hx htc (fun _ => deno_toks _) fun _ => deno_ite_is hx htc
    (fun _ => deno_toks _) fun _ => deno_ite_is hx htc (fun _ => deno_preEX hp)
    fun _ => deno_ite_is hx htc (fun _ => deno_preEU) fun _ => deno_ite_is hx htc
    (fun _ => deno_preAU hp) fun _ => deno_cp hx hp
  rw [encodeToks_cons, encodeToks_replicate]
  exact deno_seq (deno_toks [Tok.tag 0] |>.of_eq (by rw [encodeToks_single]))
    (deno_rep hm fun Γ' _ => (deno_tok (den_c 1)).of_eq (by rw [encodeToks_single]; rfl))

/-- Emission of the contribution of position `k` to the prefix of `p`. -/
def secAtO (p k : T) : TO :=
  iteO (andT (isT 10 (tcT k)) (eqT (fendCT (addT k (cT 1))) p)) (secEUO k)
    (iteO (andT (isT 11 (tcT k)) (eqT (fendCT (addT k (cT 1))) p)) (secAUO k) nilO)

lemma deno_secAt {p k : T} {P K : ℕ} (hp : Den x Γ p P) (hk : Den x Γ k K) :
    DenO x Γ (secAtO p k) (encodeToks (secAt ts P K)) := by
  unfold secAtO secAt
  have hf := den_fendC hx (den_add hk (den_c 1))
  refine deno_ite_eq (den_and (den_is (den_tc hx hk)) (den_eq' hf hp)) (fun h => ?_) (fun h => ?_)
  · simp only [ne_eq, bv_eq_zero, not_not] at h; rw [if_pos h]; exact deno_secEU hk
  · simp only [bv_eq_zero] at h; rw [if_neg h]
    refine deno_ite_eq (den_and (den_is (den_tc hx hk)) (den_eq' hf hp)) (fun h' => ?_)
      (fun h' => ?_)
    · simp only [ne_eq, bv_eq_zero, not_not] at h'; rw [if_pos h']; exact deno_secAU hk
    · simp only [bv_eq_zero] at h'; rw [if_neg h']; exact deno_nil

/-- Emission at position `p` of the translation of the formula at `j`. -/
def trAtCO (mm j p : T) : TO :=
  seqO (loopO (subT p j) fun i => secAtO p (addT j i)) (trBodyO mm p)

lemma deno_trAtC {mm j p : T} {m J P : ℕ} (hm : Den x Γ mm m) (hj : Den x Γ j J)
    (hp : Den x Γ p P) : DenO x Γ (trAtCO mm j p) (encodeToks (trAtC ts m J P)) := by
  unfold trAtCO trAtC secC rngL
  rw [encodeToks_append, encodeToks_flatMap]
  exact deno_seq (deno_loop (den_sub hp hj) fun k i _ =>
    deno_secAt hx (hp.cons _) (den_add (hj.cons _) den_var0)) (deno_trBody hx hm hp)

/-- Emission of the translation of the formula at `j`. -/
def trCO (mm j : T) : TO := loopO (subT (fendCT j) j) fun i => trAtCO mm j (addT j i)

lemma deno_trC {mm j : T} {m J : ℕ} (hm : Den x Γ mm m) (hj : Den x Γ j J) :
    DenO x Γ (trCO mm j) (encodeToks (trCToks ts m J)) := by
  unfold trCO trCToks rng
  rw [encodeToks_flatMap]
  exact deno_loop (den_sub (den_fendC hx hj) hj) fun k i _ =>
    deno_trAtC hx (hm.cons _) (hj.cons _) (den_add (hj.cons _) den_var0)

/-! ## The query -/

/-- Emission of the query. -/
def CQO (MM mm u j : T) : TO :=
  seqO (toksO [Tok.lpar]) (seqO (trCO mm j) (seqO (toksO [Tok.rpar, Tok.lpar])
    (seqO (stemO MM mm u) (seqO (toksO [Tok.rpar, Tok.lpar]) (seqO (loopCO MM mm u)
      (toksO [Tok.rpar]))))))

omit hx in
lemma deno_CQ (hx : x = pack (encodeToks ts) q a) (hq : q ≤ a.length) {MM mm u j : T}
    {M m U J : ℕ} (hM : Den x Γ MM M) (hm : Den x Γ mm m) (hu : Den x Γ u U)
    (hj : Den x Γ j J) : DenO x Γ (CQO MM mm u j) (encodeToks (CQ ts m M U J (ansC M a))) := by
  unfold CQO
  refine (deno_seq (deno_toks _) (deno_seq (deno_trC hx hm hj) (deno_seq (deno_toks _)
    (deno_seq (deno_stem hx hq hM hm hu) (deno_seq (deno_toks _) (deno_seq
      (deno_loopC hx hq hM hm hu) (deno_toks _))))))).of_eq ?_
  simp only [CQ, encodeToks_cons, encodeToks_append, List.append_assoc, encodeToks_single]
  rfl

end CTLF

open FE FD CTLF

/-- The query program. -/
def qProgC : TO :=
  lettO nT fun N => lettO (addT N (cT 1)) fun MM => lettO (addT N (cT 3)) fun mm =>
    lettO qT fun qv => lettO (divT qv MM) fun u => lettO (modT qv MM) fun j => CQO MM mm u j

/-- The query function. -/
def qFunC (x : Word) : Word := FE.evO x 0 (fun _ => 0) (qProgC 0)

/-- The query function is logspace computable. -/
theorem qFunC_logspace : LogspaceComputable qFunC :=
  FE.logspaceComputable_of_O (qProgC 0) (by decide +kernel) qFunC fun _ => rfl

/-- **The query function meets its specification.** -/
theorem qFunC_spec : CTLT.QSpecC qFunC := by
  intro ts a u j ha hu hj
  set M := ts.length + 1
  have hqa : u * M + j ≤ a.length := by
    rw [ha, CTLT.encLenC]
    have h1 : u * M + j < M * M := by nlinarith
    have h2 : M * M ≤ (5 * ts.length + 1) ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    omega
  set x := pack (encodeToks ts) (u * M + j) a with hx
  have hdiv : (u * M + j) / M = u := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (u * M + j) % M = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have key : DenO x [] qProgC (encodeToks (CTLT.CQ ts (ts.length + 3) M u j (CTLT.ansC M a))) := by
    unfold qProgC
    refine deno_lett (den_n hx) fun kN => ?_
    refine deno_lett (den_add den_var0 (den_c 1)) fun kM => ?_
    refine deno_lett (den_add (den_var (k := kN) (v := ts.length) (by simp)) (den_c 3))
      fun km => ?_
    refine deno_lett (den_q hx hqa) fun kq => ?_
    refine deno_lett (den_div den_var0 (den_var (k := kM) (v := ts.length + 1) (by simp)))
      fun ku => ?_
    refine deno_lett (den_mod (den_var (k := kq) (v := u * M + j) (by simp))
      (den_var (k := kM) (v := ts.length + 1) (by simp))) fun kj => ?_
    refine (deno_CQ hx hqa (den_var (k := kM) (v := ts.length + 1) (by simp))
      (den_var (k := km) (v := ts.length + 3) (by simp))
      (den_var (k := ku) (v := (u * M + j) / (ts.length + 1)) (by simp)) den_var0).of_eq ?_
    rw [show (u * M + j) / (ts.length + 1) = u from hdiv,
      show (u * M + j) % (ts.length + 1) = j from hmod]
  exact key 0 _ (fun _ h => absurd h (by simp))

end PathChecking
