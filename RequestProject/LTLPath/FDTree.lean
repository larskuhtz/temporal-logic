module

public import RequestProject.LTLPath.FDTok

/-!
# Terms for the formula tree and the path data

Terms computing, on inputs `pack (encodeToks ts) q a`, the positional tree of the formula
(`tnd`, `tkd`, `tar`, leaves, leaf indices) and the path data (`sLen`, `lLen`, letters, leaf
values `lvTok`, polarities `polTok`).  Global values (`tF`, `sLen`, ...) are passed as terms
(`Gl`), so that a program computes them once.
-/

@[expose] public section

namespace PathChecking

namespace FD

open FE LL CTLP LTok

variable {x : Word} {Γ : Ctx} {ts : List Tok} {q : ℕ} {a : List Bool}

/-! ## Boolean helpers -/

lemma den_andB {s t : T} {b c : Bool} (hs : Den x Γ s b.toNat) (ht : Den x Γ t c.toNat) :
    Den x Γ (andT s t) (b && c).toNat :=
  (den_and (hs.of_eq (bv_bool b)) (ht.of_eq (bv_bool c))).of_eq (toNat_eq_bv (by simp)).symm

lemma den_orB {s t : T} {b c : Bool} (hs : Den x Γ s b.toNat) (ht : Den x Γ t c.toNat) :
    Den x Γ (orT s t) (b || c).toNat :=
  (den_or (hs.of_eq (bv_bool b)) (ht.of_eq (bv_bool c))).of_eq (toNat_eq_bv (by simp)).symm

lemma den_notB {s : T} {b : Bool} (hs : Den x Γ s b.toNat) : Den x Γ (notT s) (!b).toNat :=
  (den_not (hs.of_eq (bv_bool b))).of_eq (toNat_eq_bv (by simp)).symm

lemma den_eqB {s t : T} {u v : ℕ} (hs : Den x Γ s u) (ht : Den x Γ t v) :
    Den x Γ (eqT s t) (u == v).toNat :=
  (den_eq' hs ht).of_eq (toNat_eq_bv (by simp)).symm

lemma den_ltB {s t : T} {u v : ℕ} (hs : Den x Γ s u) (ht : Den x Γ t v) :
    Den x Γ (ltT s t) (decide (u < v)).toNat := den_lt hs ht

lemma den_leB {s t : T} {u v : ℕ} (hs : Den x Γ s u) (ht : Den x Γ t v) :
    Den x Γ (leT s t) (decide (u ≤ v)).toNat := (den_le hs ht).of_eq (bv_decide _).symm

lemma den_bool_of_bv {t : T} {P : Prop} {b : Bool} (h : Den x Γ t (bv P)) (e : b = true ↔ P) :
    Den x Γ t b.toNat := h.of_eq (toNat_eq_bv e).symm

/-! ## Globals -/

/-- Number of leaves before `p` (token level). -/
def tlix (ts : List Tok) (p : ℕ) : ℕ :=
  ((List.range p).filter fun r => tnd ts r && tar ts r == 0).length

/-- Global values. -/
structure Gl where
  F : T
  s : T
  l : T
  sE : T
  N : T
  Wm : T
  L : T

/-- The globals denote their values. -/
structure Gl.Ok (x : Word) (Γ : Ctx) (ts : List Tok) (g : Gl) : Prop where
  F : Den x Γ g.F (tF ts)
  s : Den x Γ g.s (sLen ts)
  l : Den x Γ g.l (lLen ts)
  sE : Den x Γ g.sE (LTok.sE ts)
  N : Den x Γ g.N ts.length
  Wm : Den x Γ g.Wm (sLen ts + (ts.length + 1) * lLen ts)
  L : Den x Γ g.L (tlix ts (tF ts))

lemma Gl.Ok.mono {g : Gl} (h : Gl.Ok x Γ ts g) {Γ' : Ctx} (hΓ : Γ ⊆ Γ') : Gl.Ok x Γ' ts g :=
  ⟨h.F.mono hΓ, h.s.mono hΓ, h.l.mono hΓ, h.sE.mono hΓ, h.N.mono hΓ, h.Wm.mono hΓ, h.L.mono hΓ⟩

lemma Gl.Ok.cons {g : Gl} (h : Gl.Ok x Γ ts g) (kv : ℕ × ℕ) : Gl.Ok x (kv :: Γ) ts g :=
  h.mono (List.subset_cons_self _ _)

variable {g : Gl}

/-! ## The positional tree -/

/-- Node test. -/
def tndT (g : Gl) (p : T) : T := andT (leT (cT 1) p) (andT (ltT p g.F) (leT (cT 5) (tcT p)))

/-- Kind. -/
def tkdT (p : T) : T := subT (tcT p) (cT 5)

/-- Arity. -/
def tarT (p : T) : T := lettT (tkdT p) fun k =>
  iteT (leT k (cT 1)) (cT 0) (iteT (orT (eqT k (cT 2)) (eqT k (cT 4))) (cT 1) (cT 2))

/-- Leaf test. -/
def leafT (g : Gl) (p : T) : T := andT (tndT g p) (eqT (tarT p) (cT 0))

/-- Leaf index. -/
def lixT (g : Gl) (p : T) : T := countT p fun r => leafT g r

section
variable (hx : x = pack (encodeToks ts) q a) (hg : Gl.Ok x Γ ts g)
include hx hg

lemma den_tnd {p : T} {P : ℕ} (hp : Den x Γ p P) : Den x Γ (tndT g p) (tnd ts P).toNat :=
  den_bool_of_bv (den_and (den_le (den_c 1) hp) (den_and (den_lt' hp hg.F)
    (den_le (den_c 5) (den_tc hx hp)))) (by simp [tnd])

omit hg in
lemma den_tkd {p : T} {P : ℕ} (hp : Den x Γ p P) : Den x Γ (tkdT p) (tkd ts P) :=
  den_sub (den_tc hx hp) (den_c 5)

omit hg in
lemma den_tar {p : T} {P : ℕ} (hp : Den x Γ p P) : Den x Γ (tarT p) (tar ts P) := by
  refine den_lett (den_tkd hx hp) fun k => ?_
  have hv : Den x ((k, tkd ts P) :: Γ) (varT k) (tkd ts P) := den_var0
  refine den_ite_eq (den_le hv (den_c 1)) (fun h => (den_c 0).of_eq ?_) (fun h => ?_)
  · simp at h; simp [tar, h]
  · simp at h
    refine den_ite_eq (den_or (den_eq' hv (den_c 2)) (den_eq' hv (den_c 4)))
      (fun h' => (den_c 1).of_eq ?_) (fun h' => (den_c 2).of_eq ?_)
    · simp at h'; simp [tar, show ¬ tkd ts P ≤ 1 by omega]; exact h'
    · simp at h'; simp [tar, h'.1, h'.2, show ¬ tkd ts P ≤ 1 by omega]

lemma den_leaf {p : T} {P : ℕ} (hp : Den x Γ p P) :
    Den x Γ (leafT g p) (tnd ts P && tar ts P == 0).toNat :=
  den_andB (den_tnd hx hg hp) (den_eqB (den_tar hx hp) (den_c 0))

lemma den_lix {p : T} {P : ℕ} (hp : Den x Γ p P) : Den x Γ (lixT g p) (tlix ts P) := by
  refine (den_count (body := fun r => leafT g r) (f := fun r => (tnd ts r && tar ts r == 0).toNat)
    hp fun k i _ => den_leaf hx (hg.cons _) den_var0).of_eq ?_
  unfold cntU tlix
  rw [← List.countP_eq_length_filter]
  exact List.countP_congr fun i _ => by cases h : (tnd ts i && tar ts i == 0) <;> simp [h]

omit hx hg in
lemma cnt_eq_cntP (c A B : ℕ) : cnt ts c A B = cntP ts (fun v => v == c) A B := by
  unfold cnt cntP
  exact List.countP_congr fun i _ => by simp

omit hg in
lemma den_cnt {c : ℕ} {s t : T} {A B : ℕ} (hs : Den x Γ s A) (ht : Den x Γ t B) :
    Den x Γ (cntPT (isT c) s t) (cnt ts c A B) :=
  (den_cntP hx (denP_is c) hs ht).of_eq (cnt_eq_cntP c A B).symm

end

/-! ## Global values -/

/-- End of the formula. -/
def tFT : T := fendT (cT 1)
/-- End of the stem. -/
def sET (F : T) : T := subT (tend1T (addT F (cT 1))) (cT 1)
/-- Number of letters of the stem. -/
def sLenT (F sE : T) : T := cntPT (isT 3) (addT F (cT 2)) sE
/-- Number of letters of the loop. -/
def lLenT (sE N : T) : T := cntPT (isT 3) (addT sE (cT 2)) (subT N (cT 1))

section
variable (hx : x = pack (encodeToks ts) q a)
include hx

lemma den_tF : Den x Γ tFT (tF ts) := den_fend hx (den_c 1)

lemma den_sE {F : T} (hF : Den x Γ F (tF ts)) : Den x Γ (sET F) (LTok.sE ts) :=
  den_sub (den_tend1 hx (den_add hF (den_c 1))) (den_c 1)

lemma den_sLen {F s : T} (hF : Den x Γ F (tF ts)) (hs : Den x Γ s (LTok.sE ts)) :
    Den x Γ (sLenT F s) (sLen ts) := by
  rw [sLen, show tP ts + 1 = tF ts + 2 from rfl]; exact den_cnt hx (den_add hF (den_c 2)) hs

lemma den_lLen {s N : T} (hs : Den x Γ s (LTok.sE ts)) (hN : Den x Γ N ts.length) :
    Den x Γ (lLenT s N) (lLen ts) := den_cnt hx (den_add hs (den_c 2)) (den_sub hN (den_c 1))

end

/-! ## Letters and leaf values -/

/-- Position of the `m`-th opening bracket in `[b, e)`. -/
def setAtT (b e m : T) : T :=
  ffindT (fun j => andT (isT 3 (tcT j)) (eqT (cntPT (isT 3) b j) m)) b e

/-- Start of the `i`-th letter. -/
def lposT (g : Gl) (i : T) : T :=
  iteT (ltT i g.s) (setAtT (addT g.F (cT 2)) g.sE i)
    (setAtT (addT g.sE (cT 2)) (subT g.N (cT 1)) (modT (subT i g.s) g.l))

/-- Length of the number at `v`. -/
def numLenT (v : T) : T := subT (numEndT v) v

/-- Equal numbers at `u` and `v`. -/
def numEqAtT (u v : T) : T := allT (numLenT v) fun m => eqT (tcT (addT u m)) (tcT (addT v m))

/-- The letter at `j` contains the number at `v`. -/
def memAtT (j v : T) : T := lettT (tend1T j) fun te =>
  exT te fun u => andT (ltT j u) (andT (ltT (addT u (cT 1)) te)
    (andT (orT (isT 3 (tcT (subT u (cT 1)))) (isT 2 (tcT (subT u (cT 1))))) (numEqAtT u v)))

/-- Leaf value. -/
def lvTokT (g : Gl) (q i : T) : T :=
  iteT (isT 1 (tkdT q)) (cT 1) (memAtT (lposT g i) (addT q (cT 1)))

/-- Number of negations above `q`. -/
def negAboveT (g : Gl) (q : T) : T :=
  countT q fun r => andT (tndT g r) (andT (isT 2 (tkdT r)) (ltT q (fendT r)))

/-- Polarity. -/
def polTokT (g : Gl) (q : T) : T := isT 1 (modT (negAboveT g q) (cT 2))

section
variable (hx : x = pack (encodeToks ts) q a) (hg : Gl.Ok x Γ ts g)
include hx

lemma den_setAt {b e m : T} {B E M : ℕ} (hb : Den x Γ b B) (he : Den x Γ e E)
    (hm : Den x Γ m M) : Den x Γ (setAtT b e m) (setAt ts B E M) := by
  refine den_ffind (Pb := fun j => tc ts j == 3 && cnt ts 3 B j == M) (fun Γ' hΓ t v ht => ?_) hb he
  exact den_andB (den_eqB (den_tc hx ht) (den_c 3)) (den_eqB (den_cnt hx (hb.mono hΓ) ht)
    (hm.mono hΓ))

include hg

lemma den_lpos {i : T} {I : ℕ} (hi : Den x Γ i I) : Den x Γ (lposT g i) (lpos ts I) := by
  unfold lpos
  refine den_ite_eq (den_lt' hi hg.s) (fun h => ?_) (fun h => ?_)
  · simp at h; rw [if_pos h, show tP ts + 1 = tF ts + 2 from rfl]
    exact den_setAt hx (den_add hg.F (den_c 2)) hg.sE hi
  · simp at h; rw [if_neg (by omega)]
    rw [show lB ts = LTok.sE ts + 2 from rfl]
    exact den_setAt hx (den_add hg.sE (den_c 2)) (den_sub hg.N (den_c 1))
      (den_mod (den_sub hi hg.s) hg.l)

omit hg

lemma den_numLen {v : T} {V : ℕ} (hv : Den x Γ v V) : Den x Γ (numLenT v) (numLen ts V) :=
  den_sub (den_numEnd hx hv) hv

lemma den_numEqAt {u v : T} {U V : ℕ} (hu : Den x Γ u U) (hv : Den x Γ v V) :
    Den x Γ (numEqAtT u v) (numEqAt ts U V).toNat := by
  refine den_bool_of_bv (den_all (body := fun m => eqT (tcT (addT u m)) (tcT (addT v m)))
    (P := fun m => tc ts (U + m) = tc ts (V + m)) (den_numLen hx hv) fun k i _ =>
      den_eq' (den_tc hx (den_add (hu.cons _) den_var0)) (den_tc hx (den_add (hv.cons _) den_var0)))
    (by simp [numEqAt])

lemma den_memAt {j v : T} {J V : ℕ} (hj : Den x Γ j J) (hv : Den x Γ v V) :
    Den x Γ (memAtT j v) (memAt ts J V).toNat := by
  refine den_lett (den_tend1 hx hj) fun k => ?_
  have hte : Den x ((k, tend1 ts J) :: Γ) (varT k) (tend1 ts J) := den_var0
  refine den_bool_of_bv (den_ex (P := fun u => J < u ∧ u + 1 < tend1 ts J ∧
    (tc ts (u - 1) = 3 ∨ tc ts (u - 1) = 2) ∧ numEqAt ts u V = true) hte fun k' i _ => ?_)
    (by simp [memAt])
  have hu : Den x ((k', i) :: (k, tend1 ts J) :: Γ) (varT k') i := den_var0
  have hc := den_tc hx (den_sub hu (den_c 1))
  exact den_and (den_lt' ((hj.cons _).cons _) hu) (den_and (den_lt' (den_add hu (den_c 1))
    (hte.cons _)) (den_and (den_or (den_eq' hc (den_c 3)) (den_eq' hc (den_c 2)))
      ((den_numEqAt hx hu ((hv.cons _).cons _)).of_eq (bv_bool _))))

include hg

lemma den_lvTok {q' i : T} {Q I : ℕ} (hq : Den x Γ q' Q) (hi : Den x Γ i I) :
    Den x Γ (lvTokT g q' i) (lvTok ts Q I).toNat := by
  unfold lvTok
  refine den_ite_eq (den_eq' (den_tkd hx hq) (den_c 1)) (fun h => ?_) (fun h => ?_)
  · simp at h; rw [if_pos h]; exact den_c 1
  · simp at h; rw [if_neg h]
    exact den_memAt hx (den_lpos hx hg hi) (den_add hq (den_c 1))

lemma den_negAbove {q' : T} {Q : ℕ} (hq : Den x Γ q' Q) :
    Den x Γ (negAboveT g q') (negAbove ts Q) := by
  refine (den_count (body := fun r => andT (tndT g r) (andT (isT 2 (tkdT r)) (ltT q' (fendT r))))
    (f := fun r => bv (tnd ts r = true ∧ tkd ts r = 2 ∧ Q < fend ts r)) hq fun k i _ => ?_).of_eq ?_
  · have hr : Den x ((k, i) :: Γ) (varT k) i := den_var0
    exact den_and ((den_tnd hx (hg.cons _) hr).of_eq (bv_bool _))
      (den_and (den_eq' (den_tkd hx hr) (den_c 2)) (den_lt' (hq.cons _) (den_fend hx hr)))
  · rw [cntU_bv, negAbove, List.countP_eq_length_filter]
    congr 1
    refine List.filter_congr fun r _ => ?_
    by_cases h : tkd ts r = 2 <;> simp [h]

lemma den_polTok {q' : T} {Q : ℕ} (hq : Den x Γ q' Q) :
    Den x Γ (polTokT g q') (polTok ts Q).toNat :=
  den_eqB (den_mod (den_negAbove hx hg hq) (den_c 2)) (den_c 1)

end

end FD

end PathChecking
