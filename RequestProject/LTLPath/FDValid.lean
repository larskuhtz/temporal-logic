module

public import RequestProject.LTLPath.FDTree
public import RequestProject.LTLPath.ValidI

/-!
# Terms for the local recognition of instances

`validT` is a term that denotes `bv (ValidI ts)` on inputs `pack (encodeToks ts) q a`
(`den_valid`).
-/

@[expose] public section

namespace PathChecking

namespace FD

open FE LL CTLP LTok Classical

variable {x : Word} {Γ : Ctx} {ts : List Tok} {q : ℕ} {a : List Bool}

/-! ## Terms -/

/-- Implication. -/
def impT (a b : T) : T := orT (notT a) b

/-- The local rule `Lr`. -/
def LrT (b c g : T) : T :=
  lettT b fun b => lettT c fun c =>
    andT (leT c (cT 4)) (andT (impT (isT 3 c) (orT (isT 4 b) (andT (isT 3 b) g)))
      (andT (impT (isT 4 c) (orT (isT 2 b) (andT (isT 3 b) (notT g))))
        (andT (impT (leT c (cT 2)) (orT (leT b (cT 2)) (andT (isT 3 b) (notT g))))
          (impT (isT 2 c) (notT (isT 0 b))))))

/-- The local rule `RF`. -/
def RFT (b c : T) : T :=
  lettT b fun b => lettT c fun c =>
    orT (andT (leT c (cT 1)) (orT (leT b (cT 1)) (isT 5 b)))
      (orT (andT (isT 2 c) (orT (isT 1 b) (isT 5 b)))
        (andT (leT (cT 5) c) (andT (leT c (cT 10)) (notT (orT (leT b (cT 1)) (isT 5 b))))))

/-- First `sep` at or after `s`. -/
def nET (s : T) : T := ffindT (fun u => isT 2 (tcT u)) s nT

/-- Comparison of numbers `NumLt`. -/
def NumLtT (s t : T) : T :=
  lettT s fun s => lettT t fun t => lettT (nET s) fun es => lettT (nET t) fun et =>
    orT (ltT (subT es s) (subT et t)) (andT (eqT (subT es s) (subT et t))
      (exT (subT es s) fun m => andT (isT 0 (tcT (addT s m))) (andT (isT 1 (tcT (addT t m)))
        (allT (subT es s) fun k => impT (ltT m k) (eqT (tcT (addT s k)) (tcT (addT t k)))))))

/-- The condition `NumOK`. -/
def NumOKT (s : T) : T :=
  lettT s fun s => lettT (nET s) fun e =>
    impT (andT (leT (tcT s) (cT 2)) (orT (isT 2 (tcT (subT s (cT 1)))) (isT 3 (tcT (subT s (cT 1))))))
      (impT (leT (tcT (addT e (cT 1))) (cT 2)) (NumLtT s (addT e (cT 1))))

/-- The formula conditions `FormOK`. -/
def formT (F : T) : T :=
  andT (isT 3 (tcT (cT 0))) (andT (ltT F nT) (andT (isT 4 (tcT F))
    (andT (notT (orT (leT (tcT (subT F (cT 1))) (cT 1)) (isT 5 (tcT (subT F (cT 1))))))
      (allT F fun j => impT (leT (cT 1) j) (RFT (tcT (subT j (cT 1))) (tcT j))))))

/-- The path conditions `PathOK`. -/
def pathT (F sE : T) : T :=
  lettT (addT F (cT 1)) fun P => lettT nT fun N =>
    andT (isT 3 (tcT P)) (andT (ltT P sE) (andT (isT 4 (tcT sE))
      (andT (orT (isT 4 (tcT (subT sE (cT 1)))) (eqT (subT sE (cT 1)) P))
      (andT (isT 3 (tcT (addT sE (cT 1)))) (andT (isT 3 (tcT (addT sE (cT 2))))
      (andT (leT (addT sE (cT 5)) N)
      (andT (isT 4 (tcT (subT N (cT 1)))) (andT (isT 4 (tcT (subT N (cT 2))))
      (andT (allT (subT N (cT 1)) fun j => impT (ltT P j) (impT (neT j sE)
          (impT (neT j (addT sE (cT 1)))
            (LrT (tcT (subT j (cT 1))) (tcT j)
              (orT (eqT (subT j (cT 1)) P) (eqT (subT j (cT 1)) (addT sE (cT 1))))))))
        (allT N fun s => impT (ltT P s) (NumOKT s)))))))))))

/-- The recognizer of instances. -/
def validT : T := lettT tFT fun F => lettT (sET F) fun sE => andT (formT F) (pathT F sE)

/-! ## Denotations -/

lemma den_imp {a b : T} {P Q : Prop} (ha : Den x Γ a (bv P)) (hb : Den x Γ b (bv Q)) :
    Den x Γ (impT a b) (bv (P → Q)) :=
  (den_or (den_not ha) hb).of_eq (bv_congr ⟨fun h hP => h.resolve_left (not_not.2 hP),
    fun h => (Classical.em P).elim (fun hP => Or.inr (h hP)) Or.inl⟩)

lemma den_is {k : ℕ} {t : T} {v : ℕ} (ht : Den x Γ t v) : Den x Γ (isT k t) (bv (v = k)) :=
  den_eq' ht (den_c k)

lemma den_Lr {b c g : T} {B C : ℕ} {G : Prop} (hb : Den x Γ b B) (hc : Den x Γ c C)
    (hg : Den x Γ g (bv G)) : Den x Γ (LrT b c g) (bv (Lr B C G)) := by
  refine den_lett hb fun k1 => den_lett (hc.cons _) fun k2 => ?_
  have hB : Den x ((k2, C) :: (k1, B) :: Γ) (varT k1) B := den_var (by simp)
  have hC : Den x ((k2, C) :: (k1, B) :: Γ) (varT k2) C := den_var0
  have hG := (hg.cons (k1, B)).cons (k2, C)
  exact den_and (den_le hC (den_c 4)) (den_and (den_imp (den_is hC) (den_or (den_is hB)
    (den_and (den_is hB) hG))) (den_and (den_imp (den_is hC) (den_or (den_is hB)
    (den_and (den_is hB) (den_not hG)))) (den_and (den_imp (den_le hC (den_c 2))
    (den_or (den_le hB (den_c 2)) (den_and (den_is hB) (den_not hG))))
    (den_imp (den_is hC) (den_not (den_is hB))))))

lemma den_RF {b c : T} {B C : ℕ} (hb : Den x Γ b B) (hc : Den x Γ c C) :
    Den x Γ (RFT b c) (bv (RF B C)) := by
  refine den_lett hb fun k1 => den_lett (hc.cons _) fun k2 => ?_
  have hB : Den x ((k2, C) :: (k1, B) :: Γ) (varT k1) B := den_var (by simp)
  have hC : Den x ((k2, C) :: (k1, B) :: Γ) (varT k2) C := den_var0
  exact den_or (den_and (den_le hC (den_c 1)) (den_or (den_le hB (den_c 1)) (den_is hB)))
    (den_or (den_and (den_is hC) (den_or (den_is hB) (den_is hB)))
      (den_and (den_le (den_c 5) hC) (den_and (den_le hC (den_c 10))
        (den_not (den_or (den_le hB (den_c 1)) (den_is hB))))))

section

variable (hx : x = pack (encodeToks ts) q a)
include hx

lemma den_nE {s : T} {S : ℕ} (hs : Den x Γ s S) : Den x Γ (nET s) (nE ts S) :=
  den_ffind (Pb := fun u => tc ts u == 2) (fun Γ' _ _ _ ht => denP_is 2 Γ' (fun _ h => h) _ _
    (den_tc hx ht)) hs (den_n hx)

lemma den_NumLt {s t : T} {S U : ℕ} (hs : Den x Γ s S) (ht : Den x Γ t U) :
    Den x Γ (NumLtT s t) (bv (NumLt ts S U)) := by
  refine den_lett hs fun k1 => den_lett (ht.cons _) fun k2 => ?_
  set Γ2 := (k2, U) :: (k1, S) :: Γ
  have hS : Den x Γ2 (varT k1) S := den_var (by simp [Γ2])
  have hU : Den x Γ2 (varT k2) U := den_var0
  refine den_lett (den_nE hx hS) fun k3 => den_lett (den_nE hx (hU.cons _)) fun k4 => ?_
  set Γ4 := (k4, nE ts U) :: (k3, nE ts S) :: Γ2
  have s4 : Γ2 ⊆ Γ4 := fun y hy => by simp [Γ4, hy]
  have hS4 := hS.mono s4
  have hU4 := hU.mono s4
  have hes : Den x Γ4 (varT k3) (nE ts S) := den_var (by simp [Γ4])
  have het : Den x Γ4 (varT k4) (nE ts U) := den_var0
  refine den_or (den_lt' (den_sub hes hS4) (den_sub het hU4)) (den_and (den_eq' (den_sub hes hS4)
    (den_sub het hU4)) (den_ex (den_sub hes hS4) fun k m _ => ?_))
  refine den_and (den_is (den_tc hx (den_add (hS4.cons _) den_var0)))
    (den_and (den_is (den_tc hx (den_add (hU4.cons _) den_var0)))
      (den_all (den_sub (hes.cons _) (hS4.cons _)) fun k' i _ => ?_))
  exact den_imp (den_lt' (den_var (by simp)) den_var0)
    (den_eq' (den_tc hx (den_add ((hS4.cons _).cons _) den_var0))
      (den_tc hx (den_add ((hU4.cons _).cons _) den_var0)))

lemma den_NumOK {s : T} {S : ℕ} (hs : Den x Γ s S) : Den x Γ (NumOKT s) (bv (NumOK ts S)) := by
  refine den_lett hs fun k1 => den_lett (den_nE hx den_var0) fun k2 => ?_
  have hS : Den x ((k2, nE ts S) :: (k1, S) :: Γ) (varT k1) S := den_var (by simp)
  have he : Den x ((k2, nE ts S) :: (k1, S) :: Γ) (varT k2) (nE ts S) := den_var0
  exact den_imp (den_and (den_le (den_tc hx hS) (den_c 2))
    (den_or (den_is (den_tc hx (den_sub hS (den_c 1)))) (den_is (den_tc hx (den_sub hS (den_c 1))))))
    (den_imp (den_le (den_tc hx (den_add he (den_c 1))) (den_c 2))
      (den_NumLt hx hS (den_add he (den_c 1))))

lemma den_form {F : T} (hF : Den x Γ F (tF ts)) : Den x Γ (formT F) (bv (FormOK ts)) :=
  den_and (den_is (den_tc hx (den_c 0))) (den_and (den_lt' hF (den_n hx))
    (den_and (den_is (den_tc hx hF)) (den_and (den_not (den_or (den_le (den_tc hx
      (den_sub hF (den_c 1))) (den_c 1)) (den_is (den_tc hx (den_sub hF (den_c 1))))))
      (den_all hF fun _ _ _ => den_imp (den_le (den_c 1) den_var0)
        (den_RF (den_tc hx (den_sub den_var0 (den_c 1))) (den_tc hx den_var0))))))

lemma den_path {F sE : T} (hF : Den x Γ F (tF ts)) (hs : Den x Γ sE (LTok.sE ts)) :
    Den x Γ (pathT F sE) (bv (PathOK ts)) := by
  refine den_lett (den_add hF (den_c 1)) fun k1 => den_lett (den_n hx) fun k2 => ?_
  set Γ2 := (k2, ts.length) :: (k1, tF ts + 1) :: Γ
  have hP : Den x Γ2 (varT k1) (tP ts) := den_var (by simp [Γ2, tP])
  have hN : Den x Γ2 (varT k2) ts.length := den_var0
  have hs2 : Den x Γ2 sE (LTok.sE ts) := (hs.cons _).cons _
  refine den_and (den_is (den_tc hx hP)) (den_and (den_lt' hP hs2) (den_and (den_is (den_tc hx hs2))
    (den_and (den_or (den_is (den_tc hx (den_sub hs2 (den_c 1)))) (den_eq' (den_sub hs2 (den_c 1)) hP))
    (den_and (den_is (den_tc hx (den_add hs2 (den_c 1)))) (den_and (den_is (den_tc hx (den_add hs2
      (den_c 2)))) (den_and (den_le (den_add hs2 (den_c 5)) hN) (den_and (den_is (den_tc hx (den_sub hN
      (den_c 1)))) (den_and (den_is (den_tc hx (den_sub hN (den_c 2)))) (den_and ?_ ?_)))))))))
  · refine den_all (den_sub hN (den_c 1)) fun k j _ => ?_
    have hj : Den x ((k, j) :: Γ2) (varT k) j := den_var0
    exact den_imp (den_lt' (hP.cons _) hj) (den_imp (den_ne hj (hs2.cons _))
      (den_imp (den_ne hj (den_add (hs2.cons _) (den_c 1)))
        (den_Lr (den_tc hx (den_sub hj (den_c 1))) (den_tc hx hj)
          (den_or (den_eq' (den_sub hj (den_c 1)) (hP.cons _))
            (den_eq' (den_sub hj (den_c 1)) (den_add (hs2.cons _) (den_c 1)))))))
  · exact den_all hN fun k s _ => den_imp (den_lt' (hP.cons _) den_var0) (den_NumOK hx den_var0)

/-- **The recognizer of instances.** -/
lemma den_valid : Den x Γ validT (bv (ValidI ts)) := by
  refine den_lett (den_tF hx) fun k1 => den_lett (den_sE hx den_var0) fun k2 => ?_
  exact den_and (den_form hx (den_var (by simp))) (den_path hx (den_var (by simp)) den_var0)

end

end FD

end PathChecking
