module

public import RequestProject.LTLPath.FDQ
public import RequestProject.LTLPath.FDValid
public import RequestProject.Shallow.Prog.DDec

/-!
# The decision function

`dProg` is the output program of the decision function: it checks that the input word is the
encoding of a token list (`wdecT`), that the token list is the encoding of an instance (`validT`),
and that both answers for the root gate `(1, 0, main)` are `true`.  `dFun_spec` proves the
specification `DSpec`, and `dFun_logspace` that the decision function is logspace computable.
-/

@[expose] public section

namespace PathChecking

namespace FD

open FE LL CTLP LTok MCVPReduction Classical

variable {x : Word} {Γ : Ctx} {w : Word} {ts : List Tok} {q : ℕ} {a : List Bool}

/-! ## Decoding the input into tokens -/

/-- The word `w` consists of blocks of `5` bits with values `< 29`. -/
def DecW (w : Word) : Prop := w.length % 5 = 0 ∧ ∀ p < w.length / 5, wcode w p < 29

lemma five_bits : ∀ b0 b1 b2 b3 b4 : Bool,
    ((((2 ^ 0 * (if b0 = true then 1 else 0)) + 2 ^ 1 * (if b1 = true then 1 else 0)) +
      2 ^ 2 * (if b2 = true then 1 else 0)) + 2 ^ 3 * (if b3 = true then 1 else 0)) +
      2 ^ 4 * (if b4 = true then 1 else 0) =
    b0.toNat + (2 * b1.toNat + (4 * b2.toNat + (8 * b3.toNat + 16 * b4.toNat))) := by
  decide

lemma chunk_eq_wcode (w : Word) (p : ℕ) (h : 5 * p + 5 ≤ w.length) : SQ.chunk w p = wcode w p := by
  unfold SQ.chunk wcode code5
  rw [if_pos h]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
  exact five_bits _ _ _ _ _

lemma decode_of_DecW (h : DecW w) : ∃ ts : List Tok, w = encodeToks ts := by
  rcases Nat.eq_zero_or_pos w.length with h0 | h0
  · exact ⟨[], List.eq_nil_of_length_eq_zero h0⟩
  · have h5 := h.1
    obtain ⟨ts, hts, -⟩ := SQ.decode_of_decOK ⟨h.1, by omega, fun p hp => by
      rw [chunk_eq_wcode w p (by omega)]; exact h.2 p hp⟩
    exact ⟨ts, hts⟩

lemma DecW_encode (ts : List Tok) : DecW (encodeToks ts) := by
  refine ⟨by rw [SQ.encodeToks_length]; omega, fun p hp => ?_⟩
  rw [SQ.encodeToks_length] at hp
  rw [wcode_encodeToks]
  exact tc_lt_29 (by omega)

/-! ## Terms -/

/-- Decoding test. -/
def wdecT : T := andT (eqT (modT nwT (cT 5)) (cT 0))
  (allT (divT nwT (cT 5)) fun p => ltT (wcodeT p) (cT 29))

/-- The index of the root gate `(1, 0, main)`. -/
def idxV (ts : List Tok) : ℕ :=
  2 * ((ts.length - 1 - 1) * (sLen ts + (ts.length + 1) * lLen ts) +
    ((sLen ts + (ts.length + 1) * lLen ts) - 1 - 0)) + 1

/-- Term for the index of the root gate. -/
def idxDT (F sE N : T) : T :=
  lettT (sLenT F sE) fun s => lettT (lLenT sE N) fun l =>
    lettT (addT s (mulT (addT N (cT 1)) l)) fun W =>
      addT (mulT (cT 2) (addT (mulT (subT (subT N (cT 1)) (cT 1)) W) (subT (subT W (cT 1)) (cT 0))))
        (cT 1)

/-- The decision on decoded inputs. -/
def innT : T :=
  lettT tFT fun F => lettT (sET F) fun sE => lettT nT fun N => lettT (idxDT F sE N) fun I =>
    lettT (mulT (cT 5) (addT nwT (cT 1))) fun K =>
      andT (andT (formT F) (pathT F sE))
        (andT (ansT (addT K (mulT (cT 2) I))) (ansT (addT (addT K (mulT (cT 2) I)) (cT 1))))

/-- The decision program. -/
def dProg : TO := bitO (iteT wdecT innT (cT 0))

/-! ## Denotations -/

lemma den_wdec (hx : x = pack w q a) : Den x Γ wdecT (bv (DecW w)) :=
  den_and (den_eq' (den_mod (den_nw hx) (den_c 5)) (den_c 0))
    (den_all (den_div (den_nw hx) (den_c 5)) fun _ _ _ => den_lt' (den_wcode hx den_var0) (den_c 29))

/-- The condition decided on encodings of token lists. -/
def InnP (ts : List Tok) (a : List Bool) : Prop :=
  ValidI ts ∧ a.getD (5 * ((encodeToks ts).length + 1) + 2 * idxV ts) false = true ∧
    a.getD (5 * ((encodeToks ts).length + 1) + 2 * idxV ts + 1) false = true

lemma den_inn (hx : x = pack (encodeToks ts) 0 a) : Den x Γ innT (bv (InnP ts a)) := by
  refine den_lett (den_tF hx) fun k1 => den_lett (den_sE hx den_var0) fun k2 => ?_
  set Γ2 := (k2, LTok.sE ts) :: (k1, tF ts) :: Γ
  have hF : Den x Γ2 (varT k1) (tF ts) := den_var (by simp [Γ2])
  have hs : Den x Γ2 (varT k2) (LTok.sE ts) := den_var0
  refine den_lett (den_n hx) fun k3 => ?_
  have hN : Den x ((k3, ts.length) :: Γ2) (varT k3) ts.length := den_var0
  have hidx : Den x ((k3, ts.length) :: Γ2) (idxDT (varT k1) (varT k2) (varT k3)) (idxV ts) := by
    refine den_lett (den_sLen hx (hF.cons _) (hs.cons _)) fun k4 => den_lett
      (den_lLen hx ((hs.cons _).cons _) (hN.cons _)) fun k5 => ?_
    refine den_lett (den_add (den_var (k := k4) (v := sLen ts) (by simp)) (den_mul (den_add (den_var (k := k3) (v := ts.length)
      (by simp)) (den_c 1)) den_var0)) fun k6 => ?_
    exact den_add (den_mul (den_c 2) (den_add (den_mul (den_sub (den_sub (den_var (by simp))
      (den_c 1)) (den_c 1)) den_var0) (den_sub (den_sub den_var0 (den_c 1)) (den_c 0)))) (den_c 1)
  refine den_lett hidx fun k4 => den_lett (den_mul (den_c 5) (den_add (den_nw hx) (den_c 1)))
    fun k5 => ?_
  set Γ5 := (k5, 5 * ((encodeToks ts).length + 1)) :: (k4, idxV ts) :: (k3, ts.length) :: Γ2
  have s5 : Γ2 ⊆ Γ5 := fun y hy => by simp [Γ5, hy]
  have hK : Den x Γ5 (varT k5) (5 * ((encodeToks ts).length + 1)) := den_var0
  have hI : Den x Γ5 (varT k4) (idxV ts) := den_var (by simp [Γ5])
  have hv : Den x Γ5 (andT (formT (varT k1)) (pathT (varT k1) (varT k2))) (bv (ValidI ts)) :=
    den_and (den_form hx (hF.mono s5)) (den_path hx (hF.mono s5) (hs.mono s5))
  exact den_and hv (den_and ((den_ans hx (Nat.zero_le _) (den_add hK (den_mul (den_c 2) hI))).of_eq
    (bv_bool _)) ((den_ans hx (Nat.zero_le _) (den_add (den_add hK (den_mul (den_c 2) hI))
      (den_c 1))).of_eq (bv_bool _)))

/-- The value of the decision program. -/
def DVal (w : Word) (a : List Bool) : Prop := ∃ ts : List Tok, w = encodeToks ts ∧ InnP ts a

lemma deno_dProg (hx : x = pack w 0 a) : DenO x [] dProg [decide (bv (DVal w a) ≠ 0)] := by
  refine deno_bit (den_ite_eq (den_wdec hx) (fun h => ?_) (fun h => ?_))
  · simp only [ne_eq, bv_eq_zero, not_not] at h
    obtain ⟨ts, rfl⟩ := decode_of_DecW h
    refine (den_inn hx).of_eq (bv_congr ⟨fun hi => ⟨ts, rfl, hi⟩, ?_⟩)
    rintro ⟨us, hus, hi⟩
    rwa [encodeToks_injective hus]
  · simp only [bv_eq_zero] at h
    refine (den_c 0).of_eq (bv_neg ?_).symm
    rintro ⟨ts, rfl, -⟩
    exact h (DecW_encode ts)

end FD

open FD

/-- The decision function. -/
def dFun (x : Word) : Word := FE.evO x 0 (fun _ => 0) (dProg 0)

/-- The decision function is logspace computable. -/
theorem dFun_logspace : LogspaceComputable dFun :=
  FE.logspaceComputable_of_O (dProg 0) (by decide +kernel) dFun fun _ => rfl

/-- **The decision function meets its specification.** -/
theorem dFun_spec : DSpec dFun := by
  intro w a
  have key : dFun (pack w 0 a) = [decide (bv (DVal w a) ≠ 0)] :=
    deno_dProg rfl 0 _ (fun _ h => absurd h (by simp))
  rw [key]
  simp only [List.cons.injEq, and_true, decide_eq_true_eq, ne_eq, bv_eq_zero, not_not]
  constructor
  · rintro ⟨ts, rfl, hv, h1, h2⟩
    obtain ⟨φ, p, hE⟩ := LTok.validI_iff.1 hv
    have hts : ts = instToks φ p := hE
    subst hts
    exact ⟨φ, p, rfl, h1, h2⟩
  · rintro ⟨φ, p, rfl, h1, h2⟩
    exact ⟨instToks φ p, rfl, LTok.validI_iff.2 ⟨φ, p, instToks_enc φ p⟩, h1, h2⟩

end PathChecking
