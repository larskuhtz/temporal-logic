module

public import RequestProject.MCVP.Construction
public import RequestProject.Logspace.Tok

/-!
# The monotone circuit value problem and the reduction map

* `MGate.toks`, `encodeCircuit`: the binary encoding of monotone circuits (gate indices in
  binary, the same 5-bit token encoding as everywhere else in the project);
* `MCVP`: the monotone circuit value problem, as a language;
* unique decodability of the encodings of numbers, circuits, CTL* formulas and trees;
* `redFun`: the reduction map on binary words, and its correctness
  `w ∈ MCVP ↔ redFun w ∈ CTLStarTreeChecking`.

## References

MCVP is P-complete under logspace reductions: L. M. Goldschlager, *The Monotone and Planar
Circuit Value Problems are Log Space Complete for P*, SIGACT News 9(2), 1977 [Gol77]. It is proved
for this encoding as `PHardness.MCVP_PHard`. Full entries are in `REFERENCES.md`.
-/

@[expose] public section

namespace PathChecking

namespace MCVPReduction

open LS

/-! ## Encoding of monotone circuits -/

/-- Token encoding of a gate: a tag, followed by the two argument indices in binary. -/
def MGate.toks : MGate → List Tok
  | .input false => [Tok.tag 0]
  | .input true => [Tok.tag 1]
  | .and i j => Tok.tag 2 :: (natToks i ++ natToks j)
  | .or i j => Tok.tag 3 :: (natToks i ++ natToks j)

/-- Binary encoding of a monotone circuit. -/
def encodeCircuit (C : List MGate) : Word := encodeToks (C.flatMap MGate.toks)

/-- **The monotone circuit value problem**: encodings of non-empty well-formed monotone
circuits (every gate reads only earlier gates) whose output gate (the last gate) evaluates
to true. -/
def MCVP : Language :=
  {x | ∃ C : List MGate, C ≠ [] ∧ WellFormed C ∧ x = encodeCircuit C ∧ eval C = true}

/-! ## Binary numbers -/

/-- Value of a little-endian list of bits. -/
def ofBits : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * ofBits bs

lemma ofBits_bits (n : ℕ) : ofBits (Nat.bits n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ofBits]
    · rw [Nat.bits_of_ne_zero' n (by omega), ofBits, ih (n / 2) (by omega)]
      by_cases h : n % 2 = 1 <;> simp [h] <;> omega

/-- Canonical bit lists: no trailing zero. -/
def Canon (bs : List Bool) : Prop := bs = [] ∨ bs.getLast? = some true

lemma ofBits_eq_zero_of_canon {bs : List Bool} (h : Canon bs) (h0 : ofBits bs = 0) : bs = [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    exfalso
    simp only [ofBits] at h0
    have hb : b = false := by cases b <;> simp_all
    have hbs : ofBits bs = 0 := by omega
    subst hb
    rcases h with h | h
    · simp at h
    · have hc : Canon bs := by
        rcases bs with _ | ⟨c, cs⟩
        · simp at h
        · right; simpa [List.getLast?_cons_cons] using h
      have := ih hc hbs
      subst this; simp at h

lemma bits_ofBits {bs : List Bool} (h : Canon bs) : Nat.bits (ofBits bs) = bs := by
  induction bs with
  | nil => simp [ofBits]
  | cons b bs ih =>
    have hc : Canon bs := by
      rcases h with h | h
      · simp at h
      · rcases bs with _ | ⟨c, cs⟩
        · left; rfl
        · right; simpa [List.getLast?_cons_cons] using h
    have e : ofBits (b :: bs) = Nat.bit b (ofBits bs) := by
      simp [ofBits, Nat.bit_val]; ring
    rw [e, Nat.bits_append_bit, ih hc]
    intro h0
    have := ofBits_eq_zero_of_canon hc h0
    subst this
    rcases h with h | h
    · simp at h
    · simpa using h

lemma canon_bits (n : ℕ) : Canon (Nat.bits n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · left; simp
    · right
      rw [Nat.bits_of_ne_zero' n (by omega)]
      rcases ih (n / 2) (by omega) with h | h
      · rw [h]
        have : n / 2 = 0 := by
          have := ofBits_bits (n / 2); rw [h] at this; simp [ofBits] at this; omega
        have : n = 1 := by omega
        subst this; simp
      · rw [List.getLast?_cons, h]; simp

lemma bits_injective {a b : ℕ} (h : Nat.bits a = Nat.bits b) : a = b := by
  rw [← ofBits_bits a, ← ofBits_bits b, h]

/-! ## Unique decodability -/

lemma Tok.bits_injective {t u : Tok} (h : t.bits = u.bits) : t = u := by
  have h1 := decodeTok_bits t
  rw [h, decodeTok_bits] at h1
  exact (Option.some_injective _ h1).symm

/-- Bit strings of tokens decompose uniquely. -/
lemma encodeToks_append_eq {ts us : List Tok} {x y : List Bool} (hl : ts.length ≤ us.length)
    (h : encodeToks ts ++ x = encodeToks us ++ y) :
    ∃ vs, us = ts ++ vs ∧ x = encodeToks vs ++ y := by
  induction ts generalizing us with
  | nil => exact ⟨us, rfl, by simpa [encodeToks] using h⟩
  | cons t ts ih =>
    obtain ⟨u, us, rfl⟩ : ∃ u us', us = u :: us' := by
      cases us with
      | nil => simp at hl
      | cons u us => exact ⟨u, us, rfl⟩
    simp only [encodeToks_cons, List.append_assoc] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp [Tok.bits_length])
    obtain rfl := Tok.bits_injective h1
    obtain ⟨vs, rfl, rfl⟩ := ih (by simpa using hl) h2
    exact ⟨vs, rfl, rfl⟩

lemma encodeToks_injective {ts us : List Tok} (h : encodeToks ts = encodeToks us) : ts = us := by
  rcases le_total ts.length us.length with hl | hl
  · obtain ⟨vs, rfl, h2⟩ := encodeToks_append_eq (x := []) (y := []) hl (by simpa using h)
    have : (encodeToks vs).length = 0 := by
      have := congrArg List.length h2; simpa using this.symm
    rw [encodeToks_length] at this
    simp at this; subst this; simp
  · obtain ⟨vs, rfl, h2⟩ := encodeToks_append_eq (x := []) (y := []) hl (by simpa using h.symm)
    have : (encodeToks vs).length = 0 := by
      have := congrArg List.length h2; simpa using this.symm
    rw [encodeToks_length] at this
    simp at this; subst this; simp

lemma digits_sep_eq {ds es : List Bool} {l l' : List Tok}
    (h : ds.map digitTok ++ Tok.sep :: l = es.map digitTok ++ Tok.sep :: l') :
    ds = es ∧ l = l' := by
  induction ds generalizing es with
  | nil =>
    cases es with
    | nil => simpa using h
    | cons e es => cases e <;> simp [digitTok] at h
  | cons d ds ih =>
    cases es with
    | nil => cases d <;> simp [digitTok] at h
    | cons e es =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      have hde : d = e := by cases d <;> cases e <;> simp_all [digitTok]
      subst hde
      obtain ⟨h1, h2⟩ := ih h.2
      exact ⟨by rw [h1], h2⟩

lemma natToks_append_eq {a b : ℕ} {l l' : List Tok} (h : natToks a ++ l = natToks b ++ l') :
    a = b ∧ l = l' := by
  simp only [natToks_eq, List.append_assoc, List.singleton_append] at h
  obtain ⟨h1, h2⟩ := digits_sep_eq h
  exact ⟨bits_injective h1, h2⟩

lemma natToks_head (n : ℕ) : ∃ l, natToks n = Tok.sep :: l ∨ natToks n = Tok.zero :: l ∨
    natToks n = Tok.one :: l := by
  rw [natToks_eq]
  cases h : Nat.bits n with
  | nil => exact ⟨[], Or.inl rfl⟩
  | cons b bs => cases b <;> simp [digitTok]

lemma MGate.toks_append_eq {G H : MGate} {l l' : List Tok} (h : G.toks ++ l = H.toks ++ l') :
    G = H ∧ l = l' := by
  cases G with
  | input b =>
    cases b <;> cases H with
    | input c => cases c <;> simp_all [MGate.toks]
    | and i j => simp [MGate.toks] at h
    | or i j => simp [MGate.toks] at h
  | and i j =>
    cases H with
    | input c => cases c <;> simp [MGate.toks] at h
    | and i' j' =>
      simp only [MGate.toks, List.cons_append, List.cons.injEq, true_and,
        List.append_assoc] at h
      obtain ⟨e1, h2⟩ := natToks_append_eq h
      obtain ⟨e2, e3⟩ := natToks_append_eq h2
      exact ⟨by rw [e1, e2], e3⟩
    | or i' j' => simp [MGate.toks] at h
  | or i j =>
    cases H with
    | input c => cases c <;> simp [MGate.toks] at h
    | and i' j' => simp [MGate.toks] at h
    | or i' j' =>
      simp only [MGate.toks, List.cons_append, List.cons.injEq, true_and,
        List.append_assoc] at h
      obtain ⟨e1, h2⟩ := natToks_append_eq h
      obtain ⟨e2, e3⟩ := natToks_append_eq h2
      exact ⟨by rw [e1, e2], e3⟩

lemma MGate.toks_ne_nil (G : MGate) : G.toks ≠ [] := by
  cases G with
  | input b => cases b <;> simp [MGate.toks]
  | _ => simp [MGate.toks]

/-- If the token encoding of `C'` is a prefix of that of `C`, then `C'` is a prefix of `C`. -/
lemma circuit_prefix {C C' : List MGate} {l : List Tok}
    (h : C'.flatMap MGate.toks ++ l = C.flatMap MGate.toks) : ∃ D, C = C' ++ D := by
  induction C' generalizing C with
  | nil => exact ⟨C, rfl⟩
  | cons G C' ih =>
    cases C with
    | nil =>
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_assoc,
        List.append_eq_nil_iff] at h
      exact absurd h.1 (MGate.toks_ne_nil G)
    | cons H C =>
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨rfl, h2⟩ := MGate.toks_append_eq h
      obtain ⟨D, rfl⟩ := ih h2
      exact ⟨D, rfl⟩

lemma encodeCircuit_injective {C C' : List MGate} (h : encodeCircuit C = encodeCircuit C') :
    C = C' := by
  have h' := encodeToks_injective h
  obtain ⟨D, hD⟩ := circuit_prefix (l := []) (by simpa using h'.symm)
  obtain ⟨D', hD'⟩ := circuit_prefix (l := []) (by simpa using h')
  have : C.length = C'.length := by
    have := congrArg List.length hD; have := congrArg List.length hD'; simp at *; omega
  subst hD
  simp at this; subst this; simp

lemma CTLStar.toks_append_eq {φ ψ : CTLStar} {l l' : List Tok}
    (h : φ.toks ++ l = ψ.toks ++ l') : φ = ψ ∧ l = l' := by
  induction φ generalizing ψ l l' with
  | ap a =>
    cases ψ <;> simp [CTLStar.toks] at h
    obtain ⟨rfl, rfl⟩ := natToks_append_eq h
    exact ⟨rfl, rfl⟩
  | tt => cases ψ <;> simp_all [CTLStar.toks]
  | neg φ ih =>
    cases ψ <;> simp [CTLStar.toks] at h
    obtain ⟨rfl, rfl⟩ := ih h
    exact ⟨rfl, rfl⟩
  | and φ₁ φ₂ ih₁ ih₂ =>
    cases ψ <;> simp [CTLStar.toks] at h
    obtain ⟨e1, h2⟩ := ih₁ h
    obtain ⟨e2, e3⟩ := ih₂ h2
    exact ⟨by rw [e1, e2], e3⟩
  | X φ ih =>
    cases ψ <;> simp [CTLStar.toks] at h
    obtain ⟨rfl, rfl⟩ := ih h
    exact ⟨rfl, rfl⟩
  | U φ₁ φ₂ ih₁ ih₂ =>
    cases ψ <;> simp [CTLStar.toks] at h
    obtain ⟨e1, h2⟩ := ih₁ h
    obtain ⟨e2, e3⟩ := ih₂ h2
    exact ⟨by rw [e1, e2], e3⟩
  | E φ ih =>
    cases ψ <;> simp [CTLStar.toks] at h
    obtain ⟨rfl, rfl⟩ := ih h
    exact ⟨rfl, rfl⟩

lemma nats_rpar_eq {xs ys : List ℕ} {l l' : List Tok}
    (h : xs.flatMap natToks ++ Tok.rpar :: l = ys.flatMap natToks ++ Tok.rpar :: l') :
    xs = ys ∧ l = l' := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simpa using h
    | cons y ys =>
      obtain ⟨m, hm | hm | hm⟩ := natToks_head y <;> simp [hm] at h
  | cons x xs ih =>
    cases ys with
    | nil =>
      obtain ⟨m, hm | hm | hm⟩ := natToks_head x <;> simp [hm] at h
    | cons y ys =>
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨e1, h2⟩ := natToks_append_eq h
      obtain ⟨e2, e3⟩ := ih h2
      exact ⟨by rw [e1, e2], e3⟩

lemma finsetToks_append_eq {s s' : Finset ℕ} {l l' : List Tok}
    (h : finsetToks s ++ l = finsetToks s' ++ l') : s = s' ∧ l = l' := by
  simp only [finsetToks, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
  obtain ⟨h1, h2⟩ := nats_rpar_eq h
  refine ⟨?_, h2⟩
  rw [← Finset.sort_toFinset s (· ≤ ·), h1, Finset.sort_toFinset]

lemma LTree.toks_head (t : LTree) : ∃ l, t.toks = Tok.lpar :: l := by
  cases t with
  | node a cs => exact ⟨_, by rw [LTree.toks]⟩

lemma LTree.toks_length_lt (l : Finset ℕ) (cs : List LTree) :
    (LTree.toksList cs).length < (LTree.node l cs).toks.length := by
  simp [LTree.toks]; omega

lemma LTree.toks_length_pos (t : LTree) : 0 < t.toks.length := by
  obtain ⟨l, hl⟩ := LTree.toks_head t; simp [hl]

lemma LTree.toksList_cons (t : LTree) (ts : List LTree) :
    LTree.toksList (t :: ts) = t.toks ++ LTree.toksList ts := by
  simp [LTree.toksList]

lemma ltree_unique_aux (n : ℕ) :
    (∀ t u : LTree, ∀ l l' : List Tok, t.toks.length ≤ n → t.toks ++ l = u.toks ++ l' →
      t = u ∧ l = l') ∧
    (∀ cs ds : List LTree, ∀ l l' : List Tok, (LTree.toksList cs).length ≤ n →
      LTree.toksList cs ++ Tok.rpar :: l = LTree.toksList ds ++ Tok.rpar :: l' →
        cs = ds ∧ l = l') := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hlist : ∀ m < n, ∀ cs ds : List LTree, ∀ l l' : List Tok,
        (LTree.toksList cs).length ≤ m →
        LTree.toksList cs ++ Tok.rpar :: l = LTree.toksList ds ++ Tok.rpar :: l' →
          cs = ds ∧ l = l' := fun m hm => (ih m hm).2
    have htree : ∀ t u : LTree, ∀ l l' : List Tok, t.toks.length ≤ n →
        t.toks ++ l = u.toks ++ l' → t = u ∧ l = l' := by
      intro t u l l' ht h
      obtain ⟨a, cs⟩ := t
      obtain ⟨b, ds⟩ := u
      simp only [LTree.toks, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨rfl, h2⟩ := finsetToks_append_eq h
      have hlt := LTree.toks_length_lt a cs
      obtain ⟨rfl, rfl⟩ := hlist _ (by omega) cs ds l l' le_rfl (by simpa using h2)
      exact ⟨rfl, rfl⟩
    refine ⟨htree, ?_⟩
    intro cs ds l l' hcs h
    cases cs with
    | nil =>
      cases ds with
      | nil => simpa [LTree.toksList] using h
      | cons d ds =>
        obtain ⟨m, hm⟩ := LTree.toks_head d
        simp [LTree.toksList, hm] at h
    | cons c cs =>
      cases ds with
      | nil =>
        obtain ⟨m, hm⟩ := LTree.toks_head c
        simp [LTree.toksList, hm] at h
      | cons d ds =>
        simp only [LTree.toksList_cons, List.append_assoc] at h hcs
        rw [List.length_append] at hcs
        obtain ⟨rfl, h2⟩ := htree c d _ _ (by omega) h
        have := LTree.toks_length_pos c
        obtain ⟨rfl, rfl⟩ := hlist _ (by omega) cs ds l l' le_rfl h2
        exact ⟨rfl, rfl⟩

lemma LTree.toks_append_eq {t u : LTree} {l l' : List Tok} (h : t.toks ++ l = u.toks ++ l') :
    t = u ∧ l = l' :=
  (ltree_unique_aux (LTree.toks t).length).1 t u l l' le_rfl h

/-- Unique decodability of the instances of CTL* tree checking. -/
lemma instance_injective {φ ψ : CTLStar} {t u : LTree}
    (h : encodeToks (Tok.lpar :: (φ.toks ++ (Tok.rpar :: t.toks))) =
      encodeToks (Tok.lpar :: (ψ.toks ++ (Tok.rpar :: u.toks)))) : φ = ψ ∧ t = u := by
  have h' := encodeToks_injective h
  simp only [List.cons.injEq, true_and] at h'
  obtain ⟨rfl, h''⟩ := CTLStar.toks_append_eq h'
  simp only [List.cons.injEq, true_and] at h''
  exact ⟨rfl, (LTree.toks_append_eq (l := []) (l' := []) (by simpa using h'')).1⟩

/-! ## The reduction map -/

/-- The instance of CTL* tree checking produced from a circuit. -/
def instanceWord (C : List MGate) : Word :=
  encodeToks (Tok.lpar :: ((reductionFormula C).toks ++ (Tok.rpar :: (reductionTree C).toks)))

/-- Valid encodings of circuits. -/
def ValidCode (w : Word) : Prop := ∃ C : List MGate, C ≠ [] ∧ WellFormed C ∧ w = encodeCircuit C

open Classical in
/-- **The reduction map** on binary words: valid encodings of circuits are mapped to the
encoding of the CTL* instance of `reductionFormula_correct`; all other words are mapped to
the empty word (which is not an instance). -/
noncomputable def redFun (w : Word) : Word :=
  if h : ValidCode w then instanceWord h.choose else []

lemma redFun_encode {C : List MGate} (hC : C ≠ []) (hwf : WellFormed C) :
    redFun (encodeCircuit C) = instanceWord C := by
  have hv : ValidCode (encodeCircuit C) := ⟨C, hC, hwf, rfl⟩
  rw [redFun, dif_pos hv]
  have := hv.choose_spec.2.2
  rw [encodeCircuit_injective this.symm]

lemma redFun_invalid {w : Word} (h : ¬ ValidCode w) : redFun w = [] := by
  rw [redFun, dif_neg h]

/-- **Correctness of the reduction map.** -/
theorem redFun_correct (w : Word) : w ∈ MCVP ↔ redFun w ∈ CTLStarTreeChecking := by
  constructor
  · rintro ⟨C, hC, hwf, rfl, hev⟩
    rw [redFun_encode hC hwf]
    exact ⟨_, _, rfl, (reductionFormula_correct C hwf).2 hev⟩
  · rintro ⟨φ, t, hx, hsat⟩
    by_cases hv : ValidCode w
    · obtain ⟨C, hC, hwf, rfl⟩ := hv
      rw [redFun_encode hC hwf, instanceWord] at hx
      obtain ⟨rfl, rfl⟩ := instance_injective hx
      exact ⟨C, hC, hwf, rfl, (reductionFormula_correct C hwf).1 hsat⟩
    · rw [redFun_invalid hv] at hx
      simp [encodeToks, Tok.bits] at hx

end MCVPReduction

end PathChecking
