module

public import RequestProject.BLMS.LFw
public import RequestProject.BLMS.Concrete

/-!
# The token structure of circuit encodings

Pure facts about the token list `gts C` of a circuit: where the gates start (`offs`), how to
find the start of a gate by counting tags (`gs_fold`), and how to read a binary number backwards
(`readNum_ok`).
-/

@[expose] public section

namespace PathChecking

namespace BLMS

namespace LP

/-- The token list of a circuit. -/
def gts (C : Circuit) : List Tok := C.flatMap Gate.toks

/-- Start of gate `i` in the token list. -/
def offs (C : Circuit) (i : ℕ) : ℕ := ((C.take i).flatMap Gate.toks).length

/-- Token code at a position (`0` outside). -/
def tc (C : Circuit) (p : ℕ) : ℕ := (((gts C)[p]?).map Tok.code).getD 0

/-- Tag tokens. -/
def isTag (t : Tok) : Bool := decide (5 ≤ t.code)

lemma natToks_noTag (a : ℕ) : ∀ t ∈ natToks a, isTag t = false := by
  intro t ht
  simp only [natToks, List.mem_append, List.mem_map, List.mem_singleton] at ht
  rcases ht with ⟨b, -, rfl⟩ | rfl
  · cases b <;> rfl
  · rfl

lemma toks_eq (g : Gate) : ∃ t, g.toks = Tok.tag t :: g.toks.tail ∧
    ∀ t' ∈ g.toks.tail, isTag t' = false := by
  have hargs : ∀ t' ∈ Tok.lpar :: (g.args.flatMap natToks ++ [Tok.rpar]), isTag t' = false := by
    intro t' ht
    simp only [List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_singleton] at ht
    rcases ht with rfl | ⟨a, -, ht⟩ | ht
    · rfl
    · exact natToks_noTag a t' ht
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht; subst ht; rfl
  unfold Gate.toks
  rcases hk : g.kind with k | b | _ | _ | _ | _
  · refine ⟨0, rfl, ?_⟩
    intro t' ht
    simp only [List.cons_append, List.tail_cons, List.mem_append] at ht
    rcases ht with ht | ht
    · exact natToks_noTag k t' ht
    · exact hargs t' ht
  · cases b
    · exact ⟨1, rfl, hargs⟩
    · exact ⟨2, rfl, hargs⟩
  · exact ⟨3, rfl, hargs⟩
  · exact ⟨4, rfl, hargs⟩
  · exact ⟨5, rfl, hargs⟩
  · exact ⟨6, rfl, hargs⟩

lemma toks_countP (g : Gate) : g.toks.countP isTag = 1 := by
  obtain ⟨t, h1, h2⟩ := toks_eq g
  rw [h1, List.countP_cons, List.countP_eq_zero.2 (fun a ha => by simp [h2 a ha])]
  simp [isTag, Tok.code]

lemma toks_pos (g : Gate) : 0 < g.toks.length := by
  obtain ⟨t, h1, -⟩ := toks_eq g
  rw [h1]; simp

variable {C : Circuit}

lemma offs_succ {i : ℕ} (hi : i < C.length) : offs C (i + 1) = offs C i + C[i].toks.length := by
  rw [offs, offs, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    List.flatMap_append, List.length_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

lemma offs_mono {i j : ℕ} (h : i ≤ j) : offs C i ≤ offs C j := by
  unfold offs
  have : C.take j = C.take i ++ (C.take j).drop i := by
    conv_lhs => rw [← List.take_append_drop i (C.take j)]
    rw [List.take_take, min_eq_left h]
  rw [this, List.flatMap_append, List.length_append]
  omega

lemma gts_length : (gts C).length = offs C C.length := by
  simp [gts, offs]

lemma gts_getElem? {i : ℕ} (hi : i < C.length) (k : ℕ) (hk : k < C[i].toks.length) :
    (gts C)[offs C i + k]? = C[i].toks[k]? := by
  have e : gts C = (C.take i).flatMap Gate.toks ++
      (C[i].toks ++ (C.drop (i + 1)).flatMap Gate.toks) := by
    unfold gts
    conv_lhs => rw [← List.take_append_drop i C, List.drop_eq_getElem_cons hi]
    rw [List.flatMap_append, List.flatMap_cons]
  rw [e, List.getElem?_append_right (by unfold offs; omega),
    show offs C i + k - ((C.take i).flatMap Gate.toks).length = k by unfold offs; omega,
    List.getElem?_append_left hk]

lemma decomp {p : ℕ} (hp : p < (gts C).length) :
    ∃ i < C.length, offs C i ≤ p ∧ p < offs C (i + 1) := by
  have key : ∀ i ≤ C.length, p < offs C i → ∃ j < i, offs C j ≤ p ∧ p < offs C (j + 1) := by
    intro i
    induction i with
    | zero => intro _ h; simp [offs] at h
    | succ i ih =>
      intro hi h
      by_cases h' : p < offs C i
      · obtain ⟨j, hj, h1⟩ := ih (by omega) h'
        exact ⟨j, by omega, h1⟩
      · exact ⟨i, by omega, by omega, h⟩
  obtain ⟨j, hj, h⟩ := key C.length le_rfl (by rw [← gts_length]; exact hp)
  exact ⟨j, hj, h⟩

lemma gts_getElem_offs {p : ℕ} (hp : p < (gts C).length) :
    ∃ i, ∃ hi : i < C.length, ∃ k < (C[i]'hi).toks.length, p = offs C i + k ∧
      (gts C)[p]? = (C[i]'hi).toks[k]? := by
  obtain ⟨i, hi, h1, h2⟩ := decomp hp
  rw [offs_succ hi] at h2
  refine ⟨i, hi, p - offs C i, by omega, by omega, ?_⟩
  rw [← gts_getElem? hi _ (by omega)]
  congr 1; omega

lemma isTag_iff {p : ℕ} (hp : p < (gts C).length) :
    isTag ((gts C)[p]) = true ↔ ∃ i < C.length, p = offs C i := by
  obtain ⟨i, hi, k, hk, rfl, he⟩ := gts_getElem_offs hp
  obtain ⟨t, h1, h2⟩ := toks_eq C[i]
  have e : (gts C)[offs C i + k] = C[i].toks[k] := by
    have := he; rw [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hk] at this
    exact Option.some.inj this
  rw [e]
  constructor
  · intro ht
    refine ⟨i, hi, ?_⟩
    rcases k with _ | k
    · rfl
    · exfalso
      have hlt : k < C[i].toks.tail.length := by rw [List.length_tail]; omega
      have hm : C[i].toks.tail[k] ∈ C[i].toks.tail := List.getElem_mem hlt
      rw [List.getElem_tail] at hm
      rw [h2 _ hm] at ht; cases ht
  · rintro ⟨j, hj, hjk⟩
    have hij : i = j := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := offs_mono (C := C) (show i + 1 ≤ j by omega)
        rw [offs_succ hi] at this; omega
      · have := offs_mono (C := C) (show j + 1 ≤ i by omega)
        rw [offs_succ hj] at this
        have := toks_pos C[j]; omega
    subst hij
    have hk0 : k = 0 := by omega
    subst hk0
    have h0 : C[i].toks[0]? = some (Tok.tag t) := by rw [h1]; rfl
    rw [List.getElem?_eq_getElem hk] at h0
    rw [Option.some.inj h0]; simp [isTag, Tok.code]

/-- Number of tags. -/
def tagCount (l : List Tok) : ℕ := l.countP isTag

lemma take_offs {i : ℕ} : (gts C).take (offs C i) = (C.take i).flatMap Gate.toks := by
  have e : gts C = (C.take i).flatMap Gate.toks ++ (C.drop i).flatMap Gate.toks := by
    unfold gts
    conv_lhs => rw [← List.take_append_drop i C]
    rw [List.flatMap_append]
  rw [e, offs, List.take_left]

lemma tagCount_offs {i : ℕ} (hi : i ≤ C.length) : tagCount ((gts C).take (offs C i)) = i := by
  rw [take_offs, tagCount, List.countP_flatMap]
  have : (C.take i).map (List.countP isTag ∘ Gate.toks) = (C.take i).map (fun _ => 1) :=
    List.map_congr_left (fun g _ => toks_countP g)
  rw [this]
  simp; omega

lemma tc_eq {p : ℕ} (hp : p < (gts C).length) : tc C p = ((gts C)[p]).code := by
  simp [tc, List.getElem?_eq_getElem hp]

/-- One step of the scan for the start of gate `i`. -/
def gsF (C : Circuit) (i : ℕ) (a : ℕ × ℕ) (p : ℕ) : ℕ × ℕ :=
  if 5 ≤ tc C p then (if a.2 = i then p else a.1, a.2 + 1) else a

lemma gs_fold_aux (i : ℕ) : ∀ q ≤ (gts C).length,
    (List.range q).foldl (gsF C i) (0, 0) =
      (if offs C i < q then offs C i else 0, tagCount ((gts C).take q)) := by
  intro q
  induction q with
  | zero => intro _; simp [tagCount]
  | succ q ih =>
    intro hq
    rw [LL.foldl_range_succ, ih (by omega)]
    have hq' : q < (gts C).length := by omega
    have htake : (gts C).take (q + 1) = (gts C).take q ++ [(gts C)[q]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hq']; rfl
    simp only [gsF]
    rw [tc_eq hq', htake]
    simp only [tagCount]
    rw [List.countP_append]
    by_cases ht : isTag ((gts C)[q]) = true
    · have h5 : 5 ≤ ((gts C)[q]).code := by simpa [isTag] using ht
      obtain ⟨j, hj, hqj⟩ := (isTag_iff hq').1 ht
      have hc : tagCount ((gts C).take q) = j := by rw [hqj]; exact tagCount_offs hj.le
      rw [if_pos h5]
      simp only [List.countP_singleton, ht, if_true]
      refine Prod.ext ?_ rfl
      simp only [tagCount] at hc
      simp only [hc]
      by_cases hji : j = i
      · subst hji; simp [hqj]
      · rw [if_neg hji]
        have hne : offs C i ≠ q := by
          intro h
          have := (isTag_iff hq').1 ht
          rw [← h] at hqj
          rcases Nat.lt_or_gt_of_ne hji with hlt | hlt
          · have := offs_mono (C := C) (show j + 1 ≤ i by omega)
            rw [offs_succ hj] at this; have := toks_pos C[j]; omega
          · by_cases hi : i < C.length
            · have := offs_mono (C := C) (show i + 1 ≤ j by omega)
              rw [offs_succ hi] at this; have := toks_pos C[i]; omega
            · have := offs_mono (C := C) (show C.length ≤ i by omega)
              have := offs_mono (C := C) (show j + 1 ≤ C.length by omega)
              rw [offs_succ hj] at this; have := toks_pos C[j]; omega
        by_cases h1 : offs C i < q
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    · have h5 : ¬ 5 ≤ ((gts C)[q]).code := by simpa [isTag] using ht
      rw [if_neg h5]
      simp only [List.countP_singleton, Bool.not_eq_true] at ht ⊢
      simp only [ht]
      refine Prod.ext ?_ (by simp)
      have hne : offs C i ≠ q := by
        intro h
        by_cases hi : i < C.length
        · have := (isTag_iff hq').2 ⟨i, hi, h.symm⟩
          rw [ht] at this; cases this
        · have := offs_mono (C := C) (show C.length ≤ i by omega)
          rw [← gts_length] at this; omega
      by_cases h1 : offs C i < q
      · simp only [if_pos h1, if_pos (show offs C i < q + 1 by omega)]
      · simp only [if_neg h1, if_neg (show ¬ offs C i < q + 1 by omega)]

lemma gs_fold {i : ℕ} (hi : i < C.length) :
    (List.range (gts C).length).foldl (gsF C i) (0, 0) = (offs C i, C.length) := by
  rw [gs_fold_aux i _ le_rfl]
  have h1 : offs C i < (gts C).length := by
    rw [gts_length]
    have := offs_mono (C := C) (show i + 1 ≤ C.length by omega)
    rw [offs_succ hi] at this; have := toks_pos C[i]; omega
  rw [if_pos h1]
  congr 1
  have := tagCount_offs (C := C) le_rfl
  rw [List.take_length]
  rwa [← gts_length, List.take_length] at this

/-! ## Reading binary numbers -/

/-- `gts C` contains the list `l` at position `q`. -/
def At (C : Circuit) (q : ℕ) (l : List Tok) : Prop := ∀ j < l.length, (gts C)[q + j]? = l[j]?

lemma At_append {q : ℕ} {l₁ l₂ : List Tok} :
    At C q (l₁ ++ l₂) ↔ At C q l₁ ∧ At C (q + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [h j (by simp; omega), List.getElem?_append_left hj]
    · rw [show q + l₁.length + j = q + (l₁.length + j) by omega, h _ (by simp; omega),
        List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  · rintro ⟨h1, h2⟩ j hj
    by_cases hj1 : j < l₁.length
    · rw [h1 j hj1, List.getElem?_append_left hj1]
    · rw [List.getElem?_append_right (by omega), ← h2 (j - l₁.length) (by simp at hj; omega)]
      congr 1; omega

lemma At_cons {q : ℕ} {t : Tok} {l : List Tok} :
    At C q (t :: l) ↔ (gts C)[q]? = some t ∧ At C (q + 1) l := by
  have := At_append (C := C) (q := q) (l₁ := [t]) (l₂ := l)
  simp only [List.singleton_append, List.length_singleton] at this
  rw [this]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by simpa using h1 0 (by simp), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun j hj => by simp at hj; subst hj; simpa using h1, h2⟩

lemma At_gate {i : ℕ} (hi : i < C.length) : At C (offs C i) C[i].toks :=
  fun j hj => gts_getElem? hi j hj

lemma tc_of_At {q : ℕ} {l : List Tok} (h : At C q l) {j : ℕ} (hj : j < l.length) :
    tc C (q + j) = (l[j]).code := by
  have := h j hj
  rw [List.getElem?_eq_getElem hj] at this
  simp [tc, this]

lemma lt_of_At {q : ℕ} {l : List Tok} (h : At C q l) {j : ℕ} (hj : j < l.length) :
    q + j < (gts C).length := by
  have := h j hj
  rw [List.getElem?_eq_getElem hj] at this
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at this
  cases this

/-- Value of a little-endian list of bits. -/
def ofBits : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * ofBits bs

lemma ofBits_bits (n : ℕ) : ofBits (Nat.bits n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ofBits]
    · rw [LS.Nat.bits_of_ne_zero' n (by omega), ofBits, ih (n / 2) (by omega)]
      by_cases h : n % 2 = 1 <;> simp [h] <;> omega

/-- Is a separator at or after `q`. -/
def sepF (C : Circuit) (q : ℕ) (p : ℕ) : Bool := decide (q ≤ p) && decide (tc C p = 2)

/-- One step of reading a number backwards from its end `e`. -/
def numF (C : Circuit) (e : ℕ) (v j : ℕ) : ℕ := 2 * v + tc C (e - 1 - j)

/-- End of the number at `q`. -/
def readE (C : Circuit) (q : ℕ) : ℕ := firstF (sepF C q) (gts C).length

/-- Value of the number at `q`. -/
def readV (C : Circuit) (q : ℕ) : ℕ := (List.range (readE C q - q)).foldl (numF C (readE C q)) 0

lemma natToks_get {a j : ℕ} (hj : j < (Nat.bits a).length) :
    ((natToks a)[j]'(by simp [natToks]; omega)).code = ((Nat.bits a)[j]).toNat := by
  simp only [natToks]
  rw [List.getElem_append_left (by simpa using hj), List.getElem_map]
  cases h : (Nat.bits a)[j] <;> simp [Tok.code]

lemma natToks_last (a : ℕ) :
    ((natToks a)[(Nat.bits a).length]'(by simp [natToks])).code = 2 := by
  simp only [natToks]
  rw [List.getElem_append_right (by simp)]
  simp [Tok.code]

lemma readNum_ok {q a : ℕ} (h : At C q (natToks a)) :
    readE C q = q + (Nat.bits a).length ∧ readV C q = a := by
  have hlenN : (natToks a).length = (Nat.bits a).length + 1 := by simp [natToks]
  have hd : ∀ j (hj : j < (Nat.bits a).length), tc C (q + j) = ((Nat.bits a)[j]'hj).toNat :=
      fun j hj => by
    rw [tc_of_At h (by omega)]; exact natToks_get hj
  have hs : tc C (q + (Nat.bits a).length) = 2 := by rw [tc_of_At h (by omega)]; exact natToks_last a
  have hlt : q + (Nat.bits a).length < (gts C).length := lt_of_At h (by omega)
  have hE : readE C q = q + (Nat.bits a).length := by
    unfold readE
    rcases firstF_spec (sepF C q) (gts C).length with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · have := h2 (q + (Nat.bits a).length) hlt
      simp [sepF, hs] at this
    · set r := firstF (sepF C q) (gts C).length
      simp only [sepF, Bool.and_eq_true, decide_eq_true_eq] at h2
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hr | hr
      · have := hd (r - q) (by omega)
        rw [show q + (r - q) = r by omega, h2.2] at this
        cases hb : (Nat.bits a)[r - q] <;> rw [hb] at this <;> simp at this
      · have := h3 (q + (Nat.bits a).length) hr
        simp [sepF, hs] at this
  refine ⟨hE, ?_⟩
  set L := (Nat.bits a).length with hL
  unfold readV
  rw [hE, Nat.add_sub_cancel_left]
  have key : ∀ m ≤ L, (List.range m).foldl (numF C (q + L)) 0 = ofBits ((Nat.bits a).drop (L - m)) := by
    intro m
    induction m with
    | zero => intro _; simp [ofBits, L]
    | succ m ih =>
      intro hm
      rw [LL.foldl_range_succ, ih (by omega), numF,
        show q + L - 1 - m = q + (L - (m + 1)) by omega, hd _ (by omega),
        List.drop_eq_getElem_cons (show L - (m + 1) < (Nat.bits a).length by omega), ofBits,
        show L - (m + 1) + 1 = L - m by omega]
      ring
  rw [key L le_rfl, Nat.sub_self, List.drop_zero, ofBits_bits]

/-! ## Parsing gates -/

/-- Start of gate `i` found by the scan. -/
def gStart (C : Circuit) (i : ℕ) : ℕ := ((List.range (gts C).length).foldl (gsF C i) (0, 0)).1

/-- Tag code of gate `i`. -/
def pTag (C : Circuit) (i : ℕ) : ℕ := tc C (gStart C i)

/-- Gate `i` is a constant. -/
def pIsC (C : Circuit) (i : ℕ) : Bool := decide (pTag C i = 6) || decide (pTag C i = 7)

/-- First argument of gate `i`. -/
def pLo (C : Circuit) (i : ℕ) : ℕ := if pIsC C i then 0 else readV C (gStart C i + 2)

/-- Last argument of gate `i`. -/
def pHi (C : Circuit) (i : ℕ) : ℕ :=
  if pIsC C i then 0 else
    if tc C (readE C (gStart C i + 2) + 1) = 4 then readV C (gStart C i + 2)
    else readV C (readE C (gStart C i + 2) + 1)

lemma gStart_eq {i : ℕ} (hi : i < C.length) : gStart C i = offs C i := by
  simp [gStart, gs_fold hi]

lemma pTag_eq {i : ℕ} (hi : i < C.length) : pTag C i = (C[i].toks[0]'(toks_pos _)).code := by
  rw [pTag, gStart_eq hi, ← Nat.add_zero (offs C i), tc_of_At (At_gate hi) (toks_pos _)]

lemma toks_zero_code (g : Gate) : (g.toks[0]'(toks_pos _)).code =
    match g.kind with
    | .input _ => 5 | .const false => 6 | .const true => 7 | .not => 8 | .and => 9 | .or => 10
    | .oracle => 11 := by
  obtain ⟨k, args⟩ := g
  rcases k with k | b | _ | _ | _ | _
  · rfl
  · cases b <;> rfl
  all_goals rfl

lemma kindAnd_iff {i : ℕ} (hi : i < C.length) : Conc.kindAnd C[i] = decide (pTag C i = 9) := by
  rw [pTag_eq hi, toks_zero_code]
  unfold Conc.kindAnd
  rcases C[i].kind with k | b | _ | _ | _ | _
  · rfl
  · cases b <;> rfl
  all_goals rfl

lemma kindConst_iff {i : ℕ} (hi : i < C.length) : Conc.kindConst C[i] = pIsC C i := by
  rw [pIsC, pTag_eq hi, toks_zero_code]
  unfold Conc.kindConst
  rcases C[i].kind with k | b | _ | _ | _ | _
  · rfl
  · cases b <;> rfl
  all_goals rfl

lemma kindTrue_iff {i : ℕ} (hi : i < C.length) : Conc.kindTrue C[i] = decide (pTag C i = 7) := by
  rw [pTag_eq hi, toks_zero_code]
  unfold Conc.kindTrue
  rcases C[i].kind with k | b | _ | _ | _ | _
  · rfl
  · cases b <;> rfl
  all_goals rfl

lemma natToks_mem_code {a : ℕ} : ∀ t ∈ natToks a, t.code ≤ 2 := by
  intro t ht
  simp only [natToks, List.mem_append, List.mem_map, List.mem_singleton] at ht
  rcases ht with ⟨b, -, rfl⟩ | rfl
  · cases b <;> simp [Tok.code]
  · simp [Tok.code]

lemma natToks_head_le (a : ℕ) : ((natToks a)[0]'(by simp [natToks])).code ≤ 2 :=
  natToks_mem_code _ (List.getElem_mem _)

lemma natToks_length (a : ℕ) : (natToks a).length = (Nat.bits a).length + 1 := by
  simp [natToks]

lemma parse_ok (hW : C.WellFormed 0) (hM : C.MonotoneFanin2) {i : ℕ} (hi : i < C.length) :
    pLo C i = Conc.lo C i ∧ pHi C i = Conc.hi C i := by
  have hA := At_gate hi
  have hk := kindConst_iff hi
  rcases hM C[i] (List.getElem_mem hi) with ⟨b, hb, ha⟩ | ⟨hko, h1, h2⟩
  · have hc : pIsC C i = true := by rw [← hk]; simp [Conc.kindConst, hb]
    simp [pLo, pHi, hc, Conc.lo, Conc.hi, hi, ha]
  · have hc : pIsC C i = false := by
      rw [← hk]; rcases hko with h | h <;> simp [Conc.kindConst, h]
    have htoks : ∃ t, C[i].toks = Tok.tag t :: Tok.lpar ::
        (C[i].args.flatMap natToks ++ [Tok.rpar]) := by
      unfold Gate.toks
      rcases hko with h | h <;> rw [h] <;> exact ⟨_, rfl⟩
    obtain ⟨tg, htoks⟩ := htoks
    rw [htoks, At_cons, At_cons] at hA
    obtain ⟨-, -, hA⟩ := hA
    rw [show offs C i + 1 + 1 = gStart C i + 2 by rw [gStart_eq hi]] at hA
    simp only [pLo, pHi, hc, Bool.false_eq_true, if_false, Conc.lo, Conc.hi, hi, dif_pos]
    rcases hargs : C[i].args with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · simp [hargs] at h1
    · rw [hargs] at hA
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hA
      have hA1 := (At_append.1 hA).1
      obtain ⟨hE, hV⟩ := readNum_ok hA1
      have hr := (At_append.1 hA).2
      rw [natToks_length] at hr
      have : tc C (readE C (gStart C i + 2) + 1) = 4 := by
        rw [hE, show gStart C i + 2 + (Nat.bits a).length + 1 =
          gStart C i + 2 + ((Nat.bits a).length + 1) + 0 by omega, tc_of_At hr (by simp)]
        rfl
      simp [this, hV]
    · rw [hargs] at hA
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] at hA
      have hA1 := (At_append.1 hA).1
      obtain ⟨hE, hV⟩ := readNum_ok hA1
      have hr := (At_append.1 hA).2
      rw [natToks_length] at hr
      have hB := (At_append.1 hr).1
      obtain ⟨hE2, hV2⟩ := readNum_ok hB
      have hne : tc C (readE C (gStart C i + 2) + 1) ≠ 4 := by
        rw [hE, show gStart C i + 2 + (Nat.bits a).length + 1 =
          gStart C i + 2 + ((Nat.bits a).length + 1) + 0 by omega,
          tc_of_At hB (by simp [natToks])]
        have := natToks_head_le b; omega
      rw [if_neg hne, hE, show gStart C i + 2 + (Nat.bits a).length + 1 =
          gStart C i + 2 + ((Nat.bits a).length + 1) by omega, hV2, hV]
      simp
    · simp only [hargs, List.length_cons] at h2; omega

lemma e1_lt (hM : C.MonotoneFanin2) {i : ℕ} (hi : i < C.length) (hc : pIsC C i = false) :
    readE C (gStart C i + 2) + 1 < (gts C).length := by
  have hA := At_gate hi
  have hk := kindConst_iff hi
  rcases hM C[i] (List.getElem_mem hi) with ⟨b, hb, ha⟩ | ⟨hko, h1, h2⟩
  · rw [hc] at hk; simp [Conc.kindConst, hb] at hk
  · have htoks : ∃ t, C[i].toks = Tok.tag t :: Tok.lpar ::
        (C[i].args.flatMap natToks ++ [Tok.rpar]) := by
      unfold Gate.toks
      rcases hko with h | h <;> rw [h] <;> exact ⟨_, rfl⟩
    obtain ⟨tg, htoks⟩ := htoks
    rw [htoks, At_cons, At_cons] at hA
    obtain ⟨-, -, hA⟩ := hA
    rw [show offs C i + 1 + 1 = gStart C i + 2 by rw [gStart_eq hi]] at hA
    rcases hargs : C[i].args with _ | ⟨a, t⟩
    · simp [hargs] at h1
    · rw [hargs, List.flatMap_cons, List.append_assoc] at hA
      obtain ⟨hE, -⟩ := readNum_ok (At_append.1 hA).1
      have hr := (At_append.1 hA).2
      rw [natToks_length] at hr
      have := lt_of_At hr (j := 0) (by simp)
      rw [hE]; omega

lemma lo_lt_n (hW : C.WellFormed 0) {i : ℕ} (hi : i < C.length) : Conc.lo C i < C.length := by
  simp only [Conc.lo, hi, dif_pos]
  rcases h : C[i].args with _ | ⟨a, t⟩
  · simp; omega
  · have := (hW.2 i hi).1 a (by rw [h]; simp)
    simp; omega

lemma hi_lt_n (hW : C.WellFormed 0) {i : ℕ} (hi : i < C.length) : Conc.hi C i < C.length := by
  simp only [Conc.hi, hi, dif_pos]
  rw [List.getLastD_eq_getLast?]
  rcases h : C[i].args.getLast? with _ | a
  · simp; omega
  · have := (hW.2 i hi).1 a (List.mem_of_getLast? h)
    simp; omega

end LP

end BLMS

end PathChecking
