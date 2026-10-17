module

public import RequestProject.CTLStarP.Prog.Nav

/-!
# Program fragments: counting loops and the tables of well-formed subformulas and subtrees
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open HL PT

/-! ## Counting loops -/

/-- A loop counting `P` down to `0`. -/
theorem hach_forDown {m : ℕ} {w : Word} {B : ℕ} (hB : 1 ≤ B) {body : Hs m} (P : Fin m)
    (I : ℕ → HSt m → Prop)
    (hstep : ∀ p σ1, I (p + 1) σ1 → σ1.v P = p + 1 →
      HAch w B body (σ1.set P p) (fun σ2 => I p σ2 ∧ σ2.v P = p))
    (k : ℕ) (hk : k ≤ B) (σ : HSt m) (hI : I k σ) (hP : σ.v P = k) :
    HAch w B (.loop (Ex.lt (.const 0) (.var P)) (.set P (.var P - .const 1) ;; body)) σ
      (fun σ' => I 0 σ' ∧ σ'.v P = 0) := by
  refine hach_while (fun σ1 => ∃ p ≤ k, I p σ1 ∧ σ1.v P = p) (fun σ1 => σ1.v P) _ ?_ ?_ ?_ σ
    ⟨k, le_rfl, hI, hP⟩
  · rintro σ1 ⟨p, hp, -, h⟩; simp [h]; omega
  · rintro σ1 ⟨p, hp, hI1, h⟩ hc
    simp [h] at hc; subst hc; exact ⟨hI1, h⟩
  · rintro σ1 ⟨p, hp, hI1, h⟩ hc
    simp [h] at hc
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    refine hach_seq (hach_set (by simp; omega) ?_)
    have : σ1.set P ((Ex.var P - Ex.const 1).ev w σ1) = σ1.set P q := by simp [h]
    rw [this]
    refine (hstep q σ1 hI1 h).mono ?_
    rintro σ2 ⟨h1, h2⟩
    exact ⟨⟨q, by omega, h1, h2⟩, by simp only [h2, h]; omega⟩

/-- A loop counting `P` up to the value `K` of `Nv`. -/
theorem hach_forUp {m : ℕ} {w : Word} {B : ℕ} {body : Hs m} (P Nv : Fin m) (hPN : P ≠ Nv) (K : ℕ)
    (hK : K + 1 ≤ B) (I : ℕ → HSt m → Prop)
    (hstep : ∀ p σ1, p < K → I p σ1 → σ1.v P = p → σ1.v Nv = K →
      HAch w B body σ1 (fun σ2 => σ2.v P = p ∧ σ2.v Nv = K ∧ I (p + 1) (σ2.set P (p + 1))))
    (p0 : ℕ) (hp0 : p0 ≤ K) (σ : HSt m) (hI : I p0 σ) (hP : σ.v P = p0) (hN : σ.v Nv = K) :
    HAch w B (.loop (Ex.lt (.var P) (.var Nv)) (body ;; .set P (.var P + .const 1))) σ
      (fun σ' => I K σ' ∧ σ'.v P = K ∧ σ'.v Nv = K) := by
  refine hach_while (fun σ1 => ∃ p ≤ K, I p σ1 ∧ σ1.v P = p ∧ σ1.v Nv = K)
    (fun σ1 => K - σ1.v P) _ ?_ ?_ ?_ σ ⟨p0, hp0, hI, hP, hN⟩
  · rintro σ1 ⟨p, hp, -, h, h'⟩; simp [h, h']; omega
  · rintro σ1 ⟨p, hp, hI1, h, h'⟩ hc
    simp [h, h'] at hc
    obtain rfl : p = K := by omega
    exact ⟨hI1, h, h'⟩
  · rintro σ1 ⟨p, hp, hI1, h, h'⟩ hc
    simp [h, h'] at hc
    refine hach_seq ((hstep p σ1 hc hI1 h h').mono ?_)
    rintro σ2 ⟨h1, h2, h3⟩
    refine hach_set (by simp [h1]; omega) ?_
    have : σ2.set P ((Ex.var P + Ex.const 1).ev w σ2) = σ2.set P (p + 1) := by simp [h1]
    rw [this]
    refine ⟨⟨p + 1, by omega, h3, by simp, by simp [Ne.symm hPN, h2]⟩, ?_⟩
    simp [h]; omega

variable {w : Word} {B : ℕ} {ts : List Tok}

lemma Ctx.b3 (h : Ctx ts w B) : 3 * ts.length + 64 ≤ B := by
  have := h.bnd
  have : 3 * ts.length ≤ 16 * (ts.length + 2) ^ 3 := by
    have : ts.length ≤ (ts.length + 2) ^ 3 := by
      calc ts.length ≤ ts.length + 2 := by omega
        _ = (ts.length + 2) ^ 1 := by ring
        _ ≤ (ts.length + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  omega

/-! ## Pure facts -/

lemma validF_step {p : ℕ} (hp : p < ts.length) : validF ts p =
    ((decide (tc ts p = 5) && numOK ts (p + 1)) || decide (tc ts p = 6) ||
      (decide (tc ts p ∈ [7, 9, 11]) && validF ts (p + 1)) ||
      (decide (tc ts p ∈ [8, 10]) && (validF ts (p + 1) && validF ts (fend ts (p + 1))))) := by
  rw [validF_eq, if_neg (by omega)]
  by_cases h5 : tc ts p = 5
  · simp [h5]
  by_cases h6 : tc ts p = 6
  · simp [h6]
  by_cases h7 : tc ts p = 7 ∨ tc ts p = 9 ∨ tc ts p = 11
  · rcases h7 with h | h | h <;> simp [h]
  by_cases h8 : tc ts p = 8 ∨ tc ts p = 10
  · rcases h8 with h | h <;> simp [h]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at *
  simp [h5, h6, h7, h8]

lemma kidsOK_step {p : ℕ} (hp : p < ts.length) : kidsOK ts p =
    (decide (tc ts p = 4) || (decide (tc ts p = 3) && (decide (tc ts (p + 1) = 3) &&
      (labSuf ts (p + 2) && (kidsOK ts (tend ts (p + 1)) && kidsOK ts (tend ts p)))))) := by
  rw [kidsOK_eq, if_neg (by omega)]
  by_cases h4 : tc ts p = 4
  · simp [h4]
  · simp only [h4, validLab]
    by_cases h3 : tc ts p = 3 <;> by_cases h3' : tc ts (p + 1) = 3 <;>
      simp [h3, h3', Bool.and_assoc]

lemma validF_ge {p : ℕ} (hp : ts.length ≤ p) : validF ts p = false := by
  rw [validF_eq, if_pos hp]

lemma kidsOK_ge {p : ℕ} (hp : ts.length ≤ p) : kidsOK ts p = false := by
  rw [kidsOK_eq, if_pos hp]

lemma fend_le {p : ℕ} (hp : p ≤ ts.length) : fend ts p ≤ ts.length := by
  have := scan_le (ts := ts) upF downF p 1; simp only [fend]; omega

lemma tend_le {p : ℕ} (hp : p ≤ ts.length) : tend ts p ≤ ts.length := by
  have := scan_le (ts := ts) upT downT p 0; simp only [tend]; omega

lemma le_fend (p : ℕ) : p ≤ fend ts p := le_scan _ _ _ _

lemma le_tend (p : ℕ) : p ≤ tend ts p := le_scan _ _ _ _

/-! ## Memory -/

/-- Contents of the memory during the first phase: well-formed formulas at positions `≥ a`,
well-formed lists of subtrees at positions `≥ b` (shifted by `n`). -/
def Mem1 (ts : List Tok) (a b x : ℕ) : Prop :=
  (x < ts.length ∧ a ≤ x ∧ validF ts x = true) ∨
    (ts.length ≤ x ∧ x < 2 * ts.length ∧ b ≤ x - ts.length ∧ kidsOK ts (x - ts.length) = true)

lemma readF {mem : Finset ℕ} {a b y : ℕ} (hm : ∀ x, x ∈ mem ↔ Mem1 ts a b x) (hy : a ≤ y) :
    (decide (y < ts.length) && decide (y ∈ mem)) = validF ts y := by
  by_cases h : y < ts.length
  · have : y ∈ mem ↔ validF ts y = true := by
      rw [hm]; unfold Mem1; constructor
      · rintro (⟨-, -, h'⟩ | ⟨h', -⟩)
        · exact h'
        · omega
      · intro h'; exact Or.inl ⟨h, hy, h'⟩
    by_cases hv : validF ts y = true
    · simp [h, this.2 hv, hv]
    · simp only [h, decide_true, Bool.true_and, Bool.not_eq_true] at hv ⊢
      simp only [hv, decide_eq_false_iff_not]; exact fun h' => by simp [this.1 h'] at hv
  · simp [h, validF_ge (show ts.length ≤ y by omega)]

lemma readK {mem : Finset ℕ} {a b y : ℕ} (hm : ∀ x, x ∈ mem ↔ Mem1 ts a b x) (hy : b ≤ y) :
    (decide (y < ts.length) && decide (ts.length + y ∈ mem)) = kidsOK ts y := by
  by_cases h : y < ts.length
  · have : ts.length + y ∈ mem ↔ kidsOK ts y = true := by
      rw [hm]; unfold Mem1; constructor
      · rintro (⟨h', -⟩ | ⟨-, -, -, h'⟩)
        · omega
        · simpa using h'
      · intro h'; exact Or.inr ⟨by omega, by omega, by simpa using hy, by simpa using h'⟩
    by_cases hv : kidsOK ts y = true
    · simp [h, this.2 hv, hv]
    · simp only [h, decide_true, Bool.true_and, Bool.not_eq_true] at hv ⊢
      simp only [hv, decide_eq_false_iff_not]; exact fun h' => by simp [this.1 h'] at hv
  · simp [h, kidsOK_ge (show ts.length ≤ y by omega)]

/-- Conditional insertion into the memory. -/
lemma hach_condSet {e a : Ex M} {σ : HSt M} {b : Bool} (he : e.Bnd w B σ) (ha : a.Bnd w B σ)
    (hev : e.ev w σ = bv b) :
    HAch w B (.ite e (.mset a) .skip) σ (fun σ' => σ'.v = σ.v ∧ σ'.out = σ.out ∧
      ∀ x, x ∈ σ'.mem ↔ x ∈ σ.mem ∨ (b = true ∧ x = a.ev w σ)) := by
  refine hach_ite he ?_
  cases b
  · rw [if_neg (by simp [hev])]
    exact hach_skip ⟨rfl, rfl, fun x => by simp⟩
  · rw [if_pos (by simp [hev])]
    exact hach_mset ha ⟨rfl, rfl, fun x => by simp [or_comm]⟩

lemma mem1_insF {m m' : Finset ℕ} {p b : ℕ} (hm : ∀ x, x ∈ m ↔ Mem1 ts (p + 1) b x)
    (hp : p < ts.length) (h' : ∀ x, x ∈ m' ↔ x ∈ m ∨ (validF ts p = true ∧ x = p)) :
    ∀ x, x ∈ m' ↔ Mem1 ts p b x := by
  intro x; rw [h', hm]; unfold Mem1
  constructor
  · rintro ((⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩) | ⟨hv, rfl⟩)
    · exact Or.inl ⟨h1, by omega, h3⟩
    · exact Or.inr ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨hp, le_rfl, hv⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩)
    · by_cases hx : x = p
      · subst hx; exact Or.inr ⟨h3, rfl⟩
      · exact Or.inl (Or.inl ⟨h1, by omega, h3⟩)
    · exact Or.inl (Or.inr ⟨h1, h2, h3, h4⟩)

lemma mem1_insK {m m' : Finset ℕ} {p a : ℕ} (hm : ∀ x, x ∈ m ↔ Mem1 ts a (p + 1) x)
    (hp : p < ts.length) (h' : ∀ x, x ∈ m' ↔ x ∈ m ∨ (kidsOK ts p = true ∧ x = ts.length + p)) :
    ∀ x, x ∈ m' ↔ Mem1 ts a p x := by
  intro x; rw [h', hm]; unfold Mem1
  constructor
  · rintro ((⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩) | ⟨hv, rfl⟩)
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2, by omega, h4⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by simpa using hv⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩)
    · exact Or.inl (Or.inl ⟨h1, h2, h3⟩)
    · by_cases hx : x - ts.length = p
      · refine Or.inr ⟨hx ▸ h4, by omega⟩
      · exact Or.inl (Or.inr ⟨h1, h2, by omega, h4⟩)

/-! ## The first phase -/

notation "vTP" => (26 : Fin 48)
notation "vTT" => (27 : Fin 48)
notation "vTA" => (28 : Fin 48)
notation "vTB" => (29 : Fin 48)
notation "vVT" => (30 : Fin 48)

/-- Guarded read of the formula table. -/
abbrev rdF (e : Ex M) : Ex M := Ex.band (Ex.lt e (.var vN)) (Ex.mem e)
/-- Guarded read of the subtree table. -/
abbrev rdK (e : Ex M) : Ex M := Ex.band (Ex.lt e (.var vN)) (Ex.mem (.var vN + e))

/-- Formula table entry. -/
def vfE : Ex M :=
  Ex.bor (Ex.band (Ex.eq (.tok (.var vTP)) (.const 5)) (.var vDR))
      (Ex.bor (Ex.eq (.tok (.var vTP)) (.const 6))
        (Ex.bor (Ex.band (Ex.inL (.tok (.var vTP)) [7, 9, 11]) (rdF (.var vTP + .const 1)))
          (Ex.band (Ex.inL (.tok (.var vTP)) [8, 10])
            (Ex.band (rdF (.var vTP + .const 1)) (rdF (.var vTT))))))

/-- Subtree table entry. -/
def kE : Ex M :=
  Ex.bor (Ex.eq (.tok (.var vTP)) (.const 4))
      (Ex.band (Ex.eq (.tok (.var vTP)) (.const 3))
        (Ex.band (Ex.eq (.tok (.var vTP + .const 1)) (.const 3))
          (Ex.band (.var vLR) (Ex.band (rdK (.var vTA)) (rdK (.var vSR))))))

/-- One round of the first phase, at position `TP`. -/
def tabStep : Hs M :=
  numOKP (.var vTP + .const 1) ;; fendP (.var vTP + .const 1) ;; .set vTT (.var vSR) ;;
  .ite vfE (.mset (.var vTP)) .skip ;;
  .set vLQ (.var vTP + .const 2) ;; labSufP ;; tendP (.var vTP + .const 1) ;;
  .set vTA (.var vSR) ;; tendP (.var vTP) ;;
  .ite kE (.mset (.var vN + .var vTP)) .skip

theorem hach_tabStep (hc : Ctx ts w B) (σ : HSt M) (p : ℕ) (hp : p < ts.length)
    (hN : σ.v vN = ts.length) (hP : σ.v vTP = p) (hm : ∀ x, x ∈ σ.mem ↔ Mem1 ts (p + 1) (p + 1) x) :
    HAch w B tabStep σ (fun σ' => σ'.v vN = ts.length ∧ σ'.v vTP = p ∧ σ'.out = σ.out ∧
      ∀ x, x ∈ σ'.mem ↔ Mem1 ts p p x) := by
  have hB64 := hc.b64
  have hBn := hc.b3
  refine hach_seq ((hach_numOKP hc σ hN _ (by bnd_tac <;> simp <;> omega)
    (by simp; omega)).mono ?_)
  rintro σ2 ⟨hDR, hf2⟩
  simp only [ev_add, ev_var, ev_const, hP] at hDR
  have e2 : ∀ i, i ∉ cl 7 → σ2.v i = σ.v i := hf2.1
  refine hach_seq ((hach_fendP hc σ2 (by rw [e2 _ (by decide), hN]) _
    (by bnd_tac <;> simp [e2 vTP (by decide), hP] <;> omega)
    (by simp [e2 vTP (by decide), hP]; omega)).mono ?_)
  rintro σ3 ⟨hF, hf3⟩
  simp only [ev_add, ev_var, ev_const, e2 vTP (by decide), hP] at hF
  have e3 : ∀ i, i ∉ cl 4 → σ3.v i = σ2.v i := hf3.1
  have hFl : fend ts (p + 1) ≤ ts.length := fend_le (by omega)
  have hFg : p + 1 ≤ fend ts (p + 1) := le_fend _
  refine hach_seq (hach_set (by simp; omega) ?_)
  set σ4 := σ3.set vTT ((Ex.var vSR).ev w σ3) with hσ4
  have e4 : ∀ i, i ≠ vTT → σ4.v i = σ3.v i := fun i hi => by simp [σ4, hi]
  have h4N : σ4.v vN = ts.length := by rw [e4 _ (by decide), e3 _ (by decide), e2 _ (by decide), hN]
  have h4P : σ4.v vTP = p := by rw [e4 _ (by decide), e3 _ (by decide), e2 _ (by decide), hP]
  have h4T : σ4.v vTT = fend ts (p + 1) := by simp [σ4, hF]
  have h4D : σ4.v vDR = bv (numOK ts (p + 1)) := by
    rw [e4 _ (by decide), e3 _ (by decide), hDR]
  have h4m : σ4.mem = σ.mem := by simp [σ4, hf3.2.1, hf2.2.1]
  have h4o : σ4.out = σ.out := by simp [σ4, hf3.2.2, hf2.2.2]
  have hDR1 := bv_le (numOK ts (p + 1))
  have hv : vfE.ev w σ4 = bv (validF ts p) := by
    rw [validF_step hp]
    simp only [vfE, rdF, ev_bor', ev_band', ev_eq, ev_inL', ev_lt, ev_mem, ev_tok, ev_var, ev_add,
      ev_const, hc.tok, h4P, h4T, h4D, h4N, h4m, bv_mul_bv, pos_bv_add_bv, Bool.decide_eq_true,
      readF hm le_rfl, readF hm hFg, Bool.or_assoc]
  refine hach_seq ((hach_condSet (by unfold vfE; bnd_tac <;> (try simp [h4P, h4T, h4D, h4N]) <;> omega)
    (by simp [h4P]; omega) hv).mono ?_)
  rintro σ5 ⟨h5v, h5o, h5m⟩
  simp only [ev_var, h4P, h4m] at h5m
  have hm5 := mem1_insF hm hp h5m
  have e5 : ∀ i, σ5.v i = σ4.v i := fun i => by rw [h5v]
  refine hach_seq (hach_set (by simp [e5, h4P]; omega) ?_)
  refine hach_seq ((hach_labSufP hc _ (by simp [e5, h4N])
    (by simp [e5, h4P]; omega)).mono ?_)
  rintro σ6 ⟨hL, hf6⟩
  simp only [HSt.set_v, Function.update_self, ev_add, ev_var, ev_const, e5, h4P] at hL
  have e6 : ∀ i, i ∉ cl 14 → σ6.v i = σ4.v i := fun i hi => by
    rw [hf6.1 i hi]; simp [e5, show i ≠ vLQ from fun h => hi (h ▸ by decide)]
  refine hach_seq ((hach_tendP hc σ6 (by rw [e6 _ (by decide), h4N]) _
    (by bnd_tac <;> simp [e6 vTP (by decide), h4P] <;> omega)
    (by simp [e6 vTP (by decide), h4P]; omega)).mono ?_)
  rintro σ7 ⟨hTA, hf7⟩
  simp only [ev_add, ev_var, ev_const, e6 vTP (by decide), h4P] at hTA
  have hTAl : tend ts (p + 1) ≤ ts.length := tend_le (by omega)
  have hTAg : p + 1 ≤ tend ts (p + 1) := le_tend _
  refine hach_seq (hach_set (by simp; omega) ?_)
  have e8 : ∀ i, i ∉ cl 14 → i ≠ vTA → (σ7.set vTA ((Ex.var vSR).ev w σ7)).v i = σ4.v i :=
    fun i hi hi' => by
      simp only [HSt.set_v, Function.update_apply, hi', if_false]
      rw [hf7.1 i (fun h => hi (cl_mono (by omega) h)), e6 i hi]
  have h7P : σ7.v vTP = p := by rw [hf7.1 _ (by decide), e6 _ (by decide), h4P]
  refine hach_seq ((hach_tendP hc _ (by rw [e8 _ (by decide) (by decide), h4N]) _
    (by simp [h7P]; omega)
    (by simp [h7P]; omega)).mono ?_)
  rintro σ9 ⟨hTB, hf9⟩
  simp only [ev_var, HSt.set_v, Function.update_apply, Fin.reduceEq, if_false, h7P] at hTB
  have hTBl : tend ts p ≤ ts.length := tend_le (by omega)
  have hTBg : p + 1 ≤ tend ts p := tend_gt ts (by omega)
  have e9 : ∀ i, i ∉ cl 14 → i ≠ vTA → σ9.v i = σ4.v i := fun i hi hi' => by
    rw [hf9.1 i (fun h => hi (cl_mono (by omega) h)), e8 i hi hi']
  have h9N : σ9.v vN = ts.length := by rw [e9 _ (by decide) (by decide), h4N]
  have h9P : σ9.v vTP = p := by rw [e9 _ (by decide) (by decide), h4P]
  have h9A : σ9.v vTA = tend ts (p + 1) := by
    rw [hf9.1 _ (by decide)]; simp [hTA]
  have h9L : σ9.v vLR = bv (labSuf ts (p + 2)) := by
    rw [hf9.1 _ (by decide)]; simp; rw [hf7.1 _ (by decide), hL]
  have h9m : σ9.mem = σ5.mem := by
    rw [hf9.2.1]; simp only [HSt.set_mem]; rw [hf7.2.1, hf6.2.1]; rfl
  have h9o : σ9.out = σ.out := by
    rw [hf9.2.2]; simp only [HSt.set_out]; rw [hf7.2.2, hf6.2.2]; simp [h5o, h4o]
  rw [← h9m] at hm5
  have hL1 := bv_le (labSuf ts (p + 2))
  have hk : kE.ev w σ9 = bv (kidsOK ts p) := by
    rw [kidsOK_step hp]
    simp only [kE, rdK, ev_bor', ev_band', ev_eq, ev_lt, ev_mem, ev_tok, ev_var, ev_add,
      ev_const, hc.tok, h9P, h9A, hTB, h9L, h9N, bv_mul_bv, pos_bv_add_bv, Bool.decide_eq_true,
      readK hm5 hTAg, readK hm5 hTBg]
  refine (hach_condSet (by unfold kE; bnd_tac <;> (try simp [h9P, h9A, hTB, h9L, h9N]) <;> omega)
    (by simp [h9P, h9N]; omega) hk).mono ?_
  rintro σ10 ⟨h10v, h10o, h10m⟩
  simp only [ev_add, ev_var, h9P, h9N] at h10m
  refine ⟨by rw [h10v, h9N], by rw [h10v, h9P], by rw [h10o, h9o], mem1_insK hm5 hp h10m⟩

lemma validTop_step : validTop ts =
    if tc ts (fend ts 1) = 4 ∧ tc ts (fend ts 1 + 2) = 3 then
      (decide (tc ts 0 = 3) && (validF ts 1 && (decide (tc ts (fend ts 1 + 1) = 3) &&
        (labSuf ts (fend ts 1 + 3) && (kidsOK ts (tend ts (fend ts 1 + 2)) &&
          decide (tend ts (fend ts 1 + 1) = ts.length))))))
    else false := by
  unfold validTop validT validLab
  split_ifs with h
  · simp only [h.1, h.2, beq_self_eq_true, Bool.true_and, Bool.and_true]
    by_cases h0 : tc ts 0 = 3 <;> by_cases h1 : tc ts (fend ts 1 + 1) = 3 <;>
      simp [h0, h1, Bool.and_assoc, add_assoc, beq_eq_decide]
  · rcases not_and_or.1 h with h | h
    · simp [h]
    · simp [h, add_assoc]

/-- Final check of the first phase: `VT := validTop`. -/
def topP : Hs M :=
  fendP (.const 1) ;; .set vTA (.var vSR) ;;
  .ite (Ex.band (Ex.eq (.tok (.var vTA)) (.const 4)) (Ex.eq (.tok (.var vTA + .const 2)) (.const 3)))
    (.set vLQ (.var vTA + .const 3) ;; labSufP ;; tendP (.var vTA + .const 2) ;;
      .set vTB (.var vSR) ;; tendP (.var vTA + .const 1) ;;
      .set vVT (Ex.band (Ex.eq (.tok (.const 0)) (.const 3)) (Ex.band (rdF (.const 1))
        (Ex.band (Ex.eq (.tok (.var vTA + .const 1)) (.const 3)) (Ex.band (.var vLR)
          (Ex.band (rdK (.var vTB)) (Ex.eq (.var vSR) (.var vN))))))))
    (.set vVT (.const 0))

theorem hach_topP (hc : Ctx ts w B) (σ : HSt M) (hN : σ.v vN = ts.length)
    (hm : ∀ x, x ∈ σ.mem ↔ Mem1 ts 0 0 x) :
    HAch w B topP σ (fun σ' => σ'.v vVT = bv (validTop ts) ∧ Frame (cl 31) σ σ') := by
  have hB64 := hc.b64
  have hBn := hc.b3
  refine hach_seq ((hach_fendP hc σ hN _ (by simp; omega) (by simp)).mono ?_)
  rintro σ2 ⟨hF, hf2⟩
  simp only [ev_const] at hF
  have hFl : fend ts 1 ≤ ts.length + 1 := by
    have := scan_le (ts := ts) upF downF 1 1; simp only [fend]; omega
  refine hach_seq (hach_set (by simp; omega) ?_)
  have hf3 : Frame (cl 31) σ (σ2.set vTA ((Ex.var vSR).ev w σ2)) :=
    (Frame.cl_mono hf2 (by omega)).set (by decide) _
  have h3A : (σ2.set vTA ((Ex.var vSR).ev w σ2)).v vTA = fend ts 1 := by simp [hF]
  have h3N : (σ2.set vTA ((Ex.var vSR).ev w σ2)).v vN = ts.length := by
    simp [hf2.1 vN (by decide), hN]
  generalize σ2.set vTA ((Ex.var vSR).ev w σ2) = σ3 at hf3 h3A h3N ⊢
  have h3m : σ3.mem = σ.mem := hf3.2.1
  refine hach_ite (by bnd_tac <;> (try simp [h3A]) <;> omega) ?_
  simp only [ne_eq, ev_band', ev_eq, ev_tok, ev_var, ev_add, ev_const, hc.tok, h3A, bv_mul_bv,
    bv_eq_zero, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_or, not_not]
  split_ifs with hg
  · have h4 := hg.1
    have h2 := hg.2
    have hFn : fend ts 1 + 2 < ts.length := lt_of_tc_ne (by omega)
    refine hach_seq (hach_set (by simp [h3A]; omega) ?_)
    have hf3' : Frame (cl 31) σ (σ3.set vLQ ((Ex.var vTA + Ex.const 3).ev w σ3)) :=
      hf3.set (by decide) _
    have h3Q : (σ3.set vLQ ((Ex.var vTA + Ex.const 3).ev w σ3)).v vLQ = fend ts 1 + 3 := by
      simp [h3A]
    have h3A' : (σ3.set vLQ ((Ex.var vTA + Ex.const 3).ev w σ3)).v vTA = fend ts 1 := by
      simp [h3A]
    have h3N' : (σ3.set vLQ ((Ex.var vTA + Ex.const 3).ev w σ3)).v vN = ts.length := by
      simp [h3N]
    generalize σ3.set vLQ ((Ex.var vTA + Ex.const 3).ev w σ3) = σ3' at hf3' h3Q h3A' h3N' ⊢
    refine hach_seq ((hach_labSufP hc σ3' h3N' (by omega)).mono ?_)
    rintro σ4 ⟨hL, hf4⟩
    rw [h3Q] at hL
    have h4A : σ4.v vTA = fend ts 1 := by rw [hf4.1 _ (by decide), h3A']
    have h4N : σ4.v vN = ts.length := by rw [hf4.1 _ (by decide), h3N']
    have hf4' : Frame (cl 31) σ σ4 := hf3'.trans (Frame.cl_mono hf4 (by omega))
    refine hach_seq ((hach_tendP hc σ4 h4N _ (by simp [h4A]; omega) (by simp [h4A]; omega)).mono ?_)
    rintro σ5 ⟨hTB, hf5⟩
    simp only [ev_add, ev_var, ev_const, h4A] at hTB
    have hTBl : tend ts (fend ts 1 + 2) ≤ ts.length := tend_le (by omega)
    have h5L : σ5.v vLR = bv (labSuf ts (fend ts 1 + 3)) := by rw [hf5.1 _ (by decide), hL]
    have hf5' : Frame (cl 31) σ σ5 := hf4'.trans (Frame.cl_mono hf5 (by omega))
    refine hach_seq (hach_set (by simp [hTB]; omega) ?_)
    have h6A : (σ5.set vTB ((Ex.var vSR).ev w σ5)).v vTA = fend ts 1 := by
      simp [hf5.1 vTA (by decide), h4A]
    have h6N : (σ5.set vTB ((Ex.var vSR).ev w σ5)).v vN = ts.length := by
      simp [hf5.1 vN (by decide), h4N]
    have h6B : (σ5.set vTB ((Ex.var vSR).ev w σ5)).v vTB = tend ts (fend ts 1 + 2) := by
      simp [hTB]
    have h6L : (σ5.set vTB ((Ex.var vSR).ev w σ5)).v vLR = bv (labSuf ts (fend ts 1 + 3)) := by
      simp [h5L]
    have hf6 : Frame (cl 31) σ (σ5.set vTB ((Ex.var vSR).ev w σ5)) := hf5'.set (by decide) _
    generalize σ5.set vTB ((Ex.var vSR).ev w σ5) = σ6 at h6A h6N h6B h6L hf6 ⊢
    refine hach_seq ((hach_tendP hc _ h6N _ (by simp [h6A]; omega) (by simp [h6A]; omega)).mono ?_)
    rintro σ7 ⟨hS, hf7⟩
    simp only [ev_add, ev_var, ev_const, h6A] at hS
    have h7A : σ7.v vTA = fend ts 1 := by rw [hf7.1 _ (by decide), h6A]
    have h7N : σ7.v vN = ts.length := by rw [hf7.1 _ (by decide), h6N]
    have h7B : σ7.v vTB = tend ts (fend ts 1 + 2) := by rw [hf7.1 _ (by decide), h6B]
    have h7L : σ7.v vLR = bv (labSuf ts (fend ts 1 + 3)) := by rw [hf7.1 _ (by decide), h6L]
    have hf7' : Frame (cl 31) σ σ7 := hf6.trans (Frame.cl_mono hf7 (by omega))
    have h7m : σ7.mem = σ.mem := hf7'.2.1
    have hL1 := bv_le (labSuf ts (fend ts 1 + 3))
    have hSl : tend ts (fend ts 1 + 1) ≤ ts.length := tend_le (by omega)
    refine hach_set (by bnd_tac <;> (try simp [h7A, h7N, h7B, h7L, hS]) <;> omega)
      ⟨?_, hf7'.set (by decide) _⟩
    simp only [HSt.set_v, Function.update_self, rdF, rdK, ev_band', ev_eq, ev_lt, ev_mem, ev_tok,
      ev_var, ev_add, ev_const, hc.tok, h7A, h7N, h7B, h7L, hS, h7m, bv_mul_bv,
      readF hm (show 0 ≤ 1 by omega), readK hm (Nat.zero_le _), validTop_step, if_pos hg]
  · refine hach_set (by simp) ⟨?_, hf3.set (by decide) _⟩
    simp only [HSt.set_v, Function.update_self, ev_const, validTop_step]
    rw [if_neg (by tauto)]; rfl

end CTLP

end PathChecking
