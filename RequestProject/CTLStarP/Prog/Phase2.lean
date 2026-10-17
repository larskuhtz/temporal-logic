module

public import RequestProject.CTLStarP.Prog.Val

/-!
# The loops of the second phase and the final check
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open HL PT

variable {w : Word} {B : ℕ} {ts : List Tok}

/-! ## Memory lemmas -/

lemma mem2_congr {mem : Finset ℕ} {D D' : ℕ → ℕ → ℕ → Prop} (hm : ∀ x, x ∈ mem ↔ Mem2 ts D x)
    (hD : ∀ a b c, a < ts.length → b < ts.length → c < ts.length → (D a b c ↔ D' a b c)) :
    ∀ x, x ∈ mem ↔ Mem2 ts D' x := by
  intro x; rw [hm]; unfold Mem2
  constructor
  · rintro (h | ⟨a, b, c, ha, hb, hc, hd, hv, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, b, c, ha, hb, hc, (hD a b c ha hb hc).1 hd, hv, rfl⟩
  · rintro (h | ⟨a, b, c, ha, hb, hc, hd, hv, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, b, c, ha, hb, hc, (hD a b c ha hb hc).2 hd, hv, rfl⟩

lemma mem2_ins {m m' : Finset ℕ} {j u ℓ : ℕ} (hj : j < ts.length) (hu : u < ts.length)
    (hl : ℓ < ts.length) (hm : ∀ x, x ∈ m ↔ Mem2 ts (Dn j u ℓ) x)
    (h' : ∀ x, x ∈ m' ↔ x ∈ m ∨ (val ts j u ℓ = true ∧ x = addr ts.length j u ℓ)) :
    ∀ x, x ∈ m' ↔ Mem2 ts (Dn j u (ℓ + 1)) x := by
  intro x; rw [h', hm]; unfold Mem2 Dn
  constructor
  · rintro ((h | ⟨a, b, c, ha, hb, hc, hd, hv, rfl⟩) | ⟨hv, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, b, c, ha, hb, hc, by omega, hv, rfl⟩
    · exact Or.inr ⟨j, u, ℓ, hj, hu, hl, by omega, hv, rfl⟩
  · rintro (h | ⟨a, b, c, ha, hb, hc, hd, hv, rfl⟩)
    · exact Or.inl (Or.inl h)
    · by_cases he : a = j ∧ b = u ∧ c = ℓ
      · obtain ⟨rfl, rfl, rfl⟩ := he; exact Or.inr ⟨hv, rfl⟩
      · exact Or.inl (Or.inr ⟨a, b, c, ha, hb, hc, by omega, hv, rfl⟩)

/-! ## One entry, stored -/

lemma bnd_addrE (hc : Ctx ts w B) {σ : HSt M} (hN : σ.v vN = ts.length) {a b c : Ex M}
    (ha : a.Bnd w B σ) (hb : b.Bnd w B σ) (hcc : c.Bnd w B σ) (ha' : a.ev w σ ≤ ts.length + 1)
    (hb' : b.ev w σ ≤ ts.length + 1) (hc' : c.ev w σ ≤ ts.length + 1) :
    (addrE a b c).Bnd w B σ := by
  have hB := hc.bnd
  set n := ts.length
  have h1 : a.ev w σ * n ≤ (n + 1) * n := Nat.mul_le_mul_right _ ha'
  have h2 : (a.ev w σ * n + b.ev w σ) * n ≤ ((n + 1) * n + (n + 1)) * n :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : ((n + 1) * n + (n + 1)) * n + (n + 1) + (n + n) ≤ 16 * (n + 2) ^ 3 + 64 := by
    ring_nf; nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]
  have h4 : (n + 1) * n + (n + 1) ≤ ((n + 1) * n + (n + 1)) * n + (n + 1) + (n + n) + 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h]; simp
    · nlinarith
  unfold addrE
  simp only [bnd_mul, bnd_var, bnd_add, ev_var, ev_mul, ev_add, hN]
  repeat' apply And.intro
  all_goals first
    | assumption
    | omega
    | linarith

@[simp] lemma ev_addrE (σ : HSt M) (a b c : Ex M) :
    (addrE a b c).ev w σ = addr (σ.v vN) (a.ev w σ) (b.ev w σ) (c.ev w σ) := by
  simp [addrE, addr]

/-- Compute and store the entry `(J, U, L)`. -/
def valStep : Hs M :=
  valCompute ;; .ite (.var vB) (.mset (addrE (.var vJ) (.var vU) (.var vL))) .skip

theorem hach_valStep {σ : HSt M} {j u ℓ : ℕ} (h : VCtx ts w B σ j u ℓ) :
    HAch w B valStep σ (fun σ' => (∀ i, i ∉ clV → σ'.v i = σ.v i) ∧ σ'.out = σ.out ∧
      ∀ x, x ∈ σ'.mem ↔ Mem2 ts (Dn j u (ℓ + 1)) x) := by
  have hB64 := h.hc.b64
  have hBn := h.hc.bn
  have hl := h.hl; have hu := h.hu; have hj := h.hj
  refine hach_seq ((hach_valCompute h).mono ?_)
  rintro σ2 ⟨hB2, hf2⟩
  have h2 := h.of_frame hf2
  have := bv_le (val ts j u ℓ)
  refine (hach_condSet (b := val ts j u ℓ) (by simp [hB2]; omega)
    (bnd_addrE h.hc h2.hN (by simp [h2.hJ]; omega) (by simp [h2.hU]; omega)
      (by simp [h2.hL]; omega) (by simp [h2.hJ]; omega) (by simp [h2.hU]; omega)
      (by simp [h2.hL]; omega)) (by simp [hB2])).mono ?_
  rintro σ3 ⟨h3v, h3o, h3m⟩
  refine ⟨fun i hi => by rw [h3v, hf2.1 i hi], by rw [h3o, hf2.2.2], mem2_ins hj hu hl h2.hm ?_⟩
  simpa [h2.hN, h2.hJ, h2.hU, h2.hL] using h3m

/-! ## The loops -/

/-- All entries `(J, U, ℓ)`. -/
def lineP : Hs M :=
  .set vL (.const 0) ;;
  .loop (Ex.lt (.var vL) (.var vN)) (valStep ;; .set vL (.var vL + .const 1))

/-- Variables clobbered by `lineP`. -/
def clL : List (Fin 48) := clV ++ [vL]

theorem hach_lineP (hc : Ctx ts w B) {σ : HSt M} {j u : ℕ} (hN : σ.v vN = ts.length)
    (hJ : σ.v vJ = j) (hU : σ.v vU = u) (hj : j < ts.length) (hu : u < ts.length)
    (hm : ∀ x, x ∈ σ.mem ↔ Mem2 ts (Dn j u 0) x) :
    HAch w B lineP σ (fun σ' => (∀ i, i ∉ clL → σ'.v i = σ.v i) ∧ σ'.out = σ.out ∧
      ∀ x, x ∈ σ'.mem ↔ Mem2 ts (Dn j u ts.length) x) := by
  have hB64 := hc.b64
  have hBn := hc.bn
  refine hach_seq (hach_set (bnd_const' (by omega)) ?_)
  let I : ℕ → HSt M → Prop := fun ℓ σ1 => (∀ i, i ∉ clL → σ1.v i = σ.v i) ∧ σ1.out = σ.out ∧
    ∀ x, x ∈ σ1.mem ↔ Mem2 ts (Dn j u ℓ) x
  have hnl : ∀ i, i ∉ clL → i ≠ vL := fun i hi e => hi (by subst e; decide)
  have hnv : ∀ i, i ∉ clL → i ∉ clV := fun i hi h => hi (List.mem_append_left _ h)
  refine (hach_forUp vL vN (by decide) ts.length (by omega) I ?_ 0 (Nat.zero_le _)
    (σ.set vL ((Ex.const 0 : Ex M).ev w σ))
    ⟨fun i hi => by simp [hnl i hi], rfl, hm⟩ (by simp)
    (by simp [hN])).mono ?_
  · intro p σ1 hp ⟨hv1, ho1, hm1⟩ hP hN1
    have hctx : VCtx ts w B σ1 j u p :=
      ⟨hc, hN1, by rw [hv1 _ (by decide), hJ], by rw [hv1 _ (by decide), hU], hP, hj, hu, hp, hm1⟩
    refine (hach_valStep hctx).mono ?_
    rintro σ2 ⟨hv2, ho2, hm2⟩
    refine ⟨by rw [hv2 _ (by decide), hP], by rw [hv2 _ (by decide), hN1], ?_, ?_, ?_⟩
    · intro i hi
      simp only [HSt.set_v, Function.update_apply, hnl i hi, if_false]
      rw [hv2 i (hnv i hi), hv1 i hi]
    · simp [ho2, ho1]
    · exact hm2
  · rintro σ' ⟨⟨hv, ho, hm⟩, -, -⟩
    exact ⟨hv, ho, hm⟩

/-- All entries `(J, u, ℓ)`. -/
def colP : Hs M :=
  .set vU (.var vN) ;;
  .loop (Ex.lt (.const 0) (.var vU)) (.set vU (.var vU - .const 1) ;; lineP)

/-- Variables clobbered by `colP`. -/
def clC : List (Fin 48) := clL ++ [vU]

theorem hach_colP (hc : Ctx ts w B) {σ : HSt M} {j : ℕ} (hN : σ.v vN = ts.length)
    (hJ : σ.v vJ = j) (hj : j < ts.length)
    (hm : ∀ x, x ∈ σ.mem ↔ Mem2 ts (fun a _ _ => j + 1 ≤ a) x) :
    HAch w B colP σ (fun σ' => (∀ i, i ∉ clC → σ'.v i = σ.v i) ∧ σ'.out = σ.out ∧
      ∀ x, x ∈ σ'.mem ↔ Mem2 ts (fun a _ _ => j ≤ a) x) := by
  have hB64 := hc.b64
  have hBn := hc.bn
  refine hach_seq (hach_set (by simp [hN]; omega) ?_)
  let I : ℕ → HSt M → Prop := fun k σ1 => k ≤ ts.length ∧ (∀ i, i ∉ clC → σ1.v i = σ.v i) ∧
    σ1.out = σ.out ∧ ∀ x, x ∈ σ1.mem ↔ Mem2 ts (fun a b _ => j < a ∨ (a = j ∧ k ≤ b)) x
  have hnu : ∀ i, i ∉ clC → i ≠ vU := fun i hi e => hi (by subst e; decide)
  have hnl : ∀ i, i ∉ clC → i ∉ clL := fun i hi h => hi (List.mem_append_left _ h)
  refine (hach_forDown (by omega) vU I ?_ ts.length (by omega)
    (σ.set vU ((Ex.var vN : Ex M).ev w σ))
    ⟨le_rfl, fun i hi => by simp [hnu i hi], rfl, mem2_congr hm (fun a b c _ hb _ => by omega)⟩
    (by simp [hN])).mono ?_
  · intro p σ1 ⟨hp, hv1, ho1, hm1⟩ hP
    have e1 : ∀ i, i ∉ clC → (σ1.set vU p).v i = σ.v i := fun i hi => by
      simp [hnu i hi, hv1 i hi]
    refine (hach_lineP (σ := σ1.set vU p) (u := p) hc (by simpa [hN] using e1 vN (by decide)) (by simpa [hJ] using e1 vJ (by decide))
      (by simp) hj (by omega) (mem2_congr hm1 (fun a b c _ _ _ => by simp only [Dn]; omega))).mono ?_
    rintro σ2 ⟨hv2, ho2, hm2⟩
    refine ⟨⟨by omega, fun i hi => by rw [hv2 i (hnl i hi), e1 i hi], by rw [ho2, HSt.set_out, ho1],
      mem2_congr hm2 (fun a b c _ _ hc => by simp only [Dn]; omega)⟩, by rw [hv2 _ (by decide)]; simp⟩
  · rintro σ' ⟨⟨-, hv, ho, hm⟩, -⟩
    exact ⟨hv, ho, mem2_congr hm (fun a b c _ _ _ => by omega)⟩

/-- The second phase: all entries. -/
def phase2 : Hs M :=
  .set vJ (.var vN) ;;
  .loop (Ex.lt (.const 0) (.var vJ)) (.set vJ (.var vJ - .const 1) ;; colP)

/-- Variables clobbered by `phase2`. -/
def clP : List (Fin 48) := clC ++ [vJ]

theorem hach_phase2 (hc : Ctx ts w B) {σ : HSt M} (hN : σ.v vN = ts.length)
    (hm : ∀ x, x ∈ σ.mem ↔ Mem1 ts 0 0 x) :
    HAch w B phase2 σ (fun σ' => (∀ i, i ∉ clP → σ'.v i = σ.v i) ∧ σ'.out = σ.out ∧
      ∀ x, x ∈ σ'.mem ↔ Mem2 ts (fun _ _ _ => True) x) := by
  have hB64 := hc.b64
  have hBn := hc.bn
  refine hach_seq (hach_set (by simp [hN]; omega) ?_)
  let I : ℕ → HSt M → Prop := fun k σ1 => k ≤ ts.length ∧ (∀ i, i ∉ clP → σ1.v i = σ.v i) ∧
    σ1.out = σ.out ∧ ∀ x, x ∈ σ1.mem ↔ Mem2 ts (fun a _ _ => k ≤ a) x
  have hnj : ∀ i, i ∉ clP → i ≠ vJ := fun i hi e => hi (by subst e; decide)
  have hnc : ∀ i, i ∉ clP → i ∉ clC := fun i hi h => hi (List.mem_append_left _ h)
  have hm0 : ∀ x, x ∈ σ.mem ↔ Mem2 ts (fun a _ _ => ts.length ≤ a) x := by
    intro x; rw [hm]; unfold Mem2
    constructor
    · exact Or.inl
    · rintro (h | ⟨a, b, c, ha, -, -, hd, -⟩)
      · exact h
      · omega
  refine (hach_forDown (by omega) vJ I ?_ ts.length (by omega)
    (σ.set vJ ((Ex.var vN : Ex M).ev w σ))
    ⟨le_rfl, fun i hi => by simp [hnj i hi], rfl, hm0⟩ (by simp [hN])).mono ?_
  · intro p σ1 ⟨hp, hv1, ho1, hm1⟩ hP
    have e1 : ∀ i, i ∉ clP → (σ1.set vJ p).v i = σ.v i := fun i hi => by
      simp [hnj i hi, hv1 i hi]
    refine (hach_colP (σ := σ1.set vJ p) (j := p) hc (by simpa [hN] using e1 vN (by decide)) (by simp) (by omega) hm1).mono ?_
    rintro σ2 ⟨hv2, ho2, hm2⟩
    exact ⟨⟨by omega, fun i hi => by rw [hv2 i (hnc i hi), e1 i hi], by rw [ho2, HSt.set_out, ho1], hm2⟩,
      by rw [hv2 _ (by decide)]; simp⟩
  · rintro σ' ⟨⟨-, hv, ho, hm⟩, -⟩
    exact ⟨hv, ho, mem2_congr hm (fun a b c _ _ _ => by simp)⟩

/-! ## The final check -/

/-- `A := ∀ ℓ < N, val 1 root ℓ`, then output `A`. -/
def finalP : Hs M :=
  fendP (.const 1) ;; .set vR (.var vSR + .const 1) ;; .set vA (.const 1) ;; .set vL (.const 0) ;;
  .loop (Ex.lt (.var vL) (.var vN))
    (.set vA (Ex.band (.var vA) (rdV (.const 1) (.var vR) (.var vL))) ;;
      .set vL (.var vL + .const 1)) ;;
  .ite (.var vA) (.out true) (.out false)

theorem hach_finalP (hc : Ctx ts w B) {σ : HSt M} (hN : σ.v vN = ts.length)
    (hv : validTop ts = true) (hm : ∀ x, x ∈ σ.mem ↔ Mem2 ts (fun _ _ _ => True) x) :
    HAch w B finalP σ (fun σ' => σ'.out = σ.out ++ [decideCTL ts]) := by
  have hB64 := hc.b64
  have hBn := hc.bn
  have hg : tc ts (fend ts 1) = 4 ∧ tc ts (fend ts 1 + 2) = 3 := by
    rw [validTop_step] at hv
    split_ifs at hv with hg
    · exact hg
  have hr : fend ts 1 + 2 < ts.length := lt_of_tc_ne (by omega)
  have hF1 := le_fend (ts := ts) 1
  set r := fend ts 1 + 1 with hrdef
  have hrl : r < ts.length := by omega
  refine hach_seq ((hach_fendP hc σ hN _ (by simp; omega) (by simp)).mono ?_)
  rintro σ2 ⟨hF, hf2⟩
  simp only [ev_const] at hF
  have h2N : σ2.v vN = ts.length := by rw [hf2.1 _ (by decide), hN]
  refine hach_seq (hach_set (by simp [hF]; omega) (hach_seq (hach_set (bnd_const' (by omega))
    (hach_seq (hach_set (bnd_const' (by omega)) (hach_seq ?_))))))
  · let I : ℕ → HSt M → Prop := fun k σ1 => σ1.v vR = r ∧ σ1.out = σ.out ∧ σ1.mem = σ.mem ∧
      σ1.v vA = bv ((List.range k).all fun ℓ => val ts 1 r ℓ)
    let σ3 : HSt M := ((σ2.set vR ((Ex.var vSR + Ex.const 1).ev w σ2)).set vA
      ((Ex.const 1 : Ex M).ev w (σ2.set vR ((Ex.var vSR + Ex.const 1).ev w σ2)))).set vL
      ((Ex.const 0 : Ex M).ev w ((σ2.set vR ((Ex.var vSR + Ex.const 1).ev w σ2)).set vA
      ((Ex.const 1 : Ex M).ev w (σ2.set vR ((Ex.var vSR + Ex.const 1).ev w σ2)))))
    refine (hach_forUp vL vN (by decide) ts.length (by omega) I ?_ 0 (Nat.zero_le _) σ3
      ⟨by simp [σ3, hF, hrdef], by simp [σ3, hf2.2.2], by simp [σ3, hf2.2.1], by simp [σ3]⟩
      (by simp [σ3]) (by simp [σ3, h2N])).mono ?_
    · intro p σ4 hp ⟨h4R, h4o, h4m, h4A⟩ hP hN4
      have hA1 := bv_le ((List.range p).all fun ℓ => val ts 1 r ℓ)
      have hm4 : ∀ x, x ∈ σ4.mem ↔ Mem2 ts (fun _ _ _ => True) x := by rw [h4m]; exact hm
      refine hach_set (bnd_band' (by simp [h4A]; omega) (bnd_rdV hc hN4 (bnd_const' (by omega))
        (by simp [h4R]; omega) (by simp [hP]; omega) (by simp only [ev_const]; omega) (by simp [h4R]; omega)
        (by simp [hP]; omega)) (by simp [h4A]) (rdV_le_one _ _ _ _) (by omega))
        ⟨by simp [hP], by simp [hN4], ?_⟩
      refine ⟨by simp [h4R], by simp [h4o], by simp [h4m], ?_⟩
      simp only [HSt.set_v, Function.update_apply, Fin.reduceEq, if_false, if_true]
      rw [ev_band', ev_rdV_val hm4 hN4 (by simp [hP]; omega) (fun _ _ => trivial)]
      simp [h4A, h4R, hP, hrl, List.range_succ, List.all_append]
    rintro σ5 ⟨⟨-, h5o, -, h5A⟩, -, -⟩
    have hdec : decideCTL ts = (List.range ts.length).all fun ℓ => val ts 1 r ℓ := by
      simp [decideCTL, hv, root, hrdef]
    have hb1 := bv_le ((List.range ts.length).all fun ℓ => val ts 1 r ℓ)
    refine hach_ite (by simp [h5A]; omega) ?_
    rw [hdec]
    cases hb : (List.range ts.length).all fun ℓ => val ts 1 r ℓ
    · rw [if_neg (by simp [h5A, hb])]; exact hach_out (by simp [h5o])
    · rw [if_pos (by simp [h5A, hb])]; exact hach_out (by simp [h5o])

end CTLP

end PathChecking
