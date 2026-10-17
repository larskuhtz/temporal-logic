module

public import RequestProject.PTime.Sim

/-!
# Programs with polynomially bounded registers and memory run in polynomial time

`polytimeComputable_of_pprog`: if a program of `PTime/Prog.lean` terminates on every input `w`
with output `f w`, while its registers and cursor stay below a polynomial bound `B w`, then
`f` is computable in polynomial time.

The number of goto steps is bounded by counting: the memory only grows, so between two changes
of the memory the remaining part of the state (program counter, input head, registers,
cursor) cannot repeat; and each goto step costs `O(B)` machine steps.
-/

@[expose] public section

namespace PathChecking

namespace PT

open LS

variable {K : ℕ}

section Run

variable {code : List (PGI K)} {N : ℕ} {w : Word} {B : ℕ}

/-- Simulation of a single goto step. -/
lemma sim_step (a : ℕ × PSt K) (ha : a.1 ≤ N) (A : ℕ) (hA : A ≤ B + 1) (hInv : Inv A a.2)
    (hg : PGood w B a.2) (hg' : PGood w B (pstep code w a).2) :
    ∃ A', A' ≤ B + 1 ∧ Inv A' (pstep code w a).2 ∧
      RB (pmachine code N) w (4 * A + 5) (cfgOf code N a.1 a.2 A)
        (cfgOf code N (pstep code w a).1 (pstep code w a).2 A') := by
  obtain ⟨pc, σ⟩ := a
  simp only at ha hInv hg hg' ⊢
  have hpos := hg.1
  unfold pstep at hg' ⊢
  simp only at hg' ⊢
  cases hi : code.getD pc .halt with
  | inc r =>
    rw [hi] at hg'
    simp only [pexec] at hg' ⊢
    have := hg'.2.1 r
    simp only [St.setReg_reg, Function.update_self] at this
    exact sim_inc pc ha σ r hi A hInv hpos this hA
  | dec r =>
    simp only [pexec]
    exact ⟨A, hA, (sim_dec pc ha σ r hi A hInv hpos).1, (sim_dec pc ha σ r hi A hInv hpos).2⟩
  | jz r t =>
    simp only [pexec]
    exact ⟨A, hA, hInv, sim_jz pc ha σ r t hi A hInv hpos⟩
  | jm t =>
    simp only [pexec]
    exact ⟨A, hA, hInv, sim_jm pc ha σ t hi A hInv hpos⟩
  | cr =>
    rw [hi] at hg'
    simp only [pexec] at hg' ⊢
    have := hg'.2.2.1
    simp only at this
    exact ⟨_, (sim_cr pc ha σ hi A hInv hpos (by omega) hA).1,
      (sim_cr pc ha σ hi A hInv hpos (by omega) hA).2⟩
  | cl =>
    simp only [pexec]
    exact ⟨A, hA, (sim_cl pc ha σ hi A hInv hpos).1, (sim_cl pc ha σ hi A hInv hpos).2⟩
  | mset =>
    simp only [pexec]
    have := hg.2.2.1
    exact ⟨_, by omega, (sim_mset pc ha σ hi A hInv hpos).1, (sim_mset pc ha σ hi A hInv hpos).2⟩
  | halt =>
    simp only [pexec]
    exact ⟨A, hA, hInv, (RB.refl _).mono (by omega)⟩
  | jsym s t =>
    have hiF : code.getD (clampPc N pc).val .halt = .jsym s t := by
      rw [clampPc_val ha]; exact hi
    refine ⟨A, hA, hInv, (RB.single ?_).mono (by omega)⟩
    rw [cfgOf, pmachine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hi, pexec, Dir.move, min_eq_left hpos, Function.update_eq_self,
      Option.toList_none, List.append_nil, cfgOf, clampPc_val ha]
    split_ifs <;> rfl
  | left =>
    have hiF : code.getD (clampPc N pc).val .halt = .left := by rw [clampPc_val ha]; exact hi
    refine ⟨A, hA, hInv, (RB.single ?_).mono (by omega)⟩
    rw [cfgOf, pmachine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hi, pexec, Dir.move, Function.update_eq_self,
      Option.toList_none, List.append_nil, cfgOf, clampPc_val ha]
    rw [min_eq_left (by omega)]
    rfl
  | right =>
    have hiF : code.getD (clampPc N pc).val .halt = .right := by rw [clampPc_val ha]; exact hi
    refine ⟨A, hA, hInv, (RB.single ?_).mono (by omega)⟩
    rw [cfgOf, pmachine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hi, pexec, Dir.move, Function.update_eq_self,
      Option.toList_none, List.append_nil, cfgOf, clampPc_val ha]
    rfl
  | out b =>
    have hiF : code.getD (clampPc N pc).val .halt = .out b := by rw [clampPc_val ha]; exact hi
    refine ⟨A, hA, hInv, (RB.single ?_).mono (by omega)⟩
    rw [cfgOf, pmachine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hi, pexec, Dir.move, min_eq_left hpos, Function.update_eq_self,
      cfgOf, clampPc_val ha]
    rfl
  | jmp t =>
    have hiF : code.getD (clampPc N pc).val .halt = .jmp t := by rw [clampPc_val ha]; exact hi
    refine ⟨A, hA, hInv, (RB.single ?_).mono (by omega)⟩
    rw [cfgOf, pmachine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hiF, pexec, Dir.move, min_eq_left hpos, Function.update_eq_self,
      Option.toList_none, List.append_nil, cfgOf]

/-- Simulation of `k` goto steps. -/
lemma sim_iter (hinv : ∀ a : ℕ × PSt K, a.1 ≤ N → (pstep code w a).1 ≤ N) :
    ∀ k (a : ℕ × PSt K) A, a.1 ≤ N → A ≤ B + 1 → Inv A a.2 →
      (∀ i ≤ k, PGood w B ((pstep code w)^[i] a).2) →
      ∃ A', A' ≤ B + 1 ∧ RB (pmachine code N) w (k * (4 * B + 9)) (cfgOf code N a.1 a.2 A)
        (cfgOf code N ((pstep code w)^[k] a).1 ((pstep code w)^[k] a).2 A') := by
  intro k
  induction k with
  | zero =>
    intro a A _ hA _ _
    exact ⟨A, hA, by simpa using RB.refl (M := pmachine code N) (w := w) (cfgOf code N a.1 a.2 A)⟩
  | succ k ih =>
    intro a A ha hA hI hg
    obtain ⟨A₁, hA₁, hI₁, hr₁⟩ := sim_step a ha A hA hI (hg 0 (by omega)) (hg 1 (by omega))
    obtain ⟨A₂, hA₂, hr₂⟩ := ih (pstep code w a) A₁ (hinv a ha) hA₁ hI₁
      (fun i hi => by have := hg (i + 1) (by omega); rwa [Function.iterate_succ_apply] at this)
    refine ⟨A₂, hA₂, ?_⟩
    rw [Function.iterate_succ_apply]
    exact (hr₁.trans hr₂).mono (by nlinarith)

end Run

/-! ## Counting goto steps -/

section Count

variable {code : List (PGI K)} {w : Word}

/-- The part of a goto state that determines its future. -/
def pkey (a : ℕ × PSt K) : ℕ × ℕ × (Fin K → ℕ) × ℕ × Finset ℕ :=
  (a.1, a.2.base.pos, a.2.base.reg, a.2.cur, a.2.mem)

lemma pkey_step {a b : ℕ × PSt K} (h : pkey a = pkey b) :
    pkey (pstep code w a) = pkey (pstep code w b) := by
  obtain ⟨pc, ⟨p, ρ, o⟩, c, m⟩ := a
  obtain ⟨pc', ⟨p', ρ', o'⟩, c', m'⟩ := b
  simp only [pkey, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  unfold pstep
  cases code.getD pc .halt <;> simp [pexec, pkey, St.setReg]

lemma pkey_iter {a b : ℕ × PSt K} (h : pkey a = pkey b) (k : ℕ) :
    pkey ((pstep code w)^[k] a) = pkey ((pstep code w)^[k] b) := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; exact pkey_step ih

lemma mem_step (a : ℕ × PSt K) : a.2.mem ⊆ (pstep code w a).2.mem := by
  unfold pstep
  cases code.getD a.1 .halt <;> simp [pexec, Finset.subset_insert]

lemma mem_iter_mono (a : ℕ × PSt K) {i j : ℕ} (hij : i ≤ j) :
    ((pstep code w)^[i] a).2.mem ⊆ ((pstep code w)^[j] a).2.mem := by
  induction hij with
  | refl => exact Finset.Subset.refl _
  | step _ ih => rw [Function.iterate_succ_apply']; exact ih.trans (mem_step _)

/-- Bound on the first time the program counter reaches `L`, by counting states. -/
lemma halt_count (L B : ℕ) (a : ℕ × PSt K) (k : ℕ)
    (hk : ((pstep code w)^[k] a).1 = L) (hmin : ∀ i < k, ((pstep code w)^[i] a).1 ≠ L)
    (hpc : ∀ i ≤ k, ((pstep code w)^[i] a).1 ≤ L)
    (hg : ∀ i ≤ k, PGood w B ((pstep code w)^[i] a).2) :
    k + 1 ≤ (L + 1) * (w.length + 2) * (B + 1) ^ K * (B + 1) * (B + 2) := by
  have hcard : ∀ i ≤ k, ((pstep code w)^[i] a).2.mem.card ≤ B + 1 := by
    intro i hi
    have hsub : ((pstep code w)^[i] a).2.mem ⊆ Finset.range (B + 1) := by
      intro x hx; have := (hg i hi).2.2.2 x hx; simp; omega
    simpa using Finset.card_le_card hsub
  let F : Fin (k + 1) → Fin (L + 1) × Fin (w.length + 2) × (Fin K → Fin (B + 1)) ×
      Fin (B + 1) × Fin (B + 2) := fun i =>
    (⟨((pstep code w)^[i] a).1, by have := hpc i (by omega); omega⟩,
     ⟨((pstep code w)^[i] a).2.base.pos, by have := (hg i (by omega)).1; omega⟩,
     fun r => ⟨((pstep code w)^[i] a).2.base.reg r, by have := (hg i (by omega)).2.1 r; omega⟩,
     ⟨((pstep code w)^[i] a).2.cur, by have := (hg i (by omega)).2.2.1; omega⟩,
     ⟨((pstep code w)^[i] a).2.mem.card, by have := hcard i (by omega); omega⟩)
  have hF : Function.Injective F := by
    intro x y hxy
    simp only [F, Prod.mk.injEq, Fin.mk.injEq] at hxy
    obtain ⟨h1, h2, h3, h4, h5⟩ := hxy
    have hreg : ((pstep code w)^[x] a).2.base.reg = ((pstep code w)^[y] a).2.base.reg := by
      funext r; have := congrFun h3 r; simpa using this
    by_contra hne
    have hne' : x.val ≠ y.val := fun h => hne (Fin.ext h)
    -- wlog x < y
    have key : ∀ i j : ℕ, i < j → j ≤ k → ((pstep code w)^[i] a).1 = ((pstep code w)^[j] a).1 → ((pstep code w)^[i] a).2.base.pos = ((pstep code w)^[j] a).2.base.pos →
        ((pstep code w)^[i] a).2.base.reg = ((pstep code w)^[j] a).2.base.reg → ((pstep code w)^[i] a).2.cur = ((pstep code w)^[j] a).2.cur →
        ((pstep code w)^[i] a).2.mem.card = ((pstep code w)^[j] a).2.mem.card → False := by
      intro i j hij hjk e1 e2 e3 e4 e5
      have hm : ((pstep code w)^[i] a).2.mem = ((pstep code w)^[j] a).2.mem :=
        Finset.eq_of_subset_of_card_le (mem_iter_mono a hij.le) (by omega)
      have hkey : pkey ((pstep code w)^[i] a) = pkey ((pstep code w)^[j] a) := by
        simp only [pkey, e1, e2, e3, e4, hm]
      have := pkey_iter (code := code) (w := w) hkey (k - j)
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at this
      rw [show k - j + j = k by omega] at this
      have hpc' := congrArg Prod.fst this
      simp only [pkey] at hpc'
      exact hmin (k - j + i) (by omega) (by rw [hpc']; exact hk)
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact key x y h (by omega) h1 h2 hreg h4 h5
    · exact key y x h (by omega) h1.symm h2.symm hreg.symm h4.symm h5.symm
  have := Fintype.card_le_of_injective F hF
  simpa [Fintype.card_prod, Fintype.card_fun, mul_assoc] using this

end Count

/-! ## Main theorem -/

lemma psteps_iter {code : List (PGI K)} {w : Word} {B : ℕ} {a b : ℕ × PSt K}
    (h : PSteps code w B a b) (ha : PGood w B a.2) :
    ∃ k, (pstep code w)^[k] a = b ∧ ∀ i ≤ k, PGood w B ((pstep code w)^[i] a).2 := by
  induction h with
  | refl =>
    refine ⟨0, rfl, fun i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    exact ha
  | tail _ hst ih =>
    obtain ⟨k, hk, hg⟩ := ih
    obtain ⟨hst, hgc⟩ := hst
    refine ⟨k + 1, by rw [Function.iterate_succ_apply', hk, hst], fun i hi => ?_⟩
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · exact hg i (by omega)
    · obtain rfl : i = k + 1 := by omega
      rw [Function.iterate_succ_apply', hk, hst]; exact hgc

/-- Polynomial bound for the running time. -/
lemma time_poly (L K c n B k : ℕ) (hB : B ≤ c * (n + 1) ^ c)
    (hk : k + 1 ≤ (L + 1) * (n + 2) * (B + 1) ^ K * (B + 1) * (B + 2)) :
    1 + k * (4 * B + 9) ≤ (5 * (L + 1) * (c + 2) ^ (K + 4) + 1 + (c + 1) * (K + 4)) *
      (n + 1) ^ (5 * (L + 1) * (c + 2) ^ (K + 4) + 1 + (c + 1) * (K + 4)) := by
  set m := n + 1 with hmdef
  have hm : 1 ≤ m := by omega
  set E := (c + 2) * m ^ (c + 1) with hE
  have hmc : 1 ≤ m ^ c := Nat.one_le_pow _ _ hm
  have hmc1 : m ^ (c + 1) = m ^ c * m := pow_succ _ _
  have hB2 : B + 2 ≤ E := by
    rw [hE, hmc1]
    have : c * m ^ c ≤ c * (m ^ c * m) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hm)
    nlinarith
  have hn2 : n + 2 ≤ E := by
    rw [hE, hmc1]
    have : m ≤ m ^ c * m := Nat.le_mul_of_pos_left _ hmc
    have : 2 * m ≤ (c + 2) * (m ^ c * m) := Nat.mul_le_mul (by omega) this
    omega
  have hE1 : 1 ≤ E := by omega
  have h1 : (L + 1) * (n + 2) * (B + 1) ^ K * (B + 1) * (B + 2) ≤
      (L + 1) * E * E ^ K * E * E := by
    gcongr <;> omega
  have h2 : 4 * B + 9 ≤ 5 * E := by omega
  have h3 : 1 + k * (4 * B + 9) ≤ 1 + (L + 1) * E * E ^ K * E * E * (5 * E) := by
    have := Nat.mul_le_mul (show k ≤ (L + 1) * E * E ^ K * E * E by omega) h2
    omega
  have h4 : (L + 1) * E * E ^ K * E * E * (5 * E) = 5 * (L + 1) * E ^ (K + 4) := by ring
  have h5 : E ^ (K + 4) = (c + 2) ^ (K + 4) * m ^ ((c + 1) * (K + 4)) := by
    rw [hE, mul_pow, ← pow_mul]
  set C := 5 * (L + 1) * (c + 2) ^ (K + 4) + 1 + (c + 1) * (K + 4)
  have h6 : m ^ ((c + 1) * (K + 4)) ≤ m ^ C := Nat.pow_le_pow_right hm (by omega)
  have h7 : 1 ≤ m ^ ((c + 1) * (K + 4)) := Nat.one_le_pow _ _ hm
  calc 1 + k * (4 * B + 9) ≤ 1 + 5 * (L + 1) * ((c + 2) ^ (K + 4) * m ^ ((c + 1) * (K + 4))) := by
        rw [← h5, ← h4]; exact h3
    _ ≤ (5 * (L + 1) * (c + 2) ^ (K + 4) + 1) * m ^ ((c + 1) * (K + 4)) := by nlinarith
    _ ≤ C * m ^ C := Nat.mul_le_mul (by omega) h6

/-- **Programs with polynomially bounded registers and memory compute polynomial-time
functions.** -/
theorem polytimeComputable_of_pprog (P : PStmt K) (f : Word → Word) (B : Word → ℕ) (c : ℕ)
    (hB : ∀ w, B w ≤ c * (w.length + 1) ^ c)
    (hP : ∀ w, ∃ σ', PEval w (B w) P (PSt.init K) σ' ∧ σ'.base.out = f w) :
    PolytimeComputable f := by
  set L := pclen P
  set M := pmachine P.code L
  refine ⟨M, 5 * (L + 1) * (c + 2) ^ (K + 4) + 1 + (c + 1) * (K + 4), fun w => ?_⟩
  obtain ⟨σ', hev, hout⟩ := hP w
  have hg0 : PGood w (B w) (PSt.init K) :=
    ⟨by simp [PSt.init, St.init], fun r => by simp [PSt.init, St.init], by simp [PSt.init],
      by simp [PSt.init]⟩
  obtain ⟨k, hk, hgk⟩ := psteps_iter (pcode_sim hev hg0) (by simpa using hg0)
  set a0 : ℕ × PSt K := (0, PSt.init K)
  have hinv : ∀ a : ℕ × PSt K, a.1 ≤ L → (pstep P.code w a).1 ≤ L :=
    fun a ha => pstep_pc_le P w a ha
  have hpcle : ∀ i, ((pstep P.code w)^[i] a0).1 ≤ L := by
    intro i; induction i with
    | zero => simp [a0]
    | succ i ih => rw [Function.iterate_succ_apply']; exact hinv _ ih
  have hfix : ∀ b : ℕ × PSt K, b.1 = L → pstep P.code w b = b := by
    intro b hb; unfold pstep; rw [hb, pcode_halt]; rfl
  have hex : ∃ i, ((pstep P.code w)^[i] a0).1 = L := ⟨k, by rw [hk]⟩
  classical
  set k0 := Nat.find hex
  have hk0 : ((pstep P.code w)^[k0] a0).1 = L := Nat.find_spec hex
  have hk0k : k0 ≤ k := Nat.find_min' hex (by rw [hk])
  have hmin : ∀ i < k0, ((pstep P.code w)^[i] a0).1 ≠ L := fun i hi => Nat.find_min hex hi
  have hstay : ∀ j, (pstep P.code w)^[k0 + j] a0 = (pstep P.code w)^[k0] a0 := by
    intro j; induction j with
    | zero => rfl
    | succ j ih =>
      rw [← add_assoc, Function.iterate_succ_apply', ih, hfix _ hk0]
  have hfinal : (pstep P.code w)^[k0] a0 = (L, σ') := by
    rw [← hstay (k - k0), show k0 + (k - k0) = k by omega, hk]
  have hcount := halt_count L (B w) a0 k0 hk0 hmin (fun i _ => hpcle i)
    (fun i hi => hgk i (by omega))
  obtain ⟨A', -, hr⟩ := sim_iter (code := P.code) (N := L) (w := w) (B := B w) hinv k0 a0 0
    (by simp [a0]) (by omega) ⟨fun r => by simp [a0, PSt.init, St.init],
      by simp [a0, PSt.init], by simp [a0, PSt.init]⟩ (fun i hi => hgk i (by omega))
  rw [hfinal] at hr
  have hinit : M.step w M.init = cfgOf P.code L a0.1 a0.2 0 := by
    have hinit0 : M.init = ⟨((0 : Fin (L + 1)), Ph.init), 0, fun _ => blankCell, 0, []⟩ := rfl
    rw [hinit0, pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)), delta_init]
    simp only [Dir.move, min_eq_left (Nat.zero_le _), Option.toList_none, List.append_nil,
      cfgOf, a0, PSt.init, St.init]
    congr 1
    funext p
    by_cases hp : p = 0
    · subst hp; simp [tapeOf]
    · rw [Function.update_of_ne hp]
      simp [tapeOf, hp, blankCell, gOf]
  obtain ⟨t, ht, e⟩ := RB.head hinit hr
  refine ⟨t, ?_, ?_, ?_⟩
  · have := time_poly L K c w.length (B w) k0 (hB w) hcount
    omega
  · rw [TM.run, e]
    show haltQ P.code L (clampPc L L, Ph.bnd) = true
    have hN : P.code.getD L .halt = .halt := pcode_halt P
    simp only [haltQ, clampPc_val le_rfl, hN]
  · rw [TM.run, e]; simp [cfgOf, hout]

end PT

end PathChecking
