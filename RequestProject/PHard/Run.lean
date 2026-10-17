module

public import RequestProject.PHard.Gate
public import RequestProject.Logspace.Machine

/-!
# The logspace program producing the tableau circuit

`tabProg M c` computes the parameters of the tableau circuit and then outputs its gates one
by one (`ach_tabProg`); the register values stay polynomial in the input length
(`Nb_lt_pow`). Hence the tableau reduction is logspace computable
(`tabRed_logspaceComputable'`).
-/

@[expose] public section

namespace PathChecking

namespace PHardness

open Classical MCVPReduction LS
open scoped LS

noncomputable section

variable (M : TM) (c : ℕ) (w : Word)

/-- The reduction map: the binary encoding of the tableau circuit. -/
def tabRed (M : TM) (c : ℕ) (w : Word) : Word := encodeCircuit (tabCircuit M c w)

/-! ## Polynomial bound on the register values -/

lemma Nb_le_poly (n : ℕ) :
    Nb M c n ≤ 6 * (c + 1) * (2 * (c + 1) * nZ M) ^ 3 * (n + 1) ^ (4 * c + 4) := by
  have hY : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (by omega)
  set Y := (n + 1) ^ c with hYdef
  set Z := n + 1 with hZ
  have hz := nZ_pos M
  set A := 2 * (c + 1) * nZ M with hA
  have hT : Tb c n + 1 ≤ (c + 1) * Y := by unfold Tb; rw [← hYdef]; nlinarith
  have hNE : NE M c n ≤ A * (Z * Y) := by
    unfold NE
    calc (n + 2) * (Tb c n + 1) * nZ M ≤ (2 * Z) * ((c + 1) * Y) * nZ M := by gcongr; omega
      _ = A * (Z * Y) := by rw [hA]; ring
  have hP : 1 ≤ Z * Y := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hA1 : 1 ≤ A := by rw [hA]; have := Nat.mul_le_mul (show 1 ≤ 2 * (c+1) by omega) hz; simpa using this
  have hS : Sb M c n ≤ 3 * A ^ 2 * (Z * Y) ^ 2 := by
    unfold Sb
    have h1 : NE M c n * NE M c n ≤ (A * (Z * Y)) * (A * (Z * Y)) := Nat.mul_le_mul hNE hNE
    have h2 : 1 ≤ (A * (Z * Y)) * (A * (Z * Y)) := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have hL : (Tb c n + 1) * NE M c n + 1 ≤ 2 * (c + 1) * A * (Z * Y) ^ 2 := by
    have h1 : (Tb c n + 1) * NE M c n ≤ ((c + 1) * Y) * (A * (Z * Y)) := Nat.mul_le_mul hT hNE
    have h2 : ((c + 1) * Y) * (A * (Z * Y)) ≤ (c + 1) * A * (Z * Y) ^ 2 := by
      have : Y ≤ Z * Y := Nat.le_mul_of_pos_left _ (by omega)
      calc ((c + 1) * Y) * (A * (Z * Y)) = (c + 1) * A * (Y * (Z * Y)) := by ring
        _ ≤ (c + 1) * A * ((Z * Y) * (Z * Y)) := by gcongr
        _ = _ := by ring
    have h3 : 1 ≤ (c + 1) * A * (Z * Y) ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have hZY : (Z * Y) ^ 4 = (n + 1) ^ (4 * c + 4) := by
    rw [hYdef, hZ, ← pow_succ', ← pow_mul]; ring_nf
  calc Nb M c n = ((Tb c n + 1) * NE M c n + 1) * Sb M c n := rfl
    _ ≤ (2 * (c + 1) * A * (Z * Y) ^ 2) * (3 * A ^ 2 * (Z * Y) ^ 2) := Nat.mul_le_mul hL hS
    _ = 6 * (c + 1) * A ^ 3 * (Z * Y) ^ 4 := by ring
    _ = _ := by rw [hZY]


lemma Nb_lt_pow (n : ℕ) :
    Nb M c n < 2 ^ ((6 * (c + 1) * (2 * (c + 1) * nZ M) ^ 3 + 4 * c + 5) * (Nat.log 2 n + 1)) := by
  have h := Nb_le_poly M c n
  set K := 6 * (c + 1) * (2 * (c + 1) * nZ M) ^ 3
  set L := Nat.log 2 n + 1
  have hL : 1 ≤ L := Nat.succ_pos _
  have hn : n + 1 ≤ 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) n
  have hK : K ≤ 2 ^ (K * L) := (Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (by omega)))
  have h1 : (n + 1) ^ (4 * c + 4) ≤ 2 ^ (L * (4 * c + 4)) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hn _
  have h2 : Nb M c n ≤ 2 ^ ((K + 4 * c + 4) * L) := by
    calc Nb M c n ≤ K * (n + 1) ^ (4 * c + 4) := h
      _ ≤ 2 ^ (K * L) * 2 ^ (L * (4 * c + 4)) := Nat.mul_le_mul hK h1
      _ = 2 ^ ((K + 4 * c + 4) * L) := by rw [← pow_add]; ring_nf
  have h3 : 2 ^ ((K + 4 * c + 4) * L) < 2 ^ ((K + 4 * c + 5) * L) :=
    Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  omega


/-! ## Initialisation -/

/-- `r₁ := (n + 1)^c`. -/
def powList : List (ℕ × AE) :=
  (1, cst 1) :: List.replicate c (1, .mul (rg 1) (.add (rg 0) (cst 1)))

/-- The remaining parameters. -/
def paramList : List (ℕ × AE) :=
  [(1, .mul (cst c) (rg 1)),
   (7, .mul (.add (rg 1) (cst 1)) (cst (nZ M))),
   (2, .mul (.add (rg 0) (cst 2)) (rg 7)),
   (3, .add (.mul (.mul (cst 2) (rg 2)) (rg 2)) (cst 1)),
   (4, .mul (.add (.mul (.add (rg 1) (cst 1)) (rg 2)) (cst 1)) (rg 3)),
   (5, cst 0),
   (6, rg 4)]

/-- **The tableau program.** -/
def tabProg : Stmt 64 :=
  countLen ⨟ assignAll (powList c) ⨟ assignAll (paramList M c) ⨟ forLoop (body M)

lemma pow_le_Bd {n j : ℕ} (hj : j ≤ c) : (n + 1) ^ j ≤ Bd M c n := by
  have h1 : (n + 1) ^ j ≤ Tb c n + 1 := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at hj; subst hj; simp
    · have : (n + 1) ^ j ≤ (n + 1) ^ c := Nat.pow_le_pow_right (by omega) hj
      have : (n + 1) ^ c ≤ c * (n + 1) ^ c := Nat.le_mul_of_pos_left _ h0
      unfold Tb; omega
  have := T_le_NE M c n
  have := NE_le_Bd M c n
  omega

lemma ach_powRep {n : ℕ} : ∀ (k j : ℕ) (σ : St 64) (Q : St 64 → Prop), σ.reg (R 0) = n →
    σ.reg (R 1) = (n + 1) ^ j → j + k ≤ c →
    (∀ τ : St 64, τ.out = σ.out → τ.pos = σ.pos →
      (∀ x : Fin 64, x.val < 30 → x ≠ R 1 → τ.reg x = σ.reg x) →
      τ.reg (R 1) = (n + 1) ^ (j + k) → Q τ) →
    Ach w (Bd M c n) (assignAll (List.replicate k (1, .mul (rg 1) (.add (rg 0) (cst 1))))) σ Q
  | 0, j, σ, Q, _, h1, _, h => ach_skip (h σ rfl rfl (fun _ _ _ => rfl) (by simpa using h1))
  | k + 1, j, σ, Q, h0, h1, hjk, h => by
    simp only [List.replicate_succ, assignAll]
    have hb1 := pow_le_Bd M c (n := n) (j := j + 1) (by omega)
    have hb0 := pow_le_Bd M c (n := n) (j := 1) (by omega)
    have hbj := pow_le_Bd M c (n := n) (j := j) (by omega)
    simp only [pow_one] at hb0
    refine ach_seq (ach_comp _ 1 30 σ _ (by omega) (by simp [AE.RL]) (by simp [AE.ht])
      (by simp only [AE.Bnd, AE.eval, h0, h1]; rw [← pow_succ]; omega) ?_)
    intro τ ho hp hv hk
    simp only [AE.eval, h0, h1, ← pow_succ] at hv
    have h0' : τ.reg (R 0) = n := by
      rw [hk _ (by rw [R_val (by omega)]; omega) (R_ne (by omega) (by omega) (by omega)), h0]
    refine ach_powRep k (j + 1) τ Q h0' hv (by omega) ?_
    intro τ' ho' hp' hk' hv'
    refine h τ' (ho'.trans ho) (hp'.trans hp) (fun x hx hx1 => (hk' x hx hx1).trans (hk x hx hx1))
      (by rw [hv']; ring_nf)

lemma param_vals {n : ℕ} {ρ : Fin 64 → ℕ} (h0 : ρ (R 0) = n) (h1 : ρ (R 1) = (n + 1) ^ c) :
    let ρ' := updAll (paramList M c) ρ
    ρ' (R 0) = n ∧ ρ' (R 1) = Tb c n ∧ ρ' (R 2) = NE M c n ∧ ρ' (R 3) = Sb M c n ∧
    ρ' (R 4) = Nb M c n ∧ ρ' (R 5) = 0 ∧ ρ' (R 6) = Nb M c n ∧
    ρ' (R 7) = (Tb c n + 1) * nZ M := by
  simp only [paramList, updAll, AE.eval, Function.update_apply]
  simp [R] at h0 h1
  simp [R, h0, h1, Tb, NE_eq, Sb, Nb]

lemma param_ok {n : ℕ} {ρ : Fin 64 → ℕ} (h0 : ρ (R 0) = n) (h1 : ρ (R 1) = (n + 1) ^ c) :
    AllOK (Bd M c n) (paramList M c) ρ := by
  have hc := pow_le_Bd M c (n := n) (j := c) le_rfl
  have hT := T_le_NE M c n
  have hNB := NE_le_Bd M c n
  have hzN := nZ_le_NE M c n
  have hnN := n_le_NE M c n
  have hJN := JZ_le_NE M c n
  have hSB := Sb_le_Nb M c n
  have hBd : Bd M c n = Nb M c n := rfl
  have hcT : c ≤ Tb c n := by
    unfold Tb; exact Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))
  have hNS : 2 * NE M c n ≤ Sb M c n := by
    unfold Sb; have := NE_pos M c n; nlinarith
  have hTS : (Tb c n + 1) * NE M c n + 1 ≤ Nb M c n := by
    unfold Nb; exact Nat.le_mul_of_pos_right _ (Sb_pos M c n)
  simp [R] at h0 h1
  simp only [paramList, AllOK, AE.Bnd, AE.eval, AE.RL, AE.ht, Function.update_apply]
  simp [R, h0, h1]
  rw [show c * (n + 1) ^ c = Tb c n from rfl, ← NE_eq]
  have e1 : 2 * NE M c n * NE M c n + 1 = Sb M c n := rfl
  have e2 : ((Tb c n + 1) * NE M c n + 1) * Sb M c n = Nb M c n := rfl
  rw [e1, e2]
  repeat' apply And.intro
  all_goals omega

/-- Invariant of the main loop. -/
def LoopInv (j : ℕ) (τ : St 64) : Prop :=
  τ.out = encodeToks ((List.range j).flatMap fun k => (gateFn M c w k).toks) ∧
    τ.reg (R 0) = w.length ∧ τ.reg (R 1) = Tb c w.length ∧ τ.reg (R 2) = NE M c w.length ∧
    τ.reg (R 3) = Sb M c w.length ∧ τ.reg (R 4) = Nb M c w.length ∧
    τ.reg (R 7) = (Tb c w.length + 1) * nZ M

lemma ach_mainLoop (τ : St 64) (hP : LoopInv M c w 0 τ) (h5 : τ.reg (R 5) = 0)
    (h6 : τ.reg (R 6) = Nb M c w.length) :
    Ach w (Bd M c w.length) (forLoop (body M)) τ (fun τ => τ.out = tabRed M c w) := by
  refine ach_forLoop (body M) (LoopInv M c w) _ (Nb M c w.length) τ hP h5 h6 le_rfl ?_ ?_
  · intro j hj τ hP h5 h6
    obtain ⟨ho, h0, h1, h2, h3, h4, h7⟩ := hP
    refine (ach_body M c w τ ⟨h0, h1, h2, h3, h4, h5, h7⟩ hj).mono ?_
    rintro τ' ⟨ho', hr'⟩
    have e : ∀ i, i < 8 → τ'.reg (R i) = τ.reg (R i) := fun i hi => hr' _ (by rw [R_val (by omega)]; omega)
    have s : ∀ i v v', i ≠ 5 → i ≠ 6 → i < 8 →
        ((τ'.setReg (R 5) v).setReg (R 6) v').reg (R i) = τ.reg (R i) := by
      intro i v v' h5 h6 hi
      simp only [St.setReg_reg]
      rw [Function.update_of_ne (R_ne (by omega) (by omega) h6),
        Function.update_of_ne (R_ne (by omega) (by omega) h5), e i hi]
    refine ⟨by rw [e 5 (by omega), h5], by rw [e 6 (by omega), h6], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [St.setReg_out]
      rw [ho', ho, List.range_succ, List.flatMap_append, encodeToks_append]
      simp
    · rw [s 0 _ _ (by omega) (by omega) (by omega), h0]
    · rw [s 1 _ _ (by omega) (by omega) (by omega), h1]
    · rw [s 2 _ _ (by omega) (by omega) (by omega), h2]
    · rw [s 3 _ _ (by omega) (by omega) (by omega), h3]
    · rw [s 4 _ _ (by omega) (by omega) (by omega), h4]
    · rw [s 7 _ _ (by omega) (by omega) (by omega), h7]
  · intro τ hP
    rw [hP.1, tabRed, encodeCircuit, tabCircuit, List.flatMap_map]

theorem ach_tabProg :
    Ach w (Bd M c w.length) (tabProg M c) (St.init 64) (fun τ => τ.out = tabRed M c w) := by
  have hnB : w.length ≤ Bd M c w.length := by
    have := n_le_NE M c w.length; have := NE_le_Bd M c w.length; omega
  unfold tabProg
  refine ach_seq (ach_countLen _ _ hnB ?_)
  intro τ0 ho0 h00 _
  simp only [powList, assignAll]
  refine ach_seq (ach_seq (ach_comp (cst 1) 1 30 τ0 _ (by omega) trivial (by simp [AE.ht])
    (by have := pow_le_Bd M c (n := w.length) (j := 0) (Nat.zero_le _); simpa [AE.Bnd] using this)
    ?_))
  intro τ1 ho1 _ hv1 hk1
  have h10 : τ1.reg (R 0) = w.length := by
    rw [hk1 _ (by rw [R_val (by omega)]; omega) (R_ne (by omega) (by omega) (by omega)), h00]
  refine ach_powRep M c w c 0 τ1 _ h10 (by simpa [AE.eval] using hv1) (by omega) ?_
  intro τ2 ho2 _ hk2 hv2
  have h20 : τ2.reg (R 0) = w.length := by
    rw [hk2 _ (by rw [R_val (by omega)]; omega) (R_ne (by omega) (by omega) (by omega)), h10]
  rw [zero_add] at hv2
  refine ach_seq (ach_assignAll _ τ2 _ (param_ok M c h20 hv2) ?_)
  intro τ3 ho3 _ hv3
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := param_vals M c h20 hv2
  have r : ∀ i, i < 30 → τ3.reg (R i) = updAll (paramList M c) τ2.reg (R i) :=
    fun i hi => hv3 _ (by rw [R_val (by omega)]; omega)
  refine ach_mainLoop M c w τ3 ⟨?_, by rw [r 0 (by omega), v0], by rw [r 1 (by omega), v1],
    by rw [r 2 (by omega), v2], by rw [r 3 (by omega), v3], by rw [r 4 (by omega), v4],
    by rw [r 7 (by omega), v7]⟩ (by rw [r 5 (by omega), v5]) (by rw [r 6 (by omega), v6])
  rw [ho3, ho2, ho1, ho0]
  simp [St.init, encodeToks]

theorem tabRed_logspaceComputable' : LogspaceComputable (tabRed M c) := by
  refine logspaceComputable_of_prog (tabProg M c) (tabRed M c) (fun w => Bd M c w.length)
    (6 * (c + 1) * (2 * (c + 1) * nZ M) ^ 3 + 4 * c + 5) (fun w => Nb_lt_pow M c w.length) ?_
  intro w
  obtain ⟨σ', h1, h2⟩ := ach_tabProg M c w
  exact ⟨σ', h1, h2⟩

end

end PHardness

end PathChecking
