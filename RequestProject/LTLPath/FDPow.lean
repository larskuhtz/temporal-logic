module

public import RequestProject.LTLPath.FDTok

/-!
# Capped powers of two

`cp2 r L` is `2 ^ r` if `2 ^ r ≤ L` and `L + 1` otherwise; for `k < L` it can replace `2 ^ r` in
divisibility and division (`dvd_cp2`, `div_cp2`).  It is computed by a bounded search for the
power of two with exactly `r` smaller powers of two (`den_cp2`).
-/

@[expose] public section

namespace PathChecking

namespace FD

open FE LL

/-- Powers of two. -/
def isP2 (m : ℕ) : Prop := m ≠ 0 ∧ ∀ d ≤ m, m % d = 0 → d % 2 = 1 → d = 1

lemma isP2_iff {m : ℕ} : isP2 m ↔ ∃ e, m = 2 ^ e := by
  constructor
  · rintro ⟨h0, h⟩
    obtain ⟨e, o, ho, rfl⟩ := Nat.exists_eq_two_pow_mul_odd h0
    have hpos : 0 < o := ho.pos
    have := h o (Nat.le_mul_of_pos_left _ (by positivity))
      (Nat.mul_mod_left _ _) (Nat.odd_iff.1 ho)
    exact ⟨e, by rw [this, mul_one]⟩
  · rintro ⟨e, rfl⟩
    refine ⟨by positivity, fun d _ hd hodd => ?_⟩
    obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Nat.dvd_of_mod_eq_zero hd)
    rcases k with _ | k
    · rfl
    · rw [pow_succ, Nat.mul_mod_left] at hodd; omega

open Classical in
/-- Number of powers of two below `m`. -/
noncomputable def cntP2 (m : ℕ) : ℕ := (List.range m).countP fun j => decide (isP2 j)

lemma cntP2_pow (e : ℕ) : cntP2 (2 ^ e) = e := by
  classical
  have key : ∀ m n, cntP2 (m + n) = cntP2 m + (List.range n).countP fun j => decide (isP2 (m + j)) := by
    intro m n
    unfold cntP2
    rw [List.range_add, List.countP_append, List.countP_map]
    rfl
  induction e with
  | zero =>
    unfold cntP2
    simp [isP2]
  | succ e ih =>
    rw [pow_succ, mul_two, key, ih]
    congr 1
    obtain ⟨n, hn⟩ : ∃ n, 2 ^ e = n + 1 := ⟨2 ^ e - 1, by have := Nat.one_le_two_pow (n := e); omega⟩
    rw [hn, List.range_succ_eq_map, List.countP_cons, List.countP_map]
    have h1 : decide (isP2 (n + 1 + 0)) = true := by
      simp only [Nat.add_zero, decide_eq_true_eq]; exact isP2_iff.2 ⟨e, hn.symm⟩
    rw [if_pos h1, List.countP_eq_zero.2]
    intro j hj
    simp only [List.mem_range] at hj
    simp only [Function.comp, decide_eq_true_eq]
    rintro hp
    obtain ⟨a, ha⟩ := isP2_iff.1 hp
    have lo : 2 ^ e < 2 ^ a := by omega
    have hi : 2 ^ a < 2 ^ (e + 1) := by rw [pow_succ]; omega
    rw [Nat.pow_lt_pow_iff_right (by norm_num)] at lo hi
    omega

/-- Capped power of two. -/
def cp2 (r L : ℕ) : ℕ := if 2 ^ r ≤ L then 2 ^ r else L + 1

lemma cp2_findF (r L : ℕ) :
    findF (L + 2) (fun m => bv ((isP2 m ∧ cntP2 m = r) ∨ m = L + 1)) = cp2 r L := by
  unfold cp2
  split_ifs with h
  · refine findF_eq_of_spec (by omega) (fun _ => by
      simp only [ne_eq, bv_eq_zero, not_not]; exact Or.inl ⟨isP2_iff.2 ⟨r, rfl⟩, cntP2_pow r⟩)
      (fun j hj => ?_)
    simp only [bv_eq_zero, not_or, not_and]
    refine ⟨fun hp hc => ?_, by omega⟩
    obtain ⟨a, rfl⟩ := isP2_iff.1 hp
    rw [cntP2_pow] at hc; subst hc; omega
  · refine findF_eq_of_spec (by omega) (fun _ => by simp) (fun j hj => ?_)
    simp only [bv_eq_zero, not_or, not_and]
    refine ⟨fun hp hc => ?_, by omega⟩
    obtain ⟨a, rfl⟩ := isP2_iff.1 hp
    rw [cntP2_pow] at hc; subst hc; omega

lemma dvd_cp2 {r L k : ℕ} (hk : k < L) : 2 ^ r ∣ k ↔ k % cp2 r L = 0 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  unfold cp2
  split_ifs with h
  · rfl
  · rw [Nat.mod_eq_of_lt (show k < 2 ^ r by omega), Nat.mod_eq_of_lt (show k < L + 1 by omega)]

lemma div_cp2 {r L k : ℕ} (hk : k < L) : k / 2 ^ r = k / cp2 r L := by
  unfold cp2
  split_ifs with h
  · rfl
  · rw [Nat.div_eq_of_lt (show k < 2 ^ r by omega), Nat.div_eq_of_lt (show k < L + 1 by omega)]

/-! ## Terms -/

variable {x : Word} {Γ : Ctx}

/-- Power-of-two test. -/
def isP2T (m : T) : T :=
  andT (neT m (cT 0)) (allT (addT m (cT 1)) fun d =>
    orT (notT (andT (eqT (modT m d) (cT 0)) (eqT (modT d (cT 2)) (cT 1)))) (eqT d (cT 1)))

/-- Number of powers of two below `m`. -/
def cntP2T (m : T) : T := countT m fun j => isP2T j

/-- Capped power of two. -/
def cp2T (r L : T) : T :=
  findT (addT L (cT 2)) fun m => orT (andT (isP2T m) (eqT (cntP2T m) r)) (eqT m (addT L (cT 1)))

lemma den_isP2 {m : T} {M : ℕ} (hm : Den x Γ m M) : Den x Γ (isP2T m) (bv (isP2 M)) := by
  refine (den_and (den_ne hm (den_c 0)) (den_all (P := fun d => ¬ (M % d = 0 ∧ d % 2 = 1) ∨ d = 1)
    (body := fun d => orT (notT (andT (eqT (modT m d) (cT 0)) (eqT (modT d (cT 2)) (cT 1))))
      (eqT d (cT 1)))
    (den_add hm (den_c 1)) fun k i _ => ?_)).of_eq ?_
  · have hv : Den x ((k, i) :: Γ) (varT k) i := den_var0
    exact den_or (den_not (den_and (den_eq' (den_mod (hm.cons _) hv) (den_c 0))
      (den_eq' (den_mod hv (den_c 2)) (den_c 1)))) (den_eq' hv (den_c 1))
  · apply bv_congr
    unfold isP2
    refine and_congr Iff.rfl ⟨fun h d hd h1 h2 => ?_, fun h d hd => ?_⟩
    · rcases h d (by omega) with h' | h'
      · exact absurd ⟨h1, h2⟩ h'
      · exact h'
    · by_cases h' : M % d = 0 ∧ d % 2 = 1
      · exact Or.inr (h d (by omega) h'.1 h'.2)
      · exact Or.inl h'

lemma den_cntP2 {m : T} {M : ℕ} (hm : Den x Γ m M) : Den x Γ (cntP2T m) (cntP2 M) := by
  classical
  refine (den_count (body := fun j => isP2T j) (f := fun j => bv (isP2 j)) hm
    fun k i _ => den_isP2 den_var0).of_eq ?_
  rw [cntU_bv]; rfl

lemma den_cp2 {r L : T} {R N : ℕ} (hr : Den x Γ r R) (hL : Den x Γ L N) :
    Den x Γ (cp2T r L) (cp2 R N) := by
  refine (den_find (body := fun m => orT (andT (isP2T m) (eqT (cntP2T m) r))
    (eqT m (addT L (cT 1)))) (f := fun m => bv ((isP2 m ∧ cntP2 m = R) ∨ m = N + 1))
    (den_add hL (den_c 2)) fun k i _ => ?_).of_eq (cp2_findF R N)
  have hv : Den x ((k, i) :: Γ) (varT k) i := den_var0
  exact den_or (den_and (den_isP2 hv) (den_eq' (den_cntP2 hv) (hr.cons _)))
    (den_eq' hv (den_add (hL.cons _) (den_c 1)))

end FD

end PathChecking
