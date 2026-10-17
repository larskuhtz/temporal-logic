module

public import RequestProject.ACRound.Gen.Util
public import RequestProject.ACRound.Gen.Params
public import RequestProject.ACRound.LLBasic
public import RequestProject.Logspace.Concat
public import RequestProject.Logspace.Compose
public import RequestProject.ACRound.Pack

/-!
# The input of the circuit generator

The generator of the round circuit runs on the word
`zIn fB L (1ⁿ) = 1ⁿ 0 · pmapF fB (1^{L n})`: the unary input length followed by the
encodings `fB (1^ℓ)` of the oracle circuits `CB ℓ` for all `ℓ ≤ L n` (every bit doubled,
segments terminated by `00`).  This word is logspace computable from `1ⁿ` (`zIn_logspace`), and
its segments are located by `zIn_seg_*`.
-/

@[expose] public section

namespace PathChecking

open LL

namespace GenI

/-! ## `x ↦ 1^{A (|x| + 1)^A}` -/

lemma flatMap_range_true (m : ℕ) :
    List.flatMap (fun _ => [true]) (List.range m) = List.replicate m true := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ']; simp

/-- The program writing `1^{A (|x| + 1)^A}`. -/
def onesProg (A : ℕ) : Pr 4 :=
  .seq (.set 0 (.bin .add .len (.c 1))) (.seq (powP 1 0 2 A)
    (.seq (.set 1 (.bin .mul (.c A) (.v 1))) (.loop 3 (.v 1) (.out (.c 1)))))

lemma onesProg_output (A : ℕ) (x : Word) :
    (onesProg A).output (2 * A + 1) x = List.replicate (A * (x.length + 1) ^ A) true := by
  unfold Pr.output onesProg
  set n := x.length
  set C := capOf (2 * A + 1) x
  have hX : 2 ≤ n + 2 := by omega
  have hA : A ≤ (n + 2) ^ A := (Nat.lt_pow_self (by omega : 1 < n + 2)).le
  have hP : (n + 1) ^ A ≤ (n + 2) ^ A := Nat.pow_le_pow_left (by omega) _
  have hCe : C = (n + 2) ^ A * (n + 2) ^ A * (n + 2) + 3 := by
    simp only [C, capOf, n]; ring
  have hAP : A * (n + 1) ^ A ≤ C := by
    rw [hCe]
    have := Nat.mul_le_mul hA hP
    have : (n + 2) ^ A * (n + 2) ^ A ≤ (n + 2) ^ A * (n + 2) ^ A * (n + 2) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  have h1 : 1 ≤ (n + 1) ^ A := Nat.one_le_pow _ _ (by omega)
  have hAC : A ≤ C := by nlinarith
  have hPC : (n + 1) ^ A ≤ C := by
    rcases Nat.eq_zero_or_pos A with h0 | h0
    · rw [h0]; simp [C, capOf]
    · nlinarith
  have hn1 : n + 1 ≤ C := by
    rw [hCe]
    have : 1 ≤ (n + 2) ^ A := Nat.one_le_pow _ _ (by omega)
    have : 1 ≤ (n + 2) ^ A * (n + 2) ^ A := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  simp only [run_seq, run_set, eval_bin, eval_len, eval_c, ap_add, ap_mul]
  rw [min_eq_left (show n ≤ C by omega), min_eq_left (show 1 ≤ C by omega),
    min_eq_left (show n + 1 ≤ C by omega)]
  set ρ1 : Fin 4 → ℕ := Function.update (fun _ => 0) 0 (n + 1)
  obtain ⟨p1, p2⟩ := run_powP (z := x) (C := C) (1 : Fin 4) 0 2 A (by decide) (by decide)
    (by decide) ρ1 hAC (by omega) (by simpa [ρ1] using hPC)
  simp only [ρ1, Function.update_self] at p1
  set ρ2 := ((powP (1 : Fin 4) 0 2 A).run x C ρ1).1
  simp only [eval_v, p1, min_eq_left hAC, min_eq_left hAP, List.nil_append]
  rw [p2]
  have h := run_loop_spec (w := x) (C := C) (3 : Fin 4) (.v 1) (.out (.c 1))
    (Function.update ρ2 1 (A * (n + 1) ^ A)) (fun _ _ => True) (fun _ => [true]) trivial
    (fun i _ ρ' _ => ⟨trivial, by simp [min_eq_left (show 1 ≤ C by omega)]⟩)
  simp only [eval_v, Function.update_self] at h
  rw [h.2]
  exact flatMap_range_true _

lemma onesProg_logspace (A : ℕ) :
    LogspaceComputable (fun x => List.replicate (A * (x.length + 1) ^ A) true) :=
  logspaceComputable_of_output _ (onesProg A) _ (onesProg_output A)

/-! ## The generator input -/

/-- The input of the generator. -/
def zIn (fB : Word → Word) (A : ℕ) (x : Word) : Word :=
  (x.flatMap (fun _ => [true]) ++ [false]) ++
    (pmapF fB ∘ fun x => List.replicate (A * (x.length + 1) ^ A) true) x

theorem zIn_logspace {fB : Word → Word} (hfB : LogspaceComputable fB) (A : ℕ) :
    LogspaceComputable (zIn fB A) :=
  LogspaceComputable.append (LogspaceComputable.bitMap (fun _ => [true]) [false])
    ((onesProg_logspace A).comp hfB.pmap)

/-! ## Structure of the generator input -/

/-- Segment `ℓ` of the generator input. -/
def segW (CB : ℕ → Circuit) (ℓ : ℕ) : Word := (CB ℓ).encode.flatMap dupB ++ [false, false]

/-- Offset of segment `ℓ`. -/
def offW (CB : ℕ → Circuit) (ℓ : ℕ) : ℕ := ((List.range ℓ).map fun k => (segW CB k).length).sum

lemma take_replicate_true (ℓ m : ℕ) (h : ℓ ≤ m) :
    (List.replicate m true).take ℓ = List.replicate ℓ true := by
  simp [List.take_replicate, min_eq_left h]

lemma zIn_eq {fB : Word → Word} {CB : ℕ → Circuit} (A : ℕ)
    (hf : ∀ ℓ, fB (List.replicate ℓ true) = (CB ℓ).encode) (n : ℕ) :
    zIn fB A (List.replicate n true) = List.replicate n true ++ false ::
      (List.range (A * (n + 1) ^ A + 1)).flatMap (segW CB) := by
  unfold zIn pmapF
  simp only [Function.comp_apply, List.length_replicate, List.append_assoc, List.singleton_append]
  congr 1
  · simp [List.flatMap_replicate]
  · congr 1
    refine List.flatMap_congr fun ℓ hℓ => ?_
    simp only [List.mem_range] at hℓ
    rw [take_replicate_true _ _ (by omega), hf]
    rfl

lemma flatMap_range_getElem? {α : Type*} (f : ℕ → List α) (m ℓ i : ℕ) (hℓ : ℓ < m)
    (hi : i < (f ℓ).length) :
    ((List.range m).flatMap f)[((List.range ℓ).map fun k => (f k).length).sum + i]? =
      (f ℓ)[i]? := by
  obtain ⟨k, rfl⟩ : ∃ k, m = ℓ + 1 + k := ⟨m - ℓ - 1, by omega⟩
  rw [List.range_add, List.flatMap_append, List.range_succ, List.flatMap_append,
    List.getElem?_append_left, List.getElem?_append_right]
  · simp [List.length_flatMap]
  · simp [List.length_flatMap]
  · simp [List.length_flatMap]; omega

lemma flatMap_dupB_getElem?_even (l : Word) (j : ℕ) (hj : j < l.length) :
    (l.flatMap dupB)[2 * j]? = some true := by
  induction l generalizing j with
  | nil => simp at hj
  | cons b l ih =>
    rcases j with _ | j
    · simp [dupB]
    · rw [List.flatMap_cons, show 2 * (j + 1) = 2 * j + 2 by ring,
        List.getElem?_append_right (by simp [dupB])]
      simpa [dupB] using ih j (by simpa using hj)

lemma flatMap_dupB_getElem?_odd (l : Word) (j : ℕ) :
    (l.flatMap dupB)[2 * j + 1]? = l[j]? := by
  induction l generalizing j with
  | nil => simp
  | cons b l ih =>
    rcases j with _ | j
    · simp [dupB]
    · rw [List.flatMap_cons, show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring,
        List.getElem?_append_right (by simp [dupB])]
      simpa [dupB] using ih j

lemma flatMap_dupB_length (l : Word) : (l.flatMap dupB).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [List.flatMap_cons, dupB, ih]; ring

lemma segW_length (CB : ℕ → Circuit) (ℓ : ℕ) :
    (segW CB ℓ).length = 2 * (CB ℓ).encode.length + 2 := by
  rw [segW, List.length_append, flatMap_dupB_length]; rfl

lemma segW_even (CB : ℕ → Circuit) (ℓ j : ℕ) (hj : j < (CB ℓ).encode.length) :
    (segW CB ℓ)[2 * j]? = some true := by
  rw [segW, List.getElem?_append_left (by rw [flatMap_dupB_length]; omega)]
  exact flatMap_dupB_getElem?_even _ _ hj

lemma segW_odd (CB : ℕ → Circuit) (ℓ j : ℕ) (hj : j < (CB ℓ).encode.length) :
    (segW CB ℓ)[2 * j + 1]? = (CB ℓ).encode[j]? := by
  rw [segW, List.getElem?_append_left (by rw [flatMap_dupB_length]; omega)]
  exact flatMap_dupB_getElem?_odd _ _

lemma segW_end (CB : ℕ → Circuit) (ℓ : ℕ) :
    (segW CB ℓ)[2 * (CB ℓ).encode.length]? = some false := by
  rw [segW, List.getElem?_append_right (by rw [flatMap_dupB_length]), flatMap_dupB_length]
  simp

/-- Reading segment `ℓ` in the generator input. -/
lemma zIn_seg {fB : Word → Word} {CB : ℕ → Circuit} (A : ℕ)
    (hf : ∀ ℓ, fB (List.replicate ℓ true) = (CB ℓ).encode) (n ℓ i : ℕ)
    (hℓ : ℓ ≤ A * (n + 1) ^ A) (hi : i < (segW CB ℓ).length) :
    (zIn fB A (List.replicate n true))[n + 1 + offW CB ℓ + i]? = (segW CB ℓ)[i]? := by
  rw [zIn_eq A hf, List.getElem?_append_right (by simp; omega)]
  simp only [List.length_replicate, show n + 1 + offW CB ℓ + i - n = (offW CB ℓ + i) + 1 by omega,
    List.getElem?_cons_succ]
  exact flatMap_range_getElem? _ _ _ _ (by omega) hi

lemma zIn_unary {fB : Word → Word} {CB : ℕ → Circuit} (A : ℕ)
    (hf : ∀ ℓ, fB (List.replicate ℓ true) = (CB ℓ).encode) (n i : ℕ) (hi : i < n) :
    (zIn fB A (List.replicate n true))[i]? = some true := by
  rw [zIn_eq A hf, List.getElem?_append_left (by simpa using hi)]
  simp [hi]

lemma zIn_sep {fB : Word → Word} {CB : ℕ → Circuit} (A : ℕ)
    (hf : ∀ ℓ, fB (List.replicate ℓ true) = (CB ℓ).encode) (n : ℕ) :
    (zIn fB A (List.replicate n true))[n]? = some false := by
  rw [zIn_eq A hf, List.getElem?_append_right (by simp)]
  simp

end GenI

end PathChecking
