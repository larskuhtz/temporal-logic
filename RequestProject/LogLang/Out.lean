module

public import RequestProject.LogLang.Lib
public import RequestProject.Logspace.IO

/-!
# Output routines for the loop language

* `outW bs` emits a fixed bit string, `outToks ts` a fixed token list;
* `emitNat x y i` emits `natToks (ρ x)`, the binary token encoding of variable `x`.
-/

@[expose] public section

namespace PathChecking

namespace LL

open LS (encodeToks_append encodeToks_cons digitTok natToks_eq)

variable {V : ℕ} {w : Word} {C : ℕ}

/-- An expression with constant truth value `b`. -/
def bitEx (b : Bool) : Ex V := if b then .bin .eq (.c 0) (.c 0) else .c 0

@[simp] lemma decide_bitEx (b : Bool) (ρ : Fin V → ℕ) :
    decide ((bitEx b : Ex V).eval w C ρ ≠ 0) = b := by
  cases b <;> simp [bitEx]

@[simp] lemma decide_bitEx_eq (b : Bool) (ρ : Fin V → ℕ) :
    decide ((bitEx b : Ex V).eval w C ρ = 0) = !b := by
  cases b <;> simp [bitEx]

/-- Emit a fixed bit string. -/
def outW : List Bool → Pr V
  | [] => .skip
  | b :: bs => .seq (.out (bitEx b)) (outW bs)

@[simp] lemma run_outW (bs : List Bool) (ρ : Fin V → ℕ) :
    (outW bs : Pr V).run w C ρ = (ρ, bs) := by
  induction bs generalizing ρ with
  | nil => rfl
  | cons b bs ih => simp [outW, ih]

@[simp] lemma wr_outW (bs : List Bool) : (outW bs : Pr V).wr = [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [outW, Pr.wr, ih]

/-- Emit a fixed token list. -/
def outToks (ts : List Tok) : Pr V := outW (encodeToks ts)

@[simp] lemma run_outToks (ts : List Tok) (ρ : Fin V → ℕ) :
    (outToks ts : Pr V).run w C ρ = (ρ, encodeToks ts) := run_outW _ _

@[simp] lemma wr_outToks (ts : List Tok) : (outToks ts : Pr V).wr = [] := wr_outW _

lemma encodeToks_flatMap {α : Type*} (l : List α) (f : α → List Tok) :
    encodeToks (l.flatMap f) = l.flatMap (fun a => encodeToks (f a)) := by
  simp [encodeToks, List.flatMap_assoc]

/-- The tokens emitted in iteration `i` of `emitNat` on value `n`. -/
def natStepToks (n i : ℕ) : List Tok :=
  if n / 2 ^ i ≠ 0 then [digitTok (decide ((n / 2 ^ i) % 2 = 1))] else []

lemma flatMap_natStepToks (n m : ℕ) (hm : n ≤ m) :
    (List.range m).flatMap (natStepToks n) = (Nat.bits n).map digitTok := by
  induction n using Nat.strong_induction_on generalizing m with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [natStepToks]
    · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
        LS.Nat.bits_of_ne_zero' n (by omega), List.map_cons]
      have h1 : natStepToks n 0 = [digitTok (decide (n % 2 = 1))] := by
        simp [natStepToks]; omega
      have h2 : ∀ i, natStepToks n (i + 1) = natStepToks (n / 2) i := by
        intro i; simp [natStepToks, pow_succ, Nat.div_div_eq_div_mul, mul_comm]
      simp only [h1, h2, List.singleton_append]
      rw [ih (n / 2) (by omega) m (by omega)]

/-- Emit `natToks (ρ x)`, using the temporaries `y` (value) and `i` (loop counter). -/
def emitNat (x y i : Fin V) : Pr V :=
  .seq (.set y (.v x)) (.seq (.loop i (.v x)
      (.ite (.v y) (.seq (.ite (.bin .mod (.v y) (.c 2)) (outToks [Tok.one]) (outToks [Tok.zero]))
        (.set y (.bin .div (.v y) (.c 2)))) .skip))
    (outToks [Tok.sep]))

lemma emitNat_wr (x y i : Fin V) : (emitNat x y i).wr = [y, i, y] := by
  simp [emitNat, Pr.wr]

lemma run_emitNat (x y i : Fin V) (hyi : y ≠ i) (hC : 2 ≤ C) (ρ : Fin V → ℕ) :
    ((emitNat x y i).run w C ρ).2 = encodeToks (natToks (ρ x)) ∧
      ∀ z, z ≠ y → z ≠ i → ((emitNat x y i).run w C ρ).1 z = ρ z := by
  refine ⟨?_, fun z hz1 hz2 => Pr.run_frame _ _ _ (by simp [emitNat_wr, hz1, hz2])⟩
  have hc2 : min 2 C = 2 := by omega
  simp only [emitNat, run_seq, run_set, run_outToks, eval_v, List.nil_append]
  set ρ1 := Function.update ρ y (ρ x)
  have hloop := run_loop_spec (w := w) (C := C) i (.v x)
    (.ite (.v y) (.seq (.ite (.bin .mod (.v y) (.c 2)) (outToks [Tok.one]) (outToks [Tok.zero]))
        (.set y (.bin .div (.v y) (.c 2)))) .skip) ρ1
    (fun j ρ' => ρ' y = ρ x / 2 ^ j) (fun j => encodeToks (natStepToks (ρ x) j))
    (by simp [ρ1]) ?_
  · have hx : (Ex.v x : Ex V).eval w C ρ1 = ρ x := by
      show Function.update ρ y (ρ x) x = ρ x
      by_cases h : x = y
      · subst h; simp
      · simp [h]
    rw [hx] at hloop
    rw [hloop.2, ← encodeToks_flatMap, flatMap_natStepToks _ _ le_rfl, natToks_eq,
      encodeToks_append]
  · intro j _ ρ' hρ'
    have hy : (Function.update ρ' i j) y = ρ x / 2 ^ j := by
      rw [Function.update_of_ne hyi]; exact hρ'
    by_cases h0 : ρ x / 2 ^ j = 0
    · rw [run_ite_neg (by simpa using hy.trans h0)]
      refine ⟨?_, ?_⟩
      · simp only [run_skip]; rw [hy, h0, pow_succ, ← Nat.div_div_eq_div_mul, h0]
      · simp [natStepToks, h0, encodeToks]
    · rw [run_ite_pos (by simpa using hy ▸ h0)]
      by_cases h1 : ρ x / 2 ^ j % 2 = 1
      · rw [run_seq, run_ite_pos (by simp [hy, hc2, h1])]
        simp only [run_outToks, run_set, Function.update_self, eval_bin, eval_v, eval_c,
          ap_div, hy, hc2]
        refine ⟨by rw [pow_succ, Nat.div_div_eq_div_mul], ?_⟩
        simp [natStepToks, h0, h1, digitTok]
      · rw [run_seq, run_ite_neg (by simp [hy, hc2]; omega)]
        simp only [run_outToks, run_set, Function.update_self, eval_bin, eval_v, eval_c,
          ap_div, hy, hc2]
        refine ⟨by rw [pow_succ, Nat.div_div_eq_div_mul], ?_⟩
        simp [natStepToks, h0, h1, digitTok]

end LL

end PathChecking
