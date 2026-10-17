module

public import RequestProject.ACRound.Gen.Uniform
public import RequestProject.ACRound.Gen.Poly
public import RequestProject.ACRound.EvalMain
public import RequestProject.ACRound.Depth
public import RequestProject.ACRound.WF
public import RequestProject.ACRound.LangF2
public import RequestProject.ACRound.TagMap
public import RequestProject.ACRound.Self

/-!
# Rounds of logspace computation and oracle queries are in `AC`

The main result about round algorithms (`RoundDecidable`, `RequestProject/ACRound/Defs.lean`):

* `RoundDecidable.mem_ACOracle_add`: if `A` is decided by a logspace algorithm with
  `O(log^k n)` rounds of parallel queries to `B`, and `B ∈ AC^j[LogDCFL]`, then
  `A ∈ AC^{k+j}[LogDCFL]`.  The circuit simulates the rounds layer by layer: the logspace
  bookkeeping of each round becomes an oracle gate for a language in `L ⊆ LogDCFL`, and each
  query becomes a copy of the `AC^j[LogDCFL]` circuit for `B`.
* `RoundDecidable.mem_ACOracle_LogDCFL` (`j = 1`): queries to an `AC¹[LogDCFL]` language give
  `AC^{k+1}[LogDCFL]`.  This is used for CTL* on trees with shallow branching, with `B` = LTL
  path checking.
* `RoundDecidable.mem_ACOracle_of_LogDCFL` (`j = 0`): queries to a `LogDCFL` language give
  `AC^k[LogDCFL]`, since every language is in `AC⁰` relative to itself (`ACOracle_self_zero`).
  For `k = 1` this is the shape of the `AC¹[LogDCFL]` algorithm for LTL path checking.
-/

@[expose] public section

namespace PathChecking

/-- **Rounds of logspace computation and oracle queries.**  If `A` is decided by a logspace
algorithm with `O(log^k n)` rounds of parallel queries to `B`, and `B ∈ AC^j[LogDCFL]`, then
`A ∈ AC^{k+j}[LogDCFL]`. -/
theorem RoundDecidable.mem_ACOracle_add {A B : Language} {j k : ℕ}
    (hB : B ∈ ACOracle j LogDCFL) (hA : RoundDecidable A B k) :
    A ∈ ACOracle (k + j) LogDCFL := by
  obtain ⟨Bc, hBc, CB, cB, ⟨fB, hfB, hfBe⟩, hCB, hCBe⟩ := hB
  obtain ⟨e, c, Q, D, hQ, hD, hAD⟩ := hA
  obtain ⟨-, -, eQ, -, -, hQlen⟩ := hQ.exists_bound
  set A0 := 8 ^ eQ + (e + 1) * eQ with hA0
  let G : GCst := ⟨e, c, k, A0, cB⟩
  have hsz : ∀ ℓ, (CB ℓ).length ≤ G.cB * (ℓ + 1) ^ G.cB := fun ℓ => (hCB ℓ).2.1
  have hwf : ∀ n, ∀ ℓ ≤ (G.lay CB n).L, (CB ℓ).WellFormed ℓ := fun n ℓ _ => (hCB ℓ).1
  have hSize : ∀ n, (G.lay CB n).SizeOk := by
    intro n ℓ hℓ
    refine ⟨(hCB ℓ).1.1, ?_⟩
    show (CB ℓ).length + 1 ≤ G.cB * (G.L n + 1) ^ G.cB + 1
    have := hsz ℓ
    have : (ℓ + 1) ^ G.cB ≤ (G.L n + 1) ^ G.cB :=
      Nat.pow_le_pow_left (by simpa [GCst.lay] using hℓ) _
    have : G.cB * (ℓ + 1) ^ G.cB ≤ G.cB * (G.L n + 1) ^ G.cB := Nat.mul_le_mul_left _ this
    omega
  -- the oracle language
  have hO : tagU Bc (tagU (LangF Q) (LangF D)) ∈ LogDCFL :=
    LogDCFL_tagU hBc (LogDCFL_tagU (ClassL_subset_LogDCFL (LangF_mem_ClassL hQ))
      (ClassL_subset_LogDCFL (LangF_mem_ClassL hD)))
  -- size bound
  have hpoly : PolyB (fun n => (G.lay CB n).F0 + 3) := by
    have hR : PolyB G.R := by
      refine (PolyB.const c |>.mul (PolyB.id'.add (PolyB.const 1) |>.pow k)).mono fun n => ?_
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (log_add_one_le n) _)
    have hL : PolyB G.L := PolyB.const _ |>.mul (PolyB.id'.add (PolyB.const 1) |>.pow _)
    have hL1 : PolyB (fun n => G.L n + 1) := hL.add (PolyB.const 1)
    have hS : PolyB G.S := (PolyB.const _ |>.mul (hL1.pow _)).add (PolyB.const 1)
    have hW : PolyB (fun n => (G.lay CB n).W) :=
      ((PolyB.const 2 |>.mul hL1).add (hL1.mul hS)).add (PolyB.const 1)
    have hNq : PolyB G.Nq := PolyB.id'.add (PolyB.const 1) |>.pow _
    exact (((PolyB.id'.add (PolyB.const 2)).add ((hR.mul hNq).mul hW)).add (PolyB.const 3)).mono
      fun n => le_of_eq (by simp [Lay.F0, Lay.P0, GCst.lay])
  obtain ⟨K, hK⟩ := hpoly
  refine ⟨_, hO, fun n => (G.lay CB n).circ,
    K + c * (cB * (2 * A0 + 1) ^ j + 4) + 2, G.lay_uniform hfB hfBe hsz (fun ℓ => (hCB ℓ).1), fun n => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Lay.circ_wf (hSize n) (hwf n)
  · rw [Circuit.size, Lay.circ_length (hSize n)]
    refine (hK n).trans (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega)))
  · -- depth
    have hlog := log_mul_pow_le A0 n
    set X := Nat.log 2 n + 1 with hX
    have hX1 : 1 ≤ X := by omega
    have hDB : ∀ ℓ ≤ (G.lay CB n).L, (CB ℓ).depth ≤ cB * ((2 * A0 + 1) ^ j * X ^ j) := by
      intro ℓ hℓ
      refine (hCB ℓ).2.2.trans (Nat.mul_le_mul_left _ ?_)
      have h1 := Nat.log_mono_right (b := 2) (show ℓ ≤ G.L n by simpa [GCst.lay] using hℓ)
      have h2 : Nat.log 2 ℓ + 1 ≤ (2 * A0 + 1) * X := by
        have : Nat.log 2 (G.L n) + 1 ≤ (2 * A0 + 1) * X := hlog
        omega
      rw [← mul_pow]; exact Nat.pow_le_pow_left h2 _
    refine (Lay.circ_depth (hSize n) (hwf n) hDB).trans ?_
    show c * X ^ k * (cB * ((2 * A0 + 1) ^ j * X ^ j) + 4) + 2 ≤
      (K + c * (cB * (2 * A0 + 1) ^ j + 4) + 2) * X ^ (k + j)
    have h2 : 1 ≤ X ^ (k + j) := Nat.one_le_pow _ _ hX1
    have h3 : 1 ≤ X ^ j := Nat.one_le_pow _ _ hX1
    calc c * X ^ k * (cB * ((2 * A0 + 1) ^ j * X ^ j) + 4) + 2
        ≤ c * X ^ k * (cB * ((2 * A0 + 1) ^ j * X ^ j) + 4 * X ^ j) + 2 := by gcongr; omega
      _ = c * (cB * (2 * A0 + 1) ^ j + 4) * X ^ (k + j) + 2 := by ring
      _ ≤ _ := by nlinarith
  · -- correctness
    intro w
    rw [hAD w, Lay.circ_eval (hSize w.length) (hwf w.length) rfl
      (fun u _ => hCBe u) ?_]
    · simp only [GCst.lay, GCst.Nq, GCst.R, decide_eq_true_eq]
      exact Iff.rfl
    · intro r _ q hq
      set u := pack w q (roundAns B Q (G.lay CB w.length).Nq w r)
      have hu : u.length = 2 * w.length + 1 + 2 * (w.length + 1) ^ e := by
        simp only [u]
        rw [pack_length _ _ _ (by rw [roundAns_length]; omega), roundAns_length]
        rfl
      have h1 := hQlen u
      have h2 := two_pow_log_le u.length
      have h3 : 2 ^ (eQ * (Nat.log 2 u.length + 1)) ≤ (2 * (u.length + 1)) ^ eQ := by
        rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left h2 _
      set N := w.length + 1
      have hN : 1 ≤ N := by omega
      have h4 : 2 * (u.length + 1) ≤ 8 * N ^ (e + 1) := by
        rw [hu]
        have : N ≤ N ^ (e + 1) := by
          calc N = N ^ 1 := (pow_one N).symm
            _ ≤ N ^ (e + 1) := Nat.pow_le_pow_right hN (by omega)
        have : N ^ e ≤ N ^ (e + 1) := Nat.pow_le_pow_right hN (by omega)
        omega
      have h5 : (2 * (u.length + 1)) ^ eQ ≤ 8 ^ eQ * N ^ ((e + 1) * eQ) := by
        rw [pow_mul, ← mul_pow]; exact Nat.pow_le_pow_left h4 _
      have h6 : 8 ^ eQ * N ^ ((e + 1) * eQ) ≤ A0 * N ^ A0 :=
        Nat.mul_le_mul (by rw [hA0]; exact Nat.le_add_right _ _) (Nat.pow_le_pow_right hN (by rw [hA0]; exact Nat.le_add_left _ _))
      show (Q u).length ≤ A0 * N ^ A0
      have := h3.trans (h5.trans h6)
      omega


/-- **Rounds of queries to a `LogDCFL` language.**  A logspace algorithm with `O(log^k n)`
rounds of polynomially many parallel queries to a language in `LogDCFL` decides a language in
`AC^k[LogDCFL]`. -/
theorem RoundDecidable.mem_ACOracle_of_LogDCFL {A B : Language} {k : ℕ}
    (hB : B ∈ LogDCFL) (hA : RoundDecidable A B k) : A ∈ ACOracle k LogDCFL := by
  simpa using hA.mem_ACOracle_add (LogDCFL_subset_ACOracle_zero hB)

/-- **Rounds of queries to an `AC¹[LogDCFL]` language.**  If `A` is decided by a logspace
algorithm with `O(log^k n)` rounds of parallel queries to `B`, and `B ∈ AC¹[LogDCFL]`, then
`A ∈ AC^{k+1}[LogDCFL]`. -/
theorem RoundDecidable.mem_ACOracle_LogDCFL {A B : Language} {k : ℕ}
    (hB : B ∈ ACOracle 1 LogDCFL) (hA : RoundDecidable A B k) :
    A ∈ ACOracle (k + 1) LogDCFL :=
  hA.mem_ACOracle_add hB

end PathChecking
