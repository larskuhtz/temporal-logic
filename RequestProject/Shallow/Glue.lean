module

public import RequestProject.Shallow.Stab
public import RequestProject.ACRound.Defs
public import RequestProject.Shallow.Lang

/-!
# The round algorithm for CTL* tree checking with shallow branching

For an input `w` of length `n` encoding the token list `ts`, the round algorithm uses

* `M = n / 5 + 1` (one more than the number of tokens), `m = M + 1` (so that `M + 1 < 2^m`),
* the depth bound `d = (⌊log₂ n⌋ + 1)^k`,
* `(n + 1)^3 = M^3` queries per round, query `qIdx M u ℓ j` asking `QP ts (root ts) d m M u ℓ j`,
* `2 (⌊log₂ n⌋ + 1)^k ≥ d + 1` rounds.

`roundDecidable_of_specs` reduces `RoundDecidable (CTLStarShallowTreeChecking k) LTLPathChecking k`
to the existence of logspace functions `Q` and `D` with the specifications `QSpecOK` and `DSpecOK`.
-/

@[expose] public section

namespace PathChecking

namespace ShallowP

open CTLP

/-- Index of the query for the triple `(u, ℓ, j)`. -/
def qIdx (M u ℓ j : ℕ) : ℕ := (u * M + ℓ) * M + j

/-- The answers `a` of a round, as a function of the triples. -/
def ansF (M : ℕ) (a : List Bool) (u ℓ j : ℕ) : Bool :=
  if u < M ∧ ℓ < M ∧ j < M then a.getD (qIdx M u ℓ j) false else false

/-- The instance token list of a formula and a tree. -/
def instToks (φ : CTLStar) (t : LTree) : List Tok := Tok.lpar :: (φ.toks ++ Tok.rpar :: t.toks)

/-- Specification of the query function. -/
def QSpecOK (k : ℕ) (Q : Word → Word) : Prop :=
  ∀ (φ : CTLStar) (t : LTree) (a : List Bool) (u ℓ j : ℕ),
    a.length = ((encodeToks (instToks φ t)).length + 1) ^ 3 →
    u < (instToks φ t).length + 1 → ℓ < (instToks φ t).length + 1 →
    j < (instToks φ t).length + 1 →
    Q (pack (encodeToks (instToks φ t)) (qIdx ((instToks φ t).length + 1) u ℓ j) a) =
      encodeToks (QP (instToks φ t) (root (instToks φ t))
        (shallowBound k (encodeToks (instToks φ t)).length) ((instToks φ t).length + 2)
        ((instToks φ t).length + 1) u ℓ j (ansF ((instToks φ t).length + 1) a))

/-- Specification of the decision function. -/
def DSpecOK (k : ℕ) (D : Word → Word) : Prop :=
  ∀ (w : Word) (a : List Bool), a.length = (w.length + 1) ^ 3 →
    (D (pack w 0 a) = [true] ↔ ∃ (φ : CTLStar) (t : LTree), w = encodeToks (instToks φ t) ∧
      Shallow.ShallowBranching (shallowBound k w.length) t ∧
      ∀ ℓ < (instToks φ t).length + 1,
        ansF ((instToks φ t).length + 1) a (root (instToks φ t)) ℓ 1 = true)

lemma roundAns_length (B : Language) (Q : Word → Word) (Nq : ℕ) (w : Word) (r : ℕ) :
    (roundAns B Q Nq w r).length = Nq := by
  cases r <;> simp [roundAns]

lemma qIdx_lt {M u ℓ j : ℕ} (hu : u < M) (hℓ : ℓ < M) (hj : j < M) : qIdx M u ℓ j < M ^ 3 := by
  unfold qIdx
  have h1 : u * M + ℓ < M * M := by nlinarith
  have h2 : (u * M + ℓ) * M + j < M * M * M := by nlinarith
  calc _ < M * M * M := h2
    _ = M ^ 3 := by ring

lemma instToks_drop_root (φ : CTLStar) (t : LTree) :
    (instToks φ t).drop (root (instToks φ t)) = t.toks ++ [] := by
  set ts := instToks φ t
  have h1 : ts.drop 1 = φ.toks ++ Tok.rpar :: t.toks := rfl
  have hfe := fend_formula φ h1
  have h2 := drop_append_of_drop h1
  rw [← hfe] at h2
  simpa [root] using drop_succ_of_drop h2

lemma encLen (l : List Tok) : (encodeToks l).length = 5 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encodeToks, List.flatMap_cons, List.length_append, Tok.bits, List.length_map,
      List.length_range, List.length_cons] at ih ⊢
    omega

/-- **The glue**: the specifications of `Q` and `D` give the round algorithm. -/
theorem roundDecidable_of_specs (k : ℕ) (Q D : Word → Word) (hQ : LogspaceComputable Q)
    (hD : LogspaceComputable D) (hQs : QSpecOK k Q) (hDs : DSpecOK k D) :
    RoundDecidable (CTLStarShallowTreeChecking k) LTLPathChecking k := by
  refine ⟨3, 2, Q, D, hQ, hD, fun w => ?_⟩
  set n := w.length
  set Nq := (n + 1) ^ 3
  set R := 2 * (Nat.log 2 n + 1) ^ k
  set M := n / 5 + 1
  have hRd : shallowBound k n + 1 ≤ R := by
    have : 1 ≤ (Nat.log 2 n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    simp only [shallowBound, R]; omega
  -- the answers of the rounds, as functions of the triples
  set T : ℕ → ℕ → ℕ → ℕ → Bool := fun r => ansF M (roundAns LTLPathChecking Q Nq w r)
  have hstab : ∀ (φ : CTLStar) (t : LTree), w = encodeToks (instToks φ t) →
      Shallow.ShallowBranching (shallowBound k n) t →
      ∀ ℓ < (instToks φ t).length + 1, (T R (root (instToks φ t)) ℓ 1 = true ↔
        CTLStar.Holds φ (pathOf (instToks φ t) (root (instToks φ t)) ℓ)) := by
    intro φ t hw hsb ℓ hℓ
    set ts := instToks φ t
    have hn : (encodeToks ts).length = n := by rw [← hw]
    have hM : ts.length + 1 = M := by rw [encLen] at hn; simp only [M]; omega
    have hT : ∀ r u ℓ j, u < M → ℓ < M → j < M →
        (T (r + 1) u ℓ j = true ↔ encodeToks (QP ts (root ts) (shallowBound k n) (M + 1) M u ℓ j
          (T r)) ∈ LTLPathChecking) := by
      intro r u ℓ j hu hℓ hj
      have hq : qIdx M u ℓ j < Nq :=
        (qIdx_lt hu hℓ hj).trans_le (Nat.pow_le_pow_left (by simp only [M]; omega) _)
      simp only [T, ansF, hu, hℓ, hj, and_self, if_true, roundAns]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq]
      simp only [Option.map_some, Option.getD_some]
      have hQe := hQs φ t (roundAns LTLPathChecking Q Nq w r) u ℓ j
        (by rw [roundAns_length, hn]) (by rw [hM]; exact hu) (by rw [hM]; exact hℓ)
        (by rw [hM]; exact hj)
      rw [hn, ← hw, hM, show ts.length + 2 = M + 1 by omega] at hQe
      rw [hQe]
      exact @decide_eq_true_iff _ (Classical.dec _)
    have h1 : ts.drop 1 = φ.toks ++ Tok.rpar :: t.toks := rfl
    exact stab_root T Nat.lt_two_pow_self (by omega) hT
      (instToks_drop_root φ t) hsb hRd ℓ (by omega) 1 φ _ h1
  rw [hDs w _ (roundAns_length _ _ _ _ _)]
  constructor
  · rintro ⟨φ, t, hw, hsb, hsat⟩
    refine ⟨φ, t, hw, hsb, fun ℓ hℓ => ?_⟩
    have hn : (encodeToks (instToks φ t)).length = n := by simp only [n]; rw [hw]; rfl
    have hM : (instToks φ t).length + 1 = M := by rw [encLen] at hn; simp only [M]; omega
    rw [hM]
    refine (hstab φ t hw hsb ℓ hℓ).2 ?_
    have h3 := instToks_drop_root φ t
    exact hsat _ (pathOf_isTreePath h3 ℓ) (by rw [pathOf_zero, sub_eq h3])
  · rintro ⟨φ, t, hw, hsb, hall⟩
    refine ⟨φ, t, hw, hsb, fun π hπ h0 => ?_⟩
    have h3 := instToks_drop_root φ t
    obtain ⟨ℓ, -, hl2, rfl⟩ := path_cover _ t le_rfl h3 π hπ h0
    have hn : (encodeToks (instToks φ t)).length = n := by simp only [n]; rw [hw]
    have hM : (instToks φ t).length + 1 = M := by rw [encLen] at hn; simp only [M]; omega
    have hlt : ℓ < (instToks φ t).length + 1 := by
      have := toks_le h3; omega
    have := hall ℓ hlt
    rw [hM] at this
    exact (hstab φ t hw hsb ℓ hlt).1 this

end ShallowP

end PathChecking
