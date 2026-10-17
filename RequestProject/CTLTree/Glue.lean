module

public import RequestProject.CTLTree.QCorrect
public import RequestProject.ACRound.Defs

/-!
# The round algorithm for CTL tree checking

For an instance `ts = ( φ ) t` with `M = |ts| + 1`, every round asks, for all pairs `(u, j)` of
positions `< M`, the query `CQ ts (M + 2) M u j A` (query index `u M + j`), where `A` are the
answers of the previous round.  After `r` rounds, the answers for the nodes of size `< 2^r` are
correct (`stab`), so `⌊log₂ n⌋ + 1` rounds suffice.

`roundDecidable_of_specs` reduces `RoundDecidable CTLTreeChecking LTLPathChecking 1` to the
existence of logspace functions `Q` and `D` with the specifications `QSpecC` and `DSpecC`.
-/

@[expose] public section

namespace PathChecking

namespace CTLT

open CTLP MCVPReduction ShallowP LS

/-- The answers `a` of a round, as a function of the pairs `(c, k)`. -/
def ansC (M : ℕ) (a : List Bool) (c k : ℕ) : Bool :=
  if c < M ∧ k < M then a.getD (c * M + k) false else false

/-- The instance token list of a CTL formula and a tree. -/
def instC (φ : CTL) (t : LTree) : List Tok := Tok.lpar :: (φ.toks ++ Tok.rpar :: t.toks)

/-- The position of the tree in an instance. -/
def rootC (ts : List Tok) : ℕ := fendC ts 1 + 1

/-- Specification of the query function. -/
def QSpecC (Q : Word → Word) : Prop :=
  ∀ (ts : List Tok) (a : List Bool) (u j : ℕ),
    a.length = ((encodeToks ts).length + 1) ^ 2 → u < ts.length + 1 → j < ts.length + 1 →
    Q (pack (encodeToks ts) (u * (ts.length + 1) + j) a) =
      encodeToks (CQ ts (ts.length + 3) (ts.length + 1) u j (ansC (ts.length + 1) a))

/-- Specification of the decision function. -/
def DSpecC (D : Word → Word) : Prop :=
  ∀ (w : Word) (a : List Bool), a.length = (w.length + 1) ^ 2 →
    (D (pack w 0 a) = [true] ↔ ∃ (φ : CTL) (t : LTree), w = encodeToks (instC φ t) ∧
      ansC ((instC φ t).length + 1) a (rootC (instC φ t)) 1 = true)

lemma instC_drop_one (φ : CTL) (t : LTree) : (instC φ t).drop 1 = φ.toks ++ Tok.rpar :: t.toks :=
  rfl

lemma instC_drop_root (φ : CTL) (t : LTree) :
    (instC φ t).drop (rootC (instC φ t)) = t.toks ++ [] := by
  have h1 := instC_drop_one φ t
  rw [rootC, fendC_formula φ h1, show 1 + φ.toks.length + 1 = 1 + (φ.toks.length + 1) by omega,
    ← List.drop_drop, h1]
  simp

lemma encLenC (l : List Tok) : (encodeToks l).length = 5 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encodeToks, List.flatMap_cons, List.length_append, Tok.bits, List.length_map,
      List.length_range, List.length_cons] at ih ⊢
    omega

lemma sz_pos {ts : List Tok} {c : ℕ} {s : LTree} {R : List Tok} (h : ts.drop c = s.toks ++ R) :
    0 < sz ts c := by
  rw [sz_of_drop h]; exact LTree.toks_length_pos s

lemma lt_length_of_dropC {ts : List Tok} {k : ℕ} {ψ : CTL} {R : List Tok}
    (h : ts.drop k = ψ.toks ++ R) : k < ts.length := by
  have := CTL.toks_length_pos ψ
  obtain ⟨t, l, e⟩ : ∃ t l, ψ.toks = t :: l := by
    cases e : ψ.toks with
    | nil => rw [e] at this; simp at this
    | cons t l => exact ⟨t, l, rfl⟩
  exact lt_of_drop (t := t) (rest := l ++ R) (by rw [h, e]; rfl)

lemma lt_length_of_dropT {ts : List Tok} {k : ℕ} {s : LTree} {R : List Tok}
    (h : ts.drop k = s.toks ++ R) : k < ts.length := by
  have := toks_le h; have := LTree.toks_length_pos s; omega

/-- **Stabilisation.**  After `r` rounds the answers are correct for the nodes of size
`< 2^r`. -/
theorem stab {ts : List Tok} (T : ℕ → ℕ → ℕ → Bool)
    (hT : ∀ r c k, c < ts.length + 1 → k < ts.length + 1 →
      (T (r + 1) c k = true ↔
        encodeToks (CQ ts (ts.length + 3) (ts.length + 1) c k (T r)) ∈ LTLPathChecking)) :
    ∀ r c k (s : LTree) Rc (ψ : CTL) Rk, ts.drop c = s.toks ++ Rc → sz ts c < 2 ^ r →
      ts.drop k = ψ.toks ++ Rk → (T r c k = true ↔ CSat s ψ) := by
  intro r
  induction r with
  | zero => intro c k s Rc ψ Rk hc hs; have := sz_pos hc; simp at hs; omega
  | succ r ih =>
    intro c k s Rc ψ Rk hc hs hk
    rw [hT r c k (by have := lt_length_of_dropT hc; omega)
      (by have := lt_length_of_dropC hk; omega)]
    refine CQ_correct (T r) hc (by omega) (by
      have := Nat.lt_two_pow_self (n := ts.length + 3); omega) ?_ hk
    intro c' k' s' Rc' ψ' Rk' hc' hs' hk'
    exact ih c' k' s' Rc' ψ' Rk' hc' (by rw [pow_succ] at hs; omega) hk'

lemma roundAns_lengthC (B : Language) (Q : Word → Word) (Nq : ℕ) (w : Word) (r : ℕ) :
    (roundAns B Q Nq w r).length = Nq := by
  cases r <;> simp [roundAns]

/-- **The glue**: the specifications of `Q` and `D` give the round algorithm. -/
theorem roundDecidable_of_specs (Q D : Word → Word) (hQ : LogspaceComputable Q)
    (hD : LogspaceComputable D) (hQs : QSpecC Q) (hDs : DSpecC D) :
    RoundDecidable CTLTreeChecking LTLPathChecking 1 := by
  refine ⟨2, 1, Q, D, hQ, hD, fun w => ?_⟩
  set n := w.length
  set Nq := (n + 1) ^ 2
  set R := 1 * (Nat.log 2 n + 1) ^ 1
  set T : ℕ → ℕ → ℕ → ℕ → Bool := fun M r => ansC M (roundAns LTLPathChecking Q Nq w r)
  have hstab : ∀ (φ : CTL) (t : LTree), w = encodeToks (instC φ t) →
      (T ((instC φ t).length + 1) R (rootC (instC φ t)) 1 = true ↔ CTL.TreeSat t φ) := by
    intro φ t hw
    set ts := instC φ t
    have hn : (encodeToks ts).length = n := by rw [← hw]
    have hM : 5 * ts.length = n := by rw [← hn, encLenC]
    have hT : ∀ r c k, c < ts.length + 1 → k < ts.length + 1 →
        (T (ts.length + 1) (r + 1) c k = true ↔ encodeToks (CQ ts (ts.length + 3) (ts.length + 1)
          c k (T (ts.length + 1) r)) ∈ LTLPathChecking) := by
      intro r c k hc hk
      have hq : c * (ts.length + 1) + k < Nq := by
        have h1 : c * (ts.length + 1) + k < (ts.length + 1) * (ts.length + 1) := by nlinarith
        calc _ < (ts.length + 1) * (ts.length + 1) := h1
          _ ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
          _ = Nq := by ring
      simp only [T, ansC, hc, hk, and_self, if_true, roundAns]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq]
      simp only [Option.map_some, Option.getD_some]
      have hQe := hQs ts (roundAns LTLPathChecking Q Nq w r) c k
        (by rw [roundAns_lengthC, hn]) hc hk
      rw [show pack w (c * (ts.length + 1) + k) (roundAns LTLPathChecking Q Nq w r) =
        pack (encodeToks ts) (c * (ts.length + 1) + k) (roundAns LTLPathChecking Q Nq w r) by
        rw [← hw], hQe]
      exact @decide_eq_true_iff _ (Classical.dec _)
    have hroot := instC_drop_root φ t
    have hR : sz ts (rootC ts) < 2 ^ R := by
      rw [sz_of_drop hroot]
      have h1 : t.toks.length ≤ ts.length := by simp [ts, instC]; omega
      have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
      simp only [R, one_mul, pow_one]
      omega
    exact stab (T (ts.length + 1)) hT R _ 1 t [] φ _ hroot hR (instC_drop_one φ t)
  rw [hDs w _ (roundAns_lengthC _ _ _ _ _)]
  constructor
  · rintro ⟨φ, t, hw, hsat⟩
    exact ⟨φ, t, hw, (hstab φ t hw).2 hsat⟩
  · rintro ⟨φ, t, hw, hans⟩
    exact ⟨φ, t, hw, (hstab φ t hw).1 hans⟩

end CTLT

end PathChecking
