module

public import RequestProject.LTLPath.LGrid
public import RequestProject.LTLPath.FDGate

/-!
# Computing the grid drawing of a layered system

The grid drawing `LSys.circ` of a layered system (`RequestProject/LTLPath/LGrid.lean`) is
computed from a few per-gate quantities (`LSem`): rows, columns, kind codes, at most two
arguments with presence flags, and the values of the constant gates.  `Agree L s NG` says that
these quantities describe the system `L` on the live gates (all of which are below `NG`).  Under
this hypothesis the auxiliary notions of the drawing (`isR`, `sArg`, `dArg`, `hasR`, `col`,
`slot`, `GateAt`, `DDes`, `colConst`) are expressed by bounded searches over the quantities.
-/

@[expose] public section

namespace PathChecking

namespace Grid

/-- Kind of a grid node. -/
def GN.kind : GN → GateKind
  | .cst b => .const b
  | .gt k _ _ => k

/-- Does a grid node read the node straight below? -/
def GN.sf : GN → Bool
  | .cst _ => false
  | .gt _ s _ => s

/-- Does a grid node read the node diagonally below? -/
def GN.df : GN → Bool
  | .cst _ => false
  | .gt _ _ d => d

lemma gateOf_eq (nd : ℕ → ℕ → GN) (W n : ℕ) : gateOf nd W n =
    ⟨(nd (n / W) (W - 1 - n % W)).kind,
      (if (nd (n / W) (W - 1 - n % W)).df then [idx W (n / W - 1) (W - 1 - n % W + 1)] else []) ++
      (if (nd (n / W) (W - 1 - n % W)).sf then [idx W (n / W - 1) (W - 1 - n % W)] else [])⟩ := by
  unfold gateOf
  rcases nd (n / W) (W - 1 - n % W) with b | ⟨k, s, d⟩ <;> simp [GN.kind, GN.sf, GN.df]

end Grid

namespace LG

open Grid Classical

/-- Per-gate quantities of a layered system. -/
structure LSem where
  X : ℕ → ℕ
  Y : ℕ → ℕ
  kc : ℕ → ℕ
  k0 : ℕ → Bool
  a0 : ℕ → ℕ
  k1 : ℕ → Bool
  a1 : ℕ → ℕ
  cv : ℕ → ℕ

namespace LSem

variable (s : LSem) (L : LSys)

def isR (h x : ℕ) : Bool := L.live x && s.Y x == s.Y h
def r0 (h : ℕ) : Bool := s.k0 h && !s.isR L h (s.a0 h)
def r1 (h : ℕ) : Bool := s.k1 h && !s.isR L h (s.a1 h)
def sS (h : ℕ) : Bool := s.r0 L h || s.r1 L h
def sV (h : ℕ) : ℕ :=
  if (s.r0 L h && s.r1 L h) = true then max (s.a0 h) (s.a1 h)
  else if s.r0 L h = true then s.a0 h else s.a1 h
def dS (h : ℕ) : Bool := s.r0 L h && s.r1 L h && !(s.a0 h == s.a1 h)
def dV (h : ℕ) : ℕ := min (s.a0 h) (s.a1 h)
def hasR (h : ℕ) : Bool := (s.k0 h && s.isR L h (s.a0 h)) || (s.k1 h && s.isR L h (s.a1 h))

variable (M : ℕ)

def col (h : ℕ) : ℕ := 2 * (s.X h + M - s.Y h)
def slot (h x : ℕ) : ℕ := if (s.sS L h && s.sV L h == x) = true then s.col M h else s.col M h + 1

end LSem

/-- The quantities `s` describe the layered system `L`, whose live gates are below `NG`. -/
structure Agree (L : LSys) (s : LSem) (NG : ℕ) : Prop where
  X : ∀ h, L.live h = true → s.X h = L.X h
  Y : ∀ h, L.live h = true → s.Y h = L.Y h
  kc : ∀ h, L.live h = true → s.kc h = kcode (L.g h).kind
  args : ∀ h, L.live h = true →
    (L.g h).args = (if s.k0 h then [s.a0 h] else []) ++ (if s.k1 h then [s.a1 h] else [])
  cv : ∀ h, L.live h = false → s.cv h = (cval (L.g h)).toNat
  ng : ∀ h, L.live h = true → h < NG
  kind : ∀ h, L.live h = true → (L.g h).kind = .and ∨ (L.g h).kind = .or

namespace Agree

variable {L : LSys} {s : LSem} {NG M : ℕ} (A : Agree L s NG)
include A

lemma isR_eq {h : ℕ} (hl : L.live h = true) (x : ℕ) : L.isR h x = s.isR L h x := by
  unfold LSys.isR LSem.isR
  cases hx : L.live x
  · rfl
  · simp [A.Y x hx, A.Y h hl]

lemma mem_args {h : ℕ} (hl : L.live h = true) (x : ℕ) :
    x ∈ (L.g h).args ↔ (s.k0 h = true ∧ x = s.a0 h) ∨ (s.k1 h = true ∧ x = s.a1 h) := by
  rw [A.args h hl]
  cases s.k0 h <;> cases s.k1 h <;> simp

lemma nonR_eq {h : ℕ} (hl : L.live h = true) :
    L.nonR h = (if s.r0 L h then [s.a0 h] else []) ++ (if s.r1 L h then [s.a1 h] else []) := by
  unfold LSys.nonR LSem.r0 LSem.r1
  have e : L.isR h = s.isR L h := funext (A.isR_eq hl)
  rw [A.args h hl, List.filter_append, e]
  clear e
  by_cases h0 : s.isR L h (s.a0 h) = true <;> by_cases h1 : s.isR L h (s.a1 h) = true <;>
    cases s.k0 h <;> cases s.k1 h <;> simp_all [List.filter]

lemma sArg_eq {h : ℕ} (hl : L.live h = true) :
    L.sArg h = if s.sS L h = true then some (s.sV L h) else none := by
  unfold LSys.sArg LSem.sS LSem.sV
  rw [A.nonR_eq hl]
  cases s.r0 L h <;> cases s.r1 L h <;> simp

lemma dArg_eq {h : ℕ} (hl : L.live h = true) :
    L.dArg h = if s.dS L h = true then some (s.dV h) else none := by
  unfold LSys.dArg LSem.dS LSem.dV
  rw [A.nonR_eq hl]
  cases s.r0 L h <;> cases s.r1 L h <;> simp

lemma hasR_eq {h : ℕ} (hl : L.live h = true) : L.hasR h = s.hasR L h := by
  unfold LSys.hasR LSem.hasR
  have e : L.isR h = s.isR L h := funext (A.isR_eq hl)
  rw [A.args h hl, e]
  cases s.k0 h <;> cases s.k1 h <;> simp

lemma col_eq {h : ℕ} (hl : L.live h = true) : L.col M h = s.col M h := by
  unfold LSys.col LSem.col; rw [A.X h hl, A.Y h hl]

lemma sArg_some {h : ℕ} (hl : L.live h = true) (x : ℕ) :
    L.sArg h = some x ↔ s.sS L h = true ∧ s.sV L h = x := by
  rw [A.sArg_eq hl]; split_ifs with h1 <;> simp [h1]

lemma dArg_some {h : ℕ} (hl : L.live h = true) (x : ℕ) :
    L.dArg h = some x ↔ s.dS L h = true ∧ s.dV h = x := by
  rw [A.dArg_eq hl]; split_ifs with h1 <;> simp [h1]

lemma slot_eq {h : ℕ} (hl : L.live h = true) (x : ℕ) : L.slot M h x = s.slot L M h x := by
  unfold LSys.slot LSem.slot
  rw [A.col_eq hl]
  by_cases h1 : s.sS L h = true ∧ s.sV L h = x
  · rw [if_pos ((A.sArg_some hl x).2 h1), if_pos (by simp [h1.1, h1.2])]
  · rw [if_neg (fun e => h1 ((A.sArg_some hl x).1 e)), if_neg (by simpa using h1)]

lemma gateAt_iff {b c h : ℕ} :
    L.GateAt M b c h ↔ L.live h = true ∧ s.Y h = b ∧ s.col M h = c := by
  unfold LSys.GateAt
  constructor
  · rintro ⟨hl, hy, hc⟩; exact ⟨hl, by rw [A.Y h hl]; exact hy, by rw [← A.col_eq hl]; exact hc⟩
  · rintro ⟨hl, hy, hc⟩; exact ⟨hl, by rw [← A.Y h hl]; exact hy, by rw [A.col_eq hl]; exact hc⟩

lemma ex_gateAt_iff {b c : ℕ} :
    (∃ h, L.GateAt M b c h) ↔ ∃ h < NG, L.live h = true ∧ s.Y h = b ∧ s.col M h = c := by
  constructor
  · rintro ⟨h, hh⟩; have := A.gateAt_iff.1 hh; exact ⟨h, A.ng h this.1, this⟩
  · rintro ⟨h, -, hh⟩; exact ⟨h, A.gateAt_iff.2 hh⟩

/-- The wire predicate of `DDes`, for a live gate `h` and its argument `x`. -/
def WireS (s : LSem) (L : LSys) (M b φ c h x : ℕ) : Prop :=
  L.live x = true ∧ s.Y x = b ∧ s.Y x + 1 = s.Y h ∧ s.col M x = c + φ ∧
    s.slot L M h x + φ ≤ s.col M x

omit A in
lemma wireS_def {b φ c h x : ℕ} : WireS s L M b φ c h x ↔ (L.live x = true ∧ s.Y x = b ∧
    s.Y x + 1 = s.Y h ∧ s.col M x = c + φ ∧ s.slot L M h x + φ ≤ s.col M x) := Iff.rfl

lemma DDes_iff {b φ c : ℕ} : L.DDes M b φ c ↔ ∃ h < NG, L.live h = true ∧
    ((s.k0 h = true ∧ WireS s L M b φ c h (s.a0 h)) ∨
      (s.k1 h = true ∧ WireS s L M b φ c h (s.a1 h))) := by
  unfold LSys.DDes WireS
  constructor
  · rintro ⟨h, x, hl, hx, hlx, hyb, hyy, hc, hs⟩
    rw [A.col_eq hlx] at hc hs
    rw [A.slot_eq hl] at hs
    rw [← A.Y x hlx] at hyb hyy
    rw [← A.Y h hl] at hyy
    refine ⟨h, A.ng h hl, hl, ?_⟩
    rcases (A.mem_args hl x).1 hx with ⟨hk, rfl⟩ | ⟨hk, rfl⟩
    · exact Or.inl ⟨hk, hlx, hyb, hyy, hc, hs⟩
    · exact Or.inr ⟨hk, hlx, hyb, hyy, hc, hs⟩
  · rintro ⟨h, -, hl, H⟩
    have key : ∀ x, x ∈ (L.g h).args → (L.live x = true ∧ s.Y x = b ∧ s.Y x + 1 = s.Y h ∧
        s.col M x = c + φ ∧ s.slot L M h x + φ ≤ s.col M x) → ∃ x, L.live h = true ∧
        x ∈ (L.g h).args ∧ L.live x = true ∧ L.Y x = b ∧ L.Y x + 1 = L.Y h ∧
        L.col M x = c + φ ∧ L.slot M h x + φ ≤ L.col M x := by
      rintro x hx ⟨hlx, hyb, hyy, hc, hs⟩
      refine ⟨x, hl, hx, hlx, by rw [← A.Y x hlx]; exact hyb,
        by rw [← A.Y x hlx, ← A.Y h hl]; exact hyy, by rw [A.col_eq hlx]; exact hc, ?_⟩
      rw [A.col_eq hlx, A.slot_eq hl]; exact hs
    obtain ⟨x, hx⟩ : ∃ x, x ∈ (L.g h).args ∧ (L.live x = true ∧ s.Y x = b ∧ s.Y x + 1 = s.Y h ∧
        s.col M x = c + φ ∧ s.slot L M h x + φ ≤ s.col M x) := by
      rcases H with ⟨hk, hw⟩ | ⟨hk, hw⟩
      · exact ⟨_, (A.mem_args hl _).2 (Or.inl ⟨hk, rfl⟩), hw⟩
      · exact ⟨_, (A.mem_args hl _).2 (Or.inr ⟨hk, rfl⟩), hw⟩
    exact ⟨h, key x hx.1 hx.2⟩

lemma cval_iff {x : ℕ} (hx : L.live x = false) : cval (L.g x) = true ↔ s.cv x ≠ 0 := by
  rw [A.cv x hx]; cases cval (L.g x) <;> simp

lemma colConst_iff {c : ℕ} : L.colConst M c = true ↔
    ((∃ h < NG, (L.live h = true ∧ s.Y h = 1 ∧ s.col M h = c) ∧ s.sS L h = true ∧
        L.live (s.sV L h) = false ∧ s.cv (s.sV L h) ≠ 0) ∨
      (∃ h < NG, (L.live h = true ∧ s.Y h = 1 ∧ s.col M h = c - 1) ∧ c % 2 = 1 ∧
        s.dS L h = true ∧ L.live (s.dV h) = false ∧ s.cv (s.dV h) ≠ 0)) := by
  unfold LSys.colConst
  rw [decide_eq_true_iff]
  apply or_congr
  · constructor
    · rintro ⟨h, x, hg, hs, hlx, hcv⟩
      have hg' := A.gateAt_iff.1 hg
      obtain ⟨h1, rfl⟩ := (A.sArg_some hg'.1 x).1 hs
      exact ⟨h, A.ng h hg'.1, hg', h1, hlx, (A.cval_iff hlx).1 hcv⟩
    · rintro ⟨h, -, hg, h1, hlx, hcv⟩
      exact ⟨h, _, A.gateAt_iff.2 hg, (A.sArg_some hg.1 _).2 ⟨h1, rfl⟩, hlx,
        (A.cval_iff hlx).2 hcv⟩
  · constructor
    · rintro ⟨h, x, hg, hc, hs, hlx, hcv⟩
      have hg' := A.gateAt_iff.1 hg
      obtain ⟨h1, rfl⟩ := (A.dArg_some hg'.1 x).1 hs
      exact ⟨h, A.ng h hg'.1, hg', hc, h1, hlx, (A.cval_iff hlx).1 hcv⟩
    · rintro ⟨h, -, hg, hc, h1, hlx, hcv⟩
      exact ⟨h, _, A.gateAt_iff.2 hg, hc, (A.dArg_some hg.1 _).2 ⟨h1, rfl⟩, hlx,
        (A.cval_iff hlx).2 hcv⟩

lemma ex_gateR_iff {b c : ℕ} :
    (∃ h, L.GateAt M b c h ∧ L.hasR h = true) ↔
      ∃ h < NG, (L.live h = true ∧ s.Y h = b ∧ s.col M h = c) ∧ s.hasR L h = true := by
  constructor
  · rintro ⟨h, hg, hr⟩
    have hg' := A.gateAt_iff.1 hg
    exact ⟨h, A.ng h hg'.1, hg', by rw [← A.hasR_eq hg'.1]; exact hr⟩
  · rintro ⟨h, -, hg, hr⟩
    exact ⟨h, A.gateAt_iff.2 hg, by rw [A.hasR_eq hg.1]; exact hr⟩

/-- The kind of a node is never an input. -/
lemma node_kind (Cmax c t : ℕ) (i : ℕ) : (L.node M Cmax c t).kind ≠ .input i := by
  unfold LSys.node
  split_ifs with h1 h2 h3 h4 h5 h6 h7 <;> simp [GN.kind, LSys.nS, LSys.nD]
  rcases A.kind _ (Nat.find_spec h5).1 with e | e <;> rw [e] <;> simp

end Agree

end LG

end PathChecking
