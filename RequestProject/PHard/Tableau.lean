module

public import RequestProject.MCVP.Defs
public import RequestProject.Logspace.SimTM

/-!
# The tableau circuit of a polynomial-time machine

For a Turing machine `M` (with the model of `Complexity.lean`), a time bound
`T = c (n+1)^c` and an input `w` of length `n`, we build a monotone circuit `tabCircuit M c w`
whose value is true iff the configuration of `M` on `w` after `T` steps is halting with
output `[true]`.

The configuration at time `t` is represented by `NE` boolean *entries*. An entry is a triple
`(p, j, z)` with `p ≤ n + 1`, `j ≤ T` and `z < nZ = 4|Q| + |Γ|`:

* if `z < 4|Q|`, the entry says "the input head is at `p`, the work head is at `j`, the state
  is `z / 4` and the (abstracted) output is `z % 4`";
* otherwise (only meaningful for `p = 0`) it says "work cell `j` holds symbol `z - 4|Q|`".

Every entry of the next configuration is an OR, over all pairs `(a, b)` of entries, of
`a ∧ b ∧ K(a, b)` where `K` is a constant depending only on the indices (and on `w`). The
OR is computed by a chain of binary gates. The gate at index `g` is given by the closed
formula `gateFn`, so that it can be produced by a logspace machine gate by gate.

## References

Ladner [Lad75] showed that the circuit value problem is P-complete, using a tableau
construction of this kind. Goldschlager [Gol77] showed that the monotone version (MCVP) is
P-complete. See also Greenlaw–Hoover–Ruzzo [GHR95]. Full entries are in `REFERENCES.md`.
-/

@[expose] public section

namespace PathChecking

namespace PHardness

open Classical MCVPReduction

noncomputable section

variable (M : TM)

/-- Number of values of the third component of an entry. -/
def nZ : ℕ := 4 * M.nQ + M.nG

/-- Code of a state. -/
def qc (q : M.Q) : ℕ := (M.eQ q : ℕ)

/-- State with code `z / 4`. -/
def qOf (z : ℕ) : M.Q := if h : z / 4 < M.nQ then M.eQ.symm ⟨z / 4, h⟩ else M.start

/-- Work symbol with code `z - 4|Q|`. -/
def gOf (z : ℕ) : M.Γ :=
  if h : z - 4 * M.nQ < M.nG then M.eG.symm ⟨z - 4 * M.nQ, h⟩ else M.blank

/-- Abstraction of the output: `[]`, `[false]`, `[true]`, or anything else. -/
def absO : List Bool → ℕ
  | [] => 0
  | [false] => 1
  | [true] => 2
  | _ => 3

/-- Update of the abstracted output. -/
def updO : ℕ → Option Bool → ℕ
  | o, none => o
  | 0, some false => 1
  | 0, some true => 2
  | _, some _ => 3

/-- The effect of one step (halting states do nothing). -/
def res (q : M.Q) (s : InSym) (g : M.Γ) : M.Q × M.Γ × Dir × Dir × Option Bool :=
  if M.halt q then (q, g, .stay, .stay, none) else M.δ q s g

variable (c : ℕ)

/-- The time bound. -/
def Tb (n : ℕ) : ℕ := c * (n + 1) ^ c

/-- Number of entries. -/
def NE (n : ℕ) : ℕ := (n + 2) * (Tb c n + 1) * nZ M

/-- Number of gates per entry (one chain). -/
def Sb (n : ℕ) : ℕ := 2 * NE M c n * NE M c n + 1

/-- Total number of gates. -/
def Nb (n : ℕ) : ℕ := ((Tb c n + 1) * NE M c n + 1) * Sb M c n

/-- Index of the gate holding entry `e` at time `t`. -/
def Vi (n t e : ℕ) : ℕ := (t * NE M c n + e + 1) * Sb M c n - 1

/-- Components of an entry. -/
def eP (n e : ℕ) : ℕ := e / ((Tb c n + 1) * nZ M)
def eJ (n e : ℕ) : ℕ := e / nZ M % (Tb c n + 1)
def eZ (e : ℕ) : ℕ := e % nZ M

/-- The selector constant of the transition. -/
def stepK (w : Word) (pc jc zc pa ja za pb jb zb : ℕ) : Prop :=
  za < 4 * M.nQ ∧ 4 * M.nQ ≤ zb ∧
  if zc < 4 * M.nQ then
    pb = 0 ∧ jb = ja ∧
      pc = min ((res M (qOf M za) (inputSym w pa) (gOf M zb)).2.2.2.1.move pa) (w.length + 1) ∧
      jc = (res M (qOf M za) (inputSym w pa) (gOf M zb)).2.2.1.move ja ∧
      zc = 4 * qc M (res M (qOf M za) (inputSym w pa) (gOf M zb)).1 +
        updO (za % 4) (res M (qOf M za) (inputSym w pa) (gOf M zb)).2.2.2.2
  else
    pc = 0 ∧ pb = 0 ∧ jb = jc ∧
      (if ja = jc then zc - 4 * M.nQ = M.gc (res M (qOf M za) (inputSym w pa) (gOf M zb)).2.1
        else zc = zb)

/-- The selector constant of the output gate. -/
def finalK (a b : ℕ) : Prop :=
  a = b ∧ eZ M a < 4 * M.nQ ∧ M.halt (qOf M (eZ M a)) = true ∧ eZ M a % 4 = 2

/-- The initial value of an entry. -/
def initK (n e : ℕ) : Prop :=
  eP M c n e = 0 ∧ ((eJ M c n e = 0 ∧ eZ M e = 4 * qc M M.start) ∨
    eZ M e = 4 * M.nQ + M.gc M.blank)

/-- The selector of layer `t ≥ 1` (layer `T + 1` is the output gate). -/
def KK (w : Word) (t cc a b : ℕ) : Prop :=
  if t = Tb c w.length + 1 then finalK M a b
  else stepK M w (eP M c w.length cc) (eJ M c w.length cc) (eZ M cc)
    (eP M c w.length a) (eJ M c w.length a) (eZ M a)
    (eP M c w.length b) (eJ M c w.length b) (eZ M b)

/-- The gate with index `g`. -/
def gateFn (w : Word) (g : ℕ) : MGate :=
  if g / Sb M c w.length / NE M c w.length = 0 then
    (if g % Sb M c w.length = Sb M c w.length - 1 then
      .input (decide (initK M c w.length (g / Sb M c w.length % NE M c w.length)))
     else .input false)
  else if g % Sb M c w.length = 0 then .input false
  else if (g % Sb M c w.length - 1) % 2 = 0 then
    .and (Vi M c w.length (g / Sb M c w.length / NE M c w.length - 1)
          ((g % Sb M c w.length - 1) / 2 / NE M c w.length))
      (Vi M c w.length (g / Sb M c w.length / NE M c w.length - 1)
          ((g % Sb M c w.length - 1) / 2 % NE M c w.length))
  else
    .or (g - 2) (if KK M c w (g / Sb M c w.length / NE M c w.length)
        (g / Sb M c w.length % NE M c w.length)
        ((g % Sb M c w.length - 1) / 2 / NE M c w.length)
        ((g % Sb M c w.length - 1) / 2 % NE M c w.length) then g - 1 else g - 2)

/-- **The tableau circuit.** -/
def tabCircuit (w : Word) : List MGate := (List.range (Nb M c w.length)).map (gateFn M c w)

/-- Truth of an entry in a configuration. -/
def ent (n : ℕ) (cf : M.Cfg) (e : ℕ) : Prop :=
  if eZ M e < 4 * M.nQ then
    eP M c n e = cf.inPos ∧ eJ M c n e = cf.workPos ∧ eZ M e = 4 * qc M cf.state + absO cf.output
  else eP M c n e = 0 ∧ eZ M e - 4 * M.nQ = M.gc (cf.tape (eJ M c n e))

/-! ## Arithmetic of indices -/

lemma nZ_pos : 0 < nZ M := by unfold nZ; have := M.nG_pos; omega

lemma NE_pos (n : ℕ) : 0 < NE M c n := by
  unfold NE; have := nZ_pos M; positivity

lemma Sb_pos (n : ℕ) : 0 < Sb M c n := by unfold Sb; omega

lemma NE_eq (n : ℕ) : NE M c n = (n + 2) * ((Tb c n + 1) * nZ M) := by
  unfold NE; ring

/-- Entry with given components. -/
def mkE (n p j z : ℕ) : ℕ := p * ((Tb c n + 1) * nZ M) + j * nZ M + z

lemma mkE_lt {n p j z : ℕ} (hp : p < n + 2) (hj : j < Tb c n + 1) (hz : z < nZ M) :
    mkE M c n p j z < NE M c n := by
  unfold mkE
  rw [NE_eq]
  have h1 : j * nZ M + z < (Tb c n + 1) * nZ M := by
    have : j * nZ M + nZ M ≤ (Tb c n + 1) * nZ M := by nlinarith
    omega
  have h2 : p * ((Tb c n + 1) * nZ M) + (Tb c n + 1) * nZ M ≤ (n + 2) * ((Tb c n + 1) * nZ M) := by
    have := Nat.mul_le_mul_right ((Tb c n + 1) * nZ M) (show p + 1 ≤ n + 2 by omega)
    linarith [add_mul p 1 ((Tb c n + 1) * nZ M)]
  omega

lemma eZ_mkE {n p j z : ℕ} (hz : z < nZ M) : eZ M (mkE M c n p j z) = z := by
  unfold eZ mkE
  rw [show p * ((Tb c n + 1) * nZ M) + j * nZ M + z = z + nZ M * (p * (Tb c n + 1) + j) by ring]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hz]

lemma div_nZ_mkE {n p j z : ℕ} (hz : z < nZ M) :
    mkE M c n p j z / nZ M = p * (Tb c n + 1) + j := by
  unfold mkE
  rw [show p * ((Tb c n + 1) * nZ M) + j * nZ M + z = z + nZ M * (p * (Tb c n + 1) + j) by ring]
  rw [Nat.add_mul_div_left _ _ (nZ_pos M), Nat.div_eq_of_lt hz, zero_add]

lemma eJ_mkE {n p j z : ℕ} (hj : j < Tb c n + 1) (hz : z < nZ M) :
    eJ M c n (mkE M c n p j z) = j := by
  unfold eJ
  rw [div_nZ_mkE M c hz, show p * (Tb c n + 1) + j = j + (Tb c n + 1) * p by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

lemma eP_mkE {n p j z : ℕ} (hj : j < Tb c n + 1) (hz : z < nZ M) :
    eP M c n (mkE M c n p j z) = p := by
  unfold eP
  rw [mul_comm, ← Nat.div_div_eq_div_mul, div_nZ_mkE M c hz,
    show p * (Tb c n + 1) + j = j + (Tb c n + 1) * p by ring,
    Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hj, zero_add]

lemma mkE_components (n e : ℕ) : mkE M c n (eP M c n e) (eJ M c n e) (eZ M e) = e := by
  unfold mkE eP eJ eZ
  rw [mul_comm (Tb c n + 1) (nZ M), ← Nat.div_div_eq_div_mul]
  have h1 := Nat.div_add_mod (e / nZ M) (Tb c n + 1)
  have h2 := Nat.div_add_mod e (nZ M)
  set a := e / nZ M
  set b := a / (Tb c n + 1)
  have : b * (nZ M * (Tb c n + 1)) + a % (Tb c n + 1) * nZ M =
      ((Tb c n + 1) * b + a % (Tb c n + 1)) * nZ M := by ring
  rw [this, h1]; linarith [mul_comm a (nZ M)]

lemma eP_lt {n e : ℕ} (he : e < NE M c n) : eP M c n e < n + 2 := by
  unfold eP
  rw [NE_eq] at he
  exact Nat.div_lt_of_lt_mul (by linarith)

lemma eJ_lt (n e : ℕ) : eJ M c n e < Tb c n + 1 := Nat.mod_lt _ (by omega)

lemma eZ_lt (e : ℕ) : eZ M e < nZ M := Nat.mod_lt _ (nZ_pos M)

/-! ## Codes -/

lemma qc_lt (q : M.Q) : qc M q < M.nQ := M.eQ_lt q

lemma qOf_code (q : M.Q) {o : ℕ} (ho : o < 4) : qOf M (4 * qc M q + o) = q := by
  unfold qOf
  have e : (4 * qc M q + o) / 4 = qc M q := by omega
  rw [dif_pos (by rw [e]; exact qc_lt M q)]
  apply M.eQ.symm_apply_eq.2
  ext; simp only [qc] at e ⊢; exact e

lemma gOf_code (g : M.Γ) {z : ℕ} (hz : z - 4 * M.nQ = M.gc g) : gOf M z = g := by
  unfold gOf
  rw [dif_pos (by rw [hz]; exact M.gc_lt g)]
  apply M.eG.symm_apply_eq.2
  ext; simp [hz, TM.gc]

lemma absO_lt (l : List Bool) : absO l < 4 := by
  unfold absO; split <;> omega

lemma updO_lt {o : ℕ} (ho : o < 4) (x : Option Bool) : updO o x < 4 := by
  unfold updO; split <;> omega

lemma absO_append (l : List Bool) (x : Option Bool) :
    absO (l ++ x.toList) = updO (absO l) x := by
  rcases x with _ | b
  · simp [updO]
  · rcases l with _ | ⟨a, _ | ⟨a', l⟩⟩
    · cases b <;> rfl
    · cases a <;> cases b <;> rfl
    · cases a <;> cases a' <;> cases b <;> rfl

/-! ## One step on entries -/

lemma step_eq (w : Word) (cf : M.Cfg) (hin : cf.inPos ≤ w.length + 1) :
    M.step w cf =
      { state := (res M cf.state (inputSym w cf.inPos) (cf.tape cf.workPos)).1
        inPos := min ((res M cf.state (inputSym w cf.inPos) (cf.tape cf.workPos)).2.2.2.1.move
          cf.inPos) (w.length + 1)
        tape := Function.update cf.tape cf.workPos
          (res M cf.state (inputSym w cf.inPos) (cf.tape cf.workPos)).2.1
        workPos := (res M cf.state (inputSym w cf.inPos) (cf.tape cf.workPos)).2.2.1.move cf.workPos
        output := cf.output ++
          (res M cf.state (inputSym w cf.inPos) (cf.tape cf.workPos)).2.2.2.2.toList } := by
  unfold TM.step res
  by_cases h : M.halt cf.state = true
  · simp only [h, if_true]
    rcases cf with ⟨q, ip, tp, wp, o⟩
    simp only at hin ⊢
    simp [Dir.move, hin]
  · simp only [h, Bool.false_eq_true, if_false]

lemma xz_lt (cf : M.Cfg) : 4 * qc M cf.state + absO cf.output < nZ M := by
  have := qc_lt M cf.state; have := absO_lt cf.output; unfold nZ; omega

lemma tz_lt (g : M.Γ) : 4 * M.nQ + M.gc g < nZ M := by
  have := M.gc_lt g; unfold nZ; omega

lemma step_ent (w : Word) (cf : M.Cfg) (hin : cf.inPos ≤ w.length + 1)
    (hwp : cf.workPos < Tb c w.length) (e : ℕ) :
    (∃ a < NE M c w.length, ∃ b < NE M c w.length,
      stepK M w (eP M c w.length e) (eJ M c w.length e) (eZ M e)
        (eP M c w.length a) (eJ M c w.length a) (eZ M a)
        (eP M c w.length b) (eJ M c w.length b) (eZ M b) ∧
      ent M c w.length cf a ∧ ent M c w.length cf b) ↔ ent M c w.length (M.step w cf) e := by
  rw [step_eq M w cf hin]
  constructor
  · rintro ⟨a, -, b, -, ⟨hza, hzb, hK⟩, hA, hB⟩
    unfold ent at hA hB
    rw [if_pos hza] at hA
    rw [if_neg (by omega)] at hB
    obtain ⟨hpa, hja, hzA⟩ := hA
    obtain ⟨hpb, hzB⟩ := hB
    have hq : qOf M (eZ M a) = cf.state := by rw [hzA]; exact qOf_code M _ (absO_lt _)
    have hzmod : eZ M a % 4 = absO cf.output := by rw [hzA]; have := absO_lt cf.output; omega
    have hg : gOf M (eZ M b) = cf.tape (eJ M c w.length b) := gOf_code M _ hzB
    rw [hq, hg, hpa, hja, hzmod] at hK
    unfold ent
    dsimp only
    by_cases hzc : eZ M e < 4 * M.nQ
    · rw [if_pos hzc] at hK ⊢
      obtain ⟨-, hjb, h1, h2, h3⟩ := hK
      rw [hjb] at h1 h2 h3
      exact ⟨h1, h2, by rw [h3, absO_append]⟩
    · rw [if_neg hzc] at hK ⊢
      obtain ⟨h1, -, hjb, h2⟩ := hK
      refine ⟨h1, ?_⟩
      by_cases hw : cf.workPos = eJ M c w.length e
      · rw [if_pos hw] at h2
        rw [← hw, Function.update_self, h2, hjb, ← hw]
      · rw [if_neg hw] at h2
        rw [Function.update_of_ne (Ne.symm hw), h2, hzB, hjb]
  · intro h
    unfold ent at h
    dsimp only at h
    set n := w.length
    have hqa := xz_lt M cf
    have hA : ent M c n cf (mkE M c n cf.inPos cf.workPos (4 * qc M cf.state + absO cf.output)) := by
      unfold ent
      rw [eZ_mkE M c hqa, eP_mkE M c (by omega) hqa, eJ_mkE M c (by omega) hqa,
        if_pos (by have := absO_lt cf.output; have := qc_lt M cf.state; omega)]
      exact ⟨rfl, rfl, rfl⟩
    have hA' : mkE M c n cf.inPos cf.workPos (4 * qc M cf.state + absO cf.output) < NE M c n :=
      mkE_lt M c (by omega) (by omega) hqa
    have hB : ∀ j, j < Tb c n + 1 → ent M c n cf (mkE M c n 0 j (4 * M.nQ + M.gc (cf.tape j))) := by
      intro j hj
      have hz := tz_lt M (cf.tape j)
      unfold ent
      rw [eZ_mkE M c hz, eP_mkE M c hj hz, eJ_mkE M c hj hz, if_neg (by omega)]
      exact ⟨rfl, by omega⟩
    have hB' : ∀ j, j < Tb c n + 1 → mkE M c n 0 j (4 * M.nQ + M.gc (cf.tape j)) < NE M c n :=
      fun j hj => mkE_lt M c (by omega) hj (tz_lt M _)
    have hzx : (4 * qc M cf.state + absO cf.output) < 4 * M.nQ := by
      have := absO_lt cf.output; have := qc_lt M cf.state; omega
    have hq : qOf M (4 * qc M cf.state + absO cf.output) = cf.state := qOf_code M _ (absO_lt _)
    have hzmod : (4 * qc M cf.state + absO cf.output) % 4 = absO cf.output := by
      have := absO_lt cf.output; omega
    by_cases hzc : eZ M e < 4 * M.nQ
    · rw [if_pos hzc] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hj : cf.workPos < Tb c n + 1 := by omega
      refine ⟨_, hA', _, hB' cf.workPos hj, ?_, hA, hB cf.workPos hj⟩
      have hz := tz_lt M (cf.tape cf.workPos)
      rw [eZ_mkE M c hqa, eP_mkE M c (by omega) hqa, eJ_mkE M c (by omega) hqa,
        eZ_mkE M c hz, eP_mkE M c hj hz, eJ_mkE M c hj hz]
      refine ⟨hzx, by omega, ?_⟩
      rw [if_pos hzc, hq, hzmod, gOf_code M (cf.tape cf.workPos) (by omega)]
      refine ⟨rfl, rfl, h1, h2, ?_⟩
      rw [h3, absO_append]
    · rw [if_neg hzc] at h
      obtain ⟨h1, h2⟩ := h
      have hj := eJ_lt M c n e
      refine ⟨_, hA', _, hB' _ hj, ?_, hA, hB _ hj⟩
      have hz := tz_lt M (cf.tape (eJ M c n e))
      rw [eZ_mkE M c hqa, eP_mkE M c (by omega) hqa, eJ_mkE M c (by omega) hqa,
        eZ_mkE M c hz, eP_mkE M c hj hz, eJ_mkE M c hj hz]
      refine ⟨hzx, by omega, ?_⟩
      rw [if_neg hzc, hq, gOf_code M (cf.tape (eJ M c n e)) (by omega)]
      refine ⟨h1, rfl, rfl, ?_⟩
      by_cases hw : cf.workPos = eJ M c n e
      · rw [if_pos hw]
        rw [← hw, Function.update_self] at h2
        rw [h2, ← hw]
      · rw [if_neg hw]
        rw [Function.update_of_ne (Ne.symm hw)] at h2
        have := eZ_lt M e
        have := M.gc_lt (cf.tape (eJ M c n e))
        omega

lemma final_ent (n : ℕ) (cf : M.Cfg) (hin : cf.inPos ≤ n + 1) (hwp : cf.workPos ≤ Tb c n) :
    (∃ a < NE M c n, ∃ b < NE M c n, finalK M a b ∧ ent M c n cf a ∧ ent M c n cf b) ↔
      (M.halt cf.state = true ∧ absO cf.output = 2) := by
  constructor
  · rintro ⟨a, -, b, -, ⟨rfl, hza, hh, h2⟩, hA, -⟩
    unfold ent at hA
    rw [if_pos hza] at hA
    obtain ⟨-, -, hzA⟩ := hA
    have hq : qOf M (eZ M a) = cf.state := by rw [hzA]; exact qOf_code M _ (absO_lt _)
    rw [hq] at hh
    refine ⟨hh, ?_⟩
    have := absO_lt cf.output
    omega
  · rintro ⟨hh, h2⟩
    have hqa := xz_lt M cf
    have hzx : (4 * qc M cf.state + absO cf.output) < 4 * M.nQ := by
      have := absO_lt cf.output; have := qc_lt M cf.state; omega
    have ha0 : mkE M c n cf.inPos cf.workPos (4 * qc M cf.state + absO cf.output) < NE M c n :=
      mkE_lt M c (by omega) (by omega) hqa
    refine ⟨_, ha0, _, ha0, ⟨rfl, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [eZ_mkE M c hqa]; exact hzx
    · rw [eZ_mkE M c hqa, qOf_code M _ (absO_lt _)]; exact hh
    · rw [eZ_mkE M c hqa]; omega
    all_goals
      unfold ent
      rw [eZ_mkE M c hqa, eP_mkE M c (by omega) hqa, eJ_mkE M c (by omega) hqa, if_pos hzx]
      exact ⟨rfl, rfl, rfl⟩

lemma init_ent (n e : ℕ) : ent M c n M.init e ↔ initK M c n e := by
  unfold ent initK
  simp only [TM.init]
  have := qc_lt M M.start
  by_cases hz : eZ M e < 4 * M.nQ
  · rw [if_pos hz]
    simp only [absO, add_zero]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, Or.inl ⟨h2, h3⟩⟩
    · rintro ⟨h1, ⟨h2, h3⟩ | h2⟩
      · exact ⟨h1, h2, h3⟩
      · omega
  · rw [if_neg hz]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (by omega)⟩
    · rintro ⟨h1, ⟨h2, h3⟩ | h2⟩
      · omega
      · exact ⟨h1, by omega⟩

/-! ## Structure of the circuit -/

lemma gateAt_tab (w : Word) {k : ℕ} (hk : k < Nb M c w.length) :
    gateAt (tabCircuit M c w) k = gateFn M c w k := by
  unfold gateAt tabCircuit
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

lemma val_of_input {C : List MGate} {k : ℕ} {b : Bool} (h : gateAt C k = .input b) :
    val C k = b := by
  rw [val, h]

lemma val_of_and {C : List MGate} {k i j : ℕ} (h : gateAt C k = .and i j) (hi : i < k)
    (hj : j < k) : val C k = (val C i && val C j) := by
  rw [val, h]; simp [hi, hj]

lemma val_of_or {C : List MGate} {k i j : ℕ} (h : gateAt C k = .or i j) (hi : i < k)
    (hj : j < k) : val C k = (val C i || val C j) := by
  rw [val, h]; simp [hi, hj]

lemma idx_div {S N t e r : ℕ} (hS : 0 < S) (hN : 0 < N) (he : e < N) (hr : r < S) :
    ((t * N + e) * S + r) / S = t * N + e ∧ ((t * N + e) * S + r) % S = r ∧
      (t * N + e) / N = t ∧ (t * N + e) % N = e := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (t * N + e) * S + r = r + S * (t * N + e) by ring, Nat.add_mul_div_left _ _ hS,
      Nat.div_eq_of_lt hr, zero_add]
  · rw [show (t * N + e) * S + r = r + S * (t * N + e) by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hr]
  · rw [show t * N + e = e + N * t by ring, Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt he,
      zero_add]
  · rw [show t * N + e = e + N * t by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt he]

lemma Vi_eq (n t e : ℕ) :
    Vi M c n t e = (t * NE M c n + e) * Sb M c n + 2 * NE M c n * NE M c n := by
  unfold Vi; unfold Sb; rw [add_mul (t * NE M c n + e) 1]; omega

lemma Vi_lt (n t e : ℕ) (he : e < NE M c n) :
    Vi M c n t e < (t + 1) * NE M c n * Sb M c n := by
  rw [Vi_eq]
  have h1 : (t * NE M c n + e) * Sb M c n + Sb M c n ≤ (t + 1) * NE M c n * Sb M c n := by
    have := Nat.mul_le_mul_right (Sb M c n) (show t * NE M c n + e + 1 ≤ (t + 1) * NE M c n by
      nlinarith)
    linarith [add_mul (t * NE M c n + e) 1 (Sb M c n)]
  unfold Sb at h1 ⊢; omega

lemma gateFn_layer0 (w : Word) {e : ℕ} (he : e < NE M c w.length) :
    gateFn M c w (Vi M c w.length 0 e) = .input (decide (initK M c w.length e)) := by
  have hS := Sb_pos M c w.length
  have hN := NE_pos M c w.length
  have hr : 2 * NE M c w.length * NE M c w.length < Sb M c w.length := by unfold Sb; omega
  obtain ⟨h1, h2, h3, h4⟩ := idx_div (t := 0) hS hN he hr
  rw [Vi_eq]
  unfold gateFn
  rw [h1, h2, h3, h4, if_pos rfl, if_pos (by unfold Sb; omega)]

lemma gateFn_chain (w : Word) {t e r : ℕ} (ht : 1 ≤ t) (he : e < NE M c w.length)
    (hr : r < Sb M c w.length) :
    gateFn M c w ((t * NE M c w.length + e) * Sb M c w.length + r) =
      if r = 0 then .input false
      else if (r - 1) % 2 = 0 then
        .and (Vi M c w.length (t - 1) ((r - 1) / 2 / NE M c w.length))
          (Vi M c w.length (t - 1) ((r - 1) / 2 % NE M c w.length))
      else .or ((t * NE M c w.length + e) * Sb M c w.length + r - 2)
        (if KK M c w t e ((r - 1) / 2 / NE M c w.length) ((r - 1) / 2 % NE M c w.length)
          then (t * NE M c w.length + e) * Sb M c w.length + r - 1
          else (t * NE M c w.length + e) * Sb M c w.length + r - 2) := by
  have hS := Sb_pos M c w.length
  have hN := NE_pos M c w.length
  obtain ⟨h1, h2, h3, h4⟩ := idx_div (t := t) hS hN he hr
  unfold gateFn
  rw [h1, h2, h3, h4, if_neg (by omega)]

lemma exists_pair (N : ℕ) (P : ℕ → ℕ → Prop) :
    (∃ u < N * N, P (u / N) (u % N)) ↔ ∃ a < N, ∃ b < N, P a b := by
  constructor
  · rintro ⟨u, hu, h⟩
    have hN : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0; simp at hu
      · exact h0
    exact ⟨u / N, Nat.div_lt_of_lt_mul hu, u % N, Nat.mod_lt _ hN, h⟩
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨a * N + b, ?_, ?_⟩
    · have : a * N + N ≤ N * N := by nlinarith
      omega
    · have e1 : (a * N + b) / N = a := by
        rw [show a * N + b = b + N * a by ring, Nat.add_mul_div_left _ _ (by omega),
          Nat.div_eq_of_lt hb, zero_add]
      have e2 : (a * N + b) % N = b := by
        rw [show a * N + b = b + N * a by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
      rw [e1, e2]; exact h

lemma chain_val (w : Word) {t e : ℕ} (ht : 1 ≤ t) (he : e < NE M c w.length)
    (hidx : (t * NE M c w.length + e + 1) * Sb M c w.length ≤ Nb M c w.length) :
    ∀ u ≤ NE M c w.length * NE M c w.length,
      val (tabCircuit M c w) ((t * NE M c w.length + e) * Sb M c w.length + 2 * u) =
        decide (∃ u' < u, KK M c w t e (u' / NE M c w.length) (u' % NE M c w.length) ∧
          val (tabCircuit M c w) (Vi M c w.length (t - 1) (u' / NE M c w.length)) = true ∧
          val (tabCircuit M c w) (Vi M c w.length (t - 1) (u' % NE M c w.length)) = true) := by
  have hS : Sb M c w.length = 2 * (NE M c w.length * NE M c w.length) + 1 := by
    unfold Sb; ring
  have hNN := NE_pos M c w.length
  have hbase : t * NE M c w.length * Sb M c w.length ≤
      (t * NE M c w.length + e) * Sb M c w.length := Nat.mul_le_mul_right _ (by omega)
  have hlt : ∀ r, r < Sb M c w.length →
      (t * NE M c w.length + e) * Sb M c w.length + r < Nb M c w.length := by
    intro r hr
    have : (t * NE M c w.length + e) * Sb M c w.length + Sb M c w.length =
      (t * NE M c w.length + e + 1) * Sb M c w.length := by ring
    omega
  intro u
  induction u with
  | zero =>
    intro _
    simp only [mul_zero, Nat.not_lt_zero, false_and, exists_false, decide_false]
    have h := gateAt_tab M c w (hlt 0 (by omega))
    rw [gateFn_chain M c w ht he (by omega : 0 < Sb M c w.length)] at h
    simp only [if_true] at h
    exact val_of_input h
  | succ u ih =>
    intro hu
    have hu' : u < NE M c w.length * NE M c w.length := by omega
    have hr2 : 2 * u + 2 < Sb M c w.length := by rw [hS]; omega
    have hga := gateAt_tab M c w (hlt (2 * u + 2) hr2)
    rw [gateFn_chain M c w ht he hr2] at hga
    have e1 : (2 * u + 2 - 1) % 2 = 1 := by omega
    have e2 : (2 * u + 2 - 1) / 2 = u := by omega
    rw [if_neg (by omega), e1, e2, if_neg (by omega)] at hga
    have hgb := gateAt_tab M c w (hlt (2 * u + 1) (by omega))
    rw [gateFn_chain M c w ht he (by omega)] at hgb
    have e3 : (2 * u + 1 - 1) % 2 = 0 := by omega
    have e4 : (2 * u + 1 - 1) / 2 = u := by omega
    rw [if_neg (by omega), e3, e4, if_pos rfl] at hgb
    have ha : u / NE M c w.length < NE M c w.length := Nat.div_lt_of_lt_mul hu'
    have hb : u % NE M c w.length < NE M c w.length := Nat.mod_lt _ hNN
    have hva := Vi_lt M c w.length (t - 1) (u / NE M c w.length) ha
    have hvb := Vi_lt M c w.length (t - 1) (u % NE M c w.length) hb
    have ht1 : (t - 1 + 1) = t := by omega
    rw [ht1] at hva hvb
    have hvalb := val_of_and hgb (by omega) (by omega)
    have h22 : (t * NE M c w.length + e) * Sb M c w.length + (2 * u + 2) - 2 =
        (t * NE M c w.length + e) * Sb M c w.length + 2 * u := by omega
    have h21 : (t * NE M c w.length + e) * Sb M c w.length + (2 * u + 2) - 1 =
        (t * NE M c w.length + e) * Sb M c w.length + (2 * u + 1) := by omega
    rw [h22, h21] at hga
    have hrw : (t * NE M c w.length + e) * Sb M c w.length + 2 * (u + 1) =
        (t * NE M c w.length + e) * Sb M c w.length + (2 * u + 2) := by ring
    rw [hrw]
    by_cases hK : KK M c w t e (u / NE M c w.length) (u % NE M c w.length)
    · rw [if_pos hK] at hga
      rw [val_of_or hga (by omega) (by omega), ih (by omega), hvalb]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
      constructor
      · rintro (⟨u', hu', h⟩ | h)
        · exact ⟨u', by omega, h⟩
        · exact ⟨u, by omega, hK, h⟩
      · rintro ⟨u', hu', h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu' with hu' | rfl
        · exact Or.inl ⟨u', hu', h⟩
        · exact Or.inr h.2
    · rw [if_neg hK] at hga
      rw [val_of_or hga (by omega) (by omega), ih (by omega), Bool.or_self]
      apply Bool.eq_iff_iff.2
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨u', hu', h⟩; exact ⟨u', by omega, h⟩
      · rintro ⟨u', hu', h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu' with hu' | rfl
        · exact ⟨u', hu', h⟩
        · exact absurd h.1 hK

lemma val_Vi_succ (w : Word) {t e : ℕ} (ht : 1 ≤ t) (he : e < NE M c w.length)
    (hidx : (t * NE M c w.length + e + 1) * Sb M c w.length ≤ Nb M c w.length) :
    val (tabCircuit M c w) (Vi M c w.length t e) =
      decide (∃ a < NE M c w.length, ∃ b < NE M c w.length, KK M c w t e a b ∧
          val (tabCircuit M c w) (Vi M c w.length (t - 1) a) = true ∧
          val (tabCircuit M c w) (Vi M c w.length (t - 1) b) = true) := by
  rw [Vi_eq, mul_assoc 2, chain_val M c w ht he hidx _ le_rfl]
  congr 1
  exact propext (exists_pair _ (fun a b => KK M c w t e a b ∧
    val (tabCircuit M c w) (Vi M c w.length (t - 1) a) = true ∧
    val (tabCircuit M c w) (Vi M c w.length (t - 1) b) = true))

lemma workPos_le (w : Word) (t : ℕ) : (M.run w t).workPos ≤ t := by
  induction t with
  | zero => simp [TM.run_zero, TM.init]
  | succ t ih =>
    rw [TM.run_succ, step_eq M w _ (TM.inPos_le M w t)]
    simp only
    rcases (res M (M.run w t).state (inputSym w (M.run w t).inPos)
      ((M.run w t).tape (M.run w t).workPos)).2.2.1 with _ | _ | _ <;> simp [Dir.move] <;> omega

lemma layer_idx (n : ℕ) {t e : ℕ} (ht : t ≤ Tb c n) (he : e < NE M c n) :
    (t * NE M c n + e + 1) * Sb M c n ≤ Nb M c n := by
  unfold Nb
  apply Nat.mul_le_mul_right
  nlinarith

lemma Vi_lt_Nb (n : ℕ) {t e : ℕ} (ht : t ≤ Tb c n) (he : e < NE M c n) :
    Vi M c n t e < Nb M c n := by
  have h1 := Vi_lt M c n t e he
  have h2 : (t + 1) * NE M c n * Sb M c n ≤ Nb M c n := by
    unfold Nb
    apply Nat.mul_le_mul_right
    nlinarith
  omega

lemma val_layer (w : Word) :
    ∀ t ≤ Tb c w.length, ∀ e < NE M c w.length,
      val (tabCircuit M c w) (Vi M c w.length t e) = decide (ent M c w.length (M.run w t) e) := by
  intro t
  induction t with
  | zero =>
    intro _ e he
    rw [val_of_input (by rw [gateAt_tab M c w (Vi_lt_Nb M c w.length (Nat.zero_le _) he),
      gateFn_layer0 M c w he]), TM.run_zero]
    exact Bool.eq_iff_iff.2 (by simp [init_ent])
  | succ t ih =>
    intro ht e he
    rw [val_Vi_succ M c w (by omega) he (layer_idx M c w.length ht he)]
    simp only [Nat.add_sub_cancel]
    have hne : t + 1 ≠ Tb c w.length + 1 := by omega
    simp only [KK, hne, if_false]
    rw [TM.run_succ, ← step_ent M c w (M.run w t) (TM.inPos_le M w t)
      (by have := workPos_le M w t; omega) e]
    congr 1
    apply propext
    constructor
    · rintro ⟨a, ha, b, hb, hK, h1, h2⟩
      rw [ih (by omega) a ha] at h1; rw [ih (by omega) b hb] at h2
      exact ⟨a, ha, b, hb, hK, of_decide_eq_true h1, of_decide_eq_true h2⟩
    · rintro ⟨a, ha, b, hb, hK, h1, h2⟩
      refine ⟨a, ha, b, hb, hK, ?_, ?_⟩
      · rw [ih (by omega) a ha]; exact decide_eq_true h1
      · rw [ih (by omega) b hb]; exact decide_eq_true h2

/-! ## Main statements -/

lemma Nb_pos (n : ℕ) : 0 < Nb M c n := by
  unfold Nb; have := Sb_pos M c n; positivity

lemma tabCircuit_length (w : Word) : (tabCircuit M c w).length = Nb M c w.length := by
  simp [tabCircuit]

lemma tabCircuit_ne_nil (w : Word) : tabCircuit M c w ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [tabCircuit_length] at this
  have := Nb_pos M c w.length
  simp_all

lemma gateFn_args (w : Word) (k i j : ℕ)
    (h : gateFn M c w k = .and i j ∨ gateFn M c w k = .or i j) : i < k ∧ j < k := by
  have hS : Sb M c w.length = 2 * (NE M c w.length * NE M c w.length) + 1 := by
    unfold Sb; ring
  have hNN := NE_pos M c w.length
  have hk1 := Nat.div_add_mod k (Sb M c w.length)
  have hk2 := Nat.div_add_mod (k / Sb M c w.length) (NE M c w.length)
  have hr := Nat.mod_lt k (Sb_pos M c w.length)
  by_cases ht : k / Sb M c w.length / NE M c w.length = 0
  · unfold gateFn at h; rw [if_pos ht] at h; split_ifs at h <;> simp at h
  unfold gateFn at h
  rw [if_neg ht] at h
  split_ifs at h with h2 h3
  · simp at h
  · simp only [or_false, MGate.and.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hu : (k % Sb M c w.length - 1) / 2 < NE M c w.length * NE M c w.length := by omega
    have ha := Nat.div_lt_of_lt_mul hu
    have hb := Nat.mod_lt ((k % Sb M c w.length - 1) / 2) hNN
    have hva := Vi_lt M c w.length (k / Sb M c w.length / NE M c w.length - 1) _ ha
    have hvb := Vi_lt M c w.length (k / Sb M c w.length / NE M c w.length - 1) _ hb
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero ht)] at hva hvb
    have hle : k / Sb M c w.length / NE M c w.length * NE M c w.length * Sb M c w.length ≤ k := by
      have : k / Sb M c w.length / NE M c w.length * NE M c w.length ≤ k / Sb M c w.length := by
        rw [mul_comm]; exact Nat.mul_div_le _ _
      calc _ ≤ k / Sb M c w.length * Sb M c w.length := Nat.mul_le_mul_right _ this
        _ ≤ k := Nat.div_mul_le_self _ _
    omega
  all_goals
    simp only [false_or, MGate.or.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : 2 ≤ k % Sb M c w.length := by omega
    have : k % Sb M c w.length ≤ k := Nat.mod_le _ _
    constructor <;> omega

lemma tabCircuit_wellFormed (w : Word) : WellFormed (tabCircuit M c w) := by
  intro k i j h
  by_cases hk : k < Nb M c w.length
  · rw [gateAt_tab M c w hk] at h
    exact gateFn_args M c w k i j h
  · have : gateAt (tabCircuit M c w) k = .input false := by
      unfold gateAt
      rw [List.getD_eq_default _ _ (by rw [tabCircuit_length]; omega)]
    rw [this] at h
    simp at h

theorem tabCircuit_eval (w : Word) :
    eval (tabCircuit M c w) = true ↔
      (M.halt (M.run w (Tb c w.length)).state = true ∧
        absO (M.run w (Tb c w.length)).output = 2) := by
  have hNN := NE_pos M c w.length
  have hlast : (tabCircuit M c w).length - 1 = Vi M c w.length (Tb c w.length + 1) 0 := by
    rw [tabCircuit_length]; unfold Vi Nb; rw [add_zero]
  unfold eval
  rw [hlast, val_Vi_succ M c w (by omega) hNN (by unfold Nb; rw [add_zero])]
  simp only [KK, if_true, Nat.add_sub_cancel, decide_eq_true_eq]
  rw [← final_ent M c w.length (M.run w (Tb c w.length)) (TM.inPos_le M w _)
    (workPos_le M w _)]
  constructor
  · rintro ⟨a, ha, b, hb, hK, h1, h2⟩
    rw [val_layer M c w _ le_rfl a ha] at h1
    rw [val_layer M c w _ le_rfl b hb] at h2
    exact ⟨a, ha, b, hb, hK, of_decide_eq_true h1, of_decide_eq_true h2⟩
  · rintro ⟨a, ha, b, hb, hK, h1, h2⟩
    refine ⟨a, ha, b, hb, hK, ?_, ?_⟩
    · rw [val_layer M c w _ le_rfl a ha]; exact decide_eq_true h1
    · rw [val_layer M c w _ le_rfl b hb]; exact decide_eq_true h2

end

end PHardness

end PathChecking
