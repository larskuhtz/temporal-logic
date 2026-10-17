module

public import RequestProject.ACRound.Circ

/-!
# Gate systems and sandwich queries

A *gate system* is a function `g : ℕ → Gate` such that every gate only reads gates with smaller
index; its values `GS.val` are defined by strong recursion.  The prefix `[g 0, …, g h]` is a
circuit whose output is the value of gate `h` (`GS.eval_prefix`).

Given a *status* `st : ℕ → Option Bool` of partial knowledge about the values, a set of *live*
gates and, for each live gate, a set of *kept* arguments, the *query system* `GS.qsys` keeps the
live gates (restricted to their kept arguments) and replaces every other gate by the constant
`(st h).getD β`.  If the statuses are correct and only arguments with known *neutral* values are
dropped, the query values for `β = false` and `β = true` sandwich the true values of monotone
systems (`GS.sandwich`).
-/

@[expose] public section

namespace PathChecking

namespace GS

/-- The neutral argument value of a gate kind: `true` for `AND`, `false` otherwise. -/
def neutral : GateKind → Bool
  | .and => true
  | _ => false

/-- Value of gate `h` of the system `g`, by strong recursion (arguments `≥ h` read `false`). -/
noncomputable def val (g : ℕ → Gate) : ℕ → Bool :=
  fun h => Nat.strongRec (motive := fun _ => Bool) (fun h ih =>
    (g h).evalFn ∅ [] (fun j => if hj : j < h then ih j hj else false)) h

lemma val_eq (g : ℕ → Gate) (h : ℕ) :
    val g h = (g h).evalFn ∅ [] (fun j => if j < h then val g j else false) := by
  unfold val
  rw [Nat.strongRec_eq]
  congr 1

lemma evalFn_congr (B : Language) (x : Word) (gt : Gate) (f f' : ℕ → Bool)
    (h : ∀ j ∈ gt.args, f j = f' j) : gt.evalFn B x f = gt.evalFn B x f' := by
  have e : gt.args.map f = gt.args.map f' := List.map_congr_left h
  unfold Gate.evalFn
  rw [e]

/-- Gates read only smaller gates. -/
def Ordered (g : ℕ → Gate) : Prop := ∀ h, ∀ j ∈ (g h).args, j < h

lemma val_spec {g : ℕ → Gate} (hg : Ordered g) (h : ℕ) :
    val g h = (g h).evalFn ∅ [] (val g) := by
  rw [val_eq]
  exact evalFn_congr _ _ _ _ _ (fun j hj => by simp [hg h j hj])

/-- The circuit `[g 0, …, g h]`. -/
def pre (g : ℕ → Gate) (h : ℕ) : Circuit := (List.range (h + 1)).map g

@[simp] lemma pre_length (g : ℕ → Gate) (h : ℕ) : (pre g h).length = h + 1 := by simp [pre]

lemma pre_getElem (g : ℕ → Gate) (h i : ℕ) (hi : i < (pre g h).length) : (pre g h)[i] = g i := by
  simp [pre]

/-- **The prefix circuit computes the value of its last gate.** -/
theorem eval_prefix {g : ℕ → Gate} (hg : Ordered g) (h : ℕ) :
    (pre g h).eval ∅ [] = val g h := by
  have hne : pre g h ≠ [] := by simp [pre]
  rw [Circuit.eval_eq_getElem _ _ _ hne]
  have := Circuit.values_spec ∅ [] (pre g h) (val g)
    (fun i hi j hj => by rw [pre_getElem] at hj; exact hg i j hj)
    (fun i hi => by rw [pre_getElem]; exact (val_spec hg i).symm) h (by simp)
  simpa using this

/-! ## Query systems -/

/-- Monotone gates: constants without arguments, `AND` and `OR`. -/
def Mono (g : ℕ → Gate) : Prop :=
  ∀ h, (g h).kind = .and ∨ (g h).kind = .or ∨ ∃ b, (g h).kind = .const b ∧ (g h).args = []

/-- The query system: live gates keep their kind and their kept arguments, all other gates are
constants `(st h).getD β`. -/
def qsys (g : ℕ → Gate) (st : ℕ → Option Bool) (live : ℕ → Bool) (keep : ℕ → ℕ → Bool)
    (β : Bool) (h : ℕ) : Gate :=
  if live h then ⟨(g h).kind, (g h).args.filter (keep h)⟩ else ⟨.const ((st h).getD β), []⟩

lemma qsys_ordered {g : ℕ → Gate} (hg : Ordered g) (st : ℕ → Option Bool) (live : ℕ → Bool)
    (keep : ℕ → ℕ → Bool) (β : Bool) : Ordered (qsys g st live keep β) := by
  intro h j hj
  unfold qsys at hj
  split_ifs at hj with hl
  · exact hg h j (List.mem_of_mem_filter hj)
  · simp at hj

/-- Correct statuses: every known value is the true value. -/
def Correct (g : ℕ → Gate) (st : ℕ → Option Bool) : Prop := ∀ h b, st h = some b → val g h = b

/-- Admissible queries: live gates are `AND`/`OR` gates, and every dropped argument of a live
gate has a known neutral value. -/
structure Admissible (g : ℕ → Gate) (st : ℕ → Option Bool) (live : ℕ → Bool)
    (keep : ℕ → ℕ → Bool) : Prop where
  kind : ∀ h, live h = true → (g h).kind = .and ∨ (g h).kind = .or
  drop : ∀ h, live h = true → ∀ x ∈ (g h).args, keep h x = false →
    st x = some (neutral (g h).kind)

lemma all_mono {l : List ℕ} {f f' : ℕ → Bool} (h : ∀ x ∈ l, f x = true → f' x = true) :
    (l.map f).all id = true → (l.map f').all id = true := by
  simp only [List.all_map, List.all_eq_true, Function.comp, id]
  intro hf x hx; exact h x hx (hf x hx)

lemma any_mono {l : List ℕ} {f f' : ℕ → Bool} (h : ∀ x ∈ l, f x = true → f' x = true) :
    (l.map f).any id = true → (l.map f').any id = true := by
  simp only [List.any_map, List.any_eq_true, Function.comp, id]
  rintro ⟨x, hx, hf⟩; exact ⟨x, hx, h x hx hf⟩

/-- Values of non-live gates in the query system. -/
lemma val_qsys_dead {g : ℕ → Gate} (hg : Ordered g) {st : ℕ → Option Bool} {live : ℕ → Bool}
    {keep : ℕ → ℕ → Bool} {β : Bool} {h : ℕ} (hl : live h = false) :
    val (qsys g st live keep β) h = (st h).getD β := by
  rw [val_spec (qsys_ordered hg st live keep β) h]
  simp [qsys, hl, Gate.evalFn]

/-- **Sandwich lemma.** -/
theorem sandwich {g : ℕ → Gate} (hg : Ordered g) {st : ℕ → Option Bool} {live : ℕ → Bool}
    {keep : ℕ → ℕ → Bool} (hc : Correct g st) (ha : Admissible g st live keep) :
    ∀ h, (val (qsys g st live keep false) h = true → val g h = true) ∧
      (val g h = true → val (qsys g st live keep true) h = true) := by
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    by_cases hl : live h = true
    · rw [val_spec (qsys_ordered hg st live keep false) h, val_spec hg h,
        val_spec (qsys_ordered hg st live keep true) h]
      unfold qsys
      simp only [hl, if_true]
      have hargs : ∀ x ∈ (g h).args, x < h := hg h
      rcases ha.kind h hl with hk | hk
      · simp only [Gate.evalFn, hk, List.all_map, List.all_filter]
        refine ⟨fun H => ?_, fun H => ?_⟩
        · simp only [List.all_eq_true, Function.comp] at H ⊢
          intro x hx
          by_cases hkx : keep h x = true
          · have := H x hx; simp only [hkx, Bool.not_true, Bool.false_or, id] at this
            exact (ih x (hargs x hx)).1 this
          · have := ha.drop h hl x hx (by simpa using hkx)
            rw [hk] at this; exact hc x _ this
        · simp only [List.all_eq_true, Function.comp] at H ⊢
          intro x hx
          by_cases hkx : keep h x = true
          · simp only [hkx, Bool.not_true, Bool.false_or, id]
            exact (ih x (hargs x hx)).2 (H x hx)
          · simp [hkx]
      · simp only [Gate.evalFn, hk, List.any_map, List.any_filter]
        refine ⟨fun H => ?_, fun H => ?_⟩
        · simp only [List.any_eq_true, Function.comp, Bool.and_eq_true, id] at H ⊢
          obtain ⟨x, hx, hkx, hv⟩ := H
          exact ⟨x, hx, (ih x (hargs x hx)).1 hv⟩
        · simp only [List.any_eq_true, Function.comp, Bool.and_eq_true, id] at H ⊢
          obtain ⟨x, hx, hv⟩ := H
          by_cases hkx : keep h x = true
          · exact ⟨x, hx, hkx, (ih x (hargs x hx)).2 hv⟩
          · have := ha.drop h hl x hx (by simpa using hkx)
            rw [hk] at this
            have := hc x _ this
            simp [neutral] at this; rw [this] at hv; exact absurd hv (by simp)
    · have hl' : live h = false := by simpa using hl
      rw [val_qsys_dead hg hl', val_qsys_dead hg hl']
      cases hs : st h with
      | none => simp
      | some b => have := hc h b hs; simp [this]

/-- Decoding of a pair of answers into a status. -/
def dec (a b : Bool) : Option Bool := if a = b then some a else none

/-- **New statuses are correct.** -/
theorem dec_correct {g : ℕ → Gate} (hg : Ordered g) {st : ℕ → Option Bool} {live : ℕ → Bool}
    {keep : ℕ → ℕ → Bool} (hc : Correct g st) (ha : Admissible g st live keep) {h : ℕ} {b : Bool}
    (hd : dec (val (qsys g st live keep false) h) (val (qsys g st live keep true) h) = some b) :
    val g h = b := by
  have hs := sandwich hg hc ha h
  unfold dec at hd
  split_ifs at hd with he
  · cases hd
    cases hb : val g h
    · cases h1 : val (qsys g st live keep false) h
      · rfl
      · exact absurd (hs.1 h1) (by simp [hb])
    · have := hs.2 hb; rw [he]; exact this.symm

/-- For live gates: equal answers on all kept arguments give equal answers. -/
theorem live_eq_of_args {g : ℕ → Gate} {st : ℕ → Option Bool} {live : ℕ → Bool}
    {keep : ℕ → ℕ → Bool} (hg : Ordered g) {h : ℕ} (hl : live h = true)
    (H : ∀ x ∈ (g h).args, keep h x = true →
      val (qsys g st live keep false) x = val (qsys g st live keep true) x) :
    val (qsys g st live keep false) h = val (qsys g st live keep true) h := by
  rw [val_spec (qsys_ordered hg st live keep false) h,
    val_spec (qsys_ordered hg st live keep true) h]
  simp only [qsys, hl, if_true]
  apply evalFn_congr
  intro j hj
  rw [List.mem_filter] at hj
  exact H j hj.1 hj.2

/-- The absorbing argument value of `AND`/`OR`. -/
def absorb (k : GateKind) : Bool := !neutral k

/-- For live gates: an absorbing kept argument with equal answers gives equal answers. -/
theorem live_eq_of_absorb {g : ℕ → Gate} {st : ℕ → Option Bool} {live : ℕ → Bool}
    {keep : ℕ → ℕ → Bool} (hg : Ordered g) (hk : ∀ h, live h = true →
      (g h).kind = .and ∨ (g h).kind = .or) {h : ℕ} (hl : live h = true) {x : ℕ}
    (hx : x ∈ (g h).args) (hkx : keep h x = true)
    (h0 : val (qsys g st live keep false) x = absorb (g h).kind)
    (h1 : val (qsys g st live keep true) x = absorb (g h).kind) :
    val (qsys g st live keep false) h = val (qsys g st live keep true) h := by
  rw [val_spec (qsys_ordered hg st live keep false) h,
    val_spec (qsys_ordered hg st live keep true) h]
  simp only [qsys, hl, if_true]
  have hxf : x ∈ (g h).args.filter (keep h) := List.mem_filter.2 ⟨hx, hkx⟩
  rcases hk h hl with e | e
  · rw [e] at h0 h1
    simp only [absorb, neutral, Bool.not_true] at h0 h1
    have a0 : ((g h).args.filter (keep h) |>.map (val (qsys g st live keep false))).all id =
        false := by
      rw [Bool.eq_false_iff]; intro H
      simp only [List.all_map, List.all_eq_true, Function.comp, id] at H
      have := H x hxf; rw [h0] at this; exact absurd this (by simp)
    have a1 : ((g h).args.filter (keep h) |>.map (val (qsys g st live keep true))).all id =
        false := by
      rw [Bool.eq_false_iff]; intro H
      simp only [List.all_map, List.all_eq_true, Function.comp, id] at H
      have := H x hxf; rw [h1] at this; exact absurd this (by simp)
    simp only [Gate.evalFn, e]; rw [a0, a1]
  · rw [e] at h0 h1
    simp only [absorb, neutral, Bool.not_false] at h0 h1
    have a0 : ((g h).args.filter (keep h) |>.map (val (qsys g st live keep false))).any id =
        true := by
      simp only [List.any_map, List.any_eq_true, Function.comp, id]; exact ⟨x, hxf, h0⟩
    have a1 : ((g h).args.filter (keep h) |>.map (val (qsys g st live keep true))).any id =
        true := by
      simp only [List.any_map, List.any_eq_true, Function.comp, id]; exact ⟨x, hxf, h1⟩
    simp only [Gate.evalFn, e]; rw [a0, a1]

end GS

end PathChecking
