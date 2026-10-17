module

public import RequestProject.LTLPath.Phase

/-!
# The whole run of the contraction

Round `0` queries all regions of `S0 0` (all leaves), starting from the statuses in which only
the constant gates are known (`init`).  Then stage `r` (four rounds) goes from `S0 r` to
`S0 (r + 1)`.  After `R` stages with `L ≤ 2 ^ R`, only leaf `0` is left, and every gate of the
root row is known with its correct value (`run_root`).
-/

@[expose] public section

namespace PathChecking

namespace FT

variable {T : FT}

open Classical

/-! ## Arguments of `AND`/`OR` gates -/

lemma gate_idx {c j t : ℕ} (hc : c < T.N) (hj : j < T.Wm) (ht : t ≤ 1) :
    T.gate (T.idx c j t) = T.gateAt c j t := by
  unfold gate
  rw [if_pos (idx_lt_Ng hc hj ht)]
  obtain ⟨a, b, d⟩ := decode_idx (T := T) hc hj ht
  rw [a, b, d]

lemma main_AO_or_leaf {c j : ℕ} (hc : c < T.N) (hnd : T.nd c = true) (hj : j < T.W c) :
    AO (T.gate (T.idx c j 1)) ∨ T.leaf c = true := by
  rw [gate_idx hc (lt_of_lt_of_le hj (W_le_Wm hc)) le_rfl]
  unfold gateAt
  rw [if_pos ⟨hnd, hj⟩]
  rcases kd_cases hnd with e | e | e | e | e
  · right; simp [PT.leaf, hnd, (ar_of_kd hnd).1 e]
  · left; rw [if_neg (by omega), if_pos e]; simp [AO]
  · left; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e]
    exact andOr_AO _ _
  · left; rw [if_neg (by omega), if_neg (by omega), if_pos e]; simp [AO]
  · left; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp only [if_true]
    split_ifs
    · exact andOr_AO _ _
    · simp [AO]

lemma U_AO {p j u : ℕ} (hp : p < T.N) (hnd : T.nd p = true) (e : T.kd p = 5) (hj : j < T.W p)
    (hu : u ≤ 1) (hu' : u = 1 ∨ j + 1 < T.W p) : AO (T.gate (T.idx p j u)) := by
  rw [gate_idx hp (lt_of_lt_of_le hj (W_le_Wm hp)) hu]
  unfold gateAt
  rw [if_pos ⟨hnd, hj⟩, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]
  rcases hu' with rfl | h
  · simp only [if_true]; split_ifs
    · exact andOr_AO _ _
    · simp [AO]
  · split_ifs <;> exact andOr_AO _ _

/-- Every argument of an `AND`/`OR` gate is an `AND`/`OR` gate or a gate of a leaf. -/
theorem gate_arg_cases {h x : ℕ} (hA : AO (T.gate h)) (hx : x ∈ (T.gate h).args) :
    AO (T.gate x) ∨ T.leaf (T.pos x) = true := by
  have hh : h < T.Ng := (gate_AO hA).1
  unfold gate at hA hx
  rw [if_pos hh] at hA hx
  obtain ⟨-, hp, -, -⟩ := idx_decode hh
  set p := T.pos h
  set i := T.ix h
  unfold gateAt at hA hx
  by_cases h1 : T.nd p = true ∧ i < T.W p
  swap
  · rw [if_neg h1] at hA; simp [AO, cF] at hA
  rw [if_pos h1] at hA hx
  have ha := ar_of_kd h1.1
  have ch : ∀ c j, p < c → c < T.N → T.nd c = true → j ≤ i + 1 → x = T.idx c j 1 →
      AO (T.gate x) ∨ T.leaf (T.pos x) = true := by
    intro c j hpc hc hnd hj hx'
    have hjc : j < T.W c := by have := W_add (T := T) hpc; have := T.hℓ; omega
    subst hx'
    rw [(decode_idx hc (lt_of_lt_of_le hjc (W_le_Wm hc)) le_rfl).1]
    exact main_AO_or_leaf hc hnd hjc
  have c1 : ∀ j, T.ar p ≠ 0 → j ≤ i + 1 → x = T.idx (p + 1) j 1 →
      AO (T.gate x) ∨ T.leaf (T.pos x) = true := fun j har hj hx' =>
    ch (p + 1) j (by omega) (child1_lt_N h1.1 har).1 (child1_lt_N h1.1 har).2 hj hx'
  have c2 : T.ar p = 2 → x = T.idx (T.c2 p) i 1 → AO (T.gate x) ∨ T.leaf (T.pos x) = true :=
    fun har hx' => ch (T.c2 p) i (child2_lt_N h1.1 har).1 (child2_lt_N h1.1 har).2.1
      (child2_lt_N h1.1 har).2.2 (by omega) hx'
  rcases kd_cases h1.1 with e | e | e | e | e
  · rw [if_pos e] at hx; split_ifs at hx <;> simp [cF] at hx
  · rw [if_neg (by omega), if_pos e] at hx
    split_ifs at hx
    · simp only [List.mem_singleton] at hx
      exact c1 i (by rw [ha.2.1 (Or.inl e)]; omega) (by omega) hx
    · simp [cF] at hx
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e] at hx
    split_ifs at hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · exact c1 i (by rw [ha.2.2 (Or.inl e)]; omega) (by omega) hx
      · exact c2 (ha.2.2 (Or.inl e)) hx
    · simp [cF] at hx
  · rw [if_neg (by omega), if_neg (by omega), if_pos e] at hx
    split_ifs at hx
    · simp only [List.mem_singleton] at hx
      exact c1 (i + 1) (by rw [ha.2.1 (Or.inr e)]; omega) le_rfl hx
    · simp [cF] at hx
  · have e2 : T.ar p = 2 := ha.2.2 (Or.inr e)
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at hx
    split_ifs at hx with ht hi1 hi1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · exact c2 e2 hx
      · left; rw [hx]; exact U_AO hp h1.1 e h1.2 (by omega) (Or.inr hi1)
    · simp only [List.mem_singleton] at hx
      exact c2 e2 hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · exact c1 i (by omega) (by omega) hx
      · left; rw [hx]; exact U_AO hp h1.1 e hi1 le_rfl (Or.inl rfl)
    · simp [cF] at hx

/-- `AND`/`OR` gates have arguments. -/
theorem gate_args_ne {h : ℕ} (hA : AO (T.gate h)) : (T.gate h).args ≠ [] := by
  unfold gate at hA ⊢
  split_ifs at hA ⊢
  · unfold gateAt at hA ⊢
    split_ifs at hA ⊢ <;> simp_all [AO, cF]
  · simp [AO, cF] at hA

/-! ## Round 0 -/

/-- Initial statuses: only constant gates are known. -/
def init (T : FT) (h : ℕ) : Option Bool :=
  match (T.gate h).kind with
  | .const b => some b
  | _ => none

lemma init_some {h : ℕ} {b : Bool} (e : T.init h = some b) : (T.gate h).kind = .const b := by
  unfold init at e; split at e <;> simp_all

lemma init_ao {h : ℕ} (hA : AO (T.gate h)) : T.init h = none := by
  unfold init; rcases hA with e | e <;> rw [e]

lemma alive_S0_zero {y : ℕ} (hy : T.nd y = true) : T.alive (T.S0 0) y :=
  ⟨T.lix y, ⟨PT.Cont.lt_L hy ⟨le_rfl, PT.lix_lt_fe hy⟩, by simp⟩, le_rfl, PT.lix_lt_fe hy⟩

/-- A leaf row is a frontier row of every gate of a different row (when alive). -/
lemma not_nf_leaf {S : ℕ → Prop} {y c : ℕ} (hne : c ≠ y) (ha : T.alive S c)
    (hl : T.leaf c = true) : ¬ T.NF S y c := by
  rintro (h | h | h)
  · exact hne h
  · exact h ha
  · rw [h.2.1] at hl; exact absurd hl (by simp)

lemma init_inv0 : GS.Correct T.gate T.init ∧ T.ConstKnown T.init ∧ T.Dead (T.S0 0) T.init ∧
    T.Cl (T.S0 0) T.init := by
  refine ⟨fun h b e => ?_, fun h b e => by simp [init, e], fun h hA ha => ?_, ?_⟩
  · rw [GS.val_spec gate_ordered]; simp [Gate.evalFn, init_some e]
  · exact absurd (alive_S0_zero (gate_AO hA).2.1) ha
  intro h hA hu hal
  obtain ⟨-, hnd, hlf, -, hargs⟩ := gate_AO hA
  have key : ∀ x ∈ (T.gate h).args, T.init x ≠ none → ¬ T.NF (T.S0 0) (T.pos h) (T.pos x) := by
    intro x hx hk
    rcases gate_arg_cases hA hx with hxA | hxl
    · exact absurd (init_ao hxA) hk
    · refine not_nf_leaf ?_ (alive_S0_zero (PT.leaf_nd' hxl)) hxl
      intro e; rw [e, hlf] at hxl; exact absurd hxl (by simp)
  refine ⟨fun x hx hnf v hv => absurd hnf (key x hx (by rw [hv]; simp)), ?_⟩
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (gate_args_ne hA)
  refine ⟨x, hx, ?_⟩
  by_cases e : T.init x = none
  · exact Or.inl e
  · exact Or.inr (key x hx e)

/-! ## The run -/

/-- Statuses after round `0` and `r` stages. -/
noncomputable def run (T : FT) : ℕ → ℕ → Option Bool
  | 0 => T.roundB (T.S0 0) T.init
  | r + 1 => T.stage r (T.run r)

theorem run_inv (r : ℕ) : T.Inv (T.S0 r) (T.run r) := by
  induction r with
  | zero =>
    obtain ⟨a, b, c, d⟩ := init_inv0 (T := T)
    exact roundB_inv a b c d
  | succ r ih => exact stage_inv ih

/-- **After enough stages, the gates of the root row are known and correct.** -/
theorem run_root {R : ℕ} (hR : T.L ≤ 2 ^ R) {h : ℕ} (hp : T.pos h = 1) :
    T.run R h = some (GS.val T.gate h) := by
  have hI := run_inv (T := T) R
  have hL : 0 < T.L := by
    have := PT.lix_lt_fe T.nd_one; rw [T.fe_one] at this; unfold PT.L; omega
  have hS : ∀ k, T.S0 R k → k = 0 := by
    rintro k ⟨hk, j, rfl⟩
    rcases j with _ | j
    · simp
    · exfalso; have := Nat.le_mul_of_pos_right (2 ^ R) (show 0 < j + 1 by omega); omega
  have hknown : T.run R h ≠ none := by
    by_cases hA : AO (T.gate h)
    · have hal : T.alive (T.S0 R) (T.pos h) := by
        rw [hp]; exact ⟨0, ⟨hL, dvd_zero _⟩, PT.cont_root hL⟩
      refine hI.lk h hA hal (PT.leaf_down_of_unique (gate_AO hA).2.1 hal ?_)
      intro k1 k2 h1 h2 _ _; rw [hS k1 h1, hS k2 h2]
    · obtain ⟨b, hb⟩ := not_ao_const (gate_mono h) hA
      rw [hI.ck h b hb]; simp
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hknown
  rw [hb, hI.correct h b hb]

end FT

end PathChecking
