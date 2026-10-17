module

public import RequestProject.LTLPath.Run
public import RequestProject.LTLPath.Depth

/-!
# Shape of the arguments of `AND`/`OR` gates

An argument of an `AND`/`OR` gate `(p, i, t)` is either in the same row (only for `U` nodes:
`main_i → aux_i` and `aux_i → main_{i+1}`), or a `main` gate of a child row at index `i`
(`i + 1` for `X` nodes); the `main` gates of `U` nodes use the second child.
-/

@[expose] public section

namespace PathChecking

namespace FT

variable {T : FT}

open Classical

/-- Shape of an argument `x` of the gate `h`. -/
def ArgShape (T : FT) (h x : ℕ) : Prop :=
  (T.pos x = T.pos h ∧ T.kd (T.pos h) = 5 ∧
    ((ty h = 1 ∧ ty x = 0 ∧ T.ix x = T.ix h) ∨ (ty h = 0 ∧ ty x = 1 ∧ T.ix x = T.ix h + 1))) ∨
  (T.IsChild (T.pos h) (T.pos x) ∧ ty x = 1 ∧
    T.ix x = T.ix h + (if T.kd (T.pos h) = 4 then 1 else 0) ∧
    (T.kd (T.pos h) = 5 → ty h = 1 → T.pos x = T.c2 (T.pos h)))

theorem gate_arg_shape {h x : ℕ} (hA : AO (T.gate h)) (hx : x ∈ (T.gate h).args) :
    T.ArgShape h x := by
  unfold ArgShape
  have hh : h < T.Ng := (gate_AO hA).1
  unfold gate at hA hx
  rw [if_pos hh] at hA hx
  obtain ⟨-, hp, -, ht⟩ := idx_decode hh
  set p := T.pos h
  set i := T.ix h
  set t := ty h
  unfold gateAt at hA hx
  by_cases h1 : T.nd p = true ∧ i < T.W p
  swap
  · rw [if_neg h1] at hA; simp [AO, cF] at hA
  rw [if_pos h1] at hA hx
  have ha := ar_of_kd h1.1
  have hWp := W_le_Wm (T := T) hp
  have dec : ∀ q j u, q < T.N → j < T.Wm → u ≤ 1 → x = T.idx q j u →
      T.pos x = q ∧ T.ix x = j ∧ ty x = u := fun q j u hq hj hu hx' => by
    rw [hx']; exact decode_idx hq hj hu
  have c1 : ∀ j, T.ar p ≠ 0 → j ≤ i + 1 → x = T.idx (p + 1) j 1 →
      T.IsChild p (T.pos x) ∧ T.pos x = p + 1 ∧ ty x = 1 ∧ T.ix x = j := by
    intro j har hj hx'
    have hc := child1_lt_N h1.1 har
    have hjc : j < T.W (p + 1) := by rw [W_succ]; have := T.hℓ; omega
    obtain ⟨a, b, c⟩ := dec (p + 1) j 1 hc.1 (lt_of_lt_of_le hjc (W_le_Wm hc.1)) le_rfl hx'
    exact ⟨by rw [a]; exact ⟨h1.1, Or.inl ⟨by omega, rfl⟩⟩, a, c, b⟩
  have c2 : T.ar p = 2 → x = T.idx (T.c2 p) i 1 →
      T.IsChild p (T.pos x) ∧ T.pos x = T.c2 p ∧ ty x = 1 ∧ T.ix x = i := by
    intro har hx'
    have hc := child2_lt_N h1.1 har
    have hjc : i < T.W (T.c2 p) := by have := W_add (T := T) hc.1; omega
    obtain ⟨a, b, c⟩ := dec _ i 1 hc.2.1 (lt_of_lt_of_le hjc (W_le_Wm hc.2.1)) le_rfl hx'
    exact ⟨by rw [a]; exact ⟨h1.1, Or.inr ⟨har, rfl⟩⟩, a, c, b⟩
  rcases kd_cases h1.1 with e | e | e | e | e
  · rw [if_pos e] at hx; split_ifs at hx <;> simp [cF] at hx
  · rw [if_neg (by omega), if_pos e] at hx
    split_ifs at hx
    · simp only [List.mem_singleton] at hx
      obtain ⟨a, -, b, c⟩ := c1 i (by rw [ha.2.1 (Or.inl e)]; omega) (by omega) hx
      exact Or.inr ⟨a, b, by rw [c, if_neg (by omega)]; rfl, fun hk => by omega⟩
    · simp [cF] at hx
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e] at hx
    split_ifs at hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · obtain ⟨a, -, b, c⟩ := c1 i (by rw [ha.2.2 (Or.inl e)]; omega) (by omega) hx
        exact Or.inr ⟨a, b, by rw [c, if_neg (by omega)]; rfl, fun hk => by omega⟩
      · obtain ⟨a, -, b, c⟩ := c2 (ha.2.2 (Or.inl e)) hx
        exact Or.inr ⟨a, b, by rw [c, if_neg (by omega)]; rfl, fun hk => by omega⟩
    · simp [cF] at hx
  · rw [if_neg (by omega), if_neg (by omega), if_pos e] at hx
    split_ifs at hx
    · simp only [List.mem_singleton] at hx
      obtain ⟨a, -, b, c⟩ := c1 (i + 1) (by rw [ha.2.1 (Or.inr e)]; omega) le_rfl hx
      exact Or.inr ⟨a, b, by rw [c, if_pos e], fun hk => by omega⟩
    · simp [cF] at hx
  · have e2 : T.ar p = 2 := ha.2.2 (Or.inr e)
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at hx
    split_ifs at hx with ht1 hi1 hi1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · obtain ⟨a, b, c, d⟩ := c2 e2 hx
        exact Or.inr ⟨a, c, by rw [d, if_neg (by omega)]; rfl, fun _ _ => b⟩
      · obtain ⟨a, b, c⟩ := dec p i 0 hp (by omega) (by omega) hx
        exact Or.inl ⟨a, e, Or.inl ⟨ht1, c, b⟩⟩
    · simp only [List.mem_singleton] at hx
      obtain ⟨a, b, c, d⟩ := c2 e2 hx
      exact Or.inr ⟨a, c, by rw [d, if_neg (by omega)]; rfl, fun _ _ => b⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · obtain ⟨a, -, b, c⟩ := c1 i (by omega) (by omega) hx
        exact Or.inr ⟨a, b, by rw [c, if_neg (by omega)]; rfl, fun _ h => absurd h ht1⟩
      · obtain ⟨a, b, c⟩ := dec p (i + 1) 1 hp (by omega) le_rfl hx
        exact Or.inl ⟨a, e, Or.inr ⟨by omega, c, b⟩⟩
    · simp [cF] at hx

/-- `AND`/`OR` gates of type `aux` belong to `U` nodes. -/
theorem aux_U {h : ℕ} (hA : AO (T.gate h)) (ht : ty h = 0) : T.kd (T.pos h) = 5 := by
  have hh : h < T.Ng := (gate_AO hA).1
  unfold gate at hA
  rw [if_pos hh] at hA
  unfold gateAt at hA
  by_contra hne
  by_cases h1 : T.nd (T.pos h) = true ∧ T.ix h < T.W (T.pos h)
  · have := T.kd_le _ h1.1
    rw [if_pos h1] at hA
    split_ifs at hA <;> first | omega | simp_all [AO, cF]
  · rw [if_neg h1] at hA; simp [AO, cF] at hA

/-- `AND`/`OR` gates have at most two arguments. -/
theorem gate_args_le (h : ℕ) : (T.gate h).args.length ≤ 2 := by
  unfold gate
  split_ifs
  · unfold gateAt
    split_ifs <;> simp [cF]
  · simp [cF]

end FT

end PathChecking
