module

public import RequestProject.Shallow.Prog.Letter

/-!
# Loops with fuel

`sp_fuel`: a loop `for y < e: if ¬done then body`, where every execution of `body` either sets
the done flag (establishing the postcondition) or strictly increases a measure bounded by the
number of iterations, establishes the postcondition.  This is used to run tail-recursive
functions (with strictly increasing positions) in the loop language.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {x : Word} {C : ℕ}

/-- The loop with fuel. -/
def fuelP (y vd : Fin V) (e : Ex V) (body : Pr V) : Pr V := .loop y e (.ite (.v vd) .skip body)

lemma sp_fuel (y vd : Fin V) (e : Ex V) (body : Pr V) (ρ : Fin V → ℕ) (W : List (Fin V))
    (Inv Post : (Fin V → ℕ) → Prop) (μ : (Fin V → ℕ) → ℕ) (hy : y ∈ W) (hyd : vd ≠ y)
    (hInvY : ∀ r k, Inv r → Inv (Function.update r y k))
    (hμY : ∀ r k, μ (Function.update r y k) = μ r)
    (hFinY : ∀ r k, Post r → Post (Function.update r y k))
    (h0 : (ρ vd ≠ 0 ∧ Post ρ) ∨ (ρ vd = 0 ∧ Inv ρ))
    (hstep : ∀ r, (∀ v, v ∉ W → r v = ρ v) → r vd = 0 → Inv r →
      Sp x C body r W [] (fun r' => (r' vd ≠ 0 ∧ Post r') ∨ (r' vd = 0 ∧ Inv r' ∧ μ r < μ r')))
    (hbound : ∀ r, (∀ v, v ∉ W → r v = ρ v) → Inv r → μ r < e.eval x C ρ) :
    Sp x C (fuelP y vd e body) ρ W [] Post := by
  have key := sp_loop_inv (x := x) (C := C) y e (.ite (.v vd) .skip body) ρ W
    (fun k r => (r vd ≠ 0 ∧ Post r) ∨ (r vd = 0 ∧ Inv r ∧ k ≤ μ r)) hy
    (by rcases h0 with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, h.2, Nat.zero_le _⟩)
    (fun k hk r hfr hI => by
      set r' := Function.update r y k with hr'
      have hfr' : ∀ v, v ∉ W → r' v = ρ v := fun v hv => by
        rw [hr', Function.update_of_ne (ne_of_nmem hv hy), hfr v hv]
      have hdd : r' vd = r vd := Function.update_of_ne hyd _ _
      rcases hI with ⟨hd, hF⟩ | ⟨hd, hInv, hμ⟩
      · exact sp_ite_pos (by simp [hdd, hd]) (sp_skip (Or.inl ⟨by rw [hdd]; exact hd, hFinY r k hF⟩))
      · have hd0 : r' vd = 0 := by rw [hdd, hd]
        refine sp_ite_neg (by simp [hd0]) ?_
        refine (hstep r' hfr' hd0 (hInvY r k hInv)).mono (fun _ h => h) (fun r'' _ h => ?_)
        rcases h with h | ⟨h1, h2, h3⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2, by rw [hμY] at h3; omega⟩)
  refine key.mono (fun _ h => h) (fun r hfr h => ?_)
  rcases h with ⟨-, h⟩ | ⟨-, hInv, hμ⟩
  · exact h
  · have := hbound r hfr hInv
    omega

/-- Two assignments. -/
lemma sp_set2 {a b : Fin V} {e1 e2 : Ex V} {ρ : Fin V → ℕ} {W : List (Fin V)}
    {Q : (Fin V → ℕ) → Prop} (ha : a ∈ W) (hb : b ∈ W)
    (h : Q (Function.update (Function.update ρ a (e1.eval x C ρ)) b
      (e2.eval x C (Function.update ρ a (e1.eval x C ρ))))) :
    Sp x C (.seq (.set a e1) (.set b e2)) ρ W [] Q :=
  sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ a (e1.eval x C ρ))
    ha rfl) (fun r _ hr => by subst hr; exact sp_set hb h) rfl

end SQ

end PathChecking
