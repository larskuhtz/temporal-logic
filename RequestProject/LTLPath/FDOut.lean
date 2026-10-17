module

public import RequestProject.LTLPath.FDRound

/-!
# Output of query circuits

Output programs writing the encoding of the gates of a query circuit: tokens (`tokO`), the gates
of the query system (`gateO`) and constant one-gate circuits (`tickO`).
-/

@[expose] public section

namespace PathChecking

/-- The five bits of a token code. -/
def cbits (v : ℕ) : Word := (List.range 5).map fun i => v.testBit i

lemma encodeToks_append (l₁ l₂ : List Tok) :
    encodeToks (l₁ ++ l₂) = encodeToks l₁ ++ encodeToks l₂ := by
  simp [encodeToks]

lemma encodeToks_cons (t : Tok) (l : List Tok) :
    encodeToks (t :: l) = cbits t.code ++ encodeToks l := rfl

/-- Encoding of a gate whose kind is not an input. -/
lemma encode_gate_toks {k : GateKind} (hk : ∀ i, k ≠ .input i) (l : List ℕ) :
    encodeToks (Gate.toks ⟨k, l⟩) =
      cbits (5 + kcode k) ++ (cbits 3 ++ (encodeToks (l.flatMap natToks) ++ cbits 4)) := by
  have e : ∀ j : Fin 24, encodeToks (Gate.toks ⟨k, l⟩) = encodeToks ([Tok.tag j] ++
      (Tok.lpar :: (l.flatMap natToks ++ [Tok.rpar]))) → 5 + kcode k = 5 + j.val →
      encodeToks (Gate.toks ⟨k, l⟩) =
        cbits (5 + kcode k) ++ (cbits 3 ++ (encodeToks (l.flatMap natToks) ++ cbits 4)) := by
    intro j h1 h2
    rw [h1, h2, encodeToks_append, encodeToks_cons, encodeToks_cons, encodeToks_append,
      encodeToks_cons]
    simp [encodeToks, Tok.code]
  rcases k with i | b | _ | _ | _ | _
  · exact absurd rfl (hk i)
  · cases b
    · exact e 1 rfl rfl
    · exact e 2 rfl rfl
  · exact e 3 rfl rfl
  · exact e 4 rfl rfl
  · exact e 5 rfl rfl
  · exact e 6 rfl rfl

lemma filter_take_two (u v n : ℕ) (f : ℕ → Bool) (gg : ℕ → List Tok) :
    (([u, v].take n).filter f).flatMap gg =
      (if 0 < n ∧ f u = true then gg u else []) ++ (if 1 < n ∧ f v = true then gg v else []) := by
  rcases n with _ | _ | n
  · simp
  · by_cases hu : f u = true <;> simp [List.filter, hu]
  · by_cases hu : f u = true <;> by_cases hv : f v = true <;> simp [List.filter, hu, hv]

lemma kcode_const_getD (s : Option Bool) (β : Bool) :
    kcode (.const (s.getD β)) = if oc s = 0 then β.toNat + 1 else oc s := by
  rcases s with _ | b <;> (try cases b) <;> cases β <;> rfl

namespace FD

open FE LL CTLP LTok Classical

variable {x : Word} {Γ : Ctx} {ts : List Tok} {q : ℕ} {a : List Bool} {g : Gl}

lemma DenO.of_eq {o : TO} {v v' : Word} (h : DenO x Γ o v) (e : v = v') : DenO x Γ o v' :=
  e ▸ h

/-- Output of a token with code `c`. -/
def tokO (c : T) : TO :=
  seqO (bitO (modT c (cT 2))) (seqO (bitO (modT (divT c (cT 2)) (cT 2)))
    (seqO (bitO (modT (divT c (cT 4)) (cT 2))) (seqO (bitO (modT (divT c (cT 8)) (cT 2)))
      (bitO (modT (divT c (cT 16)) (cT 2))))))

lemma deno_tok {c : T} {C : ℕ} (hc : Den x Γ c C) : DenO x Γ (tokO c) (cbits C) := by
  have hb : ∀ (k : ℕ) (t : T), Den x Γ t (C / 2 ^ k) →
      DenO x Γ (bitO (modT t (cT 2))) [C.testBit k] := fun k t ht =>
    (deno_bit (den_mod ht (den_c 2))).of_eq (by rw [Nat.testBit_eq_decide_div_mod_eq]; simp)
  have := deno_seq (hb 0 c (by simpa using hc)) (deno_seq (hb 1 _ (den_div hc (den_c 2)))
    (deno_seq (hb 2 _ (den_div hc (den_c 4))) (deno_seq (hb 3 _ (den_div hc (den_c 8)))
      (hb 4 _ (den_div hc (den_c 16))))))
  exact this.of_eq (by simp [cbits, List.range_succ])

/-- Output of a one-gate constant circuit. -/
def tickO (b : T) : TO := seqO (tokO (addT (cT 6) b)) (seqO (tokO (cT 3)) (tokO (cT 4)))

lemma deno_tick {b : T} {B : Bool} (hb : Den x Γ b B.toNat) :
    DenO x Γ (tickO b) (constCirc B).encode := by
  refine (deno_seq (deno_tok (den_add (den_c 6) hb)) (deno_seq (deno_tok (den_c 3))
    (deno_tok (den_c 4)))).of_eq ?_
  have := encode_gate_toks (k := .const B) (fun i => by simp) []
  simp only [Circuit.encode, constCirc, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [this]
  cases B <;> simp [kcode, encodeToks]

/-- Output of gate `h` of the query system. -/
def gateO (g : Gl) (St : T → T) (d0 q0 K tt β h : T) : TO :=
  iteO (liveT g St d0 q0 K tt h)
    (seqO (tokO (addT (cT 5) (kcT g h))) (seqO (tokO (cT 3))
      (seqO (seqO
        (iteO (andT (ltT (cT 0) (naOfT (hcaseT g h)))
          (keepT g St K tt h (a0OfT g (hcaseT g h) (posT g h) (ixT g h))))
          (natO (a0OfT g (hcaseT g h) (posT g h) (ixT g h))) nilO)
        (iteO (andT (ltT (cT 1) (naOfT (hcaseT g h)))
          (keepT g St K tt h (a1OfT g (hcaseT g h) (posT g h) (ixT g h))))
          (natO (a1OfT g (hcaseT g h) (posT g h) (ixT g h))) nilO))
        (tokO (cT 4)))))
    (seqO (tokO (addT (cT 5) (iteT (eqT (stT g K tt h) (cT 0)) (addT β (cT 1)) (stT g K tt h))))
      (seqO (tokO (cT 3)) (tokO (cT 4))))

section

variable {φ : LTL} {p : LassoPath} (hE : Enc ts φ p)
  (hx : x = pack (encodeToks ts) q a) (hg : Gl.Ok x Γ ts g)
include hE hx hg

lemma deno_gate (hq : q ≤ a.length) {St : T → T} {S Qd : ℕ → Prop} (hS : DenS x Γ St S)
    {d0 q0 K tt β h : T} {H0 KV TT H : ℕ} {B : Bool} (hK : Den x Γ K KV) (ht : Den x Γ tt TT)
    (hd0 : Den x Γ d0 ((tokFT hE).down S ((tokFT hE).pos H0)))
    (hq0 : Den x Γ q0 (bv (Qd ((tokFT hE).down S ((tokFT hE).pos H0)) ∧
      (tokFT hE).InR S ((tokFT hE).down S ((tokFT hE).pos H0)) ((tokFT hE).pos H0))))
    (hβ : Den x Γ β B.toNat) (hh : Den x Γ h H) :
    DenO x Γ (gateO g St d0 q0 K tt β h)
      (encodeToks (Gate.toks ((tokFT hE).qsysR S Qd (stA (tokFT hE) KV TT a) H0 B H))) := by
  unfold FT.qsysR GS.qsys
  refine deno_ite_eq (den_live hE hx hg hq hS hK ht hd0 hq0 hh) (fun hl => ?_) (fun hl => ?_)
  · have hl' : (tokFT hE).live S Qd (stA (tokFT hE) KV TT a) H0 H = true := by
      revert hl; cases (tokFT hE).live S Qd (stA (tokFT hE) KV TT a) H0 H <;> simp
    rw [if_pos hl']
    have hao : FT.AO ((tokFT hE).gate H) := by
      have := hl'; simp only [FT.live, decide_eq_true_eq] at this; exact this.2.2.2.1
    rw [encode_gate_toks (fun i => by rcases hao with h' | h' <;> rw [h'] <;> simp)]
    have hc := den_hcase hE hx hg hh
    have hpos := den_pos hE hg hh
    have hix := den_ix hE hg hh
    rw [FT.gate_eq, FT.args_gOfCase, filter_take_two, encodeToks_append]
    rw [← FT.gate_eq]
    have hk0 := den_keep hE hx hg hq hS hK ht hh (den_a0Of hE hx hg hc hpos hix)
    have hk1 := den_keep hE hx hg hq hS hK ht hh (den_a1Of hE hx hg hc hpos hix)
    refine deno_seq (deno_tok (den_add (den_c 5) (den_kc hE hx hg hh))) (deno_seq (deno_tok
      (den_c 3)) (deno_seq (deno_seq ?_ ?_) (deno_tok (den_c 4))))
    · refine deno_ite_eq (den_andB (den_ltB (den_c 0) (den_naOf hc)) hk0) (fun h1 => ?_)
        (fun h1 => ?_)
      · rw [if_pos (by revert h1; simp)]; exact deno_nat (den_a0Of hE hx hg hc hpos hix)
      · rw [if_neg (by revert h1; simp)]; exact deno_nil
    · refine deno_ite_eq (den_andB (den_ltB (den_c 1) (den_naOf hc)) hk1) (fun h1 => ?_)
        (fun h1 => ?_)
      · rw [if_pos (by revert h1; simp)]; exact deno_nat (den_a1Of hE hx hg hc hpos hix)
      · rw [if_neg (by revert h1; simp)]; exact deno_nil
  · have hl' : (tokFT hE).live S Qd (stA (tokFT hE) KV TT a) H0 H = false := by
      revert hl; cases (tokFT hE).live S Qd (stA (tokFT hE) KV TT a) H0 H <;> simp
    rw [if_neg (by rw [hl']; simp), encode_gate_toks (fun i => by simp), kcode_const_getD]
    have hs := den_st hE hx hg hq hK ht hh
    refine deno_seq (deno_tok (den_add (den_c 5) ?_)) (deno_seq (deno_tok (den_c 3))
      ((deno_tok (den_c 4)).of_eq (by simp [encodeToks])))
    refine den_ite_eq (den_eq' hs (den_c 0)) (fun h1 => ?_) (fun h1 => ?_)
    · simp at h1; rw [if_pos h1]; exact den_add hβ (den_c 1)
    · simp at h1; rw [if_neg h1]; exact hs

end

end FD

end PathChecking
