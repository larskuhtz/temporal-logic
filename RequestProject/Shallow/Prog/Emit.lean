module

public import RequestProject.Shallow.Prog.Nav

/-!
# Basic emission routines for the query program

* `run_loop_emit`: a loop whose iterations emit words, with a frame of written variables;
* `emitT`: emit the token whose code is held in a variable;
* `cpP`: emit `cp ts p` (a copy of the token at position `p`, if any).
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {x : Word} {C : ℕ}

lemma seq_eq {s t : Pr V} {ρ ρ1 ρ2 : Fin V → ℕ} {o1 o2 : List Bool}
    (h1 : s.run x C ρ = (ρ1, o1)) (h2 : t.run x C ρ1 = (ρ2, o2)) :
    (Pr.seq s t).run x C ρ = (ρ2, o1 ++ o2) := by
  simp [run_seq, h1, h2]

lemma ne_of_nmem {W : List (Fin V)} {v y : Fin V} (hv : v ∉ W) (hy : y ∈ W) : v ≠ y :=
  fun h => hv (h ▸ hy)

/-- Generic loop rule with a frame `Wr` of written variables. -/
lemma run_loop_emit (y : Fin V) (e : Ex V) (body : Pr V) (ρ : Fin V → ℕ) (Wr : List (Fin V))
    (out : ℕ → List Bool)
    (hbody : ∀ k < e.eval x C ρ, ∀ ρ', (∀ v, v ∉ Wr → ρ' v = ρ v) →
      ∃ ρ'', body.run x C (Function.update ρ' y k) = (ρ'', out k) ∧ ∀ v, v ∉ Wr → ρ'' v = ρ v) :
    ∃ ρ', (Pr.loop y e body).run x C ρ = (ρ', (List.range (e.eval x C ρ)).flatMap out) ∧
      ∀ v, v ∉ Wr → ρ' v = ρ v := by
  have h := run_loop_spec (w := x) (C := C) y e body ρ (fun _ ρ' => ∀ v, v ∉ Wr → ρ' v = ρ v) out
    (fun _ _ => rfl) (fun k hk ρ' hρ' => by
      obtain ⟨ρ'', h1, h2⟩ := hbody k hk ρ' hρ'
      rw [h1]; exact ⟨h2, rfl⟩)
  exact ⟨_, Prod.ext rfl h.2, h.1⟩

lemma run_outToks_eq (ts : List Tok) (ρ : Fin V → ℕ) :
    (outToks ts : Pr V).run x C ρ = (ρ, encodeToks ts) := by simp

/-! ## Emitting tokens -/

/-- token code temporary -/
abbrev vT : Fin V := 23

/-- Emit the token whose code is held in `y`. -/
def emitT (y : Fin V) : Pr V :=
  .seq (.out (.bin .mod (.bin .div (.v y) (.c 1)) (.c 2)))
    (.seq (.out (.bin .mod (.bin .div (.v y) (.c 2)) (.c 2)))
      (.seq (.out (.bin .mod (.bin .div (.v y) (.c 4)) (.c 2)))
        (.seq (.out (.bin .mod (.bin .div (.v y) (.c 8)) (.c 2)))
          (.out (.bin .mod (.bin .div (.v y) (.c 16)) (.c 2))))))

lemma run_emitT (y : Fin V) (ρ : Fin V → ℕ) (t : Tok) (h : ρ y = t.code) (hC : 16 ≤ C) :
    (emitT y).run x C ρ = (ρ, encodeToks [t]) := by
  simp only [emitT, run_seq, run_out, eval_bin, eval_v, eval_c, ap_mod, ap_div]
  simp only [min_eq_left (by omega : 1 ≤ C), min_eq_left (by omega : 2 ≤ C),
    min_eq_left (by omega : 4 ≤ C), min_eq_left (by omega : 8 ≤ C),
    min_eq_left (by omega : 16 ≤ C), h]
  simp only [encodeToks, List.flatMap_cons, List.flatMap_nil, List.append_nil, Tok.bits]
  simp [List.range_succ, Nat.testBit_eq_decide_div_mod_eq]

/-- Emit `cp ts p`. -/
def cpP (p : Ex V) : Pr V :=
  .ite (.bin .lt p (.v vL)) (.seq (.set vT (tokE p)) (emitT vT)) .skip

lemma cp_of_lt {ts : List Tok} {i : ℕ} (h : i < ts.length) : cp ts i = [ts[i]] := by
  simp [cp, List.getElem?_eq_getElem h]

lemma cp_of_ge {ts : List Tok} {i : ℕ} (h : ts.length ≤ i) : cp ts i = [] := by
  simp [cp, List.getElem?_eq_none h]

lemma tc_of_lt {ts : List Tok} {i : ℕ} (h : i < ts.length) : tc ts i = (ts[i]).code := by
  simp [tc, List.getElem?_eq_getElem h]

lemma run_cpP {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}
    (hE : Env ts q a C ρ) (p : Ex V) :
    ∃ ρ', (cpP p).run (pack (encodeToks ts) q a) C ρ =
        (ρ', encodeToks (cp ts (p.eval (pack (encodeToks ts) q a) C ρ))) ∧
      ∀ v, v ≠ vT → ρ' v = ρ v := by
  have hC := hE.len_le
  by_cases hp : p.eval (pack (encodeToks ts) q a) C ρ < ts.length
  · rw [cpP, run_ite_pos (by simp [hE.hL, hp]), run_seq, run_set]
    have htok : (tokE p).eval (pack (encodeToks ts) q a) C ρ =
        (ts[p.eval (pack (encodeToks ts) q a) C ρ]).code := by
      rw [eval_tokE ts q a C ρ p hE.hq hE.hC hE.hN (by omega), tc_of_lt hp]
    rw [htok, run_emitT vT _ (ts[p.eval (pack (encodeToks ts) q a) C ρ]) (by simp) (by omega),
      cp_of_lt hp]
    exact ⟨Function.update ρ vT (ts[p.eval (pack (encodeToks ts) q a) C ρ]).code, rfl,
      fun v hv => Function.update_of_ne hv _ _⟩
  · rw [cpP, run_ite_neg (by simp [hE.hL]; omega), cp_of_ge (by omega)]
    exact ⟨ρ, by simp; rfl, fun _ _ => rfl⟩


/-! ## Loops over position ranges -/

lemma run_rng (y : Fin V) (ne : Ex V) (body : Pr V) (ρ : Fin V → ℕ) (Wr : List (Fin V))
    (A : ℕ) (f : ℕ → List Tok)
    (hbody : ∀ k < ne.eval x C ρ, ∀ ρ', (∀ v, v ∉ Wr → ρ' v = ρ v) →
      ∃ ρ'', body.run x C (Function.update ρ' y k) = (ρ'', encodeToks (f (A + k))) ∧
        ∀ v, v ∉ Wr → ρ'' v = ρ v) :
    ∃ ρ', (Pr.loop y ne body).run x C ρ = (ρ', encodeToks (rng A (ne.eval x C ρ) f)) ∧
      ∀ v, v ∉ Wr → ρ' v = ρ v := by
  obtain ⟨ρ', h1, h2⟩ := run_loop_emit y ne body ρ Wr (fun k => encodeToks (f (A + k))) hbody
  exact ⟨ρ', by rw [h1, rng, encodeToks_flatMap], h2⟩

/-- position temporary of the emitters -/
abbrev vX : Fin V := 24
/-- loop counter of the emission loops -/
abbrev vK : Fin V := 25
/-- length temporary of the emission loops -/
abbrev vE : Fin V := 26
/-- `j` (formula position of the query) -/
abbrev vJ : Fin V := 27

lemma eval_tokE_v {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}
    (hE : Env ts q a C ρ) (y : Fin V) (hy : ρ y ≤ ts.length + 1) :
    (tokE (.v y)).eval (pack (encodeToks ts) q a) C ρ = tc ts (ρ y) := by
  have := hE.len_le
  rw [eval_tokE ts q a C ρ _ hE.hq hE.hC hE.hN (by simp; omega)]; rfl

/-! ## Erasing -/

/-- Emit `eraseAt ts p`. -/
def eraseP (p : Ex V) : Pr V :=
  .seq (.set vX p) (.ite (.bin .eq (tokE (.v vX)) (.c 11)) .skip (cpP (.v vX)))

lemma run_eraseP {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}
    (hE : Env ts q a C ρ) (p : Ex V) (hp : p.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length + 1) :
    ∃ ρ', (eraseP p).run (pack (encodeToks ts) q a) C ρ =
        (ρ', encodeToks (eraseAt ts (p.eval (pack (encodeToks ts) q a) C ρ))) ∧
      ∀ v, v ≠ vX → v ≠ vT → ρ' v = ρ v := by
  have hC := hE.len_le
  unfold eraseP
  rw [run_seq, run_set]
  generalize p.eval (pack (encodeToks ts) q a) C ρ = pv at hp ⊢
  have hE1 : Env ts q a C (Function.update ρ vX pv) :=
    hE.congr (Function.update_of_ne (by decide) _ _) (Function.update_of_ne (by decide) _ _)
  have ht : (tokE (.v vX)).eval (pack (encodeToks ts) q a) C (Function.update ρ vX pv) =
      tc ts pv := by
    rw [eval_tokE_v hE1 vX (by simp; omega)]; simp
  by_cases h11 : tc ts pv = 11
  · rw [run_ite_pos (by simp [ht, h11, min_eq_left (show 11 ≤ C by omega)])]
    refine ⟨Function.update ρ vX pv, ?_, fun v h1 _ => Function.update_of_ne h1 _ _⟩
    simp [eraseAt, h11]; rfl
  · rw [run_ite_neg (by simp [ht, h11, min_eq_left (show 11 ≤ C by omega)])]
    obtain ⟨ρ', h1, h2⟩ := run_cpP hE1 (.v vX)
    refine ⟨ρ', ?_, fun v hv1 hv2 => by rw [h2 v hv2, Function.update_of_ne hv1]⟩
    simp only [List.nil_append, h1, eraseAt, if_neg h11]
    simp

/-- Emit `eraseToks ts j` (`j` in `vJ`). -/
def eraseLoopP : Pr V :=
  .seq (fendP (.v vJ)) (.seq (.set vE (.bin .sub (.v sR) (.v vJ)))
    (.loop vK (.v vE) (eraseP (.bin .add (.v vJ) (.v vK)))))

/-- Variables written by `eraseLoopP`. -/
def eraseW : List (Fin V) := [sR, sP, sC, sD, sI, vE, vK, vX, vT]

lemma run_eraseLoopP {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}
    (hE : Env ts q a C ρ) (hj : ρ vJ ≤ ts.length) :
    ∃ ρ', eraseLoopP.run (pack (encodeToks ts) q a) C ρ =
        (ρ', encodeToks (eraseToks ts (ρ vJ))) ∧ ∀ v, v ∉ eraseW → ρ' v = ρ v := by
  have hC := hE.len_le
  obtain ⟨f1, f2⟩ := run_fendP hE (.v vJ)
  set ρ1 := ((fendP (.v vJ)).run (pack (encodeToks ts) q a) C ρ).1
  have g1 : ∀ v, v ∉ eraseW → ρ1 v = ρ v := fun v hv =>
    frame_of_sub (fendP_wr _) ρ v (fun h => hv (by simp [eraseW] at h ⊢; omega))
  have hfe : fend ts (ρ vJ) ≤ ts.length := (scan_le _ _ _ _).trans (by omega)
  have hJ1 : ρ1 vJ = ρ vJ := g1 vJ (by decide)
  set ρ2 := Function.update ρ1 vE (fend ts (ρ vJ) - ρ vJ)
  have r2 : (Pr.set vE (.bin .sub (.v sR) (.v vJ))).run (pack (encodeToks ts) q a) C ρ1 =
      (ρ2, []) := by simp [f1, hJ1, ρ2]
  have g2 : ∀ v, v ∉ eraseW → ρ2 v = ρ v := fun v hv => by
    simp only [ρ2]; rw [Function.update_of_ne (ne_of_nmem hv (by decide)), g1 v hv]
  obtain ⟨ρ3, r3, g3⟩ := run_rng (x := pack (encodeToks ts) q a) (C := C) vK (.v vE)
    (eraseP (.bin .add (.v vJ) (.v vK))) ρ2 eraseW (ρ vJ) (eraseAt ts) (fun k hk ρ' hρ' => by
      simp only [eval_v, ρ2, Function.update_self] at hk
      have hE' : Env ts q a C (Function.update ρ' vK k) := hE.congr
        (by rw [Function.update_of_ne (by decide), hρ' _ (by decide), g2 _ (by decide)])
        (by rw [Function.update_of_ne (by decide), hρ' _ (by decide), g2 _ (by decide)])
      have hev : (Ex.bin .add (.v vJ) (.v vK) : Ex V).eval (pack (encodeToks ts) q a) C
          (Function.update ρ' vK k) = ρ vJ + k := by
        simp only [eval_bin, ap_add, eval_v, Function.update_self,
          Function.update_of_ne (show vJ ≠ vK by decide), hρ' vJ (by decide), g2 vJ (by decide)]
        exact min_eq_left (by omega)
      obtain ⟨ρ'', h1, h2⟩ := run_eraseP hE' _ (by rw [hev]; omega)
      rw [hev] at h1
      refine ⟨ρ'', h1, fun v hv => ?_⟩
      rw [h2 v (ne_of_nmem hv (by decide)) (ne_of_nmem hv (by decide)),
        Function.update_of_ne (ne_of_nmem hv (by decide)), hρ' v hv, g2 v hv])
  refine ⟨ρ3, ?_, fun v hv => by rw [g3 v hv, g2 v hv]⟩
  have r1 : (fendP (.v vJ)).run (pack (encodeToks ts) q a) C ρ = (ρ1, []) := Prod.ext rfl f2
  unfold eraseLoopP
  rw [seq_eq r1 (seq_eq r2 r3)]
  simp [ρ2, eraseToks]

end SQ

end PathChecking
