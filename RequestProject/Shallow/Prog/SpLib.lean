module

public import RequestProject.Shallow.Prog.Sp

/-!
# Specifications of the basic routines

The routines of `Nav`, `Emit` and `Tail`, restated with `Sp` and exact frames.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {C : ℕ} {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}

lemma Env.of_frame {W : List (Fin V)} {ρ' : Fin V → ℕ} (hE : Env ts q a C ρ)
    (f : ∀ v, v ∉ W → ρ' v = ρ v) (hN : vN ∉ W) (hL : vL ∉ W) : Env ts q a C ρ' :=
  hE.congr (f _ hN) (f _ hL)

lemma tend_le_succ (ts : List Tok) {p : ℕ} (hp : p ≤ ts.length + 1) : tend ts p ≤ ts.length + 1 :=
  (scan_le _ _ _ _).trans (by omega)

lemma fend_le_succ (ts : List Tok) {p : ℕ} (hp : p ≤ ts.length + 1) : fend ts p ≤ ts.length + 1 :=
  (scan_le _ _ _ _).trans (by omega)

lemma tend_le' (ts : List Tok) {p : ℕ} (hp : p ≤ ts.length) : tend ts p ≤ ts.length :=
  (scan_le _ _ _ _).trans (by omega)

lemma fend_le' (ts : List Tok) {p : ℕ} (hp : p ≤ ts.length) : fend ts p ≤ ts.length :=
  (scan_le _ _ _ _).trans (by omega)

lemma sp_tendP (hE : Env ts q a C ρ) (e : Ex V) :
    Sp (pack (encodeToks ts) q a) C (tendP e) ρ scanW []
      (fun ρ' => ρ' sR = tend ts (e.eval (pack (encodeToks ts) q a) C ρ)) := by
  obtain ⟨h1, h2⟩ := run_tendP hE e
  exact sp_of_silent h2 (tendP_wr e) h1

lemma sp_fendP (hE : Env ts q a C ρ) (e : Ex V) :
    Sp (pack (encodeToks ts) q a) C (fendP e) ρ scanW []
      (fun ρ' => ρ' sR = fend ts (e.eval (pack (encodeToks ts) q a) C ρ)) := by
  obtain ⟨h1, h2⟩ := run_fendP hE e
  exact sp_of_silent h2 (fendP_wr e) h1

lemma sp_isLeafP (hE : Env ts q a C ρ) (e : Ex V)
    (he : e.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length) :
    Sp (pack (encodeToks ts) q a) C (isLeafP e) ρ (vLf :: scanW) []
      (fun ρ' => ρ' vLf = if isLeaf ts (e.eval (pack (encodeToks ts) q a) C ρ) then 1 else 0) := by
  obtain ⟨h1, h2⟩ := run_isLeafP hE e he
  exact sp_of_silent h2 (isLeafP_wr e) h1

/-- Frame of `ctwP`. -/
abbrev ctwW : List (Fin V) := [wC, wL, wD, wI, sR, sP, sC, sD, sI]

lemma sp_ctwP (hE : Env ts q a C ρ) (c ℓ : Ex V)
    (hc : c.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length + 1) :
    Sp (pack (encodeToks ts) q a) C (ctwP c ℓ) ρ ctwW []
      (fun ρ' => ρ' wC = ctw ts (c.eval (pack (encodeToks ts) q a) C ρ)
        (ℓ.eval (pack (encodeToks ts) q a) C
          (Function.update ρ wC (c.eval (pack (encodeToks ts) q a) C ρ)))) := by
  obtain ⟨h1, h2⟩ := run_ctwP hE c ℓ hc
  exact sp_of_silent h2 (ctwP_wr c ℓ) h1

lemma sp_cpP (hE : Env ts q a C ρ) (p : Ex V) :
    Sp (pack (encodeToks ts) q a) C (cpP p) ρ [vT]
      (encodeToks (cp ts (p.eval (pack (encodeToks ts) q a) C ρ))) (fun _ => True) := by
  obtain ⟨ρ', h1, h2⟩ := run_cpP hE p
  exact ⟨ρ', h1, fun v hv => h2 v (by simpa using hv), trivial⟩

lemma sp_emitNat {x : Word} (y z i : Fin V) (hzi : z ≠ i) (hC : 2 ≤ C) :
    Sp x C (emitNat y z i) ρ [z, i] (encodeToks (natToks (ρ y))) (fun _ => True) := by
  obtain ⟨h1, h2⟩ := run_emitNat (w := x) y z i hzi hC ρ
  exact ⟨_, Prod.ext rfl h1, fun v hv => h2 v (by simp at hv; exact hv.1)
    (by simp at hv; exact hv.2), trivial⟩

lemma sp_eraseLoopP (hE : Env ts q a C ρ) (hj : ρ vJ ≤ ts.length) :
    Sp (pack (encodeToks ts) q a) C eraseLoopP ρ eraseW (encodeToks (eraseToks ts (ρ vJ)))
      (fun _ => True) := by
  obtain ⟨ρ', h1, h2⟩ := run_eraseLoopP hE hj
  exact ⟨ρ', h1, h2, trivial⟩

lemma sp_labLoopP (hE : Env ts q a C ρ) (lf : Bool) (hu : ρ vU ≤ ts.length) :
    Sp (pack (encodeToks ts) q a) C (labLoopP lf) ρ labLoopW
      (encodeToks (rng (ρ vU) (tend ts (ρ vU) - ρ vU) (labAt ts lf))) (fun _ => True) := by
  obtain ⟨ρ', h1, h2⟩ := run_labLoopP hE lf hu
  exact ⟨ρ', h1, h2, trivial⟩

/-- Frame of `cntP`. -/
abbrev cntW : List (Fin V) := [vCa, vCr, vCi]

lemma sp_cntP (hE : Env ts q a C ρ) (k : ℕ) (hk : k ≤ 29) (ea en : Ex V)
    (ha : ea.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length + 1)
    (hn : en.eval (pack (encodeToks ts) q a) C (Function.update (Function.update ρ vCa
      (ea.eval (pack (encodeToks ts) q a) C ρ)) vCr 0) ≤ ts.length + 1) :
    Sp (pack (encodeToks ts) q a) C (cntP k ea en) ρ cntW []
      (fun ρ' => ρ' vCr = cnt ts k (ea.eval (pack (encodeToks ts) q a) C ρ)
        (en.eval (pack (encodeToks ts) q a) C (Function.update (Function.update ρ vCa
          (ea.eval (pack (encodeToks ts) q a) C ρ)) vCr 0))) := by
  obtain ⟨h1, h2⟩ := run_cntP hE k hk ea en ha hn
  exact sp_of_silent h2 (cntP_wr k ea en) h1

lemma sp_emitT {x : Word} (y : Fin V) (t : Tok) (h : ρ y = t.code) (hC : 16 ≤ C) :
    Sp x C (emitT y) ρ [] (encodeToks [t]) (fun _ => True) :=
  ⟨ρ, run_emitT y ρ t h hC, fun _ _ => rfl, trivial⟩

end SQ

end PathChecking
