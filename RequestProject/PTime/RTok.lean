module

public import RequestProject.MCVP.Loops
public import RequestProject.Logspace.Arith
public import RequestProject.MCVP.Validate
public import RequestProject.CTLStarP.Scan

/-!
# Random access to the tokens of the input

`rtok w p` is the code of the `p`-th token of the input `w` (read as a sequence of 5-bit blocks):
`29` if the input ends before block `p`, `30` if block `p` is not the encoding of a token.
The register program `readTok` computes it.
-/

@[expose] public section

namespace PathChecking

namespace PT

open LS MCVPReduction
open scoped LS

variable {K : ℕ} {w : Word} {B : ℕ}

open Classical in
/-- The code of the token in block `p` of the input. -/
noncomputable def rtok (w : Word) (p : ℕ) : ℕ :=
  if w.length ≤ 5 * p then 29
  else if h : ∃ t : Tok, At w (5 * p + 1) t.bits then h.choose.code else 30

lemma rtok_of_at {p : ℕ} {t : Tok} (h : At w (5 * p + 1) t.bits) : rtok w p = t.code := by
  have hle := h.le
  rw [Tok.bits_length] at hle
  have hex : ∃ t : Tok, At w (5 * p + 1) t.bits := ⟨t, h⟩
  rw [rtok, if_neg (by omega), dif_pos hex, At.tok_eq hex.choose_spec h]

lemma rtok_none {p : ℕ} (hlt : 5 * p < w.length) (h : ∀ t : Tok, ¬ At w (5 * p + 1) t.bits) :
    rtok w p = 30 := by
  have hex : ¬ ∃ t : Tok, At w (5 * p + 1) t.bits := fun ⟨t, ht⟩ => h t ht
  rw [rtok, if_neg (by omega), dif_neg hex]

lemma rtok_end {p : ℕ} (h : w.length ≤ 5 * p) : rtok w p = 29 := by
  rw [rtok, if_pos h]

lemma rtok_le (w : Word) (p : ℕ) : rtok w p ≤ 30 := by
  unfold rtok
  split_ifs with h1 h2
  · omega
  · have := CTLP.Tok.code_lt h2.choose; omega
  · omega

lemma At.prefix_of_append {p : ℕ} {xs ys : List Bool} (h : At w p (xs ++ ys)) : At w p xs :=
  ⟨h.1, h.2.1, (List.prefix_append xs ys).trans h.2.2⟩

/-- On encodings, `rtok` reads the token codes. -/
lemma rtok_encode (ts : List Tok) (p : ℕ) : rtok (encodeToks ts) p = CTLP.tc ts p := by
  by_cases hp : p < ts.length
  · have h1 := At.toks_drop (at_self (encodeToks ts)) (le_of_lt hp)
    rw [List.drop_eq_getElem_cons hp, encodeToks_cons] at h1
    have h2 := At.prefix_of_append h1
    rw [show 1 + 5 * p = 5 * p + 1 by ring] at h2
    rw [rtok_of_at h2]
    simp [CTLP.tc, List.getElem?_eq_getElem hp]
  · rw [rtok_end (by rw [encodeToks_length]; omega)]
    simp [CTLP.tc, List.getElem?_eq_none (show ts.length ≤ p by omega)]

/-! ## The program -/

/-- Five steps to the right. -/
def fwd5 : Stmt K := .right ⨟ .right ⨟ .right ⨟ .right ⨟ .right

lemma ach_fwd5 (σ : St K) (Q : St K → Prop) (hp : σ.pos ≤ w.length + 1)
    (h : Q { σ with pos := min (σ.pos + 5) (w.length + 1) }) : Ach w B fwd5 σ Q := by
  refine ach_seq (ach_right (ach_seq (ach_right (ach_seq (ach_right (ach_seq (ach_right
    (ach_right ?_))))))))
  convert h using 2
  simp only; omega

/-- `t := rtok w c; c := 0` (moves the input head). -/
def readTok (c t : Fin K) : Stmt K :=
  rewind ⨟ whileNZ c (.dec c ⨟ fwd5) ⨟
    .ite (.sym .rend) (setC t 29) (caseTok (fun tk => setC t tk.code) (setC t 30))

lemma ach_readTok (c t : Fin K) (σ : St K) (Q : St K → Prop) (hB : 30 ≤ B)
    (h : ∀ pos, Q { (σ.setReg c 0).setReg t (rtok w (σ.reg c)) with pos := pos }) :
    Ach w B (readTok c t) σ Q := by
  set p := σ.reg c
  refine ach_seq (ach_rewind _ _ (ach_seq ?_))
  refine ach_loop (fun n τ => τ = { σ.setReg c n with pos := min (1 + 5 * (p - n)) (w.length + 1) }
    ∧ n ≤ p) _ ?_ p _ ⟨?_, le_rfl⟩
  · intro n τ ⟨hτ, hn⟩
    subst hτ
    rcases n with _ | n
    · left
      refine ⟨by simp [Cond.eval, St.setReg], ?_⟩
      set q := min (1 + 5 * (p - 0)) (w.length + 1) with hq
      have hq1 : 1 ≤ q := by omega
      by_cases hend : w.length ≤ 5 * p
      · have hsym : inputSym w q = .rend := (inputSym_eq_rend hq1 (by omega)).2 (by omega)
        refine ach_iteT (by simp [Cond.eval, hsym]) (ach_setC _ _ _ _ (by omega) ?_)
        convert h q using 2
        simp [rtok_end hend, St.setReg, p]
      · have hsym : inputSym w q ≠ .rend := fun e => by
          have := (inputSym_eq_rend hq1 (by omega)).1 e; omega
        refine ach_iteF (by simp [Cond.eval, hsym]) ?_
        refine ach_caseTok_fail _ _ _ _ (by simp; omega) (by simp; omega) ?_ ?_
        · intro tk htk
          refine ach_setC _ _ _ _ (by have := CTLP.Tok.code_lt tk; omega) ?_
          have htk' : At w (5 * p + 1) tk.bits := by
            convert htk using 1; simp only [q]; omega
          convert h (q + 5) using 2
          simp [rtok_of_at htk', St.setReg, p]
        · intro pos _ _ hno
          refine ach_setC _ _ _ _ (by omega) ?_
          have hno' : ∀ tk : Tok, ¬ At w (5 * p + 1) tk.bits := by
            intro tk htk; apply hno tk; convert htk using 1; simp only [q]; omega
          convert h pos using 2
          simp [rtok_none (by omega) hno', St.setReg, p]
    · right
      refine ⟨by simp [Cond.eval, St.setReg], ach_seq (ach_dec (ach_fwd5 _ _ ?_ ⟨n, by omega, ?_, by omega⟩))⟩
      · simp
      · simp only [St.setReg, Function.update_self]
        congr 1
        · omega
        · funext x; by_cases hx : x = c <;> simp [Function.update_apply, hx]
  · simp [St.setReg, p]

end PT

end PathChecking
