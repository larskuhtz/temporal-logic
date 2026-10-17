module

public import RequestProject.LogLang.Gadgets2

/-!
# Compiling expressions of the loop language into register programs

`compE K c e t b` evaluates the expression `e` into register `t`, using the registers `≥ b` as
scratch space; register `c` holds the cap.  Registers are numbered by natural numbers via
`R K : ℕ → Fin (K + 1)`.
-/

@[expose] public section

namespace PathChecking

namespace LL

open LS
open scoped LS

/-- Register number `i` (indices above `K` are clamped). -/
def R (K i : ℕ) : Fin (K + 1) := ⟨min i K, by omega⟩

lemma R_eq_iff {K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) : R K i = R K j ↔ i = j := by
  simp only [R, Fin.ext_iff]; omega

lemma R_ne {K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) (h : i ≠ j) : R K i ≠ R K j :=
  fun e => h ((R_eq_iff hi hj).1 e)

lemma setReg_R {K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) (σ : St (K + 1)) (v : ℕ) :
    (σ.setReg (R K i) v).reg (R K j) = if j = i then v else σ.reg (R K j) := by
  rw [St.setReg_apply]
  by_cases h : j = i
  · subst h; simp
  · rw [if_neg (R_ne hj hi h), if_neg h]

lemma frame_R {K : ℕ} {σ σ' : St (K + 1)} {L : List ℕ} (hL : ∀ j ∈ L, j ≤ K)
    (h : Frame σ σ' (L.map (R K))) {i : ℕ} (hi : i ≤ K) (hn : i ∉ L) :
    σ'.reg (R K i) = σ.reg (R K i) := by
  apply h
  simp only [List.mem_map, not_exists, not_and]
  intro j hj e
  rw [R_eq_iff (hL j hj) hi] at e
  subst e; exact hn hj

lemma nodup_R {K : ℕ} {L : List ℕ} (hL : ∀ j ∈ L, j ≤ K) (hd : L.Nodup) :
    (L.map (R K)).Nodup := by
  refine hd.map_on ?_
  intro x hx y hy e
  exact (R_eq_iff (hL x hx) (hL y hy)).1 e

/-- Gadget for a binary operation: operands in registers `b` and `b + 1`, cap in `c`,
result in `t`; scratch registers `b, …, b + 6`. -/
def opG (K : ℕ) (o : BOp) (t b c : ℕ) : Stmt (K + 1) :=
  match o with
  | .add => clear (R K t) ⨟ addTo (R K b) (R K t) ⨟ addTo (R K (b + 1)) (R K t) ⨟
      clampR (R K t) (R K c) (R K (b + 2)) (R K (b + 3)) (R K (b + 4))
  | .sub => subR (R K b) (R K (b + 1)) ⨟ clear (R K t) ⨟ addTo (R K b) (R K t)
  | .mul => clear (R K t) ⨟ mulR (R K b) (R K (b + 1)) (R K t) (R K (b + 2)) ⨟
      clampR (R K t) (R K c) (R K (b + 2)) (R K (b + 3)) (R K (b + 4))
  | .div => divR (R K b) (R K (b + 1)) (R K (b + 2)) (R K (b + 3)) (R K (b + 4))
      (R K (b + 5)) (R K (b + 6)) ⨟ clear (R K t) ⨟ addTo (R K (b + 2)) (R K t)
  | .mod => divR (R K b) (R K (b + 1)) (R K (b + 2)) (R K (b + 3)) (R K (b + 4))
      (R K (b + 5)) (R K (b + 6)) ⨟ clear (R K t) ⨟ addTo (R K b) (R K t)
  | .lt => subR (R K (b + 1)) (R K b) ⨟ clear (R K t) ⨟
      .ite (.zero (R K (b + 1))) .skip (.inc (R K t))
  | .eq => copy (R K b) (R K (b + 2)) (R K (b + 4)) ⨟ copy (R K (b + 1)) (R K (b + 3)) (R K (b + 4)) ⨟
      subR (R K b) (R K (b + 3)) ⨟ subR (R K (b + 1)) (R K (b + 2)) ⨟ clear (R K t) ⨟
      .ite (.zero (R K b)) (.ite (.zero (R K (b + 1))) (.inc (R K t)) .skip) .skip

/-- Simplification of register reads after updates, deciding index (in)equalities by `omega`. -/
syntax "rs" ("[" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| rs) => `(tactic| ((try simp (disch := omega) [Function.update_apply, R_eq_iff,
      if_pos, if_neg, Cond.eval]) <;> try omega))
  | `(tactic| rs [$xs,*]) => `(tactic| ((try simp (disch := omega) [Function.update_apply,
      R_eq_iff, if_pos, if_neg, Cond.eval, $xs,*]) <;> try omega))

section
variable {w : Word} {B C K : ℕ}

theorem ach_opG (o : BOp) (t b c : ℕ) (σ : St (K + 1)) (Q : St (K + 1) → Prop)
    (htb : t < b) (hcb : c < b) (htc : t ≠ c) (hK : b + 6 ≤ K)
    (ha : σ.reg (R K b) ≤ C) (hb : σ.reg (R K (b + 1)) ≤ C) (hc : σ.reg (R K c) = C)
    (hB : C * C + 2 * C + 1 ≤ B)
    (h : ∀ σ' : St (K + 1), σ'.pos = σ.pos → σ'.out = σ.out →
      σ'.reg (R K t) = o.ap C (σ.reg (R K b)) (σ.reg (R K (b + 1))) →
      (∀ i, i < b → i ≠ t → σ'.reg (R K i) = σ.reg (R K i)) → Q σ') :
    Ach w B (opG K o t b c) σ Q := by
  have htK : t ≤ K := by omega
  have hcK : c ≤ K := by omega
  have hCB : C ≤ B := by nlinarith
  cases o with
  | add =>
    refine ach_seq (ach_clear _ _ _ (ach_seq (ach_addTo _ _ (R_ne (by omega) htK (by omega)) _ _
      (by rs) (ach_seq (ach_addTo _ _ (R_ne (by omega) htK (by omega)) _ _ (by rs) ?_)))))
    refine ach_clampR _ _ _ _ _ (R_ne htK hcK htc) (R_ne htK (by omega) (by omega))
      (R_ne htK (by omega) (by omega)) (R_ne htK (by omega) (by omega))
      (R_ne hcK (by omega) (by omega)) (R_ne hcK (by omega) (by omega))
      (R_ne hcK (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega)) _ _
      (by rs) (by rs) ?_
    intro σ' hp ho hv hfr
    refine h σ' (by simp [hp]) (by simp [ho]) ?_ ?_
    · rw [hv]; rs [BOp.ap]
    · intro i hi hit
      rw [hfr _ (by simp (disch := omega) [R_eq_iff] <;> omega)]
      rs
  | sub =>
    refine ach_seq (ach_subR _ _ (R_ne (by omega) (by omega) (by omega)) _ _ (ach_seq
      (ach_clear _ _ _ (ach_addTo _ _ (R_ne (by omega) htK (by omega)) _ _ (by rs) ?_))))
    refine h _ rfl rfl (by rs [BOp.ap]) (fun i hi hit => by rs)
  | mul =>
    have hm : σ.reg (R K b) * σ.reg (R K (b + 1)) ≤ C * C := Nat.mul_le_mul ha hb
    refine ach_seq (ach_clear _ _ _ (ach_seq (ach_mulR _ _ _ _
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) htK (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) htK (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne htK (by omega) (by omega)) _ _
      (by rs) (by rs) ?_)))
    refine ach_clampR _ _ _ _ _ (R_ne htK hcK htc) (R_ne htK (by omega) (by omega))
      (R_ne htK (by omega) (by omega)) (R_ne htK (by omega) (by omega))
      (R_ne hcK (by omega) (by omega)) (R_ne hcK (by omega) (by omega))
      (R_ne hcK (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega)) _ _
      (by rs) (by rs) ?_
    intro σ' hp ho hv hfr
    refine h σ' (by simp [hp]) (by simp [ho]) ?_ ?_
    · rw [hv]; rs [BOp.ap]
    · intro i hi hit
      rw [hfr _ (by simp (disch := omega) [R_eq_iff] <;> omega)]
      rs
  | div =>
    refine ach_seq (ach_divR _ _ _ _ _ _ _
      (nodup_R (L := [b, b + 1, b + 2, b + 3, b + 4, b + 5, b + 6]) (by simp <;> omega)
        (by simp <;> omega)) _ _ (ha.trans hCB) (hb.trans hCB) (by omega) ?_)
    intro σ' hp ho hq hx hfr
    have hdiv : σ.reg (R K b) / σ.reg (R K (b + 1)) ≤ B :=
      (Nat.div_le_self _ _).trans (ha.trans hCB)
    refine ach_seq (ach_clear _ _ _ (ach_addTo _ _ (R_ne (by omega) htK (by omega)) _ _
      (by rs) ?_))
    refine h _ (by simp [hp]) (by simp [ho]) (by rs [BOp.ap]) (fun i hi hit => ?_)
    rs
    exact hfr _ (by simp (disch := omega) [R_eq_iff] <;> omega)
  | mod =>
    refine ach_seq (ach_divR _ _ _ _ _ _ _
      (nodup_R (L := [b, b + 1, b + 2, b + 3, b + 4, b + 5, b + 6]) (by simp <;> omega)
        (by simp <;> omega)) _ _ (ha.trans hCB) (hb.trans hCB) (by omega) ?_)
    intro σ' hp ho hq hx hfr
    have hmod : σ.reg (R K b) % σ.reg (R K (b + 1)) ≤ B :=
      (Nat.mod_le _ _).trans (ha.trans hCB)
    refine ach_seq (ach_clear _ _ _ (ach_addTo _ _ (R_ne (by omega) htK (by omega)) _ _
      (by rs) ?_))
    refine h _ (by simp [hp]) (by simp [ho]) (by rs [BOp.ap]) (fun i hi hit => ?_)
    rs
    exact hfr _ (by simp (disch := omega) [R_eq_iff] <;> omega)
  | lt =>
    refine ach_seq (ach_subR _ _ (R_ne (by omega) (by omega) (by omega)) _ _ (ach_seq
      (ach_clear _ _ _ (ach_ite ?_))))
    by_cases hlt : σ.reg (R K b) < σ.reg (R K (b + 1))
    · rw [if_neg (by rs)]
      exact ach_inc (by rs) (h _ rfl rfl (by rs [BOp.ap, hlt]) (fun i hi hit => by rs))
    · rw [if_pos (by rs)]
      exact ach_skip (h _ rfl rfl (by rs [BOp.ap, hlt]) (fun i hi hit => by rs))
  | eq =>
    refine ach_seq (ach_copy _ _ _ (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega)) _ _
      (by rs) (ach_seq (ach_copy _ _ _ (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega)) _ _
      (by rs) (ach_seq (ach_subR _ _ (R_ne (by omega) (by omega) (by omega)) _ _
      (ach_seq (ach_subR _ _ (R_ne (by omega) (by omega) (by omega)) _ _
      (ach_seq (ach_clear _ _ _ (ach_ite ?_))))))))))
    by_cases heq : σ.reg (R K b) = σ.reg (R K (b + 1))
    · rw [if_pos (by rs)]
      refine ach_ite ?_
      rw [if_pos (by rs)]
      exact ach_inc (by rs) (h _ rfl rfl (by rs [BOp.ap, heq]) (fun i hi hit => by rs))
    · by_cases hle : σ.reg (R K b) ≤ σ.reg (R K (b + 1))
      · rw [if_pos (by rs)]
        refine ach_ite ?_
        rw [if_neg (by rs)]
        exact ach_skip (h _ rfl rfl (by rs [BOp.ap, heq]) (fun i hi hit => by rs))
      · rw [if_neg (by rs)]
        exact ach_skip (h _ rfl rfl (by rs [BOp.ap, heq]) (fun i hi hit => by rs))

end

/-- Nesting depth of an expression. -/
def Ex.depth {V : ℕ} : Ex V → ℕ
  | .c _ => 0
  | .v _ => 0
  | .len => 0
  | .inp e => e.depth + 1
  | .bin _ a b => max a.depth b.depth + 1

/-- Largest constant in an expression. -/
def Ex.mc {V : ℕ} : Ex V → ℕ
  | .c k => k
  | .v _ => 0
  | .len => 0
  | .inp e => e.mc
  | .bin _ a b => max a.mc b.mc

/-- Compilation of an expression: evaluate `e` into register `t`, with scratch registers `≥ b`
and the cap in register `c`. -/
def compE (K c : ℕ) {V : ℕ} : Ex V → ℕ → ℕ → Stmt (K + 1)
  | .c k, t, b => setC (R K t) k ⨟ clampR (R K t) (R K c) (R K b) (R K (b + 1)) (R K (b + 2))
  | .v x, t, b => copy (R K x) (R K t) (R K b)
  | .len, t, b => lenR (R K t) ⨟ clampR (R K t) (R K c) (R K b) (R K (b + 1)) (R K (b + 2))
  | .inp e, t, b => compE K c e b (b + 1) ⨟ goLend ⨟ moveR (R K b) ⨟ readSym (R K t)
  | .bin o x y, t, b => compE K c x b (b + 2) ⨟ compE K c y (b + 1) (b + 2) ⨟ opG K o t b c

section
variable {w : Word} {B C K : ℕ}

lemma symNum_le (s : InSym) : symNum s ≤ 3 := by
  rcases s with _ | _ | b
  · simp [symNum]
  · simp [symNum]
  · cases b <;> simp [symNum]

lemma BOp.ap_le (o : BOp) (a b : ℕ) (ha : a ≤ C) (hC : 1 ≤ C) : o.ap C a b ≤ C := by
  cases o <;> simp only [BOp.ap]
  · exact min_le_right _ _
  · omega
  · exact min_le_right _ _
  · exact (Nat.div_le_self _ _).trans ha
  · exact (Nat.mod_le _ _).trans ha
  · split_ifs <;> omega
  · split_ifs <;> omega

lemma Ex.eval_le {V : ℕ} (e : Ex V) (ρ : Fin V → ℕ) (hρ : ∀ x, ρ x ≤ C) (hC : 3 ≤ C) :
    e.eval w C ρ ≤ C := by
  induction e with
  | c k => exact min_le_right _ _
  | v x => exact hρ x
  | len => exact min_le_right _ _
  | inp e _ => exact (symNum_le _).trans hC
  | bin o a b iha _ => exact BOp.ap_le o _ _ iha (by omega)

lemma inputSym_min (w : Word) (v : ℕ) : inputSym w (min v (w.length + 1)) = inputSym w v := by
  rcases le_or_gt v (w.length + 1) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h.le]
    unfold inputSym
    rw [if_neg (by omega), if_neg (by omega), List.getElem?_eq_none (by omega),
      List.getElem?_eq_none (by omega)]

theorem ach_compE {V : ℕ} (e : Ex V) : ∀ (t b : ℕ) (σ : St (K + 1)) (Q : St (K + 1) → Prop),
    V < t → t < b → b + 2 * e.depth + 6 ≤ K → σ.reg (R K V) = C →
    (∀ x : Fin V, σ.reg (R K x) ≤ C) → σ.pos ≤ w.length + 1 → e.mc ≤ B → 4 ≤ C →
    C * C + 2 * C + w.length + 1 ≤ B →
    (∀ σ' : St (K + 1), σ'.out = σ.out → σ'.pos ≤ w.length + 1 →
      σ'.reg (R K t) = e.eval w C (fun x => σ.reg (R K x)) →
      (∀ i, i < b → i ≠ t → σ'.reg (R K i) = σ.reg (R K i)) → Q σ') →
    Ach w B (compE K V e t b) σ Q := by
  induction e with
  | c k =>
    intro t b σ Q hVt htb hK hcap hx hpos hmc hC hB h
    have hCB : C ≤ B := by nlinarith
    simp only [Ex.depth] at hK
    simp only [Ex.mc] at hmc
    refine ach_seq (ach_setC _ _ _ _ hmc (ach_clampR _ _ _ _ _ (R_ne (by omega) (by omega)
      (by omega)) (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) _ _ (by rs) (by rs) ?_))
    intro σ' hp ho hv hfr
    refine h σ' (by simp [ho]) (by simp [hp, hpos]) ?_ (fun i hi hit => ?_)
    · rw [hv]; rs [Ex.eval]
    · rw [hfr _ (by simp (disch := omega) [R_eq_iff] <;> omega)]
      rs
  | v x =>
    intro t b σ Q hVt htb hK hcap hx hpos hmc hC hB h
    have hCB : C ≤ B := by nlinarith
    simp only [Ex.depth] at hK
    have hxV := x.isLt
    refine ach_copy _ _ _ (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega)) _ _
      ((hx x).trans hCB) ?_
    refine h _ rfl hpos (by rs [Ex.eval]) (fun i hi hit => by rs)
  | len =>
    intro t b σ Q hVt htb hK hcap hx hpos hmc hC hB h
    have hCB : C ≤ B := by nlinarith
    simp only [Ex.depth] at hK
    refine ach_seq (ach_lenR _ _ _ (by omega) (ach_clampR _ _ _ _ _ (R_ne (by omega) (by omega)
      (by omega)) (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) _ _ (by rs) (by rs) ?_))
    intro σ' hp ho hv hfr
    refine h σ' (by simp [ho]) (by simp [hp]) ?_ (fun i hi hit => ?_)
    · rw [hv]; rs [Ex.eval]
    · rw [hfr _ (by simp (disch := omega) [R_eq_iff] <;> omega)]
      rs
  | inp e ih =>
    intro t b σ Q hVt htb hK hcap hx hpos hmc hC hB h
    simp only [Ex.depth] at hK
    simp only [Ex.mc] at hmc
    refine ach_seq (ih b (b + 1) σ _ (by omega) (by omega) (by omega) hcap hx hpos hmc hC hB ?_)
    intro σ₁ ho1 hp1 hv1 hfr1
    refine ach_seq (ach_goLend _ _ (ach_seq (ach_moveR _ _ _ (by simp) (ach_readSym _ _ _
      (by nlinarith) ?_))))
    refine h _ (by simp [ho1]) (by simp) ?_ (fun i hi hit => ?_)
    · rw [St.setReg_apply, if_pos rfl]
      simp only [St.setReg_pos, zero_add, St.setReg_reg, Function.update_apply, if_true]
      rw [inputSym_min, hv1]
      rfl
    · rs
      exact hfr1 i (by omega) (by omega)
  | bin o x y ihx ihy =>
    intro t b σ Q hVt htb hK hcap hx hpos hmc hC hB h
    simp only [Ex.depth] at hK
    simp only [Ex.mc] at hmc
    refine ach_seq (ihx b (b + 2) σ _ (by omega) (by omega) (by omega) hcap hx hpos
      (le_trans (le_max_left _ _) hmc) hC hB ?_)
    intro σ₁ ho1 hp1 hv1 hfr1
    have hcap1 : σ₁.reg (R K V) = C := by rw [hfr1 V (by omega) (by omega)]; exact hcap
    have hx1 : ∀ z : Fin V, σ₁.reg (R K z) = σ.reg (R K z) := fun z =>
      hfr1 z (by have := z.isLt; omega) (by have := z.isLt; omega)
    refine ach_seq (ihy (b + 1) (b + 2) σ₁ _ (by omega) (by omega) (by omega) hcap1
      (fun z => (hx1 z).trans_le (hx z)) hp1 (le_trans (le_max_right _ _) hmc) hC hB ?_)
    intro σ₂ ho2 hp2 hv2 hfr2
    have hev : ∀ (f : Ex V), f.eval w C (fun z => σ₁.reg (R K z)) =
        f.eval w C (fun z => σ.reg (R K z)) := fun f => by
      congr 1; funext z; exact hx1 z
    have ha : σ₂.reg (R K b) = x.eval w C (fun z => σ.reg (R K z)) := by
      rw [hfr2 b (by omega) (by omega), hv1]
    have hb : σ₂.reg (R K (b + 1)) = y.eval w C (fun z => σ.reg (R K z)) := by
      rw [hv2, hev]
    refine ach_opG (C := C) o t b V σ₂ Q htb (by omega) (by omega) (by omega)
      (by rw [ha]; exact Ex.eval_le _ _ hx (by omega))
      (by rw [hb]; exact Ex.eval_le _ _ hx (by omega))
      (by rw [hfr2 V (by omega) (by omega), hcap1]) (by omega) ?_
    intro σ' hp ho hv hfr
    refine h σ' (by rw [ho, ho2, ho1]) (by rw [hp]; exact hp2) ?_ (fun i hi hit => ?_)
    · rw [hv, ha, hb]; rfl
    · rw [hfr i hi hit, hfr2 i (by omega) (by omega), hfr1 i (by omega) (by omega)]

end

end LL

end PathChecking
