module

public import RequestProject.LTLPath.FDGate
public import RequestProject.LTLPath.FDPow
public import RequestProject.LTLPath.Sequence

/-!
# Terms for the contraction schedule

Sets of leaf indices are passed as term builders (`DenS`).  Terms for leaf containment, the
stage sets `S0`, `S1`, the removed leaves `DL`, `DR`, compressed parents, the round sets `rS`,
`rQ`, and the region structure (`alive`, `down`, `InR`, `NF`).
-/

@[expose] public section

namespace PathChecking

namespace FD

open FE LL CTLP LTok Classical

variable {x : Word} {Γ : Ctx} {ts : List Tok} {q : ℕ} {a : List Bool} {g : Gl}

/-- `St` computes the set `S`. -/
def DenS (x : Word) (Γ : Ctx) (St : T → T) (S : ℕ → Prop) : Prop :=
  ∀ Γ', Γ ⊆ Γ' → ∀ t v, Den x Γ' t v → Den x Γ' (St t) (bv (S v))

lemma DenS.mono {St : T → T} {S : ℕ → Prop} (h : DenS x Γ St S) {Γ' : Ctx} (hΓ : Γ ⊆ Γ') :
    DenS x Γ' St S := fun Γ'' h' t v ht => h Γ'' (hΓ.trans h') t v ht

lemma DenS.app {St : T → T} {S : ℕ → Prop} (h : DenS x Γ St S) {t : T} {v : ℕ}
    (ht : Den x Γ t v) : Den x Γ (St t) (bv (S v)) := h Γ (List.Subset.refl _) t v ht

lemma DenS.congr {St : T → T} {S S' : ℕ → Prop} (h : DenS x Γ St S) (e : ∀ v, S v ↔ S' v) :
    DenS x Γ St S' := fun Γ' hΓ t v ht => (h Γ' hΓ t v ht).of_eq (bv_congr (e v))

/-! ## Terms -/

/-- Leaf containment. -/
def ContT (g : Gl) (y k : T) : T := andT (leT (lixT g y) k) (ltT k (lixT g (fendT y)))

/-- Stage leaves (with the capped power of two `d`). -/
def S0T (g : Gl) (d k : T) : T := andT (ltT k g.L) (eqT (modT k d) (cT 0))

/-- Odd leaves. -/
def Odd2T (d k : T) : T := eqT (modT (divT k d) (cT 2)) (cT 1)

/-- Compressed parent. -/
def parT (g : Gl) (St : T → T) (k : T) : T :=
  fgT g.F fun z => andT (tndT g z) (andT (ContT g z k)
    (exT g.L fun k' => andT (St k') (andT (neT k' k) (ContT g z k'))))

/-- Odd leaves below the first child of their compressed parent. -/
def DLT (g : Gl) (d k : T) : T :=
  andT (S0T g d k) (andT (Odd2T d k) (ContT g (addT (parT g (S0T g d) k) (cT 1)) k))

/-- Leaves after the first substep. -/
def S1T (g : Gl) (d k : T) : T := andT (S0T g d k) (notT (DLT g d k))

/-- The remaining odd leaves. -/
def DRT (g : Gl) (d k : T) : T := andT (S1T g d k) (Odd2T d k)

/-- Compressed parents of the leaves of `D`. -/
def PSetT (g : Gl) (St Dt : T → T) (p : T) : T :=
  exT g.L fun k => andT (Dt k) (eqT (parT g St k) p)

/-- Alive nodes. -/
def aliveT (g : Gl) (St : T → T) (y : T) : T := exT g.L fun k => andT (St k) (ContT g y k)

/-- Ancestors. -/
def AncT (g : Gl) (y z : T) : T :=
  andT (tndT g y) (andT (tndT g z) (andT (leT y z) (ltT z (fendT y))))

/-- Same leaves of `S`. -/
def SameST (g : Gl) (St : T → T) (y z : T) : T :=
  allT g.L fun k => orT (notT (St k)) (eqT (ContT g y k) (ContT g z k))

/-- The deepest descendant with the same leaves. -/
def downT (g : Gl) (St : T → T) (y : T) : T :=
  fgT g.F fun z => andT (AncT g y z) (SameST g St y z)

/-- `y` lies in the region with `down` node `d`. -/
def InRT (g : Gl) (St : T → T) (d y : T) : T :=
  andT (aliveT g St y) (andT (notT (leafT g y)) (eqT (downT g St y) d))

/-- Non-frontier rows. -/
def NFT (g : Gl) (St : T → T) (y c : T) : T :=
  orT (eqT c y) (orT (notT (aliveT g St c)) (InRT g St (downT g St y) c))

/-! ## Denotations -/

section

variable {φ : LTL} {p : LassoPath} (hE : Enc ts φ p)
  (hx : x = pack (encodeToks ts) q a) (hg : Gl.Ok x Γ ts g)
include hE

omit hE in
lemma tlix_le (P : ℕ) : tlix ts P ≤ tlix ts (tF ts) := by
  unfold tlix
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  rcases le_total P (tF ts) with h | h
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
    rw [hd, List.range_add, List.countP_append]; omega
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
    rw [hd, List.range_add, List.countP_append]
    simp [tnd]

lemma lix_eq (P : ℕ) : (tokFT hE).lix P = tlix ts P := rfl

lemma L_eq : (tokFT hE).L = tlix ts (tF ts) := rfl

lemma cont_lt_L {y k : ℕ} (h : (tokFT hE).Cont y k) : k < (tokFT hE).L := by
  have := h.2
  rw [lix_eq, L_eq] at *
  have := tlix_le (ts := ts) (fend ts y)
  exact lt_of_lt_of_le h.2 this

include hx hg

lemma den_Cont {y k : T} {Y K : ℕ} (hy : Den x Γ y Y) (hk : Den x Γ k K) :
    Den x Γ (ContT g y k) (bv ((tokFT hE).Cont Y K)) :=
  den_and (den_le (den_lix hx hg hy) hk) (den_lt' hk (den_lix hx hg (den_fend hx hy)))

omit hx in
lemma den_S0 {r : ℕ} {d : T} (hd : Den x Γ d (cp2 r (tokFT hE).L)) :
    DenS x Γ (S0T g d) ((tokFT hE).S0 r) := fun Γ' hΓ t v ht => by
  refine (den_and (den_lt' ht (hg.mono hΓ).L) (den_eq' (den_mod ht (hd.mono hΓ)) (den_c 0))).of_eq
    (bv_congr ?_)
  unfold PT.S0
  rw [L_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, (dvd_cp2 h1).2 h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (dvd_cp2 h1).1 h2⟩

omit hE hx hg in
lemma den_Odd2 {r L : ℕ} {d k : T} {K : ℕ} (hd : Den x Γ d (cp2 r L)) (hk : Den x Γ k K)
    (hK : K < L) : Den x Γ (Odd2T d k) (bv (PT.Odd2 r K)) :=
  (den_eq' (den_mod (den_div hk hd) (den_c 2)) (den_c 1)).of_eq (bv_congr (by
    unfold PT.Odd2; rw [div_cp2 hK]))

lemma den_par {St : T → T} {S : ℕ → Prop} (hS : DenS x Γ St S)
    (hSL : ∀ k, S k → k < (tokFT hE).L) {k : T} {K : ℕ} (hk : Den x Γ k K) :
    Den x Γ (parT g St k) ((tokFT hE).par S K) := by
  have := den_fg (N := tF ts) (P := fun z => (tokFT hE).nd z = true ∧ (tokFT hE).Cont z K ∧
      ∃ k', S k' ∧ k' ≠ K ∧ (tokFT hE).Cont z k')
    (body := fun z => andT (tndT g z) (andT (ContT g z k)
      (exT g.L fun k' => andT (St k') (andT (neT k' k) (ContT g z k'))))) hg.F
    (fun Γ' hΓ t i _ ht => ?_)
  · exact this.of_eq (by unfold PT.par; congr)
  · have hg' := hg.mono hΓ
    refine (den_and ((den_tnd hx hg' ht).of_eq (bv_bool _)) (den_and
      (den_Cont hE hx hg' ht (hk.mono hΓ)) (den_ex (P := fun k' => S k' ∧ k' ≠ K ∧
        (tokFT hE).Cont i k') hg'.L fun k'' j _ => ?_))).of_eq (bv_congr ?_)
    · have hv : Den x ((k'', j) :: Γ') (varT k'') j := den_var0
      exact den_and (hS.mono hΓ _ (List.subset_cons_self _ _) _ _ hv) (den_and
        (den_ne hv ((hk.mono hΓ).cons _)) (den_Cont hE hx (hg'.cons _) (ht.cons _) hv))
    · rw [← L_eq hE]
      exact and_congr Iff.rfl (and_congr Iff.rfl ⟨fun ⟨k', _, h⟩ => ⟨k', h⟩,
        fun ⟨k', h⟩ => ⟨k', hSL k' h.1, h⟩⟩)

omit hE hx hg in
lemma den_Odd2' {d k : T} {D K : ℕ} (hd : Den x Γ d D) (hk : Den x Γ k K) :
    Den x Γ (Odd2T d k) (bv (K / D % 2 = 1)) :=
  den_eq' (den_mod (den_div hk hd) (den_c 2)) (den_c 1)

omit hx hg in
lemma S0_lt {r k : ℕ} (h : (tokFT hE).S0 r k) : k < (tokFT hE).L := h.1

lemma den_DL {r : ℕ} {d : T} (hd : Den x Γ d (cp2 r (tokFT hE).L)) :
    DenS x Γ (DLT g d) ((tokFT hE).DL r) := fun Γ' hΓ t v ht => by
  have hg' := hg.mono hΓ
  have hd' := hd.mono hΓ
  have hS0 := den_S0 hE hg' hd'
  refine (den_and (hS0.app ht) (den_and (den_Odd2' hd' ht) (den_Cont hE hx hg'
    (den_add (den_par hE hx hg' hS0 (fun k hk => S0_lt hE hk) ht) (den_c 1)) ht))).of_eq
    (bv_congr ?_)
  unfold PT.DL
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by unfold PT.Odd2; rwa [div_cp2 h1.1], h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by unfold PT.Odd2 at h2; rwa [div_cp2 h1.1] at h2, h3⟩

lemma den_S1 {r : ℕ} {d : T} (hd : Den x Γ d (cp2 r (tokFT hE).L)) :
    DenS x Γ (S1T g d) ((tokFT hE).S1 r) := fun _ hΓ _ _ ht =>
  den_and ((den_S0 hE (hg.mono hΓ) (hd.mono hΓ)).app ht)
    (den_not ((den_DL hE hx (hg.mono hΓ) (hd.mono hΓ)).app ht))

lemma den_DR {r : ℕ} {d : T} (hd : Den x Γ d (cp2 r (tokFT hE).L)) :
    DenS x Γ (DRT g d) ((tokFT hE).DR r) := fun Γ' hΓ t v ht => by
  refine (den_and ((den_S1 hE hx (hg.mono hΓ) (hd.mono hΓ)).app ht)
    (den_Odd2' (hd.mono hΓ) ht)).of_eq (bv_congr ?_)
  unfold PT.DR
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by unfold PT.Odd2; rwa [div_cp2 h1.1.1]⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by unfold PT.Odd2 at h2; rwa [div_cp2 h1.1.1] at h2⟩

lemma den_PSet {St Dt : T → T} {S D : ℕ → Prop} (hS : DenS x Γ St S) (hD : DenS x Γ Dt D)
    (hSL : ∀ k, S k → k < (tokFT hE).L) (hDL : ∀ k, D k → k < (tokFT hE).L) :
    DenS x Γ (PSetT g St Dt) ((tokFT hE).PSet S D) := fun Γ' hΓ t v ht => by
  have hg' := hg.mono hΓ
  refine (den_ex (P := fun k => D k ∧ (tokFT hE).par S k = v) hg'.L fun k i _ => ?_).of_eq
    (bv_congr ?_)
  · have hv : Den x ((k, i) :: Γ') (varT k) i := den_var0
    exact den_and (hD.mono hΓ _ (List.subset_cons_self _ _) _ _ hv)
      (den_eq' (den_par hE hx (hg'.cons _) ((hS.mono hΓ).mono (List.subset_cons_self _ _)) hSL hv)
        (ht.cons _))
  · rw [← L_eq hE]
    exact ⟨fun ⟨k, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, hDL k h.1, h⟩⟩

lemma den_alive {St : T → T} {S : ℕ → Prop} (hS : DenS x Γ St S) {y : T} {Y : ℕ}
    (hy : Den x Γ y Y) : Den x Γ (aliveT g St y) (bv ((tokFT hE).alive S Y)) := by
  refine (den_ex (P := fun k => S k ∧ (tokFT hE).Cont Y k) hg.L fun k i _ => ?_).of_eq
    (bv_congr ?_)
  · have hv : Den x ((k, i) :: Γ) (varT k) i := den_var0
    exact den_and (hS _ (List.subset_cons_self _ _) _ _ hv)
      (den_Cont hE hx (hg.cons _) (hy.cons _) hv)
  · rw [← L_eq hE]
    exact ⟨fun ⟨k, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, cont_lt_L hE h.2, h⟩⟩

lemma den_Anc {y z : T} {Y Z : ℕ} (hy : Den x Γ y Y) (hz : Den x Γ z Z) :
    Den x Γ (AncT g y z) (bv ((tokFT hE).Anc Y Z)) :=
  den_and ((den_tnd hx hg hy).of_eq (bv_bool _)) (den_and ((den_tnd hx hg hz).of_eq (bv_bool _))
    (den_and (den_le hy hz) (den_lt' hz (den_fend hx hy))))

lemma den_SameS {St : T → T} {S : ℕ → Prop} (hS : DenS x Γ St S) {y z : T} {Y Z : ℕ}
    (hy : Den x Γ y Y) (hz : Den x Γ z Z) :
    Den x Γ (SameST g St y z) (bv ((tokFT hE).SameS S Y Z)) := by
  refine (den_all (P := fun k => ¬ S k ∨ bv ((tokFT hE).Cont Y k) = bv ((tokFT hE).Cont Z k))
    hg.L fun k i _ => ?_).of_eq (bv_congr ?_)
  · have hv : Den x ((k, i) :: Γ) (varT k) i := den_var0
    exact den_or (den_not (hS _ (List.subset_cons_self _ _) _ _ hv))
      (den_eq' (den_Cont hE hx (hg.cons _) (hy.cons _) hv) (den_Cont hE hx (hg.cons _) (hz.cons _) hv))
  · rw [← L_eq hE]
    unfold PT.SameS
    constructor
    · intro h k hk
      by_cases hkL : k < (tokFT hE).L
      · rcases h k hkL with h' | h'
        · exact absurd hk h'
        · by_cases c1 : (tokFT hE).Cont Y k <;> by_cases c2 : (tokFT hE).Cont Z k <;>
            simp_all [bv]
      · exact ⟨fun c => absurd (cont_lt_L hE c) hkL, fun c => absurd (cont_lt_L hE c) hkL⟩
    · intro h k _
      by_cases hk : S k
      · exact Or.inr (bv_congr (h k hk))
      · exact Or.inl hk

lemma den_down {St : T → T} {S : ℕ → Prop} (hS : DenS x Γ St S) {y : T} {Y : ℕ}
    (hy : Den x Γ y Y) : Den x Γ (downT g St y) ((tokFT hE).down S Y) := by
  have := den_fg (N := tF ts) (P := fun z => (tokFT hE).Anc Y z ∧ (tokFT hE).SameS S Y z)
    (body := fun z => andT (AncT g y z) (SameST g St y z)) hg.F
    (fun Γ' hΓ t i _ ht => den_and (den_Anc hE hx (hg.mono hΓ) (hy.mono hΓ) ht)
      (den_SameS hE hx (hg.mono hΓ) (hS.mono hΓ) (hy.mono hΓ) ht))
  exact this.of_eq (by unfold PT.down; congr)

lemma den_InR {St : T → T} {S : ℕ → Prop} (hS : DenS x Γ St S) {d y : T} {D Y : ℕ}
    (hd : Den x Γ d D) (hy : Den x Γ y Y) :
    Den x Γ (InRT g St d y) (bv ((tokFT hE).InR S D Y)) := by
  refine (den_and (den_alive hE hx hg hS hy) (den_and (den_not ((den_leaf hx hg hy).of_eq
    (bv_bool _))) (den_eq' (den_down hE hx hg hS hy) hd))).of_eq (bv_congr ?_)
  unfold FT.InR
  simp only [Bool.not_eq_true]
  rfl

lemma den_NF {St : T → T} {S : ℕ → Prop} (hS : DenS x Γ St S) {y c : T} {Y C : ℕ}
    (hy : Den x Γ y Y) (hc : Den x Γ c C) :
    Den x Γ (NFT g St y c) (bv ((tokFT hE).NF S Y C)) := by
  refine (den_or (den_eq' hc hy) (den_or (den_not (den_alive hE hx hg hS hc))
    (den_InR hE hx hg hS (den_down hE hx hg hS hy) hc))).of_eq (bv_congr ?_)
  unfold PT.NF PT.InReg FT.InR
  rfl

end

end FD

end PathChecking
