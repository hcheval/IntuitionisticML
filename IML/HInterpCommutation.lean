import IML.HeytingSemantics

/-!
# Commutation lemmas for Carrier → L semantics
-/

namespace IML

open Pattern

variable {Symbol : Type} {L : Type*} [Order.Frame L] {M : HModel Symbol L}

-- ─────────────────────────────────────────────────────────────
-- Valuation shifts
-- ─────────────────────────────────────────────────────────────

def HValuation.shiftEVar (ρ : HValuation M) (k : Nat) (a : M.Carrier) :
    HValuation M where
  evar i := if i < k then ρ.evar i else if i = k then a else ρ.evar (i - 1)
  svar := ρ.svar
  svar_ext := ρ.svar_ext

def HValuation.shiftSVar (ρ : HValuation M) (k : Nat) (S : M.Carrier → L)
    (hS : M.Ext S) : HValuation M where
  evar := ρ.evar
  svar i := if i < k then ρ.svar i else if i = k then S else ρ.svar (i - 1)
  svar_ext i := by
    split
    · exact ρ.svar_ext i
    · split
      · exact hS
      · exact ρ.svar_ext (i - 1)

theorem HValuation.ext' {ρ₁ ρ₂ : HValuation M}
    (he : ρ₁.evar = ρ₂.evar) (hs : ρ₁.svar = ρ₂.svar) : ρ₁ = ρ₂ := by
  cases ρ₁; cases ρ₂; cases he; cases hs; rfl

/-- Replacing the shifted predicate by an equal one (the extensionality
proof is transported along). -/
theorem HValuation.shiftSVar_congr (ρ : HValuation M) (k : Nat)
    {S S' : M.Carrier → L} (h : S = S') (hS : M.Ext S) (hS' : M.Ext S') :
    ρ.shiftSVar k S hS = ρ.shiftSVar k S' hS' := by
  subst h; rfl

@[simp] theorem HValuation.shiftEVar_zero (ρ : HValuation M) (a : M.Carrier) :
    ρ.shiftEVar 0 a = ρ.pushEVar a := by
  apply HValuation.ext' <;> ext i <;> cases i <;> simp [shiftEVar, pushEVar]

@[simp] theorem HValuation.shiftSVar_zero (ρ : HValuation M) (S : M.Carrier → L)
    (hS : M.Ext S) :
    ρ.shiftSVar 0 S hS = ρ.pushSVar S hS := by
  apply HValuation.ext'
  · rfl
  · ext i; cases i <;> simp [shiftSVar, pushSVar]

-- ─────────────────────────────────────────────────────────────
-- Push commutativity (same structure as deprecated, tedious)
-- ─────────────────────────────────────────────────────────────

theorem HValuation.shiftEVar_pushEVar_comm (ρ : HValuation M)
    (k : Nat) (a b : M.Carrier) :
    (ρ.shiftEVar k a).pushEVar b = (ρ.pushEVar b).shiftEVar (k + 1) a := by
  apply HValuation.ext'
  · ext i; cases i with
    | zero => simp [pushEVar, shiftEVar]
    | succ n =>
      simp only [pushEVar, shiftEVar]
      by_cases h1 : n < k
      · simp [h1, Nat.succ_lt_succ h1]
      · by_cases h2 : n = k
        · subst h2; simp
        · have h3 : ¬(n + 1 < k + 1) := fun h => h1 (Nat.lt_of_succ_lt_succ h)
          have h4 : n + 1 ≠ k + 1 := fun h => h2 (Nat.succ.inj h)
          simp only [h1, h2, h3, h4, ↓reduceIte]
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          rfl
  · rfl

theorem HValuation.shiftEVar_pushSVar_comm (ρ : HValuation M)
    (k : Nat) (a : M.Carrier) (S : M.Carrier → L) (hS : M.Ext S) :
    (ρ.shiftEVar k a).pushSVar S hS = (ρ.pushSVar S hS).shiftEVar k a := by
  apply HValuation.ext'
  · ext i; simp [pushSVar, shiftEVar]
  · ext i; simp [pushSVar, shiftEVar]

theorem HValuation.shiftSVar_pushEVar_comm (ρ : HValuation M)
    (k : Nat) (S : M.Carrier → L) (hS : M.Ext S) (a : M.Carrier) :
    (ρ.shiftSVar k S hS).pushEVar a = (ρ.pushEVar a).shiftSVar k S hS := by
  apply HValuation.ext'
  · ext i; simp [pushEVar, shiftSVar]
  · ext i; simp [pushEVar, shiftSVar]

theorem HValuation.shiftSVar_pushSVar_comm (ρ : HValuation M)
    (k : Nat) (S : M.Carrier → L) (hS : M.Ext S) (T : M.Carrier → L) (hT : M.Ext T) :
    (ρ.shiftSVar k S hS).pushSVar T hT = (ρ.pushSVar T hT).shiftSVar (k + 1) S hS := by
  apply HValuation.ext'
  · rfl
  · ext i; cases i with
    | zero => simp [pushSVar, shiftSVar]
    | succ n =>
      simp only [pushSVar, shiftSVar]
      by_cases h1 : n < k
      · simp [h1, Nat.succ_lt_succ h1]
      · by_cases h2 : n = k
        · subst h2; simp
        · have h3 : ¬(n + 1 < k + 1) := fun h => h1 (Nat.lt_of_succ_lt_succ h)
          have h4 : n + 1 ≠ k + 1 := fun h => h2 (Nat.succ.inj h)
          simp only [h1, h2, h3, h4, ↓reduceIte]
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          rfl

-- ─────────────────────────────────────────────────────────────
-- evarLift commutation
-- ─────────────────────────────────────────────────────────────

theorem hinterp_evarLiftFrom (M : HModel Symbol L)
    (φ : Pattern Symbol) (k : Nat) (ρ : HValuation M) (a : M.Carrier)
    (m : M.Carrier) :
    hinterp M (ρ.shiftEVar k a) (evarLiftFrom k φ) m = hinterp M ρ φ m := by
  induction φ generalizing k ρ m with
  | evar i =>
    simp only [evarLiftFrom, hinterp]
    have h : (ρ.shiftEVar k a).evar (if i ≥ k then i + 1 else i) = ρ.evar i := by
      simp only [HValuation.shiftEVar]; split
      · rename_i hge; simp [Nat.not_lt.mpr (Nat.le_succ_of_le hge), (Nat.lt_succ_of_le hge).ne']
      · rename_i hlt; simp [Nat.lt_of_not_le hlt]
    rw [h]
  | svar => rfl
  | symbol => rfl
  | bot => rfl
  | app _ _ ih₁ ih₂ => simp only [evarLiftFrom, hinterp, ih₁, ih₂]
  | impl _ _ ih₁ ih₂ => simp only [evarLiftFrom, hinterp, ih₁, ih₂]
  | conj _ _ ih₁ ih₂ => simp only [evarLiftFrom, hinterp, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => simp only [evarLiftFrom, hinterp, ih₁, ih₂]
  | exist _ ih =>
    simp only [evarLiftFrom, hinterp]
    congr 1; ext a'
    rw [HValuation.shiftEVar_pushEVar_comm, ih]
  | forallP _ ih =>
    simp only [evarLiftFrom, hinterp]
    congr 1; ext a'
    rw [HValuation.shiftEVar_pushEVar_comm, ih]
  | mu _ ih =>
    simp only [evarLiftFrom, hinterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨S, hS, hpre, rfl⟩
      refine ⟨S, hS, fun n => ?_, rfl⟩
      rw [HValuation.shiftEVar_pushSVar_comm] at hpre
      exact (ih k (ρ.pushSVar S hS) n) ▸ hpre n
    · rintro ⟨S, hS, hpre, rfl⟩
      refine ⟨S, hS, fun n => ?_, rfl⟩
      rw [HValuation.shiftEVar_pushSVar_comm]
      exact (ih k (ρ.pushSVar S hS) n).symm ▸ hpre n
  | nu _ ih =>
    simp only [evarLiftFrom, hinterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨S, hS, hpost, rfl⟩
      refine ⟨S, hS, fun n => ?_, rfl⟩
      rw [HValuation.shiftEVar_pushSVar_comm] at hpost
      exact (ih k (ρ.pushSVar S hS) n) ▸ hpost n
    · rintro ⟨S, hS, hpost, rfl⟩
      refine ⟨S, hS, fun n => ?_, rfl⟩
      rw [HValuation.shiftEVar_pushSVar_comm]
      exact (ih k (ρ.pushSVar S hS) n).symm ▸ hpost n

theorem hinterp_evarLift (M : HModel Symbol L)
    (φ : Pattern Symbol) (ρ : HValuation M) (a : M.Carrier) (m : M.Carrier) :
    hinterp M (ρ.pushEVar a) (evarLift φ) m = hinterp M ρ φ m := by
  rw [evarLift, ← HValuation.shiftEVar_zero]
  exact hinterp_evarLiftFrom M φ 0 ρ a m

-- ─────────────────────────────────────────────────────────────
-- svarSubst commutation
-- ─────────────────────────────────────────────────────────────

-- svarLift commutation (needed for svarSubst mu/nu cases)
theorem hinterp_svarLiftFrom (M : HModel Symbol L)
    (φ : Pattern Symbol) (k : Nat) (ρ : HValuation M) (S : M.Carrier → L)
    (hS : M.Ext S) (m : M.Carrier) :
    hinterp M (ρ.shiftSVar k S hS) (svarLiftFrom k φ) m = hinterp M ρ φ m := by
  induction φ generalizing k ρ m with
  | evar => rfl
  | svar i =>
    simp only [svarLiftFrom, hinterp]
    rcases Nat.lt_or_ge i k with hlt | hge
    · simp [show ¬(i ≥ k) from Nat.not_le.mpr hlt, HValuation.shiftSVar, hlt]
    · have h1 : ¬(i + 1 < k) := Nat.not_lt.mpr (Nat.le_succ_of_le hge)
      have h2 : i + 1 ≠ k := (Nat.lt_succ_of_le hge).ne'
      simp [show i ≥ k from hge, HValuation.shiftSVar, h1, h2]
  | symbol => rfl
  | bot => rfl
  | app _ _ ih₁ ih₂ => simp only [svarLiftFrom, hinterp, ih₁, ih₂]
  | impl _ _ ih₁ ih₂ => simp only [svarLiftFrom, hinterp, ih₁, ih₂]
  | conj _ _ ih₁ ih₂ => simp only [svarLiftFrom, hinterp, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => simp only [svarLiftFrom, hinterp, ih₁, ih₂]
  | exist _ ih =>
    simp only [svarLiftFrom, hinterp]
    congr 1; ext a'
    rw [HValuation.shiftSVar_pushEVar_comm, ih]
  | forallP _ ih =>
    simp only [svarLiftFrom, hinterp]
    congr 1; ext a'
    rw [HValuation.shiftSVar_pushEVar_comm, ih]
  | mu _ ih =>
    simp only [svarLiftFrom, hinterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]; constructor
    · rintro ⟨T, hT, hpre, rfl⟩
      refine ⟨T, hT, fun n => ?_, rfl⟩
      rw [HValuation.shiftSVar_pushSVar_comm] at hpre
      exact (ih (k+1) (ρ.pushSVar T hT) n) ▸ hpre n
    · rintro ⟨T, hT, hpre, rfl⟩
      refine ⟨T, hT, fun n => ?_, rfl⟩
      rw [HValuation.shiftSVar_pushSVar_comm]
      exact (ih (k+1) (ρ.pushSVar T hT) n).symm ▸ hpre n
  | nu _ ih =>
    simp only [svarLiftFrom, hinterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]; constructor
    · rintro ⟨T, hT, hpost, rfl⟩
      refine ⟨T, hT, fun n => ?_, rfl⟩
      rw [HValuation.shiftSVar_pushSVar_comm] at hpost
      exact (ih (k+1) (ρ.pushSVar T hT) n) ▸ hpost n
    · rintro ⟨T, hT, hpost, rfl⟩
      refine ⟨T, hT, fun n => ?_, rfl⟩
      rw [HValuation.shiftSVar_pushSVar_comm]
      exact (ih (k+1) (ρ.pushSVar T hT) n).symm ▸ hpost n

theorem hinterp_svarLift (M : HModel Symbol L)
    (φ : Pattern Symbol) (ρ : HValuation M) (S : M.Carrier → L) (hS : M.Ext S)
    (m : M.Carrier) :
    hinterp M (ρ.pushSVar S hS) (svarLift φ) m = hinterp M ρ φ m := by
  rw [svarLift, ← HValuation.shiftSVar_zero]
  exact hinterp_svarLiftFrom M φ 0 ρ S hS m

-- svarSubst commutation
theorem hinterp_svarSubst_aux (M : HModel Symbol L)
    (φ ψ : Pattern Symbol) (k : Nat) (ρ : HValuation M) (m : M.Carrier) :
    hinterp M ρ (svarSubst k ψ φ) m =
    hinterp M (ρ.shiftSVar k (fun n => hinterp M ρ ψ n) (hinterp_ext ψ ρ)) φ m := by
  induction φ generalizing k ψ ρ m with
  | evar => simp [svarSubst, hinterp, HValuation.shiftSVar]
  | svar i =>
    simp only [svarSubst]
    rcases Nat.lt_trichotomy i k with hlt | heq | hgt
    · -- i < k: subst gives .svar i, shift gives ρ.svar i
      have hne : (i == k) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlt)
      have hng : ¬(i > k) := Nat.not_lt.mpr (Nat.le_of_lt hlt)
      simp only [hne, Bool.false_eq_true, hng, ↓reduceIte, hinterp,
                 HValuation.shiftSVar, hlt]
    · -- i = k: subst gives ψ, shift gives the substituted predicate
      subst heq; simp [hinterp, HValuation.shiftSVar]
    · -- i > k: subst gives .svar (i-1), shift gives ρ.svar (i-1)
      have hne : (i == k) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hgt)
      have hnl : ¬(i < k) := Nat.not_lt.mpr (Nat.le_of_lt hgt)
      have hne2 : i ≠ k := Nat.ne_of_gt hgt
      simp only [hne, Bool.false_eq_true, show i > k from hgt, ↓reduceIte, hinterp,
                 HValuation.shiftSVar, hnl, hne2]
  | symbol => simp [svarSubst, hinterp]
  | bot => simp [svarSubst, hinterp]
  | app _ _ ih₁ ih₂ => simp only [svarSubst, hinterp, ih₁, ih₂]
  | impl _ _ ih₁ ih₂ => simp only [svarSubst, hinterp, ih₁, ih₂]
  | conj _ _ ih₁ ih₂ => simp only [svarSubst, hinterp, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => simp only [svarSubst, hinterp, ih₁, ih₂]
  | exist _ ih =>
    simp only [svarSubst, hinterp]
    congr 1; ext a
    rw [ih (evarLift ψ) k,
      HValuation.shiftSVar_congr _ _ (funext (fun n => hinterp_evarLift M ψ ρ a n))
        (hinterp_ext _ _) (hinterp_ext ψ ρ)]
    rw [← HValuation.shiftSVar_pushEVar_comm]
  | forallP _ ih =>
    simp only [svarSubst, hinterp]
    congr 1; ext a
    rw [ih (evarLift ψ) k,
      HValuation.shiftSVar_congr _ _ (funext (fun n => hinterp_evarLift M ψ ρ a n))
        (hinterp_ext _ _) (hinterp_ext ψ ρ)]
    rw [← HValuation.shiftSVar_pushEVar_comm]
  | mu _ ih =>
    simp only [svarSubst, hinterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]; constructor
    · rintro ⟨S, hS, hpre, rfl⟩
      refine ⟨S, hS, fun n => ?_, rfl⟩
      have key := ih (svarLift ψ) (k+1) (ρ.pushSVar S hS) n
      rw [HValuation.shiftSVar_congr _ _ (funext (fun n => hinterp_svarLift M ψ ρ S hS n))
        (hinterp_ext _ _) (hinterp_ext ψ ρ)] at key
      rw [← HValuation.shiftSVar_pushSVar_comm] at key
      exact key ▸ hpre n
    · rintro ⟨S, hS, hpre, rfl⟩
      refine ⟨S, hS, fun n => ?_, rfl⟩
      have key := ih (svarLift ψ) (k+1) (ρ.pushSVar S hS) n
      rw [HValuation.shiftSVar_congr _ _ (funext (fun n => hinterp_svarLift M ψ ρ S hS n))
        (hinterp_ext _ _) (hinterp_ext ψ ρ)] at key
      rw [← HValuation.shiftSVar_pushSVar_comm] at key
      exact key.symm ▸ hpre n
  | nu _ ih =>
    simp only [svarSubst, hinterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]; constructor
    · rintro ⟨S, hS, hpost, rfl⟩
      refine ⟨S, hS, fun n => ?_, rfl⟩
      have key := ih (svarLift ψ) (k+1) (ρ.pushSVar S hS) n
      rw [HValuation.shiftSVar_congr _ _ (funext (fun n => hinterp_svarLift M ψ ρ S hS n))
        (hinterp_ext _ _) (hinterp_ext ψ ρ)] at key
      rw [← HValuation.shiftSVar_pushSVar_comm] at key
      exact key ▸ hpost n
    · rintro ⟨S, hS, hpost, rfl⟩
      refine ⟨S, hS, fun n => ?_, rfl⟩
      have key := ih (svarLift ψ) (k+1) (ρ.pushSVar S hS) n
      rw [HValuation.shiftSVar_congr _ _ (funext (fun n => hinterp_svarLift M ψ ρ S hS n))
        (hinterp_ext _ _) (hinterp_ext ψ ρ)] at key
      rw [← HValuation.shiftSVar_pushSVar_comm] at key
      exact key.symm ▸ hpost n

theorem hinterp_svarSubst (φ ψ : Pattern Symbol) (ρ : HValuation M)
    (m : M.Carrier) :
    hinterp M ρ (svarSubst 0 ψ φ) m =
    hinterp M (ρ.pushSVar (fun n => hinterp M ρ ψ n) (hinterp_ext ψ ρ)) φ m := by
  rw [hinterp_svarSubst_aux, HValuation.shiftSVar_zero]

-- evarSubst commutation
theorem hinterp_evarSubst_aux (M : HModel Symbol L)
    (φ : Pattern Symbol) (k j : Nat) (ρ : HValuation M) (m : M.Carrier) :
    hinterp M ρ (evarSubst k (.evar j) φ) m =
    hinterp M (ρ.shiftEVar k (ρ.evar j)) φ m := by
  induction φ generalizing k j ρ m with
  | evar i =>
    simp only [evarSubst]
    -- case split on i vs k: each gives the same carrier element
    split
    · -- i = k: both sides use ρ.evar j
      rename_i heq; have := beq_iff_eq.mp heq; subst this
      simp only [hinterp]
      have : (HValuation.shiftEVar ρ i (ρ.evar j)).evar i = ρ.evar j := by
        simp only [HValuation.shiftEVar, lt_irrefl, ↓reduceIte]
      rw [this]
    · split
      · -- i > k: both sides use ρ.evar (i-1)
        rename_i hne hgt
        have hne' : i ≠ k := fun h => hne (beq_iff_eq.mpr h)
        simp only [hinterp]
        have : (ρ.shiftEVar k (ρ.evar j)).evar i = ρ.evar (i - 1) := by
          simp [HValuation.shiftEVar, Nat.not_lt.mpr (Nat.le_of_lt hgt), hne']
        rw [this]
      · -- i < k: both sides use ρ.evar i
        rename_i hne hle
        have hne' : i ≠ k := fun h => hne (beq_iff_eq.mpr h)
        have hlt : i < k := Nat.lt_of_le_of_ne (Nat.not_lt.mp hle) hne'
        simp only [hinterp]
        have : (ρ.shiftEVar k (ρ.evar j)).evar i = ρ.evar i := by
          simp [HValuation.shiftEVar, hlt]
        rw [this]
  | svar => simp [evarSubst, hinterp, HValuation.shiftEVar]
  | symbol => simp [evarSubst, hinterp]
  | bot => simp [evarSubst, hinterp]
  | app _ _ ih₁ ih₂ => simp only [evarSubst, hinterp, ih₁, ih₂]
  | impl _ _ ih₁ ih₂ => simp only [evarSubst, hinterp, ih₁, ih₂]
  | conj _ _ ih₁ ih₂ => simp only [evarSubst, hinterp, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => simp only [evarSubst, hinterp, ih₁, ih₂]
  | exist _ ih =>
    simp only [evarSubst, evarLift, evarLiftFrom, Nat.zero_le, ↓reduceIte, hinterp]
    congr 1; ext a
    rw [ih (k + 1) (j + 1)]
    rw [show (ρ.pushEVar a).evar (j + 1) = ρ.evar j from rfl,
        ← HValuation.shiftEVar_pushEVar_comm]
  | forallP _ ih =>
    simp only [evarSubst, evarLift, evarLiftFrom, Nat.zero_le, ↓reduceIte, hinterp]
    congr 1; ext a
    rw [ih (k + 1) (j + 1)]
    rw [show (ρ.pushEVar a).evar (j + 1) = ρ.evar j from rfl,
        ← HValuation.shiftEVar_pushEVar_comm]
  | mu _ ih =>
    simp only [evarSubst, hinterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]
    have comm : ∀ S (hS : M.Ext S), (ρ.shiftEVar k (ρ.evar j)).pushSVar S hS =
        (ρ.pushSVar S hS).shiftEVar k ((ρ.pushSVar S hS).evar j) := fun S hS =>
      HValuation.ext' (by ext i; simp [HValuation.pushSVar, HValuation.shiftEVar])
                      (by ext i; simp [HValuation.pushSVar, HValuation.shiftEVar])
    constructor
    · rintro ⟨S, hS, hpre, rfl⟩
      exact ⟨S, hS, fun n => by rw [comm S hS, ← ih k j (ρ.pushSVar S hS) n]; exact hpre n, rfl⟩
    · rintro ⟨S, hS, hpre, rfl⟩
      exact ⟨S, hS, fun n => by rw [ih k j (ρ.pushSVar S hS) n, ← comm S hS]; exact hpre n, rfl⟩
  | nu _ ih =>
    simp only [evarSubst, hinterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]
    have comm : ∀ S (hS : M.Ext S), (ρ.shiftEVar k (ρ.evar j)).pushSVar S hS =
        (ρ.pushSVar S hS).shiftEVar k ((ρ.pushSVar S hS).evar j) := fun S hS =>
      HValuation.ext' (by ext i; simp [HValuation.pushSVar, HValuation.shiftEVar])
                      (by ext i; simp [HValuation.pushSVar, HValuation.shiftEVar])
    constructor
    · rintro ⟨S, hS, hpost, rfl⟩
      exact ⟨S, hS, fun n => by rw [comm S hS, ← ih k j (ρ.pushSVar S hS) n]; exact hpost n, rfl⟩
    · rintro ⟨S, hS, hpost, rfl⟩
      exact ⟨S, hS, fun n => by rw [ih k j (ρ.pushSVar S hS) n, ← comm S hS]; exact hpost n, rfl⟩

theorem hinterp_evarSubst (φ : Pattern Symbol) (n : EVarIndex)
    (ρ : HValuation M) (m : M.Carrier) :
    hinterp M ρ (evarSubst 0 (.evar n) φ) m =
    hinterp M (ρ.pushEVar (ρ.evar n)) φ m := by
  rw [hinterp_evarSubst_aux, HValuation.shiftEVar_zero]

end IML
