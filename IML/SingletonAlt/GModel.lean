import IML.SingletonAlt.ProofCore

/-!
# Generalized models for independence results

To show that one singleton-shaped axiom does **not** derive another we need models that
validate all 26 non-singleton rules of iML but are free to violate the crispness of element
variables or the linearity of application. `GModel` generalizes `HModel` in two independent
directions (the technique follows `MatchingLogic/SingletonIndependence.lean` in the parent
repo):

1. **Admissible valuations.** Element variables denote arbitrary predicates `Carrier → L`
   drawn from an admissible family `Adm` (quantifiers range over `Adm`; validity is
   validity under all admissible valuations). `HModel` is the case `Adm = crisp singletons`.
2. **Twisted application.** `app` is `⨆ a b, δ(φ a) ⊓ δ(ψ b) ⊓ appInterp a b m` for a
   monotone, join-preserving `δ : L → L`. `HModel` is the case `δ = id`. Framing and
   propagation only need monotonicity and join preservation of `δ`.

`gsoundness` proves every `ProofCore` derivation valid in every `GModel` whose axiom scheme
is valid. The countermodels themselves live in `Countermodels.lean`.
-/

-- Per-theorem async elaboration spawns one thread per declaration; under the address-space
-- cap of the build wrappers (`scripts/build.sh`, 30 GB at the time of writing) that still
-- fails on this file ("failed to create thread", exit 134), so elaborate sequentially.
set_option Elab.async false

namespace IML

open Pattern

-- ─────────────────────────────────────────────────────────────
-- Models and valuations
-- ─────────────────────────────────────────────────────────────

structure GModel (Symbol : Type) (L : Type*) [Order.Frame L] where
  Carrier : Type
  appInterp : Carrier → Carrier → Carrier → L
  symInterp : Symbol → Carrier → L
  /-- The admissible denotations of element variables. -/
  Adm : Set (Carrier → L)
  /-- Needed for the `existence` rule `∃x. x`. -/
  adm_cover : ∀ m, ∃ X ∈ Adm, X m = ⊤
  /-- The twist applied to both arguments of an application. -/
  δ : L → L
  δ_mono : Monotone δ
  δ_sup : ∀ p q, δ (p ⊔ q) ≤ δ p ⊔ δ q
  δ_iSup : ∀ (f : Adm → L), δ (⨆ X, f X) ≤ ⨆ X, δ (f X)

variable {Symbol : Type} {L : Type*} [Order.Frame L]

structure GValuation (M : GModel Symbol L) where
  evar : EVarIndex → M.Carrier → L
  svar : SVarIndex → M.Carrier → L

namespace GValuation
variable {M : GModel Symbol L}

def pushEVar (ρ : GValuation M) (X : M.Carrier → L) : GValuation M where
  evar i := match i with | 0 => X | n + 1 => ρ.evar n
  svar := ρ.svar

def pushSVar (ρ : GValuation M) (S : M.Carrier → L) : GValuation M where
  evar := ρ.evar
  svar i := match i with | 0 => S | n + 1 => ρ.svar n

def shiftEVar (ρ : GValuation M) (k : Nat) (X : M.Carrier → L) : GValuation M where
  evar i := if i < k then ρ.evar i else if i = k then X else ρ.evar (i - 1)
  svar := ρ.svar

def shiftSVar (ρ : GValuation M) (k : Nat) (S : M.Carrier → L) : GValuation M where
  evar := ρ.evar
  svar i := if i < k then ρ.svar i else if i = k then S else ρ.svar (i - 1)

theorem ext' {ρ₁ ρ₂ : GValuation M}
    (he : ρ₁.evar = ρ₂.evar) (hs : ρ₁.svar = ρ₂.svar) : ρ₁ = ρ₂ := by
  cases ρ₁; cases ρ₂; simp only [mk.injEq]; exact ⟨he, hs⟩

@[simp] theorem shiftEVar_zero (ρ : GValuation M) (X : M.Carrier → L) :
    ρ.shiftEVar 0 X = ρ.pushEVar X := by
  apply ext' <;> ext i <;> cases i <;> simp [shiftEVar, pushEVar]

@[simp] theorem shiftSVar_zero (ρ : GValuation M) (S : M.Carrier → L) :
    ρ.shiftSVar 0 S = ρ.pushSVar S := by
  apply ext'
  · rfl
  · ext i; cases i <;> simp [shiftSVar, pushSVar]

theorem shiftEVar_pushEVar_comm (ρ : GValuation M) (k : Nat) (X Y : M.Carrier → L) :
    (ρ.shiftEVar k X).pushEVar Y = (ρ.pushEVar Y).shiftEVar (k + 1) X := by
  apply ext'
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

theorem shiftEVar_pushSVar_comm (ρ : GValuation M) (k : Nat) (X : M.Carrier → L)
    (S : M.Carrier → L) :
    (ρ.shiftEVar k X).pushSVar S = (ρ.pushSVar S).shiftEVar k X := by
  apply ext'
  · ext i; simp [pushSVar, shiftEVar]
  · ext i; simp [pushSVar, shiftEVar]

theorem shiftSVar_pushEVar_comm (ρ : GValuation M) (k : Nat) (S : M.Carrier → L)
    (X : M.Carrier → L) :
    (ρ.shiftSVar k S).pushEVar X = (ρ.pushEVar X).shiftSVar k S := by
  apply ext'
  · ext i; simp [pushEVar, shiftSVar]
  · ext i; simp [pushEVar, shiftSVar]

theorem shiftSVar_pushSVar_comm (ρ : GValuation M) (k : Nat) (S T : M.Carrier → L) :
    (ρ.shiftSVar k S).pushSVar T = (ρ.pushSVar T).shiftSVar (k + 1) S := by
  apply ext'
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

/-- A valuation is admissible if every element variable denotes an admissible predicate. -/
def IsAdm (ρ : GValuation M) : Prop := ∀ i, ρ.evar i ∈ M.Adm

theorem IsAdm.pushEVar {ρ : GValuation M} (h : ρ.IsAdm) {X : M.Carrier → L}
    (hX : X ∈ M.Adm) : (ρ.pushEVar X).IsAdm := by
  intro i; cases i with
  | zero => exact hX
  | succ j => exact h j

theorem IsAdm.pushSVar {ρ : GValuation M} (h : ρ.IsAdm) (S : M.Carrier → L) :
    (ρ.pushSVar S).IsAdm := h

end GValuation

-- ─────────────────────────────────────────────────────────────
-- Interpretation
-- ─────────────────────────────────────────────────────────────

def ginterp (M : GModel Symbol L) (ρ : GValuation M) :
    Pattern Symbol → M.Carrier → L
  | .evar i, m    => ρ.evar i m
  | .svar i, m    => ρ.svar i m
  | .symbol s, m  => M.symInterp s m
  | .app φ ψ, m   =>
    ⨆ a, ⨆ b, M.δ (ginterp M ρ φ a) ⊓ M.δ (ginterp M ρ ψ b) ⊓ M.appInterp a b m
  | .bot, _        => ⊥
  | .impl φ ψ, m  => ginterp M ρ φ m ⇨ ginterp M ρ ψ m
  | .conj φ ψ, m  => ginterp M ρ φ m ⊓ ginterp M ρ ψ m
  | .disj φ ψ, m  => ginterp M ρ φ m ⊔ ginterp M ρ ψ m
  | .exist φ, m   => ⨆ X : M.Adm, ginterp M (ρ.pushEVar X.1) φ m
  | .forallP φ, m => ⨅ X : M.Adm, ginterp M (ρ.pushEVar X.1) φ m
  | .mu φ, m      =>
    sInf { x | ∃ S : M.Carrier → L,
      (∀ n, ginterp M (ρ.pushSVar S) φ n ≤ S n) ∧ x = S m }
  | .nu φ, m      =>
    sSup { x | ∃ S : M.Carrier → L,
      (∀ n, S n ≤ ginterp M (ρ.pushSVar S) φ n) ∧ x = S m }

section ginterpSimp
variable {M : GModel Symbol L} {ρ : GValuation M}

@[simp] theorem ginterp_evar (i : EVarIndex) (m : M.Carrier) :
    ginterp M ρ (.evar i) m = ρ.evar i m := rfl
@[simp] theorem ginterp_svar (i : SVarIndex) (m : M.Carrier) :
    ginterp M ρ (.svar i) m = ρ.svar i m := rfl
@[simp] theorem ginterp_symbol (s : Symbol) (m : M.Carrier) :
    ginterp M ρ (.symbol s) m = M.symInterp s m := rfl
@[simp] theorem ginterp_app (φ ψ : Pattern Symbol) (m : M.Carrier) :
    ginterp M ρ (φ ⬝ ψ) m =
    ⨆ a, ⨆ b, M.δ (ginterp M ρ φ a) ⊓ M.δ (ginterp M ρ ψ b) ⊓ M.appInterp a b m := rfl
@[simp] theorem ginterp_bot (m : M.Carrier) :
    ginterp M ρ (⊥ₘ : Pattern Symbol) m = ⊥ := rfl
@[simp] theorem ginterp_impl (φ ψ : Pattern Symbol) (m : M.Carrier) :
    ginterp M ρ (φ ⇒ ψ) m = ginterp M ρ φ m ⇨ ginterp M ρ ψ m := rfl
@[simp] theorem ginterp_conj (φ ψ : Pattern Symbol) (m : M.Carrier) :
    ginterp M ρ (φ ⊓ ψ) m = ginterp M ρ φ m ⊓ ginterp M ρ ψ m := rfl
@[simp] theorem ginterp_disj (φ ψ : Pattern Symbol) (m : M.Carrier) :
    ginterp M ρ (φ ⊔ ψ) m = ginterp M ρ φ m ⊔ ginterp M ρ ψ m := rfl
@[simp] theorem ginterp_exist (φ : Pattern Symbol) (m : M.Carrier) :
    ginterp M ρ (∃ₑ φ) m = ⨆ X : M.Adm, ginterp M (ρ.pushEVar X.1) φ m := rfl
@[simp] theorem ginterp_forall (φ : Pattern Symbol) (m : M.Carrier) :
    ginterp M ρ (∀ₑ φ) m = ⨅ X : M.Adm, ginterp M (ρ.pushEVar X.1) φ m := rfl

end ginterpSimp

/-- Validity: `⊤` at every point under every admissible valuation. -/
def GValid (M : GModel Symbol L) (φ : Pattern Symbol) : Prop :=
  ∀ ρ : GValuation M, ρ.IsAdm → ∀ m, ginterp M ρ φ m = ⊤

-- ─────────────────────────────────────────────────────────────
-- Commutation lemmas (mirror HInterpCommutation.lean)
-- ─────────────────────────────────────────────────────────────

section Commutation
variable {M : GModel Symbol L}

theorem ginterp_evarLiftFrom (φ : Pattern Symbol) (k : Nat) (ρ : GValuation M)
    (X : M.Carrier → L) (m : M.Carrier) :
    ginterp M (ρ.shiftEVar k X) (evarLiftFrom k φ) m = ginterp M ρ φ m := by
  induction φ generalizing k ρ m with
  | evar i =>
    simp only [evarLiftFrom, ginterp]
    have h : (ρ.shiftEVar k X).evar (if i ≥ k then i + 1 else i) = ρ.evar i := by
      simp only [GValuation.shiftEVar]; split
      · rename_i hge; simp [Nat.not_lt.mpr (Nat.le_succ_of_le hge), (Nat.lt_succ_of_le hge).ne']
      · rename_i hlt; simp [Nat.lt_of_not_le hlt]
    rw [h]
  | svar => rfl
  | symbol => rfl
  | bot => rfl
  | app _ _ ih₁ ih₂ => simp only [evarLiftFrom, ginterp, ih₁, ih₂]
  | impl _ _ ih₁ ih₂ => simp only [evarLiftFrom, ginterp, ih₁, ih₂]
  | conj _ _ ih₁ ih₂ => simp only [evarLiftFrom, ginterp, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => simp only [evarLiftFrom, ginterp, ih₁, ih₂]
  | exist _ ih =>
    simp only [evarLiftFrom, ginterp]
    congr 1; ext Y
    rw [GValuation.shiftEVar_pushEVar_comm, ih]
  | forallP _ ih =>
    simp only [evarLiftFrom, ginterp]
    congr 1; ext Y
    rw [GValuation.shiftEVar_pushEVar_comm, ih]
  | mu _ ih =>
    simp only [evarLiftFrom, ginterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨S, hS, rfl⟩
      refine ⟨S, fun n => ?_, rfl⟩
      rw [GValuation.shiftEVar_pushSVar_comm] at hS
      exact (ih k (ρ.pushSVar S) n) ▸ hS n
    · rintro ⟨S, hS, rfl⟩
      refine ⟨S, fun n => ?_, rfl⟩
      rw [GValuation.shiftEVar_pushSVar_comm]
      exact (ih k (ρ.pushSVar S) n).symm ▸ hS n
  | nu _ ih =>
    simp only [evarLiftFrom, ginterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨S, hS, rfl⟩
      refine ⟨S, fun n => ?_, rfl⟩
      rw [GValuation.shiftEVar_pushSVar_comm] at hS
      exact (ih k (ρ.pushSVar S) n) ▸ hS n
    · rintro ⟨S, hS, rfl⟩
      refine ⟨S, fun n => ?_, rfl⟩
      rw [GValuation.shiftEVar_pushSVar_comm]
      exact (ih k (ρ.pushSVar S) n).symm ▸ hS n

theorem ginterp_evarLift (φ : Pattern Symbol) (ρ : GValuation M) (X : M.Carrier → L)
    (m : M.Carrier) :
    ginterp M (ρ.pushEVar X) (evarLift φ) m = ginterp M ρ φ m := by
  rw [evarLift, ← GValuation.shiftEVar_zero]
  exact ginterp_evarLiftFrom φ 0 ρ X m

theorem ginterp_svarLiftFrom (φ : Pattern Symbol) (k : Nat) (ρ : GValuation M)
    (S : M.Carrier → L) (m : M.Carrier) :
    ginterp M (ρ.shiftSVar k S) (svarLiftFrom k φ) m = ginterp M ρ φ m := by
  induction φ generalizing k ρ m with
  | evar => rfl
  | svar i =>
    simp only [svarLiftFrom, ginterp]
    rcases Nat.lt_or_ge i k with hlt | hge
    · simp [show ¬(i ≥ k) from Nat.not_le.mpr hlt, GValuation.shiftSVar, hlt]
    · have h1 : ¬(i + 1 < k) := Nat.not_lt.mpr (Nat.le_succ_of_le hge)
      have h2 : i + 1 ≠ k := (Nat.lt_succ_of_le hge).ne'
      simp [show i ≥ k from hge, GValuation.shiftSVar, h1, h2]
  | symbol => rfl
  | bot => rfl
  | app _ _ ih₁ ih₂ => simp only [svarLiftFrom, ginterp, ih₁, ih₂]
  | impl _ _ ih₁ ih₂ => simp only [svarLiftFrom, ginterp, ih₁, ih₂]
  | conj _ _ ih₁ ih₂ => simp only [svarLiftFrom, ginterp, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => simp only [svarLiftFrom, ginterp, ih₁, ih₂]
  | exist _ ih =>
    simp only [svarLiftFrom, ginterp]
    congr 1; ext Y
    rw [GValuation.shiftSVar_pushEVar_comm, ih]
  | forallP _ ih =>
    simp only [svarLiftFrom, ginterp]
    congr 1; ext Y
    rw [GValuation.shiftSVar_pushEVar_comm, ih]
  | mu _ ih =>
    simp only [svarLiftFrom, ginterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]; constructor
    · rintro ⟨T, hT, rfl⟩
      refine ⟨T, fun n => ?_, rfl⟩
      rw [GValuation.shiftSVar_pushSVar_comm] at hT
      exact (ih (k+1) (ρ.pushSVar T) n) ▸ hT n
    · rintro ⟨T, hT, rfl⟩
      refine ⟨T, fun n => ?_, rfl⟩
      rw [GValuation.shiftSVar_pushSVar_comm]
      exact (ih (k+1) (ρ.pushSVar T) n).symm ▸ hT n
  | nu _ ih =>
    simp only [svarLiftFrom, ginterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]; constructor
    · rintro ⟨T, hT, rfl⟩
      refine ⟨T, fun n => ?_, rfl⟩
      rw [GValuation.shiftSVar_pushSVar_comm] at hT
      exact (ih (k+1) (ρ.pushSVar T) n) ▸ hT n
    · rintro ⟨T, hT, rfl⟩
      refine ⟨T, fun n => ?_, rfl⟩
      rw [GValuation.shiftSVar_pushSVar_comm]
      exact (ih (k+1) (ρ.pushSVar T) n).symm ▸ hT n

theorem ginterp_svarLift (φ : Pattern Symbol) (ρ : GValuation M) (S : M.Carrier → L)
    (m : M.Carrier) :
    ginterp M (ρ.pushSVar S) (svarLift φ) m = ginterp M ρ φ m := by
  rw [svarLift, ← GValuation.shiftSVar_zero]
  exact ginterp_svarLiftFrom φ 0 ρ S m

theorem ginterp_svarSubst_aux (φ ψ : Pattern Symbol) (k : Nat) (ρ : GValuation M)
    (m : M.Carrier) :
    ginterp M ρ (svarSubst k ψ φ) m =
    ginterp M (ρ.shiftSVar k (fun n => ginterp M ρ ψ n)) φ m := by
  induction φ generalizing k ψ ρ m with
  | evar => simp [svarSubst, ginterp, GValuation.shiftSVar]
  | svar i =>
    simp only [svarSubst]
    rcases Nat.lt_trichotomy i k with hlt | heq | hgt
    · have hne : (i == k) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlt)
      have hng : ¬(i > k) := Nat.not_lt.mpr (Nat.le_of_lt hlt)
      simp only [hne, Bool.false_eq_true, hng, ↓reduceIte, ginterp,
                 GValuation.shiftSVar, hlt]
    · subst heq; simp [ginterp, GValuation.shiftSVar]
    · have hne : (i == k) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hgt)
      have hnl : ¬(i < k) := Nat.not_lt.mpr (Nat.le_of_lt hgt)
      have hne2 : i ≠ k := Nat.ne_of_gt hgt
      simp only [hne, Bool.false_eq_true, show i > k from hgt, ↓reduceIte, ginterp,
                 GValuation.shiftSVar, hnl, hne2]
  | symbol => simp [svarSubst, ginterp]
  | bot => simp [svarSubst, ginterp]
  | app _ _ ih₁ ih₂ => simp only [svarSubst, ginterp, ih₁, ih₂]
  | impl _ _ ih₁ ih₂ => simp only [svarSubst, ginterp, ih₁, ih₂]
  | conj _ _ ih₁ ih₂ => simp only [svarSubst, ginterp, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => simp only [svarSubst, ginterp, ih₁, ih₂]
  | exist _ ih =>
    simp only [svarSubst, ginterp]
    congr 1; ext Y
    rw [ih (evarLift ψ) k, show (fun n => ginterp M (ρ.pushEVar Y.1) (evarLift ψ) n) =
      (fun n => ginterp M ρ ψ n) from funext (fun n => ginterp_evarLift ψ ρ Y.1 n)]
    rw [← GValuation.shiftSVar_pushEVar_comm]
  | forallP _ ih =>
    simp only [svarSubst, ginterp]
    congr 1; ext Y
    rw [ih (evarLift ψ) k, show (fun n => ginterp M (ρ.pushEVar Y.1) (evarLift ψ) n) =
      (fun n => ginterp M ρ ψ n) from funext (fun n => ginterp_evarLift ψ ρ Y.1 n)]
    rw [← GValuation.shiftSVar_pushEVar_comm]
  | mu _ ih =>
    simp only [svarSubst, ginterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]; constructor
    · rintro ⟨S, hS, rfl⟩
      refine ⟨S, fun n => ?_, rfl⟩
      have key := ih (svarLift ψ) (k+1) (ρ.pushSVar S) n
      rw [show (fun n => ginterp M (ρ.pushSVar S) (svarLift ψ) n) =
        (fun n => ginterp M ρ ψ n) from funext (fun n => ginterp_svarLift ψ ρ S n)] at key
      rw [← GValuation.shiftSVar_pushSVar_comm] at key
      exact key ▸ hS n
    · rintro ⟨S, hS, rfl⟩
      refine ⟨S, fun n => ?_, rfl⟩
      have key := ih (svarLift ψ) (k+1) (ρ.pushSVar S) n
      rw [show (fun n => ginterp M (ρ.pushSVar S) (svarLift ψ) n) =
        (fun n => ginterp M ρ ψ n) from funext (fun n => ginterp_svarLift ψ ρ S n)] at key
      rw [← GValuation.shiftSVar_pushSVar_comm] at key
      exact key.symm ▸ hS n
  | nu _ ih =>
    simp only [svarSubst, ginterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]; constructor
    · rintro ⟨S, hS, rfl⟩
      refine ⟨S, fun n => ?_, rfl⟩
      have key := ih (svarLift ψ) (k+1) (ρ.pushSVar S) n
      rw [show (fun n => ginterp M (ρ.pushSVar S) (svarLift ψ) n) =
        (fun n => ginterp M ρ ψ n) from funext (fun n => ginterp_svarLift ψ ρ S n)] at key
      rw [← GValuation.shiftSVar_pushSVar_comm] at key
      exact key ▸ hS n
    · rintro ⟨S, hS, rfl⟩
      refine ⟨S, fun n => ?_, rfl⟩
      have key := ih (svarLift ψ) (k+1) (ρ.pushSVar S) n
      rw [show (fun n => ginterp M (ρ.pushSVar S) (svarLift ψ) n) =
        (fun n => ginterp M ρ ψ n) from funext (fun n => ginterp_svarLift ψ ρ S n)] at key
      rw [← GValuation.shiftSVar_pushSVar_comm] at key
      exact key.symm ▸ hS n

theorem ginterp_svarSubst (φ ψ : Pattern Symbol) (ρ : GValuation M) (m : M.Carrier) :
    ginterp M ρ (svarSubst 0 ψ φ) m =
    ginterp M (ρ.pushSVar (fun n => ginterp M ρ ψ n)) φ m := by
  rw [ginterp_svarSubst_aux, GValuation.shiftSVar_zero]

theorem ginterp_evarSubst_aux (φ : Pattern Symbol) (k j : Nat) (ρ : GValuation M)
    (m : M.Carrier) :
    ginterp M ρ (evarSubst k (.evar j) φ) m =
    ginterp M (ρ.shiftEVar k (ρ.evar j)) φ m := by
  induction φ generalizing k j ρ m with
  | evar i =>
    simp only [evarSubst]
    split
    · rename_i heq; have := beq_iff_eq.mp heq; subst this
      simp only [ginterp, GValuation.shiftEVar, lt_irrefl, ↓reduceIte]
    · split
      · rename_i hne hgt
        have hne' : i ≠ k := fun h => hne (beq_iff_eq.mpr h)
        simp only [ginterp]
        have : (ρ.shiftEVar k (ρ.evar j)).evar i = ρ.evar (i - 1) := by
          simp [GValuation.shiftEVar, Nat.not_lt.mpr (Nat.le_of_lt hgt), hne']
        rw [this]
      · rename_i hne hle
        have hne' : i ≠ k := fun h => hne (beq_iff_eq.mpr h)
        have hlt : i < k := Nat.lt_of_le_of_ne (Nat.not_lt.mp hle) hne'
        simp only [ginterp]
        have : (ρ.shiftEVar k (ρ.evar j)).evar i = ρ.evar i := by
          simp [GValuation.shiftEVar, hlt]
        rw [this]
  | svar => simp [evarSubst, ginterp, GValuation.shiftEVar]
  | symbol => simp [evarSubst, ginterp]
  | bot => simp [evarSubst, ginterp]
  | app _ _ ih₁ ih₂ => simp only [evarSubst, ginterp, ih₁, ih₂]
  | impl _ _ ih₁ ih₂ => simp only [evarSubst, ginterp, ih₁, ih₂]
  | conj _ _ ih₁ ih₂ => simp only [evarSubst, ginterp, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => simp only [evarSubst, ginterp, ih₁, ih₂]
  | exist _ ih =>
    simp only [evarSubst, evarLift, evarLiftFrom, Nat.zero_le, ↓reduceIte, ginterp]
    congr 1; ext Y
    rw [ih (k + 1) (j + 1)]
    rw [show (ρ.pushEVar Y.1).evar (j + 1) = ρ.evar j from rfl,
        ← GValuation.shiftEVar_pushEVar_comm]
  | forallP _ ih =>
    simp only [evarSubst, evarLift, evarLiftFrom, Nat.zero_le, ↓reduceIte, ginterp]
    congr 1; ext Y
    rw [ih (k + 1) (j + 1)]
    rw [show (ρ.pushEVar Y.1).evar (j + 1) = ρ.evar j from rfl,
        ← GValuation.shiftEVar_pushEVar_comm]
  | mu _ ih =>
    simp only [evarSubst, ginterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]
    have comm : ∀ S, (ρ.shiftEVar k (ρ.evar j)).pushSVar S =
        (ρ.pushSVar S).shiftEVar k ((ρ.pushSVar S).evar j) := fun S =>
      GValuation.ext' (by ext i; simp [GValuation.pushSVar, GValuation.shiftEVar])
                      (by ext i; simp [GValuation.pushSVar, GValuation.shiftEVar])
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S, fun n => by rw [comm S, ← ih k j (ρ.pushSVar S) n]; exact hS n, rfl⟩
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S, fun n => by rw [ih k j (ρ.pushSVar S) n, ← comm S]; exact hS n, rfl⟩
  | nu _ ih =>
    simp only [evarSubst, ginterp]
    congr 1; ext x; simp only [Set.mem_setOf_eq]
    have comm : ∀ S, (ρ.shiftEVar k (ρ.evar j)).pushSVar S =
        (ρ.pushSVar S).shiftEVar k ((ρ.pushSVar S).evar j) := fun S =>
      GValuation.ext' (by ext i; simp [GValuation.pushSVar, GValuation.shiftEVar])
                      (by ext i; simp [GValuation.pushSVar, GValuation.shiftEVar])
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S, fun n => by rw [comm S, ← ih k j (ρ.pushSVar S) n]; exact hS n, rfl⟩
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S, fun n => by rw [ih k j (ρ.pushSVar S) n, ← comm S]; exact hS n, rfl⟩

theorem ginterp_evarSubst (φ : Pattern Symbol) (n : EVarIndex) (ρ : GValuation M)
    (m : M.Carrier) :
    ginterp M ρ (evarSubst 0 (.evar n) φ) m =
    ginterp M (ρ.pushEVar (ρ.evar n)) φ m := by
  rw [ginterp_evarSubst_aux, GValuation.shiftEVar_zero]

end Commutation

-- ─────────────────────────────────────────────────────────────
-- Validity of the individual rules
-- ─────────────────────────────────────────────────────────────

section Validity
variable {M : GModel Symbol L} {ρ : GValuation M}

theorem gvalid_contractionOr {φ : Pattern Symbol} (m : M.Carrier) :
    ginterp M ρ (φ ⊔ φ ⇒ φ) m = ⊤ := by
  simp only [ginterp]; exact himp_eq_top_iff.mpr (le_of_eq (sup_idem _))

theorem gvalid_contractionAnd {φ : Pattern Symbol} (m : M.Carrier) :
    ginterp M ρ (φ ⇒ φ ⊓ φ) m = ⊤ := by
  simp only [ginterp]; exact himp_eq_top_iff.mpr (le_inf le_rfl le_rfl)

theorem gvalid_weakeningOr {φ ψ : Pattern Symbol} (m : M.Carrier) :
    ginterp M ρ (φ ⇒ φ ⊔ ψ) m = ⊤ := by
  simp only [ginterp]; exact himp_eq_top_iff.mpr le_sup_left

theorem gvalid_weakeningAnd {φ ψ : Pattern Symbol} (m : M.Carrier) :
    ginterp M ρ (φ ⊓ ψ ⇒ φ) m = ⊤ := by
  simp only [ginterp]; exact himp_eq_top_iff.mpr inf_le_left

theorem gvalid_permutationOr {φ ψ : Pattern Symbol} (m : M.Carrier) :
    ginterp M ρ (φ ⊔ ψ ⇒ ψ ⊔ φ) m = ⊤ := by
  simp only [ginterp]; exact himp_eq_top_iff.mpr (le_of_eq (sup_comm _ _))

theorem gvalid_permutationAnd {φ ψ : Pattern Symbol} (m : M.Carrier) :
    ginterp M ρ (φ ⊓ ψ ⇒ ψ ⊓ φ) m = ⊤ := by
  simp only [ginterp]; exact himp_eq_top_iff.mpr (le_of_eq (inf_comm _ _))

theorem gvalid_mp {φ ψ : Pattern Symbol} {m : M.Carrier}
    (h₁ : ginterp M ρ (φ ⇒ ψ) m = ⊤) (h₂ : ginterp M ρ φ m = ⊤) :
    ginterp M ρ ψ m = ⊤ := by
  simp only [ginterp] at h₁
  exact top_le_iff.mp (h₂ ▸ himp_eq_top_iff.mp h₁)

theorem gvalid_botElim {φ : Pattern Symbol} (m : M.Carrier) :
    ginterp M ρ ((⊥ₘ : Pattern Symbol) ⇒ φ) m = ⊤ := by
  simp only [ginterp]; exact himp_eq_top_iff.mpr bot_le

theorem gvalid_syllogism {φ ψ χ : Pattern Symbol} {m : M.Carrier}
    (h₁ : ginterp M ρ (φ ⇒ ψ) m = ⊤) (h₂ : ginterp M ρ (ψ ⇒ χ) m = ⊤) :
    ginterp M ρ (φ ⇒ χ) m = ⊤ := by
  simp only [ginterp] at *
  exact himp_eq_top_iff.mpr (le_trans (himp_eq_top_iff.mp h₁) (himp_eq_top_iff.mp h₂))

theorem gvalid_exportation {φ ψ χ : Pattern Symbol} {m : M.Carrier}
    (h : ginterp M ρ (φ ⊓ ψ ⇒ χ) m = ⊤) :
    ginterp M ρ (φ ⇒ ψ ⇒ χ) m = ⊤ := by
  simp only [ginterp] at *
  rw [himp_eq_top_iff, le_himp_iff]
  exact himp_eq_top_iff.mp h

theorem gvalid_importation {φ ψ χ : Pattern Symbol} {m : M.Carrier}
    (h : ginterp M ρ (φ ⇒ ψ ⇒ χ) m = ⊤) :
    ginterp M ρ (φ ⊓ ψ ⇒ χ) m = ⊤ := by
  simp only [ginterp] at *
  exact himp_eq_top_iff.mpr (le_himp_iff.mp (himp_eq_top_iff.mp h))

theorem gvalid_expansion {φ ψ χ : Pattern Symbol} {m : M.Carrier}
    (h : ginterp M ρ (φ ⇒ ψ) m = ⊤) :
    ginterp M ρ (χ ⊔ φ ⇒ χ ⊔ ψ) m = ⊤ := by
  simp only [ginterp] at *
  exact himp_eq_top_iff.mpr (sup_le_sup_left (himp_eq_top_iff.mp h) _)

-- Application: framing and propagation only use the δ axioms.

theorem gvalid_framingLeft {φ₁ φ₂ ψ : Pattern Symbol} (m : M.Carrier)
    (h : ∀ m, ginterp M ρ (φ₁ ⇒ φ₂) m = ⊤) :
    ginterp M ρ (φ₁ ⬝ ψ ⇒ φ₂ ⬝ ψ) m = ⊤ := by
  simp only [ginterp_impl, ginterp_app]
  rw [himp_eq_top_iff]
  apply iSup_le; intro a; apply iSup_le; intro b
  apply le_iSup_of_le a; apply le_iSup_of_le b
  apply inf_le_inf_right; apply inf_le_inf_right
  exact M.δ_mono (himp_eq_top_iff.mp (by simpa only [ginterp_impl] using h a))

theorem gvalid_framingRight {φ₁ φ₂ ψ : Pattern Symbol} (m : M.Carrier)
    (h : ∀ m, ginterp M ρ (φ₁ ⇒ φ₂) m = ⊤) :
    ginterp M ρ (ψ ⬝ φ₁ ⇒ ψ ⬝ φ₂) m = ⊤ := by
  simp only [ginterp_impl, ginterp_app]
  rw [himp_eq_top_iff]
  apply iSup_le; intro a; apply iSup_le; intro b
  apply le_iSup_of_le a; apply le_iSup_of_le b
  apply inf_le_inf_right; apply inf_le_inf_left
  exact M.δ_mono (himp_eq_top_iff.mp (by simpa only [ginterp_impl] using h b))

theorem gvalid_propagationOrLeft {φ₁ φ₂ ψ : Pattern Symbol} (m : M.Carrier) :
    ginterp M ρ ((φ₁ ⊔ φ₂) ⬝ ψ ⇒ φ₁ ⬝ ψ ⊔ φ₂ ⬝ ψ) m = ⊤ := by
  simp only [ginterp_app, ginterp_disj, ginterp_impl]; rw [himp_eq_top_iff]
  apply iSup_le; intro a; apply iSup_le; intro b
  refine le_trans (inf_le_inf_right _ (inf_le_inf_right _ (M.δ_sup _ _))) ?_
  rw [inf_sup_right, inf_sup_right]
  exact sup_le_sup (le_iSup₂_of_le a b le_rfl) (le_iSup₂_of_le a b le_rfl)

theorem gvalid_propagationOrRight {φ₁ φ₂ ψ : Pattern Symbol} (m : M.Carrier) :
    ginterp M ρ (ψ ⬝ (φ₁ ⊔ φ₂) ⇒ ψ ⬝ φ₁ ⊔ ψ ⬝ φ₂) m = ⊤ := by
  simp only [ginterp_app, ginterp_disj, ginterp_impl]; rw [himp_eq_top_iff]
  apply iSup_le; intro a; apply iSup_le; intro b
  refine le_trans (inf_le_inf_right _ (inf_le_inf_left _ (M.δ_sup _ _))) ?_
  rw [inf_assoc, inf_sup_right, inf_sup_left, ← inf_assoc, ← inf_assoc]
  exact sup_le_sup (le_iSup₂_of_le a b le_rfl) (le_iSup₂_of_le a b le_rfl)

theorem gvalid_propagationExistLeft {φ ψ : Pattern Symbol} (m : M.Carrier) :
    ginterp M ρ ((∃ₑ φ) ⬝ ψ ⇒ ∃ₑ (φ ⬝ evarLift ψ)) m = ⊤ := by
  simp only [ginterp_impl, ginterp_app, ginterp_exist]
  rw [himp_eq_top_iff]
  apply iSup_le; intro a; apply iSup_le; intro b
  refine le_trans (inf_le_inf_right _ (inf_le_inf_right _
    (M.δ_iSup (fun X => ginterp M (ρ.pushEVar X.1) φ a)))) ?_
  rw [iSup_inf_eq, iSup_inf_eq]
  apply iSup_le; intro X
  apply le_iSup_of_le X; apply le_iSup_of_le a; apply le_iSup_of_le b
  rw [ginterp_evarLift]

theorem gvalid_propagationExistRight {φ ψ : Pattern Symbol} (m : M.Carrier) :
    ginterp M ρ (ψ ⬝ (∃ₑ φ) ⇒ ∃ₑ (evarLift ψ ⬝ φ)) m = ⊤ := by
  simp only [ginterp_impl, ginterp_app, ginterp_exist]
  rw [himp_eq_top_iff]
  apply iSup_le; intro a; apply iSup_le; intro b
  refine le_trans (inf_le_inf_right _ (inf_le_inf_left _
    (M.δ_iSup (fun X => ginterp M (ρ.pushEVar X.1) φ b)))) ?_
  rw [inf_iSup_eq, iSup_inf_eq]
  apply iSup_le; intro X
  apply le_iSup_of_le X; apply le_iSup_of_le a; apply le_iSup_of_le b
  rw [ginterp_evarLift]

-- Quantifiers (these are where admissibility enters).

theorem gvalid_existQuant {φ : Pattern Symbol} {n : EVarIndex} (hadm : ρ.IsAdm)
    (m : M.Carrier) :
    ginterp M ρ (evarSubst 0 (.evar n) φ ⇒ ∃ₑ φ) m = ⊤ := by
  simp only [ginterp_impl, ginterp_exist]; rw [himp_eq_top_iff, ginterp_evarSubst]
  exact le_iSup (fun X : M.Adm => ginterp M (ρ.pushEVar X.1) φ m) ⟨ρ.evar n, hadm n⟩

theorem gvalid_existGen {φ₁ φ₂ : Pattern Symbol} (hadm : ρ.IsAdm)
    (h : ∀ (ρ : GValuation M), ρ.IsAdm → ∀ m, ginterp M ρ (φ₁ ⇒ evarLift φ₂) m = ⊤)
    (m : M.Carrier) :
    ginterp M ρ (∃ₑ φ₁ ⇒ φ₂) m = ⊤ := by
  simp only [ginterp_impl, ginterp_exist]; rw [himp_eq_top_iff]
  apply iSup_le; intro X
  have := himp_eq_top_iff.mp (by
    simpa only [ginterp_impl] using h (ρ.pushEVar X.1) (hadm.pushEVar X.2) m)
  rwa [ginterp_evarLift] at this

theorem gvalid_forallQuant {φ : Pattern Symbol} {n : EVarIndex} (hadm : ρ.IsAdm)
    (m : M.Carrier) :
    ginterp M ρ (∀ₑ φ ⇒ evarSubst 0 (.evar n) φ) m = ⊤ := by
  simp only [ginterp_impl, ginterp_forall]; rw [himp_eq_top_iff, ginterp_evarSubst]
  exact iInf_le (fun X : M.Adm => ginterp M (ρ.pushEVar X.1) φ m) ⟨ρ.evar n, hadm n⟩

theorem gvalid_forallGen {φ₁ φ₂ : Pattern Symbol} (hadm : ρ.IsAdm)
    (h : ∀ (ρ : GValuation M), ρ.IsAdm → ∀ m, ginterp M ρ (evarLift φ₁ ⇒ φ₂) m = ⊤)
    (m : M.Carrier) :
    ginterp M ρ (φ₁ ⇒ ∀ₑ φ₂) m = ⊤ := by
  simp only [ginterp_impl, ginterp_forall]; rw [himp_eq_top_iff]
  apply le_iInf; intro X
  have := himp_eq_top_iff.mp (by
    simpa only [ginterp_impl] using h (ρ.pushEVar X.1) (hadm.pushEVar X.2) m)
  rwa [ginterp_evarLift] at this

theorem gvalid_existence (m : M.Carrier) :
    ginterp M ρ (∃ₑ (.evar 0 : Pattern Symbol)) m = ⊤ := by
  simp only [ginterp_exist]
  obtain ⟨X, hX, hXm⟩ := M.adm_cover m
  apply eq_top_iff.mpr
  apply le_iSup_of_le ⟨X, hX⟩
  exact le_of_eq hXm.symm

theorem gvalid_svSubst {φ ψ : Pattern Symbol} (hadm : ρ.IsAdm)
    (h : ∀ (ρ : GValuation M), ρ.IsAdm → ∀ m, ginterp M ρ φ m = ⊤) (m : M.Carrier) :
    ginterp M ρ (svarSubst 0 ψ φ) m = ⊤ := by
  rw [ginterp_svarSubst]; exact h _ (hadm.pushSVar _) _

end Validity

-- ─────────────────────────────────────────────────────────────
-- Monotonicity from positivity
-- ─────────────────────────────────────────────────────────────

private def gpushSVar_mono_args {M : GModel Symbol L} {n : SVarIndex}
    {ρ₁ ρ₂ : GValuation M} (R : M.Carrier → L)
    (hevar : ρ₁.evar = ρ₂.evar)
    (hsvar_eq : ∀ i, i ≠ n → ρ₁.svar i = ρ₂.svar i)
    (hsvar_le : ∀ m, ρ₁.svar n m ≤ ρ₂.svar n m) :
    (ρ₁.pushSVar R).evar = (ρ₂.pushSVar R).evar ∧
    (∀ i, i ≠ n + 1 → (ρ₁.pushSVar R).svar i = (ρ₂.pushSVar R).svar i) ∧
    (∀ m, (ρ₁.pushSVar R).svar (n + 1) m ≤ (ρ₂.pushSVar R).svar (n + 1) m) :=
  ⟨hevar, fun i hi => by
    cases i with
    | zero => rfl
    | succ j => exact hsvar_eq j (fun h => hi (congrArg _ h)),
   fun m => hsvar_le m⟩

mutual
def ginterp_mono_pos {Symbol : Type} {L : Type*} [Order.Frame L]
    {M : GModel Symbol L} {φ : Pattern Symbol} {n : SVarIndex}
    (hpos : SVarPositive φ n) (ρ₁ ρ₂ : GValuation M)
    (hevar : ρ₁.evar = ρ₂.evar)
    (hsvar_eq : ∀ i, i ≠ n → ρ₁.svar i = ρ₂.svar i)
    (hsvar_le : ∀ m, ρ₁.svar n m ≤ ρ₂.svar n m)
    (m : M.Carrier) :
    ginterp M ρ₁ φ m ≤ ginterp M ρ₂ φ m :=
  match hpos with
  | .evar (i := i) => by simp only [ginterp]; rw [show ρ₁.evar i = ρ₂.evar i from congrFun hevar i]
  | .svar => hsvar_le m
  | .svarNe hne => by simp only [ginterp]; rw [show ρ₁.svar _ = ρ₂.svar _ from hsvar_eq _ hne]
  | .symbol => le_refl _
  | .bot => le_refl _
  | .app hpφ hpψ => by
    simp only [ginterp]
    exact iSup_mono fun a => iSup_mono fun b =>
      inf_le_inf_right _ (inf_le_inf
        (M.δ_mono (ginterp_mono_pos hpφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le a))
        (M.δ_mono (ginterp_mono_pos hpψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le b)))
  | .impl hnφ hpψ => by
    simp only [ginterp]
    exact himp_le_himp
      (ginterp_mono_neg hnφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
      (ginterp_mono_pos hpψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
  | .conj hpφ hpψ => by
    simp only [ginterp]
    exact inf_le_inf
      (ginterp_mono_pos hpφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
      (ginterp_mono_pos hpψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
  | .disj hpφ hpψ => by
    simp only [ginterp]
    exact sup_le_sup
      (ginterp_mono_pos hpφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
      (ginterp_mono_pos hpψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
  | .exist hpφ => by
    simp only [ginterp]
    exact iSup_mono fun X =>
      ginterp_mono_pos hpφ (ρ₁.pushEVar X.1) (ρ₂.pushEVar X.1)
        (by ext i; cases i <;> simp [GValuation.pushEVar, hevar])
        (fun i hi => hsvar_eq i hi) hsvar_le m
  | .forallP hpφ => by
    simp only [ginterp]
    exact iInf_mono fun X =>
      ginterp_mono_pos hpφ (ρ₁.pushEVar X.1) (ρ₂.pushEVar X.1)
        (by ext i; cases i <;> simp [GValuation.pushEVar, hevar])
        (fun i hi => hsvar_eq i hi) hsvar_le m
  | .mu hpφ => by
    simp only [ginterp]
    apply sInf_le_sInf; intro x ⟨R, hR, hx⟩
    let ⟨he, hs, hl⟩ := gpushSVar_mono_args R hevar hsvar_eq hsvar_le
    exact ⟨R, fun k => le_trans (ginterp_mono_pos hpφ _ _ he hs hl k) (hR k), hx⟩
  | .nu hpφ => by
    simp only [ginterp]
    apply sSup_le_sSup; intro x ⟨R, hR, hx⟩
    let ⟨he, hs, hl⟩ := gpushSVar_mono_args R hevar hsvar_eq hsvar_le
    exact ⟨R, fun k => le_trans (hR k) (ginterp_mono_pos hpφ _ _ he hs hl k), hx⟩

def ginterp_mono_neg {Symbol : Type} {L : Type*} [Order.Frame L]
    {M : GModel Symbol L} {φ : Pattern Symbol} {n : SVarIndex}
    (hneg : SVarNegative φ n) (ρ₁ ρ₂ : GValuation M)
    (hevar : ρ₁.evar = ρ₂.evar)
    (hsvar_eq : ∀ i, i ≠ n → ρ₁.svar i = ρ₂.svar i)
    (hsvar_le : ∀ m, ρ₁.svar n m ≤ ρ₂.svar n m)
    (m : M.Carrier) :
    ginterp M ρ₂ φ m ≤ ginterp M ρ₁ φ m :=
  match hneg with
  | .evar (i := i) => by simp only [ginterp]; rw [show ρ₁.evar i = ρ₂.evar i from congrFun hevar i]
  | .svarNe hne => by simp only [ginterp]; rw [show ρ₁.svar _ = ρ₂.svar _ from hsvar_eq _ hne]
  | .symbol => le_refl _
  | .bot => le_refl _
  | .app hnφ hnψ => by
    simp only [ginterp]
    exact iSup_mono fun a => iSup_mono fun b =>
      inf_le_inf_right _ (inf_le_inf
        (M.δ_mono (ginterp_mono_neg hnφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le a))
        (M.δ_mono (ginterp_mono_neg hnψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le b)))
  | .impl hpφ hnψ => by
    simp only [ginterp]
    exact himp_le_himp
      (ginterp_mono_pos hpφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
      (ginterp_mono_neg hnψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
  | .conj hnφ hnψ => by
    simp only [ginterp]
    exact inf_le_inf
      (ginterp_mono_neg hnφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
      (ginterp_mono_neg hnψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
  | .disj hnφ hnψ => by
    simp only [ginterp]
    exact sup_le_sup
      (ginterp_mono_neg hnφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
      (ginterp_mono_neg hnψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
  | .exist hnφ => by
    simp only [ginterp]
    exact iSup_mono fun X =>
      ginterp_mono_neg hnφ (ρ₁.pushEVar X.1) (ρ₂.pushEVar X.1)
        (by ext i; cases i <;> simp [GValuation.pushEVar, hevar])
        (fun i hi => hsvar_eq i hi) hsvar_le m
  | .forallP hnφ => by
    simp only [ginterp]
    exact iInf_mono fun X =>
      ginterp_mono_neg hnφ (ρ₁.pushEVar X.1) (ρ₂.pushEVar X.1)
        (by ext i; cases i <;> simp [GValuation.pushEVar, hevar])
        (fun i hi => hsvar_eq i hi) hsvar_le m
  | .mu hnφ => by
    simp only [ginterp]
    apply sInf_le_sInf; intro x ⟨R, hR, hx⟩
    let ⟨he, hs, hl⟩ := gpushSVar_mono_args R hevar hsvar_eq hsvar_le
    exact ⟨R, fun k => le_trans (ginterp_mono_neg hnφ _ _ he hs hl k) (hR k), hx⟩
  | .nu hnφ => by
    simp only [ginterp]
    apply sSup_le_sSup; intro x ⟨R, hR, hx⟩
    let ⟨he, hs, hl⟩ := gpushSVar_mono_args R hevar hsvar_eq hsvar_le
    exact ⟨R, fun k => le_trans (hR k) (ginterp_mono_neg hnφ _ _ he hs hl k), hx⟩
end

section Fixpoints
variable {M : GModel Symbol L} {ρ : GValuation M}

theorem gvalid_preFixpoint {φ : Pattern Symbol}
    (hpos : SVarPositive φ 0) (m : M.Carrier) :
    ginterp M ρ (svarSubst 0 (μ φ) φ ⇒ μ φ) m = ⊤ := by
  simp only [ginterp]; rw [himp_eq_top_iff, ginterp_svarSubst]
  apply le_sInf; intro x ⟨S, hS, hx⟩; subst hx
  have hmu_le : ∀ k, ginterp M ρ (μ φ) k ≤ S k := fun k => by
    apply sInf_le; exact ⟨S, hS, rfl⟩
  exact le_trans
    (ginterp_mono_pos hpos (ρ.pushSVar (fun n => ginterp M ρ (μ φ) n)) (ρ.pushSVar S)
      rfl (fun i hi => by cases i with
        | zero => exact absurd rfl hi
        | succ j => rfl)
      hmu_le m)
    (hS m)

theorem gvalid_knasterTarski {φ ψ : Pattern Symbol}
    (h : ∀ m, ginterp M ρ (svarSubst 0 ψ φ ⇒ ψ) m = ⊤) (m : M.Carrier) :
    ginterp M ρ (μ φ ⇒ ψ) m = ⊤ := by
  simp only [ginterp]; rw [himp_eq_top_iff]
  have hpre : ∀ n, ginterp M (ρ.pushSVar (fun n => ginterp M ρ ψ n)) φ n ≤
      ginterp M ρ ψ n := fun n => by
    have := h n; simp only [ginterp] at this
    exact himp_eq_top_iff.mp (by rw [ginterp_svarSubst] at this; exact this)
  apply sInf_le
  exact ⟨fun n => ginterp M ρ ψ n, hpre, rfl⟩

theorem gvalid_postFixpoint {φ : Pattern Symbol}
    (hpos : SVarPositive φ 0) (m : M.Carrier) :
    ginterp M ρ (ν φ ⇒ svarSubst 0 (ν φ) φ) m = ⊤ := by
  simp only [ginterp]; rw [himp_eq_top_iff, ginterp_svarSubst]
  apply sSup_le; intro x ⟨S, hS, hx⟩; subst hx
  have hnu_ge : ∀ k, S k ≤ ginterp M ρ (ν φ) k := fun k => by
    apply le_sSup; exact ⟨S, hS, rfl⟩
  exact le_trans (hS m)
    (ginterp_mono_pos hpos (ρ.pushSVar S) (ρ.pushSVar (fun n => ginterp M ρ (ν φ) n))
      rfl (fun i hi => by cases i with
        | zero => exact absurd rfl hi
        | succ j => rfl)
      hnu_ge m)

theorem gvalid_park {φ ψ : Pattern Symbol}
    (h : ∀ m, ginterp M ρ (ψ ⇒ svarSubst 0 ψ φ) m = ⊤) (m : M.Carrier) :
    ginterp M ρ (ψ ⇒ ν φ) m = ⊤ := by
  simp only [ginterp]; rw [himp_eq_top_iff]
  have hpost : ∀ n, ginterp M ρ ψ n ≤
      ginterp M (ρ.pushSVar (fun n => ginterp M ρ ψ n)) φ n := fun n => by
    have := h n; simp only [ginterp] at this
    exact himp_eq_top_iff.mp (by rw [ginterp_svarSubst] at this; exact this)
  apply le_sSup
  exact ⟨fun n => ginterp M ρ ψ n, hpost, rfl⟩

end Fixpoints

-- ─────────────────────────────────────────────────────────────
-- Soundness of `ProofCore` over generalized models
-- ─────────────────────────────────────────────────────────────

/-- Every `ProofCore Ax` derivation is valid in every generalized model validating `Ax`
(and the assumptions `Γ`). -/
theorem gsoundness {Symbol : Type} {ι : Type} {Ax : ι → Pattern Symbol}
    {Γ : Set (Pattern Symbol)} {φ : Pattern Symbol} (h : Γ ⊩[Ax] φ) :
    ∀ (L : Type*) [Order.Frame L] (M : GModel Symbol L),
    (∀ i, GValid M (Ax i)) → (∀ γ ∈ Γ, GValid M γ) → GValid M φ := by
  induction h with
  | ax i => exact fun _ _ M hAx _ ρ hρ m => hAx i ρ hρ m
  | assumption hmem => exact fun _ _ M _ hΓ ρ hρ m => hΓ _ hmem ρ hρ m
  | contractionOr => exact fun _ _ _ _ _ _ _ m => gvalid_contractionOr m
  | contractionAnd => exact fun _ _ _ _ _ _ _ m => gvalid_contractionAnd m
  | weakeningOr => exact fun _ _ _ _ _ _ _ m => gvalid_weakeningOr m
  | weakeningAnd => exact fun _ _ _ _ _ _ _ m => gvalid_weakeningAnd m
  | permutationOr => exact fun _ _ _ _ _ _ _ m => gvalid_permutationOr m
  | permutationAnd => exact fun _ _ _ _ _ _ _ m => gvalid_permutationAnd m
  | mp _ _ ih₁ ih₂ =>
    exact fun L _ M hAx hΓ ρ hρ m =>
      gvalid_mp (ih₁ L M hAx hΓ ρ hρ m) (ih₂ L M hAx hΓ ρ hρ m)
  | botElim => exact fun _ _ _ _ _ _ _ m => gvalid_botElim m
  | syllogism _ _ ih₁ ih₂ =>
    exact fun L _ M hAx hΓ ρ hρ m =>
      gvalid_syllogism (ih₁ L M hAx hΓ ρ hρ m) (ih₂ L M hAx hΓ ρ hρ m)
  | exportation _ ih =>
    exact fun L _ M hAx hΓ ρ hρ m => gvalid_exportation (ih L M hAx hΓ ρ hρ m)
  | importation _ ih =>
    exact fun L _ M hAx hΓ ρ hρ m => gvalid_importation (ih L M hAx hΓ ρ hρ m)
  | expansion _ ih =>
    exact fun L _ M hAx hΓ ρ hρ m => gvalid_expansion (ih L M hAx hΓ ρ hρ m)
  | existQuant => exact fun _ _ _ _ _ _ hρ m => gvalid_existQuant hρ m
  | existGen _ ih =>
    exact fun L _ M hAx hΓ ρ hρ m => gvalid_existGen hρ (ih L M hAx hΓ) m
  | forallQuant => exact fun _ _ _ _ _ _ hρ m => gvalid_forallQuant hρ m
  | forallGen _ ih =>
    exact fun L _ M hAx hΓ ρ hρ m => gvalid_forallGen hρ (ih L M hAx hΓ) m
  | existence => exact fun _ _ _ _ _ _ _ m => gvalid_existence m
  | svSubst _ ih =>
    exact fun L _ M hAx hΓ ρ hρ m => gvalid_svSubst hρ (ih L M hAx hΓ) m
  | preFixpoint hpos =>
    exact fun _ _ _ _ _ _ _ m => gvalid_preFixpoint hpos m
  | knasterTarski _ ih =>
    exact fun L _ M hAx hΓ ρ hρ m => gvalid_knasterTarski (ih L M hAx hΓ ρ hρ) m
  | postFixpoint hpos =>
    exact fun _ _ _ _ _ _ _ m => gvalid_postFixpoint hpos m
  | park _ ih =>
    exact fun L _ M hAx hΓ ρ hρ m => gvalid_park (ih L M hAx hΓ ρ hρ) m
  | propagationOrLeft =>
    exact fun _ _ _ _ _ _ _ m => gvalid_propagationOrLeft m
  | propagationOrRight =>
    exact fun _ _ _ _ _ _ _ m => gvalid_propagationOrRight m
  | propagationExistLeft =>
    exact fun _ _ _ _ _ _ _ m => gvalid_propagationExistLeft m
  | propagationExistRight =>
    exact fun _ _ _ _ _ _ _ m => gvalid_propagationExistRight m
  | framingLeft _ ih =>
    exact fun L _ M hAx hΓ ρ hρ m => gvalid_framingLeft m (ih L M hAx hΓ ρ hρ)
  | framingRight _ ih =>
    exact fun L _ M hAx hΓ ρ hρ m => gvalid_framingRight m (ih L M hAx hΓ ρ hρ)

end IML
