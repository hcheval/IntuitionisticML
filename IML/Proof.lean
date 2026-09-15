import IML.Substitution

/-!
# The proof system of iML

The Hilbert system `Proof`. Its SINGLETON rule is the *positive* form

    singletonStrong : C₁[x ⊓ φ] ⊓ C₂[x ⊓ ψ] ⇒ C₂[x ⊓ (φ ⊓ ψ)]

("an element variable matches at most one element, so information about it can
be transported between contexts"). The classical negative form
`~(C₁[x ⊓ φ] ⊓ C₂[x ⊓ ~φ])` of the published system (kept verbatim in
`IML.Crisp.Proof`) is the derived rule `Proof.singleton` below, obtained by
taking `ψ := ~φ` and propagating `⊥` out of `C₂`. Intuitionistically the
positive rule is strictly stronger (`IML/SingletonAlt/`): it is what the
definedness theory needs (`C[φ] ⇒ ⌈φ⌉`, Membership∧), and it is sound for the
Heyting semantics (`IML.hvalid_singletonStrong`). Classically the two are
interderivable.
-/

namespace IML

open Pattern

-- ─────────────────────────────────────────────────────────────
-- Positivity (same structure as classical, extended for new constructors)
-- ─────────────────────────────────────────────────────────────

mutual

inductive SVarPositive {Symbol : Type} : Pattern Symbol → SVarIndex → Prop where
  | evar   {i n}   : SVarPositive (.evar i) n
  | svar   {n}     : SVarPositive (.svar n) n
  | svarNe {i n}   : i ≠ n → SVarPositive (.svar i) n
  | symbol {s n}   : SVarPositive (.symbol s) n
  | app    {φ ψ n} : SVarPositive φ n → SVarPositive ψ n → SVarPositive (φ ⬝ ψ) n
  | bot    {n}     : SVarPositive (⊥ₘ : Pattern Symbol) n
  | impl   {φ ψ n} : SVarNegative φ n → SVarPositive ψ n → SVarPositive (φ ⇒ ψ) n
  | conj   {φ ψ n} : SVarPositive φ n → SVarPositive ψ n → SVarPositive (φ ⊓ ψ) n
  | disj   {φ ψ n} : SVarPositive φ n → SVarPositive ψ n → SVarPositive (φ ⊔ ψ) n
  | exist  {φ n}   : SVarPositive φ n → SVarPositive (∃ₑ φ) n
  | forallP {φ n}  : SVarPositive φ n → SVarPositive (∀ₑ φ) n
  | mu     {φ n}   : SVarPositive φ (n + 1) → SVarPositive (μ φ) n
  | nu     {φ n}   : SVarPositive φ (n + 1) → SVarPositive (ν φ) n

inductive SVarNegative {Symbol : Type} : Pattern Symbol → SVarIndex → Prop where
  | evar   {i n}   : SVarNegative (.evar i) n
  | svarNe {i n}   : i ≠ n → SVarNegative (.svar i) n
  | symbol {s n}   : SVarNegative (.symbol s) n
  | app    {φ ψ n} : SVarNegative φ n → SVarNegative ψ n → SVarNegative (φ ⬝ ψ) n
  | bot    {n}     : SVarNegative (⊥ₘ : Pattern Symbol) n
  | impl   {φ ψ n} : SVarPositive φ n → SVarNegative ψ n → SVarNegative (φ ⇒ ψ) n
  | conj   {φ ψ n} : SVarNegative φ n → SVarNegative ψ n → SVarNegative (φ ⊓ ψ) n
  | disj   {φ ψ n} : SVarNegative φ n → SVarNegative ψ n → SVarNegative (φ ⊔ ψ) n
  | exist  {φ n}   : SVarNegative φ n → SVarNegative (∃ₑ φ) n
  | forallP {φ n}  : SVarNegative φ n → SVarNegative (∀ₑ φ) n
  | mu     {φ n}   : SVarNegative φ (n + 1) → SVarNegative (μ φ) n
  | nu     {φ n}   : SVarNegative φ (n + 1) → SVarNegative (ν φ) n

end

-- ─────────────────────────────────────────────────────────────
-- Application contexts (same as classical)
-- ─────────────────────────────────────────────────────────────

inductive AppCtx (Symbol : Type) where
  | hole  : AppCtx Symbol
  | left  : AppCtx Symbol → Pattern Symbol → AppCtx Symbol
  | right : Pattern Symbol → AppCtx Symbol → AppCtx Symbol

def AppCtx.fill {Symbol : Type} : AppCtx Symbol → Pattern Symbol → Pattern Symbol
  | .hole, φ     => φ
  | .left C ψ, φ => (C.fill φ) ⬝ ψ
  | .right ψ C, φ => ψ ⬝ (C.fill φ)

/-- Lift the free element variables of a context. -/
def AppCtx.lift {Symbol : Type} (k : Nat) : AppCtx Symbol → AppCtx Symbol
  | .hole => .hole
  | .left C ψ => .left (AppCtx.lift k C) (evarLiftFrom k ψ)
  | .right ψ C => .right (evarLiftFrom k ψ) (AppCtx.lift k C)

theorem AppCtx.fill_lift {Symbol : Type} (k : Nat) (C : AppCtx Symbol) (φ : Pattern Symbol) :
    evarLiftFrom k (C.fill φ) = (C.lift k).fill (evarLiftFrom k φ) := by
  induction C with
  | hole => rfl
  | left C ψ ih => simp only [AppCtx.fill, AppCtx.lift, evarLiftFrom, ih]
  | right ψ C ih => simp only [AppCtx.fill, AppCtx.lift, evarLiftFrom, ih]

theorem evarLift_ctxBot_impl_bot {Symbol : Type} (C : AppCtx Symbol) :
    evarLift (C.fill ⊥ₘ ⇒ ⊥ₘ) = ((C.lift 0).fill ⊥ₘ ⇒ ⊥ₘ) := by
  simp only [evarLift, evarLiftFrom, AppCtx.fill_lift]

-- ─────────────────────────────────────────────────────────────
-- Proof system for intuitionistic AML
-- ─────────────────────────────────────────────────────────────

inductive Proof {Symbol : Type} (Γ : Set (Pattern Symbol)) :
    Pattern Symbol → Type where
  -- Assumption
  | assumption {φ} : φ ∈ Γ → Proof Γ φ
  -- Contraction
  | contractionOr {φ}    : Proof Γ (φ ⊔ φ ⇒ φ)
  | contractionAnd {φ}   : Proof Γ (φ ⇒ φ ⊓ φ)
  -- Weakening
  | weakeningOr {φ ψ}    : Proof Γ (φ ⇒ φ ⊔ ψ)
  | weakeningAnd {φ ψ}   : Proof Γ (φ ⊓ ψ ⇒ φ)
  -- Permutation
  | permutationOr {φ ψ}  : Proof Γ (φ ⊔ ψ ⇒ ψ ⊔ φ)
  | permutationAnd {φ ψ} : Proof Γ (φ ⊓ ψ ⇒ ψ ⊓ φ)
  -- Modus ponens
  | mp {φ ψ} : Proof Γ (φ ⇒ ψ) → Proof Γ φ → Proof Γ ψ
  -- Bottom
  | botElim {φ} : Proof Γ (⊥ₘ ⇒ φ)
  -- Syllogism
  | syllogism {φ ψ χ} :
      Proof Γ (φ ⇒ ψ) → Proof Γ (ψ ⇒ χ) → Proof Γ (φ ⇒ χ)
  -- Exportation / Importation
  | exportation {φ ψ χ} :
      Proof Γ (φ ⊓ ψ ⇒ χ) → Proof Γ (φ ⇒ ψ ⇒ χ)
  | importation {φ ψ χ} :
      Proof Γ (φ ⇒ ψ ⇒ χ) → Proof Γ (φ ⊓ ψ ⇒ χ)
  -- Expansion
  | expansion {φ ψ χ} :
      Proof Γ (φ ⇒ ψ) → Proof Γ (χ ⊔ φ ⇒ χ ⊔ ψ)
  -- Existential quantifier
  | existQuant {φ} {n : EVarIndex} :
      Proof Γ (evarSubst 0 (.evar n) φ ⇒ ∃ₑ φ)
  | existGen {φ₁ φ₂} :
      Proof Γ (φ₁ ⇒ evarLift φ₂) → Proof Γ (∃ₑ φ₁ ⇒ φ₂)
  -- Universal quantifier
  | forallQuant {φ} {n : EVarIndex} :
      Proof Γ (∀ₑ φ ⇒ evarSubst 0 (.evar n) φ)
  | forallGen {φ₁ φ₂} :
      Proof Γ (evarLift φ₁ ⇒ φ₂) → Proof Γ (φ₁ ⇒ ∀ₑ φ₂)
  -- Existence
  | existence : Proof Γ (∃ₑ (.evar 0 : Pattern Symbol))
  -- Set variable substitution
  | svSubst {φ ψ} : Proof Γ φ → Proof Γ (svarSubst 0 ψ φ)
  -- Least fixpoint (μ)
  | preFixpoint {φ} :
      SVarPositive φ 0 →
      Proof Γ (svarSubst 0 (μ φ) φ ⇒ μ φ)
  | knasterTarski {φ ψ} :
      Proof Γ (svarSubst 0 ψ φ ⇒ ψ) →
      Proof Γ (μ φ ⇒ ψ)
  -- Greatest fixpoint (ν)
  | postFixpoint {φ} :
      SVarPositive φ 0 →
      Proof Γ (ν φ ⇒ svarSubst 0 (ν φ) φ)
  | park {φ ψ} :
      Proof Γ (ψ ⇒ svarSubst 0 ψ φ) →
      Proof Γ (ψ ⇒ ν φ)
  -- Application: SINGLETON (positive form), propagation of ∨ and ∃ out of
  -- contexts, framing
  | singletonStrong {C₁ C₂ : AppCtx Symbol} {n : EVarIndex} {φ ψ} :
      Proof Γ (C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n ⊓ ψ) ⇒ C₂.fill (.evar n ⊓ (φ ⊓ ψ)))
  | propagationOrLeft {φ₁ φ₂ ψ} :
      Proof Γ ((φ₁ ⊔ φ₂) ⬝ ψ ⇒ φ₁ ⬝ ψ ⊔ φ₂ ⬝ ψ)
  | propagationOrRight {φ₁ φ₂ ψ} :
      Proof Γ (ψ ⬝ (φ₁ ⊔ φ₂) ⇒ ψ ⬝ φ₁ ⊔ ψ ⬝ φ₂)
  | propagationExistLeft {φ ψ} :
      Proof Γ ((∃ₑ φ) ⬝ ψ ⇒ ∃ₑ (φ ⬝ evarLift ψ))
  | propagationExistRight {φ ψ} :
      Proof Γ (ψ ⬝ (∃ₑ φ) ⇒ ∃ₑ (evarLift ψ ⬝ φ))
  | framingLeft {φ₁ φ₂ ψ} :
      Proof Γ (φ₁ ⇒ φ₂) → Proof Γ (φ₁ ⬝ ψ ⇒ φ₂ ⬝ ψ)
  | framingRight {φ₁ φ₂ ψ} :
      Proof Γ (φ₁ ⇒ φ₂) → Proof Γ (ψ ⬝ φ₁ ⇒ ψ ⬝ φ₂)

scoped notation:25 Γ " ⊩ᵢ " φ => Proof Γ φ

-- ─────────────────────────────────────────────────────────────
-- The classical (negative) SINGLETON rule is derived
-- ─────────────────────────────────────────────────────────────

namespace Proof

variable {Symbol : Type} {Γ : Set (Pattern Symbol)} {φ ψ χ : Pattern Symbol}

-- A minimal propositional toolkit, enough for the derivation below. The
-- full toolkit is in `IML.DerivedRules.Propositional`.

private def idP (φ : Pattern Symbol) : Γ ⊩ᵢ φ ⇒ φ :=
  syllogism contractionAnd weakeningAnd

private def weakeningAnd' : Γ ⊩ᵢ φ ⊓ ψ ⇒ ψ :=
  syllogism permutationAnd weakeningAnd

private def andMonoL (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ φ ⊓ χ ⇒ ψ ⊓ χ :=
  importation (syllogism h (exportation (idP (ψ ⊓ χ))))

private def andMonoR (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ χ ⊓ φ ⇒ χ ⊓ ψ :=
  syllogism permutationAnd (syllogism (andMonoL h) permutationAnd)

private def andIntro (h₁ : Γ ⊩ᵢ φ ⇒ ψ) (h₂ : Γ ⊩ᵢ φ ⇒ χ) : Γ ⊩ᵢ φ ⇒ ψ ⊓ χ :=
  syllogism contractionAnd (syllogism (andMonoL h₁) (andMonoR h₂))

private def negElim : Γ ⊩ᵢ φ ⊓ ~φ ⇒ ⊥ₘ :=
  syllogism permutationAnd (importation (idP (φ ⇒ ⊥ₘ)))

private def topIntro : Γ ⊩ᵢ φ ⇒ ⊤ₘ :=
  exportation (weakeningAnd' (φ := φ) (ψ := ⊥ₘ))

private def andTop : Γ ⊩ᵢ φ ⇒ φ ⊓ ⊤ₘ := andIntro (idP φ) topIntro

/-- Framing through a whole context. -/
private def ctxMono (C : AppCtx Symbol) (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ C.fill φ ⇒ C.fill ψ :=
  match C with
  | .hole => h
  | .left C' _ => framingLeft (ctxMono C' h)
  | .right _ C' => framingRight (ctxMono C' h)

/-- The weaker positive form `C₁[x ⊓ φ] ⊓ C₂[x] ⇒ C₂[x ⊓ φ]` (take `ψ := ⊤`). -/
def singletonAlt {C₁ C₂ : AppCtx Symbol} {n : EVarIndex} {φ : Pattern Symbol} :
    Γ ⊩ᵢ C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n) ⇒ C₂.fill (.evar n ⊓ φ) :=
  syllogism (andMonoR (ctxMono C₂ andTop))
    (syllogism (singletonStrong (C₁ := C₁) (C₂ := C₂) (n := n) (φ := φ) (ψ := ⊤ₘ))
      (ctxMono C₂ (andMonoR weakeningAnd)))

/-- Propagation of `⊥` through a context, `C[⊥] ⇒ ⊥`: the `C₂ := hole`
instance of `singletonAlt` gives `C'[x ⊓ ⊥] ⊓ x ⇒ x ⊓ ⊥` for the lifted
context `C'`; export `x`, generalize it with `existGen`, and discharge
`∃x. x` with `existence`. -/
def botProp (C : AppCtx Symbol) : Γ ⊩ᵢ C.fill ⊥ₘ ⇒ ⊥ₘ :=
  let C' := C.lift 0
  let h₁ : Γ ⊩ᵢ C'.fill (.evar 0 ⊓ ⊥ₘ) ⊓ .evar 0 ⇒ .evar 0 ⊓ ⊥ₘ :=
    singletonAlt (C₁ := C') (C₂ := .hole) (n := 0) (φ := ⊥ₘ)
  let h₂ : Γ ⊩ᵢ C'.fill ⊥ₘ ⊓ .evar 0 ⇒ ⊥ₘ :=
    syllogism (andMonoL (ctxMono C' botElim)) (syllogism h₁ weakeningAnd')
  let h₃ : Γ ⊩ᵢ .evar 0 ⇒ (C'.fill ⊥ₘ ⇒ ⊥ₘ) := exportation (syllogism permutationAnd h₂)
  let h₄ : Γ ⊩ᵢ ∃ₑ (.evar 0) ⇒ (C.fill ⊥ₘ ⇒ ⊥ₘ) :=
    existGen (by rw [evarLift_ctxBot_impl_bot]; exact h₃)
  mp h₄ existence

/-- **The classical SINGLETON rule** `~(C₁[x ⊓ φ] ⊓ C₂[x ⊓ ~φ])`, the primitive
of the published system (`IML.Crisp.Proof.singleton`), derived from the
positive rule: take `ψ := ~φ`, then `φ ⊓ ~φ ⇒ ⊥` inside `C₂` and propagate
`⊥` out. It has the signature the former constructor had, so `.singleton`
is used exactly as before. -/
def singleton {C₁ C₂ : AppCtx Symbol} {n : EVarIndex} {φ : Pattern Symbol} :
    Γ ⊩ᵢ ~(C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n ⊓ ~φ)) :=
  syllogism (singletonStrong (C₁ := C₁) (C₂ := C₂) (n := n) (φ := φ) (ψ := ~φ))
    (syllogism (ctxMono C₂ (syllogism weakeningAnd' negElim)) (botProp C₂))

end Proof

end IML
