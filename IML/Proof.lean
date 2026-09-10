import IML.Substitution

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
  -- Application (tentative — same as classical)
  | singleton {C₁ C₂ : AppCtx Symbol} {n : EVarIndex} {φ} :
      Proof Γ (~(C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n ⊓ ~φ)))
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

end IML
