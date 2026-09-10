import IML.Proof
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.FixedPoints

/-!
# Heyting algebra semantics for iAML (correct version)

Patterns are interpreted as `Carrier → L` (L-valued predicates),
NOT as global elements of L. This generalizes `Set M = M → Prop`
by replacing `Prop` with a Frame L.

Application: `app(A, B)(m) = ⨆ a b, A(a) ⊓ B(b) ⊓ f(a,b,m)`
- NOT contractive: app(A,B) is not ≤ A
- Singleton has real content (requires atomic evar predicates)
- Definedness is non-trivial
-/

namespace IML

-- ─────────────────────────────────────────────────────────────
-- Model
-- ─────────────────────────────────────────────────────────────

structure HModel (Symbol : Type) (L : Type*) [Order.Frame L] where
  Carrier : Type
  decEq : DecidableEq Carrier
  appInterp : Carrier → Carrier → Carrier → L
  symInterp : Symbol → Carrier → L

-- ─────────────────────────────────────────────────────────────
-- Valuation
-- ─────────────────────────────────────────────────────────────

structure HValuation {Symbol : Type} {L : Type*} [Order.Frame L]
    (M : HModel Symbol L) where
  evar : EVarIndex → M.Carrier
  svar : SVarIndex → M.Carrier → L

namespace HValuation
variable {Symbol : Type} {L : Type*} [Order.Frame L] {M : HModel Symbol L}

def pushEVar (ρ : HValuation M) (a : M.Carrier) : HValuation M where
  evar i := match i with | 0 => a | n + 1 => ρ.evar n
  svar := ρ.svar

def pushSVar (ρ : HValuation M) (S : M.Carrier → L) : HValuation M where
  evar := ρ.evar
  svar i := match i with | 0 => S | n + 1 => ρ.svar n

end HValuation

-- ─────────────────────────────────────────────────────────────
-- Interpretation: Pattern → Carrier → L
-- ─────────────────────────────────────────────────────────────

variable {Symbol : Type} {L : Type*} [Order.Frame L]

open Pattern in
def hinterp (M : HModel Symbol L) (ρ : HValuation M) :
    Pattern Symbol → M.Carrier → L
  | .evar i, m    => @ite _ (m = ρ.evar i) (M.decEq m (ρ.evar i)) ⊤ ⊥
  | .svar i, m    => ρ.svar i m
  | .symbol s, m  => M.symInterp s m
  | .app φ ψ, m   =>
    ⨆ a, ⨆ b, hinterp M ρ φ a ⊓ hinterp M ρ ψ b ⊓ M.appInterp a b m
  | .bot, _        => ⊥
  | .impl φ ψ, m  => hinterp M ρ φ m ⇨ hinterp M ρ ψ m
  | .conj φ ψ, m  => hinterp M ρ φ m ⊓ hinterp M ρ ψ m
  | .disj φ ψ, m  => hinterp M ρ φ m ⊔ hinterp M ρ ψ m
  | .exist φ, m   => ⨆ a : M.Carrier, hinterp M (ρ.pushEVar a) φ m
  | .forallP φ, m => ⨅ a : M.Carrier, hinterp M (ρ.pushEVar a) φ m
  | .mu φ, m      =>
    sInf { x | ∃ S : M.Carrier → L,
      (∀ n, hinterp M (ρ.pushSVar S) φ n ≤ S n) ∧ x = S m }
  | .nu φ, m      =>
    sSup { x | ∃ S : M.Carrier → L,
      (∀ n, S n ≤ hinterp M (ρ.pushSVar S) φ n) ∧ x = S m }

-- ─────────────────────────────────────────────────────────────
-- Simp lemmas for hinterp (one layer at a time)
-- ─────────────────────────────────────────────────────────────

section hinterpSimp
variable {M : HModel Symbol L} {ρ : HValuation M}

open Pattern in
@[simp] theorem hinterp_evar (i : EVarIndex) (m : M.Carrier) :
    hinterp M ρ (.evar i) m = @ite _ (m = ρ.evar i) (M.decEq m (ρ.evar i)) ⊤ ⊥ := rfl

open Pattern in
@[simp] theorem hinterp_svar (i : SVarIndex) (m : M.Carrier) :
    hinterp M ρ (.svar i) m = ρ.svar i m := rfl

open Pattern in
@[simp] theorem hinterp_symbol (s : Symbol) (m : M.Carrier) :
    hinterp M ρ (.symbol s) m = M.symInterp s m := rfl

open Pattern in
@[simp] theorem hinterp_app (φ ψ : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (φ ⬝ ψ) m =
    ⨆ a, ⨆ b, hinterp M ρ φ a ⊓ hinterp M ρ ψ b ⊓ M.appInterp a b m := rfl

open Pattern in
@[simp] theorem hinterp_bot (m : M.Carrier) :
    hinterp M ρ (⊥ₘ : Pattern Symbol) m = ⊥ := rfl

open Pattern in
@[simp] theorem hinterp_impl (φ ψ : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (φ ⇒ ψ) m = hinterp M ρ φ m ⇨ hinterp M ρ ψ m := rfl

open Pattern in
@[simp] theorem hinterp_conj (φ ψ : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (φ ⊓ ψ) m = hinterp M ρ φ m ⊓ hinterp M ρ ψ m := rfl

open Pattern in
@[simp] theorem hinterp_disj (φ ψ : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (φ ⊔ ψ) m = hinterp M ρ φ m ⊔ hinterp M ρ ψ m := rfl

open Pattern in
@[simp] theorem hinterp_exist (φ : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (∃ₑ φ) m = ⨆ a : M.Carrier, hinterp M (ρ.pushEVar a) φ m := rfl

open Pattern in
@[simp] theorem hinterp_forall (φ : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (∀ₑ φ) m = ⨅ a : M.Carrier, hinterp M (ρ.pushEVar a) φ m := rfl

end hinterpSimp

-- Validity: ⟦φ⟧(m) = ⊤ for all m and ρ
def HValid (M : HModel Symbol L) (φ : Pattern Symbol) : Prop :=
  ∀ (ρ : HValuation M) (m : M.Carrier), hinterp M ρ φ m = ⊤

end IML
