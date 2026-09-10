import Mathlib.Data.Set.Lattice

namespace IML

-- ─────────────────────────────────────────────────────────────
-- De Bruijn index types (reuse the naming convention)
-- ─────────────────────────────────────────────────────────────

abbrev EVarIndex := Nat
abbrev SVarIndex := Nat

-- ─────────────────────────────────────────────────────────────
-- Pattern syntax for intuitionistic matching logic
-- All connectives that are NOT interderivable intuitionistically
-- are made primitive.
-- ─────────────────────────────────────────────────────────────

inductive Pattern (Symbol : Type) where
  | evar    : EVarIndex → Pattern Symbol
  | svar    : SVarIndex → Pattern Symbol
  | symbol  : Symbol → Pattern Symbol
  | app     : Pattern Symbol → Pattern Symbol → Pattern Symbol
  | bot     : Pattern Symbol
  | impl    : Pattern Symbol → Pattern Symbol → Pattern Symbol
  | conj    : Pattern Symbol → Pattern Symbol → Pattern Symbol
  | disj    : Pattern Symbol → Pattern Symbol → Pattern Symbol
  | exist   : Pattern Symbol → Pattern Symbol
  | forallP : Pattern Symbol → Pattern Symbol
  | mu      : Pattern Symbol → Pattern Symbol
  | nu      : Pattern Symbol → Pattern Symbol
  deriving Repr, Inhabited

namespace Pattern

variable {Symbol : Type}

-- ─── Notations ───────────────────────────────────────────────

scoped infixl:70 " ⬝ " => Pattern.app
scoped infixr:25 " ⇒ " => Pattern.impl
scoped infixl:35 " ⊓ " => Pattern.conj
scoped infixl:30 " ⊔ " => Pattern.disj
scoped notation "⊥ₘ" => Pattern.bot
scoped notation "∃ₑ" => Pattern.exist
scoped notation "∀ₑ" => Pattern.forallP
scoped notation "μ" => Pattern.mu
scoped notation "ν" => Pattern.nu

-- ─── Derived connectives ─────────────────────────────────────

def neg (φ : Pattern Symbol) : Pattern Symbol := φ ⇒ ⊥ₘ
def top : Pattern Symbol := neg ⊥ₘ
def iff (φ ψ : Pattern Symbol) : Pattern Symbol := (φ ⇒ ψ) ⊓ (ψ ⇒ φ)

scoped prefix:max "~" => Pattern.neg
scoped notation "⊤ₘ" => Pattern.top
scoped infixl:20 " ⟺ " => Pattern.iff

end Pattern

end IML
