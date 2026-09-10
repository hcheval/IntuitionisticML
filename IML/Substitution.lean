import IML.Pattern

namespace IML

open Pattern

variable {Symbol : Type}

-- ─────────────────────────────────────────────────────────────
-- Lifting (de Bruijn index shifting)
-- ─────────────────────────────────────────────────────────────

def evarLiftFrom (cutoff : Nat) : Pattern Symbol → Pattern Symbol
  | .evar i   => .evar (if i ≥ cutoff then i + 1 else i)
  | .svar i   => .svar i
  | .symbol s => .symbol s
  | .app φ ψ  => .app (evarLiftFrom cutoff φ) (evarLiftFrom cutoff ψ)
  | .bot      => .bot
  | .impl φ ψ => .impl (evarLiftFrom cutoff φ) (evarLiftFrom cutoff ψ)
  | .conj φ ψ => .conj (evarLiftFrom cutoff φ) (evarLiftFrom cutoff ψ)
  | .disj φ ψ => .disj (evarLiftFrom cutoff φ) (evarLiftFrom cutoff ψ)
  | .exist φ  => .exist (evarLiftFrom (cutoff + 1) φ)
  | .forallP φ => .forallP (evarLiftFrom (cutoff + 1) φ)
  | .mu φ     => .mu (evarLiftFrom cutoff φ)
  | .nu φ     => .nu (evarLiftFrom cutoff φ)

def evarLift (φ : Pattern Symbol) : Pattern Symbol := evarLiftFrom 0 φ

def svarLiftFrom (cutoff : Nat) : Pattern Symbol → Pattern Symbol
  | .evar i   => .evar i
  | .svar i   => .svar (if i ≥ cutoff then i + 1 else i)
  | .symbol s => .symbol s
  | .app φ ψ  => .app (svarLiftFrom cutoff φ) (svarLiftFrom cutoff ψ)
  | .bot      => .bot
  | .impl φ ψ => .impl (svarLiftFrom cutoff φ) (svarLiftFrom cutoff ψ)
  | .conj φ ψ => .conj (svarLiftFrom cutoff φ) (svarLiftFrom cutoff ψ)
  | .disj φ ψ => .disj (svarLiftFrom cutoff φ) (svarLiftFrom cutoff ψ)
  | .exist φ  => .exist (svarLiftFrom cutoff φ)
  | .forallP φ => .forallP (svarLiftFrom cutoff φ)
  | .mu φ     => .mu (svarLiftFrom (cutoff + 1) φ)
  | .nu φ     => .nu (svarLiftFrom (cutoff + 1) φ)

def svarLift (φ : Pattern Symbol) : Pattern Symbol := svarLiftFrom 0 φ

-- ─────────────────────────────────────────────────────────────
-- Substitution
-- ─────────────────────────────────────────────────────────────

def evarSubst (n : Nat) (ψ : Pattern Symbol) : Pattern Symbol → Pattern Symbol
  | .evar i   => if i == n then ψ else if i > n then .evar (i - 1) else .evar i
  | .svar i   => .svar i
  | .symbol s => .symbol s
  | .app φ₁ φ₂ => .app (evarSubst n ψ φ₁) (evarSubst n ψ φ₂)
  | .bot      => .bot
  | .impl φ₁ φ₂ => .impl (evarSubst n ψ φ₁) (evarSubst n ψ φ₂)
  | .conj φ₁ φ₂ => .conj (evarSubst n ψ φ₁) (evarSubst n ψ φ₂)
  | .disj φ₁ φ₂ => .disj (evarSubst n ψ φ₁) (evarSubst n ψ φ₂)
  | .exist φ  => .exist (evarSubst (n + 1) (evarLift ψ) φ)
  | .forallP φ => .forallP (evarSubst (n + 1) (evarLift ψ) φ)
  | .mu φ     => .mu (evarSubst n ψ φ)
  | .nu φ     => .nu (evarSubst n ψ φ)

def svarSubst (n : Nat) (ψ : Pattern Symbol) : Pattern Symbol → Pattern Symbol
  | .evar i   => .evar i
  | .svar i   => if i == n then ψ else if i > n then .svar (i - 1) else .svar i
  | .symbol s => .symbol s
  | .app φ₁ φ₂ => .app (svarSubst n ψ φ₁) (svarSubst n ψ φ₂)
  | .bot      => .bot
  | .impl φ₁ φ₂ => .impl (svarSubst n ψ φ₁) (svarSubst n ψ φ₂)
  | .conj φ₁ φ₂ => .conj (svarSubst n ψ φ₁) (svarSubst n ψ φ₂)
  | .disj φ₁ φ₂ => .disj (svarSubst n ψ φ₁) (svarSubst n ψ φ₂)
  | .exist φ  => .exist (svarSubst n (evarLift ψ) φ)
  | .forallP φ => .forallP (svarSubst n (evarLift ψ) φ)
  | .mu φ     => .mu (svarSubst (n + 1) (svarLift ψ) φ)
  | .nu φ     => .nu (svarSubst (n + 1) (svarLift ψ) φ)

scoped notation:max φ "[" n " ₑ↦ " ψ "]" => evarSubst n ψ φ
scoped notation:max φ "[" n " ₛ↦ " ψ "]" => svarSubst n ψ φ

end IML
