import IML.DerivedRules.FOL

/-!
# Application contexts: propagation, framing, and the dual box

This file ports Chapter 3 of Chen's thesis (Propositions 3.2–3.4,
Lemma 3.4, Theorem 3.2) to iML.

The headline is `ctxBot : C[⊥] ⇒ ⊥`. iML has no PROPAGATION⊥ rule, but the
classical derivation (credited to Mircea Sebe in the thesis) only uses
`⊥ ⇒ ·`, framing, pairing and SINGLETON, all of which are intuitionistic, so
⊥-propagation is derivable after all.

What is *not* derivable is the ¬¬-propagation `C[~~φ] ⇒ ~~C[φ]`; see
`IML.DerivedRules.TopFilterModel` for the countermodel. This is the reason
the modal (K) rule for the dual box `~C[~·]` (Theorem 3.2(1)) does not go
through; only (N) and the converse Barcan formula survive.
-/

namespace IML

open Pattern

variable {Symbol : Type} {Γ : Set (Pattern Symbol)} {φ ψ χ : Pattern Symbol}

-- ─────────────────────────────────────────────────────────────
-- Framing through a context (Proposition 3.2)
-- ─────────────────────────────────────────────────────────────

def ctxFraming (C : AppCtx Symbol) (h : Γ ⊩ᵢ φ ⇒ ψ) :
    Γ ⊩ᵢ C.fill φ ⇒ C.fill ψ :=
  match C with
  | .hole => h
  | .left C' _ => .framingLeft (ctxFraming C' h)
  | .right _ C' => .framingRight (ctxFraming C' h)

def ctxFramingEquiv (C : AppCtx Symbol) (h : Γ ⊩ᵢ φ ⟺ ψ) :
    Γ ⊩ᵢ C.fill φ ⟺ C.fill ψ :=
  iffIntro (ctxFraming C (iffMpLeft h)) (ctxFraming C (iffMpRight h))

-- ─────────────────────────────────────────────────────────────
-- Propagation of ⊥ (Proposition 3.3(1)) — via SINGLETON
-- ─────────────────────────────────────────────────────────────

/-- `C[⊥] ⇒ ⊥`.  Derivation: `C[⊥] ⇒ C[x ⊓ ⊥] ⊓ C[x ⊓ ~⊥]` by framing
`⊥ ⇒ ·` twice, and SINGLETON refutes the right-hand side. -/
def ctxBot (C : AppCtx Symbol) : Γ ⊩ᵢ C.fill ⊥ₘ ⇒ ⊥ₘ :=
  .syllogism
    (implAnd (ctxFraming C (botElim (φ := .evar 0 ⊓ ⊥ₘ)))
             (ctxFraming C (botElim (φ := .evar 0 ⊓ ~⊥ₘ))))
    (.singleton (C₁ := C) (C₂ := C) (n := 0) (φ := ⊥ₘ))

def ctxBotR (C : AppCtx Symbol) : Γ ⊩ᵢ ⊥ₘ ⇒ C.fill ⊥ₘ := botElim

def ctxBotIff (C : AppCtx Symbol) : Γ ⊩ᵢ C.fill ⊥ₘ ⟺ ⊥ₘ :=
  iffIntro (ctxBot C) (ctxBotR C)

-- ─────────────────────────────────────────────────────────────
-- Propagation of ⊔ (Proposition 3.3(2))
-- ─────────────────────────────────────────────────────────────

def ctxPropagationOr (C : AppCtx Symbol) :
    Γ ⊩ᵢ C.fill (φ ⊔ ψ) ⇒ C.fill φ ⊔ C.fill ψ :=
  match C with
  | .hole => implSelf
  | .left C' _ => .syllogism (.framingLeft (ctxPropagationOr C')) .propagationOrLeft
  | .right _ C' => .syllogism (.framingRight (ctxPropagationOr C')) .propagationOrRight

def ctxPropagationOrR (C : AppCtx Symbol) :
    Γ ⊩ᵢ C.fill φ ⊔ C.fill ψ ⇒ C.fill (φ ⊔ ψ) :=
  orElim (ctxFraming C orIntroLeft) (ctxFraming C orIntroRight)

def ctxPropagationOrIff (C : AppCtx Symbol) :
    Γ ⊩ᵢ C.fill (φ ⊔ ψ) ⟺ C.fill φ ⊔ C.fill ψ :=
  iffIntro (ctxPropagationOr C) (ctxPropagationOrR C)

/-- `C[φ ⊓ ψ] ⇒ C[φ] ⊓ C[ψ]` (the converse is false already classically). -/
def ctxAnd (C : AppCtx Symbol) : Γ ⊩ᵢ C.fill (φ ⊓ ψ) ⇒ C.fill φ ⊓ C.fill ψ :=
  implAnd (ctxFraming C andElimLeft) (ctxFraming C andElimRight)

-- ─────────────────────────────────────────────────────────────
-- Lifting contexts and propagation of ∃ (Proposition 3.3(3))
-- ─────────────────────────────────────────────────────────────

def AppCtx.liftEVar : AppCtx Symbol → AppCtx Symbol
  | .hole      => .hole
  | .left C ψ  => .left (liftEVar C) (evarLift ψ)
  | .right ψ C => .right (evarLift ψ) (liftEVar C)

theorem evarLift_fill (C : AppCtx Symbol) (φ : Pattern Symbol) :
    evarLift (C.fill φ) = C.liftEVar.fill (evarLift φ) := by
  induction C with
  | hole => rfl
  | left C' ψ ih =>
    simp only [AppCtx.fill, AppCtx.liftEVar, evarLift, evarLiftFrom] at *
    rw [ih]
  | right ψ C' ih =>
    simp only [AppCtx.fill, AppCtx.liftEVar, evarLift, evarLiftFrom] at *
    rw [ih]

def ctxPropagationExist (C : AppCtx Symbol) :
    Γ ⊩ᵢ C.fill (∃ₑ φ) ⇒ ∃ₑ (C.liftEVar.fill φ) :=
  match C with
  | .hole => implSelf
  | .left C' _ => .syllogism (.framingLeft (ctxPropagationExist C')) .propagationExistLeft
  | .right _ C' => .syllogism (.framingRight (ctxPropagationExist C')) .propagationExistRight

def ctxPropagationExistR (C : AppCtx Symbol) :
    Γ ⊩ᵢ ∃ₑ (C.liftEVar.fill φ) ⇒ C.fill (∃ₑ φ) :=
  .existGen (φ₂ := C.fill (∃ₑ φ)) (by
    rw [evarLift_fill]
    exact ctxFraming _ existIntroLift)

-- ─────────────────────────────────────────────────────────────
-- Lemma 3.4: from `φ` infer `~C[~φ]`; the (N) rule of the dual box
-- ─────────────────────────────────────────────────────────────

/-- The dual box `□_C φ := ~C[~φ]` (Theorem 3.2 of the thesis defines
`σᵈ(φ) := ¬σ(¬φ)`). -/
def AppCtx.box (C : AppCtx Symbol) (φ : Pattern Symbol) : Pattern Symbol :=
  ~(C.fill (~φ))

def doubleNegCtx (C : AppCtx Symbol) (h : Γ ⊩ᵢ φ) : Γ ⊩ᵢ ~(C.fill (~φ)) :=
  .syllogism (ctxFraming C (.mp dni h)) (ctxBot C)

/-- (N): from `φ` infer `□_C φ`. -/
def boxNec (C : AppCtx Symbol) (h : Γ ⊩ᵢ φ) : Γ ⊩ᵢ C.box φ := doubleNegCtx C h

/-- Monotonicity of the dual box. -/
def boxMono (C : AppCtx Symbol) (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ C.box φ ⇒ C.box ψ :=
  contrapositive (ctxFraming C (contrapositive h))

/-- `□_C (φ ⊓ ψ) ⇒ □_C φ ⊓ □_C ψ`.  The converse would need
¬¬-propagation through `C` and is not derivable. -/
def boxAnd (C : AppCtx Symbol) : Γ ⊩ᵢ C.box (φ ⊓ ψ) ⇒ C.box φ ⊓ C.box ψ :=
  implAnd (boxMono C andElimLeft) (boxMono C andElimRight)

/-- `□_C ⊤`. -/
def boxTop (C : AppCtx Symbol) : Γ ⊩ᵢ C.box ⊤ₘ := boxNec C topIntro

/-- Converse Barcan: `□_C (∀x.φ) ⇒ ∀x. □_{C↑} φ`.  The Barcan formula
itself (the other direction) is not sound for the Heyting semantics: it
is a double-negation shift. -/
def boxConverseBarcan (C : AppCtx Symbol) :
    Γ ⊩ᵢ C.box (∀ₑ φ) ⇒ ∀ₑ (C.liftEVar.box φ) :=
  .forallGen (φ₁ := C.box (∀ₑ φ)) (by
    show Γ ⊩ᵢ ~(evarLift (C.fill (~(∀ₑ φ)))) ⇒ ~(C.liftEVar.fill (~φ))
    rw [evarLift_fill]
    exact contrapositive (ctxFraming _ (contrapositive forallElimLift)))

/-- The "diamond" half of (K): `C[φ ⇒ ψ] ⊓ □_C φ ⇒ ~~C[ψ]`?  Not derived.
What *is* derivable is the weak form `C[φ] ⊓ □_C ~φ ⇒ ⊥`. -/
def ctxBoxContra (C : AppCtx Symbol) : Γ ⊩ᵢ C.fill φ ⊓ C.box (~φ) ⇒ ⊥ₘ :=
  .syllogism (andMonoLeft (ctxFraming C dni)) (.syllogism .permutationAnd andMp)

end IML
