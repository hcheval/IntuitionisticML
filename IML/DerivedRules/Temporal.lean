import IML.DerivedRules.Context
import IML.DerivedRules.Fixpoint

/-!
# Transition systems and temporal operators

With one symbol `next` ("one-path next" `•`) we define, as usual,

* `nx φ := next ⬝ φ`                        (`•φ`)
* `allnx φ := ~nx(~φ)`                      (`◦φ`, the dual box)
* `evt φ := μX. φ ⊔ •X`                     (`⋄φ`)
* `alw φ := νX. φ ⊓ ◦X`                     (`□φ`)
* `wevt φ := νX. φ ⊔ •X`                    (`⋄w φ`, weak eventually)
* `wf := μX. ◦X`                            (well-foundedness)

and check which of the standard temporal laws survive. Everything about `•`,
`⋄` and `⋄w` (the *existential* side) goes through unchanged. On the universal
side `◦`, `□` only the "half" that follows by monotonicity and coinduction
survives; the halves that need `◦(φ ⊓ ψ) ⇐ ◦φ ⊓ ◦ψ`, the Barcan direction of
`◦∀x.φ ⇐ ∀x.◦φ`, `¬⋄¬φ ⇒ □φ`, and `◦φ₁ ⊓ •φ₂ ⇒ •(φ₁ ⊓ φ₂)` all fail, because
`◦ := ~•~` is the *double-negation* box in the Heyting semantics.
-/

namespace IML

open Pattern

variable {Symbol : Type} (next : Symbol)

def nx (φ : Pattern Symbol) : Pattern Symbol := .symbol next ⬝ φ
def allnx (φ : Pattern Symbol) : Pattern Symbol := ~(nx next (~φ))
def evt (φ : Pattern Symbol) : Pattern Symbol := μ (svarLift φ ⊔ nx next (.svar 0))
def alw (φ : Pattern Symbol) : Pattern Symbol := ν (svarLift φ ⊓ allnx next (.svar 0))
def wevt (φ : Pattern Symbol) : Pattern Symbol := ν (svarLift φ ⊔ nx next (.svar 0))
def wf : Pattern Symbol := μ (allnx next (.svar 0))

def nxCtx : AppCtx Symbol := .right (.symbol next) .hole

-- ─────────────────────────────────────────────────────────────
-- Unfolding the bodies, positivity
-- ─────────────────────────────────────────────────────────────

theorem evt_body_subst (φ ψ : Pattern Symbol) :
    svarSubst 0 ψ (svarLift φ ⊔ nx next (.svar 0)) = (φ ⊔ nx next ψ) := by
  simp [svarSubst, svarSubst_svarLift, nx]

theorem alw_body_subst (φ ψ : Pattern Symbol) :
    svarSubst 0 ψ (svarLift φ ⊓ allnx next (.svar 0)) = (φ ⊓ allnx next ψ) := by
  simp [svarSubst, svarSubst_svarLift, nx, allnx, Pattern.neg]

theorem wf_body_subst (ψ : Pattern Symbol) :
    svarSubst 0 ψ (allnx next (.svar 0)) = allnx next ψ := by
  simp [svarSubst, nx, allnx, Pattern.neg]

theorem evt_body_pos (φ : Pattern Symbol) :
    SVarPositive (svarLift φ ⊔ nx next (.svar 0)) 0 :=
  .disj (svarLift_positive φ) (.app .symbol .svar)

theorem alw_body_pos (φ : Pattern Symbol) :
    SVarPositive (svarLift φ ⊓ allnx next (.svar 0)) 0 :=
  .conj (svarLift_positive φ) (.impl (.app .symbol (.impl .svar .bot)) .bot)

theorem wf_body_pos : SVarPositive (allnx next (.svar 0 : Pattern Symbol)) 0 :=
  .impl (.app .symbol (.impl .svar .bot)) .bot

variable {Γ : Set (Pattern Symbol)} {φ ψ : Pattern Symbol}

-- ─────────────────────────────────────────────────────────────
-- • : monotonicity, ⊥, ⊔ and ∃ propagation
-- ─────────────────────────────────────────────────────────────

def nxMono (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ nx next φ ⇒ nx next ψ := .framingRight h

def nxBot : Γ ⊩ᵢ nx next ⊥ₘ ⇒ ⊥ₘ := ctxBot (nxCtx next)

def nxBotIff : Γ ⊩ᵢ nx next ⊥ₘ ⟺ ⊥ₘ := iffIntro (nxBot next) botElim

def nxOr : Γ ⊩ᵢ nx next (φ ⊔ ψ) ⟺ nx next φ ⊔ nx next ψ := ctxPropagationOrIff (nxCtx next)

def nxExist : Γ ⊩ᵢ nx next (∃ₑ φ) ⟺ ∃ₑ (nx next φ) :=
  iffIntro (ctxPropagationExist (nxCtx next)) (ctxPropagationExistR (nxCtx next))

-- ─────────────────────────────────────────────────────────────
-- ◦ : monotonicity, ⊤, and the surviving halves of ⊓ and ∀
-- ─────────────────────────────────────────────────────────────

def allnxMono (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ allnx next φ ⇒ allnx next ψ :=
  contrapositive (nxMono next (contrapositive h))

def allnxTop : Γ ⊩ᵢ allnx next ⊤ₘ :=
  .syllogism (nxMono next (.mp reverseApp topIntro)) (nxBot next)

/-- (5→). The converse `◦φ ⊓ ◦ψ ⇒ ◦(φ ⊓ ψ)` is sound but needs
¬¬-propagation through `•`, which is not derivable. -/
def allnxAnd : Γ ⊩ᵢ allnx next (φ ⊓ ψ) ⇒ allnx next φ ⊓ allnx next ψ :=
  implAnd (allnxMono next andElimLeft) (allnxMono next andElimRight)

/-- (6, converse Barcan). The Barcan direction is not sound. -/
def allnxForall : Γ ⊩ᵢ allnx next (∀ₑ φ) ⇒ ∀ₑ (allnx next φ) :=
  boxConverseBarcan (nxCtx next)

-- ─────────────────────────────────────────────────────────────
-- ⋄ : unfolding, induction, monotonicity, idempotence, ⊔
-- ─────────────────────────────────────────────────────────────

def evtUnfold : Γ ⊩ᵢ φ ⊔ nx next (evt next φ) ⇒ evt next φ := by
  have h := Proof.preFixpoint (Γ := Γ) (evt_body_pos next φ)
  rwa [evt_body_subst] at h

def evtIntro : Γ ⊩ᵢ φ ⇒ evt next φ := .syllogism orIntroLeft (evtUnfold next)

def nxEvt : Γ ⊩ᵢ nx next (evt next φ) ⇒ evt next φ := .syllogism orIntroRight (evtUnfold next)

def evtInduction (h : Γ ⊩ᵢ φ ⊔ nx next ψ ⇒ ψ) : Γ ⊩ᵢ evt next φ ⇒ ψ :=
  .knasterTarski (by rw [evt_body_subst]; exact h)

def evtMono (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ evt next φ ⇒ evt next ψ :=
  evtInduction next (orElim (.syllogism h (evtIntro next)) (nxEvt next))

def evtBot : Γ ⊩ᵢ evt next ⊥ₘ ⇒ ⊥ₘ := evtInduction next (orElim implSelf (nxBot next))

def evtIdem : Γ ⊩ᵢ evt next (evt next φ) ⇒ evt next φ :=
  evtInduction next (orElim implSelf (nxEvt next))

def evtOr : Γ ⊩ᵢ evt next (φ ⊔ ψ) ⇒ evt next φ ⊔ evt next ψ :=
  evtInduction next
    (orElim (orMono (evtIntro next) (evtIntro next))
            (.syllogism (iffMpLeft (nxOr next)) (orMono (nxEvt next) (nxEvt next))))

def evtOrR : Γ ⊩ᵢ evt next φ ⊔ evt next ψ ⇒ evt next (φ ⊔ ψ) :=
  orElim (evtMono next orIntroLeft) (evtMono next orIntroRight)

-- ─────────────────────────────────────────────────────────────
-- □ : unfolding, coinduction, monotonicity, ⊓, idempotence, □φ ⇒ ~⋄~φ
-- ─────────────────────────────────────────────────────────────

def alwUnfold : Γ ⊩ᵢ alw next φ ⇒ φ ⊓ allnx next (alw next φ) := by
  have h := Proof.postFixpoint (Γ := Γ) (alw_body_pos next φ)
  rwa [alw_body_subst] at h

def alwElim : Γ ⊩ᵢ alw next φ ⇒ φ := .syllogism (alwUnfold next) andElimLeft

def alwNext : Γ ⊩ᵢ alw next φ ⇒ allnx next (alw next φ) :=
  .syllogism (alwUnfold next) andElimRight

def alwCoinduction (h : Γ ⊩ᵢ ψ ⇒ φ ⊓ allnx next ψ) : Γ ⊩ᵢ ψ ⇒ alw next φ :=
  .park (by rw [alw_body_subst]; exact h)

def alwMono (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ alw next φ ⇒ alw next ψ :=
  alwCoinduction next (implAnd (.syllogism (alwElim next) h) (alwNext next))

def alwTop : Γ ⊩ᵢ alw next ⊤ₘ :=
  .mp (alwCoinduction next (implAnd implSelf (extraPremise (allnxTop next)))) topIntro

/-- (15→). The converse needs (5←). -/
def alwAnd : Γ ⊩ᵢ alw next (φ ⊓ ψ) ⇒ alw next φ ⊓ alw next ψ :=
  implAnd (alwMono next andElimLeft) (alwMono next andElimRight)

def alwIdem : Γ ⊩ᵢ alw next φ ⇒ alw next (alw next φ) :=
  alwCoinduction next (implAnd implSelf (alwNext next))

/-- (17→): `□φ ⇒ ¬⋄¬φ`. The converse `¬⋄¬φ ⇒ □φ` needs DNE. -/
def alwToNotEvtNot : Γ ⊩ᵢ alw next φ ⇒ ~(evt next (~φ)) :=
  flip (evtInduction next (orElim (contrapositive (alwElim next)) (flip (alwNext next))))

-- ─────────────────────────────────────────────────────────────
-- ⋄w : unfolding, coinduction, and WF
-- ─────────────────────────────────────────────────────────────

def wevtUnfold : Γ ⊩ᵢ wevt next φ ⇒ φ ⊔ nx next (wevt next φ) := by
  have h := Proof.postFixpoint (Γ := Γ) (evt_body_pos next φ)
  rwa [evt_body_subst] at h

def wevtCoinduction (h : Γ ⊩ᵢ ψ ⇒ φ ⊔ nx next ψ) : Γ ⊩ᵢ ψ ⇒ wevt next φ :=
  .park (by rw [evt_body_subst]; exact h)

def wevtFold : Γ ⊩ᵢ φ ⊔ nx next (wevt next φ) ⇒ wevt next φ :=
  wevtCoinduction next (orMono implSelf (nxMono next (wevtUnfold next)))

def wevtIntro : Γ ⊩ᵢ φ ⇒ wevt next φ := .syllogism orIntroLeft (wevtFold next)

def nxWevt : Γ ⊩ᵢ nx next (wevt next φ) ⇒ wevt next φ :=
  .syllogism orIntroRight (wevtFold next)

def wevtMono (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ wevt next φ ⇒ wevt next ψ :=
  wevtCoinduction next (.syllogism (wevtUnfold next) (orMono h implSelf))

def evtToWevt : Γ ⊩ᵢ evt next φ ⇒ wevt next φ :=
  evtInduction next (wevtFold next)

def wfFold : Γ ⊩ᵢ allnx next (wf next) ⇒ wf next := by
  have h := Proof.preFixpoint (Γ := Γ) (wf_body_pos next)
  rwa [wf_body_subst] at h

-- ─────────────────────────────────────────────────────────────
-- Peano induction = (No Junk) + KNASTER-TARSKI
-- ─────────────────────────────────────────────────────────────

/-- With `⊤Nat := μD. zero ⊔ succ(D)`, which is `evt succ zero`, structural
induction over `zero`/`succ` is an instance of `evtInduction`:
from `zero ⇒ Ψ` and `succ(Ψ) ⇒ Ψ` infer `⊤Nat ⇒ Ψ`. Fully intuitionistic. -/
def peanoInduction (succ : Symbol) {zero Ψ : Pattern Symbol}
    (h₀ : Γ ⊩ᵢ zero ⇒ Ψ) (h₁ : Γ ⊩ᵢ nx succ Ψ ⇒ Ψ) : Γ ⊩ᵢ evt succ zero ⇒ Ψ :=
  evtInduction succ (orElim h₀ h₁)

end IML
