import IML.Proof

/-!
# Derived propositional rules of iML

The intuitionistic propositional fragment of `IML.Proof` is a Hilbert system
with rules (contraction, weakening, permutation, syllogism, exportation,
importation, expansion) rather than the classical axioms `p1`, `p2`, `p3`.
This file recovers the usual toolkit: `p1`, `p2` (as patterns), pairing,
the S-combinator `implMp`, disjunction elimination, distributivity, the
intuitionistically valid De Morgan laws, double-negation introduction, and
so on. Everything here is sorry-free.

What is deliberately absent is anything needing `p3`: double-negation
elimination `~~φ ⇒ φ`, `~(φ ⇒ ψ) ⇒ φ`, `~(φ ⊓ ψ) ⇒ ~φ ⊔ ~ψ`, and excluded
middle. These are unsound for the Heyting semantics (see
`IML.DerivedRules.TopFilterModel`), so no derivation exists.
-/

namespace IML

open Pattern

variable {Symbol : Type} {Γ : Set (Pattern Symbol)} {φ ψ χ φ₁ φ₂ ψ₁ ψ₂ : Pattern Symbol}

-- ─────────────────────────────────────────────────────────────
-- Identity, transitivity, projections
-- ─────────────────────────────────────────────────────────────

def implSelf : Γ ⊩ᵢ φ ⇒ φ := .syllogism .contractionAnd .weakeningAnd

def implTrans (h₁ : Γ ⊩ᵢ φ ⇒ ψ) (h₂ : Γ ⊩ᵢ ψ ⇒ χ) : Γ ⊩ᵢ φ ⇒ χ := .syllogism h₁ h₂

def andElimLeft : Γ ⊩ᵢ φ ⊓ ψ ⇒ φ := .weakeningAnd

def andElimRight : Γ ⊩ᵢ φ ⊓ ψ ⇒ ψ := .syllogism .permutationAnd .weakeningAnd

def andSwap : Γ ⊩ᵢ φ ⊓ ψ ⇒ ψ ⊓ φ := .permutationAnd

def orIntroLeft : Γ ⊩ᵢ φ ⇒ φ ⊔ ψ := .weakeningOr

def orIntroRight : Γ ⊩ᵢ ψ ⇒ φ ⊔ ψ := .syllogism .weakeningOr .permutationOr

def orPermute : Γ ⊩ᵢ φ ⊔ ψ ⇒ ψ ⊔ φ := .permutationOr

/-- Curried pairing `φ ⇒ ψ ⇒ φ ⊓ ψ`. -/
def curriedAndIntro : Γ ⊩ᵢ φ ⇒ ψ ⇒ φ ⊓ ψ := .exportation implSelf

/-- Internal modus ponens `(φ ⇒ ψ) ⊓ φ ⇒ ψ`. -/
def andMp : Γ ⊩ᵢ (φ ⇒ ψ) ⊓ φ ⇒ ψ := .importation implSelf

def curry (h : Γ ⊩ᵢ φ ⇒ ψ ⇒ χ) : Γ ⊩ᵢ φ ⊓ ψ ⇒ χ := .importation h

def uncurry (h : Γ ⊩ᵢ φ ⊓ ψ ⇒ χ) : Γ ⊩ᵢ φ ⇒ ψ ⇒ χ := .exportation h

-- ─────────────────────────────────────────────────────────────
-- The Hilbert axioms p1 and p2 are derivable (p3 is not)
-- ─────────────────────────────────────────────────────────────

/-- Axiom `p1` of the classical system. -/
def p1 : Γ ⊩ᵢ φ ⇒ ψ ⇒ φ := .exportation .weakeningAnd

def extraPremise (h : Γ ⊩ᵢ φ) : Γ ⊩ᵢ ψ ⇒ φ := .mp p1 h

-- ─────────────────────────────────────────────────────────────
-- Monotonicity of ⊓, pairing, S-combinator
-- ─────────────────────────────────────────────────────────────

def andMonoLeft (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ φ ⊓ χ ⇒ ψ ⊓ χ :=
  .importation (.syllogism h (.exportation implSelf))

def andMonoRight (h : Γ ⊩ᵢ ψ ⇒ χ) : Γ ⊩ᵢ φ ⊓ ψ ⇒ φ ⊓ χ :=
  .syllogism .permutationAnd (.syllogism (andMonoLeft h) .permutationAnd)

def andMono (h₁ : Γ ⊩ᵢ φ₁ ⇒ ψ₁) (h₂ : Γ ⊩ᵢ φ₂ ⇒ ψ₂) : Γ ⊩ᵢ φ₁ ⊓ φ₂ ⇒ ψ₁ ⊓ ψ₂ :=
  .syllogism (andMonoLeft h₁) (andMonoRight h₂)

/-- Pairing: `(φ ⇒ ψ) → (φ ⇒ χ) → (φ ⇒ ψ ⊓ χ)`. -/
def implAnd (h₁ : Γ ⊩ᵢ φ ⇒ ψ) (h₂ : Γ ⊩ᵢ φ ⇒ χ) : Γ ⊩ᵢ φ ⇒ ψ ⊓ χ :=
  .syllogism .contractionAnd (andMono h₁ h₂)

def andIntro (h₁ : Γ ⊩ᵢ φ) (h₂ : Γ ⊩ᵢ ψ) : Γ ⊩ᵢ φ ⊓ ψ := .mp (.mp curriedAndIntro h₁) h₂

/-- The S-combinator as a rule: `(φ ⇒ ψ ⇒ χ) → (φ ⇒ ψ) → (φ ⇒ χ)`. -/
def implMp (h₁ : Γ ⊩ᵢ φ ⇒ ψ ⇒ χ) (h₂ : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ φ ⇒ χ :=
  .syllogism (implAnd implSelf h₂) (.importation h₁)

def mpExtraHyp (h₁ : Γ ⊩ᵢ φ ⇒ ψ ⇒ χ) (h₂ : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ φ ⇒ χ := implMp h₁ h₂

/-- Axiom `p2` of the classical system, as a pattern. -/
def p2 : Γ ⊩ᵢ (φ ⇒ ψ ⇒ χ) ⇒ (φ ⇒ ψ) ⇒ φ ⇒ χ :=
  .exportation (.exportation
    (.syllogism
      (implAnd (.syllogism (andMonoLeft andElimLeft) andMp)
               (.syllogism (andMonoLeft andElimRight) andMp))
      andMp))

-- ─────────────────────────────────────────────────────────────
-- Pre/post-composition, flip
-- ─────────────────────────────────────────────────────────────

/-- Post-composition: `(ψ ⇒ χ) → ((φ ⇒ ψ) ⇒ (φ ⇒ χ))`. -/
def implLift (h : Γ ⊩ᵢ ψ ⇒ χ) : Γ ⊩ᵢ (φ ⇒ ψ) ⇒ (φ ⇒ χ) :=
  .exportation (.syllogism andMp h)

/-- Pre-composition: `(φ ⇒ ψ) → ((ψ ⇒ χ) ⇒ (φ ⇒ χ))`. -/
def implPreComp (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ (ψ ⇒ χ) ⇒ (φ ⇒ χ) :=
  .exportation (.syllogism (andMonoRight h) andMp)

def flip (h : Γ ⊩ᵢ φ ⇒ ψ ⇒ χ) : Γ ⊩ᵢ ψ ⇒ φ ⇒ χ :=
  .exportation (.syllogism .permutationAnd (.importation h))

/-- Reverse application `φ ⇒ (φ ⇒ ψ) ⇒ ψ`. -/
def reverseApp : Γ ⊩ᵢ φ ⇒ (φ ⇒ ψ) ⇒ ψ := flip implSelf

-- ─────────────────────────────────────────────────────────────
-- Associativity of ⊓
-- ─────────────────────────────────────────────────────────────

def andAssoc : Γ ⊩ᵢ (φ ⊓ ψ) ⊓ χ ⇒ φ ⊓ (ψ ⊓ χ) :=
  implAnd (.syllogism andElimLeft andElimLeft)
          (andMono andElimRight implSelf)

def andAssoc' : Γ ⊩ᵢ φ ⊓ (ψ ⊓ χ) ⇒ (φ ⊓ ψ) ⊓ χ :=
  implAnd (andMono implSelf andElimLeft)
          (.syllogism andElimRight andElimRight)

-- ─────────────────────────────────────────────────────────────
-- Disjunction
-- ─────────────────────────────────────────────────────────────

/-- Disjunction elimination as a rule. -/
def orElim (h₁ : Γ ⊩ᵢ φ ⇒ χ) (h₂ : Γ ⊩ᵢ ψ ⇒ χ) : Γ ⊩ᵢ φ ⊔ ψ ⇒ χ :=
  .syllogism .permutationOr
    (.syllogism (.expansion h₁)
      (.syllogism .permutationOr
        (.syllogism (.expansion h₂) .contractionOr)))

def orMono (h₁ : Γ ⊩ᵢ φ₁ ⇒ ψ₁) (h₂ : Γ ⊩ᵢ φ₂ ⇒ ψ₂) : Γ ⊩ᵢ φ₁ ⊔ φ₂ ⇒ ψ₁ ⊔ ψ₂ :=
  orElim (.syllogism h₁ orIntroLeft) (.syllogism h₂ orIntroRight)

def orExpansion (h : Γ ⊩ᵢ φ ⇒ χ) : Γ ⊩ᵢ ψ ⊔ φ ⇒ ψ ⊔ χ := .expansion h

/-- Distributivity `φ ⊓ (ψ ⊔ χ) ⇒ (φ ⊓ ψ) ⊔ (φ ⊓ χ)`. -/
def andOrDistrib : Γ ⊩ᵢ φ ⊓ (ψ ⊔ χ) ⇒ (φ ⊓ ψ) ⊔ (φ ⊓ χ) :=
  .importation (flip (orElim (flip (.exportation orIntroLeft))
                             (flip (.exportation orIntroRight))))

def andOrDistrib' : Γ ⊩ᵢ (φ ⊓ ψ) ⊔ (φ ⊓ χ) ⇒ φ ⊓ (ψ ⊔ χ) :=
  orElim (andMonoRight orIntroLeft) (andMonoRight orIntroRight)

-- ─────────────────────────────────────────────────────────────
-- ⊤ and ⊥
-- ─────────────────────────────────────────────────────────────

def topIntro : Γ ⊩ᵢ ⊤ₘ := implSelf

def botElim : Γ ⊩ᵢ ⊥ₘ ⇒ φ := .botElim

def implTop : Γ ⊩ᵢ φ ⇒ ⊤ₘ := extraPremise topIntro

-- ─────────────────────────────────────────────────────────────
-- Negation: the intuitionistically valid part
-- ─────────────────────────────────────────────────────────────

def modusTollens (h₁ : Γ ⊩ᵢ φ ⇒ ψ) (h₂ : Γ ⊩ᵢ ~ψ) : Γ ⊩ᵢ ~φ := .syllogism h₁ h₂

def contrapositive (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ ~ψ ⇒ ~φ := implPreComp h

/-- Double-negation introduction `φ ⇒ ~~φ`. -/
def dni : Γ ⊩ᵢ φ ⇒ ~~φ := reverseApp

/-- `~~~φ ⇒ ~φ`; together with `dni` this makes `~~~φ ⟺ ~φ`. -/
def tripleNegElim : Γ ⊩ᵢ ~(~(~φ)) ⇒ ~φ := contrapositive dni

/-- `~(φ ⊔ ψ) ⇒ ~φ ⊓ ~ψ`. -/
def notOr : Γ ⊩ᵢ ~(φ ⊔ ψ) ⇒ ~φ ⊓ ~ψ :=
  implAnd (contrapositive orIntroLeft) (contrapositive orIntroRight)

/-- `~φ ⊓ ~ψ ⇒ ~(φ ⊔ ψ)`. -/
def notOrIntro : Γ ⊩ᵢ ~φ ⊓ ~ψ ⇒ ~(φ ⊔ ψ) :=
  .exportation (.syllogism andOrDistrib
    (orElim (.syllogism (andMonoLeft andElimLeft) andMp)
            (.syllogism (andMonoLeft andElimRight) andMp)))

/-- `~φ ⊔ ~ψ ⇒ ~(φ ⊓ ψ)`.  The converse needs excluded middle. -/
def notAndOfNotOr : Γ ⊩ᵢ ~φ ⊔ ~ψ ⇒ ~(φ ⊓ ψ) :=
  orElim (contrapositive andElimLeft) (contrapositive andElimRight)

/-- `φ ⊓ ~ψ ⇒ ~(φ ⇒ ψ)`.  The converses `~(φ ⇒ ψ) ⇒ φ`, `~(φ ⇒ ψ) ⇒ ~ψ`:
only the second is intuitionistic (`notImplRight`). -/
def andToNotImpl : Γ ⊩ᵢ φ ⊓ ~ψ ⇒ ~(φ ⇒ ψ) :=
  -- (φ ⊓ ~ψ) ⊓ (φ ⇒ ψ) ⇒ ((φ ⇒ ψ) ⊓ φ) ⊓ ~ψ ⇒ ψ ⊓ ~ψ ⇒ ⊥
  .exportation (.syllogism .permutationAnd (.syllogism andAssoc'
    (.syllogism (andMonoLeft andMp) (.syllogism .permutationAnd andMp))))

def notImplRight : Γ ⊩ᵢ ~(φ ⇒ ψ) ⇒ ~ψ := contrapositive p1

/-- Double negation of excluded middle, `~~(φ ⊔ ~φ)`. -/
def nnExcludedMiddle : Γ ⊩ᵢ ~~(φ ⊔ ~φ) :=
  .syllogism notOr (.syllogism .permutationAnd andMp)

/-- `~~(φ ⇒ ψ) ⇒ ~~φ ⇒ ~~ψ` (double negation is a "modality"). -/
def nnImpl : Γ ⊩ᵢ ~~(φ ⇒ ψ) ⇒ ~~φ ⇒ ~~ψ :=
  -- ~ψ ⊓ (φ ⇒ ψ) ⇒ ~φ
  let k' : Γ ⊩ᵢ ~ψ ⊓ (φ ⇒ ψ) ⇒ ~φ :=
    .exportation (.syllogism andAssoc (.syllogism (andMonoRight andMp) andMp))
  -- ~~φ ⊓ ~ψ ⇒ ~(φ ⇒ ψ)
  let k : Γ ⊩ᵢ ~~φ ⊓ ~ψ ⇒ ~(φ ⇒ ψ) :=
    .exportation (.syllogism andAssoc (.syllogism (andMonoRight k') andMp))
  -- (~~(φ ⇒ ψ) ⊓ ~~φ) ⊓ ~ψ ⇒ ⊥
  .exportation (.exportation
    (.syllogism andAssoc (.syllogism (andMonoRight k) andMp)))

/-- `~~φ ⊓ ~~ψ ⇒ ~~(φ ⊓ ψ)`. -/
def nnAnd : Γ ⊩ᵢ ~~φ ⊓ ~~ψ ⇒ ~~(φ ⊓ ψ) :=
  -- ~(φ ⊓ ψ) ⊓ φ ⇒ ~ψ
  let j' : Γ ⊩ᵢ ~(φ ⊓ ψ) ⊓ φ ⇒ ~ψ :=
    .exportation (.syllogism andAssoc andMp)
  -- ~~ψ ⊓ ~(φ ⊓ ψ) ⇒ ~φ
  let j : Γ ⊩ᵢ ~~ψ ⊓ ~(φ ⊓ ψ) ⇒ ~φ :=
    .exportation (.syllogism andAssoc (.syllogism (andMonoRight j') andMp))
  -- (~~φ ⊓ ~~ψ) ⊓ ~(φ ⊓ ψ) ⇒ ⊥
  .exportation (.syllogism andAssoc (.syllogism (andMonoRight j) andMp))

/-- Contraposition of the classically-only `~~φ ⇒ φ`: the intuitionistic
implication runs from `φ` to `~~φ`, never back. Recorded here as a
documentation lemma: `~φ ⇒ ~~~φ` holds by `dni`. -/
def negDni : Γ ⊩ᵢ ~φ ⇒ ~(~(~φ)) := dni

-- ─────────────────────────────────────────────────────────────
-- Equivalences
-- ─────────────────────────────────────────────────────────────

def iffIntro (h₁ : Γ ⊩ᵢ φ ⇒ ψ) (h₂ : Γ ⊩ᵢ ψ ⇒ φ) : Γ ⊩ᵢ φ ⟺ ψ := andIntro h₁ h₂

def iffRefl : Γ ⊩ᵢ φ ⟺ φ := iffIntro implSelf implSelf

def iffSymm (h : Γ ⊩ᵢ φ ⟺ ψ) : Γ ⊩ᵢ ψ ⟺ φ := .mp andSwap h

def iffMpLeft (h : Γ ⊩ᵢ φ ⟺ ψ) : Γ ⊩ᵢ φ ⇒ ψ := .mp andElimLeft h

def iffMpRight (h : Γ ⊩ᵢ φ ⟺ ψ) : Γ ⊩ᵢ ψ ⇒ φ := .mp andElimRight h

def iffTrans (h₁ : Γ ⊩ᵢ φ ⟺ ψ) (h₂ : Γ ⊩ᵢ ψ ⟺ χ) : Γ ⊩ᵢ φ ⟺ χ :=
  iffIntro (.syllogism (iffMpLeft h₁) (iffMpLeft h₂))
           (.syllogism (iffMpRight h₂) (iffMpRight h₁))

end IML
