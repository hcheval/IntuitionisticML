import IML.DerivedRules.Propositional

/-!
# Derived first-order rules of iML

Both quantifiers are primitive in iML, so the classical detour
`∀ = ¬∃¬` disappears. All the usual quantifier laws that do not depend on
classical logic are derived here. The ones that do depend on it are listed
at the end of the file as documentation.

The first section proves the substitution–lifting cancellation lemmas
(`evarSubst_evarLift`, `evarSubst_evarLiftFrom_succ`) for the
12-constructor syntax; they are the de Bruijn form of "`x` not free in `φ`".
-/

namespace IML

open Pattern

variable {Symbol : Type}

-- ─────────────────────────────────────────────────────────────
-- Substitution–lifting cancellation
-- ─────────────────────────────────────────────────────────────

theorem evarSubst_evarLiftFrom (φ : Pattern Symbol) (n : Nat) (ψ : Pattern Symbol) :
    evarSubst n ψ (evarLiftFrom n φ) = φ := by
  induction φ generalizing n ψ with
  | evar i =>
    simp only [evarLiftFrom]; split
    · rename_i h; simp only [evarSubst]
      split
      · exact absurd (beq_iff_eq.mp ‹_›) (Nat.ne_of_gt (Nat.lt_succ_of_le h))
      · split <;> simp
        exact absurd (Nat.lt_succ_of_le h) ‹_›
    · rename_i h; simp only [evarSubst]
      split
      · exact absurd (Nat.le_of_eq (beq_iff_eq.mp ‹_›).symm) h
      · split
        · exact absurd (Nat.le_of_lt ‹_›) h
        · rfl
  | svar | symbol | bot => rfl
  | app _ _ ih₁ ih₂ => simp only [evarLiftFrom, evarSubst, ih₁, ih₂]
  | impl _ _ ih₁ ih₂ => simp only [evarLiftFrom, evarSubst, ih₁, ih₂]
  | conj _ _ ih₁ ih₂ => simp only [evarLiftFrom, evarSubst, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => simp only [evarLiftFrom, evarSubst, ih₁, ih₂]
  | exist _ ih =>
    simp only [evarLiftFrom, evarSubst]; congr 1; exact ih (n + 1) (evarLift ψ)
  | forallP _ ih =>
    simp only [evarLiftFrom, evarSubst]; congr 1; exact ih (n + 1) (evarLift ψ)
  | mu _ ih => simp only [evarLiftFrom, evarSubst, ih]
  | nu _ ih => simp only [evarLiftFrom, evarSubst, ih]

theorem evarSubst_evarLift (φ ψ : Pattern Symbol) :
    evarSubst 0 ψ (evarLift φ) = φ :=
  evarSubst_evarLiftFrom φ 0 ψ

theorem evarSubst_evarLiftFrom_succ (φ : Pattern Symbol) (n : Nat) :
    evarSubst n (.evar n) (evarLiftFrom (n + 1) φ) = φ := by
  induction φ generalizing n with
  | evar i =>
    simp only [evarLiftFrom]; split
    · rename_i h; simp only [evarSubst]
      have hgt : n < i + 1 := Nat.lt_succ_of_le (Nat.le_of_succ_le h)
      split
      · exact absurd (beq_iff_eq.mp ‹_›) (Nat.ne_of_gt hgt)
      · simp
    · rename_i h; simp only [evarSubst]
      have hle : i ≤ n := by
        rcases Nat.lt_or_ge i (n + 1) with h' | h'
        · exact Nat.lt_succ_iff.mp h'
        · exact absurd h' h
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · subst heq; simp
      · split
        · exact absurd (Nat.le_of_eq (beq_iff_eq.mp ‹_›).symm) (Nat.not_le.mpr hlt)
        · split
          · exact absurd (Nat.le_of_lt ‹_›) (Nat.not_le.mpr hlt)
          · rfl
  | svar | symbol | bot => rfl
  | app _ _ ih₁ ih₂ => simp only [evarLiftFrom, evarSubst, ih₁, ih₂]
  | impl _ _ ih₁ ih₂ => simp only [evarLiftFrom, evarSubst, ih₁, ih₂]
  | conj _ _ ih₁ ih₂ => simp only [evarLiftFrom, evarSubst, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => simp only [evarLiftFrom, evarSubst, ih₁, ih₂]
  | exist _ ih =>
    simp only [evarLiftFrom, evarSubst]; congr 1
    show evarSubst (n + 1) (evarLift (.evar n)) (evarLiftFrom (n + 2) _) = _
    simp only [evarLift, evarLiftFrom, Nat.zero_le, ↓reduceIte]
    exact ih (n + 1)
  | forallP _ ih =>
    simp only [evarLiftFrom, evarSubst]; congr 1
    show evarSubst (n + 1) (evarLift (.evar n)) (evarLiftFrom (n + 2) _) = _
    simp only [evarLift, evarLiftFrom, Nat.zero_le, ↓reduceIte]
    exact ih (n + 1)
  | mu _ ih => simp only [evarLiftFrom, evarSubst, ih]
  | nu _ ih => simp only [evarLiftFrom, evarSubst, ih]

-- ─────────────────────────────────────────────────────────────
-- Derived quantifier rules
-- ─────────────────────────────────────────────────────────────

variable {Γ : Set (Pattern Symbol)} {φ ψ χ : Pattern Symbol}

def existIntro {n : EVarIndex} (h : Γ ⊩ᵢ evarSubst 0 (.evar n) φ) : Γ ⊩ᵢ ∃ₑ φ :=
  .mp .existQuant h

def existElim (h₁ : Γ ⊩ᵢ ∃ₑ φ) (h₂ : Γ ⊩ᵢ φ ⇒ evarLift ψ) : Γ ⊩ᵢ ψ :=
  .mp (.existGen h₂) h₁

/-- `φ ⇒ ∃x. φ` where `x` is fresh for `φ` (de Bruijn: lift above index 0). -/
def existIntroLift : Γ ⊩ᵢ φ ⇒ ∃ₑ (evarLiftFrom 1 φ) := by
  have h : Γ ⊩ᵢ evarSubst 0 (.evar 0) (evarLiftFrom 1 φ) ⇒ ∃ₑ (evarLiftFrom 1 φ) :=
    .existQuant
  rwa [evarSubst_evarLiftFrom_succ] at h

def existWeaken : Γ ⊩ᵢ φ ⇒ ∃ₑ (evarLift φ) := by
  have h : Γ ⊩ᵢ evarSubst 0 (.evar 0) (evarLift φ) ⇒ ∃ₑ (evarLift φ) := .existQuant
  rwa [evarSubst_evarLift] at h

def existMono (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ ∃ₑ φ ⇒ ∃ₑ ψ :=
  .existGen (φ₂ := ∃ₑ ψ) (.syllogism h existIntroLift)

def forallElim {n : EVarIndex} : Γ ⊩ᵢ ∀ₑ φ ⇒ evarSubst 0 (.evar n) φ := .forallQuant

def forallElimLift : Γ ⊩ᵢ ∀ₑ (evarLiftFrom 1 φ) ⇒ φ := by
  have h : Γ ⊩ᵢ ∀ₑ (evarLiftFrom 1 φ) ⇒ evarSubst 0 (.evar 0) (evarLiftFrom 1 φ) :=
    .forallQuant
  rwa [evarSubst_evarLiftFrom_succ] at h

def forallSpec : Γ ⊩ᵢ ∀ₑ (evarLift φ) ⇒ φ := by
  have h : Γ ⊩ᵢ ∀ₑ (evarLift φ) ⇒ evarSubst 0 (.evar 0) (evarLift φ) := .forallQuant
  rwa [evarSubst_evarLift] at h

def forallIntro (h : Γ ⊩ᵢ evarLift φ ⇒ ψ) : Γ ⊩ᵢ φ ⇒ ∀ₑ ψ := .forallGen h

def forallMono (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ ∀ₑ φ ⇒ ∀ₑ ψ :=
  .forallGen (φ₁ := ∀ₑ φ) (.syllogism forallElimLift h)

/-- Universal generalization as a rule: from `φ` infer `∀x. φ` (`x` fresh). -/
def gen (h : Γ ⊩ᵢ φ) : Γ ⊩ᵢ ∀ₑ (evarLift φ) := .mp (.forallGen implSelf) h

def forallConst : Γ ⊩ᵢ φ ⇒ ∀ₑ (evarLift φ) := .forallGen implSelf

def existConst : Γ ⊩ᵢ ∃ₑ (evarLift φ) ⇒ φ := .existGen implSelf

def forallToExist : Γ ⊩ᵢ ∀ₑ φ ⇒ ∃ₑ φ :=
  .syllogism (.forallQuant (n := 0)) (.existQuant (n := 0))

-- ─────────────────────────────────────────────────────────────
-- Quantifiers and negation (the intuitionistic half of the dualities)
-- ─────────────────────────────────────────────────────────────

/-- `~∃x.φ ⇒ ∀x.~φ`. -/
def negExist : Γ ⊩ᵢ ~(∃ₑ φ) ⇒ ∀ₑ (~φ) :=
  .forallGen (φ₁ := ~(∃ₑ φ)) (contrapositive existIntroLift)

/-- `∀x.~φ ⇒ ~∃x.φ`. -/
def forallNeg : Γ ⊩ᵢ ∀ₑ (~φ) ⇒ ~(∃ₑ φ) :=
  flip (.existGen (φ₂ := ~(∀ₑ (~φ))) (flip forallElimLift))

/-- `∃x.~φ ⇒ ~∀x.φ`.  The converse `~∀x.φ ⇒ ∃x.~φ` is classical. -/
def existNeg : Γ ⊩ᵢ ∃ₑ (~φ) ⇒ ~(∀ₑ φ) :=
  .existGen (φ₂ := ~(∀ₑ φ)) (contrapositive forallElimLift)

/-- `∃x.φ ⇒ ~∀x.~φ`.  The converse is classical. -/
def existToNotForallNot : Γ ⊩ᵢ ∃ₑ φ ⇒ ~(∀ₑ (~φ)) :=
  .existGen (φ₂ := ~(∀ₑ (~φ))) (flip forallElimLift)

/-- `∀x.~~φ ⇐ ~~∀x.φ`; the converse (double negation shift) is not even
sound for the Heyting semantics. -/
def nnForallToForallNn : Γ ⊩ᵢ ~~(∀ₑ φ) ⇒ ∀ₑ (~~φ) :=
  .forallGen (φ₁ := ~~(∀ₑ φ)) (contrapositive (contrapositive forallElimLift))

/-- `∃x.~~φ ⇒ ~~∃x.φ`. -/
def existNnToNnExist : Γ ⊩ᵢ ∃ₑ (~~φ) ⇒ ~~(∃ₑ φ) :=
  .existGen (φ₂ := ~~(∃ₑ φ)) (contrapositive (contrapositive existIntroLift))

-- ─────────────────────────────────────────────────────────────
-- Distribution laws
-- ─────────────────────────────────────────────────────────────

def forallAndDistrib : Γ ⊩ᵢ ∀ₑ (φ ⊓ ψ) ⇒ ∀ₑ φ ⊓ ∀ₑ ψ :=
  implAnd (forallMono andElimLeft) (forallMono andElimRight)

def andForallDistrib : Γ ⊩ᵢ ∀ₑ φ ⊓ ∀ₑ ψ ⇒ ∀ₑ (φ ⊓ ψ) :=
  .forallGen (φ₁ := ∀ₑ φ ⊓ ∀ₑ ψ) (andMono forallElimLift forallElimLift)

def existOrDistrib : Γ ⊩ᵢ ∃ₑ (φ ⊔ ψ) ⇒ ∃ₑ φ ⊔ ∃ₑ ψ :=
  .existGen (φ₂ := ∃ₑ φ ⊔ ∃ₑ ψ) (orMono existIntroLift existIntroLift)

def orExistDistrib : Γ ⊩ᵢ ∃ₑ φ ⊔ ∃ₑ ψ ⇒ ∃ₑ (φ ⊔ ψ) :=
  orElim (existMono orIntroLeft) (existMono orIntroRight)

def existAndDistrib : Γ ⊩ᵢ ∃ₑ (φ ⊓ ψ) ⇒ ∃ₑ φ ⊓ ∃ₑ ψ :=
  implAnd (existMono andElimLeft) (existMono andElimRight)

def forallOrDistrib : Γ ⊩ᵢ ∀ₑ φ ⊔ ∀ₑ ψ ⇒ ∀ₑ (φ ⊔ ψ) :=
  orElim (forallMono orIntroLeft) (forallMono orIntroRight)

def forallImplDistrib : Γ ⊩ᵢ ∀ₑ (φ ⇒ ψ) ⇒ ∀ₑ φ ⇒ ∀ₑ ψ :=
  .exportation (.forallGen (φ₁ := ∀ₑ (φ ⇒ ψ) ⊓ ∀ₑ φ)
    (.syllogism (andMono forallElimLift forallElimLift) andMp))

-- ─────────────────────────────────────────────────────────────
-- Lifted interactions (one side independent of the bound variable)
-- ─────────────────────────────────────────────────────────────

def forallImplLiftLeft : Γ ⊩ᵢ ∀ₑ (evarLift φ ⇒ ψ) ⇒ φ ⇒ ∀ₑ ψ :=
  .exportation (.forallGen (φ₁ := ∀ₑ (evarLift φ ⇒ ψ) ⊓ φ)
    (.syllogism (andMono forallElimLift implSelf) andMp))

def forallImplLiftRight : Γ ⊩ᵢ (φ ⇒ ∀ₑ ψ) ⇒ ∀ₑ (evarLift φ ⇒ ψ) :=
  .forallGen (φ₁ := φ ⇒ ∀ₑ ψ) (implLift forallElimLift)

def existImplLiftLeft : Γ ⊩ᵢ ∃ₑ (evarLift φ ⇒ ψ) ⇒ φ ⇒ ∃ₑ ψ :=
  .existGen (φ₂ := φ ⇒ ∃ₑ ψ) (implLift existIntroLift)

/-- `∀x.(ψ ⇒ χ) ⇒ (∃x.ψ ⇒ χ)` for `x` not free in `χ`. -/
def forallImplExist : Γ ⊩ᵢ ∀ₑ (ψ ⇒ evarLift χ) ⇒ (∃ₑ ψ ⇒ χ) :=
  flip (.existGen (φ₂ := ∀ₑ (ψ ⇒ evarLift χ) ⇒ χ) (flip forallElimLift))

/-- `(∃x.ψ) ⊓ φ ⇒ ∃x.(ψ ⊓ φ)` for `x` not free in `φ`. -/
def pushConjInExist : Γ ⊩ᵢ (∃ₑ ψ) ⊓ φ ⇒ ∃ₑ (ψ ⊓ evarLift φ) :=
  .importation (.existGen (φ₂ := φ ⇒ ∃ₑ (ψ ⊓ evarLift φ))
    (.syllogism curriedAndIntro (implLift existIntroLift)))

def pushConjInExist' : Γ ⊩ᵢ φ ⊓ (∃ₑ ψ) ⇒ ∃ₑ (evarLift φ ⊓ ψ) :=
  .syllogism .permutationAnd (.syllogism pushConjInExist (existMono .permutationAnd))

/-!
## Not derivable (classical)

The following classical laws from `MatchingLogic/FOLProofs.lean` have no
intuitionistic derivation, because they are not valid in the Heyting
semantics:

* `notForallNotToExist : ~∀x.~φ ⇒ ∃x.φ`  (needs DNE)
* `negForall : ~∀x.φ ⇒ ∃x.~φ`  (needs DNE)
* `existImplLiftRight : (φ ⇒ ∃x.ψ) ⇒ ∃x.(φ ⇒ ψ)`  (independence of premise)
* `forallNnToNnForall : ∀x.~~φ ⇒ ~~∀x.φ`  (double negation shift)
-/

end IML
