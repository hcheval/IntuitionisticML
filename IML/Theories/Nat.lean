import IML.DerivedRules.Definedness
import IML.DerivedRules.Fixpoint

/-!
# The theory of natural numbers in iML

A specification of the natural numbers as a matching-logic theory, in the
intuitionistic system. The signature has three symbols, `zero`, `succ` and
`nat` (the sort), on top of the definedness symbol `⌈·⌉`. The axioms are the
usual ones:

* **functionality** — `zero` is an element and `succ` is a total function:
  `∃y. zero =ⁱ y` and `∀x. ∃y. succ x =ⁱ y`;
* **no confusion** — `∀x. ¬(zero =ⁱ succ x)` and
  `∀x y. succ x =ⁱ succ y ⇒ x =ⁱ y`;
* **no junk** — `nat =ⁱ μX. zero ⊔ succ X`: the naturals are the *least* set
  containing `zero` and closed under `succ`.

Equalities are the *positive* equality `=ⁱ` of `IML.DerivedRules.Definedness`
(`φ =ⁱ ψ := ∀z. z ∈ (φ ⟺ ψ)`), which has the elimination laws the classical
`⌊φ ⟺ ψ⌋ = ¬⌈¬(φ ⟺ ψ)⌉` lacks intuitionistically.

Everything in this file is derived inside the logic, from the axioms, with
the rules of `IML.Proof`; nothing is assumed about models.

## What the axioms give and what they do not

* The **induction principle** `natInduction` — if `zero ⇒ P` and
  `succ ⬝ P ⇒ P` then `nat ⇒ P` — is no-junk plus KNASTER–TARSKI, exactly
  as in the classical development.
* **Case analysis** `natCases` — every natural is `zero` or a successor of a
  natural — is no-junk plus *unfolding* of the least fixpoint, which needs
  only the PRE-FIXPOINT rule and framing. No excluded middle is involved; it
  is constructive.
* Turning a membership fact `x ∈ succ m` into an equality `succ m =ⁱ x`
  is *not* available from the classical-shaped functionality axiom
  `∃y. succ m =ⁱ y`: it would need Lemma 3.9(→) `x ∈ y ⇒ x =ⁱ y`, whose
  derivability is open in iML (`IML.mem_impl_eqI_of_pred`). The class
  `IsNatTheoryPos` adds functionality in its *positive* form
  (`x ∈ zero ⇒ zero =ⁱ x`, `x ∈ succ m ⇒ succ m =ⁱ x`: any element of the
  singleton is all of it), which is classically equivalent and gives the
  `=ⁱ`-shaped case analysis `natCasesEq` and the decidability of
  equality with `zero`, `zeroEqDecidable`.
-/

namespace IML

open Pattern

-- ─────────────────────────────────────────────────────────────
-- Signature
-- ─────────────────────────────────────────────────────────────

/-- The symbols of the theory of naturals: the constructors and the sort. -/
class HasNatOps (Symbol : Type) where
  zero : Symbol
  succ : Symbol
  nat : Symbol

variable {Symbol : Type} [HasCeil Symbol] [HasNatOps Symbol]

/-- The pattern `zero`, matching the number 0. -/
def Pattern.zero_ : Pattern Symbol := .symbol HasNatOps.zero

/-- The pattern `succ`; `succ ⬝ φ` matches the successors of the elements of `φ`. -/
def Pattern.succ_ : Pattern Symbol := .symbol HasNatOps.succ

/-- The sort pattern `nat`, matching all natural numbers. -/
def Pattern.nat_ : Pattern Symbol := .symbol HasNatOps.nat

/-- The body `zero ⊔ succ ⬝ X` of the fixpoint defining the naturals. -/
def natBody : Pattern Symbol := zero_ ⊔ succ_ ⬝ .svar 0

omit [HasCeil Symbol] in
theorem natBody_subst (P : Pattern Symbol) :
    natBody[0 ₛ↦ P] = Pattern.disj zero_ (succ_ ⬝ P) := by
  simp [natBody, svarSubst, Pattern.zero_, Pattern.succ_]

omit [HasCeil Symbol] in
theorem natBody_pos : SVarPositive (natBody : Pattern Symbol) 0 :=
  .disj .symbol (.app .symbol .svar)

omit [HasCeil Symbol] in
theorem evarLift_zero : evarLift (zero_ : Pattern Symbol) = zero_ := rfl

omit [HasCeil Symbol] in
theorem evarLift_succ : evarLift (succ_ : Pattern Symbol) = succ_ := rfl

omit [HasCeil Symbol] in
theorem evarLift_nat : evarLift (nat_ : Pattern Symbol) = nat_ := rfl

omit [HasCeil Symbol] in
theorem evarLift_succ_evar (n : EVarIndex) :
    evarLift (succ_ ⬝ .evar n : Pattern Symbol) = succ_ ⬝ .evar (n + 1) := by
  simp [evarLift, evarLiftFrom, Pattern.succ_]

omit [HasCeil Symbol] [HasNatOps Symbol] in
theorem evarLift_conj (φ ψ : Pattern Symbol) :
    evarLift (Pattern.conj φ ψ) = Pattern.conj (evarLift φ) (evarLift ψ) := rfl

omit [HasCeil Symbol] [HasNatOps Symbol] in
theorem evarLift_neg (φ : Pattern Symbol) : evarLift (~φ) = ~(evarLift φ) := rfl

/-- The application context `succ ⬝ □`. -/
def succCtx : AppCtx Symbol := .right succ_ .hole

omit [HasCeil Symbol] in
theorem succCtx_fill (φ : Pattern Symbol) : (succCtx (Symbol := Symbol)).fill φ = succ_ ⬝ φ := rfl

-- ─────────────────────────────────────────────────────────────
-- The theory
-- ─────────────────────────────────────────────────────────────

/-- `Γ` contains the axioms of the naturals (and the definedness axiom). -/
class IsNatTheory (Symbol : Type) [HasCeil Symbol] [HasNatOps Symbol]
    (Γ : Set (Pattern Symbol)) : Prop extends IsDefinedness Symbol Γ where
  /-- `∃y. zero =ⁱ y`: zero is an element. -/
  zeroFun : (∃ₑ (zero_ =ⁱₘₗ .evar 0)) ∈ Γ
  /-- `∀x. ∃y. succ x =ⁱ y`: successor is a total function. -/
  succFun : (∀ₑ (∃ₑ (succ_ ⬝ .evar 1 =ⁱₘₗ .evar 0))) ∈ Γ
  /-- `∀x. ¬(zero =ⁱ succ x)`. -/
  noConf : (∀ₑ ~(zero_ =ⁱₘₗ succ_ ⬝ .evar 0)) ∈ Γ
  /-- `∀x y. succ x =ⁱ succ y ⇒ x =ⁱ y`. -/
  succInj : (∀ₑ (∀ₑ ((succ_ ⬝ .evar 1 =ⁱₘₗ succ_ ⬝ .evar 0) ⇒ (.evar 1 =ⁱₘₗ .evar 0)))) ∈ Γ
  /-- `nat =ⁱ μX. zero ⊔ succ X`: no junk. -/
  noJunk : (nat_ =ⁱₘₗ μ natBody) ∈ Γ

/-- `Γ` also contains functionality of the constructors in the *positive*
form "any element of the singleton is all of it". Classically these follow
from `IsNatTheory`; intuitionistically the derivation would go through
Lemma 3.9(→), which is open. -/
class IsNatTheoryPos (Symbol : Type) [HasCeil Symbol] [HasNatOps Symbol]
    (Γ : Set (Pattern Symbol)) : Prop extends IsNatTheory Symbol Γ where
  /-- `∀x. x ∈ zero ⇒ zero =ⁱ x`. -/
  zeroSingleton : (∀ₑ ((.evar 0 ∈ₘₗ zero_) ⇒ (zero_ =ⁱₘₗ .evar 0))) ∈ Γ
  /-- `∀x y. y ∈ succ x ⇒ succ x =ⁱ y`. -/
  succSingleton :
    (∀ₑ (∀ₑ ((.evar 0 ∈ₘₗ succ_ ⬝ .evar 1) ⇒ (succ_ ⬝ .evar 1 =ⁱₘₗ .evar 0)))) ∈ Γ

variable {Γ : Set (Pattern Symbol)} [IsNatTheory Symbol Γ]

-- ─────────────────────────────────────────────────────────────
-- The axioms, instantiated at variables
-- ─────────────────────────────────────────────────────────────

/-- `∃y. zero =ⁱ y`. -/
def zeroFunctional : Γ ⊩ᵢ ∃ₑ (zero_ =ⁱₘₗ .evar 0) := .assumption IsNatTheory.zeroFun

/-- `∃y. succ n =ⁱ y` (under the binder `n` is shifted to `n + 1`). -/
def succFunctional (n : EVarIndex) : Γ ⊩ᵢ ∃ₑ (succ_ ⬝ .evar (n + 1) =ⁱₘₗ .evar 0) := by
  have h : Γ ⊩ᵢ evarSubst 0 (.evar n) (∃ₑ (succ_ ⬝ .evar 1 =ⁱₘₗ .evar 0)) :=
    .mp (forallElim (n := n)) (.assumption IsNatTheory.succFun)
  simpa [Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff, Pattern.succ_,
    evarSubst, evarLift, evarLiftFrom] using h

/-- `¬(zero =ⁱ succ n)`. -/
def noConfusion (n : EVarIndex) : Γ ⊩ᵢ ~(zero_ =ⁱₘₗ succ_ ⬝ .evar n) := by
  have h : Γ ⊩ᵢ evarSubst 0 (.evar n) (~(zero_ =ⁱₘₗ succ_ ⬝ .evar 0)) :=
    .mp forallElim (.assumption IsNatTheory.noConf)
  simpa [Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff, Pattern.neg,
    Pattern.succ_, Pattern.zero_, evarSubst, evarLift, evarLiftFrom] using h

/-- `succ n =ⁱ succ m ⇒ n =ⁱ m`. -/
def succInjective (n m : EVarIndex) :
    Γ ⊩ᵢ (succ_ ⬝ .evar n =ⁱₘₗ succ_ ⬝ .evar m) ⇒ (.evar n =ⁱₘₗ .evar m) := by
  have h₁ : Γ ⊩ᵢ evarSubst 0 (.evar n)
      (∀ₑ ((succ_ ⬝ .evar 1 =ⁱₘₗ succ_ ⬝ .evar 0) ⇒ (.evar 1 =ⁱₘₗ .evar 0))) :=
    .mp forallElim (.assumption IsNatTheory.succInj)
  simp only [Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff,
    Pattern.succ_, evarSubst, evarLift, evarLiftFrom] at h₁
  have h₂ := Proof.mp (forallElim (n := m)) h₁
  simpa [Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff,
    Pattern.succ_, evarSubst, evarLift, evarLiftFrom] using h₂

/-- `nat =ⁱ μX. zero ⊔ succ X`. -/
def natNoJunk : Γ ⊩ᵢ nat_ =ⁱₘₗ μ natBody := .assumption IsNatTheory.noJunk

-- ─────────────────────────────────────────────────────────────
-- Induction, folding and unfolding
-- ─────────────────────────────────────────────────────────────

/-- `nat ⇒ μX. zero ⊔ succ X`. -/
def natToMu : Γ ⊩ᵢ nat_ ⇒ μ natBody := .mp eqI_elim natNoJunk

/-- `μX. zero ⊔ succ X ⇒ nat`. -/
def muToNat : Γ ⊩ᵢ μ natBody ⇒ nat_ := .mp eqI_elim (.mp eqI_symm natNoJunk)

/-- **Induction.** If `P` contains `zero` and is closed under `succ` then it
contains every natural: no-junk followed by KNASTER–TARSKI applied to the
body `zero ⊔ succ ⬝ P ⇒ P`. -/
def natInduction {P : Pattern Symbol} (base : Γ ⊩ᵢ zero_ ⇒ P) (step : Γ ⊩ᵢ succ_ ⬝ P ⇒ P) :
    Γ ⊩ᵢ nat_ ⇒ P :=
  .syllogism natToMu (.knasterTarski (by rw [natBody_subst]; exact orElim base step))

/-- Folding: `zero ⊔ succ ⬝ μX.(zero ⊔ succ X) ⇒ μX.(zero ⊔ succ X)` (PRE-FIXPOINT). -/
def muNatFold : Γ ⊩ᵢ zero_ ⊔ succ_ ⬝ μ natBody ⇒ μ natBody := by
  have h := muPreFixpoint (Γ := Γ) natBody_pos
  rwa [natBody_subst] at h

/-- Unfolding: `μX.(zero ⊔ succ X) ⇒ zero ⊔ succ ⬝ μX.(zero ⊔ succ X)`. By
KNASTER–TARSKI it suffices that `zero ⊔ succ ⬝ (zero ⊔ succ ⬝ μ)` folds into
`zero ⊔ succ ⬝ μ`, which is folding under `succ`. -/
def muNatUnfold : Γ ⊩ᵢ μ natBody ⇒ zero_ ⊔ succ_ ⬝ μ natBody := by
  apply muUnfoldLeft
  rw [natBody_subst, natBody_subst]
  exact orMono implSelf (.framingRight muNatFold)

/-- `zero ⇒ nat`: zero is a natural. -/
def zeroNat : Γ ⊩ᵢ zero_ ⇒ nat_ := .syllogism orIntroLeft (.syllogism muNatFold muToNat)

/-- `succ ⬝ nat ⇒ nat`: the successor of a natural is a natural. -/
def succNat : Γ ⊩ᵢ succ_ ⬝ nat_ ⇒ nat_ :=
  .syllogism (.framingRight natToMu) (.syllogism orIntroRight (.syllogism muNatFold muToNat))

/-- **Unfolding the naturals**: `nat ⇒ zero ⊔ succ ⬝ nat`. Every natural is
zero or the successor of a natural. This is the set-level case analysis; it
uses only the fixpoint rules, no excluded middle. -/
def natUnfold : Γ ⊩ᵢ nat_ ⇒ zero_ ⊔ succ_ ⬝ nat_ :=
  .syllogism natToMu (.syllogism muNatUnfold (orMono implSelf (.framingRight muToNat)))

/-- `zero ⊔ succ ⬝ nat ⇒ nat`. -/
def natFold : Γ ⊩ᵢ zero_ ⊔ succ_ ⬝ nat_ ⇒ nat_ := orElim zeroNat succNat

-- ─────────────────────────────────────────────────────────────
-- Definedness of the constructors
-- ─────────────────────────────────────────────────────────────

/-- `⌈zero⌉`: zero is defined (it equals some `y`, and `⌈y⌉`). -/
def zeroDefined : Γ ⊩ᵢ ⌈zero_⌉ :=
  existElim zeroFunctional (ψ := ⌈zero_⌉)
    (.syllogism eqI_symm
      (implMp (.exportation (eqI_leibniz_in ceilCtx .hole (φ := .evar 0) (ψ := zero_)))
        (extraPremise ceil_of_evar)))

/-- `⌈succ n⌉`: the successor of anything is defined. -/
def succDefined (n : EVarIndex) : Γ ⊩ᵢ ⌈succ_ ⬝ .evar n⌉ :=
  existElim (succFunctional n) (ψ := ⌈succ_ ⬝ .evar n⌉) (by
    rw [evarLift_ceil, evarLift_succ_evar]
    exact .syllogism eqI_symm
      (implMp (.exportation
          (eqI_leibniz_in ceilCtx .hole (φ := .evar 0) (ψ := succ_ ⬝ .evar (n + 1))))
        (extraPremise ceil_of_evar)))

-- ─────────────────────────────────────────────────────────────
-- Case analysis on an element
-- ─────────────────────────────────────────────────────────────

/-- `nat ⇒ ∃m. m ⊓ nat`: every natural is *some* element `m` of `nat`. -/
def natElem : Γ ⊩ᵢ nat_ ⇒ ∃ₑ (.evar 0 ⊓ nat_) :=
  .syllogism (implAnd (extraPremise .existence) implSelf) pushConjInExist

/-- **Case analysis on a natural `x`** (membership form): `x ∈ nat` implies
`x ∈ zero` or `x ∈ succ m` for some natural `m`. Derived by unfolding the
fixpoint (`natUnfold`) inside the membership, then propagating `⊔` and `∃`
out of `⌈·⌉`; constructive. -/
def natCases (n : EVarIndex) :
    Γ ⊩ᵢ (.evar n ∈ₘₗ nat_) ⇒
      (.evar n ∈ₘₗ zero_) ⊔ ∃ₑ ((.evar 0 ∈ₘₗ nat_) ⊓ (.evar (n + 1) ∈ₘₗ succ_ ⬝ .evar 0)) :=
  -- x ∈ succ ⬝ nat ⇒ ∃m. x ∈ succ ⬝ (m ⊓ nat)
  let s₁ : Γ ⊩ᵢ (.evar n ∈ₘₗ succ_ ⬝ nat_) ⇒ ∃ₑ (.evar (n + 1) ∈ₘₗ succ_ ⬝ (.evar 0 ⊓ nat_)) :=
    .syllogism
      (ceil_mono (andMonoRight (.syllogism (.framingRight natElem) .propagationExistRight)))
      (by rw [← evarLift_evar]; exact iffMpLeft memExist)
  -- x ∈ succ ⬝ (m ⊓ nat) ⇒ m ∈ nat ⊓ x ∈ succ ⬝ m
  let s₂ : Γ ⊩ᵢ (.evar (n + 1) ∈ₘₗ succ_ ⬝ (.evar 0 ⊓ nat_)) ⇒
      (.evar 0 ∈ₘₗ nat_) ⊓ (.evar (n + 1) ∈ₘₗ succ_ ⬝ .evar 0) :=
    implAnd (.syllogism (ceil_mono andElimRight) (ceil_ctx_impl_ceil succCtx))
      (ceil_mono (andMonoRight (.framingRight andElimLeft)))
  .syllogism (ceil_mono (andMonoRight natUnfold))
    (.syllogism (iffMpLeft memOr) (orMono implSelf (.syllogism s₁ (existMono s₂))))

-- ─────────────────────────────────────────────────────────────
-- With positive functionality: equalities instead of memberships
-- ─────────────────────────────────────────────────────────────

section Pos

variable [IsNatTheoryPos Symbol Γ]

/-- `x ∈ zero ⇒ zero =ⁱ x`. -/
def zeroSingleton (n : EVarIndex) : Γ ⊩ᵢ (.evar n ∈ₘₗ zero_) ⇒ (zero_ =ⁱₘₗ .evar n) := by
  have h : Γ ⊩ᵢ evarSubst 0 (.evar n) ((.evar 0 ∈ₘₗ zero_) ⇒ (zero_ =ⁱₘₗ .evar 0)) :=
    .mp forallElim (.assumption IsNatTheoryPos.zeroSingleton)
  simpa [Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff, Pattern.zero_,
    evarSubst, evarLift, evarLiftFrom] using h

/-- `x ∈ succ m ⇒ succ m =ⁱ x`. -/
def succSingleton (n m : EVarIndex) :
    Γ ⊩ᵢ (.evar n ∈ₘₗ succ_ ⬝ .evar m) ⇒ (succ_ ⬝ .evar m =ⁱₘₗ .evar n) := by
  have h₁ : Γ ⊩ᵢ evarSubst 0 (.evar m)
      (∀ₑ ((.evar 0 ∈ₘₗ succ_ ⬝ .evar 1) ⇒ (succ_ ⬝ .evar 1 =ⁱₘₗ .evar 0))) :=
    .mp forallElim (.assumption IsNatTheoryPos.succSingleton)
  simp only [Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff,
    Pattern.succ_, evarSubst, evarLift, evarLiftFrom] at h₁
  have h₂ := Proof.mp (forallElim (n := n)) h₁
  simpa [Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff,
    Pattern.succ_, evarSubst, evarLift, evarLiftFrom] using h₂

/-- No confusion in overlap form: `zero` and `succ m` have no common element.
If `c` were in both, `zero =ⁱ c =ⁱ succ m`. -/
def zeroSuccDisjoint (m : EVarIndex) : Γ ⊩ᵢ ~⌈zero_ ⊓ succ_ ⬝ .evar m⌉ :=
  let s₁ : Γ ⊩ᵢ ⌈zero_ ⊓ succ_ ⬝ .evar m⌉ ⇒ ∃ₑ ⌈.evar 0 ⊓ (zero_ ⊓ succ_ ⬝ .evar (m + 1))⌉ :=
    .syllogism (ceil_mono (.syllogism (implAnd (extraPremise .existence) implSelf)
                                      pushConjInExist))
      (by
        rw [evarLift_conj, evarLift_zero, evarLift_succ_evar]
        exact ctxPropagationExist ceilCtx)
  .syllogism s₁ (.existGen (φ₂ := ⊥ₘ)
    (.syllogism memAndElim
      (.syllogism (andMono (zeroSingleton 0) (.syllogism (succSingleton 0 (m + 1)) eqI_symm))
        (.syllogism eqI_trans (noConfusion (m + 1))))))

/-- **Case analysis on a natural `x`** (equality form): `x ∈ nat` implies
`zero =ⁱ x` or `succ m =ⁱ x` for some natural `m`. -/
def natCasesEq (n : EVarIndex) :
    Γ ⊩ᵢ (.evar n ∈ₘₗ nat_) ⇒
      (zero_ =ⁱₘₗ .evar n) ⊔ ∃ₑ ((.evar 0 ∈ₘₗ nat_) ⊓ (succ_ ⬝ .evar 0 =ⁱₘₗ .evar (n + 1))) :=
  .syllogism (natCases n)
    (orMono (zeroSingleton n) (existMono (andMonoRight (succSingleton (n + 1) 0))))

/-- **Equality with zero is decidable** on the naturals:
`x ∈ nat ⇒ (zero =ⁱ x) ⊔ ¬(zero =ⁱ x)`. In the successor case,
`zero =ⁱ x =ⁱ succ m` contradicts no-confusion. No excluded middle: the
disjunction comes from unfolding the fixpoint. -/
def zeroEqDecidable (n : EVarIndex) :
    Γ ⊩ᵢ (.evar n ∈ₘₗ nat_) ⇒ (zero_ =ⁱₘₗ .evar n) ⊔ ~(zero_ =ⁱₘₗ .evar n) :=
  .syllogism (natCasesEq n)
    (orMono implSelf (.existGen (φ₂ := ~(zero_ =ⁱₘₗ .evar n)) (by
      rw [evarLift_neg, evarLift_eqI, evarLift_zero, evarLift_evar]
      exact .syllogism andElimRight (.exportation (.syllogism .permutationAnd
        (.syllogism (andMonoRight eqI_symm) (.syllogism eqI_trans (noConfusion 0))))))))

end Pos

end IML
