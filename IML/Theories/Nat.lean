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

## Decidability of equality

Is `x =ⁱ y ⊔ ¬(x =ⁱ y)` derivable for naturals `x`, `y`?

* The special case `y := zero` is derived outright (`zeroEqDecidable`, from
  `IsNatTheoryPos`): by case analysis, in the successor case
  `zero =ⁱ x =ⁱ succ m` contradicts no-confusion.
* The general statement is proved as in Heyting arithmetic, by induction on
  `y` with the predicate `∀x. x ∈ nat ⇒ (y =ⁱ x) ⊔ ¬(y =ⁱ x)`
  (`natEqDecidableSet`, `natEqDecidable`). The successor step needs, in the
  branch `y =ⁱ k`, the *internal* congruence `(y =ⁱ k) ⇒ (succ y =ⁱ succ k)`
  (`eqI_congr_succ`), and carrying the predicate through the application
  context `succ ⬝ □` needs `¬(y =ⁱ x)` and `x ∈ nat` to enter contexts. Both
  amount to the *predicate-propagation* principle `θ ⇒ ⌊θ⌋ⁱ` for
  `θ = ⌈φ⌉, ⌊φ⌋ⁱ` (`IML.IsPred`): sound in every Heyting model, not derived
  from the rules of iML. It is assumed as the axiom scheme `HasPredProp`, and
  decidability is proved relative to it.

So the obstacle to decidable equality is not excluded middle — the proof is
the constructive double induction — but the fact that iML's rules do not
let a positive equality enter an application context *as an equality*. Note
also that `x =ⁱ y ⊔ ¬(x =ⁱ y)` is *valid in every Heyting model* for
element variables `x`, `y`, because element variables denote crisp points;
hence it cannot be refuted by a Heyting countermodel either.
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

omit [HasCeil Symbol] [HasNatOps Symbol] in
theorem evarLift_app (φ ψ : Pattern Symbol) : evarLift (φ ⬝ ψ) = evarLift φ ⬝ evarLift ψ := rfl

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

-- ─────────────────────────────────────────────────────────────
-- Predicate propagation: the one principle iML does not provide
-- ─────────────────────────────────────────────────────────────

/-- The predicate-propagation axiom schemes: definedness patterns and positive
totalities are predicate patterns, `θ ⇒ ⌊θ⌋ⁱ`. Sound in every `HModel` with
definedness (both have the same value at every point); whether they are
derivable in iML is open (`IML.IsPred`). Assumed, as axioms in `Γ`, only for
the results that need to rewrite with an equality *inside* `⌈·⌉`:
associativity and decidability of equality. -/
class HasPredProp (Symbol : Type) [HasCeil Symbol] (Γ : Set (Pattern Symbol)) : Prop where
  ceilPred : ∀ φ : Pattern Symbol, (⌈φ⌉ ⇒ ⌊⌈φ⌉⌋ⁱ) ∈ Γ
  totalPred : ∀ φ : Pattern Symbol, (⌊φ⌋ⁱ ⇒ ⌊⌊φ⌋ⁱ⌋ⁱ) ∈ Γ

section PredProp

variable [HasPredProp Symbol Γ]

/-- A positive equality is a predicate pattern (from the scheme). -/
def eqI_isPred (φ ψ : Pattern Symbol) : IsPred Γ (φ =ⁱₘₗ ψ) :=
  .assumption (HasPredProp.totalPred (φ ⟺ ψ))

/-- Leibniz's law for a hole below `⌈·⌉`, an application-free context `P`
and an application context `A`: `(φ =ⁱ ψ) ⊓ ⌈P[A[φ]]⌉ ⇒ ⌈P[A[ψ]]⌉`. The
equality enters `⌈·⌉` by predicate propagation, then `eqI_leibniz` applies. -/
def eqI_leibniz_ceil (P : PCtx Symbol) (A : AppCtx Symbol) {φ ψ : Pattern Symbol} :
    Γ ⊩ᵢ (φ =ⁱₘₗ ψ) ⊓ ⌈P.fill (A.fill φ)⌉ ⇒ ⌈P.fill (A.fill ψ)⌉ :=
  .syllogism (pred_ctx (eqI_isPred φ ψ) ceilCtx) (ceil_mono (eqI_leibniz P A .hole φ ψ))

/-- Leibniz's law for the two-hole context `⌈A₁[□] ⊓ A₂[□]⌉`. -/
def eqI_leibniz_ceil₂ (A₁ A₂ : AppCtx Symbol) {φ ψ : Pattern Symbol} :
    Γ ⊩ᵢ (φ =ⁱₘₗ ψ) ⊓ ⌈A₁.fill φ ⊓ A₂.fill φ⌉ ⇒ ⌈A₁.fill ψ ⊓ A₂.fill ψ⌉ :=
  .syllogism (implAnd andElimLeft (eqI_leibniz_ceil (.conjL .hole (A₂.fill φ)) A₁))
    (eqI_leibniz_ceil (.conjR (A₁.fill ψ) .hole) A₂)

/-- Lemma 3.9(→) for variables, `x ∈ y ⇒ x =ⁱ y`, from the `⌈·⌉` scheme. -/
def mem_impl_eqI (n m : EVarIndex) : Γ ⊩ᵢ (.evar n ∈ₘₗ .evar m) ⇒ (.evar n =ⁱₘₗ .evar m) :=
  mem_impl_eqI_of_pred (.assumption (by
    simp only [Pattern.memML, evarLift_ceil, evarLift_conj, evarLift_evar]
    exact HasPredProp.ceilPred _))

end PredProp

-- ─────────────────────────────────────────────────────────────
-- Decidability of equality, relative to predicate propagation
-- ─────────────────────────────────────────────────────────────

section Decidable

variable [IsNatTheoryPos Symbol Γ] [HasPredProp Symbol Γ]

/-- `(y =ⁱ x) ⊔ ¬(y =ⁱ x)`. -/
def eqDec (y x : EVarIndex) : Pattern Symbol :=
  (.evar y =ⁱₘₗ .evar x) ⊔ ~(.evar y =ⁱₘₗ .evar x)

/-- The induction predicate `∀x. x ∈ nat ⇒ (y =ⁱ x) ⊔ ¬(y =ⁱ x)` ("equality
with `y` is decidable on the naturals"); under the binder `y` is shifted. -/
def decPred (y : EVarIndex) : Pattern Symbol := ∀ₑ ((.evar 0 ∈ₘₗ nat_) ⇒ eqDec (y + 1) 0)

/-- The set `{y | equality with y is decidable}`, as `∃y. y ⊓ decPred y`. -/
def decSet : Pattern Symbol := ∃ₑ (.evar 0 ⊓ decPred 0)

omit [HasNatOps Symbol] in
theorem evarLift_eqDec (y x : EVarIndex) :
    evarLift (eqDec y x : Pattern Symbol) = eqDec (y + 1) (x + 1) := by
  simp [eqDec, Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff,
    Pattern.neg, evarLift, evarLiftFrom]

theorem evarLift_decPred (y : EVarIndex) :
    evarLift (decPred y : Pattern Symbol) = decPred (y + 1) := by
  simp [decPred, eqDec, Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff,
    Pattern.neg, Pattern.nat_, evarLift, evarLiftFrom]

theorem evarLift_decSet : evarLift (decSet : Pattern Symbol) = decSet := by
  simp [decSet, decPred, eqDec, Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil,
    Pattern.iff, Pattern.neg, Pattern.nat_, evarLift, evarLiftFrom]

/-- Instantiating the predicate: `decPred y ⇒ k ∈ nat ⇒ (y =ⁱ k) ⊔ ¬(y =ⁱ k)`. -/
def decPred_elim (y k : EVarIndex) : Γ ⊩ᵢ decPred y ⇒ ((.evar k ∈ₘₗ nat_) ⇒ eqDec y k) := by
  have h : Γ ⊩ᵢ decPred y ⇒ evarSubst 0 (.evar k) ((.evar 0 ∈ₘₗ nat_) ⇒ eqDec (y + 1) 0) :=
    forallElim
  simpa [decPred, eqDec, Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff,
    Pattern.neg, Pattern.nat_, evarSubst, evarLift, evarLiftFrom] using h

/-- `(y =ⁱ x) ⊔ ¬(y =ⁱ x)` leaves an application context: the positive
disjunct because it is a positive totality, the negative one because the
equality, a predicate pattern, enters the context and refutes it there. -/
def eqDec_out (C : AppCtx Symbol) (y x : EVarIndex) {φ : Pattern Symbol} :
    Γ ⊩ᵢ C.fill (φ ⊓ eqDec y x) ⇒ eqDec y x :=
  .syllogism (ctxFraming C andElimRight)
    (.syllogism (ctxPropagationOr C)
      (orMono (.syllogism (ctxImplDefined C) ceil_totalI)
        (.exportation (.syllogism .permutationAnd
          (.syllogism (pred_ctx (eqI_isPred (.evar y) (.evar x)) C)
            (.syllogism (ctxFraming C (.syllogism .permutationAnd andMp)) (ctxBot C)))))))

/-- The induction predicate leaves an application context:
`C[φ ⊓ decPred y] ⇒ decPred y`. -/
def decPred_out (C : AppCtx Symbol) (y : EVarIndex) {φ : Pattern Symbol} :
    Γ ⊩ᵢ C.fill (φ ⊓ decPred y) ⇒ decPred y :=
  .forallGen (φ₁ := C.fill (φ ⊓ decPred y)) (by
    rw [evarLift_fill, evarLift_conj, evarLift_decPred]
    exact .exportation (.syllogism .permutationAnd
      (.syllogism (pred_ctx (.assumption (HasPredProp.ceilPred (.evar 0 ⊓ nat_))) C.liftEVar)
        (.syllogism (ctxFraming C.liftEVar
            (implAnd (.syllogism andElimRight andElimLeft)
              (.syllogism (implAnd (.syllogism andElimRight andElimRight) andElimLeft)
                (.syllogism (andMonoLeft (decPred_elim (y + 1) 0)) andMp))))
          (eqDec_out C.liftEVar (y + 1) 0)))))

/-- **Internal congruence of `succ`** (needs predicate propagation):
`(y =ⁱ k) ⊓ (succ y =ⁱ w) ⇒ (succ k =ⁱ w)`. Under the binder of `=ⁱ`, `y`
is replaced by `k` in both halves of `succ y ⟺ w` inside `⌈z ⊓ ·⌉`. -/
def eqI_congr_succ (y k w : EVarIndex) :
    Γ ⊩ᵢ (.evar y =ⁱₘₗ .evar k) ⊓ (succ_ ⬝ .evar y =ⁱₘₗ .evar w) ⇒
      (succ_ ⬝ .evar k =ⁱₘₗ .evar w) := by
  apply Proof.forallGen
  simp only [evarLift_conj, evarLift_eqI, evarLift_iff, evarLift_app, evarLift_succ, evarLift_evar]
  exact .syllogism (implAnd andElimLeft (.syllogism andElimRight totalI_elim))
    (.syllogism
      (implAnd andElimLeft
        (eqI_leibniz_ceil
          (.conjR (.evar 0)
            (.conjL (.implL .hole (.evar (w + 1))) (.evar (w + 1) ⇒ succ_ ⬝ .evar (y + 1))))
          succCtx))
      (eqI_leibniz_ceil
        (.conjR (.evar 0)
          (.conjR (succ_ ⬝ .evar (k + 1) ⇒ .evar (w + 1)) (.implR (.evar (w + 1)) .hole)))
        succCtx))

/-- Base case: equality with `zero` is decidable. Name `zero` as `v`; for a
natural `x`, either `zero =ⁱ x` (so `v =ⁱ x`) or `x` is a successor (so
`v =ⁱ x` would make `zero` a successor). -/
def decBase : Γ ⊩ᵢ zero_ ⇒ decSet :=
  -- under ∃v (v = evar 0): (zero =ⁱ v) ⊓ zero ⇒ v ⊓ decPred 0
  let s₁ : Γ ⊩ᵢ (zero_ =ⁱₘₗ .evar 0) ⊓ zero_ ⇒ .evar 0 := .syllogism (andMonoLeft eqI_elim) andMp
  -- under ∀x (x = evar 0, v = evar 1): the zero case
  let cZero : Γ ⊩ᵢ ((zero_ =ⁱₘₗ .evar 1) ⊓ zero_) ⊓ (zero_ =ⁱₘₗ .evar 0) ⇒ eqDec 1 0 :=
    .syllogism (.syllogism (andMonoLeft (.syllogism andElimLeft eqI_symm)) eqI_trans) orIntroLeft
  -- under ∃k (k = evar 0, x = evar 1, v = evar 2): the successor case
  let cSucc : Γ ⊩ᵢ ((zero_ =ⁱₘₗ .evar 2) ⊓ zero_) ⊓
      ((.evar 0 ∈ₘₗ nat_) ⊓ (succ_ ⬝ .evar 0 =ⁱₘₗ .evar 1)) ⇒ ~(.evar 2 =ⁱₘₗ .evar 1) :=
    .exportation (.syllogism
      (implAnd (.syllogism (andMonoLeft (.syllogism andElimLeft andElimLeft)) eqI_trans)
        (.syllogism andElimLeft (.syllogism andElimRight (.syllogism andElimRight eqI_symm))))
      (.syllogism eqI_trans (noConfusion 0)))
  -- under ∀x: the successor case, with the existential
  let cSucc' : Γ ⊩ᵢ ((zero_ =ⁱₘₗ .evar 1) ⊓ zero_) ⊓
      ∃ₑ ((.evar 0 ∈ₘₗ nat_) ⊓ (succ_ ⬝ .evar 0 =ⁱₘₗ .evar 1)) ⇒ ~(.evar 1 =ⁱₘₗ .evar 0) :=
    .syllogism pushConjInExist' (.existGen (φ₂ := ~(.evar 1 =ⁱₘₗ .evar 0)) (by
      simp only [evarLift_conj, evarLift_eqI, evarLift_zero, evarLift_evar, evarLift_neg]
      exact cSucc))
  let s₂ : Γ ⊩ᵢ (zero_ =ⁱₘₗ .evar 0) ⊓ zero_ ⇒ decPred 0 :=
    .forallGen (φ₁ := (zero_ =ⁱₘₗ .evar 0) ⊓ zero_) (by
      rw [evarLift_conj, evarLift_eqI, evarLift_zero, evarLift_evar]
      exact .exportation (.syllogism (andMonoRight (natCasesEq 0))
        (.syllogism andOrDistrib (orElim cZero (.syllogism cSucc' orIntroRight)))))
  .syllogism (.syllogism (implAnd (extraPremise zeroFunctional) implSelf) pushConjInExist)
    (existMono (implAnd s₁ s₂))

/-- Inductive step: if equality with `y` is decidable then so is equality
with `succ y` (named `w`). For a natural `x`: if `x` is `zero` then
`w =ⁱ x` is refuted by no-confusion; if `x =ⁱ succ k` then decide `y =ⁱ k`:
if so, `w =ⁱ succ y =ⁱ succ k =ⁱ x` by congruence; if not, `w =ⁱ x` would
give `succ y =ⁱ succ k`, hence `y =ⁱ k` by injectivity. -/
def decStep : Γ ⊩ᵢ succ_ ⬝ decSet ⇒ decSet :=
  -- under ∃w, ∀x (x = evar 0, w = evar 1, y = evar 2): the zero case
  let cZero : Γ ⊩ᵢ ((succ_ ⬝ .evar 2 =ⁱₘₗ .evar 1) ⊓ (succ_ ⬝ .evar 2 ⊓ decPred 2)) ⊓
      (zero_ =ⁱₘₗ .evar 0) ⇒ eqDec 1 0 :=
    .syllogism (.exportation (.syllogism
        (implAnd (.syllogism (andMono andElimRight eqI_symm) eqI_trans)
          (.syllogism andElimLeft (.syllogism andElimLeft (.syllogism andElimLeft eqI_symm))))
        (.syllogism eqI_trans (noConfusion 2))))
      orIntroRight
  -- under ∃k (k = evar 0, x = evar 1, w = evar 2, y = evar 3): the successor case,
  -- given the decision on `y =ⁱ k`
  let G := ((succ_ ⬝ .evar 3 =ⁱₘₗ .evar 2) ⊓ (succ_ ⬝ .evar 3 ⊓ decPred 3)) ⊓
      ((.evar 0 ∈ₘₗ nat_) ⊓ (succ_ ⬝ .evar 0 =ⁱₘₗ .evar 1))
  let cEq : Γ ⊩ᵢ G ⊓ (.evar 3 =ⁱₘₗ .evar 0) ⇒ (.evar 2 =ⁱₘₗ .evar 1) :=
    .syllogism
      (implAnd
        (.syllogism
          (implAnd andElimRight (.syllogism andElimLeft (.syllogism andElimLeft andElimLeft)))
          (.syllogism (eqI_congr_succ 3 0 2) eqI_symm))
        (.syllogism andElimLeft (.syllogism andElimRight andElimRight)))
      eqI_trans
  let cNe : Γ ⊩ᵢ G ⊓ ~(.evar 3 =ⁱₘₗ .evar 0) ⇒ ~(.evar 2 =ⁱₘₗ .evar 1) :=
    .exportation (.syllogism
      (implAnd (.syllogism andElimLeft andElimRight)
        (.syllogism
          (implAnd
            (.syllogism
              (implAnd
                (.syllogism andElimLeft
                  (.syllogism andElimLeft (.syllogism andElimLeft andElimLeft)))
                andElimRight)
              eqI_trans)
            (.syllogism andElimLeft
              (.syllogism andElimLeft
                (.syllogism andElimRight (.syllogism andElimRight eqI_symm)))))
          (.syllogism eqI_trans (succInjective 3 0))))
      andMp)
  let cSucc : Γ ⊩ᵢ G ⇒ eqDec 2 1 :=
    .syllogism
      (implAnd implSelf
        (.syllogism
          (implAnd (.syllogism andElimLeft (.syllogism andElimRight andElimRight))
            (.syllogism andElimRight andElimLeft))
          (.syllogism (andMonoLeft (decPred_elim 3 0)) andMp)))
      (.syllogism andOrDistrib
        (orElim (.syllogism cEq orIntroLeft) (.syllogism cNe orIntroRight)))
  -- under ∃w (w = evar 0, y = evar 1): (succ y =ⁱ w) ⊓ (succ y ⊓ decPred 1) ⇒ w ⊓ decPred 0
  let s₂ : Γ ⊩ᵢ (succ_ ⬝ .evar 1 =ⁱₘₗ .evar 0) ⊓ (succ_ ⬝ .evar 1 ⊓ decPred 1) ⇒
      .evar 0 ⊓ decPred 0 :=
    implAnd
      (.syllogism (andMonoRight andElimLeft) (.syllogism (andMonoLeft eqI_elim) andMp))
      (.forallGen (φ₁ := (succ_ ⬝ .evar 1 =ⁱₘₗ .evar 0) ⊓ (succ_ ⬝ .evar 1 ⊓ decPred 1)) (by
        rw [evarLift_conj, evarLift_conj, evarLift_eqI, evarLift_app, evarLift_succ, evarLift_evar,
          evarLift_evar, evarLift_decPred]
        exact .exportation (.syllogism (andMonoRight (natCasesEq 0))
          (.syllogism andOrDistrib (orElim cZero
            (.syllogism pushConjInExist'
              (.existGen (φ₂ := eqDec 1 0) (by
                rw [evarLift_conj, evarLift_conj, evarLift_eqI, evarLift_app, evarLift_succ,
                  evarLift_evar, evarLift_evar, evarLift_decPred, evarLift_eqDec]
                exact cSucc))))))))
  .syllogism .propagationExistRight
    (.existGen (φ₂ := decSet) (by
      rw [evarLift_decSet]
      exact .syllogism (implAnd (.framingRight andElimLeft) (decPred_out succCtx 0))
        (.syllogism (.syllogism (implAnd (extraPremise (succFunctional 0)) implSelf)
                                pushConjInExist)
          (existMono (by
            rw [evarLift_conj, evarLift_app, evarLift_succ, evarLift_evar, evarLift_decPred]
            exact s₂)))))

/-- **Equality on the naturals is decidable** (relative to predicate
propagation): `nat ⇒ ∃y. y ⊓ ∀x. x ∈ nat ⇒ (y =ⁱ x) ⊔ ¬(y =ⁱ x)`. By
induction on `y`, as in Heyting arithmetic; no excluded middle. -/
def natEqDecidableSet : Γ ⊩ᵢ nat_ ⇒ decSet := natInduction decBase decStep

/-- Decidability of equality for two naturals `n`, `m`:
`n ∈ nat ⊓ m ∈ nat ⇒ (n =ⁱ m) ⊔ ¬(n =ⁱ m)`. -/
def natEqDecidable (n m : EVarIndex) :
    Γ ⊩ᵢ (.evar n ∈ₘₗ nat_) ⊓ (.evar m ∈ₘₗ nat_) ⇒ eqDec n m :=
  -- under ∃y (y = evar 0, n ↦ n + 1, m ↦ m + 1)
  let body : Γ ⊩ᵢ ⌈.evar (n + 1) ⊓ (.evar 0 ⊓ decPred 0)⌉ ⊓ (.evar (m + 1) ∈ₘₗ nat_) ⇒
      eqDec (n + 1) (m + 1) :=
    .syllogism
      (implAnd
        (.syllogism andElimLeft
          (.syllogism (ceil_mono (andMonoRight andElimLeft)) (mem_impl_eqI (n + 1) 0)))
        (.syllogism (andMono (.syllogism (ceil_mono andAssoc') (decPred_out ceilCtx 0)) implSelf)
          (.syllogism (andMonoLeft (decPred_elim 0 (m + 1))) andMp)))
      (.syllogism andOrDistrib
        (orMono eqI_trans
          (.exportation (.syllogism
            (implAnd (.syllogism andElimLeft andElimRight)
              (.syllogism (andMono (.syllogism andElimLeft eqI_symm) implSelf) eqI_trans))
            andMp))))
  let s₀ : Γ ⊩ᵢ (.evar n ∈ₘₗ decSet) ⇒ ∃ₑ (.evar (n + 1) ∈ₘₗ (.evar 0 ⊓ decPred 0)) := by
    rw [← evarLift_evar]; exact iffMpLeft memExist
  .syllogism
    (andMonoLeft (.syllogism (ceil_mono (andMonoRight natEqDecidableSet)) s₀))
    (.syllogism pushConjInExist (.existGen (φ₂ := eqDec n m) (by
      rw [evarLift_eqDec]
      simp only [Pattern.memML, evarLift_ceil, evarLift_conj, evarLift_evar, evarLift_nat]
      exact body)))

end Decidable

end IML
