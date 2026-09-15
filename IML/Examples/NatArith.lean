import IML.Theories.Nat

/-!
# Arithmetic on the naturals, proved inside iML

The theory of `IML.Theories.Nat` extended with a symbol `add` and its two
defining equations

    ∀x.   add x zero     =ⁱ x
    ∀x y. add x (succ y) =ⁱ succ (add x y)

(recursion on the second argument, as in the classical example
`MatchingLogic/Examples/NatArith.lean`). Then some arithmetic is derived in
the logic by the induction principle `natInduction`:

* `addZeroRight` — `n + 0 = n`, an instance of the first axiom;
* `addZeroLeft` — `0 + n = n` for every natural `n`, **by induction on `n`**.
  This is the theorem the classical file leaves as a `sorry`.

## How the statements are phrased, and why

Patterns denote sets, so "`0 + n = n` for every natural `n`" is the set
inclusion `nat ⇒ ∃n. n ⊓ add zero n` ("every natural `n` is an element of
`0 + n`"), or pointwise `x ⊓ nat ⇒ add zero x` ("if the current element is
the natural `x`, it lies in `0 + x`"). For a total function `add` this is
the same as `add zero x =ⁱ x`.

The induction predicate `P := ∃n. n ⊓ add zero n` is chosen so that the
hypothesis "`n ∈ 0 + n`" reaches the successor step as an *element in an
application context*, which the SINGLETON rule can transport. The
alternative predicate `∃n. n ⊓ (add zero n =ⁱ n)` carries the hypothesis as
an *equality*; using it in the step would require the internal congruence
`(φ =ⁱ ψ) ⇒ (succ φ =ⁱ succ ψ)`, which in iML needs positive totality to
be a predicate pattern (`⌊θ⌋ⁱ ⇒ ⌊⌊θ⌋ⁱ⌋ⁱ`, `IML.IsPred`): sound but not
derived. Where the axioms are instantiated at the term `zero` rather than at
a variable, the term is first named through functionality (`∃v. zero =ⁱ v`)
and the variable is replaced by Leibniz's law in application contexts
(`eqI_elim_ctx`). None of this uses excluded middle.

Associativity, which needs the two-hole predicate `⌈(a+b)+n ⊓ a+(b+n)⌉` and
hence the congruence above, is discussed at the end of the file.
-/

namespace IML

open Pattern

variable {Symbol : Type} [HasCeil Symbol] [HasNatOps Symbol]

-- ─────────────────────────────────────────────────────────────
-- The addition symbol and its axioms
-- ─────────────────────────────────────────────────────────────

class HasAddOps (Symbol : Type) where
  add : Symbol

variable [HasAddOps Symbol]

/-- The pattern `add`; `add ⬝ φ ⬝ ψ` matches the sums of an element of `φ`
and an element of `ψ`. -/
def Pattern.add_ : Pattern Symbol := .symbol HasAddOps.add

omit [HasCeil Symbol] [HasNatOps Symbol] in
theorem evarLift_add : evarLift (add_ : Pattern Symbol) = add_ := rfl

omit [HasCeil Symbol] [HasNatOps Symbol] [HasAddOps Symbol] in
theorem evarLift_app (φ ψ : Pattern Symbol) : evarLift (φ ⬝ ψ) = evarLift φ ⬝ evarLift ψ := rfl

/-- `Γ` contains the naturals together with the recursive equations of `add`. -/
class IsAddTheory (Symbol : Type) [HasCeil Symbol] [HasNatOps Symbol] [HasAddOps Symbol]
    (Γ : Set (Pattern Symbol)) : Prop extends IsNatTheory Symbol Γ where
  /-- `∀x. add x zero =ⁱ x`. -/
  addZero : (∀ₑ (add_ ⬝ .evar 0 ⬝ zero_ =ⁱₘₗ .evar 0)) ∈ Γ
  /-- `∀x y. add x (succ y) =ⁱ succ (add x y)`. -/
  addSucc : (∀ₑ (∀ₑ (add_ ⬝ .evar 1 ⬝ (succ_ ⬝ .evar 0) =ⁱₘₗ
    succ_ ⬝ (add_ ⬝ .evar 1 ⬝ .evar 0)))) ∈ Γ

variable {Γ : Set (Pattern Symbol)} [IsAddTheory Symbol Γ]

/-- **Zero is a right unit**: `n + 0 =ⁱ n`. An instance of the first axiom. -/
def addZeroRight (n : EVarIndex) : Γ ⊩ᵢ add_ ⬝ .evar n ⬝ zero_ =ⁱₘₗ .evar n := by
  have h : Γ ⊩ᵢ evarSubst 0 (.evar n) (add_ ⬝ .evar 0 ⬝ zero_ =ⁱₘₗ .evar 0) :=
    .mp (forallElim (n := n)) (.assumption IsAddTheory.addZero)
  simpa [Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff, Pattern.zero_,
    Pattern.add_, evarSubst, evarLift, evarLiftFrom] using h

/-- `n + succ m =ⁱ succ (n + m)`. An instance of the second axiom. -/
def addSuccRight (n m : EVarIndex) :
    Γ ⊩ᵢ add_ ⬝ .evar n ⬝ (succ_ ⬝ .evar m) =ⁱₘₗ succ_ ⬝ (add_ ⬝ .evar n ⬝ .evar m) := by
  have h₁ : Γ ⊩ᵢ evarSubst 0 (.evar n) (∀ₑ (add_ ⬝ .evar 1 ⬝ (succ_ ⬝ .evar 0) =ⁱₘₗ
      succ_ ⬝ (add_ ⬝ .evar 1 ⬝ .evar 0))) :=
    .mp (forallElim (n := n)) (.assumption IsAddTheory.addSucc)
  simp only [Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff,
    Pattern.succ_, Pattern.add_, evarSubst, evarLift, evarLiftFrom] at h₁
  have h₂ := Proof.mp (forallElim (n := m)) h₁
  simpa [Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff,
    Pattern.succ_, Pattern.add_, evarSubst, evarLift, evarLiftFrom] using h₂

/-- `n ⇒ n + 0`: every element lies in its own sum with zero. -/
def evar_impl_addZero (n : EVarIndex) : Γ ⊩ᵢ .evar n ⇒ add_ ⬝ .evar n ⬝ zero_ :=
  .mp eqI_elim (.mp eqI_symm (addZeroRight n))

/-- Zero is a right unit, set form: `nat ⇒ ∃n. n ⊓ (n + 0)`. No induction is
needed, the axiom already speaks about every element. -/
def addZeroRightSet : Γ ⊩ᵢ nat_ ⇒ ∃ₑ (.evar 0 ⊓ add_ ⬝ .evar 0 ⬝ zero_) :=
  .syllogism natElem (existMono (implAnd andElimLeft (.syllogism andElimLeft (evar_impl_addZero 0))))

-- ─────────────────────────────────────────────────────────────
-- Zero is a left unit, by induction
-- ─────────────────────────────────────────────────────────────

/-- The context `add ⬝ □ ⬝ ψ`. -/
def addLeftCtx (ψ : Pattern Symbol) : AppCtx Symbol := .left (.right add_ .hole) ψ

/-- The context `add ⬝ φ ⬝ □`. -/
def addRightCtx (φ : Pattern Symbol) : AppCtx Symbol := .right (add_ ⬝ φ) .hole

/-- The induction predicate `{n | n ∈ 0 + n}`, as the pattern `∃n. n ⊓ add zero n`. -/
def leftUnitPred : Pattern Symbol := ∃ₑ (.evar 0 ⊓ add_ ⬝ zero_ ⬝ .evar 0)

/-- Base case: `zero ∈ 0 + 0`. Name `zero` as `v` (`∃v. zero =ⁱ v`); then
`v ∈ v + 0` by the first axiom, and both `v`s are replaced by `zero` using
Leibniz's law in the contexts `add ⬝ □ ⬝ zero` and `add ⬝ zero ⬝ □`. -/
def leftUnitBase : Γ ⊩ᵢ zero_ ⇒ leftUnitPred :=
  -- (zero =ⁱ v) ⊓ zero ⇒ v
  let s₁ : Γ ⊩ᵢ (zero_ =ⁱₘₗ .evar 0) ⊓ zero_ ⇒ .evar 0 :=
    .syllogism (andMonoLeft eqI_elim) andMp
  -- (zero =ⁱ v) ⊓ zero ⇒ add zero v
  let s₂ : Γ ⊩ᵢ (zero_ =ⁱₘₗ .evar 0) ⊓ zero_ ⇒ add_ ⬝ zero_ ⬝ .evar 0 :=
    .syllogism (implAnd andElimLeft (.syllogism s₁ (evar_impl_addZero 0)))
      (.syllogism (implAnd andElimLeft
          (.syllogism (andMonoLeft eqI_symm) (eqI_elim_ctx (addLeftCtx zero_))))
        (eqI_elim_ctx (addRightCtx zero_)))
  .syllogism (.syllogism (implAnd (extraPremise zeroFunctional) implSelf) pushConjInExist)
    (existMono (implAnd s₁ s₂))

/-- `succ (0 + n) ⇒ 0 + succ n`: the second axiom at `x := zero`. Since the
axiom is instantiated at variables, `zero` is first named as `v`, the axiom
is used at `v`, and `v` is replaced by `zero` on both sides. -/
def succAddZero : Γ ⊩ᵢ succ_ ⬝ (add_ ⬝ zero_ ⬝ .evar 0) ⇒ add_ ⬝ zero_ ⬝ (succ_ ⬝ .evar 0) :=
  -- under ∃v (v = evar 0, n = evar 1):
  -- (zero =ⁱ v) ⊓ succ (add zero n) ⇒ (zero =ⁱ v) ⊓ succ (add v n)
  --                                ⇒ (zero =ⁱ v) ⊓ add v (succ n) ⇒ add zero (succ n)
  let inner : Γ ⊩ᵢ (zero_ =ⁱₘₗ .evar 0) ⊓ succ_ ⬝ (add_ ⬝ zero_ ⬝ .evar 1) ⇒
      add_ ⬝ zero_ ⬝ (succ_ ⬝ .evar 1) :=
    .syllogism (implAnd andElimLeft (eqI_elim_ctx (.right succ_ (addLeftCtx (.evar 1)))))
      (.syllogism (andMonoRight (.mp eqI_elim (.mp eqI_symm (addSuccRight 0 1))))
        (.syllogism (andMonoLeft eqI_symm) (eqI_elim_ctx (addLeftCtx (succ_ ⬝ .evar 1)))))
  .syllogism (.syllogism (implAnd (extraPremise zeroFunctional) implSelf) pushConjInExist)
    (.existGen (φ₂ := add_ ⬝ zero_ ⬝ (succ_ ⬝ .evar 0)) inner)

/-- Inductive step: if `n ∈ 0 + n` then `succ n ∈ 0 + succ n`. Name `succ n`
as `w` (`∃w. succ n =ⁱ w`); then `w ∈ 0 + succ n` by the hypothesis, the
axiom and framing, and `succ n` is replaced by `w` in `add ⬝ zero ⬝ □`. -/
def leftUnitStep : Γ ⊩ᵢ succ_ ⬝ leftUnitPred ⇒ leftUnitPred :=
  -- succ (n ⊓ add zero n) ⇒ succ n ⊓ add zero (succ n)
  let s₁ : Γ ⊩ᵢ succ_ ⬝ (.evar 0 ⊓ add_ ⬝ zero_ ⬝ .evar 0) ⇒
      succ_ ⬝ .evar 0 ⊓ add_ ⬝ zero_ ⬝ (succ_ ⬝ .evar 0) :=
    implAnd (.framingRight andElimLeft) (.syllogism (.framingRight andElimRight) succAddZero)
  -- under ∃w (w = evar 0, n = evar 1):
  -- (succ n =ⁱ w) ⊓ (succ n ⊓ add zero (succ n)) ⇒ w ⊓ add zero w
  let s₂ : Γ ⊩ᵢ (succ_ ⬝ .evar 1 =ⁱₘₗ .evar 0) ⊓
      (succ_ ⬝ .evar 1 ⊓ add_ ⬝ zero_ ⬝ (succ_ ⬝ .evar 1)) ⇒
      .evar 0 ⊓ add_ ⬝ zero_ ⬝ .evar 0 :=
    implAnd
      (.syllogism (andMonoRight andElimLeft) (.syllogism (andMonoLeft eqI_elim) andMp))
      (.syllogism (andMonoRight andElimRight) (eqI_elim_ctx (addRightCtx zero_)))
  .syllogism .propagationExistRight
    (.existGen (φ₂ := leftUnitPred)
      (.syllogism s₁
        (.syllogism (.syllogism (implAnd (extraPremise (succFunctional 0)) implSelf)
                                pushConjInExist)
          (existMono s₂))))

/-- **Zero is a left unit**: every natural `n` lies in `0 + n`, i.e.
`nat ⇒ ∃n. n ⊓ add zero n`. By induction (`natInduction`) with the predicate
`{n | n ∈ 0 + n}`. This is the intuitionistic analogue of the classical
`addZeroLeft`, sorry-free. -/
def addZeroLeft : Γ ⊩ᵢ nat_ ⇒ leftUnitPred := natInduction leftUnitBase leftUnitStep

/-- Zero is a left unit, pointwise: `x ⊓ nat ⇒ add zero x` — if the current
element is the natural `x` then it lies in `0 + x`. From `addZeroLeft`: the
current element is some `n` with `n ∈ 0 + n`, and `x` replaces `n` in
`add ⬝ zero ⬝ □` by SINGLETON. -/
def addZeroLeftAt (n : EVarIndex) : Γ ⊩ᵢ .evar n ⊓ nat_ ⇒ add_ ⬝ zero_ ⬝ .evar n :=
  .syllogism (andMonoRight addZeroLeft)
    (.syllogism pushConjInExist' (.existGen (φ₂ := add_ ⬝ zero_ ⬝ .evar n) (by
      rw [evarLift_app, evarLift_app, evarLift_add, evarLift_zero, evarLift_evar]
      exact .syllogism
        (implAnd (implAnd (.syllogism andElimRight andElimLeft) andElimLeft)
                 (.syllogism andElimRight andElimRight))
        (.syllogism (.singletonAlt (C₁ := .hole) (C₂ := addRightCtx zero_) (n := 0)
                      (φ := .evar (n + 1)))
          (.framingRight andElimRight)))))

/-- Zero is a left unit, universally closed: `∀x. x ⊓ nat ⇒ add zero x`. -/
def addZeroLeftAll : Γ ⊩ᵢ ∀ₑ (.evar 0 ⊓ nat_ ⇒ add_ ⬝ zero_ ⬝ .evar 0) :=
  .mp (.forallGen (φ₁ := ⊤ₘ) (extraPremise (addZeroLeftAt 0))) topIntro

end IML
