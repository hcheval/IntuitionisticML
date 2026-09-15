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
  /-- `∀x y. ∃v. add x y =ⁱ v`: addition is a total function. -/
  addFun : (∀ₑ (∀ₑ (∃ₑ (add_ ⬝ .evar 2 ⬝ .evar 1 =ⁱₘₗ .evar 0)))) ∈ Γ

variable {Γ : Set (Pattern Symbol)} [IsAddTheory Symbol Γ]

/-- `∃v. add a b =ⁱ v` (under the binder `a`, `b` are shifted). -/
def addFunctional (a b : EVarIndex) :
    Γ ⊩ᵢ ∃ₑ (add_ ⬝ .evar (a + 1) ⬝ .evar (b + 1) =ⁱₘₗ .evar 0) := by
  have h₁ : Γ ⊩ᵢ evarSubst 0 (.evar a) (∀ₑ (∃ₑ (add_ ⬝ .evar 2 ⬝ .evar 1 =ⁱₘₗ .evar 0))) :=
    .mp (forallElim (n := a)) (.assumption IsAddTheory.addFun)
  simp only [Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff,
    Pattern.add_, evarSubst, evarLift, evarLiftFrom] at h₁
  have h₂ := Proof.mp (forallElim (n := b)) h₁
  simpa [Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff,
    Pattern.add_, evarSubst, evarLift, evarLiftFrom] using h₂

/-- `⌈add a b⌉`: sums are defined. -/
def addDefined (a b : EVarIndex) : Γ ⊩ᵢ ⌈add_ ⬝ .evar a ⬝ .evar b⌉ :=
  existElim (addFunctional a b) (ψ := ⌈add_ ⬝ .evar a ⬝ .evar b⌉) (by
    rw [evarLift_ceil, evarLift_app, evarLift_app, evarLift_add, evarLift_evar, evarLift_evar]
    exact .syllogism eqI_symm
      (implMp (.exportation (eqI_leibniz_in ceilCtx .hole (φ := .evar 0)
          (ψ := add_ ⬝ .evar (a + 1) ⬝ .evar (b + 1))))
        (extraPremise ceil_of_evar)))

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

-- ─────────────────────────────────────────────────────────────
-- Associativity, relative to predicate propagation
-- ─────────────────────────────────────────────────────────────

/-!
## Associativity and the predicate-propagation principle

"`(a + b) + n = a + (b + n)` for every natural `n`" is, for a total `add`,
the statement that the two sums *overlap*: `⌈(a+b)+n ⊓ a+(b+n)⌉`. The
induction predicate is therefore `∃n. n ⊓ ⌈lsum n ⊓ rsum n⌉`, and the
successor step has to replace `succ n` by its name `w` in *both* holes of
`⌈lsum □ ⊓ rsum □⌉`. Leibniz's law `eqI_leibniz` covers holes of the shape
`Q[A[P[□]]]` (application-free above an application context above
application-free); here the hole is `⌈□ ⊓ □⌉` with application contexts
*inside* the `⊓`, i.e. two application layers separated by `⊓`. To rewrite
there, the equality `succ n =ⁱ w` must enter the outer context `⌈·⌉` *as an
equality* (not merely as the pointwise `succ n ⟺ w`, which is what
`totalI_ctx` gives). That is the principle

    ⌊θ⌋ⁱ ⇒ ⌊⌊θ⌋ⁱ⌋ⁱ      "positive totality is a predicate pattern"

(`IML.IsPred`), sound in every Heyting model (`⌊θ⌋ⁱ` has the same value at
every point) but not derived from the rules of iML. The class `HasPredProp`
assumes it, together with its `⌈·⌉` counterpart, as an axiom scheme in `Γ`;
associativity is proved relative to it. Everything else in the proof is the
same machinery as `addZeroLeft`.
-/

/-- The predicate-propagation axiom schemes: definedness patterns and positive
totalities are predicate patterns, `θ ⇒ ⌊θ⌋ⁱ`. Sound in every `HModel` with
definedness; whether they are derivable in iML is open. -/
class HasPredProp (Symbol : Type) [HasCeil Symbol] (Γ : Set (Pattern Symbol)) : Prop where
  ceilPred : ∀ φ : Pattern Symbol, (⌈φ⌉ ⇒ ⌊⌈φ⌉⌋ⁱ) ∈ Γ
  totalPred : ∀ φ : Pattern Symbol, (⌊φ⌋ⁱ ⇒ ⌊⌊φ⌋ⁱ⌋ⁱ) ∈ Γ

section Assoc

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

/-- `(a + b) + x`. -/
def lsum (a b x : Pattern Symbol) : Pattern Symbol := add_ ⬝ (add_ ⬝ a ⬝ b) ⬝ x

/-- `a + (b + x)`. -/
def rsum (a b x : Pattern Symbol) : Pattern Symbol := add_ ⬝ a ⬝ (add_ ⬝ b ⬝ x)

/-- The context `add ⬝ (add ⬝ a ⬝ b) ⬝ □`. -/
def lsumCtx (a b : Pattern Symbol) : AppCtx Symbol := .right (add_ ⬝ (add_ ⬝ a ⬝ b)) .hole

/-- The context `add ⬝ a ⬝ (add ⬝ b ⬝ □)`. -/
def rsumCtx (a b : Pattern Symbol) : AppCtx Symbol := .right (add_ ⬝ a) (.right (add_ ⬝ b) .hole)

omit [HasCeil Symbol] [HasNatOps Symbol] in
theorem lsumCtx_fill (a b x : Pattern Symbol) : (lsumCtx a b).fill x = lsum a b x := rfl

omit [HasCeil Symbol] [HasNatOps Symbol] in
theorem rsumCtx_fill (a b x : Pattern Symbol) : (rsumCtx a b).fill x = rsum a b x := rfl

/-- The induction predicate `{n | (a+b)+n and a+(b+n) overlap}` for the
element variables `a`, `b`; under the binder their indices shift by one. -/
def assocPred (a b : EVarIndex) : Pattern Symbol :=
  ∃ₑ (.evar 0 ⊓ ⌈lsum (.evar (a + 1)) (.evar (b + 1)) (.evar 0) ⊓
                 rsum (.evar (a + 1)) (.evar (b + 1)) (.evar 0)⌉)

omit [HasCeil Symbol] [HasNatOps Symbol] in
theorem evarLift_lsum (a b x : Pattern Symbol) :
    evarLift (lsum a b x) = lsum (evarLift a) (evarLift b) (evarLift x) := rfl

omit [HasCeil Symbol] [HasNatOps Symbol] in
theorem evarLift_rsum (a b x : Pattern Symbol) :
    evarLift (rsum a b x) = rsum (evarLift a) (evarLift b) (evarLift x) := rfl

omit [HasNatOps Symbol] in
theorem evarLift_assocPred (a b : EVarIndex) :
    evarLift (assocPred a b : Pattern Symbol) = assocPred (a + 1) (b + 1) := by
  simp [assocPred, lsum, rsum, Pattern.ceil, Pattern.add_, evarLift, evarLiftFrom]

/-- `succ ((a+b)+n) ⇒ (a+b)+succ n`: the second axiom at `x := a + b`, after
naming `a + b`. -/
def succLsum (a b n : EVarIndex) :
    Γ ⊩ᵢ succ_ ⬝ lsum (.evar a) (.evar b) (.evar n) ⇒ lsum (.evar a) (.evar b) (succ_ ⬝ .evar n) :=
  .syllogism (.syllogism (implAnd (extraPremise (addFunctional a b)) implSelf) pushConjInExist)
    (.existGen (φ₂ := lsum (.evar a) (.evar b) (succ_ ⬝ .evar n)) (by
      simp only [lsum, evarLift_app, evarLift_add, evarLift_succ, evarLift_evar]
      exact .syllogism
        (implAnd andElimLeft (eqI_elim_ctx (.right succ_ (addLeftCtx (.evar (n + 1))))))
        (.syllogism (andMonoRight (.mp eqI_elim (.mp eqI_symm (addSuccRight 0 (n + 1)))))
          (.syllogism (andMonoLeft eqI_symm)
            (eqI_elim_ctx (addLeftCtx (succ_ ⬝ .evar (n + 1))))))))

/-- `succ (a+(b+n)) ⇒ a+(b+succ n)`: the second axiom at `y := b + n`, after
naming `b + n`, then again at `(b, n)`. -/
def succRsum (a b n : EVarIndex) :
    Γ ⊩ᵢ succ_ ⬝ rsum (.evar a) (.evar b) (.evar n) ⇒ rsum (.evar a) (.evar b) (succ_ ⬝ .evar n) :=
  .syllogism (.syllogism (implAnd (extraPremise (addFunctional b n)) implSelf) pushConjInExist)
    (.existGen (φ₂ := rsum (.evar a) (.evar b) (succ_ ⬝ .evar n)) (by
      simp only [rsum, evarLift_app, evarLift_add, evarLift_succ, evarLift_evar]
      exact .syllogism
        (implAnd andElimLeft (eqI_elim_ctx (.right succ_ (addRightCtx (.evar (a + 1))))))
        (.syllogism (andMonoRight (.mp eqI_elim (.mp eqI_symm (addSuccRight (a + 1) 0))))
          (.syllogism (andMonoLeft eqI_symm)
            (.syllogism (eqI_elim_ctx (.right (add_ ⬝ .evar (a + 1)) (.right succ_ .hole)))
              (.framingRight (.mp eqI_elim (.mp eqI_symm (addSuccRight (b + 1) (n + 1))))))))))

/-- Base case, the overlap at `zero`: `⌈(a+b)+0 ⊓ a+(b+0)⌉`. Both sides
contain `a + b`, which is defined. -/
def assocBaseCeil (a b : EVarIndex) :
    Γ ⊩ᵢ ⌈lsum (.evar a) (.evar b) zero_ ⊓ rsum (.evar a) (.evar b) zero_⌉ :=
  -- ⌈a+b⌉ ⇒ ⌈a+b ⊓ a+(b+0)⌉
  let s₁ : Γ ⊩ᵢ ⌈add_ ⬝ .evar a ⬝ .evar b⌉ ⇒
      ⌈add_ ⬝ .evar a ⬝ .evar b ⊓ rsum (.evar a) (.evar b) zero_⌉ :=
    ceil_mono (implAnd implSelf (.framingRight (evar_impl_addZero b)))
  -- naming a+b as u: ⌈a+b ⊓ Y⌉ ⇒ ⌈u ⊓ Y⌉ ⇒ ⌈u+0 ⊓ Y⌉ ⇒ ⌈(a+b)+0 ⊓ Y⌉
  let s₂ : Γ ⊩ᵢ ⌈add_ ⬝ .evar a ⬝ .evar b ⊓ rsum (.evar a) (.evar b) zero_⌉ ⇒
      ⌈lsum (.evar a) (.evar b) zero_ ⊓ rsum (.evar a) (.evar b) zero_⌉ :=
    .syllogism (.syllogism (implAnd (extraPremise (addFunctional a b)) implSelf) pushConjInExist)
      (.existGen (φ₂ := ⌈lsum (.evar a) (.evar b) zero_ ⊓ rsum (.evar a) (.evar b) zero_⌉) (by
        simp only [lsum, rsum, evarLift_ceil, evarLift_conj, evarLift_app, evarLift_add,
          evarLift_zero, evarLift_evar]
        exact .syllogism
          (implAnd andElimLeft
            (.syllogism (eqI_leibniz_in ceilCtx (.conjL .hole _))
              (ceil_mono (andMonoLeft (evar_impl_addZero 0)))))
          (.syllogism (andMonoLeft eqI_symm)
            (eqI_leibniz_ceil (.conjL .hole _) (addLeftCtx zero_)))))
  .mp (.syllogism s₁ s₂) (addDefined a b)

/-- Base case: `zero ⇒ assocPred a b`. Name `zero` as `v` and move the
overlap from `zero` to `v` in both holes. -/
def assocBase (a b : EVarIndex) : Γ ⊩ᵢ zero_ ⇒ assocPred a b :=
  .syllogism (.syllogism (implAnd (extraPremise zeroFunctional) implSelf) pushConjInExist)
    (existMono (implAnd (.syllogism (andMonoLeft eqI_elim) andMp)
      (.syllogism (implAnd andElimLeft (extraPremise (assocBaseCeil (a + 1) (b + 1))))
        (eqI_leibniz_ceil₂ (lsumCtx _ _) (rsumCtx _ _)))))

/-- Inductive step on the overlap: if `(a+b)+n` and `a+(b+n)` share an
element `c`, then `succ c` is in both `(a+b)+succ n` and `a+(b+succ n)`. -/
def assocStepCeil (a b n : EVarIndex) :
    Γ ⊩ᵢ ⌈lsum (.evar a) (.evar b) (.evar n) ⊓ rsum (.evar a) (.evar b) (.evar n)⌉ ⇒
      ⌈lsum (.evar a) (.evar b) (succ_ ⬝ .evar n) ⊓ rsum (.evar a) (.evar b) (succ_ ⬝ .evar n)⌉ :=
  .syllogism (ceil_mono (.syllogism (implAnd (extraPremise .existence) implSelf) pushConjInExist))
    (.syllogism (ctxPropagationExist ceilCtx)
      (.existGen (φ₂ := ⌈lsum (.evar a) (.evar b) (succ_ ⬝ .evar n) ⊓
                          rsum (.evar a) (.evar b) (succ_ ⬝ .evar n)⌉) (by
        simp only [lsum, rsum, evarLift_ceil, evarLift_conj, evarLift_app, evarLift_add,
          evarLift_succ, evarLift_evar]
        exact .syllogism (implAnd implSelf (extraPremise (succDefined 0)))
          (.syllogism (.singletonAlt (C₁ := ceilCtx) (C₂ := .right (.symbol HasCeil.ceil) succCtx)
              (n := 0) (φ := _))
            (ceil_mono (.syllogism (.framingRight andElimRight)
              (.syllogism (ctxAnd succCtx)
                (andMono (succLsum (a + 1) (b + 1) (n + 1)) (succRsum (a + 1) (b + 1) (n + 1))))))))))

/-- Inductive step: `succ ⬝ assocPred a b ⇒ assocPred a b`. Name `succ n` as
`w` and move the overlap from `succ n` to `w` in both holes. -/
def assocStep (a b : EVarIndex) : Γ ⊩ᵢ succ_ ⬝ assocPred a b ⇒ assocPred a b :=
  -- under ∃w (w = evar 0, n = evar 1, a ↦ a + 2, b ↦ b + 2)
  let s₂ : Γ ⊩ᵢ (succ_ ⬝ .evar 1 =ⁱₘₗ .evar 0) ⊓
      (succ_ ⬝ .evar 1 ⊓ ⌈lsum (.evar (a + 2)) (.evar (b + 2)) (succ_ ⬝ .evar 1) ⊓
                          rsum (.evar (a + 2)) (.evar (b + 2)) (succ_ ⬝ .evar 1)⌉) ⇒
      .evar 0 ⊓ ⌈lsum (.evar (a + 2)) (.evar (b + 2)) (.evar 0) ⊓
                 rsum (.evar (a + 2)) (.evar (b + 2)) (.evar 0)⌉ :=
    implAnd
      (.syllogism (andMonoRight andElimLeft) (.syllogism (andMonoLeft eqI_elim) andMp))
      (.syllogism (andMonoRight andElimRight) (eqI_leibniz_ceil₂ (lsumCtx _ _) (rsumCtx _ _)))
  .syllogism .propagationExistRight
    (.existGen (φ₂ := assocPred a b) (by
      rw [evarLift_assocPred]
      exact .syllogism (ctx_mem_elim succCtx)
        (.syllogism (andMonoRight (assocStepCeil (a + 1) (b + 1) 0))
          (.syllogism (.syllogism (implAnd (extraPremise (succFunctional 0)) implSelf)
                                  pushConjInExist)
            (existMono (by
              simp only [lsum, rsum, evarLift_conj, evarLift_ceil, evarLift_app, evarLift_add,
                evarLift_succ, evarLift_evar]
              exact s₂))))))

/-- **Associativity** (relative to predicate propagation): for every natural
`n`, `(a+b)+n` and `a+(b+n)` overlap, i.e. `nat ⇒ ∃n. n ⊓ ⌈(a+b)+n ⊓ a+(b+n)⌉`.
By induction on `n`. -/
def addAssoc (a b : EVarIndex) : Γ ⊩ᵢ nat_ ⇒ assocPred a b :=
  natInduction (assocBase a b) (assocStep a b)

/-- Associativity, pointwise: `x ⊓ nat ⇒ ⌈(a+b)+x ⊓ a+(b+x)⌉`. From
`addAssoc`: the current element is some `n`, so `x ∈ n`, hence `x =ⁱ n`
(Lemma 3.9, from the `⌈·⌉` scheme), and `n` is replaced by `x` in both holes. -/
def addAssocAt (a b n : EVarIndex) :
    Γ ⊩ᵢ .evar n ⊓ nat_ ⇒ ⌈lsum (.evar a) (.evar b) (.evar n) ⊓ rsum (.evar a) (.evar b) (.evar n)⌉ :=
  .syllogism (andMonoRight (addAssoc a b))
    (.syllogism pushConjInExist' (.existGen
      (φ₂ := ⌈lsum (.evar a) (.evar b) (.evar n) ⊓ rsum (.evar a) (.evar b) (.evar n)⌉) (by
      simp only [lsum, rsum, evarLift_ceil, evarLift_conj, evarLift_app, evarLift_add, evarLift_evar]
      exact .syllogism
        (implAnd (.syllogism (implAnd (.syllogism andElimRight andElimLeft) andElimLeft)
                    (.syllogism evar_and_impl_ceil (mem_impl_eqI 0 (n + 1))))
                 (.syllogism andElimRight andElimRight))
        (eqI_leibniz_ceil₂ (lsumCtx _ _) (rsumCtx _ _)))))

end Assoc

end IML
