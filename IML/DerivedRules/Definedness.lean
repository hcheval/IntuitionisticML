import IML.DerivedRules.Context

/-!
# Definedness, membership and totality in iML (thesis §3.2)

`⌈φ⌉ := ceil ⬝ φ` with the axiom `∀x. ⌈x⌉`. The classical development
derives the whole membership calculus of the system P from this. Which of
it survives intuitionistically?

The proof system's SINGLETON rule is the positive
`singletonStrong : C₁[x ⊓ φ] ⊓ C₂[x ⊓ ψ] ⇒ C₂[x ⊓ (φ ⊓ ψ)]`
(`IML/Proof.lean`): information about an element variable can be
*transported* between contexts. This is what the membership calculus needs;
every classical proof of the results below routes instead through the
*membership excluded middle* `⌈x⌉ ⇒ ⌈x ⊓ φ⌉ ⊔ ⌈x ⊓ ~φ⌉`, which is unsound
in the Heyting semantics (`IML.PointModel.memEM_not_derivable`). With the
negative rule alone (the published system, `IML.Crisp.Proof`) the items
marked (†) are underivable (`IML.TopFilter.phi_impl_ceil_not_derivable`);
they used to be stated here under a hypothesis `SingletonPos`, which is now
the rule.

* Derivable: definedness of variables, `⌈·⌉` monotone, `⌈⊥⌉ ⇒ ⊥`,
  `⌈φ ⊔ ψ⌉ ⟺ ⌈φ⌉ ⊔ ⌈ψ⌉`, `⌈∃x.φ⌉ ⟺ ∃x.⌈φ⌉`, membership introduction,
  Membership∨, Membership∃, Membership∧ in both directions (†),
  Membership⇒ (†), one half of Membership¬, membership *elimination*
  `⌈x ⊓ φ⌉ ⇒ x ⇒ φ` (†), Lemma 3.8 `⌊φ⌋ⁱ ⇒ φ` for the positive totality
  `⌊φ⌋ⁱ := ∀x. x ∈ φ` (†), Lemma 3.14 `C[φ] ⇒ ⌈φ⌉` and Corollary 3.1
  `φ ⇒ ⌈φ⌉` (†), Lemma 3.19 `φ ⟺ ∃y. (⌈y ⊓ φ⌉ ⊓ y)` in both directions (†),
  equality introduction/reflexivity/symmetry, and `⌊φ⌋ⁱ ⇒ ⌊φ⌋`.

* Weakened: for the classical totality `⌊φ⌋ := ~⌈~φ⌉` only `⌊φ⌋ ⇒ ~~φ`
  (Corollary 3.1 gives `⌊φ⌋ ⇒ φ` classically, by DNE).

* Positive equality `φ =ⁱ ψ := ⌊φ ⟺ ψ⌋ⁱ`: reflexive, symmetric, transitive
  (`eqI_trans`), implies the classical `⌊φ ⟺ ψ⌋`, and satisfies Leibniz's law
  `(φ =ⁱ ψ) ⊓ C[φ] ⇒ C[ψ]` for every hole of the shape `Q[A[P[□]]]`
  (`eqI_leibniz`: application-free `Q`, application context `A`,
  application-free `P`, binders and both sides of `⇒` allowed in `Q` and
  `P`); in particular `x =ⁱ φ ⇒ x ∈ φ` (Lemma 3.9(←)). Semantically it is the
  Ω-set equality `E` (`IML/DerivedRules/EqualitySemantics.lean`).

* Open: Membership¬(←) `~(x ∈ φ) ⇒ x ∈ ~φ`, Membership⇒(←), Lemma 3.9(→)
  `x ∈ y ⇒ x =ⁱ y`, Lemma 3.17(←), and Leibniz under `μ`/`ν` or through an
  application below a connective below an application. All are sound, and
  all follow from one principle: that `⌈·⌉`-patterns (and their negations and
  implications) are *predicate patterns* `θ ⇒ ⌊θ⌋ⁱ` (`IsPred`,
  `memNegIntro_of_pred`, `memImplIntro_of_pred`, `mem_impl_eqI_of_pred`,
  `ctx_mem_intro_of_pred`). Whether `⌈φ⌉ ⇒ ⌊⌈φ⌉⌋ⁱ` is derivable is not
  settled; the top-filter refutation of Membership¬(←)
  (`IML.TopFilter.memNegIntro_not_derivable`) concerns the published system
  only.
-/

namespace IML

open Pattern

class HasCeil (Symbol : Type) where
  ceil : Symbol

variable {Symbol : Type} [HasCeil Symbol]

def Pattern.ceil (φ : Pattern Symbol) : Pattern Symbol := .symbol HasCeil.ceil ⬝ φ

/-- Classical totality `⌊φ⌋ := ~⌈~φ⌉`. -/
def Pattern.total (φ : Pattern Symbol) : Pattern Symbol := ~(Pattern.ceil (~φ))

/-- Membership `x ∈ φ := ⌈x ⊓ φ⌉`. -/
def Pattern.memML (x φ : Pattern Symbol) : Pattern Symbol := Pattern.ceil (x ⊓ φ)

/-- Positive (intuitionistic) totality `⌊φ⌋ⁱ := ∀x. x ∈ φ`. -/
def Pattern.totalI (φ : Pattern Symbol) : Pattern Symbol :=
  ∀ₑ (Pattern.memML (.evar 0) (evarLift φ))

def Pattern.eqML (φ ψ : Pattern Symbol) : Pattern Symbol := Pattern.total (φ ⟺ ψ)

scoped notation "⌈" φ "⌉" => Pattern.ceil φ
scoped notation "⌊" φ "⌋" => Pattern.total φ
scoped notation "⌊" φ "⌋ⁱ" => Pattern.totalI φ
scoped infixl:50 " ∈ₘₗ " => Pattern.memML
scoped infixl:50 " =ₘₗ " => Pattern.eqML

/-- The definedness context `⌈□⌉`. -/
def ceilCtx : AppCtx Symbol := .right (.symbol HasCeil.ceil) .hole

theorem ceilCtx_fill (φ : Pattern Symbol) : (ceilCtx (Symbol := Symbol)).fill φ = ⌈φ⌉ := rfl

theorem ceilCtx_liftEVar : (ceilCtx (Symbol := Symbol)).liftEVar = ceilCtx := rfl

theorem evarLift_ceil (φ : Pattern Symbol) : evarLift ⌈φ⌉ = ⌈evarLift φ⌉ := rfl

class IsDefinedness (Symbol : Type) [HasCeil Symbol] (Γ : Set (Pattern Symbol)) : Prop where
  defAxiom : ∀ₑ ⌈.evar 0⌉ ∈ Γ

variable {Γ : Set (Pattern Symbol)} [IsDefinedness Symbol Γ] {φ ψ x : Pattern Symbol}

-- ─────────────────────────────────────────────────────────────
-- Basic facts
-- ─────────────────────────────────────────────────────────────

def defProof : Γ ⊩ᵢ ∀ₑ ⌈.evar 0⌉ := .assumption IsDefinedness.defAxiom

theorem evarSubst_ceil_evar (n : EVarIndex) :
    evarSubst 0 (.evar n) (⌈.evar 0⌉ : Pattern Symbol) = ⌈.evar n⌉ := by
  simp [Pattern.ceil, evarSubst]

def ceil_of_evar {n : EVarIndex} : Γ ⊩ᵢ ⌈.evar n⌉ := by
  have h : Γ ⊩ᵢ evarSubst 0 (.evar n) ⌈.evar 0⌉ := .mp (forallElim (n := n)) defProof
  rwa [evarSubst_ceil_evar] at h

def ceil_mono (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ ⌈φ⌉ ⇒ ⌈ψ⌉ := .framingRight h

def ceil_bot : Γ ⊩ᵢ ⌈⊥ₘ⌉ ⇒ ⊥ₘ := ctxBot ceilCtx

def ceil_or : Γ ⊩ᵢ ⌈φ ⊔ ψ⌉ ⟺ ⌈φ⌉ ⊔ ⌈ψ⌉ := ctxPropagationOrIff ceilCtx

def ceil_exist : Γ ⊩ᵢ ⌈∃ₑ φ⌉ ⟺ ∃ₑ ⌈φ⌉ :=
  iffIntro (ctxPropagationExist ceilCtx) (ctxPropagationExistR ceilCtx)

def ceil_and : Γ ⊩ᵢ ⌈φ ⊓ ψ⌉ ⇒ ⌈φ⌉ ⊓ ⌈ψ⌉ := ctxAnd ceilCtx

-- ─────────────────────────────────────────────────────────────
-- Totality and equality: introduction is fine (Lemma 3.5, 3.6)
-- ─────────────────────────────────────────────────────────────

/-- Lemma 3.5 / Lemma 3.4: from `φ` infer `⌊φ⌋`. -/
def total_intro (h : Γ ⊩ᵢ φ) : Γ ⊩ᵢ ⌊φ⌋ := doubleNegCtx ceilCtx h

def total_mono (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ ⌊φ⌋ ⇒ ⌊ψ⌋ :=
  contrapositive (ceil_mono (contrapositive h))

def total_top : Γ ⊩ᵢ ⌊⊤ₘ⌋ := total_intro topIntro

def eqML_of_iff (h : Γ ⊩ᵢ φ ⟺ ψ) : Γ ⊩ᵢ φ =ₘₗ ψ := total_intro h

def eqML_refl : Γ ⊩ᵢ φ =ₘₗ φ := total_intro iffRefl

def eqML_symm (h : Γ ⊩ᵢ φ =ₘₗ ψ) : Γ ⊩ᵢ ψ =ₘₗ φ := .mp (total_mono andSwap) h

/-- Positive totality implies classical totality: `(∀x. x ∈ φ) ⇒ ~⌈~φ⌉`. -/
def totalI_impl_total : Γ ⊩ᵢ ⌊φ⌋ⁱ ⇒ ⌊φ⌋ :=
  -- ⌈~φ⌉ ⇒ ∃x. ⌈x ⊓ ~φ⌉
  let s₁ : Γ ⊩ᵢ ⌈~φ⌉ ⇒ ∃ₑ ⌈.evar 0 ⊓ evarLift (~φ)⌉ :=
    .syllogism (ceil_mono (.syllogism (implAnd (extraPremise .existence) implSelf)
                                      pushConjInExist))
               (ctxPropagationExist ceilCtx)
  -- ⌈x ⊓ φ⌉ ⇒ ⌈x ⊓ ~φ⌉ ⇒ ⊥   (the negative SINGLETON)
  let k : Γ ⊩ᵢ ⌈.evar 0 ⊓ evarLift φ⌉ ⇒ (⌈.evar 0 ⊓ evarLift (~φ)⌉ ⇒ evarLift ⊥ₘ) :=
    .exportation (.singleton (C₁ := ceilCtx) (C₂ := ceilCtx) (n := 0) (φ := evarLift φ))
  .syllogism (.syllogism (forallMono k) forallImplExist) (implPreComp s₁)

-- ─────────────────────────────────────────────────────────────
-- Membership (Lemmas 3.7, 3.10(→), 3.11, 3.12, 3.13)
-- ─────────────────────────────────────────────────────────────

/-- Membership introduction (Lemma 3.7): from `φ` infer `x ∈ φ`. -/
def memIntro {n : EVarIndex} (h : Γ ⊩ᵢ φ) : Γ ⊩ᵢ .evar n ∈ₘₗ φ :=
  .mp (ceil_mono (implAnd implSelf (extraPremise h))) ceil_of_evar

/-- Membership introduction, universally closed: from `φ` (with its free
variables shifted past the new binder) infer `⌊φ⌋ⁱ = ∀x. x ∈ φ`. -/
def memIntroAll (h : Γ ⊩ᵢ evarLift φ) : Γ ⊩ᵢ ⌊φ⌋ⁱ :=
  .mp (.forallGen (φ₁ := ⊤ₘ) (extraPremise (memIntro (n := 0) h))) topIntro

/-- Membership∨: `x ∈ (φ ⊔ ψ) ⟺ x ∈ φ ⊔ x ∈ ψ`. -/
def memOr : Γ ⊩ᵢ x ∈ₘₗ (φ ⊔ ψ) ⟺ (x ∈ₘₗ φ) ⊔ (x ∈ₘₗ ψ) :=
  iffIntro (.syllogism (ceil_mono andOrDistrib) (ctxPropagationOr ceilCtx))
           (.syllogism (ctxPropagationOrR ceilCtx) (ceil_mono andOrDistrib'))

/-- Membership∧(→): `x ∈ (φ ⊓ ψ) ⇒ x ∈ φ ⊓ x ∈ ψ`. -/
def memAndElim : Γ ⊩ᵢ x ∈ₘₗ (φ ⊓ ψ) ⇒ (x ∈ₘₗ φ) ⊓ (x ∈ₘₗ ψ) :=
  implAnd (ceil_mono (andMonoRight andElimLeft)) (ceil_mono (andMonoRight andElimRight))

/-- Membership∧(←): `x ∈ φ ⊓ x ∈ ψ ⇒ x ∈ (φ ⊓ ψ)`. This is literally the
`C₁ := C₂ := ⌈□⌉` instance of the positive SINGLETON. -/
def memAndIntro {n : EVarIndex} :
    Γ ⊩ᵢ (.evar n ∈ₘₗ φ) ⊓ (.evar n ∈ₘₗ ψ) ⇒ .evar n ∈ₘₗ (φ ⊓ ψ) :=
  .singletonStrong (C₁ := ceilCtx) (C₂ := ceilCtx) (n := n) (φ := φ) (ψ := ψ)

/-- Membership∧ (Lemma 3.12): `x ∈ (φ ⊓ ψ) ⟺ x ∈ φ ⊓ x ∈ ψ`. -/
def memAnd {n : EVarIndex} :
    Γ ⊩ᵢ .evar n ∈ₘₗ (φ ⊓ ψ) ⟺ (.evar n ∈ₘₗ φ) ⊓ (.evar n ∈ₘₗ ψ) :=
  iffIntro memAndElim memAndIntro

/-- Membership¬, the derivable half: `x ∈ ~φ ⇒ ~(x ∈ φ)` (by the negative
SINGLETON). -/
def memNegElim {n : EVarIndex} : Γ ⊩ᵢ .evar n ∈ₘₗ (~φ) ⇒ ~(.evar n ∈ₘₗ φ) :=
  flip (.exportation (.singleton (C₁ := ceilCtx) (C₂ := ceilCtx) (n := n) (φ := φ)))

/-- Membership∃: `x ∈ ∃y.φ ⟺ ∃y. x ∈ φ`. -/
def memExist : Γ ⊩ᵢ x ∈ₘₗ (∃ₑ φ) ⟺ ∃ₑ (evarLift x ∈ₘₗ φ) :=
  iffIntro
    (.syllogism (ceil_mono pushConjInExist') (ctxPropagationExist ceilCtx))
    (.syllogism (ctxPropagationExistR ceilCtx)
      (ceil_mono (.existGen (φ₂ := x ⊓ ∃ₑ φ) (andMono implSelf existIntroLift))))

/-- Membership⇒: `x ∈ (φ ⇒ ψ) ⊓ x ∈ φ ⇒ x ∈ ψ`, by Membership∧(←) and modus
ponens inside `⌈·⌉`. -/
def memImplElim {n : EVarIndex} :
    Γ ⊩ᵢ (.evar n ∈ₘₗ (φ ⇒ ψ)) ⊓ (.evar n ∈ₘₗ φ) ⇒ .evar n ∈ₘₗ ψ :=
  .syllogism memAndIntro (ceil_mono (andMonoRight andMp))

/-- The negative form `x ∈ (φ ⇒ ψ) ⇒ ~(x ∈ (φ ⊓ ~ψ))`, which is all that the
negative SINGLETON gives. -/
def memImplElimWeak {n : EVarIndex} :
    Γ ⊩ᵢ .evar n ∈ₘₗ (φ ⇒ ψ) ⇒ ~(.evar n ∈ₘₗ (φ ⊓ ~ψ)) :=
  -- (φ ⇒ ψ) ⇒ ~(φ ⊓ ~ψ)
  let k : Γ ⊩ᵢ (φ ⇒ ψ) ⇒ ~(φ ⊓ ~ψ) :=
    .exportation (.syllogism andAssoc'
      (.syllogism (andMonoLeft andMp) (.syllogism .permutationAnd andMp)))
  .syllogism (ceil_mono (andMonoRight k)) memNegElim

-- ─────────────────────────────────────────────────────────────
-- Membership elimination (Lemma 3.8, 3.19(→))
-- ─────────────────────────────────────────────────────────────

/-- **Membership elimination** `⌈x ⊓ φ⌉ ⇒ x ⇒ φ`: the `C₁ := ⌈□⌉, C₂ := □`
instance of the positive SINGLETON (in its `singletonAlt` form
`⌈x ⊓ φ⌉ ⊓ x ⇒ x ⊓ φ`). The negative rule only gives `⌈x ⊓ φ⌉ ⇒ x ⇒ ~~φ`
(`ceil_evar_impl_nn`). -/
def ceil_evar_impl {n : EVarIndex} : Γ ⊩ᵢ ⌈.evar n ⊓ φ⌉ ⇒ .evar n ⇒ φ :=
  .exportation (.syllogism
    (.singletonAlt (C₁ := ceilCtx) (C₂ := .hole) (n := n) (φ := φ)) andElimRight)

/-- The double-negation form `⌈x ⊓ φ⌉ ⇒ x ⇒ ~~φ`, a corollary. -/
def ceil_evar_impl_nn {n : EVarIndex} :
    Γ ⊩ᵢ ⌈.evar n ⊓ φ⌉ ⇒ .evar n ⇒ ~~φ :=
  .syllogism ceil_evar_impl (implLift dni)

/-- Lemma 3.8: `(∀x. x ∈ φ) ⇒ φ`, internal form. -/
def totalI_impl : Γ ⊩ᵢ ⌊φ⌋ⁱ ⇒ φ :=
  implMp (.syllogism (forallMono (ceil_evar_impl (n := 0) (φ := evarLift φ)))
                     (forallImplExist (ψ := .evar 0) (χ := φ)))
         (extraPremise .existence)

/-- Lemma 3.8: from `∀x. x ∈ φ` infer `φ`. -/
def memElim (h : Γ ⊩ᵢ ⌊φ⌋ⁱ) : Γ ⊩ᵢ φ := .mp totalI_impl h

/-- The double-negation form `⌊φ⌋ⁱ ⇒ ~~φ`, a corollary. -/
def totalI_impl_nn : Γ ⊩ᵢ ⌊φ⌋ⁱ ⇒ ~~φ := .syllogism totalI_impl dni

/-- Lemma 3.19(→): `∃y. (⌈y ⊓ φ⌉ ⊓ y) ⇒ φ`. -/
def existCeilEvar_impl : Γ ⊩ᵢ ∃ₑ (⌈.evar 0 ⊓ evarLift φ⌉ ⊓ .evar 0) ⇒ φ :=
  .existGen (φ₂ := φ) (.importation ceil_evar_impl)

-- ─────────────────────────────────────────────────────────────
-- Definedness of what a context sees (Lemma 3.14, Corollary 3.1, 3.19(←))
-- ─────────────────────────────────────────────────────────────

/-- `C[x ⊓ φ] ⇒ ⌈φ⌉` (the core of Lemma 3.14): transport `x ⊓ φ` from `C`
into `⌈x⌉`, which definedness provides. -/
def ctx_evar_impl_ceil (C : AppCtx Symbol) {n : EVarIndex} :
    Γ ⊩ᵢ C.fill (.evar n ⊓ φ) ⇒ ⌈φ⌉ :=
  .syllogism (implAnd implSelf (extraPremise ceil_of_evar))
    (.syllogism (.singletonAlt (C₁ := C) (C₂ := ceilCtx) (n := n) (φ := φ))
      (ceil_mono andElimRight))

/-- Lemma 3.14: `C[φ] ⇒ ⌈φ⌉`. -/
def ctxImplDefined (C : AppCtx Symbol) : Γ ⊩ᵢ C.fill φ ⇒ ⌈φ⌉ :=
  let s₁ : Γ ⊩ᵢ φ ⇒ ∃ₑ (.evar 0 ⊓ evarLift φ) :=
    .syllogism (implAnd (extraPremise .existence) implSelf) pushConjInExist
  .syllogism (ctxFraming C s₁)
    (.syllogism (ctxPropagationExist C)
      (.existGen (φ₂ := ⌈φ⌉) (ctx_evar_impl_ceil C.liftEVar)))

/-- Corollary 3.1: `φ ⇒ ⌈φ⌉`. Not derivable in the published system
(`IML.TopFilter.phi_impl_ceil_not_derivable`). -/
def phi_impl_ceil : Γ ⊩ᵢ φ ⇒ ⌈φ⌉ := ctxImplDefined .hole

/-- `⌊φ⌋ ⇒ ~~φ` for the classical totality (Corollary 3.1 gives `⌊φ⌋ ⇒ φ`
classically, by DNE). -/
def total_elim_nn : Γ ⊩ᵢ ⌊φ⌋ ⇒ ~~φ := contrapositive phi_impl_ceil

/-- `x ⊓ φ ⇒ ⌈x ⊓ φ⌉`. -/
def evar_and_impl_ceil {n : EVarIndex} : Γ ⊩ᵢ .evar n ⊓ φ ⇒ ⌈.evar n ⊓ φ⌉ :=
  .syllogism (implAnd implSelf (extraPremise ceil_of_evar))
    (.singletonAlt (C₁ := .hole) (C₂ := ceilCtx) (n := n) (φ := φ))

/-- Lemma 3.19(←): `φ ⇒ ∃y. (⌈y ⊓ φ⌉ ⊓ y)`. -/
def phi_impl_existCeilEvar : Γ ⊩ᵢ φ ⇒ ∃ₑ (⌈.evar 0 ⊓ evarLift φ⌉ ⊓ .evar 0) :=
  .syllogism (.syllogism (implAnd (extraPremise .existence) implSelf) pushConjInExist)
    (existMono (implAnd evar_and_impl_ceil andElimLeft))

/-- Lemma 3.19: `φ ⟺ ∃y. (⌈y ⊓ φ⌉ ⊓ y)`. -/
def existCeilEvar_iff : Γ ⊩ᵢ φ ⟺ ∃ₑ (⌈.evar 0 ⊓ evarLift φ⌉ ⊓ .evar 0) :=
  iffIntro phi_impl_existCeilEvar existCeilEvar_impl

-- ─────────────────────────────────────────────────────────────
-- Transport out of nested contexts: `⌈C[φ]⌉ ⇒ ⌈φ⌉`, idempotence of `⌈·⌉`
-- ─────────────────────────────────────────────────────────────

/-- `⌈C[φ]⌉ ⇒ ⌈φ⌉`: split `φ` as `∃y. y ⊓ φ`, propagate the `∃` out of
`⌈C[·]⌉`, and transport `y ⊓ φ` from the context `⌈C[□]⌉` into `⌈y⌉` by the
positive SINGLETON. -/
def ceil_ctx_impl_ceil (C : AppCtx Symbol) : Γ ⊩ᵢ ⌈C.fill φ⌉ ⇒ ⌈φ⌉ :=
  let s₁ : Γ ⊩ᵢ φ ⇒ ∃ₑ (.evar 0 ⊓ evarLift φ) :=
    .syllogism (implAnd (extraPremise .existence) implSelf) pushConjInExist
  let s₂ : Γ ⊩ᵢ ⌈C.liftEVar.fill (.evar 0 ⊓ evarLift φ)⌉ ⇒ ⌈evarLift φ⌉ :=
    ctx_evar_impl_ceil (.right (.symbol HasCeil.ceil) C.liftEVar) (n := 0)
  .syllogism (ceil_mono (ctxFraming C s₁))
    (.syllogism (ceil_mono (ctxPropagationExist C))
      (.syllogism (ctxPropagationExist ceilCtx)
        (.existGen (φ₂ := ⌈φ⌉) (by rw [ceilCtx_liftEVar, evarLift_ceil, ceilCtx_fill]; exact s₂))))

/-- Idempotence of definedness, `⌈⌈φ⌉⌉ ⇒ ⌈φ⌉`. -/
def ceil_ceil : Γ ⊩ᵢ ⌈⌈φ⌉⌉ ⇒ ⌈φ⌉ := ceil_ctx_impl_ceil ceilCtx

def ceil_ceil_iff : Γ ⊩ᵢ ⌈⌈φ⌉⌉ ⟺ ⌈φ⌉ := iffIntro ceil_ceil phi_impl_ceil

/-- `x ∈ φ ⇒ x ∈ (x ∈ φ)`. -/
def mem_mem {n : EVarIndex} : Γ ⊩ᵢ .evar n ∈ₘₗ φ ⇒ .evar n ∈ₘₗ (.evar n ∈ₘₗ φ) :=
  ceil_mono (implAnd andElimLeft evar_and_impl_ceil)

/-- Lemma 3.17 (→): `C[φ₁ ⊓ x ∈ φ₂] ⇒ C[φ₁] ⊓ x ∈ φ₂`, for any pattern `x`.
The membership conjunct leaves the context through Lemma 3.14 and
idempotence. -/
def ctx_mem_elim (C : AppCtx Symbol) :
    Γ ⊩ᵢ C.fill (φ ⊓ (x ∈ₘₗ ψ)) ⇒ C.fill φ ⊓ (x ∈ₘₗ ψ) :=
  implAnd (ctxFraming C andElimLeft)
    (.syllogism (ctxFraming C andElimRight) (.syllogism (ctxImplDefined C) ceil_ceil))

/-- Membership∀ (→): `x ∈ ∀y.φ ⇒ ∀y. x ∈ φ`. The converse is sound but not
derived (see the report). -/
def memForallElim : Γ ⊩ᵢ x ∈ₘₗ (∀ₑ φ) ⇒ ∀ₑ (evarLift x ∈ₘₗ φ) :=
  .forallGen (φ₁ := x ∈ₘₗ (∀ₑ φ)) (ceil_mono (andMonoRight forallElimLift))

-- ─────────────────────────────────────────────────────────────
-- Positive totality propagates into contexts
-- ─────────────────────────────────────────────────────────────

/-- `⌊φ⌋ⁱ ⇒ x ∈ φ` (instantiation). -/
def totalI_elim {n : EVarIndex} : Γ ⊩ᵢ ⌊φ⌋ⁱ ⇒ .evar n ∈ₘₗ φ := by
  have h : Γ ⊩ᵢ ⌊φ⌋ⁱ ⇒ evarSubst 0 (.evar n) ⌈.evar 0 ⊓ evarLift φ⌉ := forallElim
  simpa only [Pattern.ceil, Pattern.memML, evarSubst, evarSubst_evarLift,
    beq_self_eq_true, ↓reduceIte] using h

/-- Monotonicity of `⌊·⌋ⁱ` (the hypothesis is stated for the lifted patterns
because it is used under the binder). -/
def totalI_mono (h : Γ ⊩ᵢ evarLift φ ⇒ evarLift ψ) : Γ ⊩ᵢ ⌊φ⌋ⁱ ⇒ ⌊ψ⌋ⁱ :=
  forallMono (ceil_mono (andMonoRight h))

/-- **Positively total patterns propagate into contexts**:
`⌊χ⌋ⁱ ⊓ C[ψ] ⇒ C[χ ⊓ ψ]`. Write `C[ψ]` as `∃y. C[y ⊓ ψ]`; `⌊χ⌋ⁱ` instantiates
to `⌈y ⊓ χ⌉`, and the positive SINGLETON transports `χ` from `⌈y ⊓ χ⌉` into
`C[y ⊓ ψ]`. This is the constructive replacement for the thesis' "predicate
patterns propagate" (Lemma 3.17(←), Lemma 4.7). -/
def totalI_ctx (C : AppCtx Symbol) : Γ ⊩ᵢ ⌊φ⌋ⁱ ⊓ C.fill ψ ⇒ C.fill (φ ⊓ ψ) :=
  let s₁ : Γ ⊩ᵢ ψ ⇒ ∃ₑ (.evar 0 ⊓ evarLift ψ) :=
    .syllogism (implAnd (extraPremise .existence) implSelf) pushConjInExist
  let s₂ : Γ ⊩ᵢ C.fill ψ ⇒ ∃ₑ (C.liftEVar.fill (.evar 0 ⊓ evarLift ψ)) :=
    .syllogism (ctxFraming C s₁) (ctxPropagationExist C)
  let s₃ : Γ ⊩ᵢ evarLift ⌊φ⌋ⁱ ⊓ C.liftEVar.fill (.evar 0 ⊓ evarLift ψ) ⇒
      C.liftEVar.fill (evarLift φ ⊓ evarLift ψ) :=
    .syllogism (andMonoLeft (forallElimLift (φ := ⌈.evar 0 ⊓ evarLift φ⌉)))
      (.syllogism (.singletonStrong (C₁ := ceilCtx) (C₂ := C.liftEVar) (n := 0)
          (φ := evarLift φ) (ψ := evarLift ψ))
        (ctxFraming _ andElimRight))
  .syllogism (andMonoRight s₂)
    (.syllogism pushConjInExist'
      (.existGen (φ₂ := C.fill (φ ⊓ ψ)) (by rw [evarLift_fill]; exact s₃)))

/-- `⌈⌊φ⌋ⁱ⌉ ⇒ ⌊φ⌋ⁱ`: positive totality also leaves `⌈·⌉`. -/
def ceil_totalI : Γ ⊩ᵢ ⌈⌊φ⌋ⁱ⌉ ⇒ ⌊φ⌋ⁱ :=
  .forallGen (φ₁ := ⌈⌊φ⌋ⁱ⌉)
    (.syllogism (ceil_mono (forallElimLift (φ := ⌈.evar 0 ⊓ evarLift φ⌉))) ceil_ceil)

-- ─────────────────────────────────────────────────────────────
-- Positive equality `φ =ⁱ ψ := ⌊φ ⟺ ψ⌋ⁱ` and its elimination (Lemma 3.15)
-- ─────────────────────────────────────────────────────────────

/-- Positive (intuitionistic) equality `⌊φ ⟺ ψ⌋ⁱ = ∀x. x ∈ (φ ⟺ ψ)`, with
Heyting value `⨅_a (φ a ⟺ ψ a)`; the classical `φ =ₘₗ ψ := ⌊φ ⟺ ψ⌋` only
has value `⨅_a ¬¬(φ a ⟺ ψ a)`. -/
def Pattern.eqI (φ ψ : Pattern Symbol) : Pattern Symbol := ⌊φ ⟺ ψ⌋ⁱ

scoped infixl:50 " =ⁱₘₗ " => Pattern.eqI

def eqI_of_iff (h : Γ ⊩ᵢ evarLift φ ⟺ evarLift ψ) : Γ ⊩ᵢ φ =ⁱₘₗ ψ := memIntroAll h

def eqI_refl : Γ ⊩ᵢ φ =ⁱₘₗ φ := memIntroAll iffRefl

def eqI_symm : Γ ⊩ᵢ (φ =ⁱₘₗ ψ) ⇒ (ψ =ⁱₘₗ φ) := totalI_mono andSwap

/-- Positive equality implies the classical one. -/
def eqI_impl_eqML : Γ ⊩ᵢ (φ =ⁱₘₗ ψ) ⇒ (φ =ₘₗ ψ) := totalI_impl_total

/-- Lemma 3.15 for application contexts: `φ₁ =ⁱ φ₂ ⊓ C[φ₁] ⇒ C[φ₂]`. -/
def eqI_elim_ctx (C : AppCtx Symbol) :
    Γ ⊩ᵢ (φ =ⁱₘₗ ψ) ⊓ C.fill φ ⇒ C.fill ψ :=
  .syllogism (totalI_ctx C) (ctxFraming C (.syllogism (andMonoLeft andElimLeft) andMp))

/-- Lemma 3.15, hole case: `φ₁ =ⁱ φ₂ ⇒ φ₁ ⇒ φ₂`. -/
def eqI_elim : Γ ⊩ᵢ (φ =ⁱₘₗ ψ) ⇒ φ ⇒ ψ := .exportation (eqI_elim_ctx .hole)

-- ─────────────────────────────────────────────────────────────
-- Transitivity of positive equality
-- ─────────────────────────────────────────────────────────────

/-- `(φ ⇒ ψ) ⊓ (ψ ⇒ χ) ⇒ (φ ⇒ χ)`. -/
def implCompose : Γ ⊩ᵢ (φ ⇒ ψ) ⊓ (ψ ⇒ χ) ⇒ (φ ⇒ χ) :=
  .exportation (.syllogism
    (implAnd (.syllogism andElimLeft andElimRight)
             (.syllogism (andMonoLeft andElimLeft) andMp))
    andMp)

/-- `(φ ⟺ ψ) ⊓ (ψ ⟺ χ) ⇒ (φ ⟺ χ)`. -/
def iffTransAnd : Γ ⊩ᵢ (φ ⟺ ψ) ⊓ (ψ ⟺ χ) ⇒ (φ ⟺ χ) :=
  implAnd (.syllogism (andMono andElimLeft andElimLeft) implCompose)
          (.syllogism (andMono andElimRight andElimRight)
            (.syllogism .permutationAnd implCompose))

omit [HasCeil Symbol] in
theorem evarLift_iff (φ ψ : Pattern Symbol) :
    evarLift (φ ⟺ ψ) = (evarLift φ ⟺ evarLift ψ) := rfl

omit [HasCeil Symbol] in
theorem evarLift_evar (n : EVarIndex) : evarLift (.evar n : Pattern Symbol) = .evar (n + 1) := by
  simp [evarLift, evarLiftFrom]

/-- Transitivity of positive equality, from Membership∧(←) and transitivity of
`⟺` under the binder. -/
def eqI_trans : Γ ⊩ᵢ (φ =ⁱₘₗ ψ) ⊓ (ψ =ⁱₘₗ χ) ⇒ (φ =ⁱₘₗ χ) :=
  .syllogism andForallDistrib
    (forallMono (.syllogism memAndIntro (ceil_mono (andMonoRight (by
      rw [evarLift_iff, evarLift_iff, evarLift_iff]; exact iffTransAnd)))))

-- ─────────────────────────────────────────────────────────────
-- Lifting commutes with lifting; `=ⁱ` passes under a binder
-- ─────────────────────────────────────────────────────────────

/-- The index arithmetic of `evarLiftFrom_comm`, stated over `ℕ` (so that
`omega` sees through the `EVarIndex` abbreviation). -/
theorem liftIdx_comm (k i j : ℕ) (h : i ≤ j) :
    (if (if k ≥ i then k + 1 else k) ≥ j + 1 then (if k ≥ i then k + 1 else k) + 1
      else (if k ≥ i then k + 1 else k)) =
    (if (if k ≥ j then k + 1 else k) ≥ i then (if k ≥ j then k + 1 else k) + 1
      else (if k ≥ j then k + 1 else k)) := by
  split_ifs <;> omega

omit [HasCeil Symbol] in
theorem evarLiftFrom_comm (φ : Pattern Symbol) {i j : Nat} (h : i ≤ j) :
    evarLiftFrom (j + 1) (evarLiftFrom i φ) = evarLiftFrom i (evarLiftFrom j φ) := by
  induction φ generalizing i j with
  | evar k =>
    simp only [evarLiftFrom, Pattern.evar.injEq]
    exact liftIdx_comm k i j h
  | svar | symbol | bot => rfl
  | app _ _ ih₁ ih₂ => simp only [evarLiftFrom, ih₁ h, ih₂ h]
  | impl _ _ ih₁ ih₂ => simp only [evarLiftFrom, ih₁ h, ih₂ h]
  | conj _ _ ih₁ ih₂ => simp only [evarLiftFrom, ih₁ h, ih₂ h]
  | disj _ _ ih₁ ih₂ => simp only [evarLiftFrom, ih₁ h, ih₂ h]
  | exist _ ih => simp only [evarLiftFrom, ih (Nat.succ_le_succ h)]
  | forallP _ ih => simp only [evarLiftFrom, ih (Nat.succ_le_succ h)]
  | mu _ ih => simp only [evarLiftFrom, ih h]
  | nu _ ih => simp only [evarLiftFrom, ih h]

theorem evarLift_totalI (φ : Pattern Symbol) : evarLift ⌊φ⌋ⁱ = ⌊evarLift φ⌋ⁱ := by
  simp only [Pattern.totalI, Pattern.memML, Pattern.ceil, evarLift, evarLiftFrom,
    Pattern.forallP.injEq, Pattern.app.injEq, Pattern.conj.injEq, Pattern.evar.injEq,
    ge_iff_le, true_and]
  exact ⟨by decide, evarLiftFrom_comm φ (le_refl 0)⟩

theorem evarLift_eqI (φ ψ : Pattern Symbol) :
    evarLift (φ =ⁱₘₗ ψ) = (evarLift φ =ⁱₘₗ evarLift ψ) := by
  rw [Pattern.eqI, Pattern.eqI, evarLift_totalI, evarLift_iff]

-- ─────────────────────────────────────────────────────────────
-- Application-free contexts and replacement of equivalents
-- ─────────────────────────────────────────────────────────────

/-- Application-free contexts: one hole, built with `⊓, ⊔, ⇒, ∃, ∀`. When the
hole is under a binder the filled pattern is lifted (`fill`), so `fill C φ`
plugs in `φ` with its free variables intact. -/
inductive PCtx (Symbol : Type) where
  | hole : PCtx Symbol
  | conjL : PCtx Symbol → Pattern Symbol → PCtx Symbol
  | conjR : Pattern Symbol → PCtx Symbol → PCtx Symbol
  | disjL : PCtx Symbol → Pattern Symbol → PCtx Symbol
  | disjR : Pattern Symbol → PCtx Symbol → PCtx Symbol
  | implL : PCtx Symbol → Pattern Symbol → PCtx Symbol
  | implR : Pattern Symbol → PCtx Symbol → PCtx Symbol
  | exist : PCtx Symbol → PCtx Symbol
  | forallP : PCtx Symbol → PCtx Symbol

def PCtx.fill : PCtx Symbol → Pattern Symbol → Pattern Symbol
  | .hole, φ => φ
  | .conjL C ψ, φ => C.fill φ ⊓ ψ
  | .conjR ψ C, φ => ψ ⊓ C.fill φ
  | .disjL C ψ, φ => C.fill φ ⊔ ψ
  | .disjR ψ C, φ => ψ ⊔ C.fill φ
  | .implL C ψ, φ => C.fill φ ⇒ ψ
  | .implR ψ C, φ => ψ ⇒ C.fill φ
  | .exist C, φ => ∃ₑ (C.fill (evarLift φ))
  | .forallP C, φ => ∀ₑ (C.fill (evarLift φ))

/-- Lift the free element variables of a context from index `k`. -/
def PCtx.liftFrom (k : Nat) : PCtx Symbol → PCtx Symbol
  | .hole => .hole
  | .conjL C ψ => .conjL (C.liftFrom k) (evarLiftFrom k ψ)
  | .conjR ψ C => .conjR (evarLiftFrom k ψ) (C.liftFrom k)
  | .disjL C ψ => .disjL (C.liftFrom k) (evarLiftFrom k ψ)
  | .disjR ψ C => .disjR (evarLiftFrom k ψ) (C.liftFrom k)
  | .implL C ψ => .implL (C.liftFrom k) (evarLiftFrom k ψ)
  | .implR ψ C => .implR (evarLiftFrom k ψ) (C.liftFrom k)
  | .exist C => .exist (C.liftFrom (k + 1))
  | .forallP C => .forallP (C.liftFrom (k + 1))

omit [HasCeil Symbol] in
theorem PCtx.evarLiftFrom_fill (C : PCtx Symbol) (k : Nat) (φ : Pattern Symbol) :
    evarLiftFrom k (C.fill φ) = (C.liftFrom k).fill (evarLiftFrom k φ) := by
  induction C generalizing k φ with
  | hole => rfl
  | conjL C ψ ih => simp only [PCtx.fill, PCtx.liftFrom, evarLiftFrom, ih]
  | conjR ψ C ih => simp only [PCtx.fill, PCtx.liftFrom, evarLiftFrom, ih]
  | disjL C ψ ih => simp only [PCtx.fill, PCtx.liftFrom, evarLiftFrom, ih]
  | disjR ψ C ih => simp only [PCtx.fill, PCtx.liftFrom, evarLiftFrom, ih]
  | implL C ψ ih => simp only [PCtx.fill, PCtx.liftFrom, evarLiftFrom, ih]
  | implR ψ C ih => simp only [PCtx.fill, PCtx.liftFrom, evarLiftFrom, ih]
  | exist C ih =>
    simp only [PCtx.fill, PCtx.liftFrom, evarLiftFrom, ih, evarLift]
    rw [evarLiftFrom_comm φ (Nat.zero_le k)]
  | forallP C ih =>
    simp only [PCtx.fill, PCtx.liftFrom, evarLiftFrom, ih, evarLift]
    rw [evarLiftFrom_comm φ (Nat.zero_le k)]

omit [HasCeil Symbol] in
theorem PCtx.evarLift_fill (C : PCtx Symbol) (φ : Pattern Symbol) :
    evarLift (C.fill φ) = (C.liftFrom 0).fill (evarLift φ) :=
  C.evarLiftFrom_fill 0 φ

/-- **Replacement of equivalents in application-free contexts**:
`(φ ⟺ ψ) ⊓ P[φ] ⇒ P[ψ]`. Purely propositional/first-order; no definedness. -/
def iffLeibniz (P : PCtx Symbol) (φ ψ : Pattern Symbol) :
    Γ ⊩ᵢ (φ ⟺ ψ) ⊓ P.fill φ ⇒ P.fill ψ :=
  match P with
  | .hole => .syllogism (andMonoLeft andElimLeft) andMp
  | .conjL P' _ =>
    implAnd (.syllogism (andMonoRight andElimLeft) (iffLeibniz P' φ ψ))
      (.syllogism andElimRight andElimRight)
  | .conjR _ P' =>
    implAnd (.syllogism andElimRight andElimLeft)
      (.syllogism (andMonoRight andElimRight) (iffLeibniz P' φ ψ))
  | .disjL P' _ => .syllogism andOrDistrib (orMono (iffLeibniz P' φ ψ) andElimRight)
  | .disjR _ P' => .syllogism andOrDistrib (orMono andElimRight (iffLeibniz P' φ ψ))
  | .implL P' _ =>
    .exportation (.syllogism
      (implAnd (.syllogism andElimLeft andElimRight)
        (.syllogism (andMonoLeft andElimLeft)
          (.syllogism (andMonoLeft andSwap) (iffLeibniz P' ψ φ))))
      andMp)
  | .implR _ P' =>
    .exportation (.syllogism
      (implAnd (.syllogism andElimLeft andElimLeft)
        (.syllogism (andMonoLeft andElimRight) andMp))
      (iffLeibniz P' φ ψ))
  | .exist P' =>
    .syllogism pushConjInExist' (existMono (iffLeibniz P' (evarLift φ) (evarLift ψ)))
  | .forallP P' =>
    .forallGen (φ₁ := (φ ⟺ ψ) ⊓ ∀ₑ (P'.fill (evarLift φ)))
      (.syllogism (andMonoRight forallElimLift) (iffLeibniz P' (evarLift φ) (evarLift ψ)))

-- ─────────────────────────────────────────────────────────────
-- Leibniz's law for positive equality (Lemma 3.15, general positions)
-- ─────────────────────────────────────────────────────────────

/-- Lemma 3.15 for a hole below an application context `A` and an
application-free context `P`: `(φ =ⁱ ψ) ⊓ A[P[φ]] ⇒ A[P[ψ]]`. The equality
enters `A` as the plain equivalence `φ ⟺ ψ` (`totalI_ctx`), which then
replaces `φ` by `ψ` inside `P` (`iffLeibniz`). -/
def eqI_leibniz_in (A : AppCtx Symbol) (P : PCtx Symbol) :
    Γ ⊩ᵢ (φ =ⁱₘₗ ψ) ⊓ A.fill (P.fill φ) ⇒ A.fill (P.fill ψ) :=
  .syllogism (totalI_ctx A) (ctxFraming A (iffLeibniz P φ ψ))

/-- **Leibniz's law for positive equality** at every hole of the shape
`Q[A[P[□]]]` — an application-free context `Q` above an application context
`A` above an application-free context `P`, with the hole on either side of
implications and under `∃`/`∀` binders in `Q` and `P`:

    (φ =ⁱ ψ) ⊓ Q[A[P[φ]]] ⇒ Q[A[P[ψ]]].

Not covered: holes under `μ`/`ν`, and holes below two application layers
separated by a non-application connective (e.g. `(∀x. x ⬝ φ) ⬝ θ`). Both
would need `⌊θ⌋ⁱ ⇒ ⌊⌊θ⌋ⁱ⌋ⁱ`, i.e. that positive totality is itself a
"predicate pattern" (see `IsPred` below), which is sound but not derived. -/
def eqI_leibniz (Q : PCtx Symbol) (A : AppCtx Symbol) (P : PCtx Symbol) (φ ψ : Pattern Symbol) :
    Γ ⊩ᵢ (φ =ⁱₘₗ ψ) ⊓ Q.fill (A.fill (P.fill φ)) ⇒ Q.fill (A.fill (P.fill ψ)) :=
  match Q with
  | .hole => eqI_leibniz_in A P
  | .conjL Q' _ =>
    implAnd (.syllogism (andMonoRight andElimLeft) (eqI_leibniz Q' A P φ ψ))
      (.syllogism andElimRight andElimRight)
  | .conjR _ Q' =>
    implAnd (.syllogism andElimRight andElimLeft)
      (.syllogism (andMonoRight andElimRight) (eqI_leibniz Q' A P φ ψ))
  | .disjL Q' _ => .syllogism andOrDistrib (orMono (eqI_leibniz Q' A P φ ψ) andElimRight)
  | .disjR _ Q' => .syllogism andOrDistrib (orMono andElimRight (eqI_leibniz Q' A P φ ψ))
  | .implL Q' _ =>
    .exportation (.syllogism
      (implAnd (.syllogism andElimLeft andElimRight)
        (.syllogism (andMonoLeft andElimLeft)
          (.syllogism (andMonoLeft eqI_symm) (eqI_leibniz Q' A P ψ φ))))
      andMp)
  | .implR _ Q' =>
    .exportation (.syllogism
      (implAnd (.syllogism andElimLeft andElimLeft)
        (.syllogism (andMonoLeft andElimRight) andMp))
      (eqI_leibniz Q' A P φ ψ))
  | .exist Q' =>
    .syllogism pushConjInExist' (existMono (by
      rw [evarLift_eqI, evarLift_fill, evarLift_fill, PCtx.evarLift_fill, PCtx.evarLift_fill]
      exact eqI_leibniz Q' A.liftEVar (P.liftFrom 0) (evarLift φ) (evarLift ψ)))
  | .forallP Q' =>
    .forallGen (φ₁ := (φ =ⁱₘₗ ψ) ⊓ ∀ₑ (Q'.fill (evarLift (A.fill (P.fill φ))))) (by
      change Γ ⊩ᵢ evarLift (φ =ⁱₘₗ ψ) ⊓
        ∀ₑ (evarLiftFrom 1 (Q'.fill (evarLift (A.fill (P.fill φ))))) ⇒
        Q'.fill (evarLift (A.fill (P.fill ψ)))
      rw [evarLift_eqI, evarLift_fill, evarLift_fill, PCtx.evarLift_fill, PCtx.evarLift_fill]
      exact .syllogism (andMonoRight forallElimLift)
        (eqI_leibniz Q' A.liftEVar (P.liftFrom 0) (evarLift φ) (evarLift ψ)))

/-- Lemma 3.9(←) for positive equality: `x =ⁱ φ ⇒ x ∈ φ`. (For the classical
equality this direction fails: `IML.PointModel.eqML_mem_not_derivable`.) -/
def eqI_impl_mem {n : EVarIndex} : Γ ⊩ᵢ (.evar n =ⁱₘₗ φ) ⇒ .evar n ∈ₘₗ φ :=
  implMp (.exportation (eqI_leibniz_in ceilCtx (.conjR (.evar n) .hole)))
    (extraPremise (.mp (ceil_mono .contractionAnd) ceil_of_evar))

-- ─────────────────────────────────────────────────────────────
-- Predicate patterns: the one missing principle
-- ─────────────────────────────────────────────────────────────

/-- `θ` is a *predicate pattern* when it implies its own positive totality,
`θ ⇒ ⌊θ⌋ⁱ` (the converse `⌊θ⌋ⁱ ⇒ θ` always holds, `totalI_impl`). Semantically
this says `θ` has the same truth value at every point. Classically every
`⌈·⌉`-pattern is one (thesis Lemma 3.17/4.7); intuitionistically, whether
`⌈φ⌉ ⇒ ⌊⌈φ⌉⌋ⁱ` is derivable is the open question behind Membership¬(←),
Membership⇒(←), Lemma 3.9(→), Lemma 3.17(←) and the deduction theorem with
`⌊·⌋ⁱ` (see the report). It is sound in every `HModel`. -/
abbrev IsPred (Γ : Set (Pattern Symbol)) (θ : Pattern Symbol) : Type := Γ ⊩ᵢ θ ⇒ ⌊θ⌋ⁱ

/-- Every positive totality is a predicate pattern *up to the outer `⌊·⌋ⁱ`*:
`⌊φ⌋ⁱ ⇒ ⌈x ⊓ φ⌉` for every `x`, but not `⌊φ⌋ⁱ ⇒ ⌈x ⊓ ⌊φ⌋ⁱ⌉`. What is
derivable is that `⌊·⌋ⁱ`-patterns propagate their *content* into contexts
(`totalI_ctx`); a predicate pattern propagates *itself*: -/
def pred_ctx {θ : Pattern Symbol} (h : IsPred Γ θ) (C : AppCtx Symbol) :
    Γ ⊩ᵢ θ ⊓ C.fill ψ ⇒ C.fill (θ ⊓ ψ) :=
  .syllogism (andMonoLeft h) (totalI_ctx C)

/-- Lemma 3.17(←) in the form `C[φ₁] ⊓ x ∈ φ₂ ⇒ C[φ₁ ⊓ x ∈ φ₂]`, given that
`x ∈ φ₂` is a predicate pattern. -/
def ctx_mem_intro_of_pred (h : IsPred Γ (x ∈ₘₗ ψ)) (C : AppCtx Symbol) :
    Γ ⊩ᵢ C.fill φ ⊓ (x ∈ₘₗ ψ) ⇒ C.fill (φ ⊓ (x ∈ₘₗ ψ)) :=
  .syllogism .permutationAnd (.syllogism (pred_ctx h C) (ctxFraming C .permutationAnd))

/-- Lemma 3.9(→), `x ∈ y ⇒ x =ⁱ y`, given that (the lifted) `x ∈ y` is a
predicate pattern. -/
def mem_impl_eqI_of_pred {n m : EVarIndex}
    (h : IsPred Γ (evarLift (.evar n ∈ₘₗ .evar m))) :
    Γ ⊩ᵢ (.evar n ∈ₘₗ .evar m) ⇒ (.evar n =ⁱₘₗ .evar m) :=
  .forallGen (φ₁ := .evar n ∈ₘₗ .evar m) (.syllogism h (.syllogism (totalI_elim (n := 0))
    (ceil_mono (andMonoRight (by
      change Γ ⊩ᵢ ⌈evarLift (.evar n) ⊓ evarLift (.evar m)⌉ ⇒
        (evarLift (.evar n) ⟺ evarLift (.evar m))
      rw [evarLift_evar, evarLift_evar]
      exact implAnd ceil_evar_impl (.syllogism (ceil_mono andSwap) ceil_evar_impl))))))

/-- Membership¬(←), `~(x ∈ φ) ⇒ x ∈ ~φ`, given that `~(x ∈ φ)` is a predicate
pattern. -/
def memNegIntro_of_pred {n : EVarIndex} (h : IsPred Γ (~(.evar n ∈ₘₗ φ))) :
    Γ ⊩ᵢ ~(.evar n ∈ₘₗ φ) ⇒ .evar n ∈ₘₗ (~φ) :=
  implMp (.exportation (.syllogism (pred_ctx h ceilCtx) (ceil_mono
      (implAnd andElimRight (.exportation (.syllogism andAssoc
        (.syllogism (andMonoRight evar_and_impl_ceil) andMp)))))))
    (extraPremise ceil_of_evar)

/-- Membership⇒(←), `(x ∈ φ ⇒ x ∈ ψ) ⇒ x ∈ (φ ⇒ ψ)`, given that
`x ∈ φ ⇒ x ∈ ψ` is a predicate pattern. -/
def memImplIntro_of_pred {n : EVarIndex} (h : IsPred Γ ((.evar n ∈ₘₗ φ) ⇒ (.evar n ∈ₘₗ ψ))) :
    Γ ⊩ᵢ ((.evar n ∈ₘₗ φ) ⇒ (.evar n ∈ₘₗ ψ)) ⇒ .evar n ∈ₘₗ (φ ⇒ ψ) :=
  implMp (.exportation (.syllogism (pred_ctx h ceilCtx) (ceil_mono
      (implAnd andElimRight (.exportation (.syllogism
        (implAnd
          (implMp (.syllogism andElimLeft andElimLeft)
            (.syllogism (andMonoLeft andElimRight) evar_and_impl_ceil))
          (.syllogism andElimLeft andElimRight))
        (.importation ceil_evar_impl)))))))
    (extraPremise ceil_of_evar)

end IML
