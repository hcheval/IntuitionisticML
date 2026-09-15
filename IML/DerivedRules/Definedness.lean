import IML.DerivedRules.Context

/-!
# Definedness, membership and totality in iML (thesis §3.2)

`⌈φ⌉ := ceil ⬝ φ` with the axiom `∀x. ⌈x⌉`. The classical development
derives the whole membership calculus of the system P from this. Which of
it survives intuitionistically?

* Survives (proved here): definedness of variables, `⌈·⌉` monotone,
  `⌈⊥⌉ ⇒ ⊥`, `⌈φ ⊔ ψ⌉ ⟺ ⌈φ⌉ ⊔ ⌈ψ⌉`, `⌈∃x.φ⌉ ⟺ ∃x.⌈φ⌉`,
  membership introduction, Membership∨, Membership∃, one half each of
  Membership∧ and Membership¬, equality introduction/reflexivity/symmetry,
  and `⌊φ⌋ⁱ ⇒ ⌊φ⌋` where `⌊φ⌋ⁱ := ∀x. x ∈ φ` is the *positive* totality.

* Weakened: membership elimination gives only `~~φ`; Lemma 3.19(→) gives
  only `~~φ`; `⌊φ⌋ ⇒ ~~φ` instead of `⌊φ⌋ ⇒ φ`.

* Not derivable without a new principle: `C[φ] ⇒ ⌈φ⌉` (Lemma 3.14),
  Membership∧(←), Membership¬(←), Lemma 3.19(←). Every classical proof of
  these routes through the *membership excluded middle*
  `⌈x⌉ ⇒ ⌈x ⊓ φ⌉ ⊔ ⌈x ⊓ ~φ⌉`, which is unsound in the Heyting semantics.
  We isolate the sound principle `SingletonPos` (a positive companion of
  SINGLETON, classically derivable) and show it recovers Lemma 3.14 and
  Membership∧(←). `TopFilterModel` shows that `φ ⇒ ⌈φ⌉` and
  Membership¬(←) are genuinely underivable.
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

class IsDefinedness (Symbol : Type) [HasCeil Symbol] (Γ : Set (Pattern Symbol)) : Prop where
  defAxiom : ∀ₑ ⌈.evar 0⌉ ∈ Γ

variable {Γ : Set (Pattern Symbol)} [IsDefinedness Symbol Γ] {φ ψ x : Pattern Symbol}

-- ─────────────────────────────────────────────────────────────
-- Basic facts (all intuitionistic)
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

def ceil_evar_top {n : EVarIndex} : Γ ⊩ᵢ ⌈.evar n ⊓ ⊤ₘ⌉ :=
  .mp (ceil_mono (implAnd implSelf implTop)) ceil_of_evar

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
  -- ⌈x ⊓ φ⌉ ⇒ ⌈x ⊓ ~φ⌉ ⇒ ⊥   (SINGLETON)
  let k : Γ ⊩ᵢ ⌈.evar 0 ⊓ evarLift φ⌉ ⇒ (⌈.evar 0 ⊓ evarLift (~φ)⌉ ⇒ evarLift ⊥ₘ) :=
    .exportation (.singleton (C₁ := ceilCtx) (C₂ := ceilCtx) (n := 0) (φ := evarLift φ))
  .syllogism (.syllogism (forallMono k) forallImplExist) (implPreComp s₁)

-- ─────────────────────────────────────────────────────────────
-- Membership (Lemmas 3.7, 3.10(→), 3.11, 3.12(→), 3.13)
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

/-- Membership∧, the derivable half: `x ∈ (φ ⊓ ψ) ⇒ x ∈ φ ⊓ x ∈ ψ`. -/
def memAndElim : Γ ⊩ᵢ x ∈ₘₗ (φ ⊓ ψ) ⇒ (x ∈ₘₗ φ) ⊓ (x ∈ₘₗ ψ) :=
  implAnd (ceil_mono (andMonoRight andElimLeft)) (ceil_mono (andMonoRight andElimRight))

/-- Membership¬, the derivable half: `x ∈ ~φ ⇒ ~(x ∈ φ)` (by SINGLETON). -/
def memNegElim {n : EVarIndex} : Γ ⊩ᵢ .evar n ∈ₘₗ (~φ) ⇒ ~(.evar n ∈ₘₗ φ) :=
  flip (.exportation (.singleton (C₁ := ceilCtx) (C₂ := ceilCtx) (n := n) (φ := φ)))

/-- Membership∃: `x ∈ ∃y.φ ⟺ ∃y. x ∈ φ`. -/
def memExist : Γ ⊩ᵢ x ∈ₘₗ (∃ₑ φ) ⟺ ∃ₑ (evarLift x ∈ₘₗ φ) :=
  iffIntro
    (.syllogism (ceil_mono pushConjInExist') (ctxPropagationExist ceilCtx))
    (.syllogism (ctxPropagationExistR ceilCtx)
      (ceil_mono (.existGen (φ₂ := x ⊓ ∃ₑ φ) (andMono implSelf existIntroLift))))

/-- Membership⇒, the derivable half: `x ∈ (φ ⇒ ψ) ⊓ x ∈ φ ⇒ x ∈ ψ` needs
Membership∧(←); what is derivable outright is `x ∈ (φ ⇒ ψ) ⇒ ~(x ∈ (φ ⊓ ~ψ))`. -/
def memImplElimWeak {n : EVarIndex} :
    Γ ⊩ᵢ .evar n ∈ₘₗ (φ ⇒ ψ) ⇒ ~(.evar n ∈ₘₗ (φ ⊓ ~ψ)) :=
  -- (φ ⇒ ψ) ⇒ ~(φ ⊓ ~ψ)
  let k : Γ ⊩ᵢ (φ ⇒ ψ) ⇒ ~(φ ⊓ ~ψ) :=
    .exportation (.syllogism andAssoc'
      (.syllogism (andMonoLeft andMp) (.syllogism .permutationAnd andMp)))
  .syllogism (ceil_mono (andMonoRight k)) memNegElim

-- ─────────────────────────────────────────────────────────────
-- Membership elimination: only up to double negation (Lemma 3.8, 3.19)
-- ─────────────────────────────────────────────────────────────

/-- SINGLETON in the form `⌈x ⊓ φ⌉ ⇒ x ⇒ ~~φ`. -/
def ceil_evar_impl_nn {n : EVarIndex} :
    Γ ⊩ᵢ ⌈.evar n ⊓ φ⌉ ⇒ .evar n ⇒ ~~φ :=
  .exportation (.exportation (.syllogism andAssoc
    (.singleton (C₁ := ceilCtx) (C₂ := .hole) (n := n) (φ := φ))))

/-- Lemma 3.8, intuitionistic form: from `∀x. x ∈ φ` infer `~~φ`.
The classical conclusion `φ` would need DNE. -/
def totalI_impl_nn : Γ ⊩ᵢ ⌊φ⌋ⁱ ⇒ ~~φ :=
  implMp (.syllogism (forallMono (ceil_evar_impl_nn (n := 0) (φ := evarLift φ)))
                     (forallImplExist (ψ := .evar 0) (χ := ~~φ)))
         (extraPremise .existence)

/-- Internal form: `⌊φ⌋ⁱ ⇒ ~~φ`. Whether `⌊φ⌋ⁱ ⇒ φ` (sound!) is derivable
is open; see the report. -/
def memElimWeak (h : Γ ⊩ᵢ ⌊φ⌋ⁱ) : Γ ⊩ᵢ ~~φ := .mp totalI_impl_nn h

/-- Lemma 3.19(→), intuitionistic form: `∃y. (⌈y ⊓ φ⌉ ⊓ y) ⇒ ~~φ`. -/
def existCeilEvar_impl_nn :
    Γ ⊩ᵢ ∃ₑ (⌈.evar 0 ⊓ evarLift φ⌉ ⊓ .evar 0) ⇒ ~~φ :=
  .existGen (φ₂ := ~~φ) (.importation ceil_evar_impl_nn)

-- ─────────────────────────────────────────────────────────────
-- The positive singleton principle
-- ─────────────────────────────────────────────────────────────

/-- `C₁[x ⊓ φ] ⊓ C₂[x ⊓ ψ] ⇒ C₂[x ⊓ φ ⊓ ψ]`: an element variable matches at
most one element, so information about it can be *transported* between
contexts. Sound for the Heyting semantics; classically derivable from
SINGLETON and PROPAGATION∨ by splitting `ψ` as `(ψ ⊓ φ) ⊔ (ψ ⊓ ~φ)`;
intuitionistically we take it as a hypothesis. -/
def SingletonPos (Γ : Set (Pattern Symbol)) : Type :=
  ∀ (C₁ C₂ : AppCtx Symbol) (n : EVarIndex) (φ ψ : Pattern Symbol),
    Γ ⊩ᵢ C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n ⊓ ψ) ⇒ C₂.fill ((.evar n ⊓ φ) ⊓ ψ)

/-- With `SingletonPos`: `C[x ⊓ φ] ⇒ ⌈φ⌉` (the core of Lemma 3.14). -/
def ctx_evar_impl_ceil (hs : SingletonPos Γ) (C : AppCtx Symbol) {n : EVarIndex} :
    Γ ⊩ᵢ C.fill (.evar n ⊓ φ) ⇒ ⌈φ⌉ :=
  .syllogism (implAnd implSelf (extraPremise ceil_evar_top))
    (.syllogism (hs C ceilCtx n φ ⊤ₘ)
      (ceil_mono (.syllogism andElimLeft andElimRight)))

/-- Lemma 3.14 with `SingletonPos`: `C[φ] ⇒ ⌈φ⌉`. -/
def ctxImplDefined (hs : SingletonPos Γ) (C : AppCtx Symbol) : Γ ⊩ᵢ C.fill φ ⇒ ⌈φ⌉ :=
  let s₁ : Γ ⊩ᵢ φ ⇒ ∃ₑ (.evar 0 ⊓ evarLift φ) :=
    .syllogism (implAnd (extraPremise .existence) implSelf) pushConjInExist
  .syllogism (ctxFraming C s₁)
    (.syllogism (ctxPropagationExist C)
      (.existGen (φ₂ := ⌈φ⌉) (ctx_evar_impl_ceil hs C.liftEVar)))

/-- Corollary 3.1 with `SingletonPos`: `φ ⇒ ⌈φ⌉`. -/
def phi_impl_ceil (hs : SingletonPos Γ) : Γ ⊩ᵢ φ ⇒ ⌈φ⌉ := ctxImplDefined hs .hole

/-- Membership∧(←) with `SingletonPos`. -/
def memAndIntro (hs : SingletonPos Γ) {n : EVarIndex} :
    Γ ⊩ᵢ (.evar n ∈ₘₗ φ) ⊓ (.evar n ∈ₘₗ ψ) ⇒ .evar n ∈ₘₗ (φ ⊓ ψ) :=
  .syllogism (hs ceilCtx ceilCtx n φ ψ) (ceil_mono andAssoc)

/-- `⌊φ⌋ ⇒ ~~φ` with `SingletonPos` (Corollary 3.1 gives `⌊φ⌋ ⇒ φ` classically). -/
def total_elim_nn (hs : SingletonPos Γ) : Γ ⊩ᵢ ⌊φ⌋ ⇒ ~~φ :=
  contrapositive (phi_impl_ceil hs)

/-- With `SingletonPos`: `x ⊓ φ ⇒ ⌈x ⊓ φ⌉`. -/
def evar_and_impl_ceil (hs : SingletonPos Γ) {n : EVarIndex} :
    Γ ⊩ᵢ .evar n ⊓ φ ⇒ ⌈.evar n ⊓ φ⌉ :=
  .syllogism (implAnd implSelf (extraPremise ceil_evar_top))
    (.syllogism (hs .hole ceilCtx n φ ⊤ₘ) (ceil_mono andElimLeft))

/-- Lemma 3.19(←) with `SingletonPos`: `φ ⇒ ∃y. (⌈y ⊓ φ⌉ ⊓ y)`. -/
def phi_impl_existCeilEvar (hs : SingletonPos Γ) :
    Γ ⊩ᵢ φ ⇒ ∃ₑ (⌈.evar 0 ⊓ evarLift φ⌉ ⊓ .evar 0) :=
  .syllogism (.syllogism (implAnd (extraPremise .existence) implSelf) pushConjInExist)
    (existMono (implAnd (evar_and_impl_ceil hs) andElimLeft))

end IML
