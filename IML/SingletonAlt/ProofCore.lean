import IML.SingletonAlt.Kernel

/-!
# iML with a pluggable singleton axiom

`ProofCore Ax Γ φ` is the proof system of `IML/Proof.lean` with the singleton constructor
removed and replaced by an arbitrary axiom scheme `Ax : ι → Pattern Symbol` (a family of
patterns indexed by a type of instances). This lets us compare

* `singletonAx`       — the negative rule `~(C₁[x ⊓ φ] ⊓ C₂[x ⊓ ~φ])` of the published
                        system (archived as `IML.Crisp.Proof`)
* `singletonAltAx`    — the weaker positive rule `C₁[x ⊓ φ] ⊓ C₂[x] ⇒ C₂[x ⊓ φ]`
* `singletonStrongAx` — the positive rule `C₁[x ⊓ φ] ⊓ C₂[x ⊓ ψ] ⇒ C₂[x ⊓ (φ ⊓ ψ)]`, now
                        the primitive `Proof.singletonStrong` of the current system

`ProofCore singletonStrongAx` is literally the current system (`Proof.toCore`,
`ProofCore.toProof`); `ProofCore singletonAx` is the published system, rule for rule; and
`ProofAlt := ProofCore singletonAltAx` is the weaker positive variant.

## Derivability results (all sorry-free, all intuitionistic unless a `lem` hypothesis is taken)

* `botProp_of_alt`, `botProp_of_singleton` — propagation of `⊥`, `C[⊥] ⇒ ⊥`, is derivable
  from either singleton axiom (via `existence` + `existGen`); it is not a gap in iML.
* `alt_of_strong`, `singleton_of_strong` — `singletonStrong` yields both other rules. (These
  are the derivations behind `Proof.singletonAlt` and `Proof.singleton` in `IML/Proof.lean`.)
* `alt_of_singleton_lem`, `strong_of_singleton_lem` — with excluded middle, `singleton`
  yields both positive rules; so classically all three are interderivable-or-stronger in the
  order `singleton ⊣⊢ strong ⊢ alt`.

The non-derivability results (`alt ⊬ singleton` even classically; `singleton ⊬ alt`, hence
`singleton ⊬ strong`, intuitionistically) are in `Countermodels.lean`. The last one is what
makes the change of primitive a genuine strengthening of the published system.
-/

namespace IML

open Pattern

-- ─────────────────────────────────────────────────────────────
-- The core system
-- ─────────────────────────────────────────────────────────────

/-- iML minus its singleton rule, plus an axiom scheme `Ax`. Every constructor other than
`ax` is copied verbatim from `Proof`. -/
inductive ProofCore {Symbol : Type} {ι : Type} (Ax : ι → Pattern Symbol)
    (Γ : Set (Pattern Symbol)) : Pattern Symbol → Type where
  | ax (i : ι) : ProofCore Ax Γ (Ax i)
  | assumption {φ} : φ ∈ Γ → ProofCore Ax Γ φ
  | contractionOr {φ}    : ProofCore Ax Γ (φ ⊔ φ ⇒ φ)
  | contractionAnd {φ}   : ProofCore Ax Γ (φ ⇒ φ ⊓ φ)
  | weakeningOr {φ ψ}    : ProofCore Ax Γ (φ ⇒ φ ⊔ ψ)
  | weakeningAnd {φ ψ}   : ProofCore Ax Γ (φ ⊓ ψ ⇒ φ)
  | permutationOr {φ ψ}  : ProofCore Ax Γ (φ ⊔ ψ ⇒ ψ ⊔ φ)
  | permutationAnd {φ ψ} : ProofCore Ax Γ (φ ⊓ ψ ⇒ ψ ⊓ φ)
  | mp {φ ψ} : ProofCore Ax Γ (φ ⇒ ψ) → ProofCore Ax Γ φ → ProofCore Ax Γ ψ
  | botElim {φ} : ProofCore Ax Γ (⊥ₘ ⇒ φ)
  | syllogism {φ ψ χ} :
      ProofCore Ax Γ (φ ⇒ ψ) → ProofCore Ax Γ (ψ ⇒ χ) → ProofCore Ax Γ (φ ⇒ χ)
  | exportation {φ ψ χ} :
      ProofCore Ax Γ (φ ⊓ ψ ⇒ χ) → ProofCore Ax Γ (φ ⇒ ψ ⇒ χ)
  | importation {φ ψ χ} :
      ProofCore Ax Γ (φ ⇒ ψ ⇒ χ) → ProofCore Ax Γ (φ ⊓ ψ ⇒ χ)
  | expansion {φ ψ χ} :
      ProofCore Ax Γ (φ ⇒ ψ) → ProofCore Ax Γ (χ ⊔ φ ⇒ χ ⊔ ψ)
  | existQuant {φ} {n : EVarIndex} :
      ProofCore Ax Γ (evarSubst 0 (.evar n) φ ⇒ ∃ₑ φ)
  | existGen {φ₁ φ₂} :
      ProofCore Ax Γ (φ₁ ⇒ evarLift φ₂) → ProofCore Ax Γ (∃ₑ φ₁ ⇒ φ₂)
  | forallQuant {φ} {n : EVarIndex} :
      ProofCore Ax Γ (∀ₑ φ ⇒ evarSubst 0 (.evar n) φ)
  | forallGen {φ₁ φ₂} :
      ProofCore Ax Γ (evarLift φ₁ ⇒ φ₂) → ProofCore Ax Γ (φ₁ ⇒ ∀ₑ φ₂)
  | existence : ProofCore Ax Γ (∃ₑ (.evar 0 : Pattern Symbol))
  | svSubst {φ ψ} : ProofCore Ax Γ φ → ProofCore Ax Γ (svarSubst 0 ψ φ)
  | preFixpoint {φ} :
      SVarPositive φ 0 → ProofCore Ax Γ (svarSubst 0 (μ φ) φ ⇒ μ φ)
  | knasterTarski {φ ψ} :
      ProofCore Ax Γ (svarSubst 0 ψ φ ⇒ ψ) → ProofCore Ax Γ (μ φ ⇒ ψ)
  | postFixpoint {φ} :
      SVarPositive φ 0 → ProofCore Ax Γ (ν φ ⇒ svarSubst 0 (ν φ) φ)
  | park {φ ψ} :
      ProofCore Ax Γ (ψ ⇒ svarSubst 0 ψ φ) → ProofCore Ax Γ (ψ ⇒ ν φ)
  | propagationOrLeft {φ₁ φ₂ ψ} :
      ProofCore Ax Γ ((φ₁ ⊔ φ₂) ⬝ ψ ⇒ φ₁ ⬝ ψ ⊔ φ₂ ⬝ ψ)
  | propagationOrRight {φ₁ φ₂ ψ} :
      ProofCore Ax Γ (ψ ⬝ (φ₁ ⊔ φ₂) ⇒ ψ ⬝ φ₁ ⊔ ψ ⬝ φ₂)
  | propagationExistLeft {φ ψ} :
      ProofCore Ax Γ ((∃ₑ φ) ⬝ ψ ⇒ ∃ₑ (φ ⬝ evarLift ψ))
  | propagationExistRight {φ ψ} :
      ProofCore Ax Γ (ψ ⬝ (∃ₑ φ) ⇒ ∃ₑ (evarLift ψ ⬝ φ))
  | framingLeft {φ₁ φ₂ ψ} :
      ProofCore Ax Γ (φ₁ ⇒ φ₂) → ProofCore Ax Γ (φ₁ ⬝ ψ ⇒ φ₂ ⬝ ψ)
  | framingRight {φ₁ φ₂ ψ} :
      ProofCore Ax Γ (φ₁ ⇒ φ₂) → ProofCore Ax Γ (ψ ⬝ φ₁ ⇒ ψ ⬝ φ₂)

scoped notation:25 Γ " ⊩[" Ax "] " φ => ProofCore Ax Γ φ

-- ─────────────────────────────────────────────────────────────
-- Axiom schemes
-- ─────────────────────────────────────────────────────────────

section Schemes
variable (Symbol : Type)

/-- Instances of a singleton-shaped scheme: two contexts, a variable, a pattern. -/
abbrev SingletonInst := AppCtx Symbol × AppCtx Symbol × EVarIndex × Pattern Symbol

/-- The negative rule `~(C₁[x ⊓ φ] ⊓ C₂[x ⊓ ~φ])` of the published system. -/
def singletonAx : SingletonInst Symbol → Pattern Symbol
  | (C₁, C₂, n, φ) => ~(C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n ⊓ ~φ))

/-- The weaker positive rule `C₁[x ⊓ φ] ⊓ C₂[x] ⇒ C₂[x ⊓ φ]`. -/
def singletonAltAx : SingletonInst Symbol → Pattern Symbol
  | (C₁, C₂, n, φ) => C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n) ⇒ C₂.fill (.evar n ⊓ φ)

/-- The positive rule `C₁[x ⊓ φ] ⊓ C₂[x ⊓ ψ] ⇒ C₂[x ⊓ (φ ⊓ ψ)]`, the primitive
`Proof.singletonStrong` of the current system. -/
def singletonStrongAx : SingletonInst Symbol × Pattern Symbol → Pattern Symbol
  | ((C₁, C₂, n, φ), ψ) =>
      C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n ⊓ ψ) ⇒ C₂.fill (.evar n ⊓ (φ ⊓ ψ))

/-- Excluded middle `φ ⊔ ~φ`. -/
def lemAx : Pattern Symbol → Pattern Symbol := fun φ => φ ⊔ ~φ

/-- Double negation elimination `~~φ ⇒ φ`. -/
def dneAx : Pattern Symbol → Pattern Symbol := fun φ => ~~φ ⇒ φ

end Schemes

/-- Union of two schemes. -/
def axUnion {Symbol : Type} {ι κ : Type} (A : ι → Pattern Symbol) (B : κ → Pattern Symbol) :
    ι ⊕ κ → Pattern Symbol := Sum.elim A B

/-- iML with the singleton rule replaced by the weaker `singletonAlt`. -/
abbrev ProofAlt {Symbol : Type} (Γ : Set (Pattern Symbol)) (φ : Pattern Symbol) : Type :=
  ProofCore (singletonAltAx Symbol) Γ φ

-- ─────────────────────────────────────────────────────────────
-- `ProofCore singletonStrongAx` is exactly the current `Proof`
-- ─────────────────────────────────────────────────────────────

section Equivalence
variable {Symbol : Type} {Γ : Set (Pattern Symbol)}

def Proof.toCore :
    ∀ {φ : Pattern Symbol}, Proof Γ φ → ProofCore (singletonStrongAx Symbol) Γ φ
  | _, .assumption h => .assumption h
  | _, .contractionOr => .contractionOr
  | _, .contractionAnd => .contractionAnd
  | _, .weakeningOr => .weakeningOr
  | _, .weakeningAnd => .weakeningAnd
  | _, .permutationOr => .permutationOr
  | _, .permutationAnd => .permutationAnd
  | _, .mp h₁ h₂ => .mp h₁.toCore h₂.toCore
  | _, .botElim => .botElim
  | _, .syllogism h₁ h₂ => .syllogism h₁.toCore h₂.toCore
  | _, .exportation h => .exportation h.toCore
  | _, .importation h => .importation h.toCore
  | _, .expansion h => .expansion h.toCore
  | _, .existQuant => .existQuant
  | _, .existGen h => .existGen h.toCore
  | _, .forallQuant => .forallQuant
  | _, .forallGen h => .forallGen h.toCore
  | _, .existence => .existence
  | _, .svSubst h => .svSubst h.toCore
  | _, .preFixpoint hp => .preFixpoint hp
  | _, .knasterTarski h => .knasterTarski h.toCore
  | _, .postFixpoint hp => .postFixpoint hp
  | _, .park h => .park h.toCore
  | _, .singletonStrong (C₁ := C₁) (C₂ := C₂) (n := n) (φ := φ) (ψ := ψ) =>
    .ax ((C₁, C₂, n, φ), ψ)
  | _, .propagationOrLeft => .propagationOrLeft
  | _, .propagationOrRight => .propagationOrRight
  | _, .propagationExistLeft => .propagationExistLeft
  | _, .propagationExistRight => .propagationExistRight
  | _, .framingLeft h => .framingLeft h.toCore
  | _, .framingRight h => .framingRight h.toCore

def ProofCore.toProof :
    ∀ {φ : Pattern Symbol}, ProofCore (singletonStrongAx Symbol) Γ φ → Proof Γ φ
  | _, .ax ((_, _, _, _), _) => .singletonStrong
  | _, .assumption h => .assumption h
  | _, .contractionOr => .contractionOr
  | _, .contractionAnd => .contractionAnd
  | _, .weakeningOr => .weakeningOr
  | _, .weakeningAnd => .weakeningAnd
  | _, .permutationOr => .permutationOr
  | _, .permutationAnd => .permutationAnd
  | _, .mp h₁ h₂ => .mp h₁.toProof h₂.toProof
  | _, .botElim => .botElim
  | _, .syllogism h₁ h₂ => .syllogism h₁.toProof h₂.toProof
  | _, .exportation h => .exportation h.toProof
  | _, .importation h => .importation h.toProof
  | _, .expansion h => .expansion h.toProof
  | _, .existQuant => .existQuant
  | _, .existGen h => .existGen h.toProof
  | _, .forallQuant => .forallQuant
  | _, .forallGen h => .forallGen h.toProof
  | _, .existence => .existence
  | _, .svSubst h => .svSubst h.toProof
  | _, .preFixpoint hp => .preFixpoint hp
  | _, .knasterTarski h => .knasterTarski h.toProof
  | _, .postFixpoint hp => .postFixpoint hp
  | _, .park h => .park h.toProof
  | _, .propagationOrLeft => .propagationOrLeft
  | _, .propagationOrRight => .propagationOrRight
  | _, .propagationExistLeft => .propagationExistLeft
  | _, .propagationExistRight => .propagationExistRight
  | _, .framingLeft h => .framingLeft h.toProof
  | _, .framingRight h => .framingRight h.toProof

end Equivalence

-- ─────────────────────────────────────────────────────────────
-- Soundness over `HModel` (reuses every `hvalid_*` lemma verbatim)
-- ─────────────────────────────────────────────────────────────

theorem soundnessCore {Symbol : Type} {ι : Type} {Ax : ι → Pattern Symbol}
    {Γ : Set (Pattern Symbol)} {φ : Pattern Symbol} (h : Γ ⊩[Ax] φ) :
    ∀ (L : Type*) [Order.Frame L] (M : HModel Symbol L),
    (∀ i, HValid M (Ax i)) → (∀ γ ∈ Γ, HValid M γ) → HValid M φ := by
  induction h with
  | ax i => exact fun _ _ M hAx _ ρ m => hAx i ρ m
  | assumption hmem => exact fun _ _ M _ hΓ ρ m => hΓ _ hmem ρ m
  | contractionOr => exact fun _ _ _ _ _ _ m => hvalid_contractionOr m
  | contractionAnd => exact fun _ _ _ _ _ _ m => hvalid_contractionAnd m
  | weakeningOr => exact fun _ _ _ _ _ _ m => hvalid_weakeningOr m
  | weakeningAnd => exact fun _ _ _ _ _ _ m => hvalid_weakeningAnd m
  | permutationOr => exact fun _ _ _ _ _ _ m => hvalid_permutationOr m
  | permutationAnd => exact fun _ _ _ _ _ _ m => hvalid_permutationAnd m
  | mp _ _ ih₁ ih₂ =>
    exact fun L _ M hAx hΓ ρ m => hvalid_mp (ih₁ L M hAx hΓ ρ m) (ih₂ L M hAx hΓ ρ m)
  | botElim => exact fun _ _ _ _ _ _ m => hvalid_botElim m
  | syllogism _ _ ih₁ ih₂ =>
    exact fun L _ M hAx hΓ ρ m => hvalid_syllogism (ih₁ L M hAx hΓ ρ m) (ih₂ L M hAx hΓ ρ m)
  | exportation _ ih =>
    exact fun L _ M hAx hΓ ρ m => hvalid_exportation (ih L M hAx hΓ ρ m)
  | importation _ ih =>
    exact fun L _ M hAx hΓ ρ m => hvalid_importation (ih L M hAx hΓ ρ m)
  | expansion _ ih =>
    exact fun L _ M hAx hΓ ρ m => hvalid_expansion (ih L M hAx hΓ ρ m)
  | existQuant => exact fun _ _ _ _ _ _ m => hvalid_existQuant m
  | existGen _ ih =>
    exact fun L _ M hAx hΓ ρ m => hvalid_existGen (ih L M hAx hΓ) m
  | forallQuant => exact fun _ _ _ _ _ _ m => hvalid_forallQuant m
  | forallGen _ ih =>
    exact fun L _ M hAx hΓ ρ m => hvalid_forallGen (ih L M hAx hΓ) m
  | existence => exact fun _ _ _ _ _ _ m => hvalid_existence m
  | svSubst _ ih =>
    exact fun L _ M hAx hΓ ρ m => hvalid_svSubst (ih L M hAx hΓ) m
  | preFixpoint hpos =>
    exact fun _ _ _ _ _ _ m => hvalid_preFixpoint hpos m
  | knasterTarski _ ih =>
    exact fun L _ M hAx hΓ ρ m => hvalid_knasterTarski (ih L M hAx hΓ ρ) m
  | postFixpoint hpos =>
    exact fun _ _ _ _ _ _ m => hvalid_postFixpoint hpos m
  | park _ ih =>
    exact fun L _ M hAx hΓ ρ m => hvalid_park (ih L M hAx hΓ ρ) m
  | propagationOrLeft =>
    exact fun _ _ _ _ _ _ m => hvalid_propagationOrLeft m
  | propagationOrRight =>
    exact fun _ _ _ _ _ _ m => hvalid_propagationOrRight m
  | propagationExistLeft =>
    exact fun _ _ _ _ _ _ m => hvalid_propagationExistLeft m
  | propagationExistRight =>
    exact fun _ _ _ _ _ _ m => hvalid_propagationExistRight m
  | framingLeft _ ih =>
    exact fun L _ M hAx hΓ ρ m => hvalid_framingLeft m (ih L M hAx hΓ ρ)
  | framingRight _ ih =>
    exact fun L _ M hAx hΓ ρ m => hvalid_framingRight m (ih L M hAx hΓ ρ)

section AxValidity
variable {Symbol : Type} {L : Type*} [Order.Frame L] (M : HModel Symbol L)

theorem hvalid_singletonAx : ∀ i, HValid M (singletonAx Symbol i)
  | (_, _, _, _) => fun _ m => hvalid_singleton m

theorem hvalid_singletonAltAx : ∀ i, HValid M (singletonAltAx Symbol i)
  | (_, _, _, _) => fun _ m => hvalid_singletonAlt m

theorem hvalid_singletonStrongAx : ∀ i, HValid M (singletonStrongAx Symbol i)
  | ((_, _, _, _), _) => fun _ m => hvalid_singletonStrong m

end AxValidity

/-- **Soundness of the weaker system** `ProofAlt` over every `HModel`. -/
theorem soundnessAlt {Symbol : Type} {Γ : Set (Pattern Symbol)} {φ : Pattern Symbol}
    (h : ProofAlt Γ φ) :
    ∀ (L : Type*) [Order.Frame L] (M : HModel Symbol L),
    (∀ γ ∈ Γ, HValid M γ) → HValid M φ :=
  fun L _ M hΓ => soundnessCore h L M (hvalid_singletonAltAx M) hΓ

-- ─────────────────────────────────────────────────────────────
-- Derived rules (Hilbert-style toolkit), valid for every scheme `Ax`
-- ─────────────────────────────────────────────────────────────

namespace ProofCore

variable {Symbol : Type} {ι : Type} {Ax : ι → Pattern Symbol} {Γ : Set (Pattern Symbol)}
         {φ ψ χ φ' ψ' : Pattern Symbol}

def idP (φ : Pattern Symbol) : Γ ⊩[Ax] φ ⇒ φ :=
  syllogism contractionAnd weakeningAnd

def weakeningAnd' : Γ ⊩[Ax] φ ⊓ ψ ⇒ ψ :=
  syllogism permutationAnd weakeningAnd

def andMonoL (h : Γ ⊩[Ax] φ ⇒ ψ) : Γ ⊩[Ax] φ ⊓ χ ⇒ ψ ⊓ χ :=
  importation (syllogism h (exportation (idP (ψ ⊓ χ))))

def andMonoR (h : Γ ⊩[Ax] φ ⇒ ψ) : Γ ⊩[Ax] χ ⊓ φ ⇒ χ ⊓ ψ :=
  syllogism permutationAnd (syllogism (andMonoL h) permutationAnd)

def andIntro (h₁ : Γ ⊩[Ax] φ ⇒ ψ) (h₂ : Γ ⊩[Ax] φ ⇒ χ) : Γ ⊩[Ax] φ ⇒ ψ ⊓ χ :=
  syllogism contractionAnd (syllogism (andMonoL h₁) (andMonoR h₂))

def orElim (h₁ : Γ ⊩[Ax] φ ⇒ χ) (h₂ : Γ ⊩[Ax] ψ ⇒ χ) : Γ ⊩[Ax] φ ⊔ ψ ⇒ χ :=
  syllogism (expansion h₂) (syllogism permutationOr (syllogism (expansion h₁) contractionOr))

def orMono (h₁ : Γ ⊩[Ax] φ ⇒ φ') (h₂ : Γ ⊩[Ax] ψ ⇒ ψ') : Γ ⊩[Ax] φ ⊔ ψ ⇒ φ' ⊔ ψ' :=
  orElim (syllogism h₁ weakeningOr) (syllogism h₂ (syllogism weakeningOr permutationOr))

/-- `φ ⊓ (ψ ⊔ χ) ⇒ (φ ⊓ ψ) ⊔ (φ ⊓ χ)` -/
def distrib : Γ ⊩[Ax] φ ⊓ (ψ ⊔ χ) ⇒ (φ ⊓ ψ) ⊔ (φ ⊓ χ) :=
  syllogism permutationAnd (importation (orElim
    (exportation (syllogism permutationAnd weakeningOr))
    (exportation (syllogism permutationAnd (syllogism weakeningOr permutationOr)))))

/-- `φ ⊓ ~φ ⇒ ⊥` -/
def negElim : Γ ⊩[Ax] φ ⊓ ~φ ⇒ ⊥ₘ :=
  syllogism permutationAnd (importation (idP (φ ⇒ ⊥ₘ)))

/-- `~~(φ ⊔ ~φ)`: excluded middle holds up to double negation. -/
def nnLem : Γ ⊩[Ax] ~~(φ ⊔ ~φ) :=
  -- ~(φ ⊔ ~φ) ⇒ ~φ
  let h₁ : Γ ⊩[Ax] ~(φ ⊔ ~φ) ⇒ ~φ :=
    exportation (syllogism (andMonoR weakeningOr) (importation (idP (~(φ ⊔ ~φ)))))
  -- ~(φ ⊔ ~φ) ⇒ φ ⊔ ~φ
  let h₂ : Γ ⊩[Ax] ~(φ ⊔ ~φ) ⇒ φ ⊔ ~φ :=
    syllogism h₁ (syllogism weakeningOr permutationOr)
  syllogism (andIntro (idP _) h₂) (importation (idP (~(φ ⊔ ~φ))))

/-- `φ ⇒ ⊤ₘ` -/
def topIntro : Γ ⊩[Ax] φ ⇒ ⊤ₘ :=
  exportation (weakeningAnd' (φ := φ) (ψ := ⊥ₘ))

def andTop : Γ ⊩[Ax] φ ⇒ φ ⊓ ⊤ₘ := andIntro (idP φ) topIntro

/-- From a theorem `ψ`, `φ ⇒ ψ` for any `φ`. -/
def constImp (h : Γ ⊩[Ax] ψ) : Γ ⊩[Ax] φ ⇒ ψ :=
  mp (exportation weakeningAnd) h

/-- Context monotonicity (framing through a whole context). -/
def ctxMono (C : AppCtx Symbol) (h : Γ ⊩[Ax] φ ⇒ ψ) : Γ ⊩[Ax] C.fill φ ⇒ C.fill ψ :=
  match C with
  | .hole => h
  | .left C' _ => framingLeft (ctxMono C' h)
  | .right _ C' => framingRight (ctxMono C' h)

/-- Propagation of `⊔` through a whole context. -/
def ctxOr (C : AppCtx Symbol) : Γ ⊩[Ax] C.fill (φ ⊔ ψ) ⇒ C.fill φ ⊔ C.fill ψ :=
  match C with
  | .hole => idP _
  | .left C' _ => syllogism (framingLeft (ctxOr C')) propagationOrLeft
  | .right _ C' => syllogism (framingRight (ctxOr C')) propagationOrRight

end ProofCore

-- ─────────────────────────────────────────────────────────────
-- Derivability results (the context lift `AppCtx.lift`, needed to bind the
-- variable in ⊥-propagation, is in `IML/Proof.lean`)
-- ─────────────────────────────────────────────────────────────

namespace ProofCore

variable {Symbol : Type} {ι : Type} {Ax : ι → Pattern Symbol} {Γ : Set (Pattern Symbol)}

/-- Shorthand: the scheme `Ax` makes all instances of `singletonAlt` available. -/
abbrev HasAlt (Ax : ι → Pattern Symbol) (Γ : Set (Pattern Symbol)) : Type :=
  ∀ (C₁ C₂ : AppCtx Symbol) (n : EVarIndex) (φ : Pattern Symbol),
    Γ ⊩[Ax] C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n) ⇒ C₂.fill (.evar n ⊓ φ)

abbrev HasSingleton (Ax : ι → Pattern Symbol) (Γ : Set (Pattern Symbol)) : Type :=
  ∀ (C₁ C₂ : AppCtx Symbol) (n : EVarIndex) (φ : Pattern Symbol),
    Γ ⊩[Ax] ~(C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n ⊓ ~φ))

abbrev HasStrong (Ax : ι → Pattern Symbol) (Γ : Set (Pattern Symbol)) : Type :=
  ∀ (C₁ C₂ : AppCtx Symbol) (n : EVarIndex) (φ ψ : Pattern Symbol),
    Γ ⊩[Ax] C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n ⊓ ψ) ⇒ C₂.fill (.evar n ⊓ (φ ⊓ ψ))

abbrev HasLem (Ax : ι → Pattern Symbol) (Γ : Set (Pattern Symbol)) : Type :=
  ∀ φ : Pattern Symbol, Γ ⊩[Ax] φ ⊔ ~φ

def hasAlt_of_scheme {Γ : Set (Pattern Symbol)} : HasAlt (singletonAltAx Symbol) Γ :=
  fun C₁ C₂ n φ => ax (C₁, C₂, n, φ)

def hasSingleton_of_scheme {Γ : Set (Pattern Symbol)} : HasSingleton (singletonAx Symbol) Γ :=
  fun C₁ C₂ n φ => ax (C₁, C₂, n, φ)

def hasStrong_of_scheme {Γ : Set (Pattern Symbol)} : HasStrong (singletonStrongAx Symbol) Γ :=
  fun C₁ C₂ n φ ψ => ax ((C₁, C₂, n, φ), ψ)

/-- **Propagation of `⊥` is derivable from `singletonAlt`.**
Verdict: `C[⊥] ⇒ ⊥` is not a gap in the proposed system. Proof: the `C₂ := hole` instance
gives `C'[⊥] ⊓ x ⇒ x ⊓ ⊥` for `C'` the lifted context; export `x`, generalize it with
`existGen`, and discharge `∃x. x` with `existence`. -/
def botProp_of_alt (alt : HasAlt Ax Γ) (C : AppCtx Symbol) : Γ ⊩[Ax] C.fill ⊥ₘ ⇒ ⊥ₘ :=
  let C' := C.lift 0
  let h₁ : Γ ⊩[Ax] C'.fill (.evar 0 ⊓ ⊥ₘ) ⊓ .evar 0 ⇒ .evar 0 ⊓ ⊥ₘ := alt C' .hole 0 ⊥ₘ
  let h₂ : Γ ⊩[Ax] C'.fill ⊥ₘ ⊓ .evar 0 ⇒ ⊥ₘ :=
    syllogism (andMonoL (ctxMono C' botElim)) (syllogism h₁ weakeningAnd')
  let h₃ : Γ ⊩[Ax] .evar 0 ⇒ (C'.fill ⊥ₘ ⇒ ⊥ₘ) := exportation (syllogism permutationAnd h₂)
  let h₄ : Γ ⊩[Ax] ∃ₑ (.evar 0) ⇒ (C.fill ⊥ₘ ⇒ ⊥ₘ) :=
    existGen (by rw [evarLift_ctxBot_impl_bot]; exact h₃)
  mp h₄ existence

/-- **Propagation of `⊥` is derivable from the negative `singleton` rule** as well, by the
same route (instance `C₂ := hole`, `φ := ⊥`). So iML never lacked `C[⊥] ⇒ ⊥`. -/
def botProp_of_singleton (sg : HasSingleton Ax Γ) (C : AppCtx Symbol) :
    Γ ⊩[Ax] C.fill ⊥ₘ ⇒ ⊥ₘ :=
  let C' := C.lift 0
  let h₁ : Γ ⊩[Ax] C'.fill (.evar 0 ⊓ ⊥ₘ) ⊓ (.evar 0 ⊓ ~⊥ₘ) ⇒ ⊥ₘ := sg C' .hole 0 ⊥ₘ
  let h₂ : Γ ⊩[Ax] C'.fill ⊥ₘ ⊓ .evar 0 ⇒ ⊥ₘ :=
    syllogism (syllogism (andMonoL (ctxMono C' botElim)) (andMonoR andTop)) h₁
  let h₃ : Γ ⊩[Ax] .evar 0 ⇒ (C'.fill ⊥ₘ ⇒ ⊥ₘ) := exportation (syllogism permutationAnd h₂)
  let h₄ : Γ ⊩[Ax] ∃ₑ (.evar 0) ⇒ (C.fill ⊥ₘ ⇒ ⊥ₘ) :=
    existGen (by rw [evarLift_ctxBot_impl_bot]; exact h₃)
  mp h₄ existence

/-- **`singletonStrong ⊢ singletonAlt`** (take `ψ := ⊤`). -/
def alt_of_strong (st : HasStrong Ax Γ) : HasAlt Ax Γ := fun C₁ C₂ n φ =>
  syllogism (andMonoR (ctxMono C₂ andTop))
    (syllogism (st C₁ C₂ n φ ⊤ₘ) (ctxMono C₂ (andMonoR weakeningAnd)))

/-- **`singletonStrong ⊢ singleton`** (take `ψ := ~φ`, then `φ ⊓ ~φ ⇒ ⊥` and ⊥-propagation). -/
def singleton_of_strong (st : HasStrong Ax Γ) : HasSingleton Ax Γ := fun C₁ C₂ n φ =>
  syllogism (st C₁ C₂ n φ (~φ))
    (syllogism (ctxMono C₂ (syllogism weakeningAnd' negElim))
      (botProp_of_alt (alt_of_strong st) C₂))

/-- **Classically, `singleton ⊢ singletonAlt`.** With excluded middle `φ ⊔ ~φ`, split
`C₂[x]` into `C₂[x ⊓ φ] ⊔ C₂[x ⊓ ~φ]` (context ∨-propagation) and kill the second disjunct
with `singleton`. The use of `lem` is essential: `Countermodels.lean` shows the implication
fails intuitionistically. -/
def alt_of_singleton_lem (sg : HasSingleton Ax Γ) (lem : HasLem Ax Γ) : HasAlt Ax Γ :=
  fun C₁ C₂ n φ =>
  let s₁ : Γ ⊩[Ax] .evar n ⇒ (.evar n ⊓ φ) ⊔ (.evar n ⊓ ~φ) :=
    syllogism (andIntro (idP _) (constImp (lem φ))) distrib
  let s₂ : Γ ⊩[Ax] C₂.fill (.evar n) ⇒ C₂.fill (.evar n ⊓ φ) ⊔ C₂.fill (.evar n ⊓ ~φ) :=
    syllogism (ctxMono C₂ s₁) (ctxOr C₂)
  let s₃ := syllogism (andMonoR (χ := C₁.fill (.evar n ⊓ φ)) s₂) distrib
  let s₄ := orMono (weakeningAnd' (φ := C₁.fill (.evar n ⊓ φ)))
    (syllogism (sg C₁ C₂ n φ) (botElim (φ := C₂.fill (.evar n ⊓ φ))))
  syllogism s₃ (syllogism s₄ contractionOr)

/-- **Classically, `singleton ⊢ singletonStrong`** by the same splitting argument. -/
def strong_of_singleton_lem (sg : HasSingleton Ax Γ) (lem : HasLem Ax Γ) : HasStrong Ax Γ :=
  fun C₁ C₂ n φ ψ =>
  let s₁ : Γ ⊩[Ax] .evar n ⊓ ψ ⇒ (.evar n ⊓ (φ ⊓ ψ)) ⊔ (.evar n ⊓ ~φ) :=
    syllogism (andIntro (idP _) (constImp (lem φ)))
      (syllogism distrib (orMono
        (andIntro (syllogism weakeningAnd weakeningAnd)
          (andIntro weakeningAnd' (syllogism weakeningAnd weakeningAnd')))
        (andMonoL weakeningAnd)))
  let s₂ := syllogism (ctxMono C₂ s₁) (ctxOr C₂)
  let s₃ := syllogism (andMonoR (χ := C₁.fill (.evar n ⊓ φ)) s₂) distrib
  let s₄ := orMono (weakeningAnd' (φ := C₁.fill (.evar n ⊓ φ)))
    (syllogism (sg C₁ C₂ n φ) (botElim (φ := C₂.fill (.evar n ⊓ (φ ⊓ ψ)))))
  syllogism s₃ (syllogism s₄ contractionOr)

end ProofCore

end IML
