import IML.Crisp.HeytingSoundness
import IML.HeytingSoundness
import IML.CrispModels

/-!
# Bridge: the crisp development is the crisp fragment of the general one

The archived development `IML.Crisp` interprets element variables with
decidable equality; the current development `IML` interprets them through an
`L`-valued equality `E`, and recovers the crisp case as `IML.crispModel`.
This file proves that the two agree exactly:

* a crisp model `M : IML.Crisp.HModel` gives a general model `M.toGeneral`
  (`crispModel` on the same data), and a crisp valuation gives a general one
  (every predicate is extensional for crisp equality, `crisp_ext`);
* `hinterp_toGeneral`: the two interpretations coincide on every pattern;
* `hvalid_iff`: the two notions of validity coincide;
* `Proof.toGeneral`: every derivation in the archived proof system
  (`IML.Crisp.Proof`) is a derivation in the current one (`IML.Proof`);
* `soundness_of_general`: `IML.Crisp.soundness` is the crisp instance of
  `IML.soundness`.

The only case of `hinterp_toGeneral` with content is `μ`/`ν`: the general
fixpoints range over *extensional* pre- and post-fixpoints, the crisp ones over
all predicates, and `crisp_ext` shows the two index sets are the same.
-/

namespace IML.Crisp

variable {Symbol : Type} {L : Type*} [Order.Frame L]

-- ─────────────────────────────────────────────────────────────
-- Models and valuations
-- ─────────────────────────────────────────────────────────────

/-- The general model underlying a crisp model: `IML.crispModel` on the same
carrier, decidable equality, and symbol/application interpretations. -/
abbrev HModel.toGeneral (M : HModel Symbol L) : IML.HModel Symbol L :=
  @crispModel Symbol L _ M.Carrier M.decEq M.appInterp M.symInterp

/-- In the general model underlying a crisp model, every predicate is
extensional. -/
theorem HModel.toGeneral_ext (M : HModel Symbol L) (S : M.Carrier → L) :
    M.toGeneral.Ext S := by
  letI := M.decEq
  exact crisp_ext S

/-- A crisp valuation as a valuation of the underlying general model. -/
def HValuation.toGeneral {M : HModel Symbol L} (ρ : HValuation M) :
    IML.HValuation M.toGeneral where
  evar := ρ.evar
  svar := ρ.svar
  svar_ext i := M.toGeneral_ext (ρ.svar i)

/-- A valuation of the underlying general model as a crisp valuation
(the extensionality proof is forgotten). -/
def HValuation.ofGeneral {M : HModel Symbol L} (ρ : IML.HValuation M.toGeneral) :
    HValuation M where
  evar := ρ.evar
  svar := ρ.svar

theorem HValuation.toGeneral_ofGeneral {M : HModel Symbol L}
    (ρ : IML.HValuation M.toGeneral) : (HValuation.ofGeneral ρ).toGeneral = ρ := rfl

theorem HValuation.toGeneral_pushEVar {M : HModel Symbol L} (ρ : HValuation M)
    (a : M.Carrier) : (ρ.pushEVar a).toGeneral = ρ.toGeneral.pushEVar a := rfl

theorem HValuation.toGeneral_pushSVar {M : HModel Symbol L} (ρ : HValuation M)
    (S : M.Carrier → L) (hS : M.toGeneral.Ext S) :
    (ρ.pushSVar S).toGeneral = ρ.toGeneral.pushSVar S hS := rfl

-- ─────────────────────────────────────────────────────────────
-- The interpretations agree
-- ─────────────────────────────────────────────────────────────

/-- The crisp interpretation of a pattern is its general interpretation in the
underlying general model. -/
theorem hinterp_toGeneral (M : HModel Symbol L) (ρ : HValuation M)
    (φ : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ φ m = IML.hinterp M.toGeneral ρ.toGeneral φ m := by
  induction φ generalizing ρ m with
  | evar i => rfl
  | svar i => rfl
  | symbol s => rfl
  | bot => rfl
  | app φ ψ ihφ ihψ => simp only [hinterp_app, IML.hinterp_app, ihφ, ihψ]; rfl
  | impl φ ψ ihφ ihψ => simp only [hinterp_impl, IML.hinterp_impl, ihφ, ihψ]
  | conj φ ψ ihφ ihψ => simp only [hinterp_conj, IML.hinterp_conj, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [hinterp_disj, IML.hinterp_disj, ihφ, ihψ]
  | exist φ ih =>
    simp only [hinterp_exist, IML.hinterp_exist]
    congr 1; ext a
    rw [ih, HValuation.toGeneral_pushEVar]
  | forallP φ ih =>
    simp only [hinterp_forall, IML.hinterp_forall]
    congr 1; ext a
    rw [ih, HValuation.toGeneral_pushEVar]
  | mu φ ih =>
    change sInf _ = sInf _
    congr 1; ext x; simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨S, hpre, rfl⟩
      refine ⟨S, M.toGeneral_ext S, fun n => ?_, rfl⟩
      rw [← HValuation.toGeneral_pushSVar ρ S (M.toGeneral_ext S), ← ih]
      exact hpre n
    · rintro ⟨S, hS, hpre, rfl⟩
      refine ⟨S, fun n => ?_, rfl⟩
      rw [ih, HValuation.toGeneral_pushSVar ρ S hS]
      exact hpre n
  | nu φ ih =>
    change sSup _ = sSup _
    congr 1; ext x; simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨S, hpost, rfl⟩
      refine ⟨S, M.toGeneral_ext S, fun n => ?_, rfl⟩
      rw [← HValuation.toGeneral_pushSVar ρ S (M.toGeneral_ext S), ← ih]
      exact hpost n
    · rintro ⟨S, hS, hpost, rfl⟩
      refine ⟨S, fun n => ?_, rfl⟩
      rw [ih, HValuation.toGeneral_pushSVar ρ S hS]
      exact hpost n

-- ─────────────────────────────────────────────────────────────
-- Validity and soundness agree
-- ─────────────────────────────────────────────────────────────

/-- Crisp validity is general validity in the underlying general model. -/
theorem hvalid_iff (M : HModel Symbol L) (φ : Pattern Symbol) :
    HValid M φ ↔ IML.HValid M.toGeneral φ := by
  constructor
  · intro h ρ m
    exact (hinterp_toGeneral M (HValuation.ofGeneral ρ) φ m).symm.trans (h _ m)
  · intro h ρ m
    exact (hinterp_toGeneral M ρ φ m).trans (h _ m)

-- ─────────────────────────────────────────────────────────────
-- The archived proof system embeds into the current one
-- ─────────────────────────────────────────────────────────────

/-- Application contexts of the archived system as contexts of the current one. -/
def AppCtx.toGeneral : AppCtx Symbol → IML.AppCtx Symbol
  | .hole => .hole
  | .left C ψ => .left C.toGeneral ψ
  | .right ψ C => .right ψ C.toGeneral

theorem AppCtx.toGeneral_fill (C : AppCtx Symbol) (φ : Pattern Symbol) :
    C.toGeneral.fill φ = C.fill φ := by
  induction C with
  | hole => rfl
  | left C ψ ih => simp only [AppCtx.toGeneral, AppCtx.fill, IML.AppCtx.fill, ih]
  | right ψ C ih => simp only [AppCtx.toGeneral, AppCtx.fill, IML.AppCtx.fill, ih]

mutual
theorem SVarPositive.toGeneral {φ : Pattern Symbol} {n : SVarIndex} :
    SVarPositive φ n → IML.SVarPositive φ n
  | .evar => .evar
  | .svar => .svar
  | .svarNe h => .svarNe h
  | .symbol => .symbol
  | .app h₁ h₂ => .app h₁.toGeneral h₂.toGeneral
  | .bot => .bot
  | .impl h₁ h₂ => .impl h₁.toGeneral h₂.toGeneral
  | .conj h₁ h₂ => .conj h₁.toGeneral h₂.toGeneral
  | .disj h₁ h₂ => .disj h₁.toGeneral h₂.toGeneral
  | .exist h => .exist h.toGeneral
  | .forallP h => .forallP h.toGeneral
  | .mu h => .mu h.toGeneral
  | .nu h => .nu h.toGeneral

theorem SVarNegative.toGeneral {φ : Pattern Symbol} {n : SVarIndex} :
    SVarNegative φ n → IML.SVarNegative φ n
  | .evar => .evar
  | .svarNe h => .svarNe h
  | .symbol => .symbol
  | .app h₁ h₂ => .app h₁.toGeneral h₂.toGeneral
  | .bot => .bot
  | .impl h₁ h₂ => .impl h₁.toGeneral h₂.toGeneral
  | .conj h₁ h₂ => .conj h₁.toGeneral h₂.toGeneral
  | .disj h₁ h₂ => .disj h₁.toGeneral h₂.toGeneral
  | .exist h => .exist h.toGeneral
  | .forallP h => .forallP h.toGeneral
  | .mu h => .mu h.toGeneral
  | .nu h => .nu h.toGeneral
end

/-- Every derivation of the archived system is a derivation of the current
system, rule for rule. -/
def Proof.toGeneral {Γ : Set (Pattern Symbol)} :
    ∀ {φ : Pattern Symbol}, Proof Γ φ → IML.Proof Γ φ
  | _, .assumption h => .assumption h
  | _, .contractionOr => .contractionOr
  | _, .contractionAnd => .contractionAnd
  | _, .weakeningOr => .weakeningOr
  | _, .weakeningAnd => .weakeningAnd
  | _, .permutationOr => .permutationOr
  | _, .permutationAnd => .permutationAnd
  | _, .mp h₁ h₂ => .mp h₁.toGeneral h₂.toGeneral
  | _, .botElim => .botElim
  | _, .syllogism h₁ h₂ => .syllogism h₁.toGeneral h₂.toGeneral
  | _, .exportation h => .exportation h.toGeneral
  | _, .importation h => .importation h.toGeneral
  | _, .expansion h => .expansion h.toGeneral
  | _, .existQuant => .existQuant
  | _, .existGen h => .existGen h.toGeneral
  | _, .forallQuant => .forallQuant
  | _, .forallGen h => .forallGen h.toGeneral
  | _, .existence => .existence
  | _, .svSubst h => .svSubst h.toGeneral
  | _, .preFixpoint hp => .preFixpoint hp.toGeneral
  | _, .knasterTarski h => .knasterTarski h.toGeneral
  | _, .postFixpoint hp => .postFixpoint hp.toGeneral
  | _, .park h => .park h.toGeneral
  | _, .singleton (C₁ := C₁) (C₂ := C₂) (n := n) (φ := φ) => by
    rw [← AppCtx.toGeneral_fill C₁, ← AppCtx.toGeneral_fill C₂]
    exact .singleton (C₁ := C₁.toGeneral) (C₂ := C₂.toGeneral) (n := n) (φ := φ)
  | _, .propagationOrLeft => .propagationOrLeft
  | _, .propagationOrRight => .propagationOrRight
  | _, .propagationExistLeft => .propagationExistLeft
  | _, .propagationExistRight => .propagationExistRight
  | _, .framingLeft h => .framingLeft h.toGeneral
  | _, .framingRight h => .framingRight h.toGeneral

-- ─────────────────────────────────────────────────────────────
-- Validity and soundness agree
-- ─────────────────────────────────────────────────────────────

/-- `IML.Crisp.soundness` as the crisp instance of `IML.soundness`, through
the embedding `Proof.toGeneral` of the archived proof system. -/
theorem soundness_of_general {Γ : Set (Pattern Symbol)} {φ : Pattern Symbol}
    (h : Proof Γ φ) :
    ∀ (L : Type*) [Order.Frame L] (M : HModel Symbol L),
    (∀ γ ∈ Γ, HValid M γ) → HValid M φ := by
  intro L _ M hΓ
  exact (hvalid_iff M φ).mpr
    (IML.soundness h.toGeneral L M.toGeneral fun γ hγ => (hvalid_iff M γ).mp (hΓ γ hγ))

#print axioms hinterp_toGeneral
#print axioms soundness_of_general

end IML.Crisp
