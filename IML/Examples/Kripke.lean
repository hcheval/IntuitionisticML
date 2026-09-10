import IML.HeytingSoundness
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Kripke semantics for iAML as an instance of Carrier → L

A Kripke frame (W, ≤) with constant domain M gives an HModel
with L = Opens (WithUpperSet W). Since opens of the upper set
topology are exactly the upper sets, truth values are
upward-closed subsets of W — i.e., persistent propositions.

The Kripke forcing relation `w ⊩ φ(m)` corresponds to
`w ∈ (hinterp M ρ φ m).carrier`.

## Key correspondences

| Kripke                              | Carrier → L                         |
|-------------------------------------|--------------------------------------|
| Frame (W, ≤)                        | L = Opens (WithUpperSet W)           |
| Domain M                            | Carrier = M                          |
| w ⊩ φ(m)                           | w ∈ (hinterp ... φ m).carrier       |
| ∀w'≥w, w'⊩φ → w'⊩ψ               | φ(m) ⇨ ψ(m) in Opens W             |
| ∃a∈M, w⊩φ[a/x]                    | ⨆ a, hinterp (pushEVar a) φ m      |
| lfp of monotone operator            | sInf of pre-fixpoints               |

Soundness of iAML over Kripke models follows from the general
`soundness` theorem by instantiation.
-/

namespace IML.Examples.Kripke

open TopologicalSpace Pattern Topology

-- ─────────────────────────────────────────────────────────────
-- Kripke frame and model
-- ─────────────────────────────────────────────────────────────

structure KripkeFrame where
  World : Type
  ord : Preorder World

structure KripkeModel (Symbol : Type) extends KripkeFrame where
  Carrier : Type
  decEq : DecidableEq Carrier
  appInterp : Carrier → Carrier → Carrier →
    Opens (WithUpperSet World)
  symInterp : Symbol → Carrier →
    Opens (WithUpperSet World)

attribute [instance] KripkeFrame.ord KripkeModel.decEq

-- ─────────────────────────────────────────────────────────────
-- Kripke model as HModel
-- ─────────────────────────────────────────────────────────────

def KripkeModel.toHModel {Symbol : Type} (K : KripkeModel Symbol) :
    HModel Symbol (Opens (WithUpperSet K.World)) where
  Carrier := K.Carrier
  decEq := K.decEq
  appInterp := K.appInterp
  symInterp := K.symInterp

-- ─────────────────────────────────────────────────────────────
-- Kripke forcing as membership in the open set
-- ─────────────────────────────────────────────────────────────

def forces {Symbol : Type} (K : KripkeModel Symbol)
    (ρ : HValuation K.toHModel)
    (w : WithUpperSet K.World) (φ : Pattern Symbol) (m : K.Carrier) : Prop :=
  w ∈ (hinterp K.toHModel ρ φ m).carrier

scoped notation w " ⊩[" K "," ρ "] " φ " @ " m => forces K ρ w φ m

-- ─────────────────────────────────────────────────────────────
-- Persistence (monotonicity): forcing is upward-closed
-- ─────────────────────────────────────────────────────────────

theorem forces_persistent {Symbol : Type} {K : KripkeModel Symbol}
    {ρ : HValuation K.toHModel}
    {w w' : WithUpperSet K.World} {φ : Pattern Symbol} {m : K.Carrier}
    (hle : w ≤ w') (hf : forces K ρ w φ m) :
    forces K ρ w' φ m := by
  have hopen := (hinterp K.toHModel ρ φ m).2
  rw [Topology.IsUpperSet.isOpen_iff_isUpperSet] at hopen
  exact hopen hle hf

-- ─────────────────────────────────────────────────────────────
-- Soundness for Kripke models
-- ─────────────────────────────────────────────────────────────

theorem kripke_soundness {Symbol : Type}
    {K : KripkeModel Symbol}
    {Γ : Set (Pattern Symbol)} {φ : Pattern Symbol}
    (h : Γ ⊩ᵢ φ)
    (hΓ : ∀ γ ∈ Γ, HValid K.toHModel γ) :
    HValid K.toHModel φ :=
  soundness h (Opens (WithUpperSet K.World)) K.toHModel hΓ

-- ─────────────────────────────────────────────────────────────
-- Forcing-level soundness: provable patterns are forced everywhere
-- ─────────────────────────────────────────────────────────────

theorem kripke_forces_valid {Symbol : Type}
    {K : KripkeModel Symbol}
    {φ : Pattern Symbol}
    (h : (∅ : Set (Pattern Symbol)) ⊩ᵢ φ) :
    ∀ (ρ : HValuation K.toHModel) (w : WithUpperSet K.World) (m : K.Carrier),
    forces K ρ w φ m := by
  intro ρ w m
  have hv := kripke_soundness h (fun _ hm => hm.elim) ρ m
  simp [forces, hv]

end IML.Examples.Kripke
