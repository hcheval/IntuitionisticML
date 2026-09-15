import IML.HeytingSoundness
import IML.CrispModels
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.AlexandrovDiscrete

/-!
# Topological semantics for iAML: L = Opens X

`Opens X` forms a `Frame` (= complete Heyting algebra):
- `⊥ = ∅`, `⊤ = X`
- `U ⊓ V = U ∩ V`
- `U ⊔ V = U ∪ V`
- `⨆ Uᵢ = ⋃ Uᵢ` (arbitrary union of opens is open)
- `⨅ Uᵢ = interior(⋂ Uᵢ)` (intersection might not be open)
- `U ⇨ V = interior(Uᶜ ∪ V)` (Heyting implication)

This is NOT a Boolean algebra in general:
`U ⊔ (U ⇨ ⊥) ≠ ⊤` when U is open but not clopen
(`U ∪ interior(Uᶜ) ≠ X` in general).

## The model

Given a topological space X:
- Carrier = M (any type with DecidableEq)
- L = Opens X
- Patterns are interpreted as `M → Opens X`
  (each carrier element maps to an open set = "where it's true")

These are *crisp* models (`IML.crispModel`): equality on the carrier is
ordinary equality, so `⟦evar i⟧(m) = if m = ρ(i) then ⊤ else ⊥`.
This is ⊤ = X (true everywhere) or ⊥ = ∅ (true nowhere),
NOT the singleton {m}. The "atomicity" is in the Carrier dimension,
not the topological dimension. For a topological model with a genuinely
`Opens X`-valued equality see `IML.Examples.ExcludedMiddle`.
-/

namespace IML.Examples

open TopologicalSpace Pattern

-- ─────────────────────────────────────────────────────────────
-- Frame instance (from Mathlib)
-- ─────────────────────────────────────────────────────────────

instance (X : Type*) [TopologicalSpace X] : Order.Frame (Opens X) :=
  inferInstance

-- ─────────────────────────────────────────────────────────────
-- Topological HModel
-- ─────────────────────────────────────────────────────────────

def topologicalModel (Symbol : Type) (X : Type*) [TopologicalSpace X]
    (M : Type) [DecidableEq M]
    (appI : M → M → M → Opens X)
    (symI : Symbol → M → Opens X) :
    HModel Symbol (Opens X) :=
  crispModel Symbol (Opens X) M appI symI

theorem topological_soundness
    {Symbol : Type} {X : Type*} [TopologicalSpace X]
    {M : Type} [DecidableEq M]
    {appI : M → M → M → Opens X}
    {symI : Symbol → M → Opens X}
    {Γ : Set (Pattern Symbol)} {φ : Pattern Symbol}
    (h : Γ ⊩ᵢ φ)
    (hΓ : ∀ γ ∈ Γ, HValid (topologicalModel Symbol X M appI symI) γ) :
    HValid (topologicalModel Symbol X M appI symI) φ :=
  soundness h (Opens X) _ hΓ

-- ─────────────────────────────────────────────────────────────
-- Example 1: Sierpiński space (genuinely intuitionistic)
-- ─────────────────────────────────────────────────────────────

/-!
The Sierpiński space `S = {⊥, ⊤}` (two points, open sets = {∅, {⊤}, S}).
As a Frame, `Opens S ≅ {∅, {⊤}, {⊥,⊤}}` has 3 elements.
This is the simplest non-Boolean Heyting algebra.

Heyting operations:
- `{⊤} ⇨ ∅ = interior({⊥}) = ∅`
- So `{⊤} ⊔ ({⊤} ⇨ ∅) = {⊤} ⊔ ∅ = {⊤} ≠ S`
  → excluded middle fails!

We use `Prop` with the Sierpiński topology (via `OrderTopology`)
as a concrete realization: the opens of `Prop` ordered by `False < True`
are `{∅, {True}, Prop}`.
-/

-- Sierpiński space: Bool with order topology (false < true)
-- The opens are: ∅, {true}, {false, true}
-- This is the free frame on one generator.

-- ─────────────────────────────────────────────────────────────
-- Example 2: Discrete topology (recovers classical ML)
-- ─────────────────────────────────────────────────────────────

/-!
In the discrete topology, every subset is open, so `Opens X ≅ Set X`.
Heyting implication becomes Boolean: `U ⇨ V = interior(Uᶜ ∪ V) = Uᶜ ∪ V`.
So iAML over discrete spaces is just classical AML.
-/

def discreteModel (Symbol : Type)
    (M : Type) [DecidableEq M] [TopologicalSpace M] [DiscreteTopology M]
    (appI : M → M → M → Opens M)
    (symI : Symbol → M → Opens M) :
    HModel Symbol (Opens M) :=
  topologicalModel Symbol M M appI symI

-- ─────────────────────────────────────────────────────────────
-- Example 3: Alexandrov topology (= Kripke semantics)
-- ─────────────────────────────────────────────────────────────

/-!
For a preorder (W, ≤), the Alexandrov topology has as opens
exactly the upward-closed sets. Then `Opens W ≅ UpSet W`.

A topological iAML model over (W, ≤) with Carrier = M gives:
- Truth values = upward-closed subsets of W
- Pattern φ at carrier element m = an upward-closed set of "worlds
  where φ(m) holds"
- Persistence: if φ(m) holds at world w and w ≤ w', then φ(m) holds at w'

This is Kripke semantics with a *constant domain* (the same carrier M at
every world), extended with ML's application and fixpoints. It is not the
full Kripke semantics of intuitionistic predicate logic: because the
carrier does not vary with the world, this instance validates the
constant-domain axiom `∀x (p ∨ q(x)) → p ∨ ∀x q(x)`, which is not
intuitionistically valid. The general `Opens X` semantics is *not*
constant-domain in this sense: over a space such as ℝ, infima are
interiors of intersections, and the constant-domain axiom fails.

The soundness theorem for this instance gives soundness of iAML over
constant-domain Kripke models as a special case.
-/

-- Mathlib provides `AlexandrovDiscrete` for the Alexandrov topology.
-- For a preorder, `IsTopologicalBasis.isOpen_iff` shows opens = upper sets.

def alexandrovModel (Symbol : Type)
    (W : Type*) [TopologicalSpace W] [AlexandrovDiscrete W]
    (M : Type) [DecidableEq M]
    (appI : M → M → M → Opens W)
    (symI : Symbol → M → Opens W) :
    HModel Symbol (Opens W) :=
  topologicalModel Symbol W M appI symI

-- ─────────────────────────────────────────────────────────────
-- Non-example: why excluded middle fails topologically
-- ─────────────────────────────────────────────────────────────

/-!
In any non-discrete T₁ space X, there exists an open U with
`U ⊔ (U ⇨ ⊥) < ⊤` (excluded middle fails).

Proof sketch: Take any non-clopen open U.
- `U ⇨ ⊥ = interior(Uᶜ)`
- `U ∪ interior(Uᶜ) ⊆ U ∪ Uᶜ = X`
- But `U ∪ interior(Uᶜ) ≠ X` since `∂U = Uᶜ \ interior(Uᶜ) ≠ ∅`
  (the boundary is nonempty for non-clopen sets)

This is why axiom p3 (`(¬ψ → ¬φ) → φ → ψ`, equivalent to
excluded middle) is NOT sound over general topological models.
-/

end IML.Examples
