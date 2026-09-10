import IML.HeytingSoundness
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

Given a topological space X with DecidableEq:
- Carrier = M (any type with DecidableEq)
- L = Opens X
- Patterns are interpreted as `M → Opens X`
  (each carrier element maps to an open set = "where it's true")

Evar interpretation: `⟦evar i⟧(m) = if m = ρ(i) then ⊤ else ⊥`
This is ⊤ = X (true everywhere) or ⊥ = ∅ (true nowhere),
NOT the singleton {m}. The "atomicity" is in the Carrier dimension,
not the topological dimension.
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
    HModel Symbol (Opens X) where
  Carrier := M
  decEq := inferInstance
  appInterp := appI
  symInterp := symI

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

This is precisely the Kripke semantics for intuitionistic logic,
extended with ML's application and fixpoints.

The soundness theorem for this instance gives Kripke soundness of iAML
as a special case.
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
