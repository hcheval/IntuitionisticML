import IML.DerivedRules.Propositional
import IML.DerivedRules.FOL
import IML.DerivedRules.Context
import IML.DerivedRules.Fixpoint
import IML.DerivedRules.Definedness
import IML.DerivedRules.EqualitySemantics
import IML.DerivedRules.Temporal
import IML.DerivedRules.TopFilterModel
import IML.DerivedRules.PointModel
import IML.DerivedRules.DepthOneModel

/-!
# Derived rules of iML and the expressivity survey

Umbrella module for the survey of the standard matching-logic derivations in
iML (see `iml-expressivity-report.md` at the repository root).

* `Propositional` — IPC toolkit (`p1`, `p2`, pairing, `orElim`, De Morgan, …)
* `FOL` — quantifier rules, substitution–lifting cancellation
* `Context` — framing, propagation of `⊥`/`⊔`/`∃` through application
  contexts, the dual box `~C[~·]` and its (N) rule and converse Barcan
* `Fixpoint` — μ and ν pre- and post-fixpoint rules, induction/coinduction,
  monotonicity, `μX.X ⟺ ⊥`
* `Definedness` — definedness, membership, totality. The positive SINGLETON
  rule `singletonStrong` (the primitive of `IML.Proof`) gives membership
  elimination, Membership∧, `C[φ] ⇒ ⌈φ⌉`, `φ ⇒ ⌈φ⌉` and
  `φ ⟺ ∃y. (⌈y ⊓ φ⌉ ⊓ y)` outright; these were conditional on a hypothesis
  `SingletonPos` when the negative rule was the primitive. Positive equality
  `φ =ⁱ ψ := ⌊φ ⟺ ψ⌋ⁱ` with reflexivity, symmetry, transitivity and
  Leibniz's law `eqI_leibniz` for holes of the shape `Q[A[P[□]]]`; the
  remaining gaps are isolated in the single principle `IsPred`
  ("`⌈·⌉`-patterns are predicate patterns").
* `EqualitySemantics` — `⟦x =ⁱ y⟧ = E ρ(x) ρ(y)`: positive equality is the
  Ω-set equality of the Heyting semantics.
* `Temporal` — one-path next, eventually, always, weak eventually
* `TopFilterModel` — a non-standard model of all 27 rules of the *published*
  system (negative SINGLETON, `ProofCore singletonAx`) refuting
  ¬¬-propagation, DNE, `φ ⇒ ⌈φ⌉`, Membership¬(←) and the membership
  excluded middle: that system is incomplete for its Heyting semantics. The
  model refutes the positive rule (`cm_singletonStrong`), so it says nothing
  about the current system beyond witnessing that the positive rule is a
  genuine strengthening.
* `PointModel` — small `HModel`s over a complete chain. Every `HModel` is a
  model of the current system, so these refute, *for the current system*,
  DNE, excluded middle, `⌊φ⌋ ⇒ φ` and equality elimination for the classical
  totality/equality, the membership excluded middle, the deduction theorem
  with `⌊·⌋`, `x = y ⇒ x ∈ y` for the classical equality, and the
  double-negation box laws for the temporal operators.
* `DepthOneModel` — a generalized model (`GModel`) that validates every rule
  of the current system **including `singletonStrong`** (`valid_strong`) and
  refutes ¬¬-propagation `C[~~φ] ⇒ ~~C[φ]`, the modal (K) rule for the dual
  box and `σᵈφ ⊓ σᵈψ ⇒ σᵈ(φ ⊓ ψ)`, all valid in every `HModel`: the current
  system is incomplete for its Heyting semantics.
-/
