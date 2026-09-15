import IML.DerivedRules.Propositional
import IML.DerivedRules.FOL
import IML.DerivedRules.Context
import IML.DerivedRules.Fixpoint
import IML.DerivedRules.Definedness
import IML.DerivedRules.Temporal
import IML.DerivedRules.TopFilterModel

/-!
# Derived rules of iML and the expressivity survey

Umbrella module for the survey of Chen's thesis derivations in iML
(see `iml-expressivity-report.md` at the repository root).

* `Propositional` — IPC toolkit (`p1`, `p2`, pairing, `orElim`, De Morgan, …)
* `FOL` — quantifier rules, substitution–lifting cancellation
* `Context` — framing, propagation of `⊥`/`⊔`/`∃` through application
  contexts, the dual box `~C[~·]` and its (N) rule and converse Barcan
* `Fixpoint` — μ and ν pre- and post-fixpoint rules, induction/coinduction,
  monotonicity, `μX.X ⟺ ⊥`
* `Definedness` — definedness, membership, totality (§3.2 of the thesis).
  The positive SINGLETON rule `singletonStrong` (the primitive of
  `IML.Proof`) gives membership elimination, Membership∧, Lemma 3.8, 3.14,
  3.19 and Corollary 3.1 outright; these were conditional on a hypothesis
  `SingletonPos` when the negative rule was the primitive.
* `Temporal` — one-path next, eventually, always, weak eventually
  (Proposition 5.6 of the thesis)
* `TopFilterModel` — a non-standard model of all 27 rules of the *published*
  system (negative SINGLETON, `ProofCore singletonAx`) refuting
  ¬¬-propagation, DNE, `φ ⇒ ⌈φ⌉`, Membership¬(←) and the membership
  excluded middle: that system is incomplete for its Heyting semantics. The
  model refutes the positive rule (`cm_singletonStrong`), so it says nothing
  about the current system beyond witnessing that the positive rule is a
  genuine strengthening.
-/
