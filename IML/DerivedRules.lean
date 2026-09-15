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
* `Fixpoint` — μ/ν pre-/post-fixpoint, induction/coinduction,
  monotonicity, `μX.X ⟺ ⊥`
* `Definedness` — definedness, membership, totality (§3.2 of the thesis),
  and the `SingletonPos` principle
* `Temporal` — one-path next, eventually, always, weak eventually
  (Proposition 5.6 of the thesis)
* `TopFilterModel` — a non-standard model of all 27 rules refuting
  ¬¬-propagation, DNE, `φ ⇒ ⌈φ⌉`, Membership¬(←) and the membership
  excluded middle: the proof system is incomplete for its Heyting semantics.
-/
