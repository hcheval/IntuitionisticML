import IML.SingletonAlt.Kernel
import IML.SingletonAlt.ProofCore
import IML.SingletonAlt.GModel
import IML.SingletonAlt.Countermodels

/-!
# The intuitionistic SINGLETON axiom: soundness and strength comparison

This umbrella module collects the results of `IML/SingletonAlt/` and audits their axioms.

## The three candidates

    singleton       ~(C₁[x ⊓ φ] ⊓ C₂[x ⊓ ~φ])                     (existing rule)
    singletonAlt    C₁[x ⊓ φ] ⊓ C₂[x] ⇒ C₂[x ⊓ φ]                   (proposed rule)
    singletonStrong C₁[x ⊓ φ] ⊓ C₂[x ⊓ ψ] ⇒ C₂[x ⊓ (φ ⊓ ψ)]         (strengthening)

## Results (all sorry-free)

The semantic rows are over the crisp semantics `IML.Crisp` (evars as singletons); see the
porting note in `Kernel.lean` for the `L`-valued-equality semantics of `IML.HeytingSemantics`.
The proof-theoretic rows are semantics-independent, and the countermodels use their own
generalized models (`GModel.lean`).

| Statement | Where | Method |
|---|---|---|
| Kernel lemma `⟦C[X]⟧ m = ⨆ a, ⟦X⟧ a ⊓ K_C a m` | `hinterp_fill` | induction on `C` |
| `singletonAlt` sound in every `HModel` | `hvalid_singletonAlt` | kernel lemma |
| `singletonStrong` sound in every `HModel` | `hvalid_singletonStrong` | kernel lemma |
| `ProofAlt` (iML with `singletonAlt`) sound | `soundnessAlt` | reuses `hvalid_*` |
| `C[⊥] ⇒ ⊥` derivable from `singletonAlt` | `botProp_of_alt` | derivation |
| `C[⊥] ⇒ ⊥` derivable from `singleton` | `botProp_of_singleton` | derivation |
| `singletonStrong ⊢ singletonAlt` | `alt_of_strong` | derivation |
| `singletonStrong ⊢ singleton` | `singleton_of_strong` | derivation |
| `singleton + LEM ⊢ singletonAlt` | `alt_of_singleton_lem` | derivation |
| `singleton + LEM ⊢ singletonStrong` | `strong_of_singleton_lem` | derivation |
| `singletonAlt + LEM + DNE ⊬ singleton` | `singleton_not_from_alt` | countermodel A (`Prop`) |
| `singletonAlt + LEM + DNE ⊬ singletonStrong` | `strong_not_from_alt` | corollary |
| `singleton ⊬ singletonAlt` (intuitionistic) | `alt_not_from_singleton` | countermodel B (`ℕ∞`) |
| `singleton ⊬ singletonStrong` (intuitionistic) | `strong_not_from_singleton` | corollary |

So the picture is:

* **Classically:** `singleton ⊣⊢ singletonStrong ⊢ singletonAlt`, and the last arrow does
  not reverse. `singletonAlt` is strictly weaker than the existing rule even with full
  classical logic.
* **Intuitionistically:** `singletonStrong ⊢ singleton` and `singletonStrong ⊢ singletonAlt`,
  but `singleton` and `singletonAlt` are incomparable. Excluded middle is exactly what is
  needed to get `singletonAlt` out of `singleton`.

Open (stated as a conjecture, not proved either way): whether `singleton + singletonAlt`
together derive `singletonStrong` intuitionistically.

## Recommendation

Adopt `singletonStrong`. It is sound (`hvalid_singletonStrong`), positive in form, and the
only one of the three that derives both of the others intuitionistically. `singletonAlt` on
its own is too weak: it cannot recover the existing rule even classically.
-/

namespace IML

#print axioms hinterp_fill
#print axioms hvalid_singletonAlt
#print axioms hvalid_singletonStrong
#print axioms soundnessAlt
#print axioms ProofCore.botProp_of_alt
#print axioms ProofCore.botProp_of_singleton
#print axioms ProofCore.singleton_of_strong
#print axioms ProofCore.alt_of_singleton_lem
#print axioms ProofCore.strong_of_singleton_lem
#print axioms gsoundness
#print axioms singleton_not_from_alt
#print axioms alt_not_from_singleton
#print axioms strong_not_from_alt
#print axioms strong_not_from_singleton

end IML
