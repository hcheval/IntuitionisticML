# Intuitionistic Matching Logic in Lean 4

A Lean 4 / Mathlib formalization accompanying the paper

> Horaţiu Cheval, *Complete Heyting algebra semantics for an intuitionistic version of Matching Logic*, FROM 2026 (extended abstract).

It defines an intuitionistic version of Applicative Matching Logic (iML), gives it a
semantics over complete Heyting algebras, and proves the proof system sound with
respect to that semantics. The soundness theorem is sorry-free and uses no axioms
beyond `propext`, `Classical.choice` and `Quot.sound`.

The formalization has since moved beyond the paper in two ways.

1. **Semantics.** Equality on the carrier is itself `L`-valued (the "total
   elements" case of a Fourman–Scott Ω-set), and the paper's models are
   recovered as the *crisp* special case (`IML/CrispModels.lean`). The extra
   generality is what makes it possible to show that excluded middle for
   element variables, `x ∨ ¬x`, is **not derivable** in iML
   (`IML/Examples/ExcludedMiddle.lean`); in the paper's models it is valid.

2. **Proof system.** The paper's SINGLETON rule is the classical negative form
   `¬(C₁[x ∧ φ] ∧ C₂[x ∧ ¬φ])`. The current system takes the *positive* form

   ```
   singletonStrong : C₁[x ∧ φ] ∧ C₂[x ∧ ψ] → C₂[x ∧ (φ ∧ ψ)]
   ```

   as primitive and derives the negative one (`IML.Proof.singleton`, with the
   signature the constructor used to have). Intuitionistically the positive
   rule is strictly stronger: the negative rule does not derive it
   (`IML.strong_not_from_singleton`, a semantic independence proof in
   `IML/SingletonAlt/`), while it derives the negative rule and is sound for
   the Heyting semantics (`IML.hvalid_singletonStrong`). It is exactly what the
   definedness theory needs: membership elimination `⌈x ∧ φ⌉ → x → φ`,
   Membership∧, `C[φ] → ⌈φ⌉` and `φ → ⌈φ⌉` are underivable with the negative
   rule (`IML.TopFilter.phi_impl_ceil_not_derivable`) and derivable with the
   positive one (`IML/DerivedRules/Definedness.lean`). Classically the two
   rules are interderivable, so nothing changes for classical AML.

The repository therefore contains **two developments**, both sorry-free:

- **`IML/Crisp/`** — the original development, as it accompanied the paper:
  its proof system (`IML/Crisp/Proof.lean`, with the negative SINGLETON) and
  its semantics. Models carry ordinary decidable equality and an element
  variable is interpreted as `⟦x⟧(m) = if m = ρ(x) then ⊤ else ⊥`. The files
  are preserved verbatim (only the namespace, `IML.Crisp`, and the internal
  imports changed), and this is the development the paper's text corresponds
  to. Its main theorem is `IML.Crisp.soundness`, stated over its own proof
  system, so the archive is self-contained.
- **`IML/`** — the current, generalized development: positive SINGLETON and
  `L`-valued equality. The paper's models are its crisp instances
  (`IML/CrispModels.lean`). Its main theorem is `IML.soundness`.

The bridge in `IML/Crisp/Bridge.lean` relates them on both sides. Every
derivation of the archived system is one of the current system
(`IML.Crisp.Proof.toGeneral`; only the SINGLETON case has content). A crisp
model `M` determines the general model `M.toGeneral := crispModel ...`, and

```lean
theorem hinterp_toGeneral (M : Crisp.HModel Symbol L) (ρ : Crisp.HValuation M)
    (φ : Pattern Symbol) (m : M.Carrier) :
    Crisp.hinterp M ρ φ m = hinterp M.toGeneral ρ.toGeneral φ m

theorem hvalid_iff (M : Crisp.HModel Symbol L) (φ : Pattern Symbol) :
    Crisp.HValid M φ ↔ HValid M.toGeneral φ
```

so the crisp development is exactly the crisp fragment of the general one, and
`IML.Crisp.soundness_of_general` derives the statement of `IML.Crisp.soundness`
from `IML.soundness` through `Proof.toGeneral`. The only case of
`hinterp_toGeneral` with content is `μ`/`ν`, where the general fixpoints range
over extensional pre- and post-fixpoints and the crisp ones over all
predicates; `crisp_ext` shows the two index sets coincide.

## Building

Requires the toolchain in `lean-toolchain` (Lean 4.30.0-rc2) and `elan`.

```
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

## Contents

| File | Paper | What it contains |
|---|---|---|
| `IML/Pattern.lean` | §2 | The 12-constructor `Pattern` type, de Bruijn indices, notations |
| `IML/Substitution.lean` | §2 | Lifting and substitution for element and set variables |
| `IML/Proof.lean` | §2.2, Fig. 1 (SINGLETON differs) | `SVarPositive`/`SVarNegative`, application contexts `AppCtx`, the Hilbert system `Proof` with the positive `singletonStrong`, and the derived rules `Proof.singletonAlt`, `Proof.botProp`, `Proof.singleton` (the paper's SINGLETON) |
| `IML/HeytingSemantics.lean` | §2.1 | `HModel` (with `L`-valued equality `E`), extensionality `Extensional`/`HModel.Ext`, `HValuation`, the interpretation `hinterp : Pattern → Carrier → L`, the key lemma `hinterp_ext`, validity `HValid` |
| `IML/HInterpCommutation.lean` | §3, Lemma 2 | Substitution lemma: `hinterp_svarSubst`, `hinterp_evarSubst` |
| `IML/HeytingSoundness.lean` | §3, Lemma 1, Lemma 3, Theorem 2 | Monotonicity (`hinterp_mono_pos`/`hinterp_mono_neg`), the context kernel lemma `hinterp_fill` (`⟦C[X]⟧ m = ⨆ a, ⟦X⟧ a ⊓ K_C a m`), `hvalid_singletonStrong`, one validity lemma per rule, and `soundness` |
| `IML/LFPSoundness.lean` | §3 | Alternative treatment of the fixpoint rules via Mathlib's `OrderHom.lfp`/`OrderHom.gfp`, composed with the extensional hull `HModel.hull` (`soundness_lfp`) |
| `IML/CrispModels.lean` | §2.1 | The paper's models as the special case `crispModel` with `E a b = if a = b then ⊤ else ⊥`; in them element variables are crisp (`crispModel_evar_crisp`) |
| `IML/Crisp/Proof.lean` | §2.2, Fig. 1 (as published) | The original proof system with the negative SINGLETON `singleton` — namespace `IML.Crisp`, text preserved |
| `IML/Crisp/HeytingSemantics.lean` | §2.1 (as published) | The original `HModel` with decidable equality, `HValuation`, `hinterp`, `HValid` — namespace `IML.Crisp`, text preserved |
| `IML/Crisp/HInterpCommutation.lean` | §3, Lemma 2 (as published) | The original substitution lemmas `hinterp_svarSubst`, `hinterp_evarSubst` |
| `IML/Crisp/HeytingSoundness.lean` | §3, Theorem 2 (as published) | The original monotonicity lemmas, validity lemmas, and `IML.Crisp.soundness` |
| `IML/Crisp/LFPSoundness.lean` | §3 (as published) | The original lfp/gfp treatment of the fixpoint rules (`IML.Crisp.soundness_lfp`) |
| `IML/Crisp/Bridge.lean` | — | The bridge: `Proof.toGeneral` (archived derivations are current derivations), `hinterp_toGeneral`, `hvalid_iff`, and `soundness_of_general` (the crisp soundness theorem as an instance of the general one) |
| `IML/Examples/Kripke.lean` | — | Kripke models as the crisp instance `L = Opens (WithUpperSet W)`; forcing relation and persistence |
| `IML/Examples/OpenSets.lean` | — | Topological models `L = Opens X`; discrete and Alexandrov (constant-domain Kripke) instances |
| `IML/Examples/ExcludedMiddle.lean` | — | A non-crisp countermodel to `x ∨ ¬x` and the theorem `excludedMiddle_not_derivable` |
| `IML/SingletonAlt/` | — | The three singleton rules compared: soundness of the positive variants, `ProofCore` (iML with a pluggable singleton scheme), and the independence results `singleton ⊬ singletonStrong` (intuitionistically) and `singletonAlt ⊬ singleton` (even classically); see `IML/SingletonAlt.lean` |
| `IML/DerivedRules/` | — | Derived rules (propositional, first-order, contexts, fixpoints, definedness and membership, temporal) and the top-filter model, a non-standard model of the *published* system showing it incomplete for its Heyting semantics; see `IML/DerivedRules.lean` |

The main theorem is `IML.soundness` in `IML/HeytingSoundness.lean`:

```lean
theorem soundness {Γ : Set (Pattern Symbol)} {φ : Pattern Symbol}
    (h : Γ ⊩ᵢ φ) :
    ∀ (L : Type*) [Order.Frame L] (M : HModel Symbol L),
      (∀ γ ∈ Γ, HValid M γ) → HValid M φ
```

`Order.Frame` is Mathlib's name for a complete Heyting algebra. The algebra `L`
is a parameter of `HModel`, so every model carries its own algebra of truth
values, as in the paper.

The second main theorem is `IML.Examples.ExcludedMiddle.excludedMiddle_not_derivable`:

```lean
theorem excludedMiddle_not_derivable (Symbol : Type) :
    ¬ Nonempty ((∅ : Set (Pattern Symbol)) ⊩ᵢ (Pattern.evar 0 ⊔ ~(Pattern.evar 0)))
```

It follows from `soundness` and a concrete model
(`IML.Examples.ExcludedMiddle.counterModel`): carrier `Bool`, truth values the
three upper sets of the two-point Kripke frame `0 ≤ 1`, and equality between
the two distinct elements interpreted as the open `{1}`. Both theorems use only
`propext`, `Classical.choice` and `Quot.sound`.

## Proof rules: paper name to Lean constructor

The paper describes the archived system `IML.Crisp.Proof`, whose constructors
carry exactly these names. The current `IML.Proof` has the same constructors
except for SINGLETON.

| Paper | Lean (`IML.Crisp.Proof` and, unless noted, `IML.Proof`) |
|---|---|
| CONTRACTION | `contractionOr`, `contractionAnd` |
| WEAKENING | `weakeningOr`, `weakeningAnd` |
| PERMUTATION | `permutationOr`, `permutationAnd` |
| MODUS PONENS | `mp` |
| SYLLOGISM | `syllogism` |
| EXPORTATION | `exportation` |
| IMPORTATION | `importation` |
| EXPANSION | `expansion` |
| QUANTIFIER | `existQuant`, `forallQuant` |
| QUANTIFIER RULE | `existGen`, `forallGen` |
| EXISTENCE | `existence` |
| SINGLETON | `singleton` in `IML.Crisp.Proof`; in `IML.Proof` the primitive is the positive `singletonStrong` and `singleton` is a derived definition with the same signature |
| PREFIXPOINT | `preFixpoint`, `postFixpoint` |
| KNASTER-TARSKI | `knasterTarski`, `park` |
| SUBSTITUTION | `svSubst` |
| PROPAGATION∨ | `propagationOrLeft`, `propagationOrRight` |
| PROPAGATION∃ | `propagationExistLeft`, `propagationExistRight` |
| FRAMING | `framingLeft`, `framingRight` |

`assumption` (use of a hypothesis in Γ) has no named counterpart in the paper.

## Differences from the paper

- **SINGLETON.** The paper's rule is the classical negative form
  `¬(C₁[x ∧ φ] ∧ C₂[x ∧ ¬φ])`, kept as the constructor `singleton` of the
  archived `IML.Crisp.Proof`. The current `IML.Proof` takes the positive
  `singletonStrong : C₁[x ∧ φ] ∧ C₂[x ∧ ψ] → C₂[x ∧ (φ ∧ ψ)]` as primitive.
  The reasons: (i) it is sound for the Heyting semantics, by the same
  extensionality argument as the negative rule (`hvalid_singletonStrong`,
  via the context kernel lemma `hinterp_fill`); (ii) it derives the negative
  rule intuitionistically (`Proof.singleton`), but not conversely
  (`IML.strong_not_from_singleton`: a model of the negative rule refutes the
  positive one), so it is a genuine strengthening, whereas classically the two
  are interderivable; (iii) it is what the definedness theory of Chen's
  thesis needs intuitionistically — with the negative rule alone, `φ → ⌈φ⌉`
  is underivable (`IML.TopFilter.phi_impl_ceil_not_derivable`), with the
  positive rule membership elimination, Membership∧ and `C[φ] → ⌈φ⌉` are
  derived in `IML/DerivedRules/Definedness.lean`. Every derivation of the
  archived system is a derivation of the current one
  (`IML.Crisp.Proof.toGeneral`).
- **Bottom.** The paper defines `⊥ := μX. X` and derives `⊥ → φ` from
  KNASTER-TARSKI. The formalization takes `bot` as a primitive constructor with
  its own rule `botElim`. This is a convenience; nothing in the soundness proof
  depends on it.
- **Variables.** The formalization uses de Bruijn indices for both element and
  set variables. Binders `∃ₑ`, `∀ₑ`, `μ`, `ν` bind index 0. Side conditions
  such as `x ∉ FV(ψ)` are expressed by lifting (`evarLift ψ`) rather than by
  freshness hypotheses.
- **Positivity.** In the paper, positivity of `φ` in `X` is a well-formedness
  condition on forming `μX. φ`. Here `Pattern` allows any `μ φ`, and the
  PREFIXPOINT rules carry `SVarPositive φ 0` as an explicit hypothesis.
  Without positivity, `hinterp (μ φ)` is still defined (as an infimum of
  prefixpoints) but need not be a fixed point.
- **Application contexts.** `AppCtx.left C ψ` is the paper's `C ψ` and
  `AppCtx.right ψ C` is `ψ C`.
- **Equality.** In the paper, an element variable `x` is interpreted at `m` as
  `⊤` if `m = ρ(x)` and `⊥` otherwise, so element variables are crisp and
  `x ∨ ¬x` is valid in every model. The formalization equips a model with an
  `L`-valued equality `E : Carrier → Carrier → L` that is reflexive
  (`E a a = ⊤`), symmetric and transitive, and interprets `x` at `m` as
  `E m ρ(x)`. Symbol and application interpretations, set-variable valuations,
  and the pre- and post-fixpoints over which `μ`/`ν` range are all required to
  be *extensional* (`E a b ⊓ S a ≤ S b`); every interpretation is then
  extensional (`hinterp_ext`), and SINGLETON is sound for that reason.
  EXISTENCE uses reflexivity. No other rule mentions `E`. The paper's models
  are exactly the crisp models `crispModel` of `IML/CrispModels.lean`, for
  which every predicate is extensional and no side conditions are needed.
  The original development with decidable equality is kept unchanged under
  `IML/Crisp/`, and `IML/Crisp/Bridge.lean` proves the two agree on crisp
  models.
- **Empty carrier.** `Carrier` is not required to be nonempty. With an empty
  carrier every pattern is vacuously valid, since `HValid` quantifies over the
  points of the carrier.

## Provenance

The proofs were produced largely autonomously by Claude (Opus 4.6 and 4.8)
running in Claude Code, with interactive guidance and review by the author.
