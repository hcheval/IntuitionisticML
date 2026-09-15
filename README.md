# Intuitionistic Matching Logic in Lean 4

A Lean 4 / Mathlib formalization accompanying the paper

> Horaţiu Cheval, *Complete Heyting algebra semantics for an intuitionistic version of Matching Logic*, FROM 2026 (extended abstract).

It defines an intuitionistic version of Applicative Matching Logic (iML), gives it a
semantics over complete Heyting algebras, and proves the proof system sound with
respect to that semantics. The soundness theorem is sorry-free and uses no axioms
beyond `propext`, `Classical.choice` and `Quot.sound`.

The formalized semantics is slightly more general than the paper's: equality on
the carrier is itself `L`-valued (the "total elements" case of a Fourman–Scott
Ω-set), and the paper's models are recovered as the *crisp* special case
(`IML/CrispModels.lean`). The extra generality is what makes it possible to
show that excluded middle for element variables, `x ∨ ¬x`, is **not derivable**
in iML (`IML/Examples/ExcludedMiddle.lean`); in the paper's models it is valid.

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
| `IML/Proof.lean` | §2.2, Fig. 1 | `SVarPositive`/`SVarNegative`, application contexts `AppCtx`, the Hilbert system `Proof` |
| `IML/HeytingSemantics.lean` | §2.1 | `HModel` (with `L`-valued equality `E`), extensionality `Extensional`/`HModel.Ext`, `HValuation`, the interpretation `hinterp : Pattern → Carrier → L`, the key lemma `hinterp_ext`, validity `HValid` |
| `IML/HInterpCommutation.lean` | §3, Lemma 2 | Substitution lemma: `hinterp_svarSubst`, `hinterp_evarSubst` |
| `IML/HeytingSoundness.lean` | §3, Lemma 1, Lemma 3, Theorem 2 | Monotonicity (`hinterp_mono_pos`/`hinterp_mono_neg`), `fill_le_iSup`, one validity lemma per rule, and `soundness` |
| `IML/LFPSoundness.lean` | §3 | Alternative treatment of the fixpoint rules via Mathlib's `OrderHom.lfp`/`OrderHom.gfp`, composed with the extensional hull `HModel.hull` (`soundness_lfp`) |
| `IML/CrispModels.lean` | §2.1 | The paper's models as the special case `crispModel` with `E a b = if a = b then ⊤ else ⊥`; in them element variables are crisp (`crispModel_evar_crisp`) |
| `IML/Examples/Kripke.lean` | — | Kripke models as the crisp instance `L = Opens (WithUpperSet W)`; forcing relation and persistence |
| `IML/Examples/OpenSets.lean` | — | Topological models `L = Opens X`; discrete and Alexandrov (constant-domain Kripke) instances |
| `IML/Examples/ExcludedMiddle.lean` | — | A non-crisp countermodel to `x ∨ ¬x` and the theorem `excludedMiddle_not_derivable` |

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

| Paper | Lean (`IML.Proof`) |
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
| SINGLETON | `singleton` |
| PREFIXPOINT | `preFixpoint`, `postFixpoint` |
| KNASTER-TARSKI | `knasterTarski`, `park` |
| SUBSTITUTION | `svSubst` |
| PROPAGATION∨ | `propagationOrLeft`, `propagationOrRight` |
| PROPAGATION∃ | `propagationExistLeft`, `propagationExistRight` |
| FRAMING | `framingLeft`, `framingRight` |

`assumption` (use of a hypothesis in Γ) has no named counterpart in the paper.

## Differences from the paper

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
- **Empty carrier.** `Carrier` is not required to be nonempty. With an empty
  carrier every pattern is vacuously valid, since `HValid` quantifies over the
  points of the carrier.

## Provenance

The proofs were produced largely autonomously by Claude (Opus 4.6 and 4.8)
running in Claude Code, with interactive guidance and review by the author.
