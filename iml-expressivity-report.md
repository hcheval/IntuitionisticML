# Which of Chen's matching-logic derivations survive in intuitionistic AML?

Survey of the syntactic, theory-building derivations of Xiaohong Chen's PhD thesis
(*Matching µ-Logic*, 2023, chapters 3–5 and 7) against the iML proof system of
`IML/Proof.lean`, backed where indicated by Lean proofs in
`IML/DerivedRules/*.lean` (sorry-free, standard axioms only).

**Which proof system.** The verdicts below are about the *current* system
`IML.Proof`: 27 rules, classical AML minus `p3`, with `∧, ∨, ∀, ν, ⇒, ⊥`
primitive, and with the **positive SINGLETON**

    singletonStrong : C₁[x ⊓ φ] ⊓ C₂[x ⊓ ψ] ⇒ C₂[x ⊓ (φ ⊓ ψ)]

as the application axiom. The published system (archived verbatim as
`IML.Crisp.Proof`) had the classical negative form `~(C₁[x ⊓ φ] ⊓ C₂[x ⊓ ~φ])`
instead; the current system derives it (`IML.Proof.singleton`) and is strictly
stronger intuitionistically (`IML.strong_not_from_singleton`), while both are
sound for the Heyting semantics (`IML.hvalid_singletonStrong`). A first version
of this survey was written against the published system and used the top-filter
model (`IML/DerivedRules/TopFilterModel.lean`) for its impossibility proofs. That
model refutes the positive rule (`IML.TopFilter.cm_singletonStrong`), so it
proves nothing about the current system; every underivability claim below has
been re-established with a model that validates `singletonStrong`, or
downgraded. Where a verdict changed with the change of primitive the row says
so — the change of primitive is itself one of the results.

Verdict codes:

* **(a)** derivable — ported with a Lean proof, or, where marked *paper*, an
  on-paper derivation using only rules already ported.
* **(b)** classical, but a constructively meaningful variant goes through — the
  variant is stated and the weakening named.
* **(c)** genuinely missing. Sub-labelled **(c!)** when underivability is *proved*
  (by a Lean countermodel of the current system, or by unsoundness for the
  Heyting semantics), and **(c?)** when I could not derive it and no natural
  variant works, but underivability is not proved.

"Lean" in the last column means the verdict is backed by a checked proof (name in
`IML.…`); "paper" means an on-paper judgement.

## 0. Headline findings

1. **⊥-propagation is derivable.** `C[⊥] ⇒ ⊥` needs no new rule: Mircea Sebe's
   classical proof (thesis Prop. 3.3(1)) uses only `⊥ ⇒ ·`, framing, pairing and
   SINGLETON, all intuitionistic. Lean: `IML.ctxBot` (`IML.Proof.botProp`;
   its only axiom is `propext`, from the rewrite that lifts the context past
   the binder). Taking `⊥ := µX.X` instead of a primitive `⊥` changes nothing
   (`IML.muSvarIffBot`).

2. **The current system is incomplete for its Heyting semantics.** The
   ¬¬-propagation `C[~~φ] ⇒ ~~C[φ]` is valid in every `HModel`
   (`⨆ ¬¬φ(a) ⊓ R ≤ ¬¬⨆ φ(a) ⊓ R`) but **not derivable**: Lean
   `IML.DepthOne.nnPropagation_not_derivable`. The proof is the *depth-one
   model* (`IML/DerivedRules/DepthOneModel.lean`): a generalized model
   (`GModel`, admissible valuations and a twisted application) with two-point
   carrier, one-step application relation and the twist `j` (`j u = ⊤` iff
   `u = ⊤`), which **validates every rule of the current system including the
   positive SINGLETON** — `IML.DepthOne.valid_strong` — hence, by
   `IML.gsoundness`, every derivation. Its trick is that an application context
   never lands on the point it looks at, so the "inflationary" SINGLETON
   instances that break the top-filter model are vacuous. Over the five-element
   frame `L₅` of down-sets of the poset `q, r < p` (join-prime top, not a chain)
   the same model also refutes
   * the modal (K) rule `σᵈ(φ ⇒ ψ) ⇒ σᵈφ ⇒ σᵈψ` for the dual box
     `σᵈφ := ~(σ ⬝ ~φ)` — `boxK_not_derivable`;
   * `σᵈφ ⊓ σᵈψ ⇒ σᵈ(φ ⊓ ψ)` — `boxAnd_not_derivable`.

   The model does not satisfy the definedness axiom `∀x.⌈x⌉`, and no model of
   this kind can while validating `singletonStrong` (item 4). The
   incompleteness therefore concerns the pure system; whether the current system
   is complete for the *definedness theory* is open.

3. **The deduction theorem (thesis Thm 3.3 / 4.2) is false for iML**, in the
   current system as well: `IML.PointModel.deductionTheorem_fails`. From
   `Γ ∪ {c ⊔ ~c} ⊢ c ⊔ ~c` it would give `Γ ⊢ ⌊c ⊔ ~c⌋ ⇒ c ⊔ ~c`; but
   `⌊c ⊔ ~c⌋ = ~⌈~(c ⊔ ~c)⌉` *is* derivable, so excluded middle would be, and a
   one-point chain-valued `HModel` refutes it. The classical totality
   `⌊ψ⌋ := ~⌈~ψ⌉` is the wrong notion: its Heyting value is `⨅_a ¬¬ψ(a)`. The
   right one is the positive `⌊ψ⌋ⁱ := ∀x. x ∈ ψ` (value `⨅_a ψ(a)`):
   `⌊ψ⌋ⁱ ⇒ ⌊ψ⌋` and, with the positive SINGLETON, `⌊ψ⌋ⁱ ⇒ ψ` (Lemma 3.8,
   `IML.totalI_impl`) are derivable. The deduction theorem with `⌊·⌋ⁱ` is
   still not derived; its framing case needs `⌊ψ⌋ⁱ` to be a predicate pattern
   (item 4).

4. **The positive SINGLETON recovers most of §3.2, and what is left is one
   principle.** In the published system the membership calculus hinged on the
   membership excluded middle `⌈x⌉ ⇒ ⌈x ⊓ φ⌉ ⊔ ⌈x ⊓ ~φ⌉`, which is unsound
   (`IML.PointModel.memEM_not_derivable`), and `φ ⇒ ⌈φ⌉` was underivable
   (`IML.TopFilter.phi_impl_ceil_not_derivable`). With `singletonStrong` the
   following are now **derivable outright**: membership elimination
   `⌈x ⊓ φ⌉ ⇒ x ⇒ φ` (`ceil_evar_impl`), Lemma 3.8 `⌊φ⌋ⁱ ⇒ φ`
   (`totalI_impl`), Membership∧ in both directions (`memAnd`), Membership⇒
   (`memImplElim`), Lemma 3.14 `C[φ] ⇒ ⌈φ⌉` and Corollary 3.1 `φ ⇒ ⌈φ⌉`
   (`ctxImplDefined`, `phi_impl_ceil`), Lemma 3.19 in both directions
   (`existCeilEvar_iff`), Lemma 3.17(→) (`ctx_mem_elim`), idempotence
   `⌈⌈φ⌉⌉ ⟺ ⌈φ⌉`, and the propagation of positive totality into contexts
   `⌊χ⌋ⁱ ⊓ C[ψ] ⇒ C[χ ⊓ ψ]` (`totalI_ctx`). What remains — Membership¬(←),
   Membership⇒(←), Lemma 3.9(→), Lemma 3.17(←), Lemma 3.18/3.20, the
   deduction theorem with `⌊·⌋ⁱ` — all reduce (Lean: `*_of_pred`) to a single
   sound principle, that `⌈·⌉`-patterns are *predicate patterns*:

       IsPred θ  :=  θ ⇒ ⌊θ⌋ⁱ,      wanted for θ = ⌈φ⌉, ~⌈φ⌉, ⌈φ⌉ ⇒ ⌈ψ⌉.

   Semantically `IsPred θ` says `θ` has the same value at every point; it is
   valid in every `HModel`. I could neither derive `⌈φ⌉ ⇒ ⌊⌈φ⌉⌋ⁱ` nor refute
   it, and there is a structural reason no countermodel of the `GModel` kind
   exists (paper): if a generalized model validates `singletonStrong` *and* the
   definedness axiom, the instances `x ⊓ φ ⊓ ⌈x ⊓ ψ⌉ ⇒ ⌈x ⊓ (φ ⊓ ψ)⌉` and
   `⌈x ⊓ φ⌉ ⊓ x ⇒ x ⊓ φ` at the point of `x` force the twist to be the
   identity on all pattern values, and the instances with `C₁ = ⌈□⌉`, `C₂ = □`
   force every admissible element denotation `X` to satisfy
   `X a ⊓ X b ⊓ φ a ≤ φ b` for every pattern value `φ`, i.e. to be an
   `E`-singleton for `E a b := ⨆_X X a ⊓ X b`. Such a model is an Ω-set model in
   the sense of `IML/HeytingSemantics.lean`, in which every sound statement
   holds. Settling `IsPred ⌈φ⌉` therefore needs either a derivation or a
   genuinely different semantics (Kripke-style with varying domains, or
   proof-theoretic).

5. **Positive equality.** `φ =ⁱ ψ := ⌊φ ⟺ ψ⌋ⁱ` is reflexive, symmetric,
   transitive (`eqI_trans`), implies the classical `⌊φ ⟺ ψ⌋`, and satisfies
   Leibniz's law `(φ =ⁱ ψ) ⊓ C[φ] ⇒ C[ψ]` (`eqI_leibniz`) for every hole of the
   shape `Q[A[P[□]]]` — an application-free context `Q` (with `⊓, ⊔`, both
   sides of `⇒`, `∃`, `∀`) above an application context `A` above an
   application-free context `P`. Not covered: holes under `µ`/`ν`, and holes
   below two application layers separated by a non-application connective; both
   need `IsPred ⌊θ⌋ⁱ`. The classical equality `⌊φ ⟺ ψ⌋` has *no* elimination
   rule (`IML.PointModel.eqML_elim_not_derivable`) and does not give membership
   (`eqML_mem_not_derivable`), while `x =ⁱ φ ⇒ x ∈ φ` is derivable
   (`eqI_impl_mem`). Semantically, in every model with standard definedness,
   `⟦x =ⁱ y⟧ = E ρ(x) ρ(y)` — positive equality is exactly the Ω-set equality of
   the Heyting semantics (`IML.hinterp_eqI_evar`), and soundness of
   `singletonStrong` (extensionality of every interpretation) is the semantic
   form of Leibniz's law.

6. **The defined box `◦ := ~•~` is the double-negation box.** Its Heyting value
   is `⨅_b (R(b,m) ⇨ ¬¬φ(b))`, so the universal side of Chapter 5 degrades. Now
   *proved* underivable in the current system: (K) for `◦` (item 2),
   `◦φ ⊓ ◦ψ ⇒ ◦(φ ⊓ ψ)` (item 2), `◦φ₁ ⊓ •φ₂ ⇒ •(φ₁ ⊓ φ₂)` and
   `◦(φ₁ ⇒ φ₂) ⊓ •φ₁ ⇒ •φ₂` (Prop. 5.6(18), (19), unsound:
   `IML.PointModel.allnx_nx_and_not_derivable`, `allnx_nx_impl_not_derivable`)
   and the LTL rule (Fun→) `•⊤ ⊢ ◦φ ⇒ •φ` (`allnx_impl_nx_not_derivable`).
   The Barcan formula `∀x.◦φ ⇒ ◦∀x.φ` is the double negation shift (unsound in
   `Opens ℝ`, paper). LTL's (Ind), (K□), CTL's AX/AU rules, DL's (DL1)/(DL7) and
   RL's (Circularity) all pass through one of these and do not port. The
   existential side (`•, ⋄, ⋄w`, Knaster–Tarski induction, Peano induction)
   ports verbatim. Remedy: with definedness the intuitionistic box is definable
   as `◦ⁱφ := ∀y. (•y ⇒ y ∈ φ)` (value `⨅_b (R(b,m) ⇨ φ(b))`); without
   definedness it is not expressible, which argues for a primitive "all-path"
   application.

7. **Fixpoint reasoning ports completely.** With `ν` primitive Chapter 4 is
   symmetric in µ/ν (`IML/DerivedRules/Fixpoint.lean`).

## 1. The propositional and first-order basis (thesis §3.1, "FOL reasoning")

| # | Derivation | Verdict | Where classicality enters | Evidence |
|---|---|---|---|---|
| 1 | Axioms p1, p2 | (a) | — | Lean `p1`, `p2` |
| 2 | Axiom p3 `~~φ ⇒ φ` | (c!) | unsound in Heyting models | Lean `PointModel.dne_not_derivable` (one-point chain model; replaces the top-filter proof) |
| 3 | pairing, S-combinator, `orElim`, distributivity, `curry/uncurry`, `flip` | (a) | — | Lean `implAnd`, `implMp`, `orElim`, `andOrDistrib`, … |
| 4 | De Morgan `~(φ⊔ψ) ⟺ ~φ⊓~ψ`, `~φ⊔~ψ ⇒ ~(φ⊓ψ)`, `φ⊓~ψ ⇒ ~(φ⇒ψ)`, `~(φ⇒ψ) ⇒ ~ψ` | (a) | — | Lean `notOr`, `notOrIntro`, `notAndOfNotOr`, `andToNotImpl`, `notImplRight` |
| 5 | `~(φ⊓ψ) ⇒ ~φ⊔~ψ`, `~(φ⇒ψ) ⇒ φ`, `φ ⊔ ~φ` | (c!) | EM | evar-EM refuted in `IML/Examples/ExcludedMiddle.lean` (`excludedMiddle_not_derivable`), symbol-EM from definedness Lean `PointModel.em_not_derivable`; the other two unsound (paper) |
| 6 | `~~` is a modality: `~~(φ⇒ψ) ⇒ ~~φ ⇒ ~~ψ`, `~~φ⊓~~ψ ⇒ ~~(φ⊓ψ)`, `~~(φ⊔~φ)` | (a) | — | Lean `nnImpl`, `nnAnd`, `nnExcludedMiddle` |
| 7 | ∃-intro/elim, ∀-intro/elim, `existMono`, `forallMono`, `∀ ⇒ ∃` | (a) | — | Lean (FOL.lean) |
| 8 | `~∃φ ⟺ ∀~φ`, `∃~φ ⇒ ~∀φ`, `∃φ ⇒ ~∀~φ` | (a) | — | Lean `negExist`, `forallNeg`, `existNeg`, `existToNotForallNot` |
| 9 | `~∀φ ⇒ ∃~φ`, `~∀~φ ⇒ ∃φ` | (c!) | DNE | unsound (paper) |
| 10 | `∀(φ⊓ψ) ⟺ ∀φ⊓∀ψ`, `∃(φ⊔ψ) ⟺ ∃φ⊔∃ψ`, `∀(φ⇒ψ) ⇒ ∀φ⇒∀ψ`, lifted variants | (a) | — | Lean (FOL.lean) |
| 11 | `(φ ⇒ ∃ψ) ⇒ ∃(φ ⇒ ψ)` (classical `existImplLiftRight`) | (c!) | independence of premise | unsound: in `L=[0,1]`, `a ⇨ ⨆b_i = ⊤` but `⨆(a ⇨ b_i) = a` (paper) |
| 12 | `∀~~φ ⇒ ~~∀φ` (DNS) | (c!) | — | unsound in `Opens ℝ` (paper); converse `~~∀φ ⇒ ∀~~φ` Lean `nnForallToForallNn` |

## 2. Application contexts and the modal reading (thesis §3.1.2–3.1.3)

| # | Thesis | Statement | Verdict | Notes | Evidence |
|---|---|---|---|---|---|
| 13 | Prop 3.2 | framing through any context | (a) | | Lean `ctxFraming` |
| 14 | Prop 3.3(1) | `C[⊥] ⟺ ⊥` | (a) | SINGLETON proof is constructive | Lean `ctxBot`, `ctxBotIff` |
| 15 | Prop 3.3(2) | `C[φ⊔ψ] ⟺ C[φ]⊔C[ψ]` | (a) | | Lean `ctxPropagationOrIff` |
| 16 | Prop 3.3(3) | `C[∃x.φ] ⟺ ∃x.C[φ]` | (a) | | Lean `ctxPropagationExist(R)` |
| 17 | Lemma 3.4 | `φ ⊢ ~C[~φ]` | (a) | | Lean `doubleNegCtx` |
| 18 | Prop 3.4 | equivalence congruence in arbitrary contexts | (a) | app contexts Lean; `∧,∨,⇒,∃,∀` Lean (`iffLeibniz`, replacement of equivalents in application-free contexts, with an internal premise); `µ,ν` by Lemma 4.3 (paper) | Lean `ctxFramingEquiv`, `iffLeibniz` + paper |
| 19 | — | `C[~~φ] ⇒ ~~C[φ]` (¬¬-propagation) | (c!) | sound, underivable in the current system; **replaced** the top-filter proof, which did not apply | Lean `DepthOne.nnPropagation_not_derivable` |
| 20 | Thm 3.2 (N) | `φ ⊢ σᵈφ` | (a) | | Lean `boxNec` |
| 21 | Thm 3.2 (K) | `σᵈ(φ⇒ψ) ⇒ σᵈφ ⇒ σᵈψ` | (c!) | **was (c?)**: sound, not refutable over a chain (there `σᵈφ(1) = [φ(0) ≠ ⊥]` and (K) holds); refuted in the depth-one model over the non-chain frame `L₅`, instance `σᵈ(~c) ⇒ σᵈc ⇒ σᵈ⊥` | Lean `DepthOne.boxK_not_derivable` |
| 22 | Thm 3.2 (Barcan) | `∀x.σᵈφ ⇒ σᵈ∀x.φ` | (c!) | = DNS `⨅¬¬φ_a ≤ ¬¬⨅φ_a`, fails in `Opens ℝ` | paper; converse Barcan Lean `boxConverseBarcan` |
| 23 | — | `σᵈ(φ⊓ψ) ⇒ σᵈφ ⊓ σᵈψ` | (a) | | Lean `boxAnd` |
| 24 | — | `σᵈφ ⊓ σᵈψ ⇒ σᵈ(φ⊓ψ)` | (c!) | **was (c?)**; same model as #21, instance `φ = c, ψ = ~c` | Lean `DepthOne.boxAnd_not_derivable` |

## 3. Definedness, membership, totality (thesis §3.2)

All rows assume the definedness axiom `∀x.⌈x⌉` in `Γ` (`IsDefinedness`).
`x ∈ φ := ⌈x ⊓ φ⌉`, classical totality `⌊φ⌋ := ~⌈~φ⌉`, positive totality
`⌊φ⌋ⁱ := ∀x. x ∈ φ`, classical equality `φ =ₘₗ ψ := ⌊φ ⟺ ψ⌋`, positive equality
`φ =ⁱ ψ := ⌊φ ⟺ ψ⌋ⁱ`. `IsPred θ := θ ⇒ ⌊θ⌋ⁱ` ("`θ` is a predicate pattern").

| # | Thesis | Statement | Verdict | Notes | Evidence |
|---|---|---|---|---|---|
| 25 | (3.19) | `⌈x⌉`, `⌈·⌉` monotone, `⌈⊥⌉ ⇒ ⊥`, `⌈φ⊔ψ⌉ ⟺`, `⌈∃φ⌉ ⟺ ∃⌈φ⌉` | (a) | also `⌈⌈φ⌉⌉ ⟺ ⌈φ⌉`, `⌈C[φ]⌉ ⇒ ⌈φ⌉` | Lean `ceil_of_evar`, `ceil_mono`, `ceil_bot`, `ceil_or`, `ceil_exist`, `ceil_ceil_iff`, `ceil_ctx_impl_ceil` |
| 26 | Lemma 3.5/3.6 | `φ↔ψ ⊢ φ=ψ`; `φ=φ`; symmetry | (a) | for both equalities; positive equality is also transitive (`eqI_trans`) and implies the classical one (`eqI_impl_eqML`) | Lean `eqML_of_iff`, `eqML_refl`, `eqML_symm`, `eqI_of_iff`, `eqI_refl`, `eqI_symm`, `eqI_trans` |
| 27 | Lemma 3.7 | membership intro `φ ⊢ x ∈ φ` | (a) | | Lean `memIntro`, `memIntroAll` |
| 28 | Lemma 3.8 | membership elim `∀x.(x∈φ) ⊢ φ` | (a) | **was (b)** (only `~~φ` with the negative rule); `singletonStrong` gives `⌈x ⊓ φ⌉ ⇒ x ⇒ φ` directly | Lean `ceil_evar_impl`, `totalI_impl`, `memElim` |
| 29 | Lemma 3.9 | `x∈y ⟺ x=y` | (b) | classical `=ₘₗ`: (←) **refuted** (value `¬¬E x y` vs `E x y`), (→) not derived. Positive `=ⁱ`: (←) derivable, (→) reduces to `IsPred (x ∈ y)` | Lean `PointModel.eqML_mem_not_derivable`; `eqI_impl_mem`; `mem_impl_eqI_of_pred` |
| 30 | Lemma 3.10 (→) | `x∈~φ ⇒ ~(x∈φ)` | (a) | | Lean `memNegElim` |
| 31 | Lemma 3.10 (←) | `~(x∈φ) ⇒ x∈~φ` | (c?) | **downgraded from (c!)**: the top-filter refutation is for the published system only; sound; follows from `IsPred (~(x ∈ φ))`; no `GModel`-type countermodel can exist (§0.4) | Lean `memNegIntro_of_pred` (reduction) |
| 32 | Lemma 3.11 | Membership∨ | (a) | | Lean `memOr` |
| 33 | Lemma 3.12 | Membership∧ | (a) | **(←) was (c?)**: it is literally the `C₁ = C₂ = ⌈□⌉` instance of `singletonStrong` | Lean `memAnd`, `memAndIntro` |
| 34 | Lemma 3.13 | Membership∃ | (a) | | Lean `memExist` |
| 35 | (new) | Membership⇒ | (a)/(c?) | (→) `x∈(φ⇒ψ) ⊓ x∈φ ⇒ x∈ψ` **was weak form only**, now full; (←) `(x∈φ ⇒ x∈ψ) ⇒ x∈(φ⇒ψ)` sound, reduces to `IsPred (x∈φ ⇒ x∈ψ)` (the earlier "refuted in the chain model" referred to the top-filter model and does not apply) | Lean `memImplElim`; `memImplIntro_of_pred` |
| 36 | Lemma 3.14 | `C[φ] ⇒ ⌈φ⌉` | (a) | **was (c!)** for the published system (`TopFilter.phi_impl_ceil_not_derivable`); with the positive rule, transport `x ⊓ φ` from `C` into `⌈x⌉` | Lean `ctxImplDefined`, `phi_impl_ceil` |
| 37 | Cor 3.1 | `⌊φ⌋ ⇒ φ` | (b) | literal form with `⌊·⌋ = ~⌈~·⌉` **refuted** (it is DNE in disguise); the positive `⌊φ⌋ⁱ ⇒ φ` is derivable, and `⌊φ⌋ ⇒ ~~φ` | Lean `PointModel.total_impl_not_derivable`; `totalI_impl`, `total_elim_nn` |
| 38 | (new) | `⌊φ⌋ⁱ ⇒ ⌊φ⌋`, `⌈⌊φ⌋ⁱ⌉ ⇒ ⌊φ⌋ⁱ`, `⌊χ⌋ⁱ ⊓ C[ψ] ⇒ C[χ ⊓ ψ]` | (a) | positive totality propagates its content into every context | Lean `totalI_impl_total`, `ceil_totalI`, `totalI_ctx`, `totalI_mono` |
| 39 | Thm 3.3 | deduction theorem `Γ∪{ψ} ⊢ φ ⟹ Γ ⊢ ⌊ψ⌋ ⇒ φ` | (c!) | **false** for the current system too (§0.3) | Lean `PointModel.deductionTheorem_fails` |
| 40 | (variant of 39) | DT with `⌊ψ⌋ⁱ := ∀x.x∈ψ` | (c?) | `⌊ψ⌋ⁱ ⇒ ψ` is now available (#28); the framing case still needs `⌊ψ⌋ⁱ ⊓ C[χ₁] ⇒ C[⌊ψ⌋ⁱ ⊓ χ₁]`, i.e. `IsPred ⌊ψ⌋ⁱ`, which in turn needs `IsPred ⌈·⌉` and Membership∀(←) | paper |
| 41 | Lemma 3.15 | equality elimination | (b) | classical `=ₘₗ`: **refuted** already at `(⊤ = c) ⇒ (⊤ ⇒ c)`; positive `=ⁱ`: `(φ =ⁱ ψ) ⇒ φ ⇒ ψ`, congruence in application contexts, and Leibniz's law for holes `Q[A[P[□]]]` (§0.5); holes under `µ/ν` or below app–connective–app (c?) | Lean `PointModel.eqML_elim_not_derivable`; `eqI_elim`, `eqI_elim_ctx`, `eqI_leibniz` |
| 42 | Lemma 3.16 | functional substitution | (c?) | via #41: for positive equality and holes covered by `eqI_leibniz` it should follow on paper; not formalized (needs the context/substitution correspondence) | paper |
| 43 | Lemma 3.17 | `C[φ₁ ∧ x∈φ₂] = C[φ₁] ∧ x∈φ₂` | (a)/(c?) | (→) **was (c?)**, now derivable (Lemma 3.14 + idempotence); (←) is predicate propagation, reduces to `IsPred (x ∈ φ₂)` | Lean `ctx_mem_elim`; `ctx_mem_intro_of_pred` |
| 44 | Lemma 3.18 | `∃y.(x=y ∧ φ) = φ[x/y]` | (c?) | via #43(←) | paper |
| 45 | Lemma 3.19 (→) | `∃y.(⌈y⊓φ⌉ ⊓ y) ⇒ φ` | (a) | **was (b)** (only `~~φ`) | Lean `existCeilEvar_impl` |
| 46 | Lemma 3.19 (←) | `φ ⇒ ∃y.(⌈y⊓φ⌉ ⊓ y)` | (a) | **was (c?)** | Lean `phi_impl_existCeilEvar`, `existCeilEvar_iff` |
| 47 | Lemma 3.20 | membership through symbols | (c?) | via #43(←) (the other ingredient, #46, is now available) | paper |
| 48 | Thm 3.4 | definedness completeness | (c!) | fails as stated: the system P it refers to contains the membership excluded middle, which is unsound (`PointModel.cm_memEM`, value `u ≠ ⊤` in an `HModel`). Whether the *current* system is complete for the definedness theory is open: every sound-but-underivable statement known (#19, #21, #24) is refuted only in a model where `∀x.⌈x⌉` fails, and the open items of this section all reduce to `IsPred` | Lean `PointModel.memEM_not_derivable` |
| 49 | §3.3 | local completeness via MCS | (c?) | MCS uses `¬φ ∈ Γ iff φ ∉ Γ` (Prop 3.6(2)); an intuitionistic version would need prime theories / Kripke-style canonical models; out of scope | paper |

## 4. Matching µ-logic (thesis Chapter 4)

| # | Thesis | Statement | Verdict | Notes | Evidence |
|---|---|---|---|---|---|
| 50 | Lemma 4.2 | ν pre-fixpoint and ν-KT | (a) | primitive in iML; no `¬µ¬` detour | Lean `nuPostFixpoint`, `nuCoinduction` |
| 51 | Lemma 4.3 | `φ⇒ψ ⊢ µX.φ ⇒ µX.ψ` (and ν) | (a) | | Lean `muMonoFromImpl`, `nuMonoFromImpl` |
| 52 | Lemma 4.4/4.5 | positive/negative contexts | (a) | induction on contexts using #13, #7, #51 (Lean only for the app-context and hypothesis forms) | paper |
| 53 | Lemma 4.6 | `µX.φ ⟺ φ[µX.φ/X]` | (a) | given syntactic monotonicity (#52) | Lean `muUnfold`, `nuUnfold` (monotonicity as hypothesis) |
| 54 | Lemma 4.7 | predicate patterns `⊢ ψ=⊤ ∨ ψ=⊥` propagate through contexts | (b) | the *definition* is classical (a decidability condition); replace by `IsPred ψ := ψ ⇒ ⌊ψ⌋ⁱ`; then propagation `ψ ⊓ C[φ] ⇒ C[ψ ⊓ φ]` is derivable (`pred_ctx`), `⌊χ⌋ⁱ` propagates its content (`totalI_ctx`), and the substantive question is which patterns are `IsPred` — for `⌈·⌉`-patterns open (§0.4) | Lean `pred_ctx`, `totalI_ctx` |
| 55 | Lemma 4.8 | `ψ ∧ µX.φ ⟺ µX.(ψ∧φ)` for predicate `ψ` | (a) | with the `IsPred` definition the proof (KT + pre-fixpoint + 4.5) is intuitionistic | paper |
| 56 | Thm 4.2 | deduction theorem for Hµ | (c!) | as #39 | Lean `PointModel.deductionTheorem_fails` |
| 57 | §4.2 | `⊥ := µX.X` vs primitive `⊥` | (a) | interderivable | Lean `muSvarIffBot`, `nuSvarIffTop` |

## 5. Expressive power (thesis Chapter 5)

### 5.1 Recursive symbols, initial algebras (§5.1, §5.5)

| # | Thesis | Statement | Verdict | Notes | Evidence |
|---|---|---|---|---|---|
| 58 | Lemma 5.5 | "plugging out" `C[φ] ⇒ ψ  iff  φ ⇒ ∃x.(x ∧ ⌊C[x] ⇒ ψ⌋)` | (c?) | uses `φ = ∃x.(x ∧ x∈φ)` (#46 and #28, both now available) and `x∈φ` being a predicate pattern (`IsPred`, open) | paper |
| 59 | Thm 5.1 | pre-fixpoint/KT for recursive symbols | (c?) | via #58 | paper |
| 60 | Thm 5.6 | Peano induction from (No Junk) + KT | (a) | `⊤Nat = µD. zero ∨ succ(D)` is `evt succ zero`; the rule is `evtInduction` | Lean `peanoInduction` |
| 61 | Thm 5.7 | general structural induction | (a) | same shape, one KT per sort | paper |
| 62 | Lemma 5.2 | `succ(Ψ) ⇒ Ψ  iff  ∀x.(x∈Ψ ⇒ succ(x)∈Ψ)` | (c?) | the membership form needs #47 (#28 is available) | paper |
| 63 | Thm 5.5 | `plus` is a defined function | (c?) | equational reasoning modulo `≃` rests on #41, available for positive equality in the covered positions; not carried out | paper |

### 5.2 Transition systems, modal µ-calculus, temporal logics (§5.7–5.9, Prop. 5.6)

`• := next ⬝ ·`, `◦ := ~•~`, `⋄ := µX.φ ∨ •X`, `□ := νX.φ ∧ ◦X`, `⋄w := νX.φ ∨ •X`, `WF := µX.◦X`.

| # | Prop 5.6 item | Statement | Verdict | Notes | Evidence |
|---|---|---|---|---|---|
| 64 | (1)–(3) | `•⊥⟺⊥`, `•(φ∨ψ)⟺`, `•∃⟺∃•` | (a) | | Lean `nxBotIff`, `nxOr`, `nxExist` |
| 65 | (4) | `◦⊤ ⟺ ⊤` | (a) | | Lean `allnxTop` |
| 66 | (5) | `◦(φ∧ψ) ⟺ ◦φ ∧ ◦ψ` | (a)/(c!) | (→) Lean `allnxAnd`; (←) **was (c?)**, refuted (it is #24 with `next := s`) | Lean `DepthOne.boxAnd_not_derivable` |
| 67 | (6) | `◦∀x.φ ⟺ ∀x.◦φ` | (a)/(c!) | (→) Lean `allnxForall`; (←) is Barcan, unsound (#22) | |
| 68 | (7) | `φ ⇒ ⋄φ`, `•⋄φ ⇒ ⋄φ` | (a) | | Lean `evtIntro`, `nxEvt` |
| 69 | (8) | `□φ ⇒ φ`, `□φ ⇒ ◦□φ` | (a) | | Lean `alwElim`, `alwNext` |
| 70 | (9) | `φ ⇒ ⋄wφ`, `•⋄wφ ⇒ ⋄wφ` | (a) | | Lean `wevtIntro`, `nxWevt` |
| 71 | (10) | monotonicity of `•, ◦, ⋄, □, ⋄w` | (a) | | Lean `nxMono`, `allnxMono`, `evtMono`, `alwMono`, `wevtMono` |
| 72 | (11)–(13) | `⋄⊥⟺⊥`, `⋄(φ∨ψ)⟺⋄φ∨⋄ψ`, `⋄∃⟺∃⋄` | (a) | (13) paper (lifting bookkeeping only) | Lean `evtBot`, `evtOr`, `evtOrR` |
| 73 | (14) | `□⊤` | (a) | | Lean `alwTop` |
| 74 | (15) | `□(φ∧ψ) ⟺ □φ∧□ψ` | (a)/(c!) | (→) Lean `alwAnd`; (←) fails in the depth-one model over `L₅` at `φ = c ⊔ s⬝s`, `ψ = ~c ⊔ s⬝s`: `□φ(1) = □ψ(1) = ⊤` (the post-fixpoints `(u,⊤)`, `(¬u,⊤)`) while `□(φ⊓ψ) = (⊥,⊥)`; the ν-computation is on paper, not in Lean | paper (model in Lean) |
| 75 | (16) | `□∀ ⟺ ∀□` | (a)/(c!) | (→) paper; (←) Barcan | |
| 76 | (17) | `□φ ⟺ ¬⋄¬φ` | (a)/(c!) | (→) Lean `alwToNotEvtNot`; (←) is DNE in the one-point model with `next ↦ ⊤`, where `⋄ = □ = id` (paper); even `¬⋄¬φ ⇒ □~~φ` needs #19 | |
| 77 | (18) | `◦φ₁ ∧ •φ₂ ⇒ •(φ₁∧φ₂)` | (c!) | unsound (semantically `•(~~φ₁ ∧ φ₂)`); **now Lean** | Lean `PointModel.allnx_nx_and_not_derivable` |
| 78 | (19) | `◦(φ₁⇒φ₂) ∧ •φ₁ ⇒ •φ₂` | (c!) | unsound; **now Lean** | Lean `PointModel.allnx_nx_impl_not_derivable` |
| 79 | (20) | `⋄wφ ⟺ (WF ⇒ ⋄φ)` | (c?) | (→) via (19); (←) case analysis on `WF` | paper |
| 80 | (21),(22) | `⋄w` distributes over `∨`, `∃` | (a)/(c?) | (←) by monotonicity (paper); (→) via (20) | paper |
| 81 | (23) | idempotence of `⋄, □, ⋄w` | (a) | | Lean `evtIdem`, `alwIdem` (+ paper for the trivial halves) |
| 82 | (24),(25) | `WF ⟺ µX.◦ᵏX`, `WF ⟺ µX.◦□X` | (a) | KT + pre-fixpoint + Lemma 4.3 only | paper |
| 83 | (26) | `□φ₁ ∧ ⋄wφ₂ ⇒ ⋄w(φ₁∧φ₂)` | (c?) | via (18) | paper |
| 84 | (27) | `□(φ₁⇒φ₂) ∧ φ₁ ⇒ φ₂` | (a) | | paper (`alwElim` + mp) |
| 85 | Lemma 5.6 (LTL) | (K◦),(N◦),(K□),(N□),(Fun),(U1),(U2),(Ind) | mixed | (N◦),(N□),(U1) (a) paper; (K◦) = #21 **(c!) Lean** `DepthOne.boxK_not_derivable`; (Fun→) `•⊤ ⊢ ◦φ ⇒ •φ` unsound, **(c!) Lean** `PointModel.allnx_impl_nx_not_derivable`; (K□) and (Ind) need #66(←), itself refuted, but are not refuted directly (c?); (U2) via (Fun) (c?) | Lean + paper |
| 86 | Lemma 5.8 (finite LTL) | (coInd),(Fix),(¬◦) | (a)/(c!) | (coInd),(Fix) by KT (paper); (¬◦) via (Fun) | paper |
| 87 | Lemma 5.10 (CTL) | 10 rules | mixed | EX/EU rules (a); the AX (K)-rule is #21 (c!); AU rules need #66(←) (c?) | paper |
| 88 | Lemma 5.12 (DL) | (Gen),(DL1),(DL2),(DL7) | mixed | (Gen) (a) by (N)+coinduction; (DL1) is (K) for `[α]`, (c!) for atomic `α` (#21); (DL2 for `β*`) (a) by KT/park; (DL7) induction needs `[α]A ∧ [α]B ⇒ [α](A∧B)` (c?) | paper |
| 89 | Lemma 5.14 (RL) | RL proof rules | mixed | Reflexivity, Consequence, Case analysis, Abstraction, Transitivity(C=∅) (a) paper; Transitivity(C≠∅) and Circularity via (18),(20),(25) (c?); Logic framing via predicate propagation (`IsPred`) (c?) | paper |

### 5.3 Second-order logic, λ-calculus, term-generic logic (§5.6, 5.12, 5.13)

| # | Thesis | Statement | Verdict | Notes |
|---|---|---|---|---|
| 90 | Def 5.5 | powersets via `extension(α) = X`, `intension(φ) := ∃α.(α ∧ extension(α) = φ)` | (b) | definitional; `=` must be read as the positive equality `=ⁱ` (value `⨅_z (φ z ⇔ ψ z)`, `IML.hinterp_eqI_evar`) rather than `⌊↔⌋` (value `⨅_z ¬¬(φ z ⇔ ψ z)`); the meta-theorems (5.8, 5.9) are model-theoretic and outside the scope of derivability |
| 91 | (5.110) | `(π x⃗ = ⊤) ∨ (π x⃗ = ⊥)` (TGL predicates) | (c!) | a decidability axiom; it may be *assumed*, but it forces the predicate symbols to be Boolean, defeating the point of an intuitionistic logic |
| 92 | Thm 5.16 | extensiveness of `Γλ` | (c?) | needs equational reasoning (#41) |

## 6. AML and the proof checker (thesis Chapter 7)

| # | Thesis | Statement | Verdict | Notes |
|---|---|---|---|---|
| 93 | (7.16) | sorted negation `¬ₛφ := ¬φ ∧ ⊤ₛ` | (b) | fine as a definition; sorted EM/DNE fail as their unsorted versions do |
| 94 | (7.9),(7.11) | `⊆ := ⌊⇒⌋` in (Symbol Arity), wellsortedness | (b) | use `⌊·⌋ⁱ` (`∀x. x ∈ (φ ⇒ ψ)`) or a plain implication axiom; with `⌊⇒⌋` the axiom only says `¬¬`-inclusion |
| 95 | §7.4 | `or-is-sugar`, `and-is-sugar`, `proof-rule-prop-3` | (c!) | the Metamath checker's sugar `φ∨ψ := ¬φ→ψ`, `φ∧ψ := ¬(¬φ∨¬ψ)` is unsound intuitionistically (`(¬φ→ψ) ⇒ φ∨ψ` fails); an iML checker needs the 12-constructor syntax and the 27 rules, exactly as `IML/Proof.lean` |

## 7. Tally

95 numbered rows (some bundle two directions or several rules). Before/after
the change of primitive (first survey → this one):

* **(a)** 42 → **46** rows fully derivable — 41 backed by Lean proofs, 5 on paper
  (rows 52, 55, 61, 82, 84). Flipped to (a): 28, 33, 36, 45, 46.
* **(a)/(c) split by direction** 6 → **7** rows (35, 43, 66, 67, 74, 75, 76):
  one direction derived in Lean, the other (c!) (Barcan, DNE, or the
  depth-one model) or (c?) (reduces to `IsPred`). Flipped: 35(→) and 43(→) to
  derivable, 66(←) and 74(←) to refuted.
* **mixed rule tables** 5 rows (85–89: LTL, finite LTL, CTL, DL, RL): the
  existential/Knaster–Tarski rules port, every rule that distributes the dual
  box over a conjunction or is its (K) rule does not.
* **(b)** 7 → **7** rows (29, 37, 41, 54, 90, 93, 94): 28 and 45 left for (a);
  29, 37, 41 arrived from (c?)/(c!) because the positive notions
  (`⌊·⌋ⁱ`, `=ⁱ`) do what the classical ones cannot.
* **(c!)** 17 → **16** rows with proved underivability or unsoundness
  (2, 5, 9, 11, 12, 19, 21, 22, 24, 39, 48, 56, 77, 78, 91, 95) — 9 by Lean
  countermodel of the current system (2, 5, 19, 21, 24, 39, 56, 77, 78), the
  rest by unsoundness arguments on paper. Newly refuted: 21, 24 (and 66(←),
  74(←)); newly Lean-backed: 77, 78, 85(Fun→). Left: 36 (now derivable), 31
  (downgraded).
* **(c?)** 18 → **14** rows not derived and not refuted (31, 40, 42, 44, 47,
  49, 58, 59, 62, 63, 79, 80, 83, 92). Of these, 31, 40, 44, 47, 58, 59, 62
  reduce to the single principle `IsPred` of §0.4; 42, 63, 92 to equational
  reasoning that `eqI_leibniz` supplies for the covered positions but which is
  not carried out; 79, 80, 83 to Prop. 5.6(20).

Impossibility proofs, by fate: **replaced** (top-filter → a model of the
current system): rows 2, 19, 39/56 (and the symbol excluded middle of row 5);
**newly proved**: 21, 24, 66(←), 77, 78, 85(Fun→), and 29(←), 37, 41 for the
classical notions; **downgraded** to (c?): 31 (Membership¬(←)); **dropped as
an impossibility**: 36 (it is derivable now).

## 8. What is in `IML/DerivedRules/`

All files are sorry-free; `IML.p2` is axiom-free, `IML.ctxBot` uses only
`propext`, and everything else (including `IML.soundness`,
`IML.Crisp.soundness`, `IML.Examples.ExcludedMiddle.excludedMiddle_not_derivable`
and every `*_not_derivable` above) uses only `propext`, `Classical.choice`,
`Quot.sound` (checked with `#print axioms`).

| File | Lines | Content |
|---|---|---|
| `Propositional.lean` | 250 | IPC toolkit: `implSelf, p1, p2, implAnd, implMp, orElim, andOrDistrib, contrapositive, dni, tripleNegElim, notOr, notOrIntro, nnImpl, nnAnd, nnExcludedMiddle`, `⟺` lemmas |
| `FOL.lean` | 243 | `evarSubst_evarLift`, `evarSubst_evarLiftFrom_succ` (12-constructor ports); quantifier rules; `forallImplExist`, `pushConjInExist` |
| `Context.lean` | 158 | `ctxFraming, ctxBot, ctxPropagationOr(R), liftEVar, evarLift_fill, ctxPropagationExist(R), doubleNegCtx`, dual box `AppCtx.box` with `boxNec, boxMono, boxAnd, boxTop, boxConverseBarcan` |
| `Fixpoint.lean` | 159 | `svarSubst_svarLift`, `svarLift_positive`, µ/ν rules, `muSvarIffBot`, `nuSvarIffTop`, unfolding modulo monotonicity |
| `Definedness.lean` | 688 | `⌈·⌉, ⌊·⌋, ⌊·⌋ⁱ, ∈ₘₗ, =ₘₗ, =ⁱₘₗ`; rows 25–38, 41, 43, 45–46; `totalI_ctx`; positive equality with `eqI_trans`, `PCtx`/`iffLeibniz`, `eqI_leibniz`, `eqI_impl_mem`; `IsPred` and the reductions `pred_ctx`, `ctx_mem_intro_of_pred`, `mem_impl_eqI_of_pred`, `memNegIntro_of_pred`, `memImplIntro_of_pred` |
| `EqualitySemantics.lean` | 53 | `HModel.StdCeil`, `hinterp_eqI_evar : ⟦x =ⁱ y⟧ = E ρ(x) ρ(y)` |
| `Temporal.lean` | 206 | `nx, allnx, evt, alw, wevt, wf`; rows 64–76, 81; `peanoInduction` |
| `TopFilterModel.lean` | 734 | the non-standard model of the *published* system, its soundness (`TopFilter.soundness`), its refutations (`nnPropagation_not_derivable, dne_not_derivable, phi_impl_ceil_not_derivable, memNegIntro_not_derivable, memEM_not_derivable, em_not_derivable, deductionTheorem_fails`, all about `ProofCore singletonAx`), and `cm_singletonStrong`: the model refutes the positive rule |
| `PointModel.lean` | 327 | one- and two-point `HModel`s over a complete chain (`cm`, `tp`) and the refutations for the current system: `dne_not_derivable, em_not_derivable, total_impl_not_derivable, memEM_not_derivable, eqML_elim_not_derivable, deductionTheorem_fails, allnx_nx_and_not_derivable, allnx_nx_impl_not_derivable, allnx_impl_nx_not_derivable, eqML_mem_not_derivable` |
| `DepthOneModel.lean` | 434 | the depth-one `GModel` over any frame with join-prime top (`TopJoinPrime`), **`valid_strong`** (it validates `singletonStrong`), `sound`, the frame `L₅`, and `nnPropagation_not_derivable, boxK_not_derivable, boxAnd_not_derivable` |
| `../DerivedRules.lean` | | umbrella import |

Left unformalized (on-paper verdicts only): syntactic monotonicity in general
contexts (Lemma 4.5) and hence the unconditional µ-unfolding; the
ν-computation behind row 74(←); Prop. 5.6 items (13), (20)–(22), (24)–(27) and
the LTL/CTL/DL/RL rule tables; the soundness of the sound-but-underivable
statements in the *standard* `HModel` semantics (one-line lattice
computations, stated in the text, not checked in Lean); and the structural
argument of §0.4 that `GModel`s cannot refute sound statements of the
definedness theory.

## 9. Open questions worth settling next

1. **Is `⌈φ⌉ ⇒ ⌊⌈φ⌉⌋ⁱ` derivable?** (`IsPred ⌈φ⌉`; equivalently
   `⌈x⌉ ⊓ ⌈φ⌉ ⇒ ⌈x ⊓ ⌈φ⌉⌉`.) Sound. Everything still open in §3.2 reduces to
   it or to its variants for `~⌈φ⌉` and `⌈φ⌉ ⇒ ⌈ψ⌉`. A countermodel cannot be
   a `GModel` (§0.4); a Kripke-style semantics with varying domains, in which
   `⌈φ⌉` at a world only sees that world's elements, is the natural place to
   look.
2. **Membership∀(←)** `∀y.(x ∈ φ) ⇒ x ∈ ∀y.φ`: sound, not derived; with 1 it
   gives `IsPred ⌊ψ⌋ⁱ` and the deduction theorem with `⌊·⌋ⁱ`.
3. **Completeness.** The pure current system is incomplete (¬¬-propagation,
   (K), box-∧). Adding ¬¬-propagation `C[~~φ] ⇒ ~~C[φ]` as an axiom recovers
   (K) and box-∧ (paper); whether it is complete for the Heyting semantics is
   open. A Kripke-style canonical model (prime theories instead of MCS) is the
   natural approach.
4. **Leibniz under fixpoints.** `eqI_leibniz` for holes under `µ`/`ν` needs
   the propagation of `⌊·⌋ⁱ` through positive patterns, i.e. the general
   syntactic monotonicity of Lemma 4.5 with a totality parameter.

## 10. Shortlist for a presentation

1. **⊥-propagation needs no rule** — SINGLETON already gives it constructively
   (`ctxBot`, axiom-free).
2. **A checked incompleteness theorem for the current system**: the depth-one
   model validates every rule including the positive SINGLETON
   (`IML.DepthOne.valid_strong`) and refutes `C[~~φ] ⇒ ~~C[φ]`, the modal (K)
   rule and `◦φ ⊓ ◦ψ ⇒ ◦(φ ⊓ ψ)`, all valid in every Heyting model.
3. **The deduction theorem is false** in the thesis' form
   (`deductionTheorem_fails`), because `⌊·⌋ = ~⌈~·⌉` is the wrong totality;
   the positive `∀x. x ∈ ψ` is the right one: `⌊ψ⌋ⁱ ⇒ ψ` is derivable.
4. **The positive SINGLETON is what §3.2 needs**: it derives membership
   elimination, Lemma 3.14, Membership∧/⇒ and Lemma 3.19 outright; the residue
   is the single principle "`⌈·⌉`-patterns are predicate patterns".
5. **Positive equality `⌊φ ⟺ ψ⌋ⁱ` is the Ω-set equality**: transitive, with
   Leibniz's law in all non-fixpoint positions of shape `Q[A[P[□]]]`, and
   `⟦x =ⁱ y⟧ = E ρ(x) ρ(y)`; the classical `⌊φ ⟺ ψ⌋` has no elimination rule.
6. **The dual box is the ¬¬-box**: Barcan and `◦φ₁∧•φ₂ ⇒ •(φ₁∧φ₂)` are
   unsound, (K) and `◦`-conjunction are unprovable, so LTL's (Ind), CTL's AX/AU
   rules, DL's (DL1)/(DL7), RL's (Circularity) do not port, while the whole
   existential / Knaster–Tarski side ports verbatim. Suggests a primitive
   all-path application, or `◦ⁱφ := ∀y.(•y ⇒ y∈φ)` when definedness is
   available.
