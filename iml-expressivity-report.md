# Which of Chen's matching-logic derivations survive in intuitionistic AML?

Survey of the syntactic, theory-building derivations of Xiaohong Chen's PhD thesis
(*Matching µ-Logic*, 2023, chapters 3–5 and 7) against the iML proof system of
`IML/Proof.lean` (27 rules: classical AML minus `p3`, with `∧, ∨, ∀, ν, ⇒, ⊥`
primitive), backed where indicated by Lean proofs in `IML/DerivedRules/*.lean`
(branch `thesis-survey`, sorry-free, standard axioms only).

Verdict codes:

* **(a)** still derivable — ported with a Lean proof, or, where marked *paper*, an
  on-paper derivation using only rules already ported.
* **(b)** classical, but a constructively meaningful variant goes through — the
  variant is stated and the weakening named.
* **(c)** genuinely missing. Sub-labelled **(c!)** when underivability is *proved*
  (by a Lean countermodel, or by unsoundness for the Heyting semantics), and
  **(c?)** when I could not derive it and no natural variant works, but
  underivability is not proved.

"Lean" in the last column means the verdict is backed by a checked proof (name in
`IML.…`); "paper" means an on-paper judgement.

## 0. Headline findings

1. **⊥-propagation is derivable.** `C[⊥] ⇒ ⊥` needs no new rule: Mircea Sebe's
   classical proof (thesis Prop. 3.3(1)) uses only `⊥ ⇒ ·`, framing, pairing and
   SINGLETON, all intuitionistic. Lean: `IML.ctxBot` (axiom-free). The lead in the
   brief is therefore closed negatively: there is no gap here, and taking
   `⊥ := µX.X` instead of a primitive `⊥` changes nothing (`IML.muSvarIffBot`
   proves `µX.X ⟺ ⊥`; ⊥-propagation for `µX.X` is the same SINGLETON argument).

2. **The proof system is incomplete for its Heyting semantics.** The statement
   `C[~~φ] ⇒ ~~C[φ]` (*¬¬-propagation through application contexts*) is valid in
   every `HModel` (`⨆ ¬¬φ(a) ⊓ R ≤ ¬¬⨆ φ(a) ⊓ R`) but **not derivable**:
   Lean `IML.TopFilter.nnPropagation_not_derivable`. The proof is a non-standard
   model of all 27 rules (`IML/DerivedRules/TopFilterModel.lean`): one-point
   carrier, values in the chain `ℕ∞`, application interpreted Boolean-ly as
   `j(φ ⊓ ψ)` with `j u = ⊤ iff u = ⊤`. Same model, same file, also refutes:
   * `~~φ ⇒ φ` (axiom p3) — `dne_not_derivable`;
   * `φ ⇒ ⌈φ⌉` from the definedness axiom (thesis Lemma 3.14/Cor. 3.1) —
     `phi_impl_ceil_not_derivable` — although it is valid in every Heyting model
     of definedness;
   * Membership¬(←) `~(x ∈ φ) ⇒ x ∈ ~φ` — `memNegIntro_not_derivable`;
   * the membership excluded middle `⌈x⌉ ⇒ ⌈x ⊓ φ⌉ ⊔ ⌈x ⊓ ~φ⌉` — `memEM_not_derivable`.

3. **The deduction theorem (thesis Thm 3.3 / 4.2) is false for iML.**
   `IML.TopFilter.deductionTheorem_fails`: from `Γ ∪ {c ⊔ ~c} ⊢ c ⊔ ~c` it would
   give `Γ ⊢ ⌊c ⊔ ~c⌋ ⇒ c ⊔ ~c`; but `⌊c ⊔ ~c⌋ = ~⌈~(c ⊔ ~c)⌉` *is* derivable
   (double negation of excluded middle, pushed through `⌈·⌉` by framing and
   ⊥-propagation), so excluded middle would be derivable, which the model refutes.
   The classical totality `⌊ψ⌋ := ~⌈~ψ⌉` is the wrong notion: its Heyting value is
   `⨅_a ¬¬ψ(a)`, not "ψ holds everywhere". The natural intuitionistic totality is
   the positive `⌊ψ⌋ⁱ := ∀x. x ∈ ψ` (value `⨅_a ψ(a)`); `⌊ψ⌋ⁱ ⇒ ⌊ψ⌋` is derivable
   (`IML.totalI_impl_total`), and a DT with `⌊·⌋ⁱ` is semantically plausible but
   its syntactic proof needs `⌊ψ⌋ⁱ ⇒ ψ` (open, see §3.2 below).

4. **The whole membership calculus of §3.2 hinges on one classical step**, the
   membership excluded middle `⌈x⌉ ⇒ ⌈x ⊓ φ⌉ ⊔ ⌈x ⊓ ~φ⌉` (thesis: "⌈x⌉, hence
   ⌈(x ∧ ¬φ) ∨ (x ∧ φ)⌉, hence …"). It is unsound intuitionistically. SINGLETON
   only transports *negative* information between contexts; classical logic turns
   negative into positive via EM. The sound, classically derivable *positive*
   companion `SingletonPos : C₁[x ⊓ φ] ⊓ C₂[x ⊓ ψ] ⇒ C₂[x ⊓ φ ⊓ ψ]` recovers
   Lemma 3.14 (`IML.ctxImplDefined`), Membership∧(←) (`IML.memAndIntro`) and
   Lemma 3.19(←) (`IML.phi_impl_existCeilEvar`), but not ¬¬-propagation (the
   top-filter model validates `SingletonPos` and refutes ¬¬-propagation, so the
   two principles are independent).

5. **The defined box `◦ := ~•~` is the double-negation box.** Its Heyting value is
   `⨅_b (R(b,m) ⇨ ¬¬φ(b))`, so the universal side of Chapter 5 degrades:
   (K) for `~C[~·]` (Thm 3.2(1)) is not derived (it reduces to ¬¬-propagation);
   `◦φ ⊓ ◦ψ ⇒ ◦(φ ⊓ ψ)` is sound but not derived; the Barcan formula
   `∀x.◦φ ⇒ ◦∀x.φ` (Thm 3.2(3), Prop. 5.6(6,16)) is *unsound* (it is the double
   negation shift, which fails in `Opens ℝ`); `◦φ₁ ⊓ •φ₂ ⇒ •(φ₁ ⊓ φ₂)`
   (Prop. 5.6(18)) and `•⊤ ⊢ ◦φ ⇒ •φ` (LTL rule Fun→) are unsound. The LTL
   induction rule (Ind), (K□), DL's (DL1)/(DL7) and RL's (Circularity) all pass
   through `◦A ⊓ ◦B ⇒ ◦(A ⊓ B)` and therefore do not go through. The existential
   side (`•, ⋄, ⋄w`, Knaster–Tarski induction, Peano induction) ports verbatim.
   Remedy: with definedness the *intuitionistic* box is definable as
   `◦ⁱφ := ∀y. (•y ⇒ y ∈ φ)` (value `⨅_b (R(b,m) ⇨ φ(b))`); without definedness
   it is not expressible, which argues for a primitive "all-path" application.

6. **Fixpoint reasoning ports completely.** With `ν` primitive the three negations
   of `νX.φ := ¬µX.¬φ[¬X/X]` disappear and Chapter 4 is symmetric in µ/ν
   (`IML/DerivedRules/Fixpoint.lean`).

## 1. The propositional and first-order basis (thesis §3.1, "FOL reasoning")

| # | Derivation | Verdict | Where classicality enters | Evidence |
|---|---|---|---|---|
| 1 | Axioms p1, p2 | (a) | — | Lean `p1`, `p2` |
| 2 | Axiom p3 `~~φ ⇒ φ` | (c!) | unsound in Heyting models | Lean `TopFilter.dne_not_derivable` |
| 3 | pairing, S-combinator, `orElim`, distributivity, `curry/uncurry`, `flip` | (a) | — | Lean `implAnd`, `implMp`, `orElim`, `andOrDistrib`, … |
| 4 | De Morgan `~(φ⊔ψ) ⟺ ~φ⊓~ψ`, `~φ⊔~ψ ⇒ ~(φ⊓ψ)`, `φ⊓~ψ ⇒ ~(φ⇒ψ)`, `~(φ⇒ψ) ⇒ ~ψ` | (a) | — | Lean `notOr`, `notOrIntro`, `notAndOfNotOr`, `andToNotImpl`, `notImplRight` |
| 5 | `~(φ⊓ψ) ⇒ ~φ⊔~ψ`, `~(φ⇒ψ) ⇒ φ`, `φ ⊔ ~φ` | (c!) | EM | unsound; evar-EM refuted in `IML/Examples/ExcludedMiddle.lean` (omega-sets branch), symbol-EM in Lean `TopFilter.em_not_derivable` |
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
| 18 | Prop 3.4 | equivalence congruence in arbitrary contexts | (a) | app contexts Lean; `∧,∨,⇒,∃,∀` by the mono lemmas; `µ,ν` by Lemma 4.3 | Lean `ctxFramingEquiv` + paper |
| 19 | — | `C[~~φ] ⇒ ~~C[φ]` (¬¬-propagation) | (c!) | sound, underivable | Lean `TopFilter.nnPropagation_not_derivable` |
| 20 | Thm 3.2 (N) | `φ ⊢ σᵈφ` | (a) | | Lean `boxNec` |
| 21 | Thm 3.2 (K) | `σᵈ(φ⇒ψ) ⇒ σᵈφ ⇒ σᵈψ` | (c?) | classical proof: `¬ψ ⇒ ¬φ ∨ ¬(φ⇒ψ)` (weak EM); reduces to #19; sound; not refuted by the chain model (needs a non-join-prime `⊤`) | paper |
| 22 | Thm 3.2 (Barcan) | `∀x.σᵈφ ⇒ σᵈ∀x.φ` | (c!) | = DNS `⨅¬¬φ_a ≤ ¬¬⨅φ_a`, fails in `Opens ℝ` | paper; converse Barcan Lean `boxConverseBarcan` |
| 23 | — | `σᵈ(φ⊓ψ) ⇒ σᵈφ ⊓ σᵈψ` | (a) | | Lean `boxAnd` |
| 24 | — | `σᵈφ ⊓ σᵈψ ⇒ σᵈ(φ⊓ψ)` | (c?) | needs #19 | paper |

## 3. Definedness, membership, totality (thesis §3.2)

All rows assume the definedness axiom `∀x.⌈x⌉` in `Γ` (`IsDefinedness`).

| # | Thesis | Statement | Verdict | Notes | Evidence |
|---|---|---|---|---|---|
| 25 | (3.19) | `⌈x⌉`, `⌈·⌉` monotone, `⌈⊥⌉ ⇒ ⊥`, `⌈φ⊔ψ⌉ ⟺`, `⌈∃φ⌉ ⟺ ∃⌈φ⌉` | (a) | | Lean `ceil_of_evar`, `ceil_mono`, `ceil_bot`, `ceil_or`, `ceil_exist` |
| 26 | Lemma 3.5/3.6 | `φ↔ψ ⊢ φ=ψ`; `φ=φ`; symmetry | (a) | | Lean `eqML_of_iff`, `eqML_refl`, `eqML_symm` |
| 27 | Lemma 3.7 | membership intro `φ ⊢ x ∈ φ` | (a) | | Lean `memIntro`, `memIntroAll` |
| 28 | Lemma 3.8 | membership elim `∀x.(x∈φ) ⊢ φ` | (b) | SINGLETON gives `x∈φ ⇒ x ⇒ ~~φ`, hence only `~~φ`; full form is *sound* and holds in the top-filter model, derivability **open** | Lean `memElimWeak`, `totalI_impl_nn` |
| 29 | Lemma 3.9 | `x∈y ⟺ x=y` | (c?) | (→) needs `¬(x↔y) ⇒ (x∧¬y)∨(¬x∧y)` then ¬¬-propagation; (←) needs membership EM | paper |
| 30 | Lemma 3.10 (→) | `x∈~φ ⇒ ~(x∈φ)` | (a) | | Lean `memNegElim` |
| 31 | Lemma 3.10 (←) | `~(x∈φ) ⇒ x∈~φ` | (c!) | membership EM; sound in Heyting models | Lean `TopFilter.memNegIntro_not_derivable` |
| 32 | Lemma 3.11 | Membership∨ | (a) | | Lean `memOr` |
| 33 | Lemma 3.12 | Membership∧ | (a)/(c?) | (→) Lean `memAndElim`; (←) `x∈φ ⊓ x∈ψ ⇒ x∈(φ⊓ψ)` classical via `∧ = ¬(¬∨¬)`; sound; derivable from `SingletonPos` | Lean `memAndIntro` (under `SingletonPos`) |
| 34 | Lemma 3.13 | Membership∃ | (a) | | Lean `memExist` |
| 35 | (new) | Membership⇒ (→) weak form `x∈(φ⇒ψ) ⇒ ~(x∈(φ⊓~ψ))` | (a) | full (→) needs #33(←); (←) `(x∈φ ⇒ x∈ψ) ⇒ x∈(φ⇒ψ)` refuted in the chain model (paper) | Lean `memImplElimWeak` |
| 36 | Lemma 3.14 | `C[φ] ⇒ ⌈φ⌉` | (c!) | membership EM at step 4; sound; underivable already for `C = □` | Lean `TopFilter.phi_impl_ceil_not_derivable`; with `SingletonPos`: Lean `ctxImplDefined` |
| 37 | Cor 3.1 | `⌊φ⌋ ⇒ φ` | (c!) | #36 plus DNE; weakening `⌊φ⌋ ⇒ ~~φ` under `SingletonPos` | Lean `total_elim_nn` |
| 38 | (new) | `⌊φ⌋ⁱ ⇒ ⌊φ⌋` (positive totality implies classical) | (a) | | Lean `totalI_impl_total` |
| 39 | Thm 3.3 | deduction theorem `Γ∪{ψ} ⊢ φ ⟹ Γ ⊢ ⌊ψ⌋ ⇒ φ` | (c!) | **false** for iML; the framing case needs `⌊ψ⌋ ⇒ (χ₁⇒χ₂) ⟹ χ₁ ⇒ χ₂ ⊔ ⌈~ψ⌉` (DNE on `⌈~ψ⌉`) | Lean `TopFilter.deductionTheorem_fails` |
| 40 | (variant of 39) | DT with `⌊ψ⌋ⁱ := ∀x.x∈ψ` | (b?) | semantically plausible (truncate `L` to `↓⨅ψ`); syntactic proof needs `⌊ψ⌋ⁱ ⇒ ψ` (#28, open) and "constant patterns propagate into contexts" (open) | paper |
| 41 | Lemma 3.15 | equality elimination | (c?) | via #39 | paper |
| 42 | Lemma 3.16 | functional substitution | (c?) | via #41 | paper |
| 43 | Lemma 3.17 | `C[φ₁ ∧ x∈φ₂] = C[φ₁] ∧ x∈φ₂` | (c?) | (→) membership EM at line 2; (←) predicate-pattern propagation, sound, not derived | paper |
| 44 | Lemma 3.18 | `∃y.(x=y ∧ φ) = φ[x/y]` | (c?) | via #43 | paper |
| 45 | Lemma 3.19 (→) | `∃y.(⌈y⊓φ⌉ ⊓ y) ⇒ φ` | (b) | only `~~φ` | Lean `existCeilEvar_impl_nn` |
| 46 | Lemma 3.19 (←) | `φ ⇒ ∃y.(⌈y⊓φ⌉ ⊓ y)` | (c?) | classical proof uses P's membership rules; derivable from `SingletonPos` | Lean `phi_impl_existCeilEvar` (under `SingletonPos`) |
| 47 | Lemma 3.20 | membership through symbols | (c?) | via #43, #46 | paper |
| 48 | Thm 3.4 | definedness completeness | (c!) | fails twice: P's rules Membership¬(←) etc. are unsound; and sound statements (#19, #36) are underivable | Lean (#19, #36) |
| 49 | §3.3 | local completeness via MCS | (c?) | MCS uses `¬φ ∈ Γ iff φ ∉ Γ` (Prop 3.6(2)); an intuitionistic version would need prime theories / Kripke-style canonical models; out of scope | paper |

## 4. Matching µ-logic (thesis Chapter 4)

| # | Thesis | Statement | Verdict | Notes | Evidence |
|---|---|---|---|---|---|
| 50 | Lemma 4.2 | ν pre-fixpoint and ν-KT | (a) | primitive in iML; no `¬µ¬` detour | Lean `nuPostFixpoint`, `nuCoinduction` |
| 51 | Lemma 4.3 | `φ⇒ψ ⊢ µX.φ ⇒ µX.ψ` (and ν) | (a) | | Lean `muMonoFromImpl`, `nuMonoFromImpl` |
| 52 | Lemma 4.4/4.5 | positive/negative contexts | (a) | induction on contexts using #13, #7, #51 (Lean only for the app-context and hypothesis forms) | paper |
| 53 | Lemma 4.6 | `µX.φ ⟺ φ[µX.φ/X]` | (a) | given syntactic monotonicity (#52) | Lean `muUnfold`, `nuUnfold` (monotonicity as hypothesis) |
| 54 | Lemma 4.7 | predicate patterns `⊢ ψ=⊤ ∨ ψ=⊥` propagate through contexts | (b) | the *definition* is classical (a decidability condition); replace by the propagation property `ψ ⊓ C[φ] ⟺ C[ψ ⊓ φ]` itself; then the lemma is a tautology and the substantive question becomes which patterns satisfy it (e.g. `⌊ψ⌋ⁱ` semantically does; syntactically open) | paper |
| 55 | Lemma 4.8 | `ψ ∧ µX.φ ⟺ µX.(ψ∧φ)` for predicate `ψ` | (a) | with the propagation-style definition of "predicate" the proof (KT + pre-fixpoint + 4.5) is intuitionistic | paper |
| 56 | Thm 4.2 | deduction theorem for Hµ | (c!) | as #39 | Lean `TopFilter.deductionTheorem_fails` |
| 57 | §4.2 | `⊥ := µX.X` vs primitive `⊥` | (a) | interderivable | Lean `muSvarIffBot`, `nuSvarIffTop` |

## 5. Expressive power (thesis Chapter 5)

### 5.1 Recursive symbols, initial algebras (§5.1, §5.5)

| # | Thesis | Statement | Verdict | Notes | Evidence |
|---|---|---|---|---|---|
| 58 | Lemma 5.5 | "plugging out" `C[φ] ⇒ ψ  iff  φ ⇒ ∃x.(x ∧ ⌊C[x] ⇒ ψ⌋)` | (c?) | uses `φ = ∃x.(x ∧ x∈φ)` (#46, #28) and `x∈φ` being a predicate pattern (#54) | paper |
| 59 | Thm 5.1 | pre-fixpoint/KT for recursive symbols | (c?) | via #58 | paper |
| 60 | Thm 5.6 | Peano induction from (No Junk) + KT | (a) | `⊤Nat = µD. zero ∨ succ(D)` is `evt succ zero`; the rule is `evtInduction` | Lean `peanoInduction` |
| 61 | Thm 5.7 | general structural induction | (a) | same shape, one KT per sort | paper |
| 62 | Lemma 5.2 | `succ(Ψ) ⇒ Ψ  iff  ∀x.(x∈Ψ ⇒ succ(x)∈Ψ)` | (c?) | the membership form needs #47 and #28 | paper |
| 63 | Thm 5.5 | `plus` is a defined function | (c?) | equational reasoning modulo `≃` rests on #41 | paper |

### 5.2 Transition systems, modal µ-calculus, temporal logics (§5.7–5.9, Prop. 5.6)

`• := next ⬝ ·`, `◦ := ~•~`, `⋄ := µX.φ ∨ •X`, `□ := νX.φ ∧ ◦X`, `⋄w := νX.φ ∨ •X`, `WF := µX.◦X`.

| # | Prop 5.6 item | Statement | Verdict | Notes | Evidence |
|---|---|---|---|---|---|
| 64 | (1)–(3) | `•⊥⟺⊥`, `•(φ∨ψ)⟺`, `•∃⟺∃•` | (a) | | Lean `nxBotIff`, `nxOr`, `nxExist` |
| 65 | (4) | `◦⊤ ⟺ ⊤` | (a) | | Lean `allnxTop` |
| 66 | (5) | `◦(φ∧ψ) ⟺ ◦φ ∧ ◦ψ` | (a)/(c?) | (→) Lean `allnxAnd`; (←) sound (`◦` is `R ⇨ ¬¬·` and `¬¬` preserves `⊓`), needs #19 | paper |
| 67 | (6) | `◦∀x.φ ⟺ ∀x.◦φ` | (a)/(c!) | (→) Lean `allnxForall`; (←) is Barcan, unsound (#22) | |
| 68 | (7) | `φ ⇒ ⋄φ`, `•⋄φ ⇒ ⋄φ` | (a) | | Lean `evtIntro`, `nxEvt` |
| 69 | (8) | `□φ ⇒ φ`, `□φ ⇒ ◦□φ` | (a) | | Lean `alwElim`, `alwNext` |
| 70 | (9) | `φ ⇒ ⋄wφ`, `•⋄wφ ⇒ ⋄wφ` | (a) | | Lean `wevtIntro`, `nxWevt` |
| 71 | (10) | monotonicity of `•, ◦, ⋄, □, ⋄w` | (a) | | Lean `nxMono`, `allnxMono`, `evtMono`, `alwMono`, `wevtMono` |
| 72 | (11)–(13) | `⋄⊥⟺⊥`, `⋄(φ∨ψ)⟺⋄φ∨⋄ψ`, `⋄∃⟺∃⋄` | (a) | (13) paper (lifting bookkeeping only) | Lean `evtBot`, `evtOr`, `evtOrR` |
| 73 | (14) | `□⊤` | (a) | | Lean `alwTop` |
| 74 | (15) | `□(φ∧ψ) ⟺ □φ∧□ψ` | (a)/(c?) | (→) Lean `alwAnd`; (←) needs #66(←) | |
| 75 | (16) | `□∀ ⟺ ∀□` | (a)/(c!) | (→) paper; (←) Barcan | |
| 76 | (17) | `□φ ⟺ ¬⋄¬φ` | (a)/(c!) | (→) Lean `alwToNotEvtNot`; (←) needs `~~φ ⇒ φ`; even `¬⋄¬φ ⇒ □~~φ` needs #19 | |
| 77 | (18) | `◦φ₁ ∧ •φ₂ ⇒ •(φ₁∧φ₂)` | (c!) | unsound: semantically `•(~~φ₁ ∧ φ₂)`; the `~~` variant is sound but not derived (refuted in the top-filter model over `Opens ℝ`, i.e. it needs a positive-transfer principle) | paper |
| 78 | (19) | `◦(φ₁⇒φ₂) ∧ •φ₁ ⇒ •φ₂` | (c!) | via (18) | paper |
| 79 | (20) | `⋄wφ ⟺ (WF ⇒ ⋄φ)` | (c?) | (→) via (19); (←) case analysis on `WF` | paper |
| 80 | (21),(22) | `⋄w` distributes over `∨`, `∃` | (a)/(c?) | (←) by monotonicity (paper); (→) via (20) | paper |
| 81 | (23) | idempotence of `⋄, □, ⋄w` | (a) | | Lean `evtIdem`, `alwIdem` (+ paper for the trivial halves) |
| 82 | (24),(25) | `WF ⟺ µX.◦ᵏX`, `WF ⟺ µX.◦□X` | (a) | KT + pre-fixpoint + Lemma 4.3 only | paper |
| 83 | (26) | `□φ₁ ∧ ⋄wφ₂ ⇒ ⋄w(φ₁∧φ₂)` | (c?) | via (18) | paper |
| 84 | (27) | `□(φ₁⇒φ₂) ∧ φ₁ ⇒ φ₂` | (a) | | paper (`alwElim` + mp) |
| 85 | Lemma 5.6 (LTL) | (K◦),(N◦),(K□),(N□),(Fun),(U1),(U2),(Ind) | mixed | (N◦),(N□),(U1) (a) paper; (K◦) = #21 (c?); (K□) and (Ind) need #66(←) (c?); (Fun→) `•⊤ ⊢ ◦φ ⇒ •φ` unsound (c!): in the chain model `◦c = ⊤`, `•⊤ = ⊤`, `•c = ⊥`; (U2) via (Fun) | paper |
| 86 | Lemma 5.8 (finite LTL) | (coInd),(Fix),(¬◦) | (a)/(c!) | (coInd),(Fix) by KT (paper); (¬◦) via (Fun) | paper |
| 87 | Lemma 5.10 (CTL) | 10 rules | mixed | EX/EU rules (a); AX/AU rules need #66(←) (c?) | paper |
| 88 | Lemma 5.12 (DL) | (Gen),(DL1),(DL2),(DL7) | mixed | (Gen) (a) by (N)+coinduction; (DL1) is (K) for `[α]` (c?); (DL2 for `β*`) (a) by KT/park; (DL7) induction needs `[α]A ∧ [α]B ⇒ [α](A∧B)` (c?) | paper |
| 89 | Lemma 5.14 (RL) | RL proof rules | mixed | Reflexivity, Consequence, Case analysis, Abstraction, Transitivity(C=∅) (a) paper; Transitivity(C≠∅) and Circularity via (18),(20),(25) (c?); Logic framing via predicate propagation (c?) | paper |

### 5.3 Second-order logic, λ-calculus, term-generic logic (§5.6, 5.12, 5.13)

| # | Thesis | Statement | Verdict | Notes |
|---|---|---|---|---|
| 90 | Def 5.5 | powersets via `extension(α) = X`, `intension(φ) := ∃α.(α ∧ extension(α) = φ)` | (b) | definitional; `=` is `⌊↔⌋` and must be replaced by a positive equality `∀z.(z∈φ ⟺ z∈ψ)` to have the intended Heyting meaning; the meta-theorems (5.8, 5.9) are model-theoretic and outside the scope of derivability |
| 91 | (5.110) | `(π x⃗ = ⊤) ∨ (π x⃗ = ⊥)` (TGL predicates) | (c!) | a decidability axiom; only its classical consequences fail — the axiom itself may of course be *assumed*, but it forces the predicate symbols to be Boolean, defeating the point of an intuitionistic logic |
| 92 | Thm 5.16 | extensiveness of `Γλ` | (c?) | needs equational reasoning (#41) |

## 6. AML and the proof checker (thesis Chapter 7)

| # | Thesis | Statement | Verdict | Notes |
|---|---|---|---|---|
| 93 | (7.16) | sorted negation `¬ₛφ := ¬φ ∧ ⊤ₛ` | (b) | fine as a definition; sorted EM/DNE fail as their unsorted versions do |
| 94 | (7.9),(7.11) | `⊆ := ⌊⇒⌋` in (Symbol Arity), wellsortedness | (b) | use `⌊·⌋ⁱ` (`∀x. x ∈ (φ ⇒ ψ)`) or a plain implication axiom; with `⌊⇒⌋` the axiom only says `¬¬`-inclusion |
| 95 | §7.4 | `or-is-sugar`, `and-is-sugar`, `proof-rule-prop-3` | (c!) | the Metamath checker's sugar `φ∨ψ := ¬φ→ψ`, `φ∧ψ := ¬(¬φ∨¬ψ)` is unsound intuitionistically (`(¬φ→ψ) ⇒ φ∨ψ` fails); an iML checker needs the 12-constructor syntax and the 27 rules, exactly as `IML/Proof.lean` |

## 7. Tally

95 numbered rows (some bundle two directions or several rules):

* **(a)** 42 rows fully derivable — 37 backed by Lean proofs, 5 on paper
  (rows 52, 55, 61, 82, 84);
* **(a)/(c) split by direction** 6 rows (33, 66, 67, 74, 75, 76): the
  monotonicity/converse-Barcan direction is derived in Lean, the other direction
  is (c?) (needs ¬¬-propagation) or (c!) (Barcan, DNE);
* **mixed rule tables** 5 rows (85–89: LTL, finite LTL, CTL, DL, RL): the
  existential/Knaster–Tarski rules port, every rule that distributes the dual box
  over a conjunction does not;
* **(b)** 7 rows (28, 40, 45, 54, 90, 93, 94);
* **(c!)** 17 rows with proved underivability or unsoundness (2, 5, 9, 11, 12,
  19, 22, 31, 36, 37, 39, 48, 56, 77, 78, 91, 95) — 8 of them by Lean
  countermodel, the rest by unsoundness arguments on paper;
* **(c?)** 18 rows not derived and not refuted (21, 24, 29, 41–44, 46, 47, 49,
  58, 59, 62, 63, 79, 80, 83, 92).

## 8. What is in `IML/DerivedRules/`

All files are sorry-free; `IML.ctxBot` and `IML.p2` are axiom-free, everything
else uses only `propext`, `Classical.choice`, `Quot.sound` (checked with
`#print axioms`).

| File | Lines | Content |
|---|---|---|
| `Propositional.lean` | 249 | IPC toolkit: `implSelf, p1, p2, implAnd, implMp, orElim, andOrDistrib, contrapositive, dni, tripleNegElim, notOr, notOrIntro, nnImpl, nnAnd, nnExcludedMiddle`, `⟺` lemmas |
| `FOL.lean` | 243 | `evarSubst_evarLift`, `evarSubst_evarLiftFrom_succ` (12-constructor ports); quantifier rules; `forallImplExist`, `pushConjInExist` |
| `Context.lean` | 156 | `ctxFraming, ctxBot, ctxPropagationOr(R), liftEVar, evarLift_fill, ctxPropagationExist(R), doubleNegCtx`, dual box `AppCtx.box` with `boxNec, boxMono, boxAnd, boxTop, boxConverseBarcan` |
| `Fixpoint.lean` | 159 | `svarSubst_svarLift`, `svarLift_positive`, µ/ν rules, `muSvarIffBot`, `nuSvarIffTop`, unfolding modulo monotonicity |
| `Definedness.lean` | 249 | `⌈·⌉, ⌊·⌋, ⌊·⌋ⁱ, ∈ₘₗ, =ₘₗ`; rows 25–38, 45–46 above; `SingletonPos` and its consequences |
| `Temporal.lean` | 205 | `nx, allnx, evt, alw, wevt, wf`; rows 64–76, 81; `peanoInduction` |
| `TopFilterModel.lean` | 683 | the non-standard model, soundness of all 27 rules for it (`TopFilter.soundness`), and the seven refutations (`nnPropagation_not_derivable, dne_not_derivable, phi_impl_ceil_not_derivable, memNegIntro_not_derivable, memEM_not_derivable, em_not_derivable, deductionTheorem_fails`) |
| `../DerivedRules.lean` | | umbrella import |

`IML.lean` was not touched; to include the new modules add
`import IML.DerivedRules` to it.

Left unformalized (on-paper verdicts only): syntactic monotonicity in general
contexts (Lemma 4.5) and hence the unconditional µ-unfolding; Prop. 5.6 items
(13), (20)–(22), (24)–(27) and the LTL/CTL/DL/RL rule tables; the soundness of
the sound-but-underivable statements in the *standard* `HModel` semantics (these
are one-line lattice computations, stated in the text, not checked in Lean).

## 9. Open questions worth settling next

1. Is `(∀x. x ∈ φ) ⇒ φ` derivable? Sound; valid in the top-filter model; every
   attempt yields only `~~φ`. A countermodel needs a carrier with at least two
   points and non-Boolean application.
2. Is Membership∧(←) derivable? Same status (valid in the top-filter model).
3. Does `SingletonPos` (+ the 27 rules) prove `(K)` for the dual box, or is a
   separate ¬¬-propagation axiom needed? The top-filter model separates them, so
   both would be needed to recover the classical membership calculus.
4. A complete axiomatization for the Heyting semantics presumably needs
   `SingletonPos`, ¬¬-propagation, and possibly `(∀x. x∈φ) ⇒ φ`; whether these
   suffice is open. A Kripke-style canonical model (prime theories instead of
   MCS) would be the natural approach.

## 10. Shortlist for a presentation

1. **⊥-propagation needs no rule** — SINGLETON already gives it constructively
   (`ctxBot`, axiom-free). Closes the obvious suspected gap.
2. **A checked incompleteness theorem**: the top-filter model shows
   `C[~~φ] ⇒ ~~C[φ]` and `φ ⇒ ⌈φ⌉` are sound but underivable; the same model
   kills p3, Membership¬(←), membership-EM. One ~700-line file, all 27 rules.
3. **The deduction theorem is false** for iML in the thesis' form
   (`deductionTheorem_fails`), because `⌊·⌋ = ~⌈~·⌉` is the wrong totality;
   the positive `∀x. x∈ψ` is the right one, and `⌊ψ⌋ⁱ ⇒ ⌊ψ⌋` is derivable.
4. **One classical step explains all of §3.2**: the membership excluded middle.
   `SingletonPos` (sound, classically derivable, independent of ¬¬-propagation)
   is the minimal positive replacement and recovers Lemma 3.14.
5. **The dual box is the ¬¬-box**: Barcan and `◦φ₁∧•φ₂ ⇒ •(φ₁∧φ₂)` are unsound,
   (K) and `◦`-conjunction are unprovable, so LTL's (Ind), CTL's AU rules,
   DL's (DL7), RL's (Circularity) do not port, while the whole existential /
   Knaster–Tarski side (`⋄, ⋄w, WF`, Peano induction) ports verbatim. Suggests a
   primitive all-path application, or `◦ⁱφ := ∀y.(•y ⇒ y∈φ)` when definedness
   is available.
