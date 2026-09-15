import IML.DerivedRules.Definedness
import IML.DerivedRules.Temporal
import IML.DerivedRules.TopFilterModel

/-!
# Small Heyting models refuting classical statements in the current system

Every `HModel` is a model of the current proof system `IML.Proof`
(`IML.soundness`), so a statement that fails in some `HModel` is underivable in
the current system. This file collects the refutations of the survey
(`iml-expressivity-report.md`) that only need genuinely Heyting truth values,
not a non-standard application. Two models, both over a complete chain `L`
with a middle element `u` (`⊥ < u < ⊤`), symbols `s ↦ ⊤` (used as definedness
and as `next`) and `c ↦ u`:

* `pt`: one-point carrier, application interpreted as `⊓`. Patterns are then
  just `L`-valued propositional formulas (quantifiers are the identity, element
  variables are `⊤`). The definedness axiom `∀x.⌈x⌉` holds. Refuted:
  double-negation elimination, excluded middle, `⌊φ⌋ ⇒ φ` for the classical
  totality `⌊φ⌋ := ~⌈~φ⌉` (thesis Corollary 3.1 literally), the membership
  excluded middle `⌈x⌉ ⇒ ⌈x ⊓ φ⌉ ⊔ ⌈x ⊓ ~φ⌉`, equality elimination for the
  classical equality `⌊φ ⟺ ψ⌋` (Lemma 3.15 literally), the deduction theorem
  (Theorem 3.3 / 4.2) with `⌊·⌋`, and Prop. 5.6 items (18), (19) and the LTL
  rule (Fun→) for the double-negation box `◦ := ~•~`.
* `tp`: two-point carrier with `L`-valued equality `E a b = u` for `a ≠ b`,
  application `⊤` everywhere. Refuted: Lemma 3.9(←) `x = y ⇒ x ∈ y` (with
  `x = y := ⌊x ⟺ y⌋`, whose value is `¬¬E x y` while `x ∈ y` has value `E x y`).

These replace the corresponding results of `TopFilterModel.lean`, which
concern the published system only.

Notation: this file does not `open Pattern` (the lattice and pattern
connectives share notation); the scoped `⌈·⌉`, `⌊·⌋`, `∈ₘₗ`, `=ₘₗ` notations
of `Definedness.lean` are used through `HasCeil Bool`.
-/

namespace IML.PointModel

open IML.TopFilter (himp_bot_of_ne_bot nn_of_ne_bot one_ne_bot one_ne_top)

variable {L : Type*} [Order.Frame L]

-- ─────────────────────────────────────────────────────────────
-- The models
-- ─────────────────────────────────────────────────────────────

/-- The one-point model with symbol values `v`; application is `⊓`. -/
abbrev pt {Symbol : Type} (v : Symbol → L) : HModel Symbol L where
  Carrier := Unit
  E _ _ := ⊤
  E_refl _ := rfl
  E_symm _ _ := rfl
  E_trans _ _ _ := le_top
  appInterp _ _ _ := ⊤
  symInterp s _ := v s
  symInterp_ext _ _ _ := inf_le_right
  appInterp_ext₁ _ _ _ _ := inf_le_right
  appInterp_ext₂ _ _ _ _ := inf_le_right
  appInterp_ext₃ _ _ _ _ := inf_le_right

/-- Symbols: `true ↦ ⊤` (definedness / next), `false ↦ u`. -/
abbrev cm (u : L) : HModel Bool L := pt (fun b => if b then ⊤ else u)

/-- The two-point model with equality value `u` between distinct points and
application `⊤`; symbols as in `cm`. -/
abbrev tp (u : L) : HModel Bool L where
  Carrier := Bool
  E a b := if a = b then ⊤ else u
  E_refl _ := if_pos rfl
  E_symm a b := by
    by_cases h : a = b
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  E_trans a b c := by split_ifs <;> simp_all
  appInterp _ _ _ := ⊤
  symInterp s _ := if s then ⊤ else u
  symInterp_ext _ _ _ := inf_le_right
  appInterp_ext₁ _ _ _ _ := inf_le_right
  appInterp_ext₂ _ _ _ _ := inf_le_right
  appInterp_ext₃ _ _ _ _ := inf_le_right

instance : HasCeil Bool := ⟨true⟩

@[simp] theorem ceil_eq_true : (HasCeil.ceil : Bool) = true := rfl

/-- The symbol interpreted as `⊤` (definedness and `next`). -/
abbrev s : Pattern Bool := .symbol true
/-- The symbol interpreted as `u`. -/
abbrev c : Pattern Bool := .symbol false
abbrev x₀ : Pattern Bool := .evar 0
abbrev x₁ : Pattern Bool := .evar 1

/-- The definedness theory `{∀x. ⌈x⌉}`. -/
def defTheory : Set (Pattern Bool) := {.forallP ⌈x₀⌉}

instance : IsDefinedness Bool defTheory := ⟨Set.mem_singleton _⟩

/-- The valuation of `cm u` (every set variable `⊥`). -/
def ρ₀ (u : L) : HValuation (cm u) where
  evar _ := ()
  svar _ _ := ⊥
  svar_ext _ _ _ := inf_le_right

/-- The valuation of `tp u`: `x₀ ↦ true`, every other variable `↦ false`. -/
def ρ₁ (u : L) : HValuation (tp u) where
  evar i := decide (i = 0)
  svar _ _ := ⊥
  svar_ext _ _ _ := inf_le_right

-- ─────────────────────────────────────────────────────────────
-- Truth values in `cm u`
-- ─────────────────────────────────────────────────────────────

section Chain
variable {L : Type*} [CompleteLinearOrder L] (u : L)

theorem cm_definedness : ∀ γ ∈ defTheory, HValid (cm u) γ := by
  intro γ hγ
  rw [defTheory, Set.mem_singleton_iff] at hγ
  subst hγ
  intro ρ m
  simp [Pattern.ceil]

/-- `~~c ⇒ c` has value `u`. -/
theorem cm_dne (hu₁ : u ≠ ⊥) (ρ : HValuation (cm u)) :
    hinterp (cm u) ρ (.impl (.neg (.neg c)) c) () = u := by
  simp only [Pattern.neg, hinterp_impl, hinterp_bot, hinterp_symbol, ↓reduceIte,
    Bool.false_eq_true]
  rw [nn_of_ne_bot hu₁, top_himp]

/-- `c ⊔ ~c` has value `u`. -/
theorem cm_em (hu₁ : u ≠ ⊥) (ρ : HValuation (cm u)) :
    hinterp (cm u) ρ (.disj c (.neg c)) () = u := by
  simp only [Pattern.neg, hinterp_disj, hinterp_impl, hinterp_bot, hinterp_symbol, ↓reduceIte,
    Bool.false_eq_true]
  rw [himp_bot_of_ne_bot hu₁, sup_bot_eq]

/-- `⌊c⌋ ⇒ c` (Corollary 3.1 for the classical totality) has value `u`. -/
theorem cm_total_impl (hu₁ : u ≠ ⊥) (ρ : HValuation (cm u)) :
    hinterp (cm u) ρ (.impl ⌊c⌋ c) () = u := by
  simp only [Pattern.total, Pattern.ceil, Pattern.neg, hinterp_impl, hinterp_bot, hinterp_app,
    hinterp_symbol, ceil_eq_true, ↓reduceIte, Bool.false_eq_true, iSup_unique, inf_top_eq,
    top_inf_eq]
  rw [himp_bot_of_ne_bot hu₁]
  simp

/-- The membership excluded middle `⌈x⌉ ⇒ ⌈x ⊓ c⌉ ⊔ ⌈x ⊓ ~c⌉` has value `u`. -/
theorem cm_memEM (hu₁ : u ≠ ⊥) (ρ : HValuation (cm u)) :
    hinterp (cm u) ρ (.impl ⌈x₀⌉ (.disj (x₀ ∈ₘₗ c) (x₀ ∈ₘₗ (.neg c)))) () = u := by
  simp only [Pattern.memML, Pattern.ceil, Pattern.neg, hinterp_impl, hinterp_disj, hinterp_conj,
    hinterp_bot, hinterp_app, hinterp_symbol, hinterp_evar, ceil_eq_true, ↓reduceIte,
    Bool.false_eq_true, iSup_unique, inf_top_eq, top_inf_eq]
  rw [himp_bot_of_ne_bot hu₁]
  simp

/-- Equality elimination for the classical equality, `(⊤ =ₘₗ c) ⇒ (⊤ ⇒ c)`,
has value `u`. -/
theorem cm_eqML_elim (hu₁ : u ≠ ⊥) (ρ : HValuation (cm u)) :
    hinterp (cm u) ρ (.impl (Pattern.top =ₘₗ c) (.impl Pattern.top c)) () = u := by
  simp only [Pattern.eqML, Pattern.total, Pattern.iff, Pattern.top, Pattern.ceil, Pattern.neg,
    hinterp_impl, hinterp_conj, hinterp_bot, hinterp_app, hinterp_symbol, ceil_eq_true,
    ↓reduceIte, Bool.false_eq_true, iSup_unique, inf_top_eq, top_inf_eq, bot_himp, top_himp,
    himp_top]
  rw [himp_bot_of_ne_bot hu₁]
  simp

/-- Prop. 5.6(18), `◦c ⊓ •⊤ ⇒ •(c ⊓ ⊤)`, has value `u` (`next := s`). -/
theorem cm_allnx_nx_and (hu₁ : u ≠ ⊥) (ρ : HValuation (cm u)) :
    hinterp (cm u) ρ (.impl (.conj (allnx true c) (nx true Pattern.top))
      (nx true (.conj c Pattern.top))) () = u := by
  simp only [allnx, nx, Pattern.top, Pattern.neg, hinterp_impl, hinterp_conj, hinterp_bot,
    hinterp_app, hinterp_symbol, ↓reduceIte, Bool.false_eq_true, iSup_unique, inf_top_eq,
    top_inf_eq, bot_himp]
  rw [himp_bot_of_ne_bot hu₁]
  simp

/-- Prop. 5.6(19), `◦(⊤ ⇒ c) ⊓ •⊤ ⇒ •c`, has value `u`. -/
theorem cm_allnx_nx_impl (hu₁ : u ≠ ⊥) (ρ : HValuation (cm u)) :
    hinterp (cm u) ρ (.impl (.conj (allnx true (.impl Pattern.top c)) (nx true Pattern.top))
      (nx true c)) () = u := by
  simp only [allnx, nx, Pattern.top, Pattern.neg, hinterp_impl, hinterp_conj, hinterp_bot,
    hinterp_app, hinterp_symbol, ↓reduceIte, Bool.false_eq_true, iSup_unique, inf_top_eq,
    top_inf_eq, bot_himp, top_himp]
  rw [nn_of_ne_bot hu₁]
  simp

/-- LTL (Fun→): `◦c ⇒ •c` has value `u`, while its hypothesis `•⊤` is valid. -/
theorem cm_allnx_impl_nx (hu₁ : u ≠ ⊥) (ρ : HValuation (cm u)) :
    hinterp (cm u) ρ (.impl (allnx true c) (nx true c)) () = u := by
  simp only [allnx, nx, Pattern.neg, hinterp_impl, hinterp_bot, hinterp_app, hinterp_symbol,
    ↓reduceIte, Bool.false_eq_true, iSup_unique, inf_top_eq, top_inf_eq]
  rw [nn_of_ne_bot hu₁]
  simp

theorem cm_nxTop_valid : ∀ γ ∈ ({nx true Pattern.top} : Set (Pattern Bool)), HValid (cm u) γ := by
  intro γ hγ
  rw [Set.mem_singleton_iff] at hγ
  subst hγ
  intro ρ m
  simp [nx, Pattern.top, Pattern.neg]

-- ─────────────────────────────────────────────────────────────
-- Truth values in `tp u`
-- ─────────────────────────────────────────────────────────────

theorem tp_definedness : ∀ γ ∈ defTheory, HValid (tp u) γ := by
  intro γ hγ
  rw [defTheory, Set.mem_singleton_iff] at hγ
  subst hγ
  intro ρ m
  simp [Pattern.ceil, iSup_bool_eq, iInf_bool_eq, HValuation.pushEVar]

/-- `x₀ ∈ x₁` has value `u` (`x₀ ↦ true`, `x₁ ↦ false`). -/
theorem tp_mem (m : Bool) : hinterp (tp u) (ρ₁ u) (x₀ ∈ₘₗ x₁) m = u := by
  simp [Pattern.memML, Pattern.ceil, ρ₁, iSup_bool_eq]

/-- `x₀ =ₘₗ x₁` has value `⊤`: it is `¬¬E x₀ x₁ = ¬¬u`. -/
theorem tp_eqML (hu₁ : u ≠ ⊥) (m : Bool) :
    hinterp (tp u) (ρ₁ u) (x₀ =ₘₗ x₁) m = ⊤ := by
  have hc : uᶜ = ⊥ := by rw [← himp_bot]; exact himp_bot_of_ne_bot hu₁
  simp [Pattern.eqML, Pattern.total, Pattern.iff, Pattern.ceil, Pattern.neg, ρ₁, iSup_bool_eq, hc]

end Chain

-- ─────────────────────────────────────────────────────────────
-- Underivability in the current system (`L := ℕ∞`, `u := 1`)
-- ─────────────────────────────────────────────────────────────

theorem empty_valid (u : ℕ∞) : ∀ γ ∈ (∅ : Set (Pattern Bool)), HValid (cm u) γ :=
  fun _ hγ => absurd hγ (Set.notMem_empty _)

/-- Double-negation elimination (axiom p3) is not derivable in the current system. -/
theorem dne_not_derivable :
    IsEmpty ((∅ : Set (Pattern Bool)) ⊩ᵢ .impl (.neg (.neg c)) c) := by
  constructor; intro h
  have := soundness h ℕ∞ (cm 1) (empty_valid 1) (ρ₀ 1) ()
  rw [cm_dne 1 one_ne_bot] at this
  exact one_ne_top this

/-- Excluded middle for a symbol is not derivable from definedness in the current system. -/
theorem em_not_derivable : IsEmpty (defTheory ⊩ᵢ .disj c (.neg c)) := by
  constructor; intro h
  have := soundness h ℕ∞ (cm 1) (cm_definedness 1) (ρ₀ 1) ()
  rw [cm_em 1 one_ne_bot] at this
  exact one_ne_top this

/-- Thesis Corollary 3.1 in its literal form, `⌊φ⌋ ⇒ φ` for `⌊φ⌋ := ~⌈~φ⌉`, is
not derivable from definedness in the current system (`IML.total_elim_nn`
gives `⌊φ⌋ ⇒ ~~φ`, and `IML.totalI_impl` gives `⌊φ⌋ⁱ ⇒ φ`). -/
theorem total_impl_not_derivable : IsEmpty (defTheory ⊩ᵢ .impl ⌊c⌋ c) := by
  constructor; intro h
  have := soundness h ℕ∞ (cm 1) (cm_definedness 1) (ρ₀ 1) ()
  rw [cm_total_impl 1 one_ne_bot] at this
  exact one_ne_top this

/-- The membership excluded middle is not derivable from definedness in the
current system. -/
theorem memEM_not_derivable :
    IsEmpty (defTheory ⊩ᵢ .impl ⌈x₀⌉ (.disj (x₀ ∈ₘₗ c) (x₀ ∈ₘₗ (.neg c)))) := by
  constructor; intro h
  have := soundness h ℕ∞ (cm 1) (cm_definedness 1) (ρ₀ 1) ()
  rw [cm_memEM 1 one_ne_bot] at this
  exact one_ne_top this

/-- Equality elimination (thesis Lemma 3.15) for the classical equality
`φ =ₘₗ ψ := ⌊φ ⟺ ψ⌋` is not derivable, already in the instance
`(⊤ = c) ⇒ (⊤ ⇒ c)`. For the positive equality `=ⁱₘₗ` it is derivable
(`IML.eqI_elim`, `IML.eqI_elim_ctx`). -/
theorem eqML_elim_not_derivable :
    IsEmpty (defTheory ⊩ᵢ .impl (Pattern.top =ₘₗ c) (.impl Pattern.top c)) := by
  constructor; intro h
  have := soundness h ℕ∞ (cm 1) (cm_definedness 1) (ρ₀ 1) ()
  rw [cm_eqML_elim 1 one_ne_bot] at this
  exact one_ne_top this

/-- The deduction theorem of the thesis (Theorem 3.3 / 4.2), "`Γ ∪ {ψ} ⊢ φ`
implies `Γ ⊢ ⌊ψ⌋ ⇒ φ`" with `⌊ψ⌋ := ~⌈~ψ⌉`, is **false** for the current
system: for `ψ = φ = c ⊔ ~c` it would give `⊢ ⌊c ⊔ ~c⌋ ⇒ c ⊔ ~c`, but
`⌊c ⊔ ~c⌋` is derivable (the double negation of excluded middle, pushed
through `⌈·⌉`), so excluded middle would be derivable. -/
theorem deductionTheorem_fails :
    ¬ ∀ (ψ φ : Pattern Bool), Nonempty ((defTheory ∪ {ψ}) ⊩ᵢ φ) →
        Nonempty (defTheory ⊩ᵢ .impl ⌊ψ⌋ φ) := by
  intro hDT
  obtain ⟨h⟩ := hDT (.disj c (.neg c)) (.disj c (.neg c))
    ⟨.assumption (Set.mem_union_right _ (Set.mem_singleton _))⟩
  have htot : defTheory ⊩ᵢ ⌊.disj c (.neg c)⌋ :=
    .syllogism (ceil_mono nnExcludedMiddle) ceil_bot
  exact em_not_derivable.false (.mp h htot)

/-- Prop. 5.6(18) `◦φ₁ ⊓ •φ₂ ⇒ •(φ₁ ⊓ φ₂)` is not derivable in the current system. -/
theorem allnx_nx_and_not_derivable :
    IsEmpty ((∅ : Set (Pattern Bool)) ⊩ᵢ
      .impl (.conj (allnx true c) (nx true Pattern.top)) (nx true (.conj c Pattern.top))) := by
  constructor; intro h
  have := soundness h ℕ∞ (cm 1) (empty_valid 1) (ρ₀ 1) ()
  rw [cm_allnx_nx_and 1 one_ne_bot] at this
  exact one_ne_top this

/-- Prop. 5.6(19) `◦(φ₁ ⇒ φ₂) ⊓ •φ₁ ⇒ •φ₂` is not derivable in the current system. -/
theorem allnx_nx_impl_not_derivable :
    IsEmpty ((∅ : Set (Pattern Bool)) ⊩ᵢ
      .impl (.conj (allnx true (.impl Pattern.top c)) (nx true Pattern.top)) (nx true c)) := by
  constructor; intro h
  have := soundness h ℕ∞ (cm 1) (empty_valid 1) (ρ₀ 1) ()
  rw [cm_allnx_nx_impl 1 one_ne_bot] at this
  exact one_ne_top this

/-- The LTL rule (Fun→), `•⊤ ⊢ ◦φ ⇒ •φ`, fails in the current system. -/
theorem allnx_impl_nx_not_derivable :
    IsEmpty (({nx true Pattern.top} : Set (Pattern Bool)) ⊩ᵢ .impl (allnx true c) (nx true c)) := by
  constructor; intro h
  have := soundness h ℕ∞ (cm 1) (cm_nxTop_valid 1) (ρ₀ 1) ()
  rw [cm_allnx_impl_nx 1 one_ne_bot] at this
  exact one_ne_top this

/-- Thesis Lemma 3.9(←), `x = y ⇒ x ∈ y` for the classical equality
`x =ₘₗ y := ⌊x ⟺ y⌋`, is not derivable from definedness in the current
system: `x = y` has Heyting value `¬¬E x y` while `x ∈ y` has value `E x y`. -/
theorem eqML_mem_not_derivable :
    IsEmpty (defTheory ⊩ᵢ .impl (x₀ =ₘₗ x₁) (x₀ ∈ₘₗ x₁)) := by
  constructor; intro h
  have := soundness h ℕ∞ (tp 1) (tp_definedness 1) (ρ₁ 1) true
  rw [hinterp_impl, tp_eqML 1 one_ne_bot, tp_mem 1, top_himp] at this
  exact one_ne_top this

end IML.PointModel
