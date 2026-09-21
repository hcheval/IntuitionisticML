import IML.SingletonAlt.GModel
import IML.DerivedRules.TopFilterModel
import IML.DerivedRules.Temporal
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Order.UpperLower.Principal

/-!
# The depth-one model: ¬¬-propagation and the modal (K) rule are underivable
# in the current system

`TopFilterModel.lean` refutes the ¬¬-propagation `C[~~φ] ⇒ ~~C[φ]` for the
*published* system, but its model refutes the positive SINGLETON
`singletonStrong` too (`TopFilter.cm_singletonStrong`), so it says nothing
about the current system `IML.Proof`. This file gives a generalized model
(`GModel`, see `IML/SingletonAlt/GModel.lean`) that validates
**every rule of the current system, `singletonStrong` included**
(`valid_strong`), and still refutes ¬¬-propagation. Hence the current system
is incomplete for its Heyting semantics as well (`nnPropagation_not_derivable`).

Over a frame in which `⊤` is join-prime but which is not a chain (`L₅`
below) the same model also refutes the modal (K) rule for the dual box
`σᵈφ := ~(σ ⬝ ~φ)` and the conjunction law `σᵈφ ⊓ σᵈψ ⇒ σᵈ(φ ⊓ ψ)`
(`boxK_not_derivable`, `boxAnd_not_derivable`), both of which are valid in
every `HModel`.

## The model

Values in a frame `L` whose top is join-prime (`TopJoinPrime`: every complete
chain, and `L₅`); carrier `Bool`; crisp admissible element denotations
`χ 0 = {0}`, `χ 1 = {1}`; the twist `δ := j` of the top-filter model
(`j p = ⊤` iff `p = ⊤`, else `⊥`); and the one-step application relation

    R a b m := ⊤  iff  m = 1 and a = b = 0,

so an application lands on `1` exactly when both arguments hold at `0`, and
nothing lands on `0`. Consequently every non-hole context `C` satisfies
`C[Y](0) = ⊥` and `C[Y](1) = j(Y(0)) ⊓ k_C` (`shape`): contexts see the hole
only at the point `0` and only through `j`.

## Why `singletonStrong` holds

Its instances `C₁[x ⊓ φ] ⊓ C₂[x ⊓ ψ] ⇒ C₂[x ⊓ (φ ⊓ ψ)]` are checked at the
two points. At `0` every non-hole context is `⊥`. At `1`, if both contexts
are non-hole the claim is `j` preserving `⊓`; if exactly one is the hole the
premise contains both `x(1)` and `j(x(0))`, which is `⊥` for a crisp `x`. The
point is that a context never lands on the point it looks at, so the
"inflationary" instances `x ⊓ φ ⊓ C[x] ⇒ C[x ⊓ φ]` that broke the top-filter
model are vacuous here. (The definedness axiom `∀x.⌈x⌉` therefore fails in
this model, which is why it settles nothing about the definedness theory; see
the report for why no model of this kind can.)

## Why ¬¬-propagation fails

With `s ↦ ⊤` and `c ↦ u`, `⊥ < u < ⊤` in a chain: `(s ⬝ ~~c)(1) = j(⊤) ⊓
j(¬¬u) = ⊤` but `~~(s ⬝ c)(1) = ¬¬(j(⊤) ⊓ j(u)) = ¬¬⊥ = ⊥`.

## Why (K) fails

At the point `1` the dual box is `σᵈφ(1) = ¬j(¬φ(0))`. In a chain this is
`⊤` iff `φ(0) ≠ ⊥`, and (K) holds. In `L₅` (the down-sets of the poset
`q, r < p`) take `u := ↓q`: then `¬u = ↓r` and `¬¬u = ↓q`, neither `⊤`, so
`σᵈ(~c)(1) = σᵈc(1) = ⊤` while `σᵈ⊥(1) = ¬j(⊤) = ⊥`.

This file does not `open Pattern` (notation clash with the lattice
connectives).
-/

namespace IML.DepthOne

open IML.TopFilter (j j_top j_of_ne_top j_mono j_sup_le chain_top_prime nn_of_ne_bot
  one_ne_bot one_ne_top)

/-- `⊤` is join-prime. This is what makes the point `j` join-preserving. -/
class TopJoinPrime (L : Type*) [Order.Frame L] : Prop where
  prime : ∀ u v : L, u ⊔ v = ⊤ → u = ⊤ ∨ v = ⊤

instance {L : Type*} [CompleteLinearOrder L] : TopJoinPrime L := ⟨chain_top_prime⟩

section Frame

variable {L : Type*} [Order.Frame L]

-- ─────────────────────────────────────────────────────────────
-- `j` preserves binary meets; crisp singletons
-- ─────────────────────────────────────────────────────────────

theorem j_inf (p q : L) : j (p ⊓ q) = j p ⊓ j q := by
  by_cases hp : p = ⊤ <;> by_cases hq : q = ⊤ <;> simp [j, hp, hq, inf_eq_top_iff]

theorem j_bot [Nontrivial L] : j (⊥ : L) = ⊥ := j_of_ne_top bot_ne_top

/-- The crisp singleton `{c}`. -/
def χ (c : Bool) : Bool → L := fun m => if m = c then ⊤ else ⊥

theorem j_χ [Nontrivial L] (c m : Bool) : j (χ c m : L) = χ c m := by
  unfold χ; split_ifs <;> simp [j_top, j_bot]

theorem χ_true_inf_false (c : Bool) : (χ c true : L) ⊓ χ c false = ⊥ := by
  cases c <;> simp [χ]

theorem χ_false_inf_true (c : Bool) : (χ c false : L) ⊓ χ c true = ⊥ := by
  cases c <;> simp [χ]

/-- The one-step application relation. -/
def appR (a b m : Bool) : L := if m = true ∧ a = false ∧ b = false then ⊤ else ⊥

/-- The admissible element denotations: the two crisp singletons. -/
def adm : Set (Bool → L) := {χ false, χ true}

variable [TopJoinPrime L]

-- ─────────────────────────────────────────────────────────────
-- The model
-- ─────────────────────────────────────────────────────────────

/-- Symbols `true ↦ ⊤`, `false ↦ u`. -/
noncomputable abbrev M (u : L) : GModel Bool L where
  Carrier := Bool
  appInterp := appR
  symInterp s _ := if s then ⊤ else u
  Adm := adm
  adm_cover m := ⟨χ m, by cases m <;> simp [adm], by simp [χ]⟩
  δ := j
  δ_mono _ _ h := j_mono h
  δ_sup p q := j_sup_le TopJoinPrime.prime p q
  δ_iSup f := by
    by_cases h : (⨆ X, f X) = ⊤
    · have hle : (⨆ X, f X) ≤ f ⟨χ false, by simp [adm]⟩ ⊔ f ⟨χ true, by simp [adm]⟩ := by
        apply iSup_le
        rintro ⟨X, hX⟩
        simp only [adm, Set.mem_insert_iff, Set.mem_singleton_iff] at hX
        rcases hX with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      rw [h] at hle
      rcases TopJoinPrime.prime _ _ (top_le_iff.mp hle) with h' | h'
      · exact le_iSup_of_le ⟨χ false, by simp [adm]⟩ (by rw [h', j_top]; exact le_top)
      · exact le_iSup_of_le ⟨χ true, by simp [adm]⟩ (by rw [h', j_top]; exact le_top)
    · rw [j_of_ne_top h]; exact bot_le

variable {u : L}

@[simp] theorem M_δ (p : L) : (M u).δ p = j p := rfl
@[simp] theorem M_app (a b m : Bool) : (M u).appInterp a b m = appR a b m := rfl
@[simp] theorem M_sym (s : Bool) (m : Bool) : (M u).symInterp s m = if s then ⊤ else u := rfl

/-- The symbol interpreted as `⊤`. -/
abbrev s : Pattern Bool := .symbol true
/-- The symbol interpreted as `u`. -/
abbrev c : Pattern Bool := .symbol false

theorem app_false (φ ψ : Pattern Bool) (ρ : GValuation (M u)) :
    ginterp (M u) ρ (.app φ ψ) false = ⊥ := by
  simp [ginterp_app, appR]

theorem app_true (φ ψ : Pattern Bool) (ρ : GValuation (M u)) :
    ginterp (M u) ρ (.app φ ψ) true =
      j (ginterp (M u) ρ φ false) ⊓ j (ginterp (M u) ρ ψ false) := by
  simp [ginterp_app, appR, iSup_bool_eq]

/-- Every non-hole context is `⊥` at `0` and `j(hole at 0) ⊓ k` at `1`. -/
theorem shape [Nontrivial L] (C : AppCtx Bool) (ρ : GValuation (M u)) :
    C = .hole ∨ ((∀ Y, ginterp (M u) ρ (C.fill Y) false = ⊥) ∧
      ∃ k : L, ∀ Y, ginterp (M u) ρ (C.fill Y) true = j (ginterp (M u) ρ Y false) ⊓ k) := by
  induction C with
  | hole => exact Or.inl rfl
  | left C' ψ ih =>
    right
    refine ⟨fun Y => app_false _ _ _, ?_⟩
    rcases ih with rfl | ⟨hf, -⟩
    · exact ⟨j (ginterp (M u) ρ ψ false), fun Y => by simp only [AppCtx.fill, app_true]⟩
    · exact ⟨⊥, fun Y => by rw [AppCtx.fill, app_true, hf Y, j_bot, bot_inf_eq, inf_bot_eq]⟩
  | right ψ C' ih =>
    right
    refine ⟨fun Y => app_false _ _ _, ?_⟩
    rcases ih with rfl | ⟨hf, -⟩
    · exact ⟨j (ginterp (M u) ρ ψ false), fun Y => by
        simp only [AppCtx.fill, app_true]; rw [inf_comm]⟩
    · exact ⟨⊥, fun Y => by rw [AppCtx.fill, app_true, hf Y, j_bot, inf_bot_eq, inf_bot_eq]⟩

theorem evar_eq {ρ : GValuation (M u)} (hρ : ρ.IsAdm) (n : EVarIndex) :
    ∃ c : Bool, ρ.evar n = χ c := by
  have h := hρ n
  simp only [adm, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

-- ─────────────────────────────────────────────────────────────
-- `singletonStrong` is valid
-- ─────────────────────────────────────────────────────────────

/-- **The positive SINGLETON `singletonStrong` is valid in the depth-one model.**
Together with `gsoundness` this makes every derivation of the current system
`IML.Proof` valid in `M u`. -/
theorem valid_strong [Nontrivial L] : ∀ i, GValid (M u) (singletonStrongAx Bool i) := by
  rintro ⟨⟨C₁, C₂, n, φ⟩, ψ⟩ ρ hρ m
  obtain ⟨c, hc⟩ := evar_eq hρ n
  simp only [singletonStrongAx, ginterp_impl, ginterp_conj]
  rw [himp_eq_top_iff]
  rcases shape C₁ ρ with rfl | ⟨hf₁, k₁, hk₁⟩ <;>
    rcases shape C₂ ρ with rfl | ⟨hf₂, k₂, hk₂⟩ <;> cases m
  · -- hole, hole, 0
    simp only [AppCtx.fill, ginterp_conj]
    exact le_inf (inf_le_left.trans inf_le_left) (inf_le_inf inf_le_right inf_le_right)
  · -- hole, hole, 1
    simp only [AppCtx.fill, ginterp_conj]
    exact le_inf (inf_le_left.trans inf_le_left) (inf_le_inf inf_le_right inf_le_right)
  · -- hole, non-hole, 0
    rw [hf₂, hf₂]; exact inf_le_right
  · -- hole, non-hole, 1: the premise contains `x(1) ⊓ j(x(0))`
    rw [hk₂, hk₂]
    simp only [AppCtx.fill, ginterp_conj, ginterp_evar, hc]
    refine le_trans (le_trans (inf_le_inf inf_le_left (inf_le_left.trans (j_mono inf_le_left)))
      ?_) bot_le
    rw [j_χ, χ_true_inf_false]
  · -- non-hole, hole, 0
    rw [hf₁]; exact inf_le_left.trans bot_le
  · -- non-hole, hole, 1
    rw [hk₁]
    simp only [AppCtx.fill, ginterp_conj, ginterp_evar, hc]
    refine le_trans (le_trans (inf_le_inf (inf_le_left.trans (j_mono inf_le_left)) inf_le_left)
      ?_) bot_le
    rw [j_χ, χ_false_inf_true]
  · -- non-hole, non-hole, 0
    rw [hf₂, hf₂]; exact inf_le_right
  · -- non-hole, non-hole, 1: `j` preserves `⊓`
    rw [hk₁, hk₂, hk₂]
    simp only [ginterp_conj, j_inf]
    refine le_inf (le_inf ?_ (le_inf ?_ ?_)) ?_
    · exact inf_le_left.trans (inf_le_left.trans inf_le_left)
    · exact inf_le_left.trans (inf_le_left.trans inf_le_right)
    · exact inf_le_right.trans (inf_le_left.trans inf_le_right)
    · exact inf_le_right.trans inf_le_right

/-- Every derivation of the current system from `∅` is valid in `M u`. -/
theorem sound [Nontrivial L] {φ : Pattern Bool} (h : (∅ : Set (Pattern Bool)) ⊩ᵢ φ) :
    GValid (M u) φ :=
  gsoundness h.toCore L (M u) valid_strong (fun _ hγ => absurd hγ (Set.notMem_empty _))

/-- The admissible valuation `x ↦ {0}` for every `x`, set variables `⊥`. -/
def ρ₀ (u : L) : GValuation (M u) where
  evar _ := χ false
  svar _ _ := ⊥

theorem ρ₀_adm : (ρ₀ u).IsAdm := fun _ => by simp [ρ₀, adm]

-- ─────────────────────────────────────────────────────────────
-- The dual box `σᵈφ = ~(s ⬝ ~φ)` at the point `1`
-- ─────────────────────────────────────────────────────────────

theorem allnx_eq_box (φ : Pattern Bool) : allnx true φ = (AppCtx.right s .hole).box φ := rfl

/-- `σᵈφ(1) = ¬ j(¬ φ(0))`. -/
theorem allnx_true [Nontrivial L] (φ : Pattern Bool) (ρ : GValuation (M u)) :
    ginterp (M u) ρ (allnx true φ) true = j (ginterp (M u) ρ φ false ⇨ ⊥) ⇨ ⊥ := by
  simp only [allnx, nx, Pattern.neg, ginterp_impl, ginterp_bot, app_true, ginterp_symbol,
    ↓reduceIte, j_top, top_inf_eq]

/-- The (K) instance `σᵈ(~c) ⇒ σᵈc ⇒ σᵈ⊥` has value `⊥` at `1` whenever
`¬u ≠ ⊤` and `¬¬u ≠ ⊤`. -/
theorem cm_boxK [Nontrivial L] (hu₁ : u ⇨ ⊥ ≠ ⊤) (hu₂ : (u ⇨ ⊥) ⇨ ⊥ ≠ ⊤)
    (ρ : GValuation (M u)) :
    ginterp (M u) ρ (.impl (allnx true (.neg c)) (.impl (allnx true c) (allnx true .bot)))
      true = ⊥ := by
  simp only [ginterp_impl, allnx_true, Pattern.neg, ginterp_bot, ginterp_symbol,
    Bool.false_eq_true, ↓reduceIte, bot_himp, j_top, top_himp]
  rw [j_of_ne_top hu₁, j_of_ne_top hu₂, bot_himp, top_himp, top_himp]

/-- The instance `σᵈc ⊓ σᵈ(~c) ⇒ σᵈ(c ⊓ ~c)` has value `⊥` at `1` under the same
hypotheses. -/
theorem cm_boxAnd [Nontrivial L] (hu₁ : u ⇨ ⊥ ≠ ⊤) (hu₂ : (u ⇨ ⊥) ⇨ ⊥ ≠ ⊤)
    (ρ : GValuation (M u)) :
    ginterp (M u) ρ (.impl (.conj (allnx true c) (allnx true (.neg c)))
      (allnx true (.conj c (.neg c)))) true = ⊥ := by
  simp only [ginterp_impl, ginterp_conj, allnx_true, Pattern.neg, ginterp_bot, ginterp_symbol,
    Bool.false_eq_true, ↓reduceIte]
  rw [j_of_ne_top hu₁, j_of_ne_top hu₂, inf_comm u, himp_inf_self, bot_inf_eq, bot_himp, j_top,
    top_himp, top_inf_eq, top_himp]

end Frame

-- ─────────────────────────────────────────────────────────────
-- The refutation of ¬¬-propagation (over a chain)
-- ─────────────────────────────────────────────────────────────

section Chain

variable {L : Type*} [CompleteLinearOrder L] {u : L}

/-- `s ⬝ ~~c ⇒ ~~(s ⬝ c)` has value `⊥` at the point `1`. -/
theorem cm_nnPropagation [Nontrivial L] (hu₁ : u ≠ ⊥) (hu₂ : u ≠ ⊤) (ρ : GValuation (M u)) :
    ginterp (M u) ρ (.impl (.app s (.neg (.neg c))) (.neg (.neg (.app s c)))) true = ⊥ := by
  simp only [Pattern.neg, ginterp_impl, ginterp_bot, app_true, ginterp_symbol,
    ↓reduceIte, Bool.false_eq_true, j_top, top_inf_eq]
  rw [nn_of_ne_bot hu₁, j_top, j_of_ne_top hu₂]
  simp

end Chain

/-- **¬¬-propagation `C[~~φ] ⇒ ~~C[φ]` is not derivable in the current
system** (instance `C = s ⬝ □`, `φ = c`), although it is valid in every
`HModel`: the current system is incomplete for the Heyting semantics. -/
theorem nnPropagation_not_derivable :
    IsEmpty ((∅ : Set (Pattern Bool)) ⊩ᵢ
      .impl (.app s (.neg (.neg c))) (.neg (.neg (.app s c)))) := by
  constructor; intro h
  have := sound (L := ℕ∞) (u := 1) h (ρ₀ 1) ρ₀_adm true
  rw [cm_nnPropagation one_ne_bot one_ne_top] at this
  exact bot_ne_top this

-- ─────────────────────────────────────────────────────────────
-- The frame `L₅` and the refutation of (K)
-- ─────────────────────────────────────────────────────────────

/-- The poset `q, r < p`. -/
inductive Λ | p | q | r deriving DecidableEq

instance : Preorder Λ where
  le a b := a = b ∨ b = .p
  le_refl _ := Or.inl rfl
  le_trans _ _ _ h₁ h₂ := by
    rcases h₂ with rfl | rfl
    · exact h₁
    · exact Or.inr rfl

/-- The five-element frame of down-sets of `Λ`: `⊥ < ↓q, ↓r < ↓q ⊔ ↓r < ⊤`.
Its top is join-prime (it is the only down-set containing `p`) but it is not
a chain, and `¬↓q = ↓r`. -/
abbrev L₅ := LowerSet Λ

theorem Λ.le_iff (a b : Λ) : a ≤ b ↔ (a = b ∨ b = Λ.p) := Iff.rfl

theorem L₅.eq_top_of_mem_p {u : L₅} (h : Λ.p ∈ u) : u = ⊤ := by
  apply le_antisymm le_top
  intro x _
  exact u.lower (Or.inr rfl : x ≤ Λ.p) h

instance : TopJoinPrime L₅ where
  prime u v h := by
    have hp : Λ.p ∈ u ⊔ v := by rw [h]; exact LowerSet.mem_top
    rw [LowerSet.mem_sup_iff] at hp
    exact hp.imp L₅.eq_top_of_mem_p L₅.eq_top_of_mem_p

/-- The value `↓q`. -/
abbrev uq : L₅ := LowerSet.Iic Λ.q
/-- The value `↓r`. -/
abbrev ur : L₅ := LowerSet.Iic Λ.r

theorem uq_inf_ur : uq ⊓ ur = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [SetLike.mem_coe, LowerSet.mem_inf_iff, LowerSet.mem_Iic_iff, LowerSet.mem_Iic_iff,
    Λ.le_iff, Λ.le_iff] at hx
  cases x <;> simp_all

theorem uq_ne_top : uq ≠ ⊤ := by
  intro h
  have : Λ.p ∈ uq := by rw [h]; exact LowerSet.mem_top
  rw [LowerSet.mem_Iic_iff, Λ.le_iff] at this; simp at this

theorem ur_ne_top : ur ≠ ⊤ := by
  intro h
  have : Λ.p ∈ ur := by rw [h]; exact LowerSet.mem_top
  rw [LowerSet.mem_Iic_iff, Λ.le_iff] at this; simp at this

theorem himp_bot_uq : uq ⇨ ⊥ = ur := by
  apply le_antisymm
  · intro x hx
    rw [SetLike.mem_coe] at hx ⊢
    have h1 : Λ.q ∉ (uq ⇨ ⊥ : L₅) := by
      intro hq
      have : Λ.q ∈ ((uq ⇨ ⊥) ⊓ uq : L₅) :=
        LowerSet.mem_inf_iff.mpr ⟨hq, by rw [LowerSet.mem_Iic_iff]⟩
      rw [himp_inf_self, bot_inf_eq] at this
      exact LowerSet.notMem_bot this
    have h2 : Λ.p ∉ (uq ⇨ ⊥ : L₅) := fun hp =>
      h1 ((uq ⇨ ⊥ : L₅).lower (Or.inr rfl : Λ.q ≤ Λ.p) hp)
    rw [LowerSet.mem_Iic_iff, Λ.le_iff]
    cases x with
    | p => exact absurd hx h2
    | q => exact absurd hx h1
    | r => simp
  · rw [le_himp_iff, inf_comm, uq_inf_ur]

theorem himp_bot_ur : ur ⇨ ⊥ = uq := by
  apply le_antisymm
  · intro x hx
    rw [SetLike.mem_coe] at hx ⊢
    have h1 : Λ.r ∉ (ur ⇨ ⊥ : L₅) := by
      intro hr
      have : Λ.r ∈ ((ur ⇨ ⊥) ⊓ ur : L₅) :=
        LowerSet.mem_inf_iff.mpr ⟨hr, by rw [LowerSet.mem_Iic_iff]⟩
      rw [himp_inf_self, bot_inf_eq] at this
      exact LowerSet.notMem_bot this
    have h2 : Λ.p ∉ (ur ⇨ ⊥ : L₅) := fun hp =>
      h1 ((ur ⇨ ⊥ : L₅).lower (Or.inr rfl : Λ.r ≤ Λ.p) hp)
    rw [LowerSet.mem_Iic_iff, Λ.le_iff]
    cases x with
    | p => exact absurd hx h2
    | q => simp
    | r => exact absurd hx h1
  · rw [le_himp_iff, uq_inf_ur]

theorem not_uq_ne_top : uq ⇨ ⊥ ≠ ⊤ := by rw [himp_bot_uq]; exact ur_ne_top

theorem nn_uq_ne_top : (uq ⇨ ⊥) ⇨ ⊥ ≠ ⊤ := by rw [himp_bot_uq, himp_bot_ur]; exact uq_ne_top

instance : Nontrivial L₅ := ⟨⟨⊥, ⊤, fun h => LowerSet.notMem_bot (h ▸ LowerSet.mem_top : Λ.p ∈ ⊥)⟩⟩

/-- **The modal (K) rule for the dual box `σᵈφ := ~(σ ⬝ ~φ)`,
`σᵈ(φ ⇒ ψ) ⇒ σᵈφ ⇒ σᵈψ` (the LTL rule (K◦)), is not
derivable in the current system** (instance `σ = s`, `φ = c`, `ψ = ⊥`),
although it is valid in every `HModel`. -/
theorem boxK_not_derivable :
    IsEmpty ((∅ : Set (Pattern Bool)) ⊩ᵢ
      .impl (allnx true (.neg c)) (.impl (allnx true c) (allnx true .bot))) := by
  constructor; intro h
  have := sound (L := L₅) (u := uq) h (ρ₀ uq) ρ₀_adm true
  rw [cm_boxK not_uq_ne_top nn_uq_ne_top] at this
  exact bot_ne_top this

/-- **`σᵈφ ⊓ σᵈψ ⇒ σᵈ(φ ⊓ ψ)` (Prop. 5.6(5)(←) for `◦`) is not derivable in the
current system** (instance `φ = c`, `ψ = ~c`), although it is valid in every
`HModel`. -/
theorem boxAnd_not_derivable :
    IsEmpty ((∅ : Set (Pattern Bool)) ⊩ᵢ
      .impl (.conj (allnx true c) (allnx true (.neg c))) (allnx true (.conj c (.neg c)))) := by
  constructor; intro h
  have := sound (L := L₅) (u := uq) h (ρ₀ uq) ρ₀_adm true
  rw [cm_boxAnd not_uq_ne_top nn_uq_ne_top] at this
  exact bot_ne_top this

end IML.DepthOne
