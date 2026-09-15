import IML.SingletonAlt.GModel
import IML.DerivedRules.TopFilterModel

/-!
# The depth-one model: ¬¬-propagation is underivable in the current system

`TopFilterModel.lean` refutes the ¬¬-propagation `C[~~φ] ⇒ ~~C[φ]` for the
*published* system, but its model refutes the positive SINGLETON
`singletonStrong` too (`TopFilter.cm_singletonStrong`), so it says nothing
about the current system `IML.Proof`. This file gives a generalized model
(`GModel`, see `IML/SingletonAlt/GModel.lean`) that validates
**every rule of the current system, `singletonStrong` included**
(`valid_strong`), and still refutes ¬¬-propagation. Hence the current system
is incomplete for its Heyting semantics as well (`nnPropagation_not_derivable`).

## The model

Values in a complete chain `L` with a middle element `u`; carrier `Bool`;
crisp admissible element denotations `χ 0 = {0}`, `χ 1 = {1}`; the twist
`δ := j` of the top-filter model (`j p = ⊤` iff `p = ⊤`, else `⊥`); and the
one-step application relation

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
this model, which is why it settles nothing about §3.2 of the thesis.)

## Why ¬¬-propagation fails

With `s ↦ ⊤` and `c ↦ u`: `(s ⬝ ~~c)(1) = j(⊤) ⊓ j(¬¬u) = ⊤` but
`~~(s ⬝ c)(1) = ¬¬(j(⊤) ⊓ j(u)) = ¬¬⊥ = ⊥`.

This file does not `open Pattern` (notation clash with the lattice
connectives).
-/

namespace IML.DepthOne

open IML.TopFilter (j j_top j_of_ne_top j_mono j_sup_le chain_top_prime nn_of_ne_bot
  one_ne_bot one_ne_top)

variable {L : Type*} [CompleteLinearOrder L]

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
  δ_sup p q := j_sup_le chain_top_prime p q
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
      rcases chain_top_prime _ _ (top_le_iff.mp hle) with h' | h'
      · exact le_iSup_of_le ⟨χ false, by simp [adm]⟩ (by rw [h', j_top]; exact le_top)
      · exact le_iSup_of_le ⟨χ true, by simp [adm]⟩ (by rw [h', j_top]; exact le_top)
    · rw [j_of_ne_top h]; exact bot_le

variable {u : L}

@[simp] theorem M_δ (p : L) : (M u).δ p = j p := rfl
@[simp] theorem M_app (a b m : Bool) : (M u).appInterp a b m = appR a b m := rfl
@[simp] theorem M_sym (s : Bool) (m : Bool) : (M u).symInterp s m = if s then ⊤ else u := rfl

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

/-- **The positive SINGLETON `singletonStrong` is valid in the depth-one model.** -/
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

-- ─────────────────────────────────────────────────────────────
-- The refutation
-- ─────────────────────────────────────────────────────────────

/-- The symbol interpreted as `⊤`. -/
abbrev s : Pattern Bool := .symbol true
/-- The symbol interpreted as `u`. -/
abbrev c : Pattern Bool := .symbol false

/-- `s ⬝ ~~c ⇒ ~~(s ⬝ c)` has value `⊥` at the point `1`. -/
theorem cm_nnPropagation [Nontrivial L] (hu₁ : u ≠ ⊥) (hu₂ : u ≠ ⊤) (ρ : GValuation (M u)) :
    ginterp (M u) ρ (.impl (.app s (.neg (.neg c))) (.neg (.neg (.app s c)))) true = ⊥ := by
  simp only [Pattern.neg, ginterp_impl, ginterp_bot, app_true, ginterp_symbol,
    ↓reduceIte, Bool.false_eq_true, j_top, top_inf_eq]
  rw [nn_of_ne_bot hu₁, j_top, j_of_ne_top hu₂]
  simp

/-- The admissible valuation `x ↦ {0}` for every `x`, set variables `⊥`. -/
def ρ₀ (u : L) : GValuation (M u) where
  evar _ := χ false
  svar _ _ := ⊥

theorem ρ₀_adm : (ρ₀ u).IsAdm := fun _ => by simp [ρ₀, adm]

/-- **¬¬-propagation `C[~~φ] ⇒ ~~C[φ]` is not derivable in the current
system** (instance `C = s ⬝ □`, `φ = c`), although it is valid in every
`HModel`: the current system is incomplete for the Heyting semantics. -/
theorem nnPropagation_not_derivable :
    IsEmpty ((∅ : Set (Pattern Bool)) ⊩ᵢ
      .impl (.app s (.neg (.neg c))) (.neg (.neg (.app s c)))) := by
  constructor; intro h
  have := gsoundness h.toCore ℕ∞ (M 1) valid_strong
    (fun _ hγ => absurd hγ (Set.notMem_empty _)) (ρ₀ 1) ρ₀_adm true
  rw [cm_nnPropagation one_ne_bot one_ne_top] at this
  exact bot_ne_top this

end IML.DepthOne
