import IML.HeytingSoundness
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Excluded middle for element variables is not derivable

With `L`-valued equality, an element variable need not be crisp, and
`x ⊔ ~x` is no longer valid in every model. This file gives a concrete
countermodel and concludes, by `soundness`, that `x ⊔ ~x` is not derivable
in iML from no hypotheses.

## The model

For any frame `L` and any `u : L`, `twoPointModel L u` has carrier `Bool`,
equality `E a b = if a = b then ⊤ else u`, and every symbol and application
interpreted as `⊥`. Under `ρ(x) := true`, at the point `false`,

    ⟦x ⊔ ~x⟧(false) = u ⊔ (u ⇨ ⊥)

so the model refutes `x ⊔ ~x` as soon as `u ⊔ (u ⇨ ⊥) ≠ ⊤`
(`twoPointModel_not_valid`).

## The witness

`L := Opens (WithUpperSet (Fin 2))`, the three upper sets `∅ ⊂ {1} ⊂ {0,1}`
of the two-point Kripke frame `0 ≤ 1`, and `u := {1}`. Then `u ⇨ ⊥` is the
largest open disjoint from `{1}`, which is `∅` since every nonempty upper
set contains `1`, so `u ⊔ (u ⇨ ⊥) = {1} ≠ ⊤` (`U₁_sup_himp_ne_top`).

In crisp models (`IML.CrispModels`) the same pattern is valid, so this
separation depends on the `L`-valued equality.
-/

namespace IML.Examples.ExcludedMiddle

open TopologicalSpace Topology

-- ─────────────────────────────────────────────────────────────
-- The generic two-point model
-- ─────────────────────────────────────────────────────────────

/-- Two elements whose equality has truth value `u`. -/
def twoPointModel (Symbol : Type) (L : Type*) [Order.Frame L] (u : L) :
    HModel Symbol L where
  Carrier := Bool
  E a b := if a = b then ⊤ else u
  E_refl _ := if_pos rfl
  E_symm a b := by
    by_cases h : a = b
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  E_trans a b c := by
    split_ifs <;> simp_all
  appInterp _ _ _ := ⊥
  symInterp _ _ := ⊥
  symInterp_ext _ _ _ := inf_le_right
  appInterp_ext₁ _ _ _ _ := inf_le_right
  appInterp_ext₂ _ _ _ _ := inf_le_right
  appInterp_ext₃ _ _ _ _ := inf_le_right

/-- The valuation sending every element variable to `true` and every set
variable to `⊥`. -/
def trueValuation (Symbol : Type) (L : Type*) [Order.Frame L] (u : L) :
    HValuation (twoPointModel Symbol L u) where
  evar _ := true
  svar _ _ := ⊥
  svar_ext _ _ _ := inf_le_right

theorem twoPointModel_hinterp_evar_false (Symbol : Type) (L : Type*) [Order.Frame L]
    (u : L) :
    hinterp (twoPointModel Symbol L u) (trueValuation Symbol L u) (.evar 0) false = u := by
  change (if false = true then (⊤ : L) else u) = u
  exact if_neg Bool.false_ne_true

theorem twoPointModel_hinterp_em (Symbol : Type) (L : Type*) [Order.Frame L] (u : L) :
    hinterp (twoPointModel Symbol L u) (trueValuation Symbol L u)
      (Pattern.disj (Pattern.evar 0) (Pattern.neg (Pattern.evar 0))) false = u ⊔ (u ⇨ ⊥) := by
  rw [hinterp_disj, Pattern.neg, hinterp_impl, hinterp_bot,
    twoPointModel_hinterp_evar_false]

theorem twoPointModel_not_valid (Symbol : Type) (L : Type*) [Order.Frame L] (u : L)
    (hu : u ⊔ (u ⇨ ⊥) ≠ ⊤) :
    ¬ HValid (twoPointModel Symbol L u)
      (Pattern.disj (Pattern.evar 0) (Pattern.neg (Pattern.evar 0))) := by
  intro h
  exact hu ((twoPointModel_hinterp_em Symbol L u).symm.trans (h _ false))

-- ─────────────────────────────────────────────────────────────
-- The witness: the open `{1}` of the two-point Kripke frame `0 ≤ 1`
-- ─────────────────────────────────────────────────────────────

/-- The open (= upper) set `{1}` of the two-point frame `0 ≤ 1`. -/
def U₁ : Opens (WithUpperSet (Fin 2)) :=
  ⟨Set.Ici (WithUpperSet.toUpperSet 1),
    (Topology.IsUpperSet.isOpen_iff_isUpperSet).mpr (isUpperSet_Ici _)⟩

theorem zero_notMem_U₁ : WithUpperSet.toUpperSet (0 : Fin 2) ∉ U₁ := by
  intro h
  have h' : (1 : Fin 2) ≤ 0 := WithUpperSet.toUpperSet_le_iff.mp (Set.mem_Ici.mp h)
  exact absurd h' (by decide)

theorem one_mem_U₁ : WithUpperSet.toUpperSet (1 : Fin 2) ∈ U₁ :=
  Set.mem_Ici.mpr le_rfl

theorem U₁_sup_himp_ne_top : U₁ ⊔ (U₁ ⇨ ⊥) ≠ ⊤ := by
  intro h
  have h0 : WithUpperSet.toUpperSet (0 : Fin 2) ∈ U₁ ⊔ (U₁ ⇨ ⊥) := by
    rw [h]; exact trivial
  rcases Opens.mem_sup.mp h0 with h0 | h0
  · exact zero_notMem_U₁ h0
  · -- `U₁ ⇨ ⊥` is open, hence an upper set, so it contains `1` as well as `0`;
    -- but `(U₁ ⇨ ⊥) ⊓ U₁ ≤ ⊥`.
    have hup : IsUpperSet
        ((U₁ ⇨ ⊥ : Opens (WithUpperSet (Fin 2))) : Set (WithUpperSet (Fin 2))) := by
      have hopen := (U₁ ⇨ ⊥ : Opens (WithUpperSet (Fin 2))).2
      rw [Topology.IsUpperSet.isOpen_iff_isUpperSet] at hopen
      exact hopen
    have h01 : (0 : Fin 2) ≤ 1 := by decide
    have h1 : WithUpperSet.toUpperSet (1 : Fin 2) ∈ (U₁ ⇨ ⊥ : Opens (WithUpperSet (Fin 2))) :=
      hup (WithUpperSet.toUpperSet_le_iff.mpr h01) h0
    have hmem : WithUpperSet.toUpperSet (1 : Fin 2) ∈
        ((U₁ ⇨ ⊥) ⊓ U₁ : Opens (WithUpperSet (Fin 2))) :=
      ⟨h1, one_mem_U₁⟩
    have hbot := (himp_inf_le : (U₁ ⇨ ⊥) ⊓ U₁ ≤ ⊥) hmem
    exact hbot

-- ─────────────────────────────────────────────────────────────
-- The headline theorem
-- ─────────────────────────────────────────────────────────────

/-- The concrete countermodel. -/
def counterModel (Symbol : Type) : HModel Symbol (Opens (WithUpperSet (Fin 2))) :=
  twoPointModel Symbol _ U₁

theorem counterModel_not_valid (Symbol : Type) :
    ¬ HValid (counterModel Symbol)
      (Pattern.disj (Pattern.evar 0) (Pattern.neg (Pattern.evar 0))) :=
  twoPointModel_not_valid Symbol _ U₁ U₁_sup_himp_ne_top

open Pattern in
/-- Excluded middle for an element variable, `x ⊔ ~x`, is not derivable in
iML from no hypotheses. -/
theorem excludedMiddle_not_derivable (Symbol : Type) :
    ¬ Nonempty ((∅ : Set (Pattern Symbol)) ⊩ᵢ (Pattern.evar 0 ⊔ ~(Pattern.evar 0))) := by
  rintro ⟨h⟩
  exact counterModel_not_valid Symbol
    (soundness h _ (counterModel Symbol) (fun _ hγ => hγ.elim))

#print axioms excludedMiddle_not_derivable

end IML.Examples.ExcludedMiddle
