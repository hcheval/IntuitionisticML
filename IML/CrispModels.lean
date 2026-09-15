import IML.HeytingSemantics

/-!
# Crisp models

The special case of `HModel` in which equality on the carrier is ordinary
(decidable) equality:

    E a b = if a = b then ⊤ else ⊥

Every predicate is extensional for this `E` (`crisp_ext`), so a crisp model
is determined by the carrier and the symbol/application interpretations
alone — the shape `HModel` had before equality was made `L`-valued. In a
crisp model element variables are crisp: `⟦x⟧(m)` is `⊤` or `⊥`
(`crispModel_evar_crisp`), which is why `x ⊔ ~x` is valid in every crisp
model; see `IML.Examples.ExcludedMiddle` for a non-crisp model where it fails.
-/

namespace IML

variable {L : Type*} [Order.Frame L]

/-- Ordinary equality as an `L`-valued equality. -/
def crispE (Carrier : Type) [DecidableEq Carrier] : Carrier → Carrier → L :=
  fun a b => if a = b then ⊤ else ⊥

/-- Every predicate is extensional for crisp equality. -/
theorem crisp_ext {Carrier : Type} [DecidableEq Carrier] (f : Carrier → L) :
    Extensional (crispE Carrier) f := by
  intro a b
  unfold crispE
  split
  · rename_i h; subst h; exact inf_le_right
  · simp

/-- The crisp model on a carrier with decidable equality. -/
def crispModel (Symbol : Type) (L : Type*) [Order.Frame L]
    (Carrier : Type) [DecidableEq Carrier]
    (appI : Carrier → Carrier → Carrier → L)
    (symI : Symbol → Carrier → L) :
    HModel Symbol L where
  Carrier := Carrier
  E := crispE Carrier
  E_refl _ := if_pos rfl
  E_symm a b := by
    unfold crispE
    by_cases h : a = b
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  E_trans a b c := by
    unfold crispE
    split_ifs <;> simp_all
  appInterp := appI
  symInterp := symI
  symInterp_ext _ := crisp_ext _
  appInterp_ext₁ _ _ := crisp_ext _
  appInterp_ext₂ _ _ := crisp_ext _
  appInterp_ext₃ _ _ := crisp_ext _

section Recovery

variable {Symbol : Type} {Carrier : Type} [DecidableEq Carrier]
  {appI : Carrier → Carrier → Carrier → L} {symI : Symbol → Carrier → L}

/-- In a crisp model, element variables are interpreted as before the
generalization: `⊤` at their value and `⊥` elsewhere. -/
theorem crispModel_hinterp_evar
    (ρ : HValuation (crispModel Symbol L Carrier appI symI)) (i : EVarIndex) (m : Carrier) :
    hinterp (crispModel Symbol L Carrier appI symI) ρ (.evar i) m =
      if m = ρ.evar i then ⊤ else ⊥ := rfl

/-- In a crisp model, the truth value of an element variable is `⊤` or `⊥`. -/
theorem crispModel_evar_crisp
    (ρ : HValuation (crispModel Symbol L Carrier appI symI)) (i : EVarIndex) (m : Carrier) :
    hinterp (crispModel Symbol L Carrier appI symI) ρ (.evar i) m = ⊤ ∨
    hinterp (crispModel Symbol L Carrier appI symI) ρ (.evar i) m = ⊥ := by
  rw [crispModel_hinterp_evar]
  split_ifs <;> simp

/-- Excluded middle for element variables holds in every crisp model. -/
theorem crispModel_evar_excludedMiddle
    (ρ : HValuation (crispModel Symbol L Carrier appI symI)) (i : EVarIndex) (m : Carrier) :
    hinterp (crispModel Symbol L Carrier appI symI) ρ
      (Pattern.disj (.evar i) (Pattern.neg (.evar i))) m = ⊤ := by
  rw [hinterp_disj, Pattern.neg, hinterp_impl, hinterp_bot, crispModel_hinterp_evar]
  split_ifs <;> simp

end Recovery

end IML
