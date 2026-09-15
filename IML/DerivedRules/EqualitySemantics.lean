import IML.DerivedRules.Definedness
import IML.HeytingSemantics

/-!
# Positive equality is the Ω-set equality `E`

The Heyting semantics (`IML/HeytingSemantics.lean`) carries a primitive
`L`-valued equality `E` on the carrier. This file shows that the syntactic
positive equality `x =ⁱ y := ⌊x ⟺ y⌋ⁱ = ∀z. ⌈z ⊓ (x ⟺ y)⌉` of
`Definedness.lean` denotes exactly `E` in every model that interprets
definedness *standardly* (definedness symbol and application relation `⊤`,
so that `⟦⌈φ⌉⟧ m = ⨆ a, ⟦φ⟧ a`):

    ⟦x =ⁱ y⟧ m = E ρ(x) ρ(y).

The two inequalities are the two halves of the Ω-set axioms: `E x y ≤
(E c x ⇔ E c y)` for every `c` is symmetry-plus-transitivity, and `⨆_b E b x ⊓
(E b x ⇔ E b y) ≤ E x y` is transitivity again. So `=ⁱ` is the internal
counterpart of `E`, and soundness of the positive SINGLETON — extensionality
`E a b ⊓ φ a ≤ φ b` of every interpretation (`hinterp_ext`) — is the
semantic form of Leibniz's law `eqI_leibniz`.
-/

namespace IML

open Pattern

variable {Symbol : Type} [HasCeil Symbol] {L : Type*} [Order.Frame L]

/-- Standard interpretation of definedness: the symbol and the application
relation are `⊤`. -/
def HModel.StdCeil (M : HModel Symbol L) : Prop :=
  (∀ m, M.symInterp HasCeil.ceil m = ⊤) ∧ (∀ a b m, M.appInterp a b m = ⊤)

/-- **Positive equality of element variables denotes `E`.** -/
theorem hinterp_eqI_evar {M : HModel Symbol L} (h : M.StdCeil) (ρ : HValuation M)
    (n k : EVarIndex) (m : M.Carrier) :
    hinterp M ρ (.evar n =ⁱₘₗ .evar k) m = M.E (ρ.evar n) (ρ.evar k) := by
  simp only [Pattern.eqI, Pattern.totalI, Pattern.memML, Pattern.ceil, Pattern.iff, evarLift,
    evarLiftFrom, ge_iff_le, Nat.zero_le, ↓reduceIte, hinterp_forall, hinterp_app, hinterp_conj,
    hinterp_impl, hinterp_evar, hinterp_symbol, h.1, h.2, top_inf_eq, inf_top_eq,
    HValuation.pushEVar]
  apply le_antisymm
  · refine (iInf_le _ (ρ.evar n)).trans (iSup_le fun _ => iSup_le fun b => ?_)
    refine le_trans (le_inf inf_le_left ?_) (M.E_symm_trans b _ _)
    exact (inf_le_inf_left _ inf_le_left).trans inf_himp_le
  · refine le_iInf fun c => le_iSup_of_le c (le_iSup_of_le c ?_)
    refine le_inf ?_ (le_inf ?_ ?_)
    · rw [M.E_refl]; exact le_top
    · rw [le_himp_iff, inf_comm]; exact M.E_trans c _ _
    · rw [le_himp_iff, inf_comm]; exact M.E_trans_symm c _ _

end IML
