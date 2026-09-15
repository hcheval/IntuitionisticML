import IML.HeytingSoundness

/-!
# Soundness of the positive singleton variants

This file works over the `L`-valued-equality semantics of `IML.HeytingSemantics`. The
context kernel lemma `hinterp_fill` and the soundness of the primitive positive rule
`hvalid_singletonStrong` live in `IML.HeytingSoundness`; what remains here are the
variants used in the comparison of `IML/SingletonAlt/`:

* `singletonAlt`:    `C₁[x ⊓ φ] ⊓ C₂[x] ⇒ C₂[x ⊓ φ]`
* `botProp`:         `C[⊥] ⇒ ⊥`

Both are sound (`hvalid_singletonAlt`, `hvalid_botProp`), by the same witness argument as
`hvalid_singletonStrong`: for witnesses `a` (at the hole of `C₁`) and `b` (at the hole of
`C₂`), `E a x ⊓ E b x ≤ E a b` by symmetry and transitivity, and `hinterp_ext` gives
`E a b ⊓ φ a ≤ φ b`, so `b` also witnesses `C₂[x ⊓ φ]`.
-/

namespace IML

open Pattern

variable {Symbol : Type} {L : Type*} [Order.Frame L]
         {M : HModel Symbol L} {ρ : HValuation M}

/-- **`singletonAlt` is sound**: `C₁[x ⊓ φ] ⊓ C₂[x] ⇒ C₂[x ⊓ φ]` holds in every `HModel`. -/
theorem hvalid_singletonAlt {C₁ C₂ : AppCtx Symbol} {n : EVarIndex}
    {φ : Pattern Symbol} (m : M.Carrier) :
    hinterp M ρ (C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n) ⇒ C₂.fill (.evar n ⊓ φ)) m
      = ⊤ := by
  simp only [hinterp_impl, hinterp_conj]
  rw [himp_eq_top_iff, hinterp_fill, hinterp_fill, hinterp_fill]
  rw [iSup_inf_eq]; apply iSup_le; intro a
  rw [inf_iSup_eq]; apply iSup_le; intro b
  apply le_iSup_of_le b
  simp only [hinterp_conj, hinterp_evar]
  -- goal: (E a x ⊓ φ a ⊓ K₁ a m) ⊓ (E b x ⊓ K₂ b m) ≤ E b x ⊓ φ b ⊓ K₂ b m
  refine le_inf (le_inf ?_ ?_) ?_
  · exact inf_le_right.trans inf_le_left
  · refine le_trans ?_ (hinterp_ext φ ρ a b)
    refine le_trans (le_inf ?_ ?_) (inf_le_inf_right _ (M.E_trans_symm a b (ρ.evar n)))
    · exact le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
        (inf_le_right.trans inf_le_left)
    · exact inf_le_left.trans (inf_le_left.trans inf_le_right)
  · exact inf_le_right.trans inf_le_right

/-- Propagation of `⊥` through contexts is (trivially) sound. -/
theorem hvalid_botProp {C : AppCtx Symbol} (m : M.Carrier) :
    hinterp M ρ (C.fill ⊥ₘ ⇒ ⊥ₘ) m = ⊤ := by
  simp only [hinterp_impl, hinterp_bot]
  rw [himp_eq_top_iff, hinterp_fill]
  apply iSup_le; intro a; simp

end IML
