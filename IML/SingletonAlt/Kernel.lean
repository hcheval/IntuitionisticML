import IML.HeytingSoundness

/-!
# The context kernel lemma, and soundness of the positive singleton axioms

For every application context `C` there is a kernel `K_C : Carrier → Carrier → L` with

    hinterp M ρ (C.fill X) m = ⨆ a, hinterp M ρ X a ⊓ K_C a m.

This strengthens `fill_le_iSup` from `HeytingSoundness.lean` (which only records the
inequality `≤ ⨆ a, hinterp X a`) to an equality, and makes the soundness of the
positive singleton variants a one-line lattice computation.

The two positive variants considered:

* `singletonAlt`:    `C₁[x ⊓ φ] ⊓ C₂[x] ⇒ C₂[x ⊓ φ]`
* `singletonStrong`: `C₁[x ⊓ φ] ⊓ C₂[x ⊓ ψ] ⇒ C₂[x ⊓ (φ ⊓ ψ)]`

Both are sound (`hvalid_singletonAlt`, `hvalid_singletonStrong`).

## Porting note (L-valued equality)

`K_hole a m` is deliberately its own definition. Under the generalized semantics in which
`hinterp (.evar i) m = E m (ρ.evar i)` for an `L`-valued equality `E`, one sets
`K_hole a m := E a m`; `hinterp_fill` goes through unchanged (its proof never unfolds
`K_hole`). The collapse lemmas `iSup_evar_inf` / `iSup_evar_conj_inf` become inequalities
`≤` rather than equalities, and the soundness argument for `singletonAlt` becomes: for fixed
witnesses `a` (from `C₁[x ⊓ φ]`) and `b` (from `C₂[x]`), `E a e ⊓ E b e ≤ E a b` by
symmetry and transitivity, and extensionality of the interpretation (`hinterp_ext`) gives
`E a b ⊓ φ a ≤ φ b`, so the witness `b` also witnesses `C₂[x ⊓ φ]`.
-/

namespace IML

open Pattern

variable {Symbol : Type} {L : Type*} [Order.Frame L]
         {M : HModel Symbol L} {ρ : HValuation M}

/-- The kernel of the empty context: crisp equality on the carrier. -/
def K_hole (M : HModel Symbol L) (a m : M.Carrier) : L :=
  @ite L (a = m) (M.decEq a m) ⊤ ⊥

/-- The kernel of an application context: `K_C a m` measures "`a` at the hole of `C`
yields `m`". -/
def AppCtx.kernel (M : HModel Symbol L) (ρ : HValuation M) :
    AppCtx Symbol → M.Carrier → M.Carrier → L
  | .hole => fun a m => K_hole M a m
  | .left C ψ => fun a m =>
      ⨆ b, ⨆ c, AppCtx.kernel M ρ C a b ⊓ hinterp M ρ ψ c ⊓ M.appInterp b c m
  | .right ψ C => fun a m =>
      ⨆ b, ⨆ c, hinterp M ρ ψ b ⊓ AppCtx.kernel M ρ C a c ⊓ M.appInterp b c m

theorem iSup_inf_K_hole (X : M.Carrier → L) (m : M.Carrier) :
    ⨆ a, X a ⊓ K_hole M a m = X m := by
  apply le_antisymm
  · apply iSup_le; intro a
    unfold K_hole; split
    · rename_i h; subst h; exact inf_le_left
    · simp
  · apply le_iSup_of_le m
    unfold K_hole; simp

/-- **The context kernel lemma.** -/
theorem hinterp_fill (C : AppCtx Symbol) (X : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (C.fill X) m = ⨆ a, hinterp M ρ X a ⊓ C.kernel M ρ a m := by
  induction C generalizing m with
  | hole => simp only [AppCtx.fill, AppCtx.kernel]; rw [iSup_inf_K_hole]
  | left C ψ ih =>
    simp only [AppCtx.fill, AppCtx.kernel, hinterp_app]
    apply le_antisymm
    · apply iSup_le; intro b; apply iSup_le; intro c
      rw [ih b, iSup_inf_eq, iSup_inf_eq]
      apply iSup_le; intro a
      apply le_iSup_of_le a
      rw [inf_iSup_eq]; apply le_iSup_of_le b
      rw [inf_iSup_eq]; apply le_iSup_of_le c
      exact le_of_eq (by simp only [inf_assoc])
    · apply iSup_le; intro a
      rw [inf_iSup_eq]; apply iSup_le; intro b
      rw [inf_iSup_eq]; apply iSup_le; intro c
      apply le_iSup_of_le b; apply le_iSup_of_le c
      rw [ih b, iSup_inf_eq, iSup_inf_eq]
      apply le_iSup_of_le a
      exact le_of_eq (by simp only [inf_assoc])
  | right ψ C ih =>
    simp only [AppCtx.fill, AppCtx.kernel, hinterp_app]
    apply le_antisymm
    · apply iSup_le; intro b; apply iSup_le; intro c
      rw [ih c, inf_iSup_eq, iSup_inf_eq]
      apply iSup_le; intro a
      apply le_iSup_of_le a
      rw [inf_iSup_eq]; apply le_iSup_of_le b
      rw [inf_iSup_eq]; apply le_iSup_of_le c
      exact le_of_eq (by simp only [inf_assoc, inf_left_comm (hinterp M ρ ψ b)])
    · apply iSup_le; intro a
      rw [inf_iSup_eq]; apply iSup_le; intro b
      rw [inf_iSup_eq]; apply iSup_le; intro c
      apply le_iSup_of_le b; apply le_iSup_of_le c
      rw [ih c, inf_iSup_eq, iSup_inf_eq]
      apply le_iSup_of_le a
      exact le_of_eq (by simp only [inf_assoc, inf_left_comm (hinterp M ρ ψ b)])

/-- The old bound `fill_le_iSup` is a corollary of the kernel lemma. -/
theorem fill_le_iSup' (C : AppCtx Symbol) (X : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (C.fill X) m ≤ ⨆ a, hinterp M ρ X a := by
  rw [hinterp_fill]; exact iSup_mono fun a => inf_le_left

-- ─────────────────────────────────────────────────────────────
-- Crispness of element variables collapses the supremum
-- ─────────────────────────────────────────────────────────────

theorem iSup_evar_inf {n : EVarIndex} (K : M.Carrier → L) :
    ⨆ a, hinterp M ρ (.evar n) a ⊓ K a = K (ρ.evar n) := by
  apply le_antisymm
  · apply iSup_le; intro a
    simp only [hinterp_evar]; split
    · rename_i h; subst h; exact inf_le_right
    · simp
  · apply le_iSup_of_le (ρ.evar n); simp

theorem iSup_evar_conj_inf {n : EVarIndex} (φ : Pattern Symbol) (K : M.Carrier → L) :
    ⨆ a, hinterp M ρ (.evar n ⊓ φ) a ⊓ K a = hinterp M ρ φ (ρ.evar n) ⊓ K (ρ.evar n) := by
  apply le_antisymm
  · apply iSup_le; intro a
    simp only [hinterp_conj, hinterp_evar]; split
    · rename_i h; subst h; simp
    · simp
  · apply le_iSup_of_le (ρ.evar n); simp

-- ─────────────────────────────────────────────────────────────
-- Soundness of the positive singleton axioms
-- ─────────────────────────────────────────────────────────────

/-- **`singletonAlt` is sound**: `C₁[x ⊓ φ] ⊓ C₂[x] ⇒ C₂[x ⊓ φ]` holds in every `HModel`. -/
theorem hvalid_singletonAlt {C₁ C₂ : AppCtx Symbol} {n : EVarIndex}
    {φ : Pattern Symbol} (m : M.Carrier) :
    hinterp M ρ (C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n) ⇒ C₂.fill (.evar n ⊓ φ)) m
      = ⊤ := by
  simp only [hinterp_impl, hinterp_conj]
  rw [himp_eq_top_iff, hinterp_fill, hinterp_fill, hinterp_fill,
      iSup_evar_conj_inf, iSup_evar_conj_inf, iSup_evar_inf]
  exact inf_le_inf_right _ inf_le_left

/-- **`singletonStrong` is sound**: `C₁[x ⊓ φ] ⊓ C₂[x ⊓ ψ] ⇒ C₂[x ⊓ (φ ⊓ ψ)]` holds in every
`HModel`. -/
theorem hvalid_singletonStrong {C₁ C₂ : AppCtx Symbol} {n : EVarIndex}
    {φ ψ : Pattern Symbol} (m : M.Carrier) :
    hinterp M ρ (C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n ⊓ ψ) ⇒
      C₂.fill (.evar n ⊓ (φ ⊓ ψ))) m = ⊤ := by
  simp only [hinterp_impl, hinterp_conj]
  rw [himp_eq_top_iff, hinterp_fill, hinterp_fill, hinterp_fill,
      iSup_evar_conj_inf, iSup_evar_conj_inf, iSup_evar_conj_inf, hinterp_conj]
  exact le_inf (le_inf (le_trans inf_le_left inf_le_left)
    (le_trans inf_le_right inf_le_left)) (le_trans inf_le_right inf_le_right)

/-- Propagation of `⊥` through contexts is (trivially) sound. -/
theorem hvalid_botProp {C : AppCtx Symbol} (m : M.Carrier) :
    hinterp M ρ (C.fill ⊥ₘ ⇒ ⊥ₘ) m = ⊤ := by
  simp only [hinterp_impl, hinterp_bot]
  rw [himp_eq_top_iff, hinterp_fill]
  apply iSup_le; intro a; simp

end IML
