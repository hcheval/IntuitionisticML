import IML.HeytingSoundness

/-!
# Fixed-point soundness via lfp/gfp

Under positivity, the map `S ↦ ⟦φ⟧(ρ[X := S])` is monotone on extensional
predicates. To use Mathlib's `OrderHom.lfp`/`OrderHom.gfp` on the complete
lattice `Carrier → L` without building a lattice structure on the subtype of
extensional predicates, we precompose with the extensional hull
`HModel.hull` (the least extensional predicate above a given one):

    fixpointFun S := ⟦φ⟧(ρ[X := hull S])

Its least fixed point is extensional (it is an interpretation) and coincides
with `hinterp (μ φ)`, the infimum of the extensional prefixpoints; dually for
`ν`. The fixpoint rules then follow from `OrderHom.map_lfp`/`OrderHom.map_gfp`
(Knaster-Tarski).

- **preFixpoint**: immediate from `map_lfp` (the fixed point equation)
- **postFixpoint**: immediate from `map_gfp`
- **knasterTarski**: `OrderHom.lfp_le` (needs positivity for the bridge)
- **park**: `OrderHom.le_gfp` (needs positivity for the bridge)
-/

namespace IML

open Pattern

variable {Symbol : Type} {L : Type*} [Order.Frame L]
         {M : HModel Symbol L} {ρ : HValuation M}

private theorem himp_eq_top_iff {a b : L} :
    (a ⇨ b) = ⊤ ↔ a ≤ b := by
  rw [eq_top_iff, le_himp_iff]
  exact ⟨fun h => by rw [top_inf_eq] at h; exact h,
         fun h => by rw [top_inf_eq]; exact h⟩

-- ─────────────────────────────────────────────────────────────
-- The monotone functional
-- ─────────────────────────────────────────────────────────────

section MonotoneFunctional

variable (M : HModel Symbol L) (ρ : HValuation M) (φ : Pattern Symbol)

noncomputable def fixpointFun (hpos : SVarPositive φ 0) :
    (M.Carrier → L) →o (M.Carrier → L) where
  toFun S := fun m => hinterp M (ρ.pushSVar (M.hull S) (M.hull_ext S)) φ m
  monotone' S₁ S₂ hle m :=
    hinterp_mono_pos hpos (ρ.pushSVar (M.hull S₁) (M.hull_ext S₁))
      (ρ.pushSVar (M.hull S₂) (M.hull_ext S₂)) rfl
      (fun i hi => by cases i with | zero => exact absurd rfl hi | succ => rfl)
      (fun n => M.hull_mono hle n) m

end MonotoneFunctional

-- ─────────────────────────────────────────────────────────────
-- Bridge: hinterp of μ/ν equals Mathlib's lfp/gfp
-- ─────────────────────────────────────────────────────────────

theorem fixpointFun_apply_of_ext {φ : Pattern Symbol} (hpos : SVarPositive φ 0)
    {S : M.Carrier → L} (hS : M.Ext S) (m : M.Carrier) :
    fixpointFun M ρ φ hpos S m = hinterp M (ρ.pushSVar S hS) φ m := by
  change hinterp M (ρ.pushSVar (M.hull S) (M.hull_ext S)) φ m = _
  rw [HValuation.pushSVar_congr ρ (M.hull_eq_of_ext hS) (M.hull_ext S) hS]

theorem lfp_ext {φ : Pattern Symbol} (hpos : SVarPositive φ 0) :
    M.Ext (fixpointFun M ρ φ hpos).lfp := by
  rw [← (fixpointFun M ρ φ hpos).map_lfp]
  exact hinterp_ext φ _

theorem gfp_ext {φ : Pattern Symbol} (hpos : SVarPositive φ 0) :
    M.Ext (fixpointFun M ρ φ hpos).gfp := by
  rw [← (fixpointFun M ρ φ hpos).map_gfp]
  exact hinterp_ext φ _

theorem hinterp_mu_eq_lfp {φ : Pattern Symbol} (hpos : SVarPositive φ 0)
    (m : M.Carrier) :
    hinterp M ρ (μ φ) m = (fixpointFun M ρ φ hpos).lfp m := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨(fixpointFun M ρ φ hpos).lfp, lfp_ext hpos, fun n => ?_, rfl⟩
    rw [← fixpointFun_apply_of_ext hpos (lfp_ext hpos) n]
    exact le_of_eq (congr_fun (fixpointFun M ρ φ hpos).map_lfp n)
  · apply le_sInf; rintro x ⟨S, hS, hpre, rfl⟩
    refine OrderHom.lfp_le (f := fixpointFun M ρ φ hpos) (fun n => ?_) m
    rw [fixpointFun_apply_of_ext hpos hS n]
    exact hpre n

theorem hinterp_nu_eq_gfp {φ : Pattern Symbol} (hpos : SVarPositive φ 0)
    (m : M.Carrier) :
    hinterp M ρ (ν φ) m = (fixpointFun M ρ φ hpos).gfp m := by
  apply le_antisymm
  · apply sSup_le; rintro x ⟨S, hS, hpost, rfl⟩
    refine OrderHom.le_gfp (f := fixpointFun M ρ φ hpos) (fun n => ?_) m
    rw [fixpointFun_apply_of_ext hpos hS n]
    exact hpost n
  · apply le_sSup
    refine ⟨(fixpointFun M ρ φ hpos).gfp, gfp_ext hpos, fun n => ?_, rfl⟩
    rw [← fixpointFun_apply_of_ext hpos (gfp_ext hpos) n]
    exact le_of_eq (congr_fun (fixpointFun M ρ φ hpos).map_gfp n).symm

-- ─────────────────────────────────────────────────────────────
-- Fixed point equations via Mathlib's Knaster-Tarski
-- ─────────────────────────────────────────────────────────────

theorem hinterp_mu_fixpoint {φ : Pattern Symbol} (hpos : SVarPositive φ 0)
    (m : M.Carrier) :
    hinterp M (ρ.pushSVar (fun n => hinterp M ρ (μ φ) n) (hinterp_ext _ ρ)) φ m =
    hinterp M ρ (μ φ) m := by
  have hfun : (fun n => hinterp M ρ (μ φ) n) = (fixpointFun M ρ φ hpos).lfp :=
    funext (hinterp_mu_eq_lfp hpos)
  rw [HValuation.pushSVar_congr ρ hfun (hinterp_ext _ ρ) (lfp_ext hpos),
    ← fixpointFun_apply_of_ext hpos (lfp_ext hpos) m, hinterp_mu_eq_lfp hpos m]
  exact congr_fun (fixpointFun M ρ φ hpos).map_lfp m

theorem hinterp_nu_fixpoint {φ : Pattern Symbol} (hpos : SVarPositive φ 0)
    (m : M.Carrier) :
    hinterp M (ρ.pushSVar (fun n => hinterp M ρ (ν φ) n) (hinterp_ext _ ρ)) φ m =
    hinterp M ρ (ν φ) m := by
  have hfun : (fun n => hinterp M ρ (ν φ) n) = (fixpointFun M ρ φ hpos).gfp :=
    funext (hinterp_nu_eq_gfp hpos)
  rw [HValuation.pushSVar_congr ρ hfun (hinterp_ext _ ρ) (gfp_ext hpos),
    ← fixpointFun_apply_of_ext hpos (gfp_ext hpos) m, hinterp_nu_eq_gfp hpos m]
  exact congr_fun (fixpointFun M ρ φ hpos).map_gfp m

-- ─────────────────────────────────────────────────────────────
-- Fixpoint soundness rules
-- ─────────────────────────────────────────────────────────────

theorem hvalid_preFixpoint_lfp {φ : Pattern Symbol}
    (hpos : SVarPositive φ 0) (m : M.Carrier) :
    hinterp M ρ (svarSubst 0 (μ φ) φ ⇒ μ φ) m = ⊤ := by
  simp only [hinterp_impl]; rw [himp_eq_top_iff, hinterp_svarSubst]
  exact le_of_eq (hinterp_mu_fixpoint hpos m)

theorem hvalid_knasterTarski_lfp {φ ψ : Pattern Symbol}
    (h : ∀ m, hinterp M ρ (svarSubst 0 ψ φ ⇒ ψ) m = ⊤)
    (m : M.Carrier) :
    hinterp M ρ (μ φ ⇒ ψ) m = ⊤ := by
  simp only [hinterp]; rw [himp_eq_top_iff]
  have hpre : ∀ n, hinterp M (ρ.pushSVar (fun n => hinterp M ρ ψ n) (hinterp_ext ψ ρ)) φ n ≤
      hinterp M ρ ψ n := fun n => by
    have := h n; simp only [hinterp] at this
    exact himp_eq_top_iff.mp (by rw [hinterp_svarSubst] at this; exact this)
  apply sInf_le
  exact ⟨fun n => hinterp M ρ ψ n, hinterp_ext ψ ρ, hpre, rfl⟩

theorem hvalid_postFixpoint_lfp {φ : Pattern Symbol}
    (hpos : SVarPositive φ 0) (m : M.Carrier) :
    hinterp M ρ (ν φ ⇒ svarSubst 0 (ν φ) φ) m = ⊤ := by
  simp only [hinterp_impl]; rw [himp_eq_top_iff, hinterp_svarSubst]
  exact le_of_eq (hinterp_nu_fixpoint hpos m).symm

theorem hvalid_park_lfp {φ ψ : Pattern Symbol}
    (h : ∀ m, hinterp M ρ (ψ ⇒ svarSubst 0 ψ φ) m = ⊤)
    (m : M.Carrier) :
    hinterp M ρ (ψ ⇒ ν φ) m = ⊤ := by
  simp only [hinterp]; rw [himp_eq_top_iff]
  have hpost : ∀ n, hinterp M ρ ψ n ≤
      hinterp M (ρ.pushSVar (fun n => hinterp M ρ ψ n) (hinterp_ext ψ ρ)) φ n := fun n => by
    have := h n; simp only [hinterp] at this
    exact himp_eq_top_iff.mp (by rw [hinterp_svarSubst] at this; exact this)
  apply le_sSup
  exact ⟨fun n => hinterp M ρ ψ n, hinterp_ext ψ ρ, hpost, rfl⟩

-- ─────────────────────────────────────────────────────────────
-- Full soundness theorem
-- ─────────────────────────────────────────────────────────────

theorem soundness_lfp {Γ : Set (Pattern Symbol)} {φ : Pattern Symbol}
    (h : Γ ⊩ᵢ φ) :
    ∀ (L : Type*) [Order.Frame L] (M : HModel Symbol L),
    (∀ γ ∈ Γ, HValid M γ) → HValid M φ := by
  induction h with
  | assumption hmem => exact fun _ _ M hΓ ρ m => hΓ _ hmem ρ m
  | contractionOr => exact fun _ _ _ _ _ m => hvalid_contractionOr m
  | contractionAnd => exact fun _ _ _ _ _ m => hvalid_contractionAnd m
  | weakeningOr => exact fun _ _ _ _ _ m => hvalid_weakeningOr m
  | weakeningAnd => exact fun _ _ _ _ _ m => hvalid_weakeningAnd m
  | permutationOr => exact fun _ _ _ _ _ m => hvalid_permutationOr m
  | permutationAnd => exact fun _ _ _ _ _ m => hvalid_permutationAnd m
  | mp _ _ ih₁ ih₂ =>
    exact fun L _ M hΓ ρ m => hvalid_mp (ih₁ L M hΓ ρ m) (ih₂ L M hΓ ρ m)
  | botElim => exact fun _ _ _ _ _ m => hvalid_botElim m
  | syllogism _ _ ih₁ ih₂ =>
    exact fun L _ M hΓ ρ m => hvalid_syllogism (ih₁ L M hΓ ρ m) (ih₂ L M hΓ ρ m)
  | exportation _ ih =>
    exact fun L _ M hΓ ρ m => hvalid_exportation (ih L M hΓ ρ m)
  | importation _ ih =>
    exact fun L _ M hΓ ρ m => hvalid_importation (ih L M hΓ ρ m)
  | expansion _ ih =>
    exact fun L _ M hΓ ρ m => hvalid_expansion (ih L M hΓ ρ m)
  | existQuant => exact fun _ _ _ _ _ m => hvalid_existQuant m
  | existGen _ ih =>
    exact fun L _ M hΓ ρ m => hvalid_existGen (ih L M hΓ) m
  | forallQuant => exact fun _ _ _ _ _ m => hvalid_forallQuant m
  | forallGen _ ih =>
    exact fun L _ M hΓ ρ m => hvalid_forallGen (ih L M hΓ) m
  | existence => exact fun _ _ _ _ _ m => hvalid_existence m
  | svSubst _ ih =>
    exact fun L _ M hΓ ρ m => hvalid_svSubst (ih L M hΓ) m
  | preFixpoint hpos =>
    exact fun _ _ _ _ _ m => hvalid_preFixpoint_lfp hpos m
  | knasterTarski _ ih =>
    exact fun L _ M hΓ ρ m => hvalid_knasterTarski_lfp (ih L M hΓ ρ) m
  | postFixpoint hpos =>
    exact fun _ _ _ _ _ m => hvalid_postFixpoint_lfp hpos m
  | park _ ih =>
    exact fun L _ M hΓ ρ m => hvalid_park_lfp (ih L M hΓ ρ) m
  | singleton =>
    exact fun _ _ _ _ _ m => hvalid_singleton m
  | propagationOrLeft =>
    exact fun _ _ _ _ _ m => hvalid_propagationOrLeft m
  | propagationOrRight =>
    exact fun _ _ _ _ _ m => hvalid_propagationOrRight m
  | propagationExistLeft =>
    exact fun _ _ _ _ _ m => hvalid_propagationExistLeft m
  | propagationExistRight =>
    exact fun _ _ _ _ _ m => hvalid_propagationExistRight m
  | framingLeft _ ih =>
    exact fun L _ M hΓ ρ m => hvalid_framingLeft m (ih L M hΓ ρ)
  | framingRight _ ih =>
    exact fun L _ M hΓ ρ m => hvalid_framingRight m (ih L M hΓ ρ)

end IML
