import IML.HeytingSoundness

/-!
# Fixed-point soundness via lfp/gfp

Under positivity, the map `S ↦ ⟦φ⟧(ρ[X := S])` is monotone on the
complete lattice `Carrier → L`. We connect `hinterp` of `μ`/`ν` to
Mathlib's `OrderHom.lfp`/`OrderHom.gfp`, then derive the fixpoint rules
from `OrderHom.map_lfp`/`OrderHom.map_gfp` (Knaster-Tarski).

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
  toFun S := fun m => hinterp M (ρ.pushSVar S) φ m
  monotone' S₁ S₂ hle m :=
    hinterp_mono_pos hpos (ρ.pushSVar S₁) (ρ.pushSVar S₂) rfl
      (fun i hi => by cases i with | zero => exact absurd rfl hi | succ => rfl)
      (hle ·) m

end MonotoneFunctional

-- ─────────────────────────────────────────────────────────────
-- Bridge: hinterp of μ/ν equals Mathlib's lfp/gfp
-- ─────────────────────────────────────────────────────────────

theorem hinterp_mu_eq_lfp {φ : Pattern Symbol} (hpos : SVarPositive φ 0)
    (m : M.Carrier) :
    hinterp M ρ (μ φ) m = (fixpointFun M ρ φ hpos).lfp m := by
  apply le_antisymm
  · apply sInf_le
    exact ⟨(fixpointFun M ρ φ hpos).lfp,
      fun n => le_of_eq (congr_fun (fixpointFun M ρ φ hpos).map_lfp n), rfl⟩
  · apply le_sInf; intro x ⟨S, hS, hx⟩; subst hx
    exact OrderHom.lfp_le (f := fixpointFun M ρ φ hpos) hS m

theorem hinterp_nu_eq_gfp {φ : Pattern Symbol} (hpos : SVarPositive φ 0)
    (m : M.Carrier) :
    hinterp M ρ (ν φ) m = (fixpointFun M ρ φ hpos).gfp m := by
  apply le_antisymm
  · apply sSup_le; intro x ⟨S, hS, hx⟩; subst hx
    exact OrderHom.le_gfp (f := fixpointFun M ρ φ hpos) hS m
  · apply le_sSup
    exact ⟨(fixpointFun M ρ φ hpos).gfp,
      fun n => le_of_eq (congr_fun (fixpointFun M ρ φ hpos).map_gfp n).symm, rfl⟩

-- ─────────────────────────────────────────────────────────────
-- Fixed point equations via Mathlib's Knaster-Tarski
-- ─────────────────────────────────────────────────────────────

theorem hinterp_mu_fixpoint {φ : Pattern Symbol} (hpos : SVarPositive φ 0)
    (m : M.Carrier) :
    hinterp M (ρ.pushSVar (fun n => hinterp M ρ (μ φ) n)) φ m =
    hinterp M ρ (μ φ) m := by
  have hfun : (fun n => hinterp M ρ (μ φ) n) = (fixpointFun M ρ φ hpos).lfp :=
    funext (hinterp_mu_eq_lfp hpos)
  trans (fixpointFun M ρ φ hpos).lfp m
  · rw [hfun]; exact congr_fun (fixpointFun M ρ φ hpos).map_lfp m
  · exact (hinterp_mu_eq_lfp hpos m).symm

theorem hinterp_nu_fixpoint {φ : Pattern Symbol} (hpos : SVarPositive φ 0)
    (m : M.Carrier) :
    hinterp M (ρ.pushSVar (fun n => hinterp M ρ (ν φ) n)) φ m =
    hinterp M ρ (ν φ) m := by
  have hfun : (fun n => hinterp M ρ (ν φ) n) = (fixpointFun M ρ φ hpos).gfp :=
    funext (hinterp_nu_eq_gfp hpos)
  trans (fixpointFun M ρ φ hpos).gfp m
  · rw [hfun]; exact congr_fun (fixpointFun M ρ φ hpos).map_gfp m
  · exact (hinterp_nu_eq_gfp hpos m).symm

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
  have hpre : ∀ n, hinterp M (ρ.pushSVar (fun n => hinterp M ρ ψ n)) φ n ≤
      hinterp M ρ ψ n := fun n => by
    have := h n; simp only [hinterp] at this
    exact himp_eq_top_iff.mp (by rw [hinterp_svarSubst] at this; exact this)
  apply sInf_le
  exact ⟨fun n => hinterp M ρ ψ n, hpre, rfl⟩

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
      hinterp M (ρ.pushSVar (fun n => hinterp M ρ ψ n)) φ n := fun n => by
    have := h n; simp only [hinterp] at this
    exact himp_eq_top_iff.mp (by rw [hinterp_svarSubst] at this; exact this)
  apply le_sSup
  exact ⟨fun n => hinterp M ρ ψ n, hpost, rfl⟩

-- ─────────────────────────────────────────────────────────────
-- Full soundness theorem
-- ─────────────────────────────────────────────────────────────

theorem soundness_lfp {Γ : Set (Pattern Symbol)} {φ : Pattern Symbol}
    (h : Γ ⊩ᵢ φ) :
    ∀ (L : Type*) [inst : Order.Frame L] (M : HModel Symbol L),
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
