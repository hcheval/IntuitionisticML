import IML.HInterpCommutation

/-!
# Soundness of iAML over Carrier → L semantics

The correct Heyting algebra semantics: patterns interpreted as
L-valued predicates (Carrier → L), not global lattice elements.
-/

namespace IML

open Pattern

variable {Symbol : Type} {L : Type*} [Order.Frame L]
         {M : HModel Symbol L} {ρ : HValuation M}

-- ─────────────────────────────────────────────────────────────
-- Helper: pointwise himp = ⊤ iff ≤
-- ─────────────────────────────────────────────────────────────

private theorem himp_eq_top_iff {a b : L} :
    (a ⇨ b) = ⊤ ↔ a ≤ b := by
  rw [eq_top_iff, le_himp_iff]
  exact ⟨fun h => by rw [top_inf_eq] at h; exact h,
         fun h => by rw [top_inf_eq]; exact h⟩

-- ─────────────────────────────────────────────────────────────
-- Contraction / Weakening / Permutation
-- ─────────────────────────────────────────────────────────────

theorem hvalid_contractionOr {φ : Pattern Symbol} (m : M.Carrier) :
    hinterp M ρ (φ ⊔ φ ⇒ φ) m = ⊤ := by
  simp only [hinterp]; exact himp_eq_top_iff.mpr (le_of_eq (sup_idem _))

theorem hvalid_contractionAnd {φ : Pattern Symbol} (m : M.Carrier) :
    hinterp M ρ (φ ⇒ φ ⊓ φ) m = ⊤ := by
  simp only [hinterp]; exact himp_eq_top_iff.mpr (le_inf le_rfl le_rfl)

theorem hvalid_weakeningOr {φ ψ : Pattern Symbol} (m : M.Carrier) :
    hinterp M ρ (φ ⇒ φ ⊔ ψ) m = ⊤ := by
  simp only [hinterp]; exact himp_eq_top_iff.mpr le_sup_left

theorem hvalid_weakeningAnd {φ ψ : Pattern Symbol} (m : M.Carrier) :
    hinterp M ρ (φ ⊓ ψ ⇒ φ) m = ⊤ := by
  simp only [hinterp]; exact himp_eq_top_iff.mpr inf_le_left

theorem hvalid_permutationOr {φ ψ : Pattern Symbol} (m : M.Carrier) :
    hinterp M ρ (φ ⊔ ψ ⇒ ψ ⊔ φ) m = ⊤ := by
  simp only [hinterp]; exact himp_eq_top_iff.mpr (le_of_eq (sup_comm _ _))

theorem hvalid_permutationAnd {φ ψ : Pattern Symbol} (m : M.Carrier) :
    hinterp M ρ (φ ⊓ ψ ⇒ ψ ⊓ φ) m = ⊤ := by
  simp only [hinterp]; exact himp_eq_top_iff.mpr (le_of_eq (inf_comm _ _))

-- ─────────────────────────────────────────────────────────────
-- Modus ponens / Bottom elimination
-- ─────────────────────────────────────────────────────────────

theorem hvalid_mp {φ ψ : Pattern Symbol} {m : M.Carrier}
    (h₁ : hinterp M ρ (φ ⇒ ψ) m = ⊤)
    (h₂ : hinterp M ρ φ m = ⊤) :
    hinterp M ρ ψ m = ⊤ := by
  simp only [hinterp] at h₁
  exact top_le_iff.mp (h₂ ▸ himp_eq_top_iff.mp h₁)

theorem hvalid_botElim {φ : Pattern Symbol} (m : M.Carrier) :
    hinterp M ρ ((⊥ₘ : Pattern Symbol) ⇒ φ) m = ⊤ := by
  simp only [hinterp]; exact himp_eq_top_iff.mpr bot_le

-- ─────────────────────────────────────────────────────────────
-- Syllogism / Exportation / Importation / Expansion
-- ─────────────────────────────────────────────────────────────

theorem hvalid_syllogism {φ ψ χ : Pattern Symbol} {m : M.Carrier}
    (h₁ : hinterp M ρ (φ ⇒ ψ) m = ⊤)
    (h₂ : hinterp M ρ (ψ ⇒ χ) m = ⊤) :
    hinterp M ρ (φ ⇒ χ) m = ⊤ := by
  simp only [hinterp] at *
  exact himp_eq_top_iff.mpr (le_trans (himp_eq_top_iff.mp h₁) (himp_eq_top_iff.mp h₂))

theorem hvalid_exportation {φ ψ χ : Pattern Symbol} {m : M.Carrier}
    (h : hinterp M ρ (φ ⊓ ψ ⇒ χ) m = ⊤) :
    hinterp M ρ (φ ⇒ ψ ⇒ χ) m = ⊤ := by
  simp only [hinterp] at *
  rw [himp_eq_top_iff, le_himp_iff]
  exact himp_eq_top_iff.mp h

theorem hvalid_importation {φ ψ χ : Pattern Symbol} {m : M.Carrier}
    (h : hinterp M ρ (φ ⇒ ψ ⇒ χ) m = ⊤) :
    hinterp M ρ (φ ⊓ ψ ⇒ χ) m = ⊤ := by
  simp only [hinterp] at *
  exact himp_eq_top_iff.mpr (le_himp_iff.mp (himp_eq_top_iff.mp h))

theorem hvalid_expansion {φ ψ χ : Pattern Symbol} {m : M.Carrier}
    (h : hinterp M ρ (φ ⇒ ψ) m = ⊤) :
    hinterp M ρ (χ ⊔ φ ⇒ χ ⊔ ψ) m = ⊤ := by
  simp only [hinterp] at *
  exact himp_eq_top_iff.mpr (sup_le_sup_left (himp_eq_top_iff.mp h) _)

-- ─────────────────────────────────────────────────────────────
-- Application: framing
-- ─────────────────────────────────────────────────────────────

theorem hvalid_framingLeft {φ₁ φ₂ ψ : Pattern Symbol} (m : M.Carrier)
    (h : ∀ m, hinterp M ρ (φ₁ ⇒ φ₂) m = ⊤) :
    hinterp M ρ (φ₁ ⬝ ψ ⇒ φ₂ ⬝ ψ) m = ⊤ := by
  simp only [hinterp] at h ⊢
  rw [himp_eq_top_iff]
  apply iSup_le; intro a; apply iSup_le; intro b
  apply le_iSup_of_le a; apply le_iSup_of_le b
  apply inf_le_inf_right
  exact inf_le_inf_right _ (himp_eq_top_iff.mp (h a))

theorem hvalid_framingRight {φ₁ φ₂ ψ : Pattern Symbol} (m : M.Carrier)
    (h : ∀ m, hinterp M ρ (φ₁ ⇒ φ₂) m = ⊤) :
    hinterp M ρ (ψ ⬝ φ₁ ⇒ ψ ⬝ φ₂) m = ⊤ := by
  simp only [hinterp] at h ⊢
  rw [himp_eq_top_iff]
  apply iSup_le; intro a; apply iSup_le; intro b
  apply le_iSup_of_le a; apply le_iSup_of_le b
  apply inf_le_inf_right
  exact inf_le_inf_left _ (himp_eq_top_iff.mp (h b))

-- ─────────────────────────────────────────────────────────────
-- Propagation (uses Frame distributivity)
-- ─────────────────────────────────────────────────────────────

theorem hvalid_propagationOrLeft {φ₁ φ₂ ψ : Pattern Symbol}
    (m : M.Carrier) :
    hinterp M ρ ((φ₁ ⊔ φ₂) ⬝ ψ ⇒ φ₁ ⬝ ψ ⊔ φ₂ ⬝ ψ) m = ⊤ := by
  simp only [hinterp_app, hinterp_disj, hinterp_impl]; rw [himp_eq_top_iff]
  apply iSup_le; intro a; apply iSup_le; intro b
  rw [inf_sup_right, inf_sup_right]
  exact sup_le_sup (le_iSup₂_of_le a b le_rfl) (le_iSup₂_of_le a b le_rfl)

theorem hvalid_propagationOrRight {φ₁ φ₂ ψ : Pattern Symbol}
    (m : M.Carrier) :
    hinterp M ρ (ψ ⬝ (φ₁ ⊔ φ₂) ⇒ ψ ⬝ φ₁ ⊔ ψ ⬝ φ₂) m = ⊤ := by
  simp only [hinterp_app, hinterp_disj, hinterp_impl]; rw [himp_eq_top_iff]
  apply iSup_le; intro a; apply iSup_le; intro b
  rw [inf_assoc, inf_sup_right, inf_sup_left, ← inf_assoc, ← inf_assoc]
  exact sup_le_sup (le_iSup₂_of_le a b le_rfl) (le_iSup₂_of_le a b le_rfl)

-- ─────────────────────────────────────────────────────────────
-- Singleton
-- ─────────────────────────────────────────────────────────────

private theorem evar_conj_eq {n : EVarIndex} (φ : Pattern Symbol)
    (a : M.Carrier) :
    hinterp M ρ (.conj (.evar n) φ) a =
    @ite L (a = ρ.evar n) (M.decEq a (ρ.evar n)) (hinterp M ρ φ a) ⊥ := by
  change @Min.min L _ (@ite L (a = ρ.evar n) (M.decEq a (ρ.evar n)) ⊤ ⊥) (hinterp M ρ φ a) = _
  split <;> simp_all

private theorem fill_le_iSup (C : AppCtx Symbol) (X : Pattern Symbol)
    (m : M.Carrier) :
    hinterp M ρ (C.fill X) m ≤ ⨆ a, hinterp M ρ X a := by
  match C with
  | .hole => exact le_iSup _ m
  | .left C' ψ =>
    simp only [AppCtx.fill, hinterp]
    apply iSup_le; intro a; apply iSup_le; intro b
    exact le_trans (le_trans inf_le_left inf_le_left) (fill_le_iSup C' X a)
  | .right ψ C' =>
    simp only [AppCtx.fill, hinterp]
    apply iSup_le; intro a; apply iSup_le; intro b
    exact le_trans (le_trans inf_le_left inf_le_right) (fill_le_iSup C' X b)

theorem hvalid_singleton {C₁ C₂ : AppCtx Symbol} {n : EVarIndex}
    {φ : Pattern Symbol} (m : M.Carrier) :
    hinterp M ρ (~(C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n ⊓ ~φ))) m = ⊤ := by
  change @HImp.himp L _ (@Min.min L _
    (hinterp M ρ (C₁.fill _) m) (hinterp M ρ (C₂.fill _) m)) ⊥ = ⊤
  rw [himp_eq_top_iff]
  apply le_trans (inf_le_inf (fill_le_iSup C₁ _ m) (fill_le_iSup C₂ _ m))
  rw [inf_iSup_eq]
  apply iSup_le; intro a
  rw [iSup_inf_eq]
  apply iSup_le; intro a'
  rw [evar_conj_eq φ a', evar_conj_eq (Pattern.neg φ) a]
  split <;> split <;> simp_all [bot_le]
  · exact le_bot_iff.mp inf_himp_le

-- ─────────────────────────────────────────────────────────────
-- Quantifiers
-- ─────────────────────────────────────────────────────────────
#check himp_eq_sSup
theorem hvalid_existQuant {φ : Pattern Symbol} {n : EVarIndex}
    (m : M.Carrier) :
    hinterp M ρ (evarSubst 0 (.evar n) φ ⇒ ∃ₑ φ) m = ⊤ := by
  simp only [hinterp]; rw [himp_eq_top_iff, hinterp_evarSubst]
  exact le_iSup (fun a => hinterp M (ρ.pushEVar a) φ m) (ρ.evar n)

theorem hvalid_existGen {φ₁ φ₂ : Pattern Symbol}
    (h : ∀ (ρ : HValuation M) (m : M.Carrier),
      hinterp M ρ (φ₁ ⇒ evarLift φ₂) m = ⊤) (m : M.Carrier) :
    hinterp M ρ (∃ₑ φ₁ ⇒ φ₂) m = ⊤ := by
  simp only [hinterp]; rw [himp_eq_top_iff]
  apply iSup_le; intro a
  have := himp_eq_top_iff.mp (by simp only [hinterp] at h; exact h (ρ.pushEVar a) m)
  rwa [hinterp_evarLift] at this

theorem hvalid_forallQuant {φ : Pattern Symbol} {n : EVarIndex}
    (m : M.Carrier) :
    hinterp M ρ (∀ₑ φ ⇒ evarSubst 0 (.evar n) φ) m = ⊤ := by
  simp only [hinterp]; rw [himp_eq_top_iff, hinterp_evarSubst]
  exact iInf_le (fun a => hinterp M (ρ.pushEVar a) φ m) (ρ.evar n)

theorem hvalid_forallGen {φ₁ φ₂ : Pattern Symbol}
    (h : ∀ (ρ : HValuation M) (m : M.Carrier),
      hinterp M ρ (evarLift φ₁ ⇒ φ₂) m = ⊤) (m : M.Carrier) :
    hinterp M ρ (φ₁ ⇒ ∀ₑ φ₂) m = ⊤ := by
  simp only [hinterp]; rw [himp_eq_top_iff]
  apply le_iInf; intro a
  have := himp_eq_top_iff.mp (by simp only [hinterp] at h; exact h (ρ.pushEVar a) m)
  rwa [hinterp_evarLift] at this

theorem hvalid_existence (m : M.Carrier) :
    hinterp M ρ (∃ₑ (.evar 0 : Pattern Symbol)) m = ⊤ := by
  simp only [hinterp, HValuation.pushEVar]
  apply eq_top_iff.mpr
  exact le_iSup_of_le m (by split <;> simp_all)

-- ─────────────────────────────────────────────────────────────
-- Propagation for ∃
-- ─────────────────────────────────────────────────────────────

theorem hvalid_propagationExistLeft {φ ψ : Pattern Symbol}
    (m : M.Carrier) :
    hinterp M ρ ((∃ₑ φ) ⬝ ψ ⇒ ∃ₑ (φ ⬝ evarLift ψ)) m = ⊤ := by
  simp only [hinterp_impl, hinterp_app, hinterp_exist]
  rw [himp_eq_top_iff]
  apply iSup_le; intro a; apply iSup_le; intro b
  rw [inf_assoc]; rw [iSup_inf_eq]
  apply iSup_le; intro c
  apply le_iSup_of_le c; apply le_iSup_of_le a; apply le_iSup_of_le b
  rw [← inf_assoc, hinterp_evarLift]

theorem hvalid_propagationExistRight {φ ψ : Pattern Symbol}
    (m : M.Carrier) :
    hinterp M ρ (ψ ⬝ (∃ₑ φ) ⇒ ∃ₑ (evarLift ψ ⬝ φ)) m = ⊤ := by
  simp only [hinterp_impl, hinterp_app, hinterp_exist]
  rw [himp_eq_top_iff]
  apply iSup_le; intro a; apply iSup_le; intro b
  rw [inf_iSup_eq, iSup_inf_eq]
  apply iSup_le; intro c
  apply le_iSup_of_le c; apply le_iSup_of_le a; apply le_iSup_of_le b
  rw [hinterp_evarLift]

-- ─────────────────────────────────────────────────────────────
-- Substitution and fixpoints
-- ─────────────────────────────────────────────────────────────

theorem hvalid_svSubst {φ ψ : Pattern Symbol}
    (h : ∀ (ρ : HValuation M) (m : M.Carrier), hinterp M ρ φ m = ⊤)
    (m : M.Carrier) :
    hinterp M ρ (svarSubst 0 ψ φ) m = ⊤ := by
  rw [hinterp_svarSubst]; exact h _ _

-- ─────────────────────────────────────────────────────────────
-- Monotonicity from positivity (mutual induction)
-- ─────────────────────────────────────────────────────────────

private def pushSVar_mono_args {M : HModel Symbol L} {n : SVarIndex}
    {ρ₁ ρ₂ : HValuation M} (R : M.Carrier → L)
    (hevar : ρ₁.evar = ρ₂.evar)
    (hsvar_eq : ∀ i, i ≠ n → ρ₁.svar i = ρ₂.svar i)
    (hsvar_le : ∀ m, ρ₁.svar n m ≤ ρ₂.svar n m) :
    (ρ₁.pushSVar R).evar = (ρ₂.pushSVar R).evar ∧
    (∀ i, i ≠ n + 1 → (ρ₁.pushSVar R).svar i = (ρ₂.pushSVar R).svar i) ∧
    (∀ m, (ρ₁.pushSVar R).svar (n + 1) m ≤ (ρ₂.pushSVar R).svar (n + 1) m) :=
  ⟨hevar, fun i hi => by
    cases i with
    | zero => rfl
    | succ j => exact hsvar_eq j (fun h => hi (congrArg _ h)),
   fun m => hsvar_le m⟩

mutual
def hinterp_mono_pos {Symbol : Type} {L : Type*} [Order.Frame L]
    {M : HModel Symbol L} {φ : Pattern Symbol} {n : SVarIndex}
    (hpos : SVarPositive φ n) (ρ₁ ρ₂ : HValuation M)
    (hevar : ρ₁.evar = ρ₂.evar)
    (hsvar_eq : ∀ i, i ≠ n → ρ₁.svar i = ρ₂.svar i)
    (hsvar_le : ∀ m, ρ₁.svar n m ≤ ρ₂.svar n m)
    (m : M.Carrier) :
    hinterp M ρ₁ φ m ≤ hinterp M ρ₂ φ m :=
  match hpos with
  | .evar (i := i) => by simp only [hinterp]; rw [show ρ₁.evar i = ρ₂.evar i from congrFun hevar i]
  | .svar => hsvar_le m
  | .svarNe hne => by simp only [hinterp]; rw [show ρ₁.svar _ = ρ₂.svar _ from hsvar_eq _ hne]
  | .symbol => le_refl _
  | .bot => le_refl _
  | .app hpφ hpψ => by
    simp only [hinterp]
    exact iSup_mono fun a => iSup_mono fun b =>
      inf_le_inf_right _ (inf_le_inf
        (hinterp_mono_pos hpφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le a)
        (hinterp_mono_pos hpψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le b))
  | .impl hnφ hpψ => by
    simp only [hinterp]
    exact himp_le_himp
      (hinterp_mono_neg hnφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
      (hinterp_mono_pos hpψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
  | .conj hpφ hpψ => by
    simp only [hinterp]
    exact inf_le_inf
      (hinterp_mono_pos hpφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
      (hinterp_mono_pos hpψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
  | .disj hpφ hpψ => by
    simp only [hinterp]
    exact sup_le_sup
      (hinterp_mono_pos hpφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
      (hinterp_mono_pos hpψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
  | .exist hpφ => by
    simp only [hinterp]
    exact iSup_mono fun a =>
      hinterp_mono_pos hpφ (ρ₁.pushEVar a) (ρ₂.pushEVar a)
        (by ext i; cases i <;> simp [HValuation.pushEVar, hevar])
        (fun i hi => hsvar_eq i hi) hsvar_le m
  | .forallP hpφ => by
    simp only [hinterp]
    exact iInf_mono fun a =>
      hinterp_mono_pos hpφ (ρ₁.pushEVar a) (ρ₂.pushEVar a)
        (by ext i; cases i <;> simp [HValuation.pushEVar, hevar])
        (fun i hi => hsvar_eq i hi) hsvar_le m
  | .mu hpφ => by
    simp only [hinterp]
    apply sInf_le_sInf; intro x ⟨R, hR, hx⟩
    let ⟨he, hs, hl⟩ := pushSVar_mono_args R hevar hsvar_eq hsvar_le
    exact ⟨R, fun k => le_trans (hinterp_mono_pos hpφ _ _ he hs hl k) (hR k), hx⟩
  | .nu hpφ => by
    simp only [hinterp]
    apply sSup_le_sSup; intro x ⟨R, hR, hx⟩
    let ⟨he, hs, hl⟩ := pushSVar_mono_args R hevar hsvar_eq hsvar_le
    exact ⟨R, fun k => le_trans (hR k) (hinterp_mono_pos hpφ _ _ he hs hl k), hx⟩

def hinterp_mono_neg {Symbol : Type} {L : Type*} [Order.Frame L]
    {M : HModel Symbol L} {φ : Pattern Symbol} {n : SVarIndex}
    (hneg : SVarNegative φ n) (ρ₁ ρ₂ : HValuation M)
    (hevar : ρ₁.evar = ρ₂.evar)
    (hsvar_eq : ∀ i, i ≠ n → ρ₁.svar i = ρ₂.svar i)
    (hsvar_le : ∀ m, ρ₁.svar n m ≤ ρ₂.svar n m)
    (m : M.Carrier) :
    hinterp M ρ₂ φ m ≤ hinterp M ρ₁ φ m :=
  match hneg with
  | .evar (i := i) => by simp only [hinterp]; rw [show ρ₁.evar i = ρ₂.evar i from congrFun hevar i]
  | .svarNe hne => by simp only [hinterp]; rw [show ρ₁.svar _ = ρ₂.svar _ from hsvar_eq _ hne]
  | .symbol => le_refl _
  | .bot => le_refl _
  | .app hnφ hnψ => by
    simp only [hinterp]
    exact iSup_mono fun a => iSup_mono fun b =>
      inf_le_inf_right _ (inf_le_inf
        (hinterp_mono_neg hnφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le a)
        (hinterp_mono_neg hnψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le b))
  | .impl hpφ hnψ => by
    simp only [hinterp]
    exact himp_le_himp
      (hinterp_mono_pos hpφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
      (hinterp_mono_neg hnψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
  | .conj hnφ hnψ => by
    simp only [hinterp]
    exact inf_le_inf
      (hinterp_mono_neg hnφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
      (hinterp_mono_neg hnψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
  | .disj hnφ hnψ => by
    simp only [hinterp]
    exact sup_le_sup
      (hinterp_mono_neg hnφ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
      (hinterp_mono_neg hnψ ρ₁ ρ₂ hevar hsvar_eq hsvar_le m)
  | .exist hnφ => by
    simp only [hinterp]
    exact iSup_mono fun a =>
      hinterp_mono_neg hnφ (ρ₁.pushEVar a) (ρ₂.pushEVar a)
        (by ext i; cases i <;> simp [HValuation.pushEVar, hevar])
        (fun i hi => hsvar_eq i hi) hsvar_le m
  | .forallP hnφ => by
    simp only [hinterp]
    exact iInf_mono fun a =>
      hinterp_mono_neg hnφ (ρ₁.pushEVar a) (ρ₂.pushEVar a)
        (by ext i; cases i <;> simp [HValuation.pushEVar, hevar])
        (fun i hi => hsvar_eq i hi) hsvar_le m
  | .mu hnφ => by
    simp only [hinterp]
    apply sInf_le_sInf; intro x ⟨R, hR, hx⟩
    let ⟨he, hs, hl⟩ := pushSVar_mono_args R hevar hsvar_eq hsvar_le
    exact ⟨R, fun k => le_trans (hinterp_mono_neg hnφ _ _ he hs hl k) (hR k), hx⟩
  | .nu hnφ => by
    simp only [hinterp]
    apply sSup_le_sSup; intro x ⟨R, hR, hx⟩
    let ⟨he, hs, hl⟩ := pushSVar_mono_args R hevar hsvar_eq hsvar_le
    exact ⟨R, fun k => le_trans (hR k) (hinterp_mono_neg hnφ _ _ he hs hl k), hx⟩
end

-- ─────────────────────────────────────────────────────────────

theorem hvalid_preFixpoint {φ : Pattern Symbol}
    (hpos : SVarPositive φ 0) (m : M.Carrier) :
    hinterp M ρ (svarSubst 0 (μ φ) φ ⇒ μ φ) m = ⊤ := by
  simp only [hinterp]; rw [himp_eq_top_iff, hinterp_svarSubst]
  apply le_sInf; intro x ⟨S, hS, hx⟩; subst hx
  have hmu_le : ∀ k, hinterp M ρ (μ φ) k ≤ S k := fun k => by
    apply sInf_le; exact ⟨S, hS, rfl⟩
  exact le_trans
    (hinterp_mono_pos hpos (ρ.pushSVar (fun n => hinterp M ρ (μ φ) n)) (ρ.pushSVar S)
      rfl (fun i hi => by cases i with
        | zero => exact absurd rfl hi
        | succ j => rfl)
      hmu_le m)
    (hS m)

theorem hvalid_knasterTarski {φ ψ : Pattern Symbol}
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

theorem hvalid_postFixpoint {φ : Pattern Symbol}
    (hpos : SVarPositive φ 0) (m : M.Carrier) :
    hinterp M ρ (ν φ ⇒ svarSubst 0 (ν φ) φ) m = ⊤ := by
  simp only [hinterp]; rw [himp_eq_top_iff, hinterp_svarSubst]
  apply sSup_le; intro x ⟨S, hS, hx⟩; subst hx
  have hnu_ge : ∀ k, S k ≤ hinterp M ρ (ν φ) k := fun k => by
    apply le_sSup; exact ⟨S, hS, rfl⟩
  exact le_trans (hS m)
    (hinterp_mono_pos hpos (ρ.pushSVar S) (ρ.pushSVar (fun n => hinterp M ρ (ν φ) n))
      rfl (fun i hi => by cases i with
        | zero => exact absurd rfl hi
        | succ j => rfl)
      hnu_ge m)

theorem hvalid_park {φ ψ : Pattern Symbol}
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
-- Soundness theorem
-- ─────────────────────────────────────────────────────────────

theorem soundness {Γ : Set (Pattern Symbol)} {φ : Pattern Symbol}
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
    exact fun _ _ _ _ _ m => hvalid_preFixpoint hpos m
  | knasterTarski _ ih =>
    exact fun L _ M hΓ ρ m => hvalid_knasterTarski (ih L M hΓ ρ) m
  | postFixpoint hpos =>
    exact fun _ _ _ _ _ m => hvalid_postFixpoint hpos m
  | park _ ih =>
    exact fun L _ M hΓ ρ m => hvalid_park (ih L M hΓ ρ) m
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

#print axioms soundness
end IML
