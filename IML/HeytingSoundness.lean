import IML.HInterpCommutation

/-!
# Soundness of iAML over Carrier → L semantics

Patterns are interpreted as L-valued predicates (Carrier → L) over an
L-valued equality `E`; see `IML.HeytingSemantics`. SINGLETON is sound
because every interpretation is extensional (`hinterp_ext`), and
EXISTENCE because `E` is reflexive. No other rule touches `E`.

The SINGLETON case goes through the *context kernel lemma* `hinterp_fill`:
for every application context `C` there is a kernel `K_C : Carrier → Carrier → L`
with `⟦C[X]⟧ m = ⨆ a, ⟦X⟧ a ⊓ K_C a m`.
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
-- The context kernel lemma
-- ─────────────────────────────────────────────────────────────

/-- The kernel of an application context: `K_C a m` measures "`a` at the hole
of `C` yields `m`". For the empty context it is the model's equality `E a m`. -/
def AppCtx.kernel (M : HModel Symbol L) (ρ : HValuation M) :
    AppCtx Symbol → M.Carrier → M.Carrier → L
  | .hole => fun a m => M.E a m
  | .left C ψ => fun a m =>
      ⨆ b, ⨆ c, AppCtx.kernel M ρ C a b ⊓ hinterp M ρ ψ c ⊓ M.appInterp b c m
  | .right ψ C => fun a m =>
      ⨆ b, ⨆ c, hinterp M ρ ψ b ⊓ AppCtx.kernel M ρ C a c ⊓ M.appInterp b c m

/-- **The context kernel lemma**: `⟦C[X]⟧ m = ⨆ a, ⟦X⟧ a ⊓ K_C a m`. The hole
case is extensionality of `⟦X⟧` (`hull_eq_of_ext`); the other cases are Frame
distributivity. -/
theorem hinterp_fill (C : AppCtx Symbol) (X : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (C.fill X) m = ⨆ a, hinterp M ρ X a ⊓ C.kernel M ρ a m := by
  induction C generalizing m with
  | hole =>
    simp only [AppCtx.fill, AppCtx.kernel]
    refine (congrFun (M.hull_eq_of_ext (hinterp_ext X ρ)) m).symm.trans ?_
    exact iSup_congr fun a => inf_comm _ _
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

/-- The bound `⟦C[X]⟧ m ≤ ⨆ a, ⟦X⟧ a`, a corollary of the kernel lemma. -/
theorem fill_le_iSup (C : AppCtx Symbol) (X : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (C.fill X) m ≤ ⨆ a, hinterp M ρ X a := by
  rw [hinterp_fill]; exact iSup_mono fun a => inf_le_left

-- ─────────────────────────────────────────────────────────────
-- Singleton
-- ─────────────────────────────────────────────────────────────

/-- **The positive SINGLETON rule is sound**:
`C₁[x ⊓ φ] ⊓ C₂[x ⊓ ψ] ⇒ C₂[x ⊓ (φ ⊓ ψ)]` holds in every `HModel`. By the
kernel lemma the premise is a supremum over witnesses `a` (at the hole of
`C₁`) and `b` (at the hole of `C₂`) of `E a x ⊓ φ a ⊓ K₁ a m ⊓ E b x ⊓ ψ b ⊓ K₂ b m`.
Symmetry and transitivity give `E a x ⊓ E b x ≤ E a b`, and extensionality of
`⟦φ⟧` transports `φ` from `a` to `b`, so `b` witnesses the conclusion. -/
theorem hvalid_singletonStrong {C₁ C₂ : AppCtx Symbol} {n : EVarIndex}
    {φ ψ : Pattern Symbol} (m : M.Carrier) :
    hinterp M ρ (C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n ⊓ ψ) ⇒
      C₂.fill (.evar n ⊓ (φ ⊓ ψ))) m = ⊤ := by
  simp only [hinterp_impl, hinterp_conj]
  rw [himp_eq_top_iff, hinterp_fill, hinterp_fill, hinterp_fill]
  rw [iSup_inf_eq]; apply iSup_le; intro a
  rw [inf_iSup_eq]; apply iSup_le; intro b
  apply le_iSup_of_le b
  simp only [hinterp_conj, hinterp_evar]
  -- goal: (E a x ⊓ φ a ⊓ K₁ a m) ⊓ (E b x ⊓ ψ b ⊓ K₂ b m) ≤ E b x ⊓ (φ b ⊓ ψ b) ⊓ K₂ b m
  refine le_inf (le_inf ?_ (le_inf ?_ ?_)) ?_
  · exact inf_le_right.trans (inf_le_left.trans inf_le_left)
  · refine le_trans ?_ (hinterp_ext φ ρ a b)
    refine le_trans (le_inf ?_ ?_) (inf_le_inf_right _ (M.E_trans_symm a b (ρ.evar n)))
    · exact le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
        (inf_le_right.trans (inf_le_left.trans inf_le_left))
    · exact inf_le_left.trans (inf_le_left.trans inf_le_right)
  · exact inf_le_right.trans (inf_le_left.trans inf_le_right)
  · exact inf_le_right.trans inf_le_right

/-- The classical negative SINGLETON `~(C₁[x ⊓ φ] ⊓ C₂[x ⊓ ~φ])` is sound as
well (it is a derived rule of the proof system; this is a direct semantic
proof). -/
theorem hvalid_singleton {C₁ C₂ : AppCtx Symbol} {n : EVarIndex}
    {φ : Pattern Symbol} (m : M.Carrier) :
    hinterp M ρ (~(C₁.fill (.evar n ⊓ φ) ⊓ C₂.fill (.evar n ⊓ ~φ))) m = ⊤ := by
  change @HImp.himp L _ (@Min.min L _
    (hinterp M ρ (C₁.fill _) m) (hinterp M ρ (C₂.fill _) m)) ⊥ = ⊤
  rw [himp_eq_top_iff]
  apply le_trans (inf_le_inf (fill_le_iSup C₁ _ m) (fill_le_iSup C₂ _ m))
  rw [inf_iSup_eq]
  apply iSup_le; intro b
  rw [iSup_inf_eq]
  apply iSup_le; intro a
  -- `a` matches `x ∧ φ`, `b` matches `x ∧ ¬φ`: then `E a b` holds, so by
  -- extensionality `φ` transfers from `a` to `b`, contradicting `¬φ b`.
  simp only [Pattern.neg, hinterp_conj, hinterp_evar, hinterp_impl, hinterp_bot]
  -- goal: (E a x ⊓ φ a) ⊓ (E b x ⊓ (φ b ⇨ ⊥)) ≤ ⊥
  refine le_trans (le_inf ?_ (le_trans inf_le_right inf_le_right)) inf_himp_le
  -- goal: (E a x ⊓ φ a) ⊓ (E b x ⊓ (φ b ⇨ ⊥)) ≤ φ b
  refine le_trans (le_inf ?_ (le_trans inf_le_left inf_le_right)) (hinterp_ext φ ρ a b)
  -- goal: (E a x ⊓ φ a) ⊓ (E b x ⊓ (φ b ⇨ ⊥)) ≤ E a b
  exact le_trans (le_inf (le_trans inf_le_left inf_le_left) (le_trans inf_le_right inf_le_left))
    (M.E_trans_symm a b (ρ.evar n))

-- ─────────────────────────────────────────────────────────────
-- Quantifiers
-- ─────────────────────────────────────────────────────────────

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
  simp only [hinterp_exist]
  apply eq_top_iff.mpr
  refine le_iSup_of_le m ?_
  change ⊤ ≤ M.E m m
  rw [M.E_refl]

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
    {ρ₁ ρ₂ : HValuation M} (R : M.Carrier → L) (hR : M.Ext R)
    (hevar : ρ₁.evar = ρ₂.evar)
    (hsvar_eq : ∀ i, i ≠ n → ρ₁.svar i = ρ₂.svar i)
    (hsvar_le : ∀ m, ρ₁.svar n m ≤ ρ₂.svar n m) :
    (ρ₁.pushSVar R hR).evar = (ρ₂.pushSVar R hR).evar ∧
    (∀ i, i ≠ n + 1 → (ρ₁.pushSVar R hR).svar i = (ρ₂.pushSVar R hR).svar i) ∧
    (∀ m, (ρ₁.pushSVar R hR).svar (n + 1) m ≤ (ρ₂.pushSVar R hR).svar (n + 1) m) :=
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
    apply sInf_le_sInf; intro x ⟨R, hRe, hR, hx⟩
    let ⟨he, hs, hl⟩ := pushSVar_mono_args R hRe hevar hsvar_eq hsvar_le
    exact ⟨R, hRe, fun k => le_trans (hinterp_mono_pos hpφ _ _ he hs hl k) (hR k), hx⟩
  | .nu hpφ => by
    simp only [hinterp]
    apply sSup_le_sSup; intro x ⟨R, hRe, hR, hx⟩
    let ⟨he, hs, hl⟩ := pushSVar_mono_args R hRe hevar hsvar_eq hsvar_le
    exact ⟨R, hRe, fun k => le_trans (hR k) (hinterp_mono_pos hpφ _ _ he hs hl k), hx⟩

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
    apply sInf_le_sInf; intro x ⟨R, hRe, hR, hx⟩
    let ⟨he, hs, hl⟩ := pushSVar_mono_args R hRe hevar hsvar_eq hsvar_le
    exact ⟨R, hRe, fun k => le_trans (hinterp_mono_neg hnφ _ _ he hs hl k) (hR k), hx⟩
  | .nu hnφ => by
    simp only [hinterp]
    apply sSup_le_sSup; intro x ⟨R, hRe, hR, hx⟩
    let ⟨he, hs, hl⟩ := pushSVar_mono_args R hRe hevar hsvar_eq hsvar_le
    exact ⟨R, hRe, fun k => le_trans (hR k) (hinterp_mono_neg hnφ _ _ he hs hl k), hx⟩
end

-- ─────────────────────────────────────────────────────────────

theorem hvalid_preFixpoint {φ : Pattern Symbol}
    (hpos : SVarPositive φ 0) (m : M.Carrier) :
    hinterp M ρ (svarSubst 0 (μ φ) φ ⇒ μ φ) m = ⊤ := by
  simp only [hinterp]; rw [himp_eq_top_iff, hinterp_svarSubst]
  apply le_sInf; intro x ⟨S, hSe, hS, hx⟩; subst hx
  have hmu_le : ∀ k, hinterp M ρ (μ φ) k ≤ S k := fun k => by
    apply sInf_le; exact ⟨S, hSe, hS, rfl⟩
  exact le_trans
    (hinterp_mono_pos hpos (ρ.pushSVar (fun n => hinterp M ρ (μ φ) n) (hinterp_ext _ ρ))
      (ρ.pushSVar S hSe)
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
  have hpre : ∀ n, hinterp M (ρ.pushSVar (fun n => hinterp M ρ ψ n) (hinterp_ext ψ ρ)) φ n ≤
      hinterp M ρ ψ n := fun n => by
    have := h n; simp only [hinterp] at this
    exact himp_eq_top_iff.mp (by rw [hinterp_svarSubst] at this; exact this)
  apply sInf_le
  exact ⟨fun n => hinterp M ρ ψ n, hinterp_ext ψ ρ, hpre, rfl⟩

theorem hvalid_postFixpoint {φ : Pattern Symbol}
    (hpos : SVarPositive φ 0) (m : M.Carrier) :
    hinterp M ρ (ν φ ⇒ svarSubst 0 (ν φ) φ) m = ⊤ := by
  simp only [hinterp]; rw [himp_eq_top_iff, hinterp_svarSubst]
  apply sSup_le; intro x ⟨S, hSe, hS, hx⟩; subst hx
  have hnu_ge : ∀ k, S k ≤ hinterp M ρ (ν φ) k := fun k => by
    apply le_sSup; exact ⟨S, hSe, hS, rfl⟩
  exact le_trans (hS m)
    (hinterp_mono_pos hpos (ρ.pushSVar S hSe)
      (ρ.pushSVar (fun n => hinterp M ρ (ν φ) n) (hinterp_ext _ ρ))
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
      hinterp M (ρ.pushSVar (fun n => hinterp M ρ ψ n) (hinterp_ext ψ ρ)) φ n := fun n => by
    have := h n; simp only [hinterp] at this
    exact himp_eq_top_iff.mp (by rw [hinterp_svarSubst] at this; exact this)
  apply le_sSup
  exact ⟨fun n => hinterp M ρ ψ n, hinterp_ext ψ ρ, hpost, rfl⟩

-- ─────────────────────────────────────────────────────────────
-- Soundness theorem
-- ─────────────────────────────────────────────────────────────

theorem soundness {Γ : Set (Pattern Symbol)} {φ : Pattern Symbol}
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
    exact fun _ _ _ _ _ m => hvalid_preFixpoint hpos m
  | knasterTarski _ ih =>
    exact fun L _ M hΓ ρ m => hvalid_knasterTarski (ih L M hΓ ρ) m
  | postFixpoint hpos =>
    exact fun _ _ _ _ _ m => hvalid_postFixpoint hpos m
  | park _ ih =>
    exact fun L _ M hΓ ρ m => hvalid_park (ih L M hΓ ρ) m
  | singletonStrong =>
    exact fun _ _ _ _ _ m => hvalid_singletonStrong m
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
