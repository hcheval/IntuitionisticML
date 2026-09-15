import IML.SingletonAlt.GModel
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.FinCases

/-!
# Countermodels: the two non-derivability results

Both use `gsoundness` from `GModel.lean`: a `GModel` that validates every non-singleton rule
plus one singleton-shaped scheme but refutes an instance of another shows the latter is not
derivable from the former.

## Model A — `singletonAlt ⊬ singleton`, even classically

`L = Prop`, carrier `Fin 3 = {a, b, c}`, every application lands on `c`
(`appInterp _ _ m := m = c`), one symbol `s` denoting `{a}`, and admissible element-variable
denotations `{a}, {b}, {c}, {a, b}`. With `x ↦ {a, b}`:

* `C₁[x ⊓ s] ⊓ C₂[x ⊓ ~s]` at `c` is `{c} ∩ {c}`, nonempty — `singleton` fails.
* `singletonAlt` holds: every non-hole context has the shape `C[Y] = (Y ≠ ∅) ∧ k ∧ (m = c)`,
  and no admissible denotation contains `c` together with another element.

Since `L = Prop` is Boolean, the model also validates excluded middle and double-negation
elimination, so the result is classical: no amount of classical reasoning recovers
`singleton` from `singletonAlt`.

## Model B — `singleton ⊬ singletonAlt` intuitionistically

`L = ℕ∞` (a complete chain: `0 < 1 < ⋯ < ⊤`), one-point carrier, crisp evars, and the
twisted application `δ p = if p = ⊥ then ⊥ else ⊤` (double negation in a chain). With `s ↦ 1`:

* `singleton` holds: `δ p ⊓ ¬p = ⊥` and `p ⊓ δ(¬p) = ⊥` in a chain.
* `singletonAlt` fails at `C₁ = [_] ⬝ ⊤, C₂ = hole, φ = s`: the premise `δ(1) ⊓ ⊤ = ⊤` but the
  conclusion is `1`.

The classical derivation `alt_of_singleton_lem` shows exactly where this needs excluded
middle: `Prop`-valued models make `δ = ¬¬ = id`.
-/

namespace IML

open Pattern Crisp

-- ═════════════════════════════════════════════════════════════
-- Model A
-- ═════════════════════════════════════════════════════════════

namespace ModelA

/-- Admissible denotations: `{0}`, `{1}`, `{2}`, `{0, 1}`. -/
def admA : Set (Fin 3 → Prop) :=
  {fun m => m = 0, fun m => m = 1, fun m => m = 2, fun m => m = 0 ∨ m = 1}

abbrev MA : GModel Unit Prop where
  Carrier := Fin 3
  appInterp _ _ m := m = 2
  symInterp _ m := m = 0
  Adm := admA
  adm_cover m := by
    fin_cases m
    · exact ⟨fun m => m = 0, by simp [admA], by simp⟩
    · exact ⟨fun m => m = 1, by simp [admA], by simp⟩
    · exact ⟨fun m => m = 2, by simp [admA], by simp⟩
  δ := id
  δ_mono := monotone_id
  δ_sup _ _ := le_rfl
  δ_iSup _ := le_rfl

@[simp] theorem MA_δ (p : Prop) : MA.δ p = p := rfl
@[simp] theorem MA_app (a b m : Fin 3) : MA.appInterp a b m = (m = 2) := rfl
@[simp] theorem MA_sym (s : Unit) (m : Fin 3) : MA.symInterp s m = (m = 0) := rfl

/-- If an admissible denotation contains `2` it is `{2}`. -/
theorem admA_two {X : Fin 3 → Prop} (hX : X ∈ admA) (h2 : X 2) : ∀ a, X a → a = 2 := by
  simp only [admA, Set.mem_insert_iff, Set.mem_singleton_iff] at hX
  rcases hX with rfl | rfl | rfl | rfl
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · exact fun a h => h
  · exact absurd h2 (by decide)

theorem ginterp_app_iff (φ ψ : Pattern Unit) (ρ : GValuation MA) (m : Fin 3) :
    ginterp MA ρ (φ ⬝ ψ) m ↔
      (∃ a, ginterp MA ρ φ a) ∧ (∃ b, ginterp MA ρ ψ b) ∧ m = 2 := by
  simp only [ginterp_app, iSup_Prop_eq]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, hm⟩; exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hm⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, hm⟩; exact ⟨a, b, ⟨ha, hb⟩, hm⟩

/-- Every non-hole context has the shape "hole nonempty, some constant, and `m = 2`". -/
theorem shape (C : AppCtx Unit) (ρ : GValuation MA) :
    C = .hole ∨ ∃ k : Prop, ∀ (Y : Pattern Unit) (m : Fin 3),
      ginterp MA ρ (C.fill Y) m ↔ (∃ a, ginterp MA ρ Y a) ∧ k ∧ m = 2 := by
  induction C with
  | hole => exact Or.inl rfl
  | left C' ψ ih =>
    right
    rcases ih with rfl | ⟨k', hk'⟩
    · exact ⟨∃ b, ginterp MA ρ ψ b, fun Y m => ginterp_app_iff Y ψ ρ m⟩
    · refine ⟨k' ∧ ∃ b, ginterp MA ρ ψ b, fun Y m => ?_⟩
      rw [AppCtx.fill, ginterp_app_iff]
      simp only [hk']
      constructor
      · rintro ⟨⟨a, hY, hk, _⟩, hb, hm⟩; exact ⟨hY, ⟨hk, hb⟩, hm⟩
      · rintro ⟨hY, ⟨hk, hb⟩, hm⟩; exact ⟨⟨2, hY, hk, rfl⟩, hb, hm⟩
  | right ψ C' ih =>
    right
    rcases ih with rfl | ⟨k', hk'⟩
    · refine ⟨∃ b, ginterp MA ρ ψ b, fun Y m => ?_⟩
      rw [AppCtx.fill, ginterp_app_iff]
      constructor
      · rintro ⟨hb, hY, hm⟩; exact ⟨hY, hb, hm⟩
      · rintro ⟨hY, hb, hm⟩; exact ⟨hb, hY, hm⟩
    · refine ⟨k' ∧ ∃ b, ginterp MA ρ ψ b, fun Y m => ?_⟩
      rw [AppCtx.fill, ginterp_app_iff]
      simp only [hk']
      constructor
      · rintro ⟨hb, ⟨a, hY, hk, _⟩, hm⟩; exact ⟨hY, ⟨hk, hb⟩, hm⟩
      · rintro ⟨hY, ⟨hk, hb⟩, hm⟩; exact ⟨hb, ⟨2, hY, hk, rfl⟩, hm⟩

/-- **`singletonAlt` is valid in Model A.** -/
theorem valid_alt : ∀ i, GValid MA (singletonAltAx Unit i) := by
  rintro ⟨C₁, C₂, n, φ⟩ ρ hρ m
  simp only [singletonAltAx, ginterp_impl, ginterp_conj, Prop.top_eq_true]
  apply eq_true
  rw [himp_iff_imp]
  rintro ⟨h₁, h₂⟩
  rcases shape C₂ ρ with rfl | ⟨k₂, hk₂⟩
  · -- C₂ = hole
    simp only [AppCtx.fill, ginterp_conj, ginterp_evar] at h₂ ⊢
    rcases shape C₁ ρ with rfl | ⟨k₁, hk₁⟩
    · simpa only [AppCtx.fill, ginterp_conj, ginterp_evar] using h₁
    · obtain ⟨⟨a, ha, hφ⟩, _, rfl⟩ := (hk₁ _ m).mp h₁
      have := admA_two (hρ n) h₂ a ha
      subst this
      exact ⟨h₂, hφ⟩
  · -- C₂ non-hole
    rw [hk₂] at h₂ ⊢
    obtain ⟨_, hk, hm⟩ := h₂
    refine ⟨?_, hk, hm⟩
    rcases shape C₁ ρ with rfl | ⟨k₁, hk₁⟩
    · exact ⟨m, h₁⟩
    · exact ((hk₁ _ m).mp h₁).1

/-- Model A is Boolean, so excluded middle holds. -/
theorem valid_lem : ∀ φ, GValid MA (lemAx Unit φ) := by
  intro φ ρ _ m
  simp only [lemAx, ginterp_disj, Prop.top_eq_true]
  exact eq_true (Classical.em _)

theorem valid_dne : ∀ φ, GValid MA (dneAx Unit φ) := by
  intro φ ρ _ m
  simp only [dneAx, ginterp_impl, Prop.top_eq_true, himp_iff_imp]
  exact eq_true fun h => Classical.by_contradiction h

/-- The refuting valuation: `x ↦ {0, 1}`. -/
def ρ₀ : GValuation MA where
  evar _ := fun m => m = 0 ∨ m = 1
  svar _ := fun _ => False

theorem ρ₀_adm : ρ₀.IsAdm := fun _ => by simp [admA, ρ₀]

/-- The refuted instance: `C₁ = C₂ = [_] ⬝ ⊤, φ = s`. -/
def badInst : SingletonInst Unit := (.left .hole ⊤ₘ, .left .hole ⊤ₘ, 0, .symbol ())

theorem top_true (ρ : GValuation MA) (m : Fin 3) : ginterp MA ρ (⊤ₘ : Pattern Unit) m := by
  simp only [Pattern.top, Pattern.neg, ginterp_impl, ginterp_bot, Prop.bot_eq_false,
    himp_iff_imp]
  exact id

/-- **`singleton` fails in Model A** at the point `2`. -/
theorem refutes_singleton : ginterp MA ρ₀ (singletonAx Unit badInst) 2 ≠ ⊤ := by
  simp only [singletonAx, badInst, Pattern.neg, ginterp_impl, ginterp_conj, ginterp_bot,
    Prop.top_eq_true, Prop.bot_eq_false, himp_iff_imp, AppCtx.fill]
  intro h
  have h' := of_eq_true h
  apply h'
  constructor
  · rw [ginterp_app_iff]
    refine ⟨⟨0, ?_⟩, ⟨0, top_true ρ₀ 0⟩, rfl⟩
    simp [ρ₀]
  · rw [ginterp_app_iff]
    refine ⟨⟨1, ?_⟩, ⟨0, top_true ρ₀ 0⟩, rfl⟩
    simp [ρ₀]

end ModelA

/-- The classical scheme: `singletonAlt` together with excluded middle and double negation
elimination. -/
abbrev altClassicalAx : (SingletonInst Unit ⊕ (Pattern Unit ⊕ Pattern Unit)) → Pattern Unit :=
  axUnion (singletonAltAx Unit) (axUnion (lemAx Unit) (dneAx Unit))

theorem ModelA.valid_altClassical : ∀ i, GValid ModelA.MA (altClassicalAx i)
  | .inl i => ModelA.valid_alt i
  | .inr (.inl φ) => ModelA.valid_lem φ
  | .inr (.inr φ) => ModelA.valid_dne φ

/-- **Verdict on question 2: `singleton` is NOT derivable from `singletonAlt`, even with
excluded middle and double negation elimination.** (Semantic independence proof, Model A.) -/
theorem singleton_not_from_alt
    (h : ProofCore altClassicalAx ∅ (singletonAx Unit ModelA.badInst)) : False :=
  ModelA.refutes_singleton
    (gsoundness h Prop ModelA.MA ModelA.valid_altClassical (fun _ h => absurd h (by simp))
      ModelA.ρ₀ ModelA.ρ₀_adm 2)

/-- Hence `singletonStrong` is not derivable from `singletonAlt` either (it would give
`singleton` by `singleton_of_strong`), even classically. -/
theorem strong_not_from_alt (h : ProofCore.HasStrong altClassicalAx ∅) : False :=
  singleton_not_from_alt (ProofCore.singleton_of_strong h _ _ _ _)

-- ═════════════════════════════════════════════════════════════
-- Model B
-- ═════════════════════════════════════════════════════════════

namespace ModelB

/-- Double negation in the chain `ℕ∞`. -/
noncomputable def δB (p : ℕ∞) : ℕ∞ := if p = ⊥ then ⊥ else ⊤

theorem δB_bot : δB ⊥ = ⊥ := if_pos rfl

theorem δB_of_ne {p : ℕ∞} (h : p ≠ ⊥) : δB p = ⊤ := if_neg h

theorem δB_mono : Monotone δB := by
  intro p q hpq
  by_cases hp : p = ⊥
  · subst hp; rw [δB_bot]; exact bot_le
  · have hq : q ≠ ⊥ := fun hq => hp (le_bot_iff.mp (hq ▸ hpq))
    rw [δB_of_ne hp, δB_of_ne hq]

theorem δB_sup (p q : ℕ∞) : δB (max p q) ≤ max (δB p) (δB q) := by
  by_cases hp : p = ⊥
  · subst hp; rw [bot_sup_eq, δB_bot, bot_sup_eq]
  · rw [δB_of_ne (fun h => hp (sup_eq_bot_iff.mp h).1), δB_of_ne hp]; exact le_sup_left

theorem δB_iSup {ι : Type*} (f : ι → ℕ∞) : δB (⨆ i, f i) ≤ ⨆ i, δB (f i) := by
  by_cases h : (⨆ i, f i) = ⊥
  · rw [h, δB_bot]; exact bot_le
  · rw [iSup_eq_bot, not_forall] at h
    obtain ⟨i, hi⟩ := h
    apply le_iSup_of_le i
    rw [δB_of_ne hi]; exact le_top

theorem δB_inf (p q : ℕ∞) : δB (min p q) = min (δB p) (δB q) := by
  by_cases hp : p = ⊥
  · subst hp; rw [bot_inf_eq, δB_bot, bot_inf_eq]
  · by_cases hq : q = ⊥
    · subst hq; rw [inf_bot_eq, δB_bot, inf_bot_eq]
    · have : min p q ≠ ⊥ := fun h => by
        rcases min_eq_bot.mp h with h | h
        · exact hp h
        · exact hq h
      rw [δB_of_ne this, δB_of_ne hp, δB_of_ne hq, top_inf_eq]

theorem δB_δB (p : ℕ∞) : δB (δB p) = δB p := by
  by_cases hp : p = ⊥
  · subst hp; rw [δB_bot, δB_bot]
  · rw [δB_of_ne hp, δB_of_ne top_ne_bot]

/-- In a chain, a nonzero element has zero negation. -/
theorem himp_bot_of_ne {p : ℕ∞} (h : p ≠ ⊥) : p ⇨ ⊥ = ⊥ := by
  have := @himp_inf_le ℕ∞ _ p ⊥
  rw [le_bot_iff] at this
  rcases min_eq_bot.mp this with h1 | h1
  · exact h1
  · exact absurd h1 h

theorem δB_inf_neg (p : ℕ∞) : min (δB p) (p ⇨ ⊥) = ⊥ := by
  by_cases hp : p = ⊥
  · subst hp; rw [δB_bot, bot_inf_eq]
  · rw [himp_bot_of_ne hp, inf_bot_eq]

theorem inf_δB_neg (p : ℕ∞) : min p (δB (p ⇨ ⊥)) = ⊥ := by
  by_cases hp : p = ⊥
  · subst hp; rw [bot_inf_eq]
  · rw [himp_bot_of_ne hp, δB_bot, inf_bot_eq]

theorem δB_inf_δB_neg (p : ℕ∞) : min (δB p) (δB (p ⇨ ⊥)) = ⊥ := by
  by_cases hp : p = ⊥
  · subst hp; rw [δB_bot, bot_inf_eq]
  · rw [himp_bot_of_ne hp, δB_bot, inf_bot_eq]

noncomputable abbrev MB : GModel Unit ℕ∞ where
  Carrier := Unit
  appInterp _ _ _ := ⊤
  symInterp _ _ := 1
  Adm := {fun _ => ⊤}
  adm_cover _ := ⟨fun _ => ⊤, Set.mem_singleton _, rfl⟩
  δ := δB
  δ_mono := δB_mono
  δ_sup := δB_sup
  δ_iSup := fun f => δB_iSup f

@[simp] theorem MB_δ (p : ℕ∞) : MB.δ p = δB p := rfl
@[simp] theorem MB_app (a b m : Unit) : MB.appInterp a b m = ⊤ := rfl
@[simp] theorem MB_sym (s : Unit) (m : Unit) : MB.symInterp s m = 1 := rfl

theorem ginterp_app_eq (φ ψ : Pattern Unit) (ρ : GValuation MB) :
    ginterp MB ρ (φ ⬝ ψ) () = min (δB (ginterp MB ρ φ ())) (δB (ginterp MB ρ ψ ())) := by
  simp only [ginterp_app, inf_top_eq, iSup_unique]

/-- Every non-hole context has the shape `δ(hole) ⊓ k`. -/
theorem shape (C : AppCtx Unit) (ρ : GValuation MB) :
    C = .hole ∨ ∃ k : ℕ∞, ∀ Y : Pattern Unit,
      ginterp MB ρ (C.fill Y) () = min (δB (ginterp MB ρ Y ())) k := by
  induction C with
  | hole => exact Or.inl rfl
  | left C' ψ ih =>
    right
    rcases ih with rfl | ⟨k', hk'⟩
    · exact ⟨δB (ginterp MB ρ ψ ()), fun Y => ginterp_app_eq Y ψ ρ⟩
    · refine ⟨min (δB k') (δB (ginterp MB ρ ψ ())), fun Y => ?_⟩
      rw [AppCtx.fill, ginterp_app_eq, hk', δB_inf, δB_δB, inf_assoc]
  | right ψ C' ih =>
    right
    rcases ih with rfl | ⟨k', hk'⟩
    · exact ⟨δB (ginterp MB ρ ψ ()), fun Y => by
        simp only [AppCtx.fill]; rw [ginterp_app_eq, inf_comm]⟩
    · refine ⟨min (δB (ginterp MB ρ ψ ())) (δB k'), fun Y => ?_⟩
      rw [AppCtx.fill, ginterp_app_eq, hk', δB_inf, δB_δB, inf_left_comm]

theorem evar_top {ρ : GValuation MB} (hρ : ρ.IsAdm) (n : EVarIndex) :
    ρ.evar n = fun _ => ⊤ := Set.mem_singleton_iff.mp (hρ n)

/-- **`singleton` is valid in Model B.** -/
theorem valid_singleton : ∀ i, GValid MB (singletonAx Unit i) := by
  rintro ⟨C₁, C₂, n, φ⟩ ρ hρ m
  cases m
  simp only [singletonAx, Pattern.neg, ginterp_impl, ginterp_conj, ginterp_bot]
  rw [himp_eq_top_iff, le_bot_iff]
  have hx := evar_top hρ n
  rcases shape C₁ ρ with rfl | ⟨k₁, hk₁⟩ <;> rcases shape C₂ ρ with rfl | ⟨k₂, hk₂⟩
  · simp only [AppCtx.fill, ginterp_conj, ginterp_evar, ginterp_impl, ginterp_bot, hx,
      top_inf_eq]
    exact le_bot_iff.mp inf_himp_le
  · rw [hk₂]
    simp only [AppCtx.fill, ginterp_conj, ginterp_evar, ginterp_impl, ginterp_bot, hx,
      top_inf_eq]
    exact le_bot_iff.mp (le_trans (inf_le_inf_left _ inf_le_left)
      (le_of_eq (inf_δB_neg _)))
  · rw [hk₁]
    simp only [AppCtx.fill, ginterp_conj, ginterp_evar, ginterp_impl, ginterp_bot, hx,
      top_inf_eq]
    exact le_bot_iff.mp (le_trans (inf_le_inf_right _ inf_le_left)
      (le_of_eq (δB_inf_neg _)))
  · rw [hk₁, hk₂]
    simp only [ginterp_conj, ginterp_evar, ginterp_impl, ginterp_bot, hx, top_inf_eq]
    exact le_bot_iff.mp (le_trans (inf_le_inf inf_le_left inf_le_left)
      (le_of_eq (δB_inf_δB_neg _)))

/-- The refuting valuation: crisp `x ↦ {()}`. -/
noncomputable def ρ₁ : GValuation MB where
  evar _ := fun _ => ⊤
  svar _ := fun _ => ⊥

theorem ρ₁_adm : ρ₁.IsAdm := fun _ => Set.mem_singleton _

/-- The refuted instance: `C₁ = [_] ⬝ ⊤, C₂ = hole, φ = s`. -/
def badInst : SingletonInst Unit := (.left .hole ⊤ₘ, .hole, 0, .symbol ())

theorem one_ne_bot : (1 : ℕ∞) ≠ ⊥ := by decide

theorem one_ne_top : (1 : ℕ∞) ≠ ⊤ := by decide

/-- **`singletonAlt` fails in Model B**: its value is `1`, not `⊤`. -/
theorem refutes_alt : ginterp MB ρ₁ (singletonAltAx Unit badInst) () ≠ ⊤ := by
  simp only [singletonAltAx, badInst, AppCtx.fill, ginterp_impl, ginterp_conj]
  rw [ginterp_app_eq]
  simp only [ginterp_conj, ginterp_evar, ginterp_symbol, ρ₁, top_inf_eq, Pattern.top,
    Pattern.neg, ginterp_impl, ginterp_bot, himp_self, δB_of_ne one_ne_bot, δB_of_ne top_ne_bot,
    inf_top_eq, top_himp]
  exact one_ne_top

end ModelB

/-- **Verdict on question 3: `singletonAlt` is NOT derivable from `singleton` in iML.**
(Semantic independence proof, Model B.) Together with `alt_of_singleton_lem`, this is
exactly the classical/intuitionistic split: the derivation exists iff excluded middle is
available. -/
theorem alt_not_from_singleton
    (h : ProofCore (singletonAx Unit) ∅ (singletonAltAx Unit ModelB.badInst)) : False :=
  ModelB.refutes_alt
    (gsoundness h ℕ∞ ModelB.MB ModelB.valid_singleton (fun _ h => absurd h (by simp))
      ModelB.ρ₁ ModelB.ρ₁_adm ())

/-- Hence `singletonStrong` is not derivable from `singleton` intuitionistically either. -/
theorem strong_not_from_singleton (h : ProofCore.HasStrong (singletonAx Unit) ∅) : False :=
  alt_not_from_singleton (ProofCore.alt_of_strong h _ _ _ _)

end IML
