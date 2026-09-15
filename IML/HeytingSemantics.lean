import IML.Proof
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.FixedPoints

/-!
# Heyting algebra semantics for iAML

Patterns are interpreted as `Carrier → L` (L-valued predicates) over a
Frame `L` (= complete Heyting algebra). This generalizes the classical
`Set M = M → Prop` by replacing `Prop` with `L`.

Equality on the carrier is itself `L`-valued: a model carries
`E : Carrier → Carrier → L` that is reflexive (`E a a = ⊤`), symmetric and
transitive. This is the "total elements" case of a Fourman–Scott Ω-set.
Element variables are interpreted through `E`:

    ⟦x⟧(m) = E m ρ(x)

so their truth value need not be `⊥` or `⊤`. The crisp case
`E a b = if a = b then ⊤ else ⊥` is recovered in `IML.CrispModels`.

Every predicate that arises as an interpretation is *extensional*:
`E a b ⊓ S a ≤ S b`. The model's symbol and application interpretations
are required to be extensional, set-variable valuations are extensional,
and `μ`/`ν` range over extensional pre- and post-fixpoints. Extensionality is
what makes SINGLETON sound (`hinterp_ext` in this file).

Application: `app(A, B)(m) = ⨆ a b, A(a) ⊓ B(b) ⊓ f(a,b,m)`
- NOT contractive: app(A,B) is not ≤ A
- Definedness is non-trivial
-/

namespace IML

-- ─────────────────────────────────────────────────────────────
-- Extensionality
-- ─────────────────────────────────────────────────────────────

/-- `S : Carrier → L` is extensional for the `L`-valued equality `E`
when `E a b ⊓ S a ≤ S b`. -/
def Extensional {Carrier : Type} {L : Type*} [Order.Frame L]
    (E : Carrier → Carrier → L) (S : Carrier → L) : Prop :=
  ∀ a b, E a b ⊓ S a ≤ S b

-- ─────────────────────────────────────────────────────────────
-- Model
-- ─────────────────────────────────────────────────────────────

structure HModel (Symbol : Type) (L : Type*) [Order.Frame L] where
  Carrier : Type
  /-- `L`-valued equality on the carrier. -/
  E : Carrier → Carrier → L
  E_refl : ∀ a, E a a = ⊤
  E_symm : ∀ a b, E a b = E b a
  E_trans : ∀ a b c, E a b ⊓ E b c ≤ E a c
  appInterp : Carrier → Carrier → Carrier → L
  symInterp : Symbol → Carrier → L
  symInterp_ext : ∀ s, Extensional E (symInterp s)
  appInterp_ext₁ : ∀ b c, Extensional E (fun a => appInterp a b c)
  appInterp_ext₂ : ∀ a c, Extensional E (fun b => appInterp a b c)
  appInterp_ext₃ : ∀ a b, Extensional E (appInterp a b)

namespace HModel
variable {Symbol : Type} {L : Type*} [Order.Frame L]

/-- Extensionality with respect to the model's equality. -/
abbrev Ext (M : HModel Symbol L) (S : M.Carrier → L) : Prop :=
  Extensional M.E S

theorem E_symm_trans (M : HModel Symbol L) (a b c : M.Carrier) :
    M.E a b ⊓ M.E a c ≤ M.E b c := by
  rw [M.E_symm a b]; exact M.E_trans b a c

theorem E_trans_symm (M : HModel Symbol L) (a b c : M.Carrier) :
    M.E a c ⊓ M.E b c ≤ M.E a b := by
  rw [M.E_symm b c]; exact M.E_trans a c b

theorem ext_bot (M : HModel Symbol L) : M.Ext (fun _ => ⊥) :=
  fun _ _ => inf_le_right

theorem ext_const (M : HModel Symbol L) (x : L) : M.Ext (fun _ => x) :=
  fun _ _ => inf_le_right

/-- The extensional hull of a predicate: the least extensional predicate
above it. It is the identity on extensional predicates (`hull_eq_of_ext`). -/
def hull (M : HModel Symbol L) (S : M.Carrier → L) : M.Carrier → L :=
  fun b => ⨆ a, M.E a b ⊓ S a

theorem le_hull (M : HModel Symbol L) (S : M.Carrier → L) : S ≤ M.hull S := by
  intro b
  exact le_iSup_of_le b (by rw [M.E_refl, top_inf_eq])

theorem hull_ext (M : HModel Symbol L) (S : M.Carrier → L) : M.Ext (M.hull S) := by
  intro b c
  simp only [hull]
  rw [inf_iSup_eq]
  apply iSup_mono; intro a
  rw [← inf_assoc, inf_comm (M.E b c)]
  exact inf_le_inf_right _ (M.E_trans a b c)

theorem hull_le_of_ext (M : HModel Symbol L) {S : M.Carrier → L} (hS : M.Ext S) :
    M.hull S ≤ S := by
  intro b
  exact iSup_le fun a => hS a b

theorem hull_eq_of_ext (M : HModel Symbol L) {S : M.Carrier → L} (hS : M.Ext S) :
    M.hull S = S :=
  le_antisymm (M.hull_le_of_ext hS) (M.le_hull S)

theorem hull_mono (M : HModel Symbol L) : Monotone M.hull := by
  intro S₁ S₂ h b
  exact iSup_mono fun a => inf_le_inf_left _ (h a)

end HModel

-- ─────────────────────────────────────────────────────────────
-- Valuation
-- ─────────────────────────────────────────────────────────────

structure HValuation {Symbol : Type} {L : Type*} [Order.Frame L]
    (M : HModel Symbol L) where
  evar : EVarIndex → M.Carrier
  svar : SVarIndex → M.Carrier → L
  svar_ext : ∀ i, M.Ext (svar i)

namespace HValuation
variable {Symbol : Type} {L : Type*} [Order.Frame L] {M : HModel Symbol L}

def pushEVar (ρ : HValuation M) (a : M.Carrier) : HValuation M where
  evar i := match i with | 0 => a | n + 1 => ρ.evar n
  svar := ρ.svar
  svar_ext := ρ.svar_ext

def pushSVar (ρ : HValuation M) (S : M.Carrier → L) (hS : M.Ext S) :
    HValuation M where
  evar := ρ.evar
  svar i := match i with | 0 => S | n + 1 => ρ.svar n
  svar_ext i := match i with | 0 => hS | n + 1 => ρ.svar_ext n

/-- Replacing the pushed predicate by an equal one (the extensionality
proof is transported along). -/
theorem pushSVar_congr (ρ : HValuation M) {S S' : M.Carrier → L} (h : S = S')
    (hS : M.Ext S) (hS' : M.Ext S') : ρ.pushSVar S hS = ρ.pushSVar S' hS' := by
  subst h; rfl

end HValuation

-- ─────────────────────────────────────────────────────────────
-- Interpretation: Pattern → Carrier → L
-- ─────────────────────────────────────────────────────────────

variable {Symbol : Type} {L : Type*} [Order.Frame L]

open Pattern in
def hinterp (M : HModel Symbol L) (ρ : HValuation M) :
    Pattern Symbol → M.Carrier → L
  | .evar i, m    => M.E m (ρ.evar i)
  | .svar i, m    => ρ.svar i m
  | .symbol s, m  => M.symInterp s m
  | .app φ ψ, m   =>
    ⨆ a, ⨆ b, hinterp M ρ φ a ⊓ hinterp M ρ ψ b ⊓ M.appInterp a b m
  | .bot, _        => ⊥
  | .impl φ ψ, m  => hinterp M ρ φ m ⇨ hinterp M ρ ψ m
  | .conj φ ψ, m  => hinterp M ρ φ m ⊓ hinterp M ρ ψ m
  | .disj φ ψ, m  => hinterp M ρ φ m ⊔ hinterp M ρ ψ m
  | .exist φ, m   => ⨆ a : M.Carrier, hinterp M (ρ.pushEVar a) φ m
  | .forallP φ, m => ⨅ a : M.Carrier, hinterp M (ρ.pushEVar a) φ m
  | .mu φ, m      =>
    sInf { x | ∃ S : M.Carrier → L, ∃ hS : M.Ext S,
      (∀ n, hinterp M (ρ.pushSVar S hS) φ n ≤ S n) ∧ x = S m }
  | .nu φ, m      =>
    sSup { x | ∃ S : M.Carrier → L, ∃ hS : M.Ext S,
      (∀ n, S n ≤ hinterp M (ρ.pushSVar S hS) φ n) ∧ x = S m }

-- ─────────────────────────────────────────────────────────────
-- Simp lemmas for hinterp (one layer at a time)
-- ─────────────────────────────────────────────────────────────

section hinterpSimp
variable {M : HModel Symbol L} {ρ : HValuation M}

open Pattern in
@[simp] theorem hinterp_evar (i : EVarIndex) (m : M.Carrier) :
    hinterp M ρ (.evar i) m = M.E m (ρ.evar i) := rfl

open Pattern in
@[simp] theorem hinterp_svar (i : SVarIndex) (m : M.Carrier) :
    hinterp M ρ (.svar i) m = ρ.svar i m := rfl

open Pattern in
@[simp] theorem hinterp_symbol (s : Symbol) (m : M.Carrier) :
    hinterp M ρ (.symbol s) m = M.symInterp s m := rfl

open Pattern in
@[simp] theorem hinterp_app (φ ψ : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (φ ⬝ ψ) m =
    ⨆ a, ⨆ b, hinterp M ρ φ a ⊓ hinterp M ρ ψ b ⊓ M.appInterp a b m := rfl

open Pattern in
@[simp] theorem hinterp_bot (m : M.Carrier) :
    hinterp M ρ (⊥ₘ : Pattern Symbol) m = ⊥ := rfl

open Pattern in
@[simp] theorem hinterp_impl (φ ψ : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (φ ⇒ ψ) m = hinterp M ρ φ m ⇨ hinterp M ρ ψ m := rfl

open Pattern in
@[simp] theorem hinterp_conj (φ ψ : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (φ ⊓ ψ) m = hinterp M ρ φ m ⊓ hinterp M ρ ψ m := rfl

open Pattern in
@[simp] theorem hinterp_disj (φ ψ : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (φ ⊔ ψ) m = hinterp M ρ φ m ⊔ hinterp M ρ ψ m := rfl

open Pattern in
@[simp] theorem hinterp_exist (φ : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (∃ₑ φ) m = ⨆ a : M.Carrier, hinterp M (ρ.pushEVar a) φ m := rfl

open Pattern in
@[simp] theorem hinterp_forall (φ : Pattern Symbol) (m : M.Carrier) :
    hinterp M ρ (∀ₑ φ) m = ⨅ a : M.Carrier, hinterp M (ρ.pushEVar a) φ m := rfl

end hinterpSimp

-- ─────────────────────────────────────────────────────────────
-- Key lemma: every interpretation is extensional
-- ─────────────────────────────────────────────────────────────

theorem hinterp_ext {M : HModel Symbol L} (φ : Pattern Symbol) (ρ : HValuation M) :
    M.Ext (hinterp M ρ φ) := by
  induction φ generalizing ρ with
  | evar i =>
    intro a b
    simp only [hinterp_evar]
    exact M.E_symm_trans a b _
  | svar i => exact ρ.svar_ext i
  | symbol s => exact M.symInterp_ext s
  | bot => intro a b; simp
  | app φ ψ ihφ ihψ =>
    intro a b
    simp only [hinterp_app]
    rw [inf_iSup_eq]; apply iSup_mono; intro x
    rw [inf_iSup_eq]; apply iSup_mono; intro y
    rw [inf_comm (M.E a b), inf_assoc]
    apply inf_le_inf_left
    rw [inf_comm]
    exact M.appInterp_ext₃ x y a b
  | impl φ ψ ihφ ihψ =>
    intro a b
    simp only [hinterp_impl]
    rw [le_himp_iff]
    have h₁ : M.E a b ⊓ hinterp M ρ φ b ≤ hinterp M ρ φ a := by
      rw [M.E_symm]; exact ihφ ρ b a
    calc M.E a b ⊓ (hinterp M ρ φ a ⇨ hinterp M ρ ψ a) ⊓ hinterp M ρ φ b
        ≤ M.E a b ⊓ ((hinterp M ρ φ a ⇨ hinterp M ρ ψ a) ⊓ (M.E a b ⊓ hinterp M ρ φ b)) :=
          le_inf (le_trans inf_le_left inf_le_left)
            (le_inf (le_trans inf_le_left inf_le_right)
              (le_inf (le_trans inf_le_left inf_le_left) inf_le_right))
      _ ≤ M.E a b ⊓ ((hinterp M ρ φ a ⇨ hinterp M ρ ψ a) ⊓ hinterp M ρ φ a) :=
          inf_le_inf_left _ (inf_le_inf_left _ h₁)
      _ ≤ M.E a b ⊓ hinterp M ρ ψ a := inf_le_inf_left _ himp_inf_le
      _ ≤ hinterp M ρ ψ b := ihψ ρ a b
  | conj φ ψ ihφ ihψ =>
    intro a b
    simp only [hinterp_conj]
    exact le_inf (le_trans (inf_le_inf_left _ inf_le_left) (ihφ ρ a b))
      (le_trans (inf_le_inf_left _ inf_le_right) (ihψ ρ a b))
  | disj φ ψ ihφ ihψ =>
    intro a b
    simp only [hinterp_disj]
    rw [inf_sup_left]
    exact sup_le_sup (ihφ ρ a b) (ihψ ρ a b)
  | exist φ ih =>
    intro a b
    simp only [hinterp_exist]
    rw [inf_iSup_eq]
    exact iSup_mono fun x => ih (ρ.pushEVar x) a b
  | forallP φ ih =>
    intro a b
    simp only [hinterp_forall]
    exact le_iInf fun x => le_trans (inf_le_inf_left _ (iInf_le _ x)) (ih (ρ.pushEVar x) a b)
  | mu φ _ =>
    intro a b
    simp only [hinterp]
    apply le_sInf
    rintro x ⟨S, hS, hpre, rfl⟩
    exact le_trans (inf_le_inf_left _ (sInf_le ⟨S, hS, hpre, rfl⟩)) (hS a b)
  | nu φ _ =>
    intro a b
    simp only [hinterp]
    rw [inf_sSup_eq]
    apply iSup₂_le
    rintro x ⟨S, hS, hpost, rfl⟩
    exact le_trans (hS a b) (le_sSup ⟨S, hS, hpost, rfl⟩)

-- Validity: ⟦φ⟧(m) = ⊤ for all m and ρ
def HValid (M : HModel Symbol L) (φ : Pattern Symbol) : Prop :=
  ∀ (ρ : HValuation M) (m : M.Carrier), hinterp M ρ φ m = ⊤

end IML
