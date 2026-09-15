import IML.DerivedRules.Definedness
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.ENat.Lattice

/-!
# The top-filter model: a non-standard semantics separating iML from its Heyting semantics

All 27 rules of `IML.Proof` are sound for the following *non-standard*
interpretation, which is therefore a tool for **underivability** proofs:

* patterns take values in a frame `L` (one-point carrier, so element
  variables are `⊤` and both quantifiers are the identity);
* application is interpreted *Boolean-ly*: `φ ⬝ ψ ↦ j (φ ⊓ ψ)` where
  `j u = ⊤` if `u = ⊤` and `⊥` otherwise. `j` is monotone, preserves `⊥`,
  and — when `⊤` is join-prime in `L`, e.g. `L` a chain — preserves binary
  joins, which is exactly what FRAMING, PROPAGATION∨/∃ and (via
  two-valuedness) SINGLETON need.

Because `j` does not commute with Heyting negation (`j (~~u) = ⊤` but
`~~(j u) = ⊥` for `⊥ < u < ⊤`), the model refutes several statements that
*are* valid in the standard Heyting semantics of `IML.HeytingSemantics`.
By `TopFilter.soundness` those statements are underivable, and by the
standard soundness theorem they are consistent: the iML proof system is
**incomplete** for its Heyting semantics. Concretely (`L := ℕ∞`, `u := 1`):

* `nnPropagation_not_derivable`: `C[~~φ] ⇒ ~~C[φ]` is not derivable
  (this is the missing ingredient in the modal (K) rule for `~C[~·]`,
  in `◦φ ⊓ ◦ψ ⇒ ◦(φ ⊓ ψ)`, and in `~⋄~φ ⇒ □~~φ`).
* `dne_not_derivable`: `~~φ ⇒ φ` (axiom p3) is not derivable.
* `phi_impl_ceil_not_derivable`: with the definedness axiom `∀x.⌈x⌉`,
  `φ ⇒ ⌈φ⌉` (thesis Lemma 3.14 / Corollary 3.1) is not derivable.
* `memNegIntro_not_derivable`: with definedness, Membership¬(←)
  `~(x ∈ φ) ⇒ x ∈ ~φ` is not derivable.
* `memEM_not_derivable`: the membership excluded middle
  `⌈x⌉ ⇒ ⌈x ⊓ φ⌉ ⊔ ⌈x ⊓ ~φ⌉` (the classical step behind all of §3.2) is
  not derivable.

This file does not `open Pattern`: the lattice connectives of `L` and the
pattern connectives share notation, and the low-precedence pattern
notation would otherwise capture `u ⊔ v = ⊤`.
-/

namespace IML.TopFilter

variable {Symbol : Type} {L : Type*} [Order.Frame L]

-- ─────────────────────────────────────────────────────────────
-- The point `j`
-- ─────────────────────────────────────────────────────────────

open Classical in
/-- `j u = ⊤` iff `u = ⊤`, else `⊥`. -/
noncomputable def j (u : L) : L := if u = ⊤ then ⊤ else ⊥

@[simp] theorem j_top : j (⊤ : L) = ⊤ := by simp [j]

theorem j_of_ne_top {u : L} (h : u ≠ ⊤) : j u = ⊥ := by simp [j, h]

theorem j_cases (u : L) : j u = ⊥ ∨ j u = ⊤ := by
  unfold j; split_ifs <;> simp

theorem j_eq_top_iff [Nontrivial L] {u : L} : j u = ⊤ ↔ u = ⊤ := by
  unfold j; split_ifs with h <;> simp [h, bot_ne_top]

theorem j_mono {u v : L} (h : u ≤ v) : j u ≤ j v := by
  unfold j; split_ifs with hu hv
  · exact le_rfl
  · exact absurd (top_le_iff.mp (hu ▸ h)) hv
  · exact bot_le
  · exact le_rfl

theorem j_sup_le (hprime : ∀ u v : L, u ⊔ v = ⊤ → u = ⊤ ∨ v = ⊤) (u v : L) :
    j (u ⊔ v) ≤ j u ⊔ j v := by
  by_cases h : u ⊔ v = ⊤
  · rcases hprime u v h with hu | hv
    · rw [h, j_top, hu, j_top]; exact le_sup_left
    · rw [h, j_top, hv, j_top]; exact le_sup_right
  · rw [j_of_ne_top h]; exact bot_le

-- ─────────────────────────────────────────────────────────────
-- Models, valuations, interpretation
-- ─────────────────────────────────────────────────────────────

structure TModel (Symbol : Type) (L : Type*) [Order.Frame L] where
  symInterp : Symbol → L
  top_prime : ∀ u v : L, u ⊔ v = ⊤ → u = ⊤ ∨ v = ⊤

/-- Set-variable valuations (element variables need no valuation). -/
abbrev SVal (L : Type*) := Nat → L

def SVal.insert (ρ : SVal L) (n : Nat) (S : L) : SVal L :=
  fun i => if i < n then ρ i else if i = n then S else ρ (i - 1)

def SVal.push (ρ : SVal L) (S : L) : SVal L := ρ.insert 0 S

omit [Order.Frame L] in
theorem SVal.push_zero (ρ : SVal L) (S : L) : ρ.push S 0 = S := by
  simp [SVal.push, SVal.insert]

omit [Order.Frame L] in
theorem SVal.push_succ (ρ : SVal L) (S : L) (i : Nat) : ρ.push S (i + 1) = ρ i := by
  simp [SVal.push, SVal.insert]

omit [Order.Frame L] in
theorem SVal.insert_push (ρ : SVal L) (n : Nat) (S T : L) :
    (ρ.insert n S).push T = (ρ.push T).insert (n + 1) S := by
  funext i
  cases i with
  | zero => simp [SVal.push, SVal.insert]
  | succ i =>
    rw [SVal.push_succ]
    change (if i < n then ρ i else if i = n then S else ρ (i - 1)) =
      (if i + 1 < n + 1 then ρ.push T (i + 1) else
        if i + 1 = n + 1 then S else ρ.push T (i + 1 - 1))
    by_cases h₁ : i < n
    · rw [if_pos h₁, if_pos (show i + 1 < n + 1 by omega), SVal.push_succ]
    · rw [if_neg h₁, if_neg (show ¬ i + 1 < n + 1 by omega)]
      by_cases h₂ : i = n
      · rw [if_pos h₂, if_pos (show i + 1 = n + 1 by omega)]
      · rw [if_neg h₂, if_neg (show ¬ i + 1 = n + 1 by omega), Nat.add_sub_cancel]
        obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        rw [SVal.push_succ, Nat.add_sub_cancel]

noncomputable def tinterp (M : TModel Symbol L) (ρ : SVal L) : Pattern Symbol → L
  | .evar _ => ⊤
  | .svar i => ρ i
  | .symbol s => M.symInterp s
  | .app φ ψ => j (tinterp M ρ φ ⊓ tinterp M ρ ψ)
  | .bot => ⊥
  | .impl φ ψ => tinterp M ρ φ ⇨ tinterp M ρ ψ
  | .conj φ ψ => tinterp M ρ φ ⊓ tinterp M ρ ψ
  | .disj φ ψ => tinterp M ρ φ ⊔ tinterp M ρ ψ
  | .exist φ => tinterp M ρ φ
  | .forallP φ => tinterp M ρ φ
  | .mu φ => sInf {S | tinterp M (ρ.push S) φ ≤ S}
  | .nu φ => sSup {S | S ≤ tinterp M (ρ.push S) φ}

def TValid (M : TModel Symbol L) (φ : Pattern Symbol) : Prop := ∀ ρ, tinterp M ρ φ = ⊤

variable {M : TModel Symbol L}

theorem tinterp_impl_eq_top {ρ : SVal L} {φ ψ : Pattern Symbol} :
    tinterp M ρ (.impl φ ψ) = ⊤ ↔ tinterp M ρ φ ≤ tinterp M ρ ψ := by
  simp only [tinterp]; exact himp_eq_top_iff

-- ─────────────────────────────────────────────────────────────
-- Substitution lemmas
-- ─────────────────────────────────────────────────────────────

theorem tinterp_evarLiftFrom (φ : Pattern Symbol) :
    ∀ (ρ : SVal L) (c : Nat), tinterp M ρ (evarLiftFrom c φ) = tinterp M ρ φ := by
  induction φ <;> intro ρ c <;> simp [evarLiftFrom, tinterp, *]

theorem tinterp_evarLift (φ : Pattern Symbol) (ρ : SVal L) :
    tinterp M ρ (evarLift φ) = tinterp M ρ φ :=
  tinterp_evarLiftFrom φ ρ 0

theorem tinterp_evarSubst (φ : Pattern Symbol) :
    ∀ (ρ : SVal L) (n : Nat) (ψ : Pattern Symbol), (∀ ρ', tinterp M ρ' ψ = ⊤) →
      tinterp M ρ (evarSubst n ψ φ) = tinterp M ρ φ := by
  induction φ with
  | evar i =>
    intro ρ n ψ hψ
    simp only [evarSubst, tinterp]
    split_ifs <;> simp [tinterp, hψ]
  | svar i => intro ρ n ψ hψ; rfl
  | symbol s => intro ρ n ψ hψ; rfl
  | bot => intro ρ n ψ hψ; rfl
  | app _ _ ih₁ ih₂ =>
    intro ρ n ψ hψ; simp only [evarSubst, tinterp, ih₁ ρ n ψ hψ, ih₂ ρ n ψ hψ]
  | impl _ _ ih₁ ih₂ =>
    intro ρ n ψ hψ; simp only [evarSubst, tinterp, ih₁ ρ n ψ hψ, ih₂ ρ n ψ hψ]
  | conj _ _ ih₁ ih₂ =>
    intro ρ n ψ hψ; simp only [evarSubst, tinterp, ih₁ ρ n ψ hψ, ih₂ ρ n ψ hψ]
  | disj _ _ ih₁ ih₂ =>
    intro ρ n ψ hψ; simp only [evarSubst, tinterp, ih₁ ρ n ψ hψ, ih₂ ρ n ψ hψ]
  | exist _ ih =>
    intro ρ n ψ hψ
    simp only [evarSubst, tinterp]
    exact ih ρ (n + 1) (evarLift ψ) (fun ρ' => by rw [tinterp_evarLift]; exact hψ ρ')
  | forallP _ ih =>
    intro ρ n ψ hψ
    simp only [evarSubst, tinterp]
    exact ih ρ (n + 1) (evarLift ψ) (fun ρ' => by rw [tinterp_evarLift]; exact hψ ρ')
  | mu _ ih =>
    intro ρ n ψ hψ
    simp only [evarSubst, tinterp]
    congr 1; ext S; simp only [Set.mem_setOf_eq, ih _ n ψ hψ]
  | nu _ ih =>
    intro ρ n ψ hψ
    simp only [evarSubst, tinterp]
    congr 1; ext S; simp only [Set.mem_setOf_eq, ih _ n ψ hψ]

theorem tinterp_svarLiftFrom (φ : Pattern Symbol) :
    ∀ (ρ : SVal L) (c : Nat) (S : L),
      tinterp M (ρ.insert c S) (svarLiftFrom c φ) = tinterp M ρ φ := by
  induction φ with
  | evar i => intro ρ c S; rfl
  | svar i =>
    intro ρ c S
    simp only [svarLiftFrom, tinterp, SVal.insert]
    unfold SVarIndex at *
    by_cases h : i ≥ c
    · rw [if_pos h, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
    · rw [if_neg h, if_pos (by omega)]
  | symbol s => intro ρ c S; rfl
  | bot => intro ρ c S; rfl
  | app _ _ ih₁ ih₂ => intro ρ c S; simp only [svarLiftFrom, tinterp, ih₁, ih₂]
  | impl _ _ ih₁ ih₂ => intro ρ c S; simp only [svarLiftFrom, tinterp, ih₁, ih₂]
  | conj _ _ ih₁ ih₂ => intro ρ c S; simp only [svarLiftFrom, tinterp, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => intro ρ c S; simp only [svarLiftFrom, tinterp, ih₁, ih₂]
  | exist _ ih => intro ρ c S; simp only [svarLiftFrom, tinterp, ih]
  | forallP _ ih => intro ρ c S; simp only [svarLiftFrom, tinterp, ih]
  | mu _ ih =>
    intro ρ c S
    simp only [svarLiftFrom, tinterp]
    congr 1; ext T; simp only [Set.mem_setOf_eq, SVal.insert_push, ih]
  | nu _ ih =>
    intro ρ c S
    simp only [svarLiftFrom, tinterp]
    congr 1; ext T; simp only [Set.mem_setOf_eq, SVal.insert_push, ih]

theorem tinterp_svarLift (φ : Pattern Symbol) (ρ : SVal L) (S : L) :
    tinterp M (ρ.push S) (svarLift φ) = tinterp M ρ φ :=
  tinterp_svarLiftFrom φ ρ 0 S

theorem tinterp_svarSubst (φ : Pattern Symbol) :
    ∀ (ρ : SVal L) (n : Nat) (ψ : Pattern Symbol),
      tinterp M ρ (svarSubst n ψ φ) = tinterp M (ρ.insert n (tinterp M ρ ψ)) φ := by
  induction φ with
  | evar i => intro ρ n ψ; rfl
  | svar i =>
    intro ρ n ψ
    unfold SVarIndex at *
    by_cases h₁ : i = n
    · subst h₁; simp [svarSubst, tinterp, SVal.insert]
    · have hb : (i == n) = false := by simpa using h₁
      by_cases h₂ : n < i
      · have h₃ : ¬ i < n := by omega
        simp [svarSubst, tinterp, SVal.insert, hb, h₂, h₁, h₃]
      · have h₃ : i < n := by omega
        simp [svarSubst, tinterp, SVal.insert, hb, h₂, h₃]
  | symbol s => intro ρ n ψ; rfl
  | bot => intro ρ n ψ; rfl
  | app _ _ ih₁ ih₂ => intro ρ n ψ; simp only [svarSubst, tinterp, ih₁, ih₂]
  | impl _ _ ih₁ ih₂ => intro ρ n ψ; simp only [svarSubst, tinterp, ih₁, ih₂]
  | conj _ _ ih₁ ih₂ => intro ρ n ψ; simp only [svarSubst, tinterp, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => intro ρ n ψ; simp only [svarSubst, tinterp, ih₁, ih₂]
  | exist _ ih =>
    intro ρ n ψ
    simp only [svarSubst, tinterp]
    rw [ih, tinterp_evarLift]
  | forallP _ ih =>
    intro ρ n ψ
    simp only [svarSubst, tinterp]
    rw [ih, tinterp_evarLift]
  | mu _ ih =>
    intro ρ n ψ
    simp only [svarSubst, tinterp]
    congr 1; ext S
    simp only [Set.mem_setOf_eq, ih, tinterp_svarLift, SVal.insert_push]
  | nu _ ih =>
    intro ρ n ψ
    simp only [svarSubst, tinterp]
    congr 1; ext S
    simp only [Set.mem_setOf_eq, ih, tinterp_svarLift, SVal.insert_push]

theorem tinterp_svarSubst_zero (φ ψ : Pattern Symbol) (ρ : SVal L) :
    tinterp M ρ (svarSubst 0 ψ φ) = tinterp M (ρ.push (tinterp M ρ ψ)) φ :=
  tinterp_svarSubst φ ρ 0 ψ

-- ─────────────────────────────────────────────────────────────
-- Monotonicity from positivity
-- ─────────────────────────────────────────────────────────────

private theorem push_mono_args {n : Nat} {ρ₁ ρ₂ : SVal L} (S : L)
    (heq : ∀ i, i ≠ n → ρ₁ i = ρ₂ i) (hle : ρ₁ n ≤ ρ₂ n) :
    (∀ i, i ≠ n + 1 → ρ₁.push S i = ρ₂.push S i) ∧ ρ₁.push S (n + 1) ≤ ρ₂.push S (n + 1) := by
  refine ⟨fun i hi => ?_, ?_⟩
  · cases i with
    | zero => rw [SVal.push_zero, SVal.push_zero]
    | succ i =>
      rw [SVal.push_succ, SVal.push_succ]
      exact heq i (fun h => hi (by rw [h]))
  · rw [SVal.push_succ, SVal.push_succ]; exact hle

mutual
theorem tinterp_mono_pos {φ : Pattern Symbol} {n : Nat}
    (hpos : SVarPositive φ n) (ρ₁ ρ₂ : SVal L)
    (heq : ∀ i, i ≠ n → ρ₁ i = ρ₂ i) (hle : ρ₁ n ≤ ρ₂ n) :
    tinterp M ρ₁ φ ≤ tinterp M ρ₂ φ :=
  match hpos with
  | .evar => le_rfl
  | .svar => hle
  | .svarNe hne => by simp only [tinterp]; rw [heq _ hne]
  | .symbol => le_rfl
  | .bot => le_rfl
  | .app hpφ hpψ => by
    simp only [tinterp]
    exact j_mono (inf_le_inf (tinterp_mono_pos hpφ ρ₁ ρ₂ heq hle)
                             (tinterp_mono_pos hpψ ρ₁ ρ₂ heq hle))
  | .impl hnφ hpψ => by
    simp only [tinterp]
    exact himp_le_himp (tinterp_mono_neg hnφ ρ₁ ρ₂ heq hle) (tinterp_mono_pos hpψ ρ₁ ρ₂ heq hle)
  | .conj hpφ hpψ => by
    simp only [tinterp]
    exact inf_le_inf (tinterp_mono_pos hpφ ρ₁ ρ₂ heq hle) (tinterp_mono_pos hpψ ρ₁ ρ₂ heq hle)
  | .disj hpφ hpψ => by
    simp only [tinterp]
    exact sup_le_sup (tinterp_mono_pos hpφ ρ₁ ρ₂ heq hle) (tinterp_mono_pos hpψ ρ₁ ρ₂ heq hle)
  | .exist hpφ => by simp only [tinterp]; exact tinterp_mono_pos hpφ ρ₁ ρ₂ heq hle
  | .forallP hpφ => by simp only [tinterp]; exact tinterp_mono_pos hpφ ρ₁ ρ₂ heq hle
  | .mu hpφ => by
    simp only [tinterp]
    apply sInf_le_sInf; intro S hS
    obtain ⟨he, hl⟩ := push_mono_args S heq hle
    exact le_trans (tinterp_mono_pos hpφ _ _ he hl) hS
  | .nu hpφ => by
    simp only [tinterp]
    apply sSup_le_sSup; intro S hS
    obtain ⟨he, hl⟩ := push_mono_args S heq hle
    exact le_trans hS (tinterp_mono_pos hpφ _ _ he hl)

theorem tinterp_mono_neg {φ : Pattern Symbol} {n : Nat}
    (hneg : SVarNegative φ n) (ρ₁ ρ₂ : SVal L)
    (heq : ∀ i, i ≠ n → ρ₁ i = ρ₂ i) (hle : ρ₁ n ≤ ρ₂ n) :
    tinterp M ρ₂ φ ≤ tinterp M ρ₁ φ :=
  match hneg with
  | .evar => le_rfl
  | .svarNe hne => by simp only [tinterp]; rw [heq _ hne]
  | .symbol => le_rfl
  | .bot => le_rfl
  | .app hnφ hnψ => by
    simp only [tinterp]
    exact j_mono (inf_le_inf (tinterp_mono_neg hnφ ρ₁ ρ₂ heq hle)
                             (tinterp_mono_neg hnψ ρ₁ ρ₂ heq hle))
  | .impl hpφ hnψ => by
    simp only [tinterp]
    exact himp_le_himp (tinterp_mono_pos hpφ ρ₁ ρ₂ heq hle) (tinterp_mono_neg hnψ ρ₁ ρ₂ heq hle)
  | .conj hnφ hnψ => by
    simp only [tinterp]
    exact inf_le_inf (tinterp_mono_neg hnφ ρ₁ ρ₂ heq hle) (tinterp_mono_neg hnψ ρ₁ ρ₂ heq hle)
  | .disj hnφ hnψ => by
    simp only [tinterp]
    exact sup_le_sup (tinterp_mono_neg hnφ ρ₁ ρ₂ heq hle) (tinterp_mono_neg hnψ ρ₁ ρ₂ heq hle)
  | .exist hnφ => by simp only [tinterp]; exact tinterp_mono_neg hnφ ρ₁ ρ₂ heq hle
  | .forallP hnφ => by simp only [tinterp]; exact tinterp_mono_neg hnφ ρ₁ ρ₂ heq hle
  | .mu hnφ => by
    simp only [tinterp]
    apply sInf_le_sInf; intro S hS
    obtain ⟨he, hl⟩ := push_mono_args S heq hle
    exact le_trans (tinterp_mono_neg hnφ _ _ he hl) hS
  | .nu hnφ => by
    simp only [tinterp]
    apply sSup_le_sSup; intro S hS
    obtain ⟨he, hl⟩ := push_mono_args S heq hle
    exact le_trans hS (tinterp_mono_neg hnφ _ _ he hl)
end

private theorem push_args_zero (ρ : SVal L) (S T : L) (h : S ≤ T) :
    (∀ i, i ≠ 0 → ρ.push S i = ρ.push T i) ∧ ρ.push S 0 ≤ ρ.push T 0 := by
  refine ⟨fun i hi => ?_, ?_⟩
  · cases i with
    | zero => exact absurd rfl hi
    | succ i => rw [SVal.push_succ, SVal.push_succ]
  · rw [SVal.push_zero, SVal.push_zero]; exact h

-- ─────────────────────────────────────────────────────────────
-- Application contexts are two-valued
-- ─────────────────────────────────────────────────────────────

theorem fill_top [Nontrivial L] (C : AppCtx Symbol) (X : Pattern Symbol) (ρ : SVal L) :
    tinterp M ρ (C.fill X) = ⊤ → tinterp M ρ X = ⊤ := by
  induction C with
  | hole => exact id
  | left C' ψ ih =>
    intro h
    simp only [AppCtx.fill, tinterp] at h
    exact ih (inf_eq_top_iff.mp (j_eq_top_iff.mp h)).1
  | right ψ C' ih =>
    intro h
    simp only [AppCtx.fill, tinterp] at h
    exact ih (inf_eq_top_iff.mp (j_eq_top_iff.mp h)).2

theorem fill_cases (C : AppCtx Symbol) (ρ : SVal L) :
    C = .hole ∨ ∀ X, tinterp M ρ (C.fill X) = ⊥ ∨ tinterp M ρ (C.fill X) = ⊤ := by
  cases C with
  | hole => exact Or.inl rfl
  | left C' ψ => exact Or.inr fun X => by simp only [AppCtx.fill, tinterp]; exact j_cases _
  | right ψ C' => exact Or.inr fun X => by simp only [AppCtx.fill, tinterp]; exact j_cases _

-- ─────────────────────────────────────────────────────────────
-- Soundness of the 27 rules
-- ─────────────────────────────────────────────────────────────

theorem tvalid_singleton [Nontrivial L] {C₁ C₂ : AppCtx Symbol} {n : EVarIndex}
    {φ : Pattern Symbol} (ρ : SVal L) :
    tinterp M ρ (Pattern.neg (Pattern.conj (C₁.fill (Pattern.conj (.evar n) φ))
      (C₂.fill (Pattern.conj (.evar n) (Pattern.neg φ))))) = ⊤ := by
  change tinterp M ρ (Pattern.impl (Pattern.conj (C₁.fill (Pattern.conj (.evar n) φ))
      (C₂.fill (Pattern.conj (.evar n) (Pattern.neg φ)))) Pattern.bot) = ⊤
  rw [tinterp_impl_eq_top]
  simp only [tinterp]
  have hx : tinterp M ρ (Pattern.conj (.evar n) φ) = tinterp M ρ φ := by simp [tinterp]
  have hnx : tinterp M ρ (Pattern.conj (.evar n) (Pattern.neg φ)) = tinterp M ρ φ ⇨ ⊥ := by
    simp [tinterp, Pattern.neg]
  rcases fill_cases (M := M) C₁ ρ with rfl | h₁ <;> rcases fill_cases (M := M) C₂ ρ with rfl | h₂
  · simp only [AppCtx.fill]; rw [hx, hnx]; exact inf_himp_le
  · rcases h₂ (Pattern.conj (.evar n) (Pattern.neg φ)) with hb | hb
    · rw [hb]; exact inf_le_right
    · have := fill_top C₂ _ ρ hb; rw [hnx] at this
      simp only [AppCtx.fill]; rw [hx]
      exact le_trans inf_le_left (himp_eq_top_iff.mp this)
  · rcases h₁ (Pattern.conj (.evar n) φ) with ha | ha
    · rw [ha]; exact inf_le_left
    · have := fill_top C₁ _ ρ ha; rw [hx] at this
      simp only [AppCtx.fill]; rw [hnx, this, top_himp]; exact inf_le_right
  · rcases h₁ (Pattern.conj (.evar n) φ) with ha | ha
    · rw [ha]; exact inf_le_left
    · rcases h₂ (Pattern.conj (.evar n) (Pattern.neg φ)) with hb | hb
      · rw [hb]; exact inf_le_right
      · have h₁' := fill_top C₁ _ ρ ha; rw [hx] at h₁'
        have h₂' := fill_top C₂ _ ρ hb; rw [hnx, h₁', top_himp] at h₂'
        exact absurd h₂' bot_ne_top

theorem soundness [Nontrivial L] {Γ : Set (Pattern Symbol)} {φ : Pattern Symbol}
    (h : Γ ⊩ᵢ φ) (M : TModel Symbol L) (hΓ : ∀ γ ∈ Γ, TValid M γ) : TValid M φ := by
  induction h with
  | assumption hmem => exact hΓ _ hmem
  | contractionOr =>
    intro ρ; rw [tinterp_impl_eq_top]; simp only [tinterp]; exact sup_le le_rfl le_rfl
  | contractionAnd =>
    intro ρ; rw [tinterp_impl_eq_top]; simp only [tinterp]; exact le_inf le_rfl le_rfl
  | weakeningOr => intro ρ; rw [tinterp_impl_eq_top]; simp only [tinterp]; exact le_sup_left
  | weakeningAnd => intro ρ; rw [tinterp_impl_eq_top]; simp only [tinterp]; exact inf_le_left
  | permutationOr =>
    intro ρ; rw [tinterp_impl_eq_top]; simp only [tinterp]; exact (sup_comm _ _).le
  | permutationAnd =>
    intro ρ; rw [tinterp_impl_eq_top]; simp only [tinterp]; exact (inf_comm _ _).le
  | mp _ _ ih₁ ih₂ =>
    intro ρ
    have h₁ := tinterp_impl_eq_top.mp (ih₁ ρ)
    rw [ih₂ ρ] at h₁; exact top_le_iff.mp h₁
  | botElim => intro ρ; rw [tinterp_impl_eq_top]; simp only [tinterp]; exact bot_le
  | syllogism _ _ ih₁ ih₂ =>
    intro ρ; rw [tinterp_impl_eq_top]
    exact le_trans (tinterp_impl_eq_top.mp (ih₁ ρ)) (tinterp_impl_eq_top.mp (ih₂ ρ))
  | exportation _ ih =>
    intro ρ; rw [tinterp_impl_eq_top]
    have := tinterp_impl_eq_top.mp (ih ρ); simp only [tinterp] at this ⊢
    exact le_himp_iff.mpr this
  | importation _ ih =>
    intro ρ; rw [tinterp_impl_eq_top]
    have := tinterp_impl_eq_top.mp (ih ρ); simp only [tinterp] at this ⊢
    exact le_himp_iff.mp this
  | expansion _ ih =>
    intro ρ; rw [tinterp_impl_eq_top]; simp only [tinterp]
    exact sup_le_sup_left (tinterp_impl_eq_top.mp (ih ρ)) _
  | existQuant =>
    intro ρ; rw [tinterp_impl_eq_top]
    rw [tinterp_evarSubst _ _ _ _ (fun _ => rfl)]; simp only [tinterp]; exact le_rfl
  | existGen _ ih =>
    intro ρ; rw [tinterp_impl_eq_top]
    have := tinterp_impl_eq_top.mp (ih ρ); rw [tinterp_evarLift] at this
    simp only [tinterp]; exact this
  | forallQuant =>
    intro ρ; rw [tinterp_impl_eq_top]
    rw [tinterp_evarSubst _ _ _ _ (fun _ => rfl)]; simp only [tinterp]; exact le_rfl
  | forallGen _ ih =>
    intro ρ; rw [tinterp_impl_eq_top]
    have := tinterp_impl_eq_top.mp (ih ρ); rw [tinterp_evarLift] at this
    simp only [tinterp]; exact this
  | existence => intro ρ; simp [tinterp]
  | svSubst _ ih => intro ρ; rw [tinterp_svarSubst_zero]; exact ih _
  | preFixpoint hpos =>
    intro ρ; rw [tinterp_impl_eq_top, tinterp_svarSubst_zero]
    simp only [tinterp]
    apply le_sInf; intro S hS
    have hmu : sInf {S | tinterp M (ρ.push S) _ ≤ S} ≤ S := sInf_le hS
    obtain ⟨he, hl⟩ := push_args_zero ρ _ S hmu
    exact le_trans (tinterp_mono_pos hpos _ _ he hl) hS
  | knasterTarski _ ih =>
    intro ρ; rw [tinterp_impl_eq_top]
    have := tinterp_impl_eq_top.mp (ih ρ); rw [tinterp_svarSubst_zero] at this
    simp only [tinterp]; exact sInf_le this
  | postFixpoint hpos =>
    intro ρ; rw [tinterp_impl_eq_top, tinterp_svarSubst_zero]
    simp only [tinterp]
    apply sSup_le; intro S hS
    have hnu : S ≤ sSup {S | S ≤ tinterp M (ρ.push S) _} := le_sSup hS
    obtain ⟨he, hl⟩ := push_args_zero ρ S _ hnu
    exact le_trans hS (tinterp_mono_pos hpos _ _ he hl)
  | park _ ih =>
    intro ρ; rw [tinterp_impl_eq_top]
    have := tinterp_impl_eq_top.mp (ih ρ); rw [tinterp_svarSubst_zero] at this
    simp only [tinterp]; exact le_sSup this
  | singleton => intro ρ; exact tvalid_singleton ρ
  | propagationOrLeft =>
    intro ρ; rw [tinterp_impl_eq_top]; simp only [tinterp]
    rw [inf_sup_right]; exact j_sup_le M.top_prime _ _
  | propagationOrRight =>
    intro ρ; rw [tinterp_impl_eq_top]; simp only [tinterp]
    rw [inf_sup_left]; exact j_sup_le M.top_prime _ _
  | propagationExistLeft =>
    intro ρ; rw [tinterp_impl_eq_top]; simp only [tinterp]
    rw [tinterp_evarLift]
  | propagationExistRight =>
    intro ρ; rw [tinterp_impl_eq_top]; simp only [tinterp]
    rw [tinterp_evarLift]
  | framingLeft _ ih =>
    intro ρ; rw [tinterp_impl_eq_top]; simp only [tinterp]
    exact j_mono (inf_le_inf_right _ (tinterp_impl_eq_top.mp (ih ρ)))
  | framingRight _ ih =>
    intro ρ; rw [tinterp_impl_eq_top]; simp only [tinterp]
    exact j_mono (inf_le_inf_left _ (tinterp_impl_eq_top.mp (ih ρ)))

-- ─────────────────────────────────────────────────────────────
-- The countermodel over a complete chain
-- ─────────────────────────────────────────────────────────────

section Counter

variable {L : Type*} [CompleteLinearOrder L]

theorem chain_top_prime (u v : L) (h : u ⊔ v = ⊤) : u = ⊤ ∨ v = ⊤ := by
  rcases le_total u v with huv | hvu
  · right; rwa [sup_eq_right.mpr huv] at h
  · left; rwa [sup_eq_left.mpr hvu] at h

/-- Symbols `true ↦ ⊤` (used as definedness / next symbol) and `false ↦ u`. -/
noncomputable def cm (u : L) : TModel Bool L where
  symInterp b := if b then ⊤ else u
  top_prime := chain_top_prime

/-- In a chain, `~u = ⊥` for `u ≠ ⊥`. -/
theorem himp_bot_of_ne_bot {u : L} (hu : u ≠ ⊥) : u ⇨ ⊥ = ⊥ := by
  apply le_antisymm _ bot_le
  have h₁ : (u ⇨ ⊥) ⊓ u ≤ ⊥ := by rw [inf_comm]; exact inf_himp_le
  rcases le_total (u ⇨ ⊥) u with h | h
  · rwa [inf_eq_left.mpr h] at h₁
  · rw [inf_eq_right.mpr h] at h₁; exact absurd (le_bot_iff.mp h₁) hu

theorem nn_of_ne_bot {u : L} (hu : u ≠ ⊥) : (u ⇨ ⊥) ⇨ ⊥ = ⊤ := by
  rw [himp_bot_of_ne_bot hu, bot_himp]

/-- The symbol interpreted as `⊤` (plays `ceil` and `next`). -/
abbrev s : Pattern Bool := .symbol true
/-- The symbol interpreted as `u`. -/
abbrev c : Pattern Bool := .symbol false
abbrev x₀ : Pattern Bool := .evar 0

@[simp] theorem cm_true (u : L) : (cm u).symInterp true = ⊤ := by simp [cm]
@[simp] theorem cm_false (u : L) : (cm u).symInterp false = u := by simp [cm]

/-- Truth value of `s ⬝ ~~c ⇒ ~~(s ⬝ c)` in `cm u`. -/
theorem cm_nnPropagation (u : L) (hu₁ : u ≠ ⊥) (hu₂ : u ≠ ⊤) (ρ : SVal L) :
    tinterp (cm u) ρ (.impl (.app s (.neg (.neg c))) (.neg (.neg (.app s c)))) = ⊥ := by
  simp only [Pattern.neg, tinterp, cm_true, cm_false, top_inf_eq]
  rw [nn_of_ne_bot hu₁, j_top, j_of_ne_top hu₂, bot_himp, top_himp, top_himp]

/-- Truth value of `~~c ⇒ c` in `cm u`. -/
theorem cm_dne (u : L) (hu₁ : u ≠ ⊥) (ρ : SVal L) :
    tinterp (cm u) ρ (.impl (.neg (.neg c)) c) = u := by
  simp only [Pattern.neg, tinterp, cm_false]
  rw [nn_of_ne_bot hu₁, top_himp]

/-- The definedness axiom `∀x. ⌈x⌉` (with `⌈·⌉ := s ⬝ ·`) holds in `cm u`. -/
theorem cm_definedness (u : L) : TValid (cm u) (.forallP (.app s x₀)) := by
  intro ρ; simp [tinterp, cm_true]

/-- Truth value of `c ⇒ ⌈c⌉` in `cm u`. -/
theorem cm_phi_impl_ceil (u : L) (hu₁ : u ≠ ⊥) (hu₂ : u ≠ ⊤) (ρ : SVal L) :
    tinterp (cm u) ρ (.impl c (.app s c)) = ⊥ := by
  simp only [tinterp, cm_true, cm_false, top_inf_eq]
  rw [j_of_ne_top hu₂, himp_bot_of_ne_bot hu₁]

/-- Truth value of Membership¬(←) `~(x ∈ c) ⇒ x ∈ ~c` in `cm u`. -/
theorem cm_memNegIntro (u : L) (hu₁ : u ≠ ⊥) (hu₂ : u ≠ ⊤) (ρ : SVal L) :
    tinterp (cm u) ρ
      (.impl (.neg (.app s (.conj x₀ c))) (.app s (.conj x₀ (.neg c)))) = ⊥ := by
  have hbt : (⊥ : L) ≠ ⊤ := fun h => hu₁ (le_bot_iff.mp (by rw [h]; exact le_top))
  simp only [Pattern.neg, tinterp, cm_true, cm_false, top_inf_eq]
  rw [j_of_ne_top hu₂, himp_bot_of_ne_bot hu₁, j_of_ne_top hbt, bot_himp, top_himp]

/-- Truth value of the membership excluded middle `⌈x⌉ ⇒ ⌈x ⊓ c⌉ ⊔ ⌈x ⊓ ~c⌉` in `cm u`. -/
theorem cm_memEM (u : L) (hu₁ : u ≠ ⊥) (hu₂ : u ≠ ⊤) (ρ : SVal L) :
    tinterp (cm u) ρ
      (.impl (.app s x₀) (.disj (.app s (.conj x₀ c)) (.app s (.conj x₀ (.neg c))))) = ⊥ := by
  have hbt : (⊥ : L) ≠ ⊤ := fun h => hu₁ (le_bot_iff.mp (by rw [h]; exact le_top))
  simp only [Pattern.neg, tinterp, cm_true, cm_false, top_inf_eq, j_top]
  rw [j_of_ne_top hu₂, himp_bot_of_ne_bot hu₁, j_of_ne_top hbt, bot_sup_eq, top_himp]

end Counter

-- ─────────────────────────────────────────────────────────────
-- Underivability results (L := ℕ∞, u := 1)
-- ─────────────────────────────────────────────────────────────

theorem one_ne_bot : (1 : ℕ∞) ≠ ⊥ := by decide
theorem one_ne_top : (1 : ℕ∞) ≠ ⊤ := by decide

theorem empty_valid (u : ℕ∞) : ∀ γ ∈ (∅ : Set (Pattern Bool)), TValid (cm u) γ :=
  fun _ hγ => absurd hγ (Set.notMem_empty _)

/-- `C[~~φ] ⇒ ~~C[φ]` is not derivable in iML (instance `C = s ⬝ □`, `φ = c`). -/
theorem nnPropagation_not_derivable :
    IsEmpty ((∅ : Set (Pattern Bool)) ⊩ᵢ
      .impl (.app s (.neg (.neg c))) (.neg (.neg (.app s c)))) := by
  constructor; intro h
  have := soundness h (cm (1 : ℕ∞)) (empty_valid 1) (fun _ => ⊥)
  rw [cm_nnPropagation _ one_ne_bot one_ne_top] at this
  exact bot_ne_top this

/-- Double-negation elimination (axiom p3) is not derivable in iML. -/
theorem dne_not_derivable :
    IsEmpty ((∅ : Set (Pattern Bool)) ⊩ᵢ .impl (.neg (.neg c)) c) := by
  constructor; intro h
  have := soundness h (cm (1 : ℕ∞)) (empty_valid 1) (fun _ => ⊥)
  rw [cm_dne _ one_ne_bot] at this
  exact one_ne_top this

/-- The definedness theory `{∀x. ⌈x⌉}`, with `⌈·⌉ := s ⬝ ·`. -/
def defTheory : Set (Pattern Bool) := {.forallP (.app s x₀)}

theorem defTheory_valid (u : ℕ∞) : ∀ γ ∈ defTheory, TValid (cm u) γ := by
  intro γ hγ; rw [defTheory, Set.mem_singleton_iff] at hγ; subst hγ; exact cm_definedness u

/-- Thesis Lemma 3.14 / Corollary 3.1, `φ ⇒ ⌈φ⌉`, is not derivable from definedness. -/
theorem phi_impl_ceil_not_derivable :
    IsEmpty (defTheory ⊩ᵢ .impl c (.app s c)) := by
  constructor; intro h
  have := soundness h (cm (1 : ℕ∞)) (defTheory_valid 1) (fun _ => ⊥)
  rw [cm_phi_impl_ceil _ one_ne_bot one_ne_top] at this
  exact bot_ne_top this

/-- Membership¬(←), `~(x ∈ φ) ⇒ x ∈ ~φ`, is not derivable from definedness. -/
theorem memNegIntro_not_derivable :
    IsEmpty (defTheory ⊩ᵢ
      .impl (.neg (.app s (.conj x₀ c))) (.app s (.conj x₀ (.neg c)))) := by
  constructor; intro h
  have := soundness h (cm (1 : ℕ∞)) (defTheory_valid 1) (fun _ => ⊥)
  rw [cm_memNegIntro _ one_ne_bot one_ne_top] at this
  exact bot_ne_top this

/-- Truth value of `c ⊔ ~c` in `cm u`. -/
theorem cm_em {L : Type*} [CompleteLinearOrder L] (u : L) (hu₁ : u ≠ ⊥) (ρ : SVal L) :
    tinterp (cm u) ρ (.disj c (.neg c)) = u := by
  simp only [Pattern.neg, tinterp, cm_false]
  rw [himp_bot_of_ne_bot hu₁, sup_bot_eq]

/-- Excluded middle `c ⊔ ~c` is not derivable from definedness. -/
theorem em_not_derivable : IsEmpty (defTheory ⊩ᵢ .disj c (.neg c)) := by
  constructor; intro h
  have := soundness h (cm (1 : ℕ∞)) (defTheory_valid 1) (fun _ => ⊥)
  rw [cm_em _ one_ne_bot] at this
  exact one_ne_top this

/-- The deduction theorem of the thesis (Theorem 3.3 / Theorem 4.2), in the
form "`Γ ∪ {ψ} ⊢ φ` implies `Γ ⊢ ⌊ψ⌋ ⇒ φ`" with `⌊ψ⌋ := ~⌈~ψ⌉`, is **false**
for iML: applied to `ψ = φ = c ⊔ ~c` it would yield `⊢ ⌊c ⊔ ~c⌋ ⇒ c ⊔ ~c`,
but `⌊c ⊔ ~c⌋` is derivable (it is the double negation of excluded middle,
pushed through `⌈·⌉` by framing and ⊥-propagation), so excluded middle
would be derivable. -/
theorem deductionTheorem_fails :
    ¬ ∀ (ψ φ : Pattern Bool), Nonempty ((defTheory ∪ {ψ}) ⊩ᵢ φ) →
        Nonempty (defTheory ⊩ᵢ .impl (.neg (.app s (.neg ψ))) φ) := by
  intro hDT
  obtain ⟨h⟩ := hDT (.disj c (.neg c)) (.disj c (.neg c))
    ⟨.assumption (Set.mem_union_right _ (Set.mem_singleton _))⟩
  have htot : defTheory ⊩ᵢ .neg (.app s (.neg (.disj c (.neg c)))) :=
    .syllogism (.framingRight nnExcludedMiddle) (ctxBot (.right s .hole))
  exact em_not_derivable.false (.mp h htot)

/-- The membership excluded middle is not derivable from definedness. -/
theorem memEM_not_derivable :
    IsEmpty (defTheory ⊩ᵢ
      .impl (.app s x₀) (.disj (.app s (.conj x₀ c)) (.app s (.conj x₀ (.neg c))))) := by
  constructor; intro h
  have := soundness h (cm (1 : ℕ∞)) (defTheory_valid 1) (fun _ => ⊥)
  rw [cm_memEM _ one_ne_bot one_ne_top] at this
  exact bot_ne_top this

end IML.TopFilter
