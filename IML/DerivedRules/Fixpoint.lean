import IML.DerivedRules.FOL

/-!
# Derived fixpoint rules of iML

Chapter 4 of the thesis (Lemmas 4.2, 4.3, 4.6 and the ν-duals). Since `ν`
is primitive in iML with its own PREFIXPOINT/KNASTER-TARSKI rules
(`postFixpoint`, `park`), the classical detour `ν = ¬μ¬` and its three
negations disappear entirely; the μ and ν results are perfectly symmetric.

Also: `μX.X ⟺ ⊥`, which shows that taking `⊥` primitive (as this
formalization does) versus `⊥ := μX.X` (as the thesis does) makes no
difference to derivability.
-/

namespace IML

open Pattern

variable {Symbol : Type}

-- ─────────────────────────────────────────────────────────────
-- Substitution–lifting cancellation for set variables
-- ─────────────────────────────────────────────────────────────

theorem svarSubst_svarLiftFrom (φ : Pattern Symbol) (n : Nat) (ψ : Pattern Symbol) :
    svarSubst n ψ (svarLiftFrom n φ) = φ := by
  induction φ generalizing n ψ with
  | svar i =>
    simp only [svarLiftFrom]; split
    · rename_i h; simp only [svarSubst]
      split
      · exact absurd (beq_iff_eq.mp ‹_›) (Nat.ne_of_gt (Nat.lt_succ_of_le h))
      · split <;> simp
        exact absurd (Nat.lt_succ_of_le h) ‹_›
    · rename_i h; simp only [svarSubst]
      split
      · exact absurd (Nat.le_of_eq (beq_iff_eq.mp ‹_›).symm) h
      · split
        · exact absurd (Nat.le_of_lt ‹_›) h
        · rfl
  | evar | symbol | bot => rfl
  | app _ _ ih₁ ih₂ => simp only [svarLiftFrom, svarSubst, ih₁, ih₂]
  | impl _ _ ih₁ ih₂ => simp only [svarLiftFrom, svarSubst, ih₁, ih₂]
  | conj _ _ ih₁ ih₂ => simp only [svarLiftFrom, svarSubst, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => simp only [svarLiftFrom, svarSubst, ih₁, ih₂]
  | exist _ ih => simp only [svarLiftFrom, svarSubst, ih]
  | forallP _ ih => simp only [svarLiftFrom, svarSubst, ih]
  | mu _ ih =>
    simp only [svarLiftFrom, svarSubst]; congr 1; exact ih (n + 1) (svarLift ψ)
  | nu _ ih =>
    simp only [svarLiftFrom, svarSubst]; congr 1; exact ih (n + 1) (svarLift ψ)

theorem svarSubst_svarLift (φ ψ : Pattern Symbol) :
    svarSubst 0 ψ (svarLift φ) = φ :=
  svarSubst_svarLiftFrom φ 0 ψ

/-- A lifted pattern is both positive and negative at the lifted index. -/
theorem svarLiftFrom_pos_neg (φ : Pattern Symbol) (k : Nat) :
    SVarPositive (svarLiftFrom k φ) k ∧ SVarNegative (svarLiftFrom k φ) k := by
  induction φ generalizing k with
  | evar => exact ⟨.evar, .evar⟩
  | svar i =>
    simp only [svarLiftFrom]
    have hne : (if i ≥ k then i + 1 else i) ≠ k := by
      by_cases h : i ≥ k
      · rw [if_pos h]; exact Nat.ne_of_gt (Nat.lt_succ_of_le h)
      · rw [if_neg h]; exact fun heq => h (Nat.le_of_eq heq.symm)
    exact ⟨.svarNe hne, .svarNe hne⟩
  | symbol => exact ⟨.symbol, .symbol⟩
  | bot => exact ⟨.bot, .bot⟩
  | app _ _ ih₁ ih₂ => exact ⟨.app (ih₁ k).1 (ih₂ k).1, .app (ih₁ k).2 (ih₂ k).2⟩
  | impl _ _ ih₁ ih₂ => exact ⟨.impl (ih₁ k).2 (ih₂ k).1, .impl (ih₁ k).1 (ih₂ k).2⟩
  | conj _ _ ih₁ ih₂ => exact ⟨.conj (ih₁ k).1 (ih₂ k).1, .conj (ih₁ k).2 (ih₂ k).2⟩
  | disj _ _ ih₁ ih₂ => exact ⟨.disj (ih₁ k).1 (ih₂ k).1, .disj (ih₁ k).2 (ih₂ k).2⟩
  | exist _ ih => exact ⟨.exist (ih k).1, .exist (ih k).2⟩
  | forallP _ ih => exact ⟨.forallP (ih k).1, .forallP (ih k).2⟩
  | mu _ ih => exact ⟨.mu (ih (k + 1)).1, .mu (ih (k + 1)).2⟩
  | nu _ ih => exact ⟨.nu (ih (k + 1)).1, .nu (ih (k + 1)).2⟩

theorem svarLift_positive (φ : Pattern Symbol) : SVarPositive (svarLift φ) 0 :=
  (svarLiftFrom_pos_neg φ 0).1

-- ─────────────────────────────────────────────────────────────
-- μ: pre-fixpoint, induction, monotonicity (Lemma 4.3)
-- ─────────────────────────────────────────────────────────────

variable {Γ : Set (Pattern Symbol)} {φ ψ : Pattern Symbol}

def muPreFixpoint (hpos : SVarPositive φ 0) : Γ ⊩ᵢ φ[0 ₛ↦ μ φ] ⇒ μ φ :=
  .preFixpoint hpos

def muInduction (h : Γ ⊩ᵢ φ[0 ₛ↦ ψ] ⇒ ψ) : Γ ⊩ᵢ μ φ ⇒ ψ := .knasterTarski h

def muMono (hpos : SVarPositive ψ 0) (h : Γ ⊩ᵢ φ[0 ₛ↦ μ ψ] ⇒ ψ[0 ₛ↦ μ ψ]) :
    Γ ⊩ᵢ μ φ ⇒ μ ψ :=
  .knasterTarski (.syllogism h (.preFixpoint hpos))

/-- Lemma 4.3: `φ ⇒ ψ` implies `μX.φ ⇒ μX.ψ`. -/
def muMonoFromImpl (hpos : SVarPositive ψ 0) (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ μ φ ⇒ μ ψ :=
  muMono hpos (.svSubst h)

-- ─────────────────────────────────────────────────────────────
-- ν: post-fixpoint, coinduction, monotonicity (Lemma 4.2, dual of 4.3)
-- ─────────────────────────────────────────────────────────────

def nuPostFixpoint (hpos : SVarPositive φ 0) : Γ ⊩ᵢ ν φ ⇒ φ[0 ₛ↦ ν φ] :=
  .postFixpoint hpos

def nuCoinduction (h : Γ ⊩ᵢ ψ ⇒ φ[0 ₛ↦ ψ]) : Γ ⊩ᵢ ψ ⇒ ν φ := .park h

def nuMono (hpos : SVarPositive φ 0) (h : Γ ⊩ᵢ φ[0 ₛ↦ ν φ] ⇒ ψ[0 ₛ↦ ν φ]) :
    Γ ⊩ᵢ ν φ ⇒ ν ψ :=
  .park (.syllogism (.postFixpoint hpos) h)

def nuMonoFromImpl (hpos : SVarPositive φ 0) (h : Γ ⊩ᵢ φ ⇒ ψ) : Γ ⊩ᵢ ν φ ⇒ ν ψ :=
  nuMono hpos (.svSubst h)

-- ─────────────────────────────────────────────────────────────
-- μX.X is ⊥, νX.X is ⊤
-- ─────────────────────────────────────────────────────────────

theorem svarSubst_svar_zero (ψ : Pattern Symbol) : svarSubst 0 ψ (.svar 0) = ψ := by
  simp [svarSubst]

/-- `μX.X ⇒ φ` for every `φ`: the thesis' definition `⊥ := μX.X` and the
primitive `⊥` of this formalization are interderivable (`muSvarIffBot`). -/
def muSvar : Γ ⊩ᵢ μ (.svar 0) ⇒ φ :=
  .knasterTarski (by rw [svarSubst_svar_zero]; exact implSelf)

def muSvarIffBot : Γ ⊩ᵢ μ (.svar 0 : Pattern Symbol) ⟺ ⊥ₘ := iffIntro muSvar botElim

def nuSvar : Γ ⊩ᵢ φ ⇒ ν (.svar 0) :=
  .park (by rw [svarSubst_svar_zero]; exact implSelf)

def nuSvarIffTop : Γ ⊩ᵢ ν (.svar 0 : Pattern Symbol) ⟺ ⊤ₘ := iffIntro implTop nuSvar

-- ─────────────────────────────────────────────────────────────
-- μ-unfolding needs syntactic monotonicity (Lemma 4.5), which we only
-- state as a hypothesis here.  Given `svarMono` for `φ`, both directions
-- of Lemma 4.6 follow.
-- ─────────────────────────────────────────────────────────────

/-- Lemma 4.6 (→), assuming the substitution instance of Lemma 4.5 for `φ`. -/
def muUnfoldLeft (hmono : Γ ⊩ᵢ φ[0 ₛ↦ φ[0 ₛ↦ μ φ]] ⇒ φ[0 ₛ↦ μ φ]) :
    Γ ⊩ᵢ μ φ ⇒ φ[0 ₛ↦ μ φ] :=
  .knasterTarski hmono

def muUnfold (hpos : SVarPositive φ 0)
    (hmono : Γ ⊩ᵢ φ[0 ₛ↦ φ[0 ₛ↦ μ φ]] ⇒ φ[0 ₛ↦ μ φ]) :
    Γ ⊩ᵢ μ φ ⟺ φ[0 ₛ↦ μ φ] :=
  iffIntro (muUnfoldLeft hmono) (.preFixpoint hpos)

def nuUnfold (hpos : SVarPositive φ 0)
    (hmono : Γ ⊩ᵢ φ[0 ₛ↦ ν φ] ⇒ φ[0 ₛ↦ φ[0 ₛ↦ ν φ]]) :
    Γ ⊩ᵢ ν φ ⟺ φ[0 ₛ↦ ν φ] :=
  iffIntro (.postFixpoint hpos) (.park hmono)

end IML
