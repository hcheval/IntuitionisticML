import IML.HeytingSoundness
import IML.DerivedRules.EqualitySemantics
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The sheaf of functions: a genuinely non-crisp Ω-set model

An `HModel` (`IML/HeytingSemantics.lean`) carries an `L`-valued equality
`E : Carrier → Carrier → L` that is reflexive with value `⊤`, symmetric and
transitive, together with symbol and application interpretations that are
*extensional* for `E`. This is the total-elements case of a Fourman–Scott
**Ω-set**: a set whose elements are not simply equal or distinct, but
identified *to a degree* measured in the frame `L`.

Every other model in this development is either *crisp* (`IML.crispModel`:
`E` is `⊤` or `⊥`, ordinary equality dressed up — this is what the
topological and Kripke examples in `IML.Examples.OpenSets` and
`IML.Examples.Kripke` go through) or a two-element countermodel built to
refute a formula. None of them shows what the extra generality *is for*.
This file supplies the motivating example.

## The construction

Fix a topological space `X` and a type `Y`. Truth values are `Opens X`
("where a statement holds"), and the carrier is the set `X → Y` of
`Y`-valued functions on `X`. Two functions `f g` are equal *to the extent
that they agree*:

    E f g = agree f g := interior {x | f x = g x},

the largest open set on which `f` and `g` coincide. So `f` and `g` are
"equal near `x`" when they agree on a neighbourhood of `x`. Reflexivity is
`interior univ = univ`, symmetry is symmetry of `=`, and transitivity says
that where `f = g` and `g = h` hold on a neighbourhood, so does `f = h`.

This is the sheaf of `Y`-valued functions on `X`, viewed as an Ω-set; `X → Y`
is its set of *global sections*. Restricting to continuous functions
`C(X, Y)` gives the sheaf of continuous sections of the trivial bundle and
works verbatim. Genuinely *partial* sections `s : U → Y` defined on a proper
open `U` are also elements of the Fourman–Scott Ω-set, but with self-equality
`E s s = U ≠ ⊤`; `HModel` asks for `E a a = ⊤`, so it captures exactly the
total elements, and we do not include partial sections here.

Symbols and application act **pointwise**. Given a classical applicative
structure on `Y` — a ternary application relation `app : Y → Y → Y → Prop`
and, for each symbol, a set `sym s ⊆ Y` of values (`PointwiseData`) — the
model interprets

    ⟦s⟧(f)         = interior {x | sym s (f x)}             (`f` takes values in `s`)
    ⟦app⟧(f, g, h) = interior {x | app (f x) (g x) (h x)}   (`h` applies `f` to `g`).

These are extensional for `agree` because they are *local*: replacing `f`
by a function that agrees with it near `x` does not change whether the
condition holds near `x`. All four extensionality obligations reduce to one
lemma, `locus_inf_le`.

## What it buys

* `agree_ramp_zero`: on `X = ℝ`, the ramp `x ↦ max x 0` and the zero
  function have equality `(-∞, 0)`, a proper open — they are neither equal
  nor distinct (`agree_ramp_zero_ne_bot`, `agree_ramp_zero_ne_top`). No
  crisp model can produce this.
* `sheafModel_hinterp_eqI_evar`: when the applicative data interpret
  definedness standardly, the *syntactic* positive equality `x =ⁱ y` of two
  element variables denotes the agreement locus of their values, so
  `⟦x =ⁱ y⟧ = (-∞, 0)` for the ramp and zero (`hinterp_eqI_ramp_zero`).

## Relation to `OpenSets.lean` and `Kripke.lean`

Those files use the *same* frame `Opens X` of truth values but go through
`crispModel`, so their elements are still crisply equal: only the truth of
a symbol or application varies over `X`. Here the *elements themselves*
vary over `X`, and equality between them is a genuine open set. Same
lattice of truth values, different notion of element.
-/

namespace IML.Examples.Sheaf

open TopologicalSpace

variable {X : Type} [TopologicalSpace X] {Y : Type}

-- ─────────────────────────────────────────────────────────────
-- Loci: the open set where a pointwise condition holds
-- ─────────────────────────────────────────────────────────────

/-- The **locus** of a pointwise condition `P` on `X`: the largest open set on
which `P` holds. Every truth value in the model is a locus. -/
def locus (P : X → Prop) : Opens X :=
  ⟨interior {x | P x}, isOpen_interior⟩

theorem coe_locus (P : X → Prop) : (locus P : Set X) = interior {x | P x} := rfl

/-- A condition that holds everywhere holds on all of `X`. -/
theorem locus_eq_top {P : X → Prop} (h : ∀ x, P x) : locus P = ⊤ := by
  apply Opens.ext
  rw [coe_locus, Opens.coe_top, interior_eq_univ]
  exact Set.eq_univ_of_forall h

/-- Loci are monotone in the condition. -/
theorem locus_mono {P Q : X → Prop} (h : ∀ x, P x → Q x) : locus P ≤ locus Q :=
  interior_mono fun x hx => h x hx

/-- **The locality principle.** If `R` follows pointwise from `P` and `Q`, then
`R` holds wherever `P` and `Q` hold on a neighbourhood. This single lemma
discharges transitivity of `agree` and all four extensionality obligations. -/
theorem locus_inf_le {P Q R : X → Prop} (h : ∀ x, P x → Q x → R x) :
    locus P ⊓ locus Q ≤ locus R := by
  change interior {x | P x} ∩ interior {x | Q x} ⊆ interior {x | R x}
  rw [← interior_inter]
  exact interior_mono fun x hx => h x hx.1 hx.2

-- ─────────────────────────────────────────────────────────────
-- The Ω-set: functions, equal where they agree
-- ─────────────────────────────────────────────────────────────

/-- The **agreement locus** of two functions: the largest open set on which
they coincide. This is the `Opens X`-valued equality of the model. -/
def agree (f g : X → Y) : Opens X :=
  locus fun x => f x = g x

theorem coe_agree (f g : X → Y) : (agree f g : Set X) = interior {x | f x = g x} := rfl

/-- A function agrees with itself everywhere. -/
theorem agree_refl (f : X → Y) : agree f f = ⊤ :=
  locus_eq_top fun _ => rfl

/-- Agreement is symmetric. -/
theorem agree_symm (f g : X → Y) : agree f g = agree g f := by
  simp only [agree, locus, Opens.mk.injEq]
  congr 1
  ext x
  exact eq_comm

/-- Agreement is transitive: where `f = g` and `g = h` near a point, so is
`f = h`. -/
theorem agree_trans (f g h : X → Y) : agree f g ⊓ agree g h ≤ agree f h :=
  locus_inf_le fun _ hfg hgh => hfg.trans hgh

-- ─────────────────────────────────────────────────────────────
-- Pointwise applicative structure
-- ─────────────────────────────────────────────────────────────

/-- A classical applicative structure on the value type `Y`: a ternary
application relation and a set of values for each symbol. This is exactly
the data of a classical matching-logic model on `Y`; the sheaf model lifts it
pointwise to `Y`-valued functions on a space. -/
structure PointwiseData (Symbol : Type) (Y : Type) where
  /-- `app a b c`: `c` is a result of applying `a` to `b`. -/
  app : Y → Y → Y → Prop
  /-- `sym s y`: the value `y` matches the symbol `s`. -/
  sym : Symbol → Y → Prop

/-- The pointwise applicative structure of a binary operation: application
is the graph of `op`, and a symbol matches the values in the given set. -/
def PointwiseData.ofOp {Symbol : Type} (op : Y → Y → Y) (sym : Symbol → Y → Prop) :
    PointwiseData Symbol Y :=
  ⟨fun a b c => op a b = c, sym⟩

-- ─────────────────────────────────────────────────────────────
-- The model
-- ─────────────────────────────────────────────────────────────

/-- **The sheaf model.** Carrier `X → Y`, equality the agreement locus,
symbols and application interpreted pointwise from `D`. -/
def sheafModel (Symbol : Type) (X : Type) [TopologicalSpace X] (Y : Type)
    (D : PointwiseData Symbol Y) : HModel Symbol (Opens X) where
  Carrier := X → Y
  E := agree
  E_refl := agree_refl
  E_symm := agree_symm
  E_trans := agree_trans
  appInterp f g h := locus fun x => D.app (f x) (g x) (h x)
  symInterp s f := locus fun x => D.sym s (f x)
  symInterp_ext _ _ _ := locus_inf_le fun _ hfg hs => hfg ▸ hs
  appInterp_ext₁ _ _ _ _ := locus_inf_le fun _ hff' ha => hff' ▸ ha
  appInterp_ext₂ _ _ _ _ := locus_inf_le fun _ hgg' ha => hgg' ▸ ha
  appInterp_ext₃ _ _ _ _ := locus_inf_le fun _ hhh' ha => hhh' ▸ ha

section Unfolding

variable {Symbol : Type} {D : PointwiseData Symbol Y}

/-- An element variable at a function `m` is true exactly where `m` agrees
with the variable's value. -/
theorem sheafModel_hinterp_evar (ρ : HValuation (sheafModel Symbol X Y D)) (i : EVarIndex)
    (m : X → Y) :
    hinterp (sheafModel Symbol X Y D) ρ (.evar i) m = agree m (ρ.evar i) := rfl

/-- A symbol at a function `m` is true exactly where `m` takes values in the
symbol's set. -/
theorem sheafModel_hinterp_symbol (ρ : HValuation (sheafModel Symbol X Y D)) (s : Symbol)
    (m : X → Y) :
    hinterp (sheafModel Symbol X Y D) ρ (.symbol s) m = locus fun x => D.sym s (m x) := rfl

/-- Soundness of iML over the sheaf model. -/
theorem sheafModel_soundness {Γ : Set (Pattern Symbol)} {φ : Pattern Symbol}
    (h : Γ ⊩ᵢ φ) (hΓ : ∀ γ ∈ Γ, HValid (sheafModel Symbol X Y D) γ) :
    HValid (sheafModel Symbol X Y D) φ :=
  soundness h (Opens X) _ hΓ

end Unfolding

-- ─────────────────────────────────────────────────────────────
-- Non-crispness: two functions that are neither equal nor distinct
-- ─────────────────────────────────────────────────────────────

/-- The ramp function `x ↦ max x 0` on the real line. -/
def ramp : ℝ → ℝ := fun x => max x 0

/-- The open negative half-line `(-∞, 0)` as an open set of `ℝ`. -/
def negHalfLine : Opens ℝ := ⟨Set.Iio 0, isOpen_Iio⟩

/-- **A proper open equality.** The ramp and the zero function agree exactly
on the closed half-line `(-∞, 0]`, whose interior is `(-∞, 0)`: they are
equal on the negative axis, distinct on the positive axis, and at `0` — where
they take the same value but not on any neighbourhood — neither. -/
theorem agree_ramp_zero : agree ramp (fun _ => 0) = negHalfLine := by
  apply Opens.ext
  change interior {x : ℝ | max x 0 = 0} = Set.Iio 0
  have : {x : ℝ | max x 0 = 0} = Set.Iic 0 := by
    ext x
    simp
  rw [this, interior_Iic]

/-- The ramp and zero are not distinct: they agree somewhere. -/
theorem agree_ramp_zero_ne_bot : agree ramp (fun _ => 0) ≠ ⊥ := by
  rw [agree_ramp_zero]
  intro h
  have hm : (-1 : ℝ) ∈ negHalfLine := by
    change (-1 : ℝ) ∈ Set.Iio 0
    simp
  rw [h] at hm
  exact hm

/-- The ramp and zero are not equal: they disagree somewhere. -/
theorem agree_ramp_zero_ne_top : agree ramp (fun _ => 0) ≠ ⊤ := by
  rw [agree_ramp_zero]
  intro h
  have hm : (1 : ℝ) ∈ (⊤ : Opens ℝ) := trivial
  rw [← h] at hm
  change (1 : ℝ) < 0 at hm
  exact lt_irrefl _ (hm.trans zero_lt_one)

-- ─────────────────────────────────────────────────────────────
-- Syntactic equality computes to the agreement locus
-- ─────────────────────────────────────────────────────────────

section Definedness

variable {Symbol : Type} [HasCeil Symbol]

/-- The sheaf model interprets definedness standardly as soon as the
pointwise data do: the definedness symbol matches every value and the
application relation is total. The remaining symbols are unconstrained. -/
theorem sheafModel_stdCeil (D : PointwiseData Symbol Y) (hceil : ∀ y, D.sym HasCeil.ceil y)
    (happ : ∀ a b c, D.app a b c) : (sheafModel Symbol X Y D).StdCeil :=
  ⟨fun _ => locus_eq_top fun _ => hceil _, fun _ _ _ => locus_eq_top fun _ => happ _ _ _⟩

open Pattern in
/-- **Positive equality of element variables is the agreement locus.** Under
standard definedness, the syntactic equality `x =ⁱ y` of `Definedness.lean`
denotes, at every point of the carrier, the largest open set on which the
values of `x` and `y` coincide. -/
theorem sheafModel_hinterp_eqI_evar (D : PointwiseData Symbol Y)
    (hceil : ∀ y, D.sym HasCeil.ceil y) (happ : ∀ a b c, D.app a b c)
    (ρ : HValuation (sheafModel Symbol X Y D)) (n k : EVarIndex) (m : X → Y) :
    hinterp (sheafModel Symbol X Y D) ρ (.evar n =ⁱₘₗ .evar k) m = agree (ρ.evar n) (ρ.evar k) :=
  hinterp_eqI_evar (sheafModel_stdCeil D hceil happ) ρ n k m

/-- The trivial pointwise data over `ℝ`: every symbol matches every value and
application is total. Its only purpose is to interpret definedness standardly
for the example below; the interest of that example lies entirely in the
equality. -/
def trivialData (Symbol : Type) : PointwiseData Symbol ℝ :=
  ⟨fun _ _ _ => True, fun _ _ => True⟩

/-- The valuation `x ↦ ramp`, all other element variables `↦ 0`, and every set
variable `↦ ⊥`. -/
def rampValuation (Symbol : Type) [HasCeil Symbol] :
    HValuation (sheafModel Symbol ℝ ℝ (trivialData Symbol)) where
  evar n := if n = 0 then ramp else fun _ => 0
  svar _ _ := ⊥
  svar_ext _ _ _ := inf_le_right

open Pattern in
/-- **The payoff.** With `x ↦ ramp` and `y ↦ 0`, the syntactic equality
`x =ⁱ y` is the proper open `(-∞, 0)`, at every point of the carrier: the two
variables are provably-equal on the negative axis, provably-distinct on the
positive axis, and undecided at the origin. -/
theorem hinterp_eqI_ramp_zero (m : ℝ → ℝ) :
    hinterp (sheafModel Symbol ℝ ℝ (trivialData Symbol)) (rampValuation Symbol)
      (.evar 0 =ⁱₘₗ .evar 1) m = negHalfLine := by
  rw [sheafModel_hinterp_eqI_evar _ (fun _ => trivial) (fun _ _ _ => trivial)]
  exact agree_ramp_zero

end Definedness

end IML.Examples.Sheaf
