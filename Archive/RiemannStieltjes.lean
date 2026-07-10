/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic

/-! # Riemann–Stieltjes integral

In this file we give some API for intervals (using the type `BoxIntegral.Box (Fin 1)`), and
use this to define the (one-dimensional) Riemann–Stieltjes integral `∫ˢ x in a..b, f x ∂[B; g]`
from `a` to `b` of a function `f : ℝ → E` against an integrator `g : ℝ → F`, paired
by a continuous bilinear map `B : E →L[ℝ] F →L[ℝ] G`.  It is not required that `a < b`.

The notation here is deliberately chosen to mimic the notation `∫ x in a..b, f x ∂μ` for
`IntervalIntegral`, as well as the notation `∫ᵛ x, f x ∂[B; μ]` for
`MeasureTheory.VectorMeasure.Integral`.

The bilinear pairing `B` covers the three main variants of
Stieltjes integration that appear in practice:
* **`f` scalar, `g` vector-valued** (`B = .lsmul ℝ ℝ`): notation `∫ˢ x in a..b, f x ∂•g`.
* **`f` vector-valued, `g` scalar** (`B = (.lsmul ℝ ℝ).flip`): notation `∫ˢ x in a..b, f x ∂<•g`.
* **`f` and `g` both real or both complex** (`B = .mul ℝ E`): no dedicated shorthand; use the
  general `∫ˢ x in a..b, f x ∂[B; g]`.

The `.` here can be removed if `ContinuousLinearMap` is open.

The Riemann integral is the special case `F = ℝ`, `B = (.lsmul ℝ ℝ).flip` and `g = id`.

## Key definitions

* `Interval hab`: the one-dimensional interval `(a, b]` as a `Box (Fin 1)`, given a proof of
`hab : a < b`.
* `BoxAdditiveMap.ofDiff g`: the box-additive map on `Box (Fin 1)` defined by
`J ↦ g J.upper₁ - g J.lower₁`, where `g : ℝ → M` is a function to an additive commutative
group `M`.
* `BoxIntegral.StieltjesIntegrable a b B f g`: the predicate that the integral
`∫ˢ x in a..b, f x ∂[B; g]` exists.
* `BoxIntegral.HasStieltjesIntegral a b B f g L`: the predicate that the integral
`∫ˢ x in a..b, f x ∂[B; g]` exists and equals `L`.
* `BoxIntegral.stieltjesIntegral a b B f g`: the value of `∫ˢ x in a..b, f x ∂[B; g]` if it
exists, or the junk value of `0` otherwise.
* `BoxIntegral.RiemannIntegrable a b f`: the predicate that the Riemann integral
`∫ʳ x in a..b, f x` exists.
* `BoxIntegral.HasRiemannIntegral a b f L`: the predicate that the Riemann integral
`∫ʳ x in a..b, f x` exists and equals `L`.
* `BoxIntegral.riemannIntegral a b f`: the value of `∫ʳ x in a..b, f x` if it exists, or the
junk value of `0` otherwise.

These notions are named in analogy with `BoxInterval.Integrable`, `BoxInterval.HasIntegral`, and
`BoxInterval.integral`.

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.

## Usage

Some very basic API is provided in this file.  More extensive API may be found at
https://github.com/leanprover-community/mathlib-at-ICERM26/tree/stieltjes .  However, unless
one is specifically interested in the Riemann aspect of integration theory, it is recommended that
one instead use the more general integration API already in
Mathlib, specifically `MeasureTheory.Integral.Bochner` (for
integration against non-negative measures) or `MeasureTheory.VectorMeasure` (to handle
Lebesgue--Stieltjes) type integrals.

## Tags

Stieltjes integral, Riemann–-Stieltjes, Riemann integral
-/

@[expose] public section

open ContinuousLinearMap

namespace BoxIntegral

section Interval

/-! ## One-dimensional intervals

`Ioc` intervals can be represented within the `BoxIntegral` API as objects of type `Box (Fin 1)`.
We provide some minimal API for manipulating such intervals.
-/

variable {a b : ℝ} (J J' : Box (Fin 1))

/-- The left endpoint of a one-dimensional box. -/
def Box.lower₁ : ℝ := J.lower 0

/-- The right endpoint of a one-dimensional box. -/
def Box.upper₁ : ℝ := J.upper 0

lemma Box.lower_lt_upper₁ : J.lower₁ < J.upper₁ := J.lower_lt_upper 0

@[simp]
lemma Box.le_iff₁ : J ≤ J' ↔ J'.lower₁ ≤ J.lower₁ ∧ J.upper₁ ≤ J'.upper₁ :=
  by simp [Box.le_iff_bounds, Pi.le_def, lower₁, upper₁]

/-- One-dimensional `Ioc` interval as a `Box (Fin 1)` -/
noncomputable def Interval (hab : a < b) : Box (Fin 1) := ⟨ ![a], ![b], by simp [hab] ⟩

@[simp]
lemma interval_lower (hab : a < b) : (Interval hab).lower₁ = a := rfl

@[simp]
lemma interval_upper (hab : a < b) : (Interval hab).upper₁ = b := rfl

@[simp]
lemma interval_Icc (hab : a < b) : Box.Icc (Interval hab) = {x | x 0 ∈ Set.Icc a b} := by
  ext; simp [Box.Icc_def, Interval, Pi.le_def]

end Interval

section ofDiff

namespace BoxAdditiveMap

open Function Set Box Prepartition Finset

/-! ## The differential `ofDiff` of a function on `ℝ` -/

variable {M : Type*} [AddCommGroup M]

/-- Underlying construction for `ofDiff`: sends `g : ℝ → M` to the box-additive map on
`Box (Fin 1)` defined by `J ↦ g J.upper₁ - g J.lower₁`. -/
def ofDiffAux (g : ℝ → M) : (Fin 1) →ᵇᵃ M :=
  ofMapSplitAdd (fun J : Box (Fin 1) ↦ g J.upper₁ - g J.lower₁) ⊤
    (fun I _ i x hx ↦ by
      fin_cases i
      rw [splitLower_def hx, splitUpper_def hx]
      simp [Option.elim', upper₁, lower₁])

@[simp]
private lemma ofDiffAux_apply (g : ℝ → M) (J : Box (Fin 1)) :
    ofDiffAux g J = g J.upper₁ - g J.lower₁ := rfl

/-- The box-additive "differential" sending a function `g : ℝ → M` to the box-additive map on
`Box (Fin 1)` defined by `J ↦ g J.upper₁ - g J.lower₁`, bundled as an
`AddMonoidHom`. -/
def ofDiff : (ℝ → M) →+ ((Fin 1) →ᵇᵃ M) where
  toFun := ofDiffAux
  map_zero' := by ext; simp
  map_add' g h := by ext; simp [sub_add_sub_comm]

@[simp]
lemma ofDiff_apply (g : ℝ → M) (J : Box (Fin 1)) : ofDiff g J = g J.upper₁ - g J.lower₁ := rfl

@[simp]
lemma ofDiff_smul {R : Type*} [Monoid R] [DistribMulAction R M] (c : R) (g : ℝ → M) :
    ofDiff (c • g) = c • ofDiff g := by ext J; simp [smul_sub]

/-- The Riemann–Stieltjes differential of `ContinuousLinearMap.lsmul ℝ ℝ : ℝ → (E →L[ℝ] E)`
equals the Lebesgue volume box-additive map on `Box (Fin 1)`. -/
lemma ofDiff_lsmul_eq_volume {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ofDiff (fun x : ℝ ↦ (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) x) =
      (BoxAdditiveMap.volume : (Fin 1) →ᵇᵃ E →L[ℝ] E) := by
  ext
  simp [volume_apply, Box.upper₁, Box.lower₁]
  module

end BoxAdditiveMap

end ofDiff

/-! ## Definition of the Riemann--Stieltjes integral -/

variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

section Defs

variable (a b : ℝ) (B : E →L[ℝ] F →L[ℝ] G) (f : ℝ → E) (g : ℝ → F) (L : G)

/-- The (Riemann--)Stieltjes integral predicate of a function `f : ℝ → E` and `g : ℝ → F` having
its Riemann--Stieltjes sums converge to a limit `L : G`, given a bilinear map `B : E → F → G` and
endpoints `a`, `b` takes values in `G`. Initially defined under the implicit assumption that
`a < b`, with junk values otherwise. -/
def HasStieltjesIntegral_ordered (hab : a < b) : Prop := HasIntegral (Interval hab)
    IntegrationParams.Riemann (f <| · 0) (BoxAdditiveMap.ofDiff (B.flip <| g ·)) L

/-- Extension of `HasStieltjesIntegral_ordered` to cover the cases `a = b` and `a > b`. -/
def HasStieltjesIntegral : Prop :=
  if heq : a = b then L = 0 else
    if hab : a < b then HasStieltjesIntegral_ordered a b B f g L hab else
      HasStieltjesIntegral_ordered b a B f g (-L) (by order)

/-- `StieltjesIntegrable_ordered a b B f g hab` asserts that the ordered Riemann–Stieltjes integral
of `f` against `g` paired by `B` from `a` to `b` exists, i.e. some `L` satisfies
`HasStieltjesIntegral_ordered a b B f g L hab`.
-/
def StieltjesIntegrable_ordered (hab : a < b) : Prop :=
  ∃ L, HasStieltjesIntegral_ordered a b B f g L hab

/-- `StieltjesIntegrable a b B f g` asserts that the Riemann–Stieltjes integral of `f` against `g`
paired by `B` from `a` to `b` exists, i.e. some `L` satisfies `HasStieltjesIntegral a b B f g L`.
-/
def StieltjesIntegrable : Prop := ∃ L, HasStieltjesIntegral a b B f g L

open Classical in
/-- The Riemann–Stieltjes integral of `f` against `g` paired by `B` from `a` to `b`.
Returns the junk value `0` if no such integral exists.
The integral remains meaningful outside of the case `a < b`. -/
noncomputable def stieltjesIntegral : G :=
  if h : StieltjesIntegrable a b B f g then h.choose else 0

/-- Notation `∫ˢ x in a..b, f x ∂[B; g]` for the Riemann–Stieltjes integral of `f` against the
integrator `g`, paired by the bilinear map `B`.  Mirrors the vector-measure integral notation
`∫ᵛ x, f x ∂[B; μ]`, and parallels `∫ x in a..b, f x ∂μ` for `intervalIntegral`. -/
scoped notation3 "∫ˢ "(...)" in "a".."b", "r:60:(scoped f => f)" ∂["B:70"; "g:70"]" =>
  stieltjesIntegral a b B r g

/-- The special case of `∫ˢ x in a..b, f x ∂[B; g]` with `f` real-valued, `g` vector-valued, and
`B = ContinuousLinearMap.lsmul ℝ ℝ`. -/
scoped notation3 "∫ˢ "(...)" in "a".."b", "r:60:(scoped f => f)" ∂•"g:70 =>
  stieltjesIntegral a b (lsmul ℝ ℝ) r g

/-- The special case of `∫ˢ x in a..b, f x ∂[B; g]` with `f` vector-valued, `g` real-valued, and
`B = (ContinuousLinearMap.lsmul ℝ ℝ).flip`. -/
scoped notation3 "∫ˢ "(...)" in "a".."b", "r:60:(scoped f => f)" ∂<•"g:70 =>
  stieltjesIntegral a b (lsmul ℝ ℝ).flip r g

-- The case where `f` and `g` are both real- or both complex-valued (`B = .mul ℝ E`) has no
-- dedicated shorthand; write it with the general notation as `∫ˢ x in a..b, f x ∂[.mul ℝ E; g]`.

/-! ### The Riemann integral
-/

variable (L : E)

/-- `HasRiemannIntegral a b f L` is defined to equal
`HasStieltjesIntegral a b (lsmul ℝ ℝ).flip f id L`.  Use `unfold HasRiemannIntegral` or similar
to access the Stieltjes integral API. -/
def HasRiemannIntegral := HasStieltjesIntegral a b (lsmul ℝ ℝ).flip f id L

/-- `RiemannIntegrable a b f` is defined to equal
`StieltjesIntegrable a b (lsmul ℝ ℝ).flip f id`.  Use `unfold RiemannIntegrable` or similar
to access the Stieltjes integral API. -/
def RiemannIntegrable := StieltjesIntegrable a b (lsmul ℝ ℝ).flip f id

/-- `riemannIntegral a b f`, with notation `∫ʳ x in a..b, f x`, is defined to equal
`∫ˢ x in a..b, f x ∂<•id`.  Use `unfold riemannIntegral` or similar to access the Stieltjes integral
API.  A future PR will relate `riemannIntegral` to `intervalIntegral` under suitable hypotheses on
`f`. -/
noncomputable def riemannIntegral : E := ∫ˢ x in a..b, f x ∂<•id

@[inherit_doc riemannIntegral]
scoped notation3 "∫ʳ "(...)" in "a".."b", "r:60:(scoped f => f) => riemannIntegral a b r

end Defs

section Simple

/-! ## Simple properties -/

variable {a b : ℝ} {B : E →L[ℝ] F →L[ℝ] G} {f f₁ f₂ : ℝ → E} {g g₁ g₂ : ℝ → F} {L L₁ L₂ : G}

@[simp]
lemma HasStieltjesIntegral.of_eq_iff_zero : HasStieltjesIntegral a a B f g L ↔ L = 0 := by
  simp [HasStieltjesIntegral]

lemma HasStieltjesIntegral.of_lt (hab : a < b) :
    HasStieltjesIntegral a b B f g L ↔ HasStieltjesIntegral_ordered a b B f g L hab := by
  simp [HasStieltjesIntegral, hab, hab.ne]

@[simp]
lemma HasStieltjesIntegral.of_gt (hba : b < a) :
    HasStieltjesIntegral a b B f g L ↔ HasStieltjesIntegral_ordered b a B f g (-L) hba := by
  simp [HasStieltjesIntegral, Std.not_gt_of_lt hba, hba.ne.symm]

lemma HasStieltjesIntegral.symm_iff :
    HasStieltjesIntegral a b B f g L ↔ HasStieltjesIntegral b a B f g (-L) := by
  unfold HasStieltjesIntegral
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h, Std.not_gt_of_lt h, h.ne, h.ne.symm]
  · simp
  simp [h, Std.not_gt_of_lt h, h.ne, h.ne.symm]

@[symm]
lemma HasStieltjesIntegral.symm (h : HasStieltjesIntegral a b B f g L) :
    HasStieltjesIntegral b a B f g (-L) := by rwa [← symm_iff]

theorem stieltjesIntegrable_ordered_iff_integrable (hab : a < b) :
    StieltjesIntegrable_ordered a b B f g hab ↔
    Integrable (Interval hab) IntegrationParams.Riemann (f <| · 0) (.ofDiff (B.flip <| g ·)) :=
  ⟨fun ⟨_, hL⟩ ↦ HasIntegral.integrable hL, fun h ↦ ⟨_, h.hasIntegral⟩⟩

@[simp]
lemma StieltjesIntegrable.of_eq : StieltjesIntegrable a a B f g := by
  simp [StieltjesIntegrable, HasStieltjesIntegral]

lemma StieltjesIntegrable.of_lt (hab : a < b) :
    StieltjesIntegrable a b B f g ↔ StieltjesIntegrable_ordered a b B f g hab := by
  simp [StieltjesIntegrable, StieltjesIntegrable_ordered, HasStieltjesIntegral.of_lt, hab]

lemma StieltjesIntegrable.symm_iff :
    StieltjesIntegrable a b B f g ↔ StieltjesIntegrable b a B f g := by
  unfold StieltjesIntegrable
  constructor <;> rintro ⟨L, h⟩ <;> exact ⟨-L, h.symm⟩

@[symm]
lemma StieltjesIntegrable.symm (h : StieltjesIntegrable a b B f g) :
    StieltjesIntegrable b a B f g := by rwa [← symm_iff]

lemma StieltjesIntegrable.of_gt (hba : b < a) :
    StieltjesIntegrable a b B f g ↔ StieltjesIntegrable_ordered b a B f g hba := by
  rw [symm_iff]; exact of_lt hba

lemma StieltjesIntegrable.iff_min_max :
    StieltjesIntegrable a b B f g ↔ StieltjesIntegrable (min a b) (max a b) B f g := by
  rcases le_total a b with h | h <;> simp [h, symm_iff]

/-- Uniqueness: the Riemann–Stieltjes integral, when it exists, is unique. -/
theorem HasStieltjesIntegral.unique
    (h₁ : HasStieltjesIntegral a b B f g L₁) (h₂ : HasStieltjesIntegral a b B f g L₂) :
    L₁ = L₂ := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp only [h, of_lt] at h₁ h₂
    exact HasIntegral.unique h₁ h₂
  · simp_all
  symm at h₁ h₂
  simp only [h, of_lt] at h₁ h₂
  exact neg_injective (HasIntegral.unique h₁ h₂)

/-- The existence of a Riemann–Stieltjes integral implies `StieltjesIntegrable`. -/
theorem HasStieltjesIntegral.stieltjesIntegrable
    (h : HasStieltjesIntegral a b B f g L) : StieltjesIntegrable a b B f g := ⟨L, h⟩

/-- A chosen witness extracted from `StieltjesIntegrable`. -/
theorem StieltjesIntegrable.hasStieltjesIntegral (h : StieltjesIntegrable a b B f g) :
    HasStieltjesIntegral a b B f g ∫ˢ x in a..b, f x ∂[B; g] := by
  simp [stieltjesIntegral, h, h.choose_spec]

/-- If `HasStieltjesIntegral a b B f g L`, then `∫ˢ x in a..b, f x ∂[B; g] = L`. -/
theorem HasStieltjesIntegral.stieltjesIntegral_eq
    (h : HasStieltjesIntegral a b B f g L) : ∫ˢ x in a..b, f x ∂[B; g] = L := by
  classical
  simp only [stieltjesIntegral, dif_pos h.stieltjesIntegrable]
  exact h.stieltjesIntegrable.choose_spec.unique h

theorem StieltjesIntegrable.hasStieltjesIntegral_iff (h : StieltjesIntegrable a b B f g) (L : G) :
    HasStieltjesIntegral a b B f g L ↔ ∫ˢ x in a..b, f x ∂[B; g] = L := by
  grind [hasStieltjesIntegral, HasStieltjesIntegral.unique]

@[simp]
theorem stieltjesIntegral.integral_same : ∫ˢ x in a..a, f x ∂[B; g] = 0 :=
  HasStieltjesIntegral.of_eq_iff_zero.mp StieltjesIntegrable.of_eq.hasStieltjesIntegral

@[simp]
theorem stieltjesIntegral.integral_undef (h : ¬StieltjesIntegrable a b B f g) :
    ∫ˢ x in a..b, f x ∂[B; g] = 0 := by simp [stieltjesIntegral, h]

theorem stieltjesIntegral.integral_symm :
    ∫ˢ x in b..a, f x ∂[B; g] = -∫ˢ x in a..b, f x ∂[B; g] := by
  by_cases h_integ : StieltjesIntegrable a b B f g
  · exact (h_integ.hasStieltjesIntegral.symm.unique h_integ.symm.hasStieltjesIntegral).symm
  have h_integ_symm : ¬ StieltjesIntegrable b a B f g := by contrapose! h_integ; exact h_integ.symm
  simp [stieltjesIntegral, h_integ, h_integ_symm]

theorem hasStieltjesIntegral'_congr (hab : a < b)
    (hf : Set.EqOn f₁ f₂ (.Icc a b)) (hg : Set.EqOn g₁ g₂ (.Icc a b)) :
    HasStieltjesIntegral_ordered a b B f₁ g₁ L hab ↔
    HasStieltjesIntegral_ordered a b B f₂ g₂ L hab := by
  unfold HasStieltjesIntegral_ordered
  apply BoxIntegral.hasIntegral_congr
  · intro x hx; exact hf (by simpa [hab] using hx)
  intro J hJ
  simp only [Set.mem_Iic, Box.le_iff₁, interval_lower, interval_upper,
    BoxAdditiveMap.ofDiff_apply] at hJ ⊢
  have := J.lower_lt_upper₁
  congr 2 <;> exact hg (by grind)

theorem hasStieltjesIntegral_congr
    (hf : Set.EqOn f₁ f₂ (.uIcc a b)) (hg : Set.EqOn g₁ g₂ (.uIcc a b)) :
    HasStieltjesIntegral a b B f₁ g₁ L ↔ HasStieltjesIntegral a b B f₂ g₂ L := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · simp only [hab.le, Set.uIcc_of_le, hab, HasStieltjesIntegral.of_lt] at hf hg ⊢
    exact hasStieltjesIntegral'_congr hab hf hg
  · simp
  simp only [HasStieltjesIntegral.symm_iff (a := a) (b := b), hab.le, Set.uIcc_of_ge, hab,
    HasStieltjesIntegral.of_lt] at hf hg ⊢
  exact hasStieltjesIntegral'_congr hab hf hg

theorem stieltjesIntegrable_congr
    (hf : Set.EqOn f₁ f₂ (.uIcc a b)) (hg : Set.EqOn g₁ g₂ (.uIcc a b)) :
    StieltjesIntegrable a b B f₁ g₁ ↔ StieltjesIntegrable a b B f₂ g₂ := by
  simp only [StieltjesIntegrable, hasStieltjesIntegral_congr hf hg]

theorem stieltjesIntegral_congr
    (hf : Set.EqOn f₁ f₂ (.uIcc a b)) (hg : Set.EqOn g₁ g₂ (.uIcc a b)) :
    ∫ˢ x in a..b, f₁ x ∂[B; g₁] = ∫ˢ x in a..b, f₂ x ∂[B; g₂] := by
  by_cases! h : StieltjesIntegrable a b B f₁ g₁
    <;> have h' := h <;> rw [stieltjesIntegrable_congr hf hg] at h'
  · apply h.hasStieltjesIntegral.unique
    simp [hasStieltjesIntegral_congr hf hg, h'.hasStieltjesIntegral]
  simp [stieltjesIntegral, h, h']

end Simple

section Riemann

/-! ## The Riemann integral -/

variable {a b : ℝ} {f f₁ f₂ : ℝ → E} {L L₁ L₂ : E}

theorem HasRiemannIntegral.iff_hasIntegral (hab : a < b) : HasRiemannIntegral a b f L ↔
    HasIntegral (Interval hab) IntegrationParams.Riemann (f <| · 0) BoxAdditiveMap.volume L := by
  simp [HasRiemannIntegral, hab, HasStieltjesIntegral.of_lt, HasStieltjesIntegral_ordered,
    BoxAdditiveMap.ofDiff_lsmul_eq_volume]

lemma RiemannIntegrable_def : RiemannIntegrable a b f ↔ ∃ L, HasRiemannIntegral a b f L := Iff.rfl

lemma HasRiemannIntegral.symm_iff : HasRiemannIntegral a b f L ↔ HasRiemannIntegral b a f (-L) :=
  HasStieltjesIntegral.symm_iff

@[symm]
lemma HasRiemannIntegral.symm (h : HasRiemannIntegral a b f L) :
    HasRiemannIntegral b a f (-L) := HasStieltjesIntegral.symm h

@[symm]
lemma RiemannIntegrable.symm (h : RiemannIntegrable a b f) : RiemannIntegrable b a f :=
  StieltjesIntegrable.symm h

@[simp]
lemma HasRiemannIntegral.of_eq_iff_zero : HasRiemannIntegral a a f L ↔ L = 0 :=
  HasStieltjesIntegral.of_eq_iff_zero

@[simp]
lemma RiemannIntegrable.of_eq : RiemannIntegrable a a f := StieltjesIntegrable.of_eq

@[simp]
theorem riemannIntegral.integral_same : ∫ʳ x in a..a, f x = 0 := stieltjesIntegral.integral_same

theorem RiemannIntegrable.iff_integrable (hab : a < b) : RiemannIntegrable a b f ↔
    Integrable (Interval hab) IntegrationParams.Riemann (f <| · 0) BoxAdditiveMap.volume := by
  simp [RiemannIntegrable_def, Integrable, HasRiemannIntegral.iff_hasIntegral, hab]

theorem HasRiemannIntegral.unique
    (h₁ : HasRiemannIntegral a b f L₁) (h₂ : HasRiemannIntegral a b f L₂) : L₁ = L₂ :=
  HasStieltjesIntegral.unique h₁ h₂

theorem HasRiemannIntegral.riemannIntegrable
    (h : HasRiemannIntegral a b f L) : RiemannIntegrable a b f := ⟨L, h⟩

theorem RiemannIntegrable.hasRiemannIntegral (h : RiemannIntegrable a b f) :
    HasRiemannIntegral a b f (∫ʳ x in a..b, f x) :=
  StieltjesIntegrable.hasStieltjesIntegral h

theorem HasRiemannIntegral.riemannIntegral_eq
    (h : HasRiemannIntegral a b f L) : ∫ʳ x in a..b, f x = L :=
  HasStieltjesIntegral.stieltjesIntegral_eq h

theorem RiemannIntegrable.hasRiemannIntegral_iff (h : RiemannIntegrable a b f) (L : E) :
    HasRiemannIntegral a b f L ↔ ∫ʳ x in a..b, f x = L :=
  StieltjesIntegrable.hasStieltjesIntegral_iff h L

theorem hasRiemannIntegral_congr (hf : Set.EqOn f₁ f₂ (.uIcc a b)) :
    HasRiemannIntegral a b f₁ L ↔ HasRiemannIntegral a b f₂ L :=
  hasStieltjesIntegral_congr hf (Set.graphOn_inj.mp rfl)

theorem riemannIntegrable_congr (hf : Set.EqOn f₁ f₂ (.uIcc a b)) :
    RiemannIntegrable a b f₁ ↔ RiemannIntegrable a b f₂ :=
  stieltjesIntegrable_congr hf (Set.graphOn_inj.mp rfl)

@[simp]
theorem riemannIntegral.integral_undef (h : ¬RiemannIntegrable a b f) :
    ∫ʳ x in a..b, f x = 0 := stieltjesIntegral.integral_undef h

theorem riemannIntegral.integral_symm : ∫ʳ x in b..a, f x = -∫ʳ x in a..b, f x :=
  stieltjesIntegral.integral_symm

end Riemann

end BoxIntegral
