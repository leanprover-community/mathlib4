/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic

/-! # Riemann–Stieltjes integral

In this file we define the (one-dimensional) Riemann–Stieltjes integral `∫⟨B⟩ x in a..b, f x ∂g`
from `a` to `b` of a function `f : ℝ → E` against an integrator `g : ℝ → F`, paired
by a continuous bilinear map `B : E →L[ℝ] F →L[ℝ] G`.  It is not required that `a < b`.

The notation here is deliberately chosen to mimic the notation `∫ x in a..b, f x ∂μ` for
`IntervalIntegral`.

The bilinear pairing `B` covers the three main variants of
Stieltjes integration that appear in practice:
* **`f` scalar, `g` vector-valued.** Here we take `B = .lsmul ℝ ℝ`
* **`f` vector-valued, `g` scalar.** Here we take `B = (.lsmul ℝ ℝ).flip`.
* **`f` and `g` are both real or both complex.** Here we take `B = .mul ℝ E`.

The `.` here can be removed if `ContinuousLinearMap` is open.

The Riemann integral is the special case `F = ℝ`, `B = (.lsmul ℝ ℝ).flip` and `g = id`.
Separate API is provided for this classical case; alternatively, one can `unfold` the Riemann
integral definitions to access the more general Stieltjes integral API.

The development follows the treatment of Riemann–Stieltjes integration in
Montgomery–Vaughan, *Multiplicative Number Theory I: Classical Theory*, Appendix A.

## Key definitions

* `BoxIntegral.StieltjesIntegrable a b B f g`: the predicate that the integral
`∫⟨B⟩ x in a..b, f x ∂g` exists.
* `BoxIntegral.HasStieltjesIntegral a b B f g L`: the predicate that the integral
`∫⟨B⟩ x in a..b, f x ∂g` exists and equals `L`.
* `BoxIntegral.stieltjesIntegral a b B f g`: the value of `∫⟨B⟩ x in a..b, f x ∂g` if it exists, or
the junk value of `0` otherwise.

## Implementation notes

Mathematically, one can define `∫⟨B⟩ x in a..b, f x ∂g` for `a < b` as the limit of
Riemann-Stieltjes sums `∑ B (f (π.tag x)) (g(x.upper) - g(x.lower))` as the mesh size of the
tagged partition `π` of `(a, b]` tends to `0`.  We implement this via the
`BoxIntegral.HasIntegral` predicate on `Box (Fin 1)`, relying in particular on the differential
`ofDiff g` of `g`, which is implemented as a `BoxAdditiveMap`.

The Riemann--Stieltjes integral is also extended to the `a = b` and `a > b` cases by antisymmetry.
In all cases, we denote the integral by `∫⟨B⟩ x in a..b, f x ∂g`.

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.

## Tags

Stieltjes integral, Riemann–Stieltjes, Riemann integral
-/

@[expose] public section

open ContinuousLinearMap

namespace BoxIntegral

/-! ## Definition of the Riemann--Stieltjes integral -/

variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

section Defs

variable (a b : ℝ) (B : E →L[ℝ] F →L[ℝ] G) (f : ℝ → E) (g : ℝ → F) (L : G)

/-- The (Riemann--)Stieltjes integral of a function `f : ℝ → E` and `g : ℝ → F` given a bilinear
map `B : E → F → G` and endpoints `a`, `b` takes values in `G`.
Initially defined under the implicit assumption that `a < b`. -/
def HasStieltjesIntegral' : Prop :=
  HasIntegral (uIoc a b) IntegrationParams.Riemann
    (fun x ↦ f (x 0)) (BoxAdditiveMap.ofDiff (fun x ↦ B.flip (g x))) L

/-- Extension of the Stieltjes integral to cover the cases `a = b` and `a > b`. Prefer this
notion over `HasStieltjesIntegral'`, as it has a more developed API. -/
def HasStieltjesIntegral : Prop :=
  if a = b then L = 0 else
    if a < b then HasStieltjesIntegral' a b B f g L else
      HasStieltjesIntegral' b a B f g (-L)

/-- `StieltjesIntegrable' a b B f g` asserts that the Riemann–Stieltjes integral of `f` against `g`
paired by `B` over `(a, b]` exists, i.e. some `L` satisfies `HasStieltjesIntegral' a b B f g L`.
-/
def StieltjesIntegrable' : Prop := ∃ L, HasStieltjesIntegral' a b B f g L

/-- `StieltjesIntegrable a b B f g` asserts that the Riemann–Stieltjes integral of `f` against `g`
paired by `B` from `a` to `b` exists, i.e. some `L` satisfies `HasStieltjesIntegral a b B f g L`.

Prefer this over `StieltjesIntegrable'` as it has a better API and remains
useful even outside of the case `a < b`.
-/
def StieltjesIntegrable : Prop := ∃ L, HasStieltjesIntegral a b B f g L

open Classical in
/-- The Riemann–Stieltjes integral of `f` against `g` paired by `B` from `a` to `b`.
Returns the junk value `0` if no such integral exists.
The integral remains meaningful outside of the case `a < b`. -/
noncomputable def stieltjesIntegral : G :=
  if h : StieltjesIntegrable a b B f g then h.choose else 0

/-- Notation for the Riemann–Stieltjes integral. `∫⟨B⟩ x in a..b, f x ∂g` is
`stieltjesIntegral a b B (fun x ↦ f x) g`.
The notation parallels Mathlib's `∫ x in a..b, f x ∂μ` for `intervalIntegral`. -/
scoped notation3 "∫⟨"B"⟩ "(...)" in "a".."b", "r:60:(scoped f => f)" ∂"g:70 =>
  stieltjesIntegral a b B r g

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

/-- `riemannIntegral a b f` is defined to equal `∫⟨(lsmul ℝ ℝ).flip⟩ x in a..b, f x ∂id`.
Use `unfold riemannIntegral` or similar to access the Stieltjes integral API. -/
noncomputable def riemannIntegral : E := ∫⟨(lsmul ℝ ℝ).flip⟩ x in a..b, f x ∂id

end Defs

section Simple

/-! ## Simple properties -/

variable {a b : ℝ} {B : E →L[ℝ] F →L[ℝ] G} {f f₁ f₂ : ℝ → E} {g g₁ g₂ : ℝ → F} {L L₁ L₂ : G}

@[simp]
lemma HasStieltjesIntegral.of_eq_iff_zero : HasStieltjesIntegral a a B f g L ↔ L = 0 := by
  simp [HasStieltjesIntegral]

lemma HasStieltjesIntegral.of_lt (hab : a < b) :
    HasStieltjesIntegral a b B f g L ↔ HasStieltjesIntegral' a b B f g L := by
  simp [HasStieltjesIntegral, hab, hab.ne]

@[simp]
lemma HasStieltjesIntegral.of_gt (hba : b < a) :
    HasStieltjesIntegral a b B f g L ↔ HasStieltjesIntegral' b a B f g (-L) := by
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

theorem stieltjesIntegrable'_iff_integrable : StieltjesIntegrable' a b B f g ↔
    Integrable (uIoc a b) IntegrationParams.Riemann
      (fun x ↦ f (x 0)) (BoxAdditiveMap.ofDiff (fun x ↦ B.flip (g x))) :=
  ⟨fun ⟨_, hL⟩ ↦ HasIntegral.integrable hL, fun h ↦ ⟨_, h.hasIntegral⟩⟩

@[simp]
lemma StieltjesIntegrable.of_eq : StieltjesIntegrable a a B f g := by
  simp [StieltjesIntegrable, HasStieltjesIntegral]

lemma StieltjesIntegrable.of_lt (hab : a < b) :
    StieltjesIntegrable a b B f g ↔ StieltjesIntegrable' a b B f g := by
  simp [StieltjesIntegrable, StieltjesIntegrable', HasStieltjesIntegral.of_lt, hab]

lemma StieltjesIntegrable.symm_iff :
    StieltjesIntegrable a b B f g ↔ StieltjesIntegrable b a B f g := by
  unfold StieltjesIntegrable
  constructor <;> rintro ⟨L, h⟩ <;> exact ⟨-L, h.symm⟩

@[symm]
lemma StieltjesIntegrable.symm (h : StieltjesIntegrable a b B f g) :
    StieltjesIntegrable b a B f g := by rwa [← symm_iff]

lemma StieltjesIntegrable.of_gt (hba : b < a) :
    StieltjesIntegrable a b B f g ↔ StieltjesIntegrable' b a B f g := by
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
    HasStieltjesIntegral a b B f g (∫⟨B⟩ x in a..b, f x ∂g) := by
  simp [stieltjesIntegral, h, h.choose_spec]

/-- If `HasStieltjesIntegral a b B f g L`, then `∫⟨B⟩ x in a..b, f x ∂g = L`. -/
theorem HasStieltjesIntegral.stieltjesIntegral_eq
    (h : HasStieltjesIntegral a b B f g L) : ∫⟨B⟩ x in a..b, f x ∂g = L := by
  classical
  simp only [stieltjesIntegral, dif_pos h.stieltjesIntegrable]
  exact h.stieltjesIntegrable.choose_spec.unique h

theorem StieltjesIntegrable.hasStieltjesIntegral_iff (h : StieltjesIntegrable a b B f g) (L : G) :
    HasStieltjesIntegral a b B f g L ↔ ∫⟨B⟩ x in a..b, f x ∂g = L := by
  grind [hasStieltjesIntegral, HasStieltjesIntegral.unique]

@[simp]
theorem stieltjesIntegral.integral_same : ∫⟨B⟩ x in a..a, f x ∂g = 0 :=
  HasStieltjesIntegral.of_eq_iff_zero.mp StieltjesIntegrable.of_eq.hasStieltjesIntegral

@[simp]
theorem stieltjesIntegral.integral_undef (h : ¬StieltjesIntegrable a b B f g) :
    ∫⟨B⟩ x in a..b, f x ∂g = 0 := by simp [stieltjesIntegral, h]

theorem stieltjesIntegral.integral_symm : ∫⟨B⟩ x in b..a, f x ∂g = -∫⟨B⟩ x in a..b, f x ∂g := by
  by_cases h_integ : StieltjesIntegrable a b B f g
  · exact (h_integ.hasStieltjesIntegral.symm.unique h_integ.symm.hasStieltjesIntegral).symm
  have h_integ_symm : ¬ StieltjesIntegrable b a B f g := by contrapose! h_integ; exact h_integ.symm
  simp [stieltjesIntegral, h_integ, h_integ_symm]

theorem hasStieltjesIntegral'_congr (hab : a < b)
    (hf : Set.EqOn f₁ f₂ (.Icc a b)) (hg : Set.EqOn g₁ g₂ (.Icc a b)) :
    HasStieltjesIntegral' a b B f₁ g₁ L ↔ HasStieltjesIntegral' a b B f₂ g₂ L := by
  unfold HasStieltjesIntegral'
  apply BoxIntegral.hasIntegral_congr
  · intro x hx; exact hf (by simpa [hab, uIoc.Icc_eq] using hx)
  intro J hJ
  simp only [Set.mem_Iic, Box.le_uIoc_iff hab, BoxAdditiveMap.ofDiff_apply] at hJ ⊢
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
    ∫⟨B⟩ x in a..b, f₁ x ∂g₁ = ∫⟨B⟩ x in a..b, f₂ x ∂g₂ := by
  by_cases! h : StieltjesIntegrable a b B f₁ g₁
    <;> have h' := h <;> rw [stieltjesIntegrable_congr hf hg] at h'
  · apply h.hasStieltjesIntegral.unique
    simp [hasStieltjesIntegral_congr hf hg, h'.hasStieltjesIntegral]
  simp [stieltjesIntegral, h, h']

end Simple

section Riemann

/-! ## The Riemann integral -/

variable {a b : ℝ} {f f₁ f₂ : ℝ → E} {L L₁ L₂ : E}

theorem HasRiemannIntegral.iff_hasIntegral (hab : a < b) :
    HasRiemannIntegral a b f L ↔
      HasIntegral (uIoc a b) IntegrationParams.Riemann (fun x ↦ f (x 0))
        BoxAdditiveMap.volume L := by
  simp [HasRiemannIntegral, hab, HasStieltjesIntegral.of_lt, HasStieltjesIntegral',
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
theorem riemannIntegral.integral_same : riemannIntegral a a f = 0 := stieltjesIntegral.integral_same

theorem RiemannIntegrable.iff_integrable (hab : a < b) : RiemannIntegrable a b f ↔
    Integrable (uIoc a b) IntegrationParams.Riemann (fun x ↦ f (x 0)) BoxAdditiveMap.volume := by
  simp [RiemannIntegrable_def, Integrable, HasRiemannIntegral.iff_hasIntegral, hab]

theorem HasRiemannIntegral.unique
    (h₁ : HasRiemannIntegral a b f L₁) (h₂ : HasRiemannIntegral a b f L₂) :
    L₁ = L₂ := HasStieltjesIntegral.unique h₁ h₂

theorem HasRiemannIntegral.riemannIntegrable
    (h : HasRiemannIntegral a b f L) : RiemannIntegrable a b f := ⟨L, h⟩

theorem RiemannIntegrable.hasRiemannIntegral (h : RiemannIntegrable a b f) :
    HasRiemannIntegral a b f (riemannIntegral a b f) :=
  StieltjesIntegrable.hasStieltjesIntegral h

theorem HasRiemannIntegral.riemannIntegral_eq
    (h : HasRiemannIntegral a b f L) : riemannIntegral a b f = L :=
  HasStieltjesIntegral.stieltjesIntegral_eq h

theorem RiemannIntegrable.hasRiemannIntegral_iff (h : RiemannIntegrable a b f) (L : E) :
    HasRiemannIntegral a b f L ↔ riemannIntegral a b f = L :=
  StieltjesIntegrable.hasStieltjesIntegral_iff h L

theorem hasRiemannIntegral_congr (hf : Set.EqOn f₁ f₂ (.uIcc a b)) :
    HasRiemannIntegral a b f₁ L ↔ HasRiemannIntegral a b f₂ L :=
  hasStieltjesIntegral_congr hf (Set.graphOn_inj.mp rfl)

theorem riemannIntegrable_congr (hf : Set.EqOn f₁ f₂ (.uIcc a b)) :
    RiemannIntegrable a b f₁ ↔ RiemannIntegrable a b f₂ :=
  stieltjesIntegrable_congr hf (Set.graphOn_inj.mp rfl)

@[simp]
theorem riemannIntegral.integral_undef (h : ¬RiemannIntegrable a b f) :
    riemannIntegral a b f = 0 := stieltjesIntegral.integral_undef h

theorem riemannIntegral.integral_symm : riemannIntegral b a f = -riemannIntegral a b f :=
  stieltjesIntegral.integral_symm

end Riemann

end BoxIntegral
