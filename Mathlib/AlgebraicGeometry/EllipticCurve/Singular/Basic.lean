/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!

# Singular cubics

Let `E` be a cubic over an arbitrary field `K`,
given by a Weierstrass equation `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`.

We define `E.singular` as a typeclass containing the data of a singular point.
(Such a point is unique if exists.
See `WeierstrassCurve.IsSingularPoint.ext` or `WeierstrassCurve.Singular.subsingleton`.)

For curves `E` with `[E.Singular]`, we define `E.SplitSingular` to contain the data of
(one of) the tangents at the singular point.

## TODO (Andrew)
- Classify singular cubics

-/

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (E : WeierstrassCurve R)

/-- The predicate of being a singular point on an `WeierstrassCurve` in affine coordinates. -/
def Affine.IsSingularPoint (E : WeierstrassCurve.Affine R) (x y : R) : Prop :=
  E.Equation x y ∧ E.polynomialX.evalEval x y = 0 ∧ E.polynomialY.evalEval x y = 0

lemma Affine.isSingularPoint_iff {E : WeierstrassCurve.Affine R} {x y : R} :
    E.IsSingularPoint x y ↔ E.Equation x y ∧
      E.a₁ * y - (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄) = 0 ∧ 2 * y + E.a₁ * x + E.a₃ = 0 := by
  rw [IsSingularPoint, evalEval_polynomialX, evalEval_polynomialY]

lemma Affine.IsSingularPoint.relation_x
    {E : WeierstrassCurve.Affine R} {x y : R} (h : E.IsSingularPoint x y) :
    E.a₁ * y = 3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ :=
  sub_eq_zero.mp ((Affine.isSingularPoint_iff.mp h).2.1)

lemma Affine.IsSingularPoint.relation_y
    {E : WeierstrassCurve.Affine R} {x y : R} (h : E.IsSingularPoint x y) :
    2 * y + E.a₁ * x + E.a₃ = 0 :=
  (Affine.isSingularPoint_iff.mp h).2.2

variable {E} in
lemma Affine.IsSingularPoint.of_variableChange (f : VariableChange R) {x y}
    (h : (f • E).toAffine.IsSingularPoint x y) :
    E.toAffine.IsSingularPoint
      (f.u ^ 2 * x + f.r) (f.u ^ 3 * y + f.u ^ 2 * f.s * x + f.t) := by
  generalize hE' : f • E = E' at h
  obtain rfl : E = f⁻¹ • E' := eq_inv_smul_iff.mpr hE'
  simp only [isSingularPoint_iff, equation_iff', variableChange_inv_a₁, variableChange_inv_a₃,
    variableChange_inv_a₂, variableChange_inv_a₄, variableChange_inv_a₆, toAffine] at h ⊢
  refine ⟨?_, ?_, ?_⟩
  · linear_combination f.u ^ 6 * h.1
  · linear_combination - f.u ^ 3 * f.s * h.2.2 + f.u ^ 4 * h.2.1
  · linear_combination f.u ^ 3 * h.2.2

variable {E} in
lemma Affine.IsSingularPoint.variableChange (f : VariableChange R) {x y}
    (h : E.toAffine.IsSingularPoint x y) :
    (f • E).toAffine.IsSingularPoint
      (f⁻¹.u ^ 2 * x + f⁻¹.r) (f⁻¹.u ^ 3 * y + f⁻¹.u ^ 2 * f⁻¹.s * x + f⁻¹.t) :=
  .of_variableChange f⁻¹ (by simpa)

/--
We say that a weierstrass curve is singular if it has at least one **rational** singular point.
We show below that the singular point (if exists) is unique, see `Affine.isSingularPoint_ext`.

Warning:
Because of the rationality assumption, it is not true that every curve that is not
nonsingular (i.e. `IsElliptic`) is `Singular`.
(e.g. `y² = x³ - T` is not nonsingular over `𝔽₃(T)` but the cusp is in a degree `3` extension)

Implementation detail:
This contains data for defeq and computable purposes,
but we do have an `Subsingleton` instance on it.
Theorems who doesn't need the defeq should assume `Nonempty E.Singular` instead.
-/
class Singular (E : WeierstrassCurve R) where
  /-- The x coordinate of the singular point. -/
  x : R
  /-- The y coordinate of the singular point. -/
  y : R
  isSingularPoint (E) : E.toAffine.IsSingularPoint x y

alias singularityX := Singular.x
alias singularityY := Singular.y

instance [E.Singular] : Nonempty E.Singular := Nonempty.intro ‹_›

lemma isSingularPoint_singularity (E : WeierstrassCurve R) [E.Singular] :
    E.toAffine.IsSingularPoint E.singularityX E.singularityY :=
  Singular.isSingularPoint E

instance (f : VariableChange R) [Nonempty E.Singular] : Nonempty (f • E).Singular := by
  let _ : E.Singular := Nonempty.some ‹_›
  exact ⟨_, _, E.isSingularPoint_singularity.variableChange f⟩

@[simp]
lemma Δ_of_singular (E : WeierstrassCurve R) [Nonempty E.Singular] : E.Δ = 0 := by
  by_contra h
  obtain ⟨x, y, H⟩ := Nonempty.some ‹_›
  exact not_and_of_not_or_not (((E.toAffine.equation_iff_nonsingular_of_Δ_ne_zero h).mp H.1).2) H.2

variable {E} in
@[simp]
lemma nonempty_singular_variableChange_iff {f : VariableChange R} :
    Nonempty (f • E).Singular ↔ Nonempty E.Singular :=
  ⟨fun _ ↦ by rw [← inv_smul_smul f E]; infer_instance, fun _ ↦ inferInstance⟩

/-- We say that a `WeierstrassCurve` is in singular normal form if it is `y² + a₁xy = x³ + a₂x²`.
Any weierstrass curve with a (rational) singular point can be turned into this normal form.
See `toIsSingularNF`. -/
class IsSingularNF (E : WeierstrassCurve R) : Prop where
  a₃ (E) : E.a₃ = 0
  a₄ (E) : E.a₄ = 0
  a₆ (E) : E.a₆ = 0

section

variable [E.IsSingularNF]

@[simp] alias a₃_of_isSingularNF := IsSingularNF.a₃
@[simp] alias a₄_of_isSingularNF := IsSingularNF.a₄
@[simp] alias a₆_of_isSingularNF := IsSingularNF.a₆
@[simp] lemma b₄_of_isSingularNF : E.b₄ = 0 := by simp [b₄]
@[simp] lemma b₆_of_isSingularNF : E.b₆ = 0 := by simp [b₆]
@[simp] lemma b₈_of_isSingularNF : E.b₈ = 0 := by simp [b₈]
lemma c₄_of_isSingularNF : E.c₄ = E.b₂ ^ 2 := by simp [c₄]
lemma c₆_of_isSingularNF : E.c₆ = - E.b₂ ^ 3 := by simp [c₆]

end

/-- There is an explicit change of variables of a `WeierstrassCurve` to
a singular normal form, provided the existence of a rational singular point. -/
def toIsSingularNF [E.Singular] : VariableChange R where
  u := 1
  r := E.singularityX
  s := 0
  t := E.singularityY

instance toIsSingularNF_spec [E.Singular] : (E.toIsSingularNF • E).IsSingularNF := by
  have := E.isSingularPoint_singularity.variableChange E.toIsSingularNF
  generalize hE' : E.toIsSingularNF • E = E' at this ⊢
  have inst : Nonempty E'.Singular := hE' ▸ inferInstance
  have hE' : E'.toAffine.IsSingularPoint 0 0 := by
    simpa [toIsSingularNF, VariableChange.inv_def] using this
  have H : E'.a₆ = 0 ∧ E'.a₄ = 0 ∧ E'.a₃ = 0 := by simpa [Affine.isSingularPoint_iff] using hE'
  constructor <;> aesop

lemma x_eq_zero_of_isSingularNF [IsReduced R] [E.IsSingularNF] {x y}
    (H : E.toAffine.IsSingularPoint x y) : x = 0 := by
  simp only [toAffine, Affine.isSingularPoint_iff, Affine.equation_iff, a₃_of_isSingularNF,
    zero_mul, add_zero, a₄_of_isSingularNF, a₆_of_isSingularNF] at H
  obtain ⟨H, h₁, h₂⟩ := H
  simpa using show x ^ 3 = 0 by linear_combination 2 * H - x * h₁ - y * h₂

lemma y_eq_zero_of_isSingularNF [IsReduced R] [E.IsSingularNF] {x y}
    (H : E.toAffine.IsSingularPoint x y) : y = 0 := by
  simpa [x_eq_zero_of_isSingularNF E H, Affine.equation_iff] using H.1

lemma isSingularPoint_iff_of_isSingularNF [IsReduced R] [E.IsSingularNF] {x y} :
    E.toAffine.IsSingularPoint x y ↔ x = 0 ∧ y = 0 := by
  refine ⟨fun H ↦ ⟨x_eq_zero_of_isSingularNF E H, y_eq_zero_of_isSingularNF E H⟩, ?_⟩
  rintro ⟨rfl, rfl⟩
  simp [Affine.isSingularPoint_iff, Affine.equation_iff]

@[simp]
lemma singularityX_of_isSingularNF [IsReduced R] [E.IsSingularNF] [E.Singular] :
    E.singularityX = 0 :=
  x_eq_zero_of_isSingularNF E E.isSingularPoint_singularity

@[simp]
lemma singularityY_of_isSingularNF [IsReduced R] [E.IsSingularNF] [E.Singular] :
    E.singularityY = 0 :=
  y_eq_zero_of_isSingularNF E E.isSingularPoint_singularity

/-- A curve in the singular normal form has `(0, 0)` as the singular point. -/
def Singular.ofIsSingularNF [IsReduced R] [E.IsSingularNF] : E.Singular :=
  ⟨0, 0, E.isSingularPoint_iff_of_isSingularNF.mpr (by simp)⟩

instance [IsReduced R] [E.IsSingularNF] : Nonempty E.Singular := ⟨.ofIsSingularNF E⟩

lemma Affine.IsSingularPoint.ext [IsReduced R] {E : Affine R} {x y} {x' y'}
    (H : E.IsSingularPoint x y) (H' : E.IsSingularPoint x' y') :
    x = x' ∧ y = y' := by
  letI : E.Singular := ⟨_, _, H⟩
  constructor
  · simpa [toIsSingularNF, pow_two, VariableChange.mul_def,
      VariableChange.inv_def, add_eq_zero_iff_eq_neg'] using
        (E.toIsSingularNF • E).x_eq_zero_of_isSingularNF (H'.variableChange _)
  · simpa [toIsSingularNF, pow_two, VariableChange.mul_def,
      VariableChange.inv_def, add_eq_zero_iff_eq_neg'] using
        (E.toIsSingularNF • E).y_eq_zero_of_isSingularNF (H'.variableChange _)

instance Singular.subsingleton [IsReduced R] : Subsingleton E.Singular where
  allEq
  | ⟨x, y, H⟩, ⟨x', y', H'⟩ => by
    obtain ⟨rfl, rfl⟩ := H.ext H'
    rfl

@[simp]
lemma singularityX_variableChange [IsReduced R]
    (f : VariableChange R) [E.Singular] [(f • E).Singular] :
    (f • E).singularityX = f⁻¹.u ^ 2 * E.singularityX + f⁻¹.r :=
  ((E.isSingularPoint_singularity.variableChange f).ext
      (f • E).isSingularPoint_singularity).1.symm

@[simp]
lemma singularityY_variableChange [IsReduced R]
    (f : VariableChange R) [E.Singular] [(f • E).Singular] :
    (f • E).singularityY =
      ↑f⁻¹.u ^ 3 * E.singularityY + ↑f⁻¹.u ^ 2 * f⁻¹.s * E.singularityX + f⁻¹.t :=
  ((E.isSingularPoint_singularity.variableChange f).ext
      (f • E).isSingularPoint_singularity).2.symm

/-- We say that a weierstrass curve is split singular if it has a (rational) singular point,
and its tangent lines at the singular point is split in the base field.
We later show that this is unique up to swapping the tangents.

Implementation detail:
This contains data for defeq and computable purposes. -/
class SplitSingular [IsReduced R] (E : WeierstrassCurve R) where
  mk' ::
  nonempty_singular : Nonempty E.Singular := by infer_instance
  /-- The slope of (one of) the tangent line at a singular point. -/
  α : R
  cond' (E) : α ^ 2 + E.a₁ * α - (E.a₂ + 3 * nonempty_singular.some.x) = 0

attribute [instance] SplitSingular.nonempty_singular

/-- The slope of one of the tangent line at a singular point. -/
alias α₁ := SplitSingular.α

/-- The slope of the other the tangent line at a singular point. -/
def α₂ [IsReduced R] [E.SplitSingular] := - E.a₁ - E.α₁

lemma SplitSingular.cond [IsReduced R] (E : WeierstrassCurve R) [E.Singular] [E.SplitSingular] :
    E.α₁ ^ 2 + E.a₁ * E.α₁ - (E.a₂ + 3 * E.singularityX) = 0 := by
  convert cond' E
  exact Subsingleton.elim _ _

/-- Constructor of `SplitSingular` assuming we already have a `Singular` instance. -/
def SplitSingular.mk [IsReduced R] (E : WeierstrassCurve R) [E.Singular]
    (α : R) (cond : α ^ 2 + E.a₁ * α - (E.a₂ + 3 * E.singularityX) = 0) :
    E.SplitSingular :=
  ⟨⟨‹_›⟩, α, by convert cond; exact Subsingleton.elim _ _⟩

variable {E} in
/-- The variable change of a `SplitSingular` weierstrass curve is `SplitSingular`. -/
def SplitSingular.variableChange [IsReduced R] [E.SplitSingular] (f : VariableChange R) :
    (f • E).SplitSingular where
  nonempty_singular := inferInstance
  α := f.u⁻¹ * (E.α₁ - f.s)
  cond' := by
    rw [← singularityX]
    letI := (inferInstanceAs (Nonempty E.Singular)).some
    letI := (inferInstanceAs (Nonempty (f • E).Singular)).some
    simp only [variableChange_a₁, variableChange_a₂, singularityX_variableChange,
      VariableChange.inv_def]
    linear_combination f.u⁻¹ ^ 2 * SplitSingular.cond E

variable {E} in
/-- The other `SplitSingular` instance obtained by swapping the two tangents -/
abbrev SplitSingular.swap [IsReduced R] [E.SplitSingular] : E.SplitSingular where
  α := E.α₂
  cond' := by delta α₁ α₂; linear_combination SplitSingular.cond' E

variable {E} in
lemma SplitSingular.swap_swap [IsReduced R] (H : E.SplitSingular) :
    H.swap.swap = H := by
  cases H; dsimp [swap, α₂, α₁]; congr; simp

lemma SplitSingular.ext [IsDomain R] (h₁ h₂ : E.SplitSingular) :
    h₁ = h₂ ∨ h₁ = h₂.swap := by
  have : (h₁.α - h₂.α) * (h₁.α + h₂.α + E.a₁) = 0 := by
    linear_combination h₁.cond' - h₂.cond'
  refine (mul_eq_zero.mp this).imp ?_ ?_
  all_goals { cases h₁; cases h₂; intro h; congr; dsimp only [α₁, α₂]; linear_combination h }

end WeierstrassCurve
