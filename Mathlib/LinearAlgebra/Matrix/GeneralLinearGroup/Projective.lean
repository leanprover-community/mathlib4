/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Edison Xie
-/
module

public import Mathlib.Data.Sign.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Projective general linear group

In this file we define `Matrix.ProjGenLinGroup n R` as the quotient of `GL n R` by its center.
We introduce notation `PGL(n, R)` for this group,
which works if `n` is either a finite type or a natural number.
If `n` is a number, then `PGL(n, R)` is interpreted as `PGL(Fin n, R)`.

## Main definitions

* `Matrix.SpecialLinearGroup.toPGL` is the natural map from `SL(n, R)` to `PGL(n, R)`.

* `Matrix.ProjectiveSpecialLinearGroup.toPGL` is the natural
  inclusion from `PSL(n, R)` to `PGL(n, R)`.

* `Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed` is an isomorphism between
  `PGL(n, F)` and `PSL(n, F)` in the case of an algebraically closed field.

-/

open scoped MatrixGroups

@[expose] public section

namespace Matrix

/-- Projective general linear group $PGL(n, R)$
defined as the quotient of the general linear group by its center. -/
def ProjGenLinGroup (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] : Type _ :=
  GL n R ⧸ Subgroup.center (GL n R)
  deriving Group

@[inherit_doc]
scoped[MatrixGroups] notation "PGL(" n ", " R ")" => Matrix.ProjGenLinGroup n R

@[inherit_doc]
scoped[MatrixGroups] notation "PGL(" n ", " R ")" => Matrix.ProjGenLinGroup (Fin n) R

namespace ProjGenLinGroup
variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The natural projection from `GL n R` to `PGL n R`. -/
def mk : GL n R →* PGL(n, R) := QuotientGroup.mk' (Subgroup.center (GL n R))

theorem mk_surjective : Function.Surjective (mk : GL n R → PGL(n, R)) :=
  Quotient.mk_surjective

lemma mk_eq_mk_iff' {g₁ g₂ : GL n R} :
    mk g₁ = mk g₂ ↔ ∃ z ∈ Subgroup.center (GL n R), g₁ * z = g₂ :=
  QuotientGroup.mk'_eq_mk' (Subgroup.center (GL n R))

lemma mk_eq_mk_iff {g₁ g₂ : GL n R} :
    mk g₁ = mk g₂ ↔ ∃ u : Rˣ, g₁ * .scalar n u = g₂ := by
  simp [mk_eq_mk_iff', Matrix.GeneralLinearGroup.center_eq_range_scalar]

@[simp]
theorem ker_mk : mk.ker = Subgroup.center (GL n R) := QuotientGroup.ker_mk' _

@[simp]
theorem mk_eq_one {g : GL n R} : mk g = 1 ↔ g ∈ Subgroup.center (GL n R) := by
  rw [← MonoidHom.mem_ker, ker_mk]

@[simp]
lemma mk_one : mk (1 : GL n R) = 1 := rfl

@[simp]
theorem mk_scalar (u : Rˣ) : mk (.scalar n u) = 1 := by
  rw [← MonoidHom.mem_ker, ker_mk, GeneralLinearGroup.center_eq_range_scalar]
  simp

@[elab_as_elim, cases_eliminator]
theorem induction_on {motive : PGL(n, R) → Prop} (g : PGL(n, R))
    (mk : ∀ g : GL n R, motive (ProjGenLinGroup.mk g)) : motive g :=
  Quotient.inductionOn g mk

end ProjGenLinGroup

section isoPSL

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

open Matrix.ProjGenLinGroup

namespace SpecialLinearGroup

/-- The natural map from `SL(n, R)` to `PGL(n, R)` by composing the maps from `SL` to `GL` and the
  quotient map from `GL` to `PGL`. -/
abbrev toPGL : SpecialLinearGroup n R →* PGL(n, R) := mk.comp toGL

lemma toPGL_ker : toPGL.ker = Subgroup.center (SpecialLinearGroup n R) := by
  ext; simp [toGL_mem_center_iff]

end SpecialLinearGroup

namespace ProjectiveSpecialLinearGroup

open Matrix.SpecialLinearGroup

/-- The natural inclusion map from `PSL(n, R)` to `PGL(n, R)` induced by the inclusion
  map from `SL(n, R)` to `GL(n, R)`. -/
def toPGL : ProjectiveSpecialLinearGroup n R →* PGL(n, R) :=
  QuotientGroup.lift _ SpecialLinearGroup.toPGL <| le_of_eq toPGL_ker.symm

@[simp]
lemma toPGL_mk (g : SpecialLinearGroup n R) :
    ProjectiveSpecialLinearGroup.toPGL g = mk (toGL g) := rfl

lemma toPGL_injective :
    Function.Injective (ProjectiveSpecialLinearGroup.toPGL (n := n) (R := R)) :=
  QuotientGroup.injective_lift_iff _ _ _ |>.2 toPGL_ker.symm

lemma toPGL_surj_of_roots
    (hR : ∀ r : Rˣ, ∃ k : Rˣ, k ^ Fintype.card n = r) :
    Function.Surjective (ProjectiveSpecialLinearGroup.toPGL (n := n) (R := R)) := fun g ↦ by
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  obtain ⟨r, hr⟩ : ∃ r : Rˣ, r ^ Fintype.card n * g.det = 1 := by
    obtain ⟨r, hr⟩ := hR g.det⁻¹
    exact ⟨r, by simpa [mul_eq_one_iff_eq_inv] using hr⟩
  simp only [Units.ext_iff, Units.val_mul, Units.val_pow_eq_pow_val,
    GeneralLinearGroup.val_det_apply, ← Matrix.det_smul g.1 r.1, Units.val_one] at hr
  use QuotientGroup.mk ⟨r.1 • g.1, hr⟩
  simp only [ProjectiveSpecialLinearGroup.toPGL_mk, mk_eq_mk_iff]
  refine ⟨r⁻¹, Units.ext ?_⟩
  simp only [Units.val_mul, coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar]
  simp [← Matrix.mul_smul, ← Matrix.diagonal_smul, Pi.smul_def, smul_eq_mul]

lemma toPGL_surj_iff [Nonempty n] :
    Function.Surjective (ProjectiveSpecialLinearGroup.toPGL (n := n) (R := R)) ↔
      ∀ r : Rˣ, ∃ k : Rˣ, k ^ Fintype.card n = r := by
  refine ⟨fun h r ↦ ?_, ProjectiveSpecialLinearGroup.toPGL_surj_of_roots⟩
  obtain ⟨A, hA⟩ := GeneralLinearGroup.det_surjective (n := n) r
  obtain ⟨X, hX⟩ := h (.mk A)
  induction X using QuotientGroup.induction_on with | H X =>
  obtain ⟨u, hu⟩ : ∃ u, toGL X * (GeneralLinearGroup.scalar n) u = A := by
    simpa [mk_eq_mk_iff] using hX
  exact ⟨u, by simpa [hA] using congr(Matrix.GeneralLinearGroup.det $hu)⟩

open Polynomial in
/-- An isomorphism between `PGL(n, F)` and `PSL(n, F)` in the case of an algebraically closed field
  induced from the natural inclusion map. -/
noncomputable def isoPSLOfAlgClosedOfNonempty [Nonempty n] {F : Type*} [Field F] [IsAlgClosed F] :
    PGL(n, F) ≃* ProjectiveSpecialLinearGroup n F :=
  MulEquiv.symm (MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
    ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
    Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r => by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ Fintype.card n - C r.1 : F[X]) (by
    simp [Polynomial.degree_X_pow_sub_C Fintype.card_pos])
  have hx' : x ≠ 0 := by aesop
  exact ⟨⟨x, x⁻¹, mul_inv_cancel₀ hx', inv_mul_cancel₀ hx'⟩, by
    simpa [Units.ext_iff, sub_eq_zero] using hx⟩⟩)

/-- An isomorphism between `PGL(n, F)` and `PSL(n, F)` in the case of an algebraically closed field
  induced from the natural inclusion map where when `n` is empty it gives a junk isomorphism. -/
noncomputable def isoPSLOfAlgClosed {F : Type*} [Field F] [IsAlgClosed F] :
    PGL(n, F) ≃* ProjectiveSpecialLinearGroup n F :=
  open scoped Classical in
  if h : Nonempty n then isoPSLOfAlgClosedOfNonempty else
  have : IsEmpty n := by simpa using h
  have : Subsingleton (PGL(n, F)) := mk_surjective.subsingleton
  MulEquiv.symm (MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
    ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective, Function.surjective_to_subsingleton _⟩)

end ProjectiveSpecialLinearGroup

end isoPSL

namespace ProjGenLinGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] {M : Type*} [Monoid M]

/-- Lift a monoid homomorphism `f : GL n R →* M` that vanishes on all scalar matrices
to a homomorphism from `PGL(n, R)`. -/
def lift (f : GL n R →* M) (hf : f.comp (GeneralLinearGroup.scalar n) = 1) :
    PGL(n, R) →* M :=
  QuotientGroup.lift _ f <| by
    rwa [GeneralLinearGroup.center_eq_range_scalar, MonoidHom.range_le_ker_iff]

@[simp]
theorem lift_mk {f : GL n R →* M} (hf) (g : GL n R) : lift f hf (mk g) = f g := by
  rfl

@[simp]
theorem lift_comp_mk {f : GL n R →* M} (hf) : (lift f hf).comp mk = f := by
  rfl

/-- Given an action of `GL n R` such that the scalar matrices act trivially,
define an action of `PGL n R`. -/
@[instance_reducible]
def mulActionOfGL {α : Type*} [MulAction (GL n R) α]
    (h : ∀ (u : Rˣ) (a : α), GeneralLinearGroup.scalar n u • a = a) :
    MulAction (PGL(n, R)) α :=
  .ofEndHom <| lift MulAction.toEndHom <| by
    ext u
    funext a -- TODO: should we add an `ext` lemma for `Function.End`?
    exact h u a

theorem mk_smul {α : Type*} [MulAction (GL n R) α] (h) (g : GL n R) (a : α) :
    letI : MulAction (PGL(n, R)) α := mulActionOfGL h
    mk g • a = g • a := by
  rfl

/-- The monoid hom between `PGL(n, R)` and `PGL(n, S)` induced by a
  ring homomorphism `f : R →+* S`. -/
def map {S : Type*} [CommRing S] (f : R →+* S) : PGL(n, R) →* PGL(n, S) :=
  QuotientGroup.map _ _ (GeneralLinearGroup.map (n := n) f) <| GeneralLinearGroup.map_center_le f

@[simp]
lemma map_id : map (RingHom.id R) = MonoidHom.id (PGL(n, R)) := QuotientGroup.map_id _

@[simp]
lemma map_mk {S : Type*} [CommRing S] (f : R →+* S) (g : GL n R) :
    map f (mk g) = mk (GeneralLinearGroup.map f g) := rfl

lemma map_comp {S T : Type*} [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    map (n := n) (g.comp f) = (map g).comp (map f) := by
  ext g
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk g => simp

variable [Fact (Even (Fintype.card n))] [LinearOrder R] [IsStrictOrderedRing R]

/-- In case of an even dimension, the sign of the determinant of `g : PGL(n, R)` is well-defined. -/
def signDet : PGL(n, R) →* SignTypeˣ :=
  lift ((Units.map signHom.toMonoidHom).comp GeneralLinearGroup.det) <| by
    ext u
    simp [← sign_pow, Even.pow_pos Fact.out]

theorem signDet_mk (g : GL n R) : signDet (mk g) = Units.map signHom.toMonoidHom g.det := by
  rfl

@[simp]
theorem val_signDet_mk (g : GL n R) : (signDet (mk g) : SignType) = .sign g.det.val := by
  rfl

end ProjGenLinGroup

end Matrix
