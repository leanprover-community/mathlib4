/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

#align_import algebraic_geometry.projective_spectrum.structure_sheaf from "leanprover-community/mathlib"@"486cb2f3bda4a67557c6285f5bd0c3348c1eea81"

/-!
# The structure sheaf on `projective_spectrum 𝒜`.

In `Mathlib.AlgebraicGeometry.Topology`, we have given a topology on `ProjectiveSpectrum 𝒜`; in
this file we will construct a sheaf on `ProjectiveSpectrum 𝒜`.

## Notation
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `𝒜 : ℕ → Submodule R A` is the grading of `A`;
- `U` is opposite object of some open subset of `ProjectiveSpectrum.top`.

## Main definitions and results
We define the structure sheaf as the subsheaf of all dependent function
`f : Π x : U, HomogeneousLocalization 𝒜 x` such that `f` is locally expressible as ratio of two
elements of the *same grading*, i.e. `∀ y ∈ U, ∃ (V ⊆ U) (i : ℕ) (a b ∈ 𝒜 i), ∀ z ∈ V, f z = a / b`.

* `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.isLocallyFraction`: the predicate that
  a dependent function is locally expressible as a ratio of two elements of the same grading.
* `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.sectionsSubring`: the dependent functions
  satisfying the above local property forms a subring of all dependent functions
  `Π x : U, HomogeneousLocalization 𝒜 x`.
* `AlgebraicGeometry.Proj.StructureSheaf`: the sheaf with `U ↦ sectionsSubring U` and natural
  restriction map.

Then we establish that `Proj 𝒜` is a `LocallyRingedSpace`:
* `AlgebraicGeometry.Proj.stalkIso'`: for any `x : ProjectiveSpectrum 𝒜`, the stalk of
  `Proj.StructureSheaf` at `x` is isomorphic to `HomogeneousLocalization 𝒜 x`.
* `AlgebraicGeometry.Proj.toLocallyRingedSpace`: `Proj` as a locally ringed space.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/


noncomputable section

namespace AlgebraicGeometry

open scoped DirectSum Pointwise

open DirectSum SetLike Localization TopCat TopologicalSpace CategoryTheory Opposite

variable {R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

local notation3 "at " x =>
  HomogeneousLocalization.AtPrime 𝒜
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x))

namespace ProjectiveSpectrum.StructureSheaf

variable {𝒜}

/-- The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` of *same grading* in each of the stalks (which are localizations at various prime ideals).
-/
def IsFraction {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : ∀ x : U, at x.1) : Prop :=
  ∃ (i : ℕ) (r s : 𝒜 i) (s_nin : ∀ x : U, s.1 ∉ x.1.asHomogeneousIdeal),
    ∀ x : U, f x = .mk ⟨i, r, s, s_nin x⟩
#align algebraic_geometry.projective_spectrum.structure_sheaf.is_fraction AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.IsFraction
variable (𝒜)

/--
The predicate `IsFraction` is "prelocal", in the sense that if it holds on `U` it holds on any open
subset `V` of `U`.
-/
def isFractionPrelocal : PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => at x where
  pred f := IsFraction f
  res := by rintro V U i f ⟨j, r, s, h, w⟩; exact ⟨j, r, s, (h <| i ·), (w <| i ·)⟩
#align algebraic_geometry.projective_spectrum.structure_sheaf.is_fraction_prelocal AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.isFractionPrelocal

/-- We will define the structure sheaf as the subsheaf of all dependent functions in
`Π x : U, HomogeneousLocalization 𝒜 x` consisting of those functions which can locally be expressed
as a ratio of `A` of same grading. -/
def isLocallyFraction : LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => at x :=
  (isFractionPrelocal 𝒜).sheafify
#align algebraic_geometry.projective_spectrum.structure_sheaf.is_locally_fraction AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.isLocallyFraction

namespace SectionSubring

variable {𝒜}

open Submodule SetLike.GradedMonoid HomogeneousLocalization

theorem zero_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜).pred (0 : ∀ x : U.unop, at x.1) := fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨0, zero_mem _⟩, ⟨1, one_mem_graded _⟩, _, fun _ => rfl⟩⟩
#align algebraic_geometry.projective_spectrum.structure_sheaf.section_subring.zero_mem' AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.zero_mem'

theorem one_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜).pred (1 : ∀ x : U.unop, at x.1) := fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨1, one_mem_graded _⟩, ⟨1, one_mem_graded _⟩, _, fun _ => rfl⟩⟩
#align algebraic_geometry.projective_spectrum.structure_sheaf.section_subring.one_mem' AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.one_mem'

theorem add_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : ∀ x : U.unop, at x.1)
    (ha : (isLocallyFraction 𝒜).pred a) (hb : (isLocallyFraction 𝒜).pred b) :
    (isLocallyFraction 𝒜).pred (a + b) := fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, hwa, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, hwb, wb⟩
  refine
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨sb * ra + sa * rb,
        add_mem (add_comm jb ja ▸ mul_mem_graded sb_mem ra_mem : sb * ra ∈ 𝒜 (ja + jb))
          (mul_mem_graded sa_mem rb_mem)⟩,
      ⟨sa * sb, mul_mem_graded sa_mem sb_mem⟩, fun y ↦
        y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩),
      fun y => ?_⟩
  simp only at wa wb
  simp only [Pi.add_apply, wa ⟨y.1, y.2.1⟩, wb ⟨y.1, y.2.2⟩, ext_iff_val,
    val_add, val_mk, add_mk, add_comm (sa * rb)]
  rfl
#align algebraic_geometry.projective_spectrum.structure_sheaf.section_subring.add_mem' AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.add_mem'

theorem neg_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a : ∀ x : U.unop, at x.1)
    (ha : (isLocallyFraction 𝒜).pred a) : (isLocallyFraction 𝒜).pred (-a) := fun x => by
  rcases ha x with ⟨V, m, i, j, ⟨r, r_mem⟩, ⟨s, s_mem⟩, nin, hy⟩
  refine ⟨V, m, i, j, ⟨-r, Submodule.neg_mem _ r_mem⟩, ⟨s, s_mem⟩, nin, fun y => ?_⟩
  simp only [ext_iff_val, val_mk] at hy
  simp only [Pi.neg_apply, ext_iff_val, val_neg, hy, val_mk, neg_mk]
#align algebraic_geometry.projective_spectrum.structure_sheaf.section_subring.neg_mem' AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.neg_mem'

theorem mul_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : ∀ x : U.unop, at x.1)
    (ha : (isLocallyFraction 𝒜).pred a) (hb : (isLocallyFraction 𝒜).pred b) :
    (isLocallyFraction 𝒜).pred (a * b) := fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, hwa, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, hwb, wb⟩
  refine
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨ra * rb, SetLike.mul_mem_graded ra_mem rb_mem⟩,
      ⟨sa * sb, SetLike.mul_mem_graded sa_mem sb_mem⟩, fun y =>
      y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩),
      fun y ↦ ?_⟩
  simp only [Pi.mul_apply, wa ⟨y.1, y.2.1⟩, wb ⟨y.1, y.2.2⟩, ext_iff_val, val_mul, val_mk,
    Localization.mk_mul]
  rfl
#align algebraic_geometry.projective_spectrum.structure_sheaf.section_subring.mul_mem' AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.mul_mem'

end SectionSubring

section

open SectionSubring

variable {𝒜}

/-- The functions satisfying `isLocallyFraction` form a subring of all dependent functions
`Π x : U, HomogeneousLocalization 𝒜 x`. -/
def sectionsSubring (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Subring (∀ x : U.unop, at x.1) where
  carrier := {f | (isLocallyFraction 𝒜).pred f}
  zero_mem' := zero_mem' U
  one_mem' := one_mem' U
  add_mem' := add_mem' U _ _
  neg_mem' := neg_mem' U _
  mul_mem' := mul_mem' U _ _
#align algebraic_geometry.projective_spectrum.structure_sheaf.sections_subring AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.sectionsSubring

end

/-- The structure sheaf (valued in `Type`, not yet `CommRing`) is the subsheaf consisting of
functions satisfying `isLocallyFraction`. -/
def structureSheafInType : Sheaf (Type _) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜)
#align algebraic_geometry.projective_spectrum.structure_sheaf.structure_sheaf_in_Type AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.structureSheafInType

instance commRingStructureSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    CommRing ((structureSheafInType 𝒜).1.obj U) :=
  (sectionsSubring U).toCommRing
#align algebraic_geometry.projective_spectrum.structure_sheaf.comm_ring_structure_sheaf_in_Type_obj AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.commRingStructureSheafInTypeObj

/-- The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type` valued
structure presheaf. -/
@[simps]
def structurePresheafInCommRing : Presheaf CommRingCat (ProjectiveSpectrum.top 𝒜) where
  obj U := CommRingCat.of ((structureSheafInType 𝒜).1.obj U)
  map i :=
    { toFun := (structureSheafInType 𝒜).1.map i
      map_zero' := rfl
      map_add' := fun x y => rfl
      map_one' := rfl
      map_mul' := fun x y => rfl }
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.projective_spectrum.structure_sheaf.structure_presheaf_in_CommRing AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.structurePresheafInCommRing

-- These lemmas have always been bad (#7657), but leanprover/lean4#2644 made `simp` start noticing
attribute [nolint simpNF]
  AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.structurePresheafInCommRing_map_apply

/-- Some glue, verifying that the structure presheaf valued in `CommRing` agrees with the `Type`
valued structure presheaf. -/
def structurePresheafCompForget :
    structurePresheafInCommRing 𝒜 ⋙ forget CommRingCat ≅ (structureSheafInType 𝒜).1 :=
  NatIso.ofComponents (fun U => Iso.refl _) (by aesop_cat)
#align algebraic_geometry.projective_spectrum.structure_sheaf.structure_presheaf_comp_forget AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.structurePresheafCompForget

end ProjectiveSpectrum.StructureSheaf

namespace ProjectiveSpectrum

open TopCat.Presheaf ProjectiveSpectrum.StructureSheaf Opens

/-- The structure sheaf on `Proj` 𝒜, valued in `CommRing`. -/
def Proj.structureSheaf : Sheaf CommRingCat (ProjectiveSpectrum.top 𝒜) :=
  ⟨structurePresheafInCommRing 𝒜,
    (-- We check the sheaf condition under `forget CommRing`.
          isSheaf_iff_isSheaf_comp
          _ _).mpr
      (isSheaf_of_iso (structurePresheafCompForget 𝒜).symm (structureSheafInType 𝒜).cond)⟩
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.projective_spectrum.Proj.structure_sheaf AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf

end ProjectiveSpectrum

section

open ProjectiveSpectrum ProjectiveSpectrum.StructureSheaf Opens

section
variable {U V : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (i : V ⟶ U)
    (s t : (Proj.structureSheaf 𝒜).1.obj V) (x : V.unop)

@[simp]
theorem Proj.res_apply (x) : ((Proj.structureSheaf 𝒜).1.map i s).1 x = s.1 (i.unop x) := rfl
#align algebraic_geometry.res_apply AlgebraicGeometry.Proj.res_apply

@[ext] theorem Proj.ext (h : s.1 = t.1) : s = t := Subtype.ext h
@[simp] theorem Proj.add_apply : (s + t).1 x = s.1 x + t.1 x := rfl
@[simp] theorem Proj.mul_apply : (s * t).1 x = s.1 x * t.1 x := rfl
@[simp] theorem Proj.sub_apply : (s - t).1 x = s.1 x - t.1 x := rfl
@[simp] theorem Proj.pow_apply (n : ℕ) : (s ^ n).1 x = s.1 x ^ n := rfl
@[simp] theorem Proj.zero_apply : (0 : (Proj.structureSheaf 𝒜).1.obj V).1 x = 0 := rfl
@[simp] theorem Proj.one_apply : (1 : (Proj.structureSheaf 𝒜).1.obj V).1 x = 1 := rfl

end

/-- `Proj` of a graded ring as a `SheafedSpace`-/
def Proj.toSheafedSpace : SheafedSpace CommRingCat where
  carrier := TopCat.of (ProjectiveSpectrum 𝒜)
  presheaf := (Proj.structureSheaf 𝒜).1
  IsSheaf := (Proj.structureSheaf 𝒜).2
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Proj.to_SheafedSpace AlgebraicGeometry.Proj.toSheafedSpace

/-- The ring homomorphism that takes a section of the structure sheaf of `Proj` on the open set `U`,
implemented as a subtype of dependent functions to localizations at homogeneous prime ideals, and
evaluates the section on the point corresponding to a given homogeneous prime ideal. -/
def openToLocalization (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : ProjectiveSpectrum.top 𝒜)
    (hx : x ∈ U) : (Proj.structureSheaf 𝒜).1.obj (op U) ⟶ CommRingCat.of (at x) where
  toFun s := (s.1 ⟨x, hx⟩ : _)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
#align algebraic_geometry.open_to_localization AlgebraicGeometry.openToLocalization

/-- The ring homomorphism from the stalk of the structure sheaf of `Proj` at a point corresponding
to a homogeneous prime ideal `x` to the *homogeneous localization* at `x`,
formed by gluing the `openToLocalization` maps. -/
def stalkToFiberRingHom (x : ProjectiveSpectrum.top 𝒜) :
    (Proj.structureSheaf 𝒜).presheaf.stalk x ⟶ CommRingCat.of (at x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (Proj.structureSheaf 𝒜).1)
    { pt := _
      ι :=
        { app := fun U =>
            openToLocalization 𝒜 ((OpenNhds.inclusion _).obj U.unop) x U.unop.2 } }
#align algebraic_geometry.stalk_to_fiber_ring_hom AlgebraicGeometry.stalkToFiberRingHom

@[simp]
theorem germ_comp_stalkToFiberRingHom (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : U) :
    (Proj.structureSheaf 𝒜).presheaf.germ x ≫ stalkToFiberRingHom 𝒜 x =
      openToLocalization 𝒜 U x x.2 :=
  Limits.colimit.ι_desc _ _
#align algebraic_geometry.germ_comp_stalk_to_fiber_ring_hom AlgebraicGeometry.germ_comp_stalkToFiberRingHom

@[simp]
theorem stalkToFiberRingHom_germ' (U : Opens (ProjectiveSpectrum.top 𝒜))
    (x : ProjectiveSpectrum.top 𝒜) (hx : x ∈ U) (s : (Proj.structureSheaf 𝒜).1.obj (op U)) :
    stalkToFiberRingHom 𝒜 x ((Proj.structureSheaf 𝒜).presheaf.germ ⟨x, hx⟩ s) = (s.1 ⟨x, hx⟩ : _) :=
  RingHom.ext_iff.1 (germ_comp_stalkToFiberRingHom 𝒜 U ⟨x, hx⟩ : _) s
#align algebraic_geometry.stalk_to_fiber_ring_hom_germ' AlgebraicGeometry.stalkToFiberRingHom_germ'

@[simp]
theorem stalkToFiberRingHom_germ (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : U)
    (s : (Proj.structureSheaf 𝒜).1.obj (op U)) :
    stalkToFiberRingHom 𝒜 x ((Proj.structureSheaf 𝒜).presheaf.germ x s) = s.1 x :=
  stalkToFiberRingHom_germ' 𝒜 U _ _ _
#align algebraic_geometry.stalk_to_fiber_ring_hom_germ AlgebraicGeometry.stalkToFiberRingHom_germ

theorem mem_basicOpen_den (x : ProjectiveSpectrum.top 𝒜)
    (f : HomogeneousLocalization.NumDenSameDeg 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl) :
    x ∈ ProjectiveSpectrum.basicOpen 𝒜 f.den := by
  rw [ProjectiveSpectrum.mem_basicOpen]
  exact f.den_mem
#align algebraic_geometry.homogeneous_localization.mem_basic_open AlgebraicGeometry.mem_basicOpen_den

/-- Given a point `x` corresponding to a homogeneous prime ideal, there is a (dependent) function
such that, for any `f` in the homogeneous localization at `x`, it returns the obvious section in the
basic open set `D(f.den)`-/
def sectionInBasicOpen (x : ProjectiveSpectrum.top 𝒜) :
    ∀ f : HomogeneousLocalization.NumDenSameDeg 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl,
    (Proj.structureSheaf 𝒜).1.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f.den)) :=
  fun f =>
  ⟨fun y => HomogeneousLocalization.mk ⟨f.deg, f.num, f.den, y.2⟩, fun y =>
    ⟨ProjectiveSpectrum.basicOpen 𝒜 f.den, y.2,
      ⟨𝟙 _, ⟨f.deg, ⟨f.num, f.den, _, fun _ => rfl⟩⟩⟩⟩⟩
#align algebraic_geometry.section_in_basic_open AlgebraicGeometry.sectionInBasicOpen

open HomogeneousLocalization in
/-- Given any point `x` and `f` in the homogeneous localization at `x`, there is an element in the
stalk at `x` obtained by `sectionInBasicOpen`. This is the inverse of `stalkToFiberRingHom`.
-/
def homogeneousLocalizationToStalk (x : ProjectiveSpectrum.top 𝒜) (y : at x) :
    (Proj.structureSheaf 𝒜).presheaf.stalk x := Quotient.liftOn' y (fun f =>
  (Proj.structureSheaf 𝒜).presheaf.germ ⟨x, mem_basicOpen_den _ x f⟩ (sectionInBasicOpen _ x f))
  fun f g (e : f.embedding = g.embedding) ↦ by
    simp only [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
      IsLocalization.mk'_eq_iff_eq,
      IsLocalization.eq_iff_exists x.asHomogeneousIdeal.toIdeal.primeCompl] at e
    obtain ⟨⟨c, hc⟩, hc'⟩ := e
    apply (Proj.structureSheaf 𝒜).presheaf.germ_ext
      (ProjectiveSpectrum.basicOpen 𝒜 f.den.1 ⊓
        ProjectiveSpectrum.basicOpen 𝒜 g.den.1 ⊓ ProjectiveSpectrum.basicOpen 𝒜 c)
      ⟨⟨mem_basicOpen_den _ x f, mem_basicOpen_den _ x g⟩, hc⟩
      (homOfLE inf_le_left ≫ homOfLE inf_le_left) (homOfLE inf_le_left ≫ homOfLE inf_le_right)
    apply Subtype.ext
    ext ⟨t, ⟨htf, htg⟩, ht'⟩
    rw [Proj.res_apply, Proj.res_apply]
    simp only [sectionInBasicOpen, HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
      IsLocalization.mk'_eq_iff_eq]
    apply (IsLocalization.map_units (M := t.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization t.asHomogeneousIdeal.toIdeal.primeCompl) ⟨c, ht'⟩).mul_left_cancel
    rw [← map_mul, ← map_mul, hc']
#align algebraic_geometry.homogeneous_localization_to_stalk AlgebraicGeometry.homogeneousLocalizationToStalk

lemma homogeneousLocalizationToStalk_stalkToFiberRingHom (x z) :
    homogeneousLocalizationToStalk 𝒜 x (stalkToFiberRingHom 𝒜 x z) = z := by
  obtain ⟨U, hxU, s, rfl⟩ := (Proj.structureSheaf 𝒜).presheaf.germ_exist x z
  obtain ⟨V, hxV, i, n, a, b, h, e⟩ := s.2 ⟨x, hxU⟩
  simp only at e
  rw [stalkToFiberRingHom_germ', homogeneousLocalizationToStalk, e ⟨x, hxV⟩, Quotient.liftOn'_mk'']
  refine Presheaf.germ_ext _ V hxV (by exact homOfLE <| fun _ h' ↦ h ⟨_, h'⟩) i ?_
  apply Subtype.ext
  ext ⟨t, ht⟩
  rw [Proj.res_apply, Proj.res_apply]
  simp only [sectionInBasicOpen, HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_iff_eq, e ⟨t, ht⟩]

lemma stalkToFiberRingHom_homogeneousLocalizationToStalk (x z) :
    stalkToFiberRingHom 𝒜 x (homogeneousLocalizationToStalk 𝒜 x z) = z := by
  obtain ⟨z, rfl⟩ := Quotient.surjective_Quotient_mk'' z
  rw [homogeneousLocalizationToStalk, Quotient.liftOn'_mk'',
    stalkToFiberRingHom_germ', sectionInBasicOpen]

/-- Using `homogeneousLocalizationToStalk`, we construct a ring isomorphism between stalk at `x`
and homogeneous localization at `x` for any point `x` in `Proj`. -/
def Proj.stalkIso' (x : ProjectiveSpectrum.top 𝒜) :
    (Proj.structureSheaf 𝒜).presheaf.stalk x ≃+* at x where
  __ := stalkToFiberRingHom _ x
  invFun := homogeneousLocalizationToStalk 𝒜 x
  left_inv := homogeneousLocalizationToStalk_stalkToFiberRingHom 𝒜 x
  right_inv := stalkToFiberRingHom_homogeneousLocalizationToStalk 𝒜 x
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Proj.stalk_iso' AlgebraicGeometry.Proj.stalkIso'

@[simp]
theorem Proj.stalkIso'_germ' (U : Opens (ProjectiveSpectrum.top 𝒜))
    (x : ProjectiveSpectrum.top 𝒜) (hx : x ∈ U) (s : (Proj.structureSheaf 𝒜).1.obj (op U)) :
    Proj.stalkIso' 𝒜 x ((Proj.structureSheaf 𝒜).presheaf.germ ⟨x, hx⟩ s) = (s.1 ⟨x, hx⟩ : _) :=
  stalkToFiberRingHom_germ' 𝒜 U x hx s

@[simp]
theorem Proj.stalkIso'_germ (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : U)
    (s : (Proj.structureSheaf 𝒜).1.obj (op U)) :
    Proj.stalkIso' 𝒜 x ((Proj.structureSheaf 𝒜).presheaf.germ x s) = s.1 x :=
  stalkToFiberRingHom_germ' 𝒜 U x x.2 s

@[simp]
theorem Proj.stalkIso'_symm_mk (x) (f) :
    (Proj.stalkIso' 𝒜 x).symm (.mk f) = (Proj.structureSheaf 𝒜).presheaf.germ
      ⟨x, mem_basicOpen_den _ x f⟩ (sectionInBasicOpen _ x f) := rfl

/-- `Proj` of a graded ring as a `LocallyRingedSpace`-/
def Proj.toLocallyRingedSpace : LocallyRingedSpace :=
  { Proj.toSheafedSpace 𝒜 with
    localRing := fun x =>
      @RingEquiv.localRing _ _ _ (show LocalRing (at x) from inferInstance) _
        (Proj.stalkIso' 𝒜 x).symm }
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Proj.to_LocallyRingedSpace AlgebraicGeometry.Proj.toLocallyRingedSpace

end

end AlgebraicGeometry
