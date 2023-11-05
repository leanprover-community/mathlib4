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

open scoped DirectSum BigOperators Pointwise

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
  ∃ (i : ℕ) (r s : 𝒜 i),
    ∀ x : U, ∃ s_nin : s.1 ∉ x.1.asHomogeneousIdeal, f x = Quotient.mk'' ⟨i, r, s, s_nin⟩
variable (𝒜)

/--
The predicate `IsFraction` is "prelocal", in the sense that if it holds on `U` it holds on any open
subset `V` of `U`.
-/
def isFractionPrelocal : PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => at x where
  pred f := IsFraction f
  res := by rintro V U i f ⟨j, r, s, w⟩; exact ⟨j, r, s, fun y => w (i y)⟩

/-- We will define the structure sheaf as the subsheaf of all dependent functions in
`Π x : U, HomogeneousLocalization 𝒜 x` consisting of those functions which can locally be expressed
as a ratio of `A` of same grading.-/
def isLocallyFraction : LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => at x :=
  (isFractionPrelocal 𝒜).sheafify

namespace SectionSubring

variable {𝒜}

open Submodule SetLike.GradedMonoid HomogeneousLocalization

theorem zeroMem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜).pred (0 : ∀ x : U.unop, at x.1) := fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨0, zero_mem _⟩, ⟨1, one_mem_graded _⟩, fun _ => ⟨_, rfl⟩⟩⟩

theorem oneMem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜).pred (1 : ∀ x : U.unop, at x.1) := fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨1, one_mem_graded _⟩, ⟨1, one_mem_graded _⟩, fun _ => ⟨_, rfl⟩⟩⟩

theorem addMem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : ∀ x : U.unop, at x.1)
    (ha : (isLocallyFraction 𝒜).pred a) (hb : (isLocallyFraction 𝒜).pred b) :
    (isLocallyFraction 𝒜).pred (a + b) := fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, wb⟩
  refine'
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨sb * ra + sa * rb,
        add_mem (add_comm jb ja ▸ mul_mem_graded sb_mem ra_mem : sb * ra ∈ 𝒜 (ja + jb))
          (mul_mem_graded sa_mem rb_mem)⟩,
      ⟨sa * sb, mul_mem_graded sa_mem sb_mem⟩, fun y => ⟨fun h => _, _⟩⟩
  · cases' (y : ProjectiveSpectrum.top 𝒜).isPrime.mem_or_mem h with h h
    · obtain ⟨nin, -⟩ := wa ⟨y, (Opens.infLELeft Va Vb y).2⟩; exact nin h
    · obtain ⟨nin, -⟩ := wb ⟨y, (Opens.infLERight Va Vb y).2⟩; exact nin h
  · simp only [add_mul, map_add, Pi.add_apply, RingHom.map_mul, ext_iff_val, add_val]
    obtain ⟨nin1, hy1⟩ := wa (Opens.infLELeft Va Vb y)
    obtain ⟨nin2, hy2⟩ := wb (Opens.infLERight Va Vb y)
    dsimp only at hy1 hy2
    erw [hy1, hy2]
    simp only [val_mk'', add_mk, add_comm (sa * rb)]
    rfl

theorem negMem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a : ∀ x : U.unop, at x.1)
    (ha : (isLocallyFraction 𝒜).pred a) : (isLocallyFraction 𝒜).pred (-a) := fun x => by
  rcases ha x with ⟨V, m, i, j, ⟨r, r_mem⟩, ⟨s, s_mem⟩, w⟩
  choose nin hy using w
  refine' ⟨V, m, i, j, ⟨-r, Submodule.neg_mem _ r_mem⟩, ⟨s, s_mem⟩, fun y => ⟨nin y, _⟩⟩
  simp only [ext_iff_val, val_mk''] at hy
  simp only [Pi.neg_apply, ext_iff_val, neg_val, hy, val_mk'', neg_mk]

theorem mulMem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : ∀ x : U.unop, at x.1)
    (ha : (isLocallyFraction 𝒜).pred a) (hb : (isLocallyFraction 𝒜).pred b) :
    (isLocallyFraction 𝒜).pred (a * b) := fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, wb⟩
  refine'
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨ra * rb, SetLike.mul_mem_graded ra_mem rb_mem⟩,
      ⟨sa * sb, SetLike.mul_mem_graded sa_mem sb_mem⟩, fun y => ⟨fun h => _, _⟩⟩
  · cases' (y : ProjectiveSpectrum.top 𝒜).isPrime.mem_or_mem h with h h
    · choose nin _ using wa ⟨y, (Opens.infLELeft Va Vb y).2⟩; exact nin h
    · choose nin _ using wb ⟨y, (Opens.infLERight Va Vb y).2⟩; exact nin h
  · simp only [Pi.mul_apply, RingHom.map_mul]
    choose nin1 hy1 using wa (Opens.infLELeft Va Vb y)
    choose nin2 hy2 using wb (Opens.infLERight Va Vb y)
    rw [ext_iff_val] at hy1 hy2 ⊢
    erw [mul_val, hy1, hy2]
    simp only [val_mk'', mk_mul]
    rfl

end SectionSubring

section

open SectionSubring

variable {𝒜}

/-- The functions satisfying `isLocallyFraction` form a subring of all dependent functions
`Π x : U, HomogeneousLocalization 𝒜 x`.-/
def sectionsSubring (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) : Subring (∀ x : U.unop, at x.1)
    where
  carrier := {f | (isLocallyFraction 𝒜).pred f}
  zero_mem' := zeroMem' U
  one_mem' := oneMem' U
  add_mem' := addMem' U _ _
  neg_mem' := negMem' U _
  mul_mem' := mulMem' U _ _

end

/-- The structure sheaf (valued in `Type`, not yet `CommRing`) is the subsheaf consisting of
functions satisfying `isLocallyFraction`.-/
def structureSheafInType : Sheaf (Type _) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜)

instance commRingStructureSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    CommRing ((structureSheafInType 𝒜).1.obj U) :=
  (sectionsSubring U).toCommRing

/-- The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type` valued
structure presheaf.-/
@[simps]
def structurePresheafInCommRing : Presheaf CommRingCat (ProjectiveSpectrum.top 𝒜) where
  obj U := CommRingCat.of ((structureSheafInType 𝒜).1.obj U)
  map i :=
    { toFun := (structureSheafInType 𝒜).1.map i
      map_zero' := rfl
      map_add' := fun x y => rfl
      map_one' := rfl
      map_mul' := fun x y => rfl }

-- These lemmas have always been bad (#7657), but leanprover/lean4#2644 made `simp` start noticing
attribute [nolint simpNF]
  AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.structurePresheafInCommRing_map_apply

/-- Some glue, verifying that that structure presheaf valued in `CommRing` agrees with the `Type`
valued structure presheaf.-/
def structurePresheafCompForget :
    structurePresheafInCommRing 𝒜 ⋙ forget CommRingCat ≅ (structureSheafInType 𝒜).1 :=
  NatIso.ofComponents (fun U => Iso.refl _) (by aesop_cat)

end ProjectiveSpectrum.StructureSheaf

namespace ProjectiveSpectrum

open TopCat.Presheaf ProjectiveSpectrum.StructureSheaf Opens

/-- The structure sheaf on `Proj` 𝒜, valued in `CommRing`.-/
def Proj.structureSheaf : Sheaf CommRingCat (ProjectiveSpectrum.top 𝒜) :=
  ⟨structurePresheafInCommRing 𝒜,
    (-- We check the sheaf condition under `forget CommRing`.
          isSheaf_iff_isSheaf_comp
          _ _).mpr
      (isSheaf_of_iso (structurePresheafCompForget 𝒜).symm (structureSheafInType 𝒜).cond)⟩

end ProjectiveSpectrum

section

open ProjectiveSpectrum ProjectiveSpectrum.StructureSheaf Opens

@[simp]
theorem res_apply (U V : Opens (ProjectiveSpectrum.top 𝒜)) (i : V ⟶ U)
    (s : (Proj.structureSheaf 𝒜).1.obj (op U)) (x : V) :
    ((Proj.structureSheaf 𝒜).1.map i.op s).1 x = (s.1 (i x) : _) :=
  rfl

/-- `Proj` of a graded ring as a `SheafedSpace`-/
def Proj.toSheafedSpace : SheafedSpace CommRingCat where
  carrier := TopCat.of (ProjectiveSpectrum 𝒜)
  presheaf := (Proj.structureSheaf 𝒜).1
  IsSheaf := (Proj.structureSheaf 𝒜).2

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

/-- The ring homomorphism from the stalk of the structure sheaf of `Proj` at a point corresponding
to a homogeneous prime ideal `x` to the *homogeneous localization* at `x`,
formed by gluing the `openToLocalization` maps. -/
def stalkToFiberRingHom (x : ProjectiveSpectrum.top 𝒜) :
    (Proj.structureSheaf 𝒜).presheaf.stalk x ⟶ CommRingCat.of (at x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (Proj.structureSheaf 𝒜).1)
    { pt := _
      ι :=
        { app := fun U =>
            openToLocalization 𝒜 ((OpenNhds.inclusion _).obj U.unop) x U.unop.2
          -- porting note: this proof was automatic in mathlib3
          naturality := fun _ _ _ => rfl } }

@[simp]
theorem germ_comp_stalkToFiberRingHom (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : U) :
    (Proj.structureSheaf 𝒜).presheaf.germ x ≫ stalkToFiberRingHom 𝒜 x =
      openToLocalization 𝒜 U x x.2 :=
  Limits.colimit.ι_desc _ _

@[simp]
theorem stalkToFiberRingHom_germ' (U : Opens (ProjectiveSpectrum.top 𝒜))
    (x : ProjectiveSpectrum.top 𝒜) (hx : x ∈ U) (s : (Proj.structureSheaf 𝒜).1.obj (op U)) :
    stalkToFiberRingHom 𝒜 x ((Proj.structureSheaf 𝒜).presheaf.germ ⟨x, hx⟩ s) = (s.1 ⟨x, hx⟩ : _) :=
  RingHom.ext_iff.1 (germ_comp_stalkToFiberRingHom 𝒜 U ⟨x, hx⟩ : _) s

@[simp]
theorem stalkToFiberRingHom_germ (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : U)
    (s : (Proj.structureSheaf 𝒜).1.obj (op U)) :
    stalkToFiberRingHom 𝒜 x ((Proj.structureSheaf 𝒜).presheaf.germ x s) = s.1 x :=
  stalkToFiberRingHom_germ' 𝒜 U _ _ _

theorem HomogeneousLocalization.mem_basicOpen (x : ProjectiveSpectrum.top 𝒜) (f : at x) :
    x ∈ ProjectiveSpectrum.basicOpen 𝒜 f.den := by
  rw [ProjectiveSpectrum.mem_basicOpen]
  exact f.den_mem

/-- Given a point `x` corresponding to a homogeneous prime ideal, there is a (dependent) function
such that, for any `f` in the homogeneous localization at `x`, it returns the obvious section in the
basic open set `D(f.den)`-/
def sectionInBasicOpen (x : ProjectiveSpectrum.top 𝒜) :
    ∀ f : at x, (Proj.structureSheaf 𝒜).1.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f.den)) :=
  fun f =>
  ⟨fun y => Quotient.mk'' ⟨f.deg, ⟨f.num, f.num_mem_deg⟩, ⟨f.den, f.den_mem_deg⟩, y.2⟩, fun y =>
    ⟨ProjectiveSpectrum.basicOpen 𝒜 f.den, y.2,
      ⟨𝟙 _, ⟨f.deg, ⟨⟨f.num, f.num_mem_deg⟩, ⟨f.den, f.den_mem_deg⟩, fun z => ⟨z.2, rfl⟩⟩⟩⟩⟩⟩

/-- Given any point `x` and `f` in the homogeneous localization at `x`, there is an element in the
stalk at `x` obtained by `sectionInBasicOpen`. This is the inverse of `stalkToFiberRingHom`.
-/
def homogeneousLocalizationToStalk (x : ProjectiveSpectrum.top 𝒜) :
    (at x) → (Proj.structureSheaf 𝒜).presheaf.stalk x := fun f =>
  (Proj.structureSheaf 𝒜).presheaf.germ
    (⟨x, HomogeneousLocalization.mem_basicOpen _ x f⟩ : ProjectiveSpectrum.basicOpen _ f.den)
    (sectionInBasicOpen _ x f)

/-- Using `homogeneousLocalizationToStalk`, we construct a ring isomorphism between stalk at `x`
and homogeneous localization at `x` for any point `x` in `Proj`.-/
def Proj.stalkIso' (x : ProjectiveSpectrum.top 𝒜) :
    (Proj.structureSheaf 𝒜).presheaf.stalk x ≃+* CommRingCat.of (at x) :=
  RingEquiv.ofBijective (stalkToFiberRingHom _ x)
    ⟨fun z1 z2 eq1 => by
      obtain ⟨u1, memu1, s1, rfl⟩ := (Proj.structureSheaf 𝒜).presheaf.germ_exist x z1
      obtain ⟨u2, memu2, s2, rfl⟩ := (Proj.structureSheaf 𝒜).presheaf.germ_exist x z2
      obtain ⟨v1, memv1, i1, ⟨j1, ⟨a1, a1_mem⟩, ⟨b1, b1_mem⟩, hs1⟩⟩ := s1.2 ⟨x, memu1⟩
      obtain ⟨v2, memv2, i2, ⟨j2, ⟨a2, a2_mem⟩, ⟨b2, b2_mem⟩, hs2⟩⟩ := s2.2 ⟨x, memu2⟩
      obtain ⟨b1_nin_x, eq2⟩ := hs1 ⟨x, memv1⟩
      obtain ⟨b2_nin_x, eq3⟩ := hs2 ⟨x, memv2⟩
      dsimp only at eq1 eq2 eq3
      erw [stalkToFiberRingHom_germ 𝒜 u1 ⟨x, memu1⟩ s1,
        stalkToFiberRingHom_germ 𝒜 u2 ⟨x, memu2⟩ s2] at eq1
      erw [eq1] at eq2
      erw [eq2, Quotient.eq''] at eq3
      change Localization.mk _ _ = Localization.mk _ _ at eq3
      rw [Localization.mk_eq_mk', IsLocalization.eq] at eq3
      obtain ⟨⟨c, hc⟩, eq3⟩ := eq3
      have eq3' :
        ∀ (y : ProjectiveSpectrum.top 𝒜)
          (hy : y ∈ ProjectiveSpectrum.basicOpen 𝒜 b1 ⊓ ProjectiveSpectrum.basicOpen 𝒜 b2 ⊓
                ProjectiveSpectrum.basicOpen 𝒜 c), (Localization.mk a1 ⟨b1,
                  show b1 ∉ y.asHomogeneousIdeal by
                    rw [← ProjectiveSpectrum.mem_basicOpen]
                    exact leOfHom (Opens.infLELeft _ _ ≫ Opens.infLELeft _ _) hy⟩ :
              Localization.AtPrime y.1.toIdeal) = Localization.mk a2
              ⟨b2, by
                change b2 ∉ y.asHomogeneousIdeal
                rw [← ProjectiveSpectrum.mem_basicOpen]
                exact leOfHom (Opens.infLELeft _ _ ≫ Opens.infLERight _ _) hy⟩ := by
        intro y hy
        rw [Localization.mk_eq_mk', IsLocalization.eq]
        exact
          ⟨⟨c, show c ∉ y.asHomogeneousIdeal by
                  rw [← ProjectiveSpectrum.mem_basicOpen]
                  exact leOfHom (Opens.infLERight _ _) hy⟩, eq3⟩
      refine'
        Presheaf.germ_ext (Proj.structureSheaf 𝒜).1
          (ProjectiveSpectrum.basicOpen _ b1 ⊓ ProjectiveSpectrum.basicOpen _ b2 ⊓
                ProjectiveSpectrum.basicOpen _ c ⊓ v1 ⊓ v2)
          ⟨⟨⟨⟨b1_nin_x, b2_nin_x⟩, hc⟩, memv1⟩, memv2⟩
          (Opens.infLELeft _ _ ≫ Opens.infLERight _ _ ≫ i1) (Opens.infLERight _ _ ≫ i2) _
      rw [Subtype.ext_iff_val]
      ext1 y
      simp only [res_apply]
      obtain ⟨b1_nin_y, eq6⟩ :=
        hs1 ⟨_, leOfHom (Opens.infLELeft _ _ ≫ Opens.infLERight _ _) y.2⟩
      obtain ⟨b2_nin_y, eq7⟩ := hs2 ⟨_, leOfHom (Opens.infLERight _ _) y.2⟩
      simp only at eq6 eq7
      erw [eq6, eq7, Quotient.eq'']
      change Localization.mk _ _ = Localization.mk _ _
      exact eq3' _
          ⟨⟨leOfHom
                (Opens.infLELeft _ _ ≫
                  Opens.infLELeft _ _ ≫ Opens.infLELeft _ _ ≫ Opens.infLELeft _ _) y.2,
              leOfHom
                (Opens.infLELeft _ _ ≫
                  Opens.infLELeft _ _ ≫ Opens.infLELeft _ _ ≫ Opens.infLERight _ _) y.2⟩,
            leOfHom (Opens.infLELeft _ _ ≫ Opens.infLELeft _ _ ≫ Opens.infLERight _ _) y.2⟩,
      Function.surjective_iff_hasRightInverse.mpr
        ⟨homogeneousLocalizationToStalk 𝒜 x, fun f => by
          rw [homogeneousLocalizationToStalk]
          erw [stalkToFiberRingHom_germ 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 f.den) ⟨x, _⟩
              (sectionInBasicOpen _ x f)]
          rw [sectionInBasicOpen, HomogeneousLocalization.ext_iff_val, f.eq_num_div_den]
          simp only [unop_op, HomogeneousLocalization.val_mk'', mk_eq_monoidOf_mk'] ⟩⟩

/-- `Proj` of a graded ring as a `LocallyRingedSpace`-/
def Proj.toLocallyRingedSpace : LocallyRingedSpace :=
  { Proj.toSheafedSpace 𝒜 with
    localRing := fun x =>
      @RingEquiv.localRing _ _ _ (show LocalRing (at x) from inferInstance) _
        (Proj.stalkIso' 𝒜 x).symm }

end

end AlgebraicGeometry
