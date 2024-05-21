/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.Algebra.Ring.Subring.Basic

#align_import algebraic_geometry.structure_sheaf from "leanprover-community/mathlib"@"5dc6092d09e5e489106865241986f7f2ad28d4c8"

/-!
# The structure sheaf on `PrimeSpectrum R`.

We define the structure sheaf on `TopCat.of (PrimeSpectrum R)`, for a commutative ring `R` and prove
basic properties about it. We define this as a subsheaf of the sheaf of dependent functions into the
localizations, cut out by the condition that the function must be locally equal to a ratio of
elements of `R`.

Because the condition "is equal to a fraction" passes to smaller open subsets,
the subset of functions satisfying this condition is automatically a subpresheaf.
Because the condition "is locally equal to a fraction" is local,
it is also a subsheaf.

(It may be helpful to refer back to `Mathlib/Topology/Sheaves/SheafOfFunctions.lean`,
where we show that dependent functions into any type family form a sheaf,
and also `Mathlib/Topology/Sheaves/LocalPredicate.lean`, where we characterise the predicates
which pick out sub-presheaves and sub-sheaves of these sheaves.)

We also set up the ring structure, obtaining
`structureSheaf : Sheaf CommRingCat (PrimeSpectrum.Top R)`.

We then construct two basic isomorphisms, relating the structure sheaf to the underlying ring `R`.
First, `StructureSheaf.stalkIso` gives an isomorphism between the stalk of the structure sheaf
at a point `p` and the localization of `R` at the prime ideal `p`. Second,
`StructureSheaf.basicOpenIso` gives an isomorphism between the structure sheaf on `basicOpen f`
and the localization of `R` at the submonoid of powers of `f`.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/


universe u

noncomputable section

variable (R : Type u) [CommRing R]

open TopCat

open TopologicalSpace

open CategoryTheory

open Opposite

namespace AlgebraicGeometry

/-- The prime spectrum, just as a topological space.
-/
def PrimeSpectrum.Top : TopCat :=
  TopCat.of (PrimeSpectrum R)
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.prime_spectrum.Top AlgebraicGeometry.PrimeSpectrum.Top

namespace StructureSheaf

/-- The type family over `PrimeSpectrum R` consisting of the localization over each point.
-/
def Localizations (P : PrimeSpectrum.Top R) : Type u :=
  Localization.AtPrime P.asIdeal
#align algebraic_geometry.structure_sheaf.localizations AlgebraicGeometry.StructureSheaf.Localizations

-- Porting note: can't derive `CommRingCat`
instance commRingLocalizations (P : PrimeSpectrum.Top R) : CommRing <| Localizations R P :=
  inferInstanceAs <| CommRing <| Localization.AtPrime P.asIdeal

-- Porting note: can't derive `LocalRing`
instance localRingLocalizations (P : PrimeSpectrum.Top R) : LocalRing <| Localizations R P :=
  inferInstanceAs <| LocalRing <| Localization.AtPrime P.asIdeal

instance (P : PrimeSpectrum.Top R) : Inhabited (Localizations R P) :=
  ⟨1⟩

instance (U : Opens (PrimeSpectrum.Top R)) (x : U) : Algebra R (Localizations R x) :=
  inferInstanceAs <| Algebra R (Localization.AtPrime x.1.asIdeal)

instance (U : Opens (PrimeSpectrum.Top R)) (x : U) :
    IsLocalization.AtPrime (Localizations R x) (x : PrimeSpectrum.Top R).asIdeal :=
  Localization.isLocalization

variable {R}

/-- The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` in each of the stalks (which are localizations at various prime ideals).
-/
def IsFraction {U : Opens (PrimeSpectrum.Top R)} (f : ∀ x : U, Localizations R x) : Prop :=
  ∃ r s : R, ∀ x : U, ¬s ∈ x.1.asIdeal ∧ f x * algebraMap _ _ s = algebraMap _ _ r
#align algebraic_geometry.structure_sheaf.is_fraction AlgebraicGeometry.StructureSheaf.IsFraction

theorem IsFraction.eq_mk' {U : Opens (PrimeSpectrum.Top R)} {f : ∀ x : U, Localizations R x}
    (hf : IsFraction f) :
    ∃ r s : R,
      ∀ x : U,
        ∃ hs : s ∉ x.1.asIdeal,
          f x =
            IsLocalization.mk' (Localization.AtPrime _) r
              (⟨s, hs⟩ : (x : PrimeSpectrum.Top R).asIdeal.primeCompl) := by
  rcases hf with ⟨r, s, h⟩
  refine' ⟨r, s, fun x => ⟨(h x).1, (IsLocalization.mk'_eq_iff_eq_mul.mpr _).symm⟩⟩
  exact (h x).2.symm
#align algebraic_geometry.structure_sheaf.is_fraction.eq_mk' AlgebraicGeometry.StructureSheaf.IsFraction.eq_mk'

variable (R)

/-- The predicate `IsFraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
def isFractionPrelocal : PrelocalPredicate (Localizations R) where
  pred {U} f := IsFraction f
  res := by rintro V U i f ⟨r, s, w⟩; exact ⟨r, s, fun x => w (i x)⟩
#align algebraic_geometry.structure_sheaf.is_fraction_prelocal AlgebraicGeometry.StructureSheaf.isFractionPrelocal

/-- We will define the structure sheaf as
the subsheaf of all dependent functions in `Π x : U, Localizations R x`
consisting of those functions which can locally be expressed as a ratio of
(the images in the localization of) elements of `R`.

Quoting Hartshorne:

For an open set $U ⊆ Spec A$, we define $𝒪(U)$ to be the set of functions
$s : U → ⨆_{𝔭 ∈ U} A_𝔭$, such that $s(𝔭) ∈ A_𝔭$ for each $𝔭$,
and such that $s$ is locally a quotient of elements of $A$:
to be precise, we require that for each $𝔭 ∈ U$, there is a neighborhood $V$ of $𝔭$,
contained in $U$, and elements $a, f ∈ A$, such that for each $𝔮 ∈ V, f ∉ 𝔮$,
and $s(𝔮) = a/f$ in $A_𝔮$.

Now Hartshorne had the disadvantage of not knowing about dependent functions,
so we replace his circumlocution about functions into a disjoint union with
`Π x : U, Localizations x`.
-/
def isLocallyFraction : LocalPredicate (Localizations R) :=
  (isFractionPrelocal R).sheafify
#align algebraic_geometry.structure_sheaf.is_locally_fraction AlgebraicGeometry.StructureSheaf.isLocallyFraction

@[simp]
theorem isLocallyFraction_pred {U : Opens (PrimeSpectrum.Top R)} (f : ∀ x : U, Localizations R x) :
    (isLocallyFraction R).pred f =
      ∀ x : U,
        ∃ (V : _) (_ : x.1 ∈ V) (i : V ⟶ U),
          ∃ r s : R,
            ∀ y : V, ¬s ∈ y.1.asIdeal ∧ f (i y : U) * algebraMap _ _ s = algebraMap _ _ r :=
  rfl
#align algebraic_geometry.structure_sheaf.is_locally_fraction_pred AlgebraicGeometry.StructureSheaf.isLocallyFraction_pred

/-- The functions satisfying `isLocallyFraction` form a subring.
-/
def sectionsSubring (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Subring (∀ x : U.unop, Localizations R x) where
  carrier := { f | (isLocallyFraction R).pred f }
  zero_mem' := by
    refine' fun x => ⟨unop U, x.2, 𝟙 _, 0, 1, fun y => ⟨_, _⟩⟩
    · rw [← Ideal.ne_top_iff_one]; exact y.1.IsPrime.1
    · simp
  one_mem' := by
    refine' fun x => ⟨unop U, x.2, 𝟙 _, 1, 1, fun y => ⟨_, _⟩⟩
    · rw [← Ideal.ne_top_iff_one]; exact y.1.IsPrime.1
    · simp
  add_mem' := by
    intro a b ha hb x
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩
    refine' ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ra * sb + rb * sa, sa * sb, _⟩
    intro y
    rcases wa (Opens.infLELeft _ _ y) with ⟨nma, wa⟩
    rcases wb (Opens.infLERight _ _ y) with ⟨nmb, wb⟩
    fconstructor
    · intro H; cases y.1.IsPrime.mem_or_mem H <;> contradiction
    · simp only [add_mul, RingHom.map_add, Pi.add_apply, RingHom.map_mul]
      erw [← wa, ← wb]
      simp only [mul_assoc]
      congr 2
      rw [mul_comm]
  neg_mem' := by
    intro a ha x
    rcases ha x with ⟨V, m, i, r, s, w⟩
    refine ⟨V, m, i, -r, s, ?_⟩
    intro y
    rcases w y with ⟨nm, w⟩
    fconstructor
    · exact nm
    · simp only [RingHom.map_neg, Pi.neg_apply]
      erw [← w]
      simp only [neg_mul]
  mul_mem' := by
    intro a b ha hb x
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩
    refine' ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ra * rb, sa * sb, _⟩
    intro y
    rcases wa (Opens.infLELeft _ _ y) with ⟨nma, wa⟩
    rcases wb (Opens.infLERight _ _ y) with ⟨nmb, wb⟩
    fconstructor
    · intro H; cases y.1.IsPrime.mem_or_mem H <;> contradiction
    · simp only [Pi.mul_apply, RingHom.map_mul]
      erw [← wa, ← wb]
      simp only [mul_left_comm, mul_assoc, mul_comm]
#align algebraic_geometry.structure_sheaf.sections_subring AlgebraicGeometry.StructureSheaf.sectionsSubring

end StructureSheaf

open StructureSheaf

/-- The structure sheaf (valued in `Type`, not yet `CommRingCat`) is the subsheaf consisting of
functions satisfying `isLocallyFraction`.
-/
def structureSheafInType : Sheaf (Type u) (PrimeSpectrum.Top R) :=
  subsheafToTypes (isLocallyFraction R)
#align algebraic_geometry.structure_sheaf_in_Type AlgebraicGeometry.structureSheafInType

instance commRingStructureSheafInTypeObj (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    CommRing ((structureSheafInType R).1.obj U) :=
  (sectionsSubring R U).toCommRing
#align algebraic_geometry.comm_ring_structure_sheaf_in_Type_obj AlgebraicGeometry.commRingStructureSheafInTypeObj

open PrimeSpectrum

/-- The structure presheaf, valued in `CommRingCat`, constructed by dressing up the `Type` valued
structure presheaf.
-/
@[simps]
def structurePresheafInCommRing : Presheaf CommRingCat (PrimeSpectrum.Top R) where
  obj U := CommRingCat.of ((structureSheafInType R).1.obj U)
  map {U V} i :=
    { toFun := (structureSheafInType R).1.map i
      map_zero' := rfl
      map_add' := fun x y => rfl
      map_one' := rfl
      map_mul' := fun x y => rfl }
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.structure_presheaf_in_CommRing AlgebraicGeometry.structurePresheafInCommRing

-- These lemmas have always been bad (#7657), but leanprover/lean4#2644 made `simp` start noticing
attribute [nolint simpNF] AlgebraicGeometry.structurePresheafInCommRing_map_apply

/-- Some glue, verifying that that structure presheaf valued in `CommRingCat` agrees
with the `Type` valued structure presheaf.
-/
def structurePresheafCompForget :
    structurePresheafInCommRing R ⋙ forget CommRingCat ≅ (structureSheafInType R).1 :=
  NatIso.ofComponents fun U => Iso.refl _
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.structure_presheaf_comp_forget AlgebraicGeometry.structurePresheafCompForget

open TopCat.Presheaf

/-- The structure sheaf on $Spec R$, valued in `CommRingCat`.

This is provided as a bundled `SheafedSpace` as `Spec.SheafedSpace R` later.
-/
def Spec.structureSheaf : Sheaf CommRingCat (PrimeSpectrum.Top R) :=
  ⟨structurePresheafInCommRing R,
    (-- We check the sheaf condition under `forget CommRingCat`.
          isSheaf_iff_isSheaf_comp
          _ _).mpr
      (isSheaf_of_iso (structurePresheafCompForget R).symm (structureSheafInType R).cond)⟩
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.structure_sheaf AlgebraicGeometry.Spec.structureSheaf

open Spec (structureSheaf)

namespace StructureSheaf

@[simp]
theorem res_apply (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U)
    (s : (structureSheaf R).1.obj (op U)) (x : V) :
    ((structureSheaf R).1.map i.op s).1 x = (s.1 (i x) : _) :=
  rfl
#align algebraic_geometry.structure_sheaf.res_apply AlgebraicGeometry.StructureSheaf.res_apply

/-

Notation in this comment

X = Spec R
OX = structure sheaf

In the following we construct an isomorphism between OX_p and R_p given any point p corresponding
to a prime ideal in R.

We do this via 8 steps:

1. def const (f g : R) (V) (hv : V ≤ D_g) : OX(V) [for api]
2. def toOpen (U) : R ⟶ OX(U)
3. [2] def toStalk (p : Spec R) : R ⟶ OX_p
4. [2] def toBasicOpen (f : R) : R_f ⟶ OX(D_f)
5. [3] def localizationToStalk (p : Spec R) : R_p ⟶ OX_p
6. def openToLocalization (U) (p) (hp : p ∈ U) : OX(U) ⟶ R_p
7. [6] def stalkToFiberRingHom (p : Spec R) : OX_p ⟶ R_p
8. [5,7] def stalkIso (p : Spec R) : OX_p ≅ R_p

In the square brackets we list the dependencies of a construction on the previous steps.

-/
/-- The section of `structureSheaf R` on an open `U` sending each `x ∈ U` to the element
`f/g` in the localization of `R` at `x`. -/
def const (f g : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, g ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) :
    (structureSheaf R).1.obj (op U) :=
  ⟨fun x => IsLocalization.mk' _ f ⟨g, hu x x.2⟩, fun x =>
    ⟨U, x.2, 𝟙 _, f, g, fun y => ⟨hu y y.2, IsLocalization.mk'_spec _ _ _⟩⟩⟩
#align algebraic_geometry.structure_sheaf.const AlgebraicGeometry.StructureSheaf.const

@[simp]
theorem const_apply (f g : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, g ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) (x : U) :
    (const R f g U hu).1 x = IsLocalization.mk' _ f ⟨g, hu x x.2⟩ :=
  rfl
#align algebraic_geometry.structure_sheaf.const_apply AlgebraicGeometry.StructureSheaf.const_apply

theorem const_apply' (f g : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, g ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) (x : U)
    (hx : g ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) :
    (const R f g U hu).1 x = IsLocalization.mk' _ f ⟨g, hx⟩ :=
  rfl
#align algebraic_geometry.structure_sheaf.const_apply' AlgebraicGeometry.StructureSheaf.const_apply'

theorem exists_const (U) (s : (structureSheaf R).1.obj (op U)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) :
    ∃ (V : Opens (PrimeSpectrum.Top R)) (_ : x ∈ V) (i : V ⟶ U) (f g : R) (hg : _),
      const R f g V hg = (structureSheaf R).1.map i.op s :=
  let ⟨V, hxV, iVU, f, g, hfg⟩ := s.2 ⟨x, hx⟩
  ⟨V, hxV, iVU, f, g, fun y hyV => (hfg ⟨y, hyV⟩).1,
    Subtype.eq <| funext fun y => IsLocalization.mk'_eq_iff_eq_mul.2 <| Eq.symm <| (hfg y).2⟩
#align algebraic_geometry.structure_sheaf.exists_const AlgebraicGeometry.StructureSheaf.exists_const

@[simp]
theorem res_const (f g : R) (U hu V hv i) :
    (structureSheaf R).1.map i (const R f g U hu) = const R f g V hv :=
  rfl
#align algebraic_geometry.structure_sheaf.res_const AlgebraicGeometry.StructureSheaf.res_const

theorem res_const' (f g : R) (V hv) :
    (structureSheaf R).1.map (homOfLE hv).op (const R f g (PrimeSpectrum.basicOpen g) fun _ => id) =
      const R f g V hv :=
  rfl
#align algebraic_geometry.structure_sheaf.res_const' AlgebraicGeometry.StructureSheaf.res_const'

theorem const_zero (f : R) (U hu) : const R 0 f U hu = 0 :=
  Subtype.eq <| funext fun x => IsLocalization.mk'_eq_iff_eq_mul.2 <| by
    rw [RingHom.map_zero]
    exact (mul_eq_zero_of_left rfl ((algebraMap R (Localizations R x)) _)).symm
#align algebraic_geometry.structure_sheaf.const_zero AlgebraicGeometry.StructureSheaf.const_zero

theorem const_self (f : R) (U hu) : const R f f U hu = 1 :=
  Subtype.eq <| funext fun _ => IsLocalization.mk'_self _ _
#align algebraic_geometry.structure_sheaf.const_self AlgebraicGeometry.StructureSheaf.const_self

theorem const_one (U) : (const R 1 1 U fun _ _ => Submonoid.one_mem _) = 1 :=
  const_self R 1 U _
#align algebraic_geometry.structure_sheaf.const_one AlgebraicGeometry.StructureSheaf.const_one

theorem const_add (f₁ f₂ g₁ g₂ : R) (U hu₁ hu₂) :
    const R f₁ g₁ U hu₁ + const R f₂ g₂ U hu₂ =
      const R (f₁ * g₂ + f₂ * g₁) (g₁ * g₂) U fun x hx =>
        Submonoid.mul_mem _ (hu₁ x hx) (hu₂ x hx) :=
  Subtype.eq <| funext fun x => Eq.symm <| IsLocalization.mk'_add _ _
    ⟨g₁, hu₁ x x.2⟩ ⟨g₂, hu₂ x x.2⟩
#align algebraic_geometry.structure_sheaf.const_add AlgebraicGeometry.StructureSheaf.const_add

theorem const_mul (f₁ f₂ g₁ g₂ : R) (U hu₁ hu₂) :
    const R f₁ g₁ U hu₁ * const R f₂ g₂ U hu₂ =
      const R (f₁ * f₂) (g₁ * g₂) U fun x hx => Submonoid.mul_mem _ (hu₁ x hx) (hu₂ x hx) :=
  Subtype.eq <|
    funext fun x =>
      Eq.symm <| by convert IsLocalization.mk'_mul _ f₁ f₂ ⟨g₁, hu₁ x x.2⟩ ⟨g₂, hu₂ x x.2⟩
#align algebraic_geometry.structure_sheaf.const_mul AlgebraicGeometry.StructureSheaf.const_mul

theorem const_ext {f₁ f₂ g₁ g₂ : R} {U hu₁ hu₂} (h : f₁ * g₂ = f₂ * g₁) :
    const R f₁ g₁ U hu₁ = const R f₂ g₂ U hu₂ :=
  Subtype.eq <|
    funext fun x =>
      IsLocalization.mk'_eq_of_eq (by rw [mul_comm, Subtype.coe_mk, ← h, mul_comm, Subtype.coe_mk])
#align algebraic_geometry.structure_sheaf.const_ext AlgebraicGeometry.StructureSheaf.const_ext

theorem const_congr {f₁ f₂ g₁ g₂ : R} {U hu} (hf : f₁ = f₂) (hg : g₁ = g₂) :
    const R f₁ g₁ U hu = const R f₂ g₂ U (hg ▸ hu) := by substs hf hg; rfl
#align algebraic_geometry.structure_sheaf.const_congr AlgebraicGeometry.StructureSheaf.const_congr

theorem const_mul_rev (f g : R) (U hu₁ hu₂) : const R f g U hu₁ * const R g f U hu₂ = 1 := by
  rw [const_mul, const_congr R rfl (mul_comm g f), const_self]
#align algebraic_geometry.structure_sheaf.const_mul_rev AlgebraicGeometry.StructureSheaf.const_mul_rev

theorem const_mul_cancel (f g₁ g₂ : R) (U hu₁ hu₂) :
    const R f g₁ U hu₁ * const R g₁ g₂ U hu₂ = const R f g₂ U hu₂ := by
  rw [const_mul, const_ext]; rw [mul_assoc]
#align algebraic_geometry.structure_sheaf.const_mul_cancel AlgebraicGeometry.StructureSheaf.const_mul_cancel

theorem const_mul_cancel' (f g₁ g₂ : R) (U hu₁ hu₂) :
    const R g₁ g₂ U hu₂ * const R f g₁ U hu₁ = const R f g₂ U hu₂ := by
  rw [mul_comm, const_mul_cancel]
#align algebraic_geometry.structure_sheaf.const_mul_cancel' AlgebraicGeometry.StructureSheaf.const_mul_cancel'

/-- The canonical ring homomorphism interpreting an element of `R` as
a section of the structure sheaf. -/
def toOpen (U : Opens (PrimeSpectrum.Top R)) :
    CommRingCat.of R ⟶ (structureSheaf R).1.obj (op U) where
  toFun f :=
    ⟨fun x => algebraMap R _ f, fun x =>
      ⟨U, x.2, 𝟙 _, f, 1, fun y =>
        ⟨(Ideal.ne_top_iff_one _).1 y.1.2.1, by rw [RingHom.map_one, mul_one]⟩⟩⟩
  map_one' := Subtype.eq <| funext fun x => RingHom.map_one _
  map_mul' f g := Subtype.eq <| funext fun x => RingHom.map_mul _ _ _
  map_zero' := Subtype.eq <| funext fun x => RingHom.map_zero _
  map_add' f g := Subtype.eq <| funext fun x => RingHom.map_add _ _ _
#align algebraic_geometry.structure_sheaf.to_open AlgebraicGeometry.StructureSheaf.toOpen

@[simp]
theorem toOpen_res (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U) :
    toOpen R U ≫ (structureSheaf R).1.map i.op = toOpen R V :=
  rfl
#align algebraic_geometry.structure_sheaf.to_open_res AlgebraicGeometry.StructureSheaf.toOpen_res

@[simp]
theorem toOpen_apply (U : Opens (PrimeSpectrum.Top R)) (f : R) (x : U) :
    (toOpen R U f).1 x = algebraMap _ _ f :=
  rfl
#align algebraic_geometry.structure_sheaf.to_open_apply AlgebraicGeometry.StructureSheaf.toOpen_apply

theorem toOpen_eq_const (U : Opens (PrimeSpectrum.Top R)) (f : R) :
    toOpen R U f = const R f 1 U fun x _ => (Ideal.ne_top_iff_one _).1 x.2.1 :=
  Subtype.eq <| funext fun _ => Eq.symm <| IsLocalization.mk'_one _ f
#align algebraic_geometry.structure_sheaf.to_open_eq_const AlgebraicGeometry.StructureSheaf.toOpen_eq_const

/-- The canonical ring homomorphism interpreting an element of `R` as an element of
the stalk of `structureSheaf R` at `x`. -/
def toStalk (x : PrimeSpectrum.Top R) : CommRingCat.of R ⟶ (structureSheaf R).presheaf.stalk x :=
  (toOpen R ⊤ ≫ (structureSheaf R).presheaf.germ ⟨x, by trivial⟩)
#align algebraic_geometry.structure_sheaf.to_stalk AlgebraicGeometry.StructureSheaf.toStalk

@[simp]
theorem toOpen_germ (U : Opens (PrimeSpectrum.Top R)) (x : U) :
    toOpen R U ≫ (structureSheaf R).presheaf.germ x = toStalk R x := by
  rw [← toOpen_res R ⊤ U (homOfLE le_top : U ⟶ ⊤), Category.assoc, Presheaf.germ_res]; rfl
#align algebraic_geometry.structure_sheaf.to_open_germ AlgebraicGeometry.StructureSheaf.toOpen_germ

@[simp]
theorem germ_toOpen (U : Opens (PrimeSpectrum.Top R)) (x : U) (f : R) :
    (structureSheaf R).presheaf.germ x (toOpen R U f) = toStalk R x f := by rw [← toOpen_germ]; rfl
#align algebraic_geometry.structure_sheaf.germ_to_open AlgebraicGeometry.StructureSheaf.germ_toOpen

theorem germ_to_top (x : PrimeSpectrum.Top R) (f : R) :
    (structureSheaf R).presheaf.germ (⟨x, trivial⟩ : (⊤ : Opens (PrimeSpectrum.Top R)))
        (toOpen R ⊤ f) =
      toStalk R x f :=
  rfl
#align algebraic_geometry.structure_sheaf.germ_to_top AlgebraicGeometry.StructureSheaf.germ_to_top

theorem isUnit_to_basicOpen_self (f : R) : IsUnit (toOpen R (PrimeSpectrum.basicOpen f) f) :=
  isUnit_of_mul_eq_one _ (const R 1 f (PrimeSpectrum.basicOpen f) fun _ => id) <| by
    rw [toOpen_eq_const, const_mul_rev]
#align algebraic_geometry.structure_sheaf.is_unit_to_basic_open_self AlgebraicGeometry.StructureSheaf.isUnit_to_basicOpen_self

theorem isUnit_toStalk (x : PrimeSpectrum.Top R) (f : x.asIdeal.primeCompl) :
    IsUnit (toStalk R x (f : R)) := by
  erw [← germ_toOpen R (PrimeSpectrum.basicOpen (f : R)) ⟨x, f.2⟩ (f : R)]
  exact RingHom.isUnit_map _ (isUnit_to_basicOpen_self R f)
#align algebraic_geometry.structure_sheaf.is_unit_to_stalk AlgebraicGeometry.StructureSheaf.isUnit_toStalk

/-- The canonical ring homomorphism from the localization of `R` at `p` to the stalk
of the structure sheaf at the point `p`. -/
def localizationToStalk (x : PrimeSpectrum.Top R) :
    CommRingCat.of (Localization.AtPrime x.asIdeal) ⟶ (structureSheaf R).presheaf.stalk x :=
  show Localization.AtPrime x.asIdeal →+* _ from IsLocalization.lift (isUnit_toStalk R x)
#align algebraic_geometry.structure_sheaf.localization_to_stalk AlgebraicGeometry.StructureSheaf.localizationToStalk

@[simp]
theorem localizationToStalk_of (x : PrimeSpectrum.Top R) (f : R) :
    localizationToStalk R x (algebraMap _ (Localization _) f) = toStalk R x f :=
  IsLocalization.lift_eq (S := Localization x.asIdeal.primeCompl) _ f
#align algebraic_geometry.structure_sheaf.localization_to_stalk_of AlgebraicGeometry.StructureSheaf.localizationToStalk_of

@[simp]
theorem localizationToStalk_mk' (x : PrimeSpectrum.Top R) (f : R) (s : x.asIdeal.primeCompl) :
    localizationToStalk R x (IsLocalization.mk' (Localization.AtPrime x.asIdeal) f s) =
      (structureSheaf R).presheaf.germ (⟨x, s.2⟩ : PrimeSpectrum.basicOpen (s : R))
        (const R f s (PrimeSpectrum.basicOpen s) fun _ => id) :=
  (IsLocalization.lift_mk'_spec (S := Localization.AtPrime x.asIdeal) _ _ _ _).2 <| by
    erw [← germ_toOpen R (PrimeSpectrum.basicOpen s) ⟨x, s.2⟩,
      ← germ_toOpen R (PrimeSpectrum.basicOpen s) ⟨x, s.2⟩, ← RingHom.map_mul, toOpen_eq_const,
      toOpen_eq_const, const_mul_cancel']
#align algebraic_geometry.structure_sheaf.localization_to_stalk_mk' AlgebraicGeometry.StructureSheaf.localizationToStalk_mk'

/-- The ring homomorphism that takes a section of the structure sheaf of `R` on the open set `U`,
implemented as a subtype of dependent functions to localizations at prime ideals, and evaluates
the section on the point corresponding to a given prime ideal. -/
def openToLocalization (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x ∈ U) :
    (structureSheaf R).1.obj (op U) ⟶ CommRingCat.of (Localization.AtPrime x.asIdeal) where
  toFun s := (s.1 ⟨x, hx⟩ : _)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
#align algebraic_geometry.structure_sheaf.open_to_localization AlgebraicGeometry.StructureSheaf.openToLocalization

@[simp]
theorem coe_openToLocalization (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) :
    (openToLocalization R U x hx :
        (structureSheaf R).1.obj (op U) → Localization.AtPrime x.asIdeal) =
      fun s => (s.1 ⟨x, hx⟩ : _) :=
  rfl
#align algebraic_geometry.structure_sheaf.coe_open_to_localization AlgebraicGeometry.StructureSheaf.coe_openToLocalization

theorem openToLocalization_apply (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) (s : (structureSheaf R).1.obj (op U)) :
    openToLocalization R U x hx s = (s.1 ⟨x, hx⟩ : _) :=
  rfl
#align algebraic_geometry.structure_sheaf.open_to_localization_apply AlgebraicGeometry.StructureSheaf.openToLocalization_apply

/-- The ring homomorphism from the stalk of the structure sheaf of `R` at a point corresponding to
a prime ideal `p` to the localization of `R` at `p`,
formed by gluing the `openToLocalization` maps. -/
def stalkToFiberRingHom (x : PrimeSpectrum.Top R) :
    (structureSheaf R).presheaf.stalk x ⟶ CommRingCat.of (Localization.AtPrime x.asIdeal) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (structureSheaf R).1)
    { pt := _
      ι := { app := fun U =>
        openToLocalization R ((OpenNhds.inclusion _).obj (unop U)) x (unop U).2 } }
#align algebraic_geometry.structure_sheaf.stalk_to_fiber_ring_hom AlgebraicGeometry.StructureSheaf.stalkToFiberRingHom

@[simp]
theorem germ_comp_stalkToFiberRingHom (U : Opens (PrimeSpectrum.Top R)) (x : U) :
    (structureSheaf R).presheaf.germ x ≫ stalkToFiberRingHom R x = openToLocalization R U x x.2 :=
  Limits.colimit.ι_desc _ _
#align algebraic_geometry.structure_sheaf.germ_comp_stalk_to_fiber_ring_hom AlgebraicGeometry.StructureSheaf.germ_comp_stalkToFiberRingHom

@[simp]
theorem stalkToFiberRingHom_germ' (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) (s : (structureSheaf R).1.obj (op U)) :
    stalkToFiberRingHom R x ((structureSheaf R).presheaf.germ ⟨x, hx⟩ s) = (s.1 ⟨x, hx⟩ : _) :=
  RingHom.ext_iff.1 (germ_comp_stalkToFiberRingHom R U ⟨x, hx⟩ : _) s
#align algebraic_geometry.structure_sheaf.stalk_to_fiber_ring_hom_germ' AlgebraicGeometry.StructureSheaf.stalkToFiberRingHom_germ'

@[simp]
theorem stalkToFiberRingHom_germ (U : Opens (PrimeSpectrum.Top R)) (x : U)
    (s : (structureSheaf R).1.obj (op U)) :
    stalkToFiberRingHom R x ((structureSheaf R).presheaf.germ x s) = s.1 x := by
  cases x; exact stalkToFiberRingHom_germ' R U _ _ _
#align algebraic_geometry.structure_sheaf.stalk_to_fiber_ring_hom_germ AlgebraicGeometry.StructureSheaf.stalkToFiberRingHom_germ

@[simp]
theorem toStalk_comp_stalkToFiberRingHom (x : PrimeSpectrum.Top R) :
    -- Porting note: now `algebraMap _ _` needs to be explicitly typed
    toStalk R x ≫ stalkToFiberRingHom R x = algebraMap R (Localization.AtPrime x.asIdeal) := by
  erw [toStalk, Category.assoc, germ_comp_stalkToFiberRingHom]; rfl
#align algebraic_geometry.structure_sheaf.to_stalk_comp_stalk_to_fiber_ring_hom AlgebraicGeometry.StructureSheaf.toStalk_comp_stalkToFiberRingHom

@[simp]
theorem stalkToFiberRingHom_toStalk (x : PrimeSpectrum.Top R) (f : R) :
    -- Porting note: now `algebraMap _ _` needs to be explicitly typed
    stalkToFiberRingHom R x (toStalk R x f) = algebraMap R (Localization.AtPrime x.asIdeal) f :=
  RingHom.ext_iff.1 (toStalk_comp_stalkToFiberRingHom R x) _
#align algebraic_geometry.structure_sheaf.stalk_to_fiber_ring_hom_to_stalk AlgebraicGeometry.StructureSheaf.stalkToFiberRingHom_toStalk

/-- The ring isomorphism between the stalk of the structure sheaf of `R` at a point `p`
corresponding to a prime ideal in `R` and the localization of `R` at `p`. -/
@[simps]
def stalkIso (x : PrimeSpectrum.Top R) :
    (structureSheaf R).presheaf.stalk x ≅ CommRingCat.of (Localization.AtPrime x.asIdeal) where
  hom := stalkToFiberRingHom R x
  inv := localizationToStalk R x
  hom_inv_id := by
    ext U hxU s
    -- Note: this `simp` was longer, but the line below had to become an `erw`
    simp only [Category.comp_id]
    erw [comp_apply, comp_apply, stalkToFiberRingHom_germ']
    obtain ⟨V, hxV, iVU, f, g, (hg : V ≤ PrimeSpectrum.basicOpen _), hs⟩ :=
      exists_const _ _ s x hxU
    erw [← res_apply R U V iVU s ⟨x, hxV⟩, ← hs, const_apply, localizationToStalk_mk']
    refine' (structureSheaf R).presheaf.germ_ext V hxV (homOfLE hg) iVU _
    dsimp
    erw [← hs, res_const']
  inv_hom_id :=
    @IsLocalization.ringHom_ext R _ x.asIdeal.primeCompl (Localization.AtPrime x.asIdeal) _ _
      (Localization.AtPrime x.asIdeal) _ _
      (RingHom.comp (stalkToFiberRingHom R x) (localizationToStalk R x))
      (RingHom.id (Localization.AtPrime _)) <| by
        ext f
        -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
        rw [RingHom.comp_apply, RingHom.comp_apply]; erw [localizationToStalk_of,
          stalkToFiberRingHom_toStalk]; rw [RingHom.comp_apply, RingHom.id_apply]
#align algebraic_geometry.structure_sheaf.stalk_iso AlgebraicGeometry.StructureSheaf.stalkIso

instance (x : PrimeSpectrum R) : IsIso (stalkToFiberRingHom R x) :=
  IsIso.of_iso (stalkIso R x)

instance (x : PrimeSpectrum R) : IsIso (localizationToStalk R x) :=
  IsIso.of_iso (stalkIso R x).symm

@[simp, reassoc]
theorem stalkToFiberRingHom_localizationToStalk (x : PrimeSpectrum.Top R) :
    stalkToFiberRingHom R x ≫ localizationToStalk R x = 𝟙 _ :=
  (stalkIso R x).hom_inv_id
#align algebraic_geometry.structure_sheaf.stalk_to_fiber_ring_hom_localization_to_stalk AlgebraicGeometry.StructureSheaf.stalkToFiberRingHom_localizationToStalk

@[simp, reassoc]
theorem localizationToStalk_stalkToFiberRingHom (x : PrimeSpectrum.Top R) :
    localizationToStalk R x ≫ stalkToFiberRingHom R x = 𝟙 _ :=
  (stalkIso R x).inv_hom_id
#align algebraic_geometry.structure_sheaf.localization_to_stalk_stalk_to_fiber_ring_hom AlgebraicGeometry.StructureSheaf.localizationToStalk_stalkToFiberRingHom

/-- The canonical ring homomorphism interpreting `s ∈ R_f` as a section of the structure sheaf
on the basic open defined by `f ∈ R`. -/
def toBasicOpen (f : R) :
    Localization.Away f →+* (structureSheaf R).1.obj (op <| PrimeSpectrum.basicOpen f) :=
  IsLocalization.Away.lift f (isUnit_to_basicOpen_self R f)
#align algebraic_geometry.structure_sheaf.to_basic_open AlgebraicGeometry.StructureSheaf.toBasicOpen

@[simp]
theorem toBasicOpen_mk' (s f : R) (g : Submonoid.powers s) :
    toBasicOpen R s (IsLocalization.mk' (Localization.Away s) f g) =
      const R f g (PrimeSpectrum.basicOpen s) fun x hx => Submonoid.powers_le.2 hx g.2 :=
  (IsLocalization.lift_mk'_spec _ _ _ _).2 <| by
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [toOpen_eq_const, toOpen_eq_const]; rw [const_mul_cancel']
#align algebraic_geometry.structure_sheaf.to_basic_open_mk' AlgebraicGeometry.StructureSheaf.toBasicOpen_mk'

@[simp]
theorem localization_toBasicOpen (f : R) :
    RingHom.comp (toBasicOpen R f) (algebraMap R (Localization.Away f)) =
    toOpen R (PrimeSpectrum.basicOpen f) :=
  RingHom.ext fun g => by
    rw [toBasicOpen, IsLocalization.Away.lift, RingHom.comp_apply, IsLocalization.lift_eq]
#align algebraic_geometry.structure_sheaf.localization_to_basic_open AlgebraicGeometry.StructureSheaf.localization_toBasicOpen

@[simp]
theorem toBasicOpen_to_map (s f : R) :
    toBasicOpen R s (algebraMap R (Localization.Away s) f) =
      const R f 1 (PrimeSpectrum.basicOpen s) fun _ _ => Submonoid.one_mem _ :=
  (IsLocalization.lift_eq _ _).trans <| toOpen_eq_const _ _ _
#align algebraic_geometry.structure_sheaf.to_basic_open_to_map AlgebraicGeometry.StructureSheaf.toBasicOpen_to_map

-- The proof here follows the argument in Hartshorne's Algebraic Geometry, Proposition II.2.2.
theorem toBasicOpen_injective (f : R) : Function.Injective (toBasicOpen R f) := by
  intro s t h_eq
  obtain ⟨a, ⟨b, hb⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) s
  obtain ⟨c, ⟨d, hd⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) t
  simp only [toBasicOpen_mk'] at h_eq
  rw [IsLocalization.eq]
  -- We know that the fractions `a/b` and `c/d` are equal as sections of the structure sheaf on
  -- `basicOpen f`. We need to show that they agree as elements in the localization of `R` at `f`.
  -- This amounts showing that `r * (d * a) = r * (b * c)`, for some power `r = f ^ n` of `f`.
  -- We define `I` as the ideal of *all* elements `r` satisfying the above equation.
  let I : Ideal R :=
    { carrier := { r : R | r * (d * a) = r * (b * c) }
      zero_mem' := by simp only [Set.mem_setOf_eq, zero_mul]
      add_mem' := fun {r₁ r₂} hr₁ hr₂ => by dsimp at hr₁ hr₂ ⊢; simp only [add_mul, hr₁, hr₂]
      smul_mem' := fun {r₁ r₂} hr₂ => by dsimp at hr₂ ⊢; simp only [mul_assoc, hr₂] }
  -- Our claim now reduces to showing that `f` is contained in the radical of `I`
  suffices f ∈ I.radical by
    cases' this with n hn
    exact ⟨⟨f ^ n, n, rfl⟩, hn⟩
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.mem_vanishingIdeal]
  intro p hfp
  contrapose hfp
  rw [PrimeSpectrum.mem_zeroLocus, Set.not_subset]
  have := congr_fun (congr_arg Subtype.val h_eq) ⟨p, hfp⟩
  dsimp at this
  -- Porting note: need to tell Lean what `S` is and need to change to `erw`
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  erw [IsLocalization.eq (S := Localization.AtPrime p.asIdeal)] at this
  cases' this with r hr
  exact ⟨r.1, hr, r.2⟩
#align algebraic_geometry.structure_sheaf.to_basic_open_injective AlgebraicGeometry.StructureSheaf.toBasicOpen_injective

/-
Auxiliary lemma for surjectivity of `toBasicOpen`.
Every section can locally be represented on basic opens `basicOpen g` as a fraction `f/g`
-/
theorem locally_const_basicOpen (U : Opens (PrimeSpectrum.Top R))
    (s : (structureSheaf R).1.obj (op U)) (x : U) :
    ∃ (f g : R) (i : PrimeSpectrum.basicOpen g ⟶ U), x.1 ∈ PrimeSpectrum.basicOpen g ∧
      (const R f g (PrimeSpectrum.basicOpen g) fun y hy => hy) =
      (structureSheaf R).1.map i.op s := by
  -- First, any section `s` can be represented as a fraction `f/g` on some open neighborhood of `x`
  -- and we may pass to a `basicOpen h`, since these form a basis
  obtain ⟨V, hxV : x.1 ∈ V.1, iVU, f, g, hVDg : V ≤ PrimeSpectrum.basicOpen g, s_eq⟩ :=
    exists_const R U s x.1 x.2
  obtain ⟨_, ⟨h, rfl⟩, hxDh, hDhV : PrimeSpectrum.basicOpen h ≤ V⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxV V.2
  -- The problem is of course, that `g` and `h` don't need to coincide.
  -- But, since `basicOpen h ≤ basicOpen g`, some power of `h` must be a multiple of `g`
  cases' (PrimeSpectrum.basicOpen_le_basicOpen_iff h g).mp (Set.Subset.trans hDhV hVDg) with n hn
  -- Actually, we will need a *nonzero* power of `h`.
  -- This is because we will need the equality `basicOpen (h ^ n) = basicOpen h`, which only
  -- holds for a nonzero power `n`. We therefore artificially increase `n` by one.
  replace hn := Ideal.mul_mem_right h (Ideal.span {g}) hn
  rw [← pow_succ, Ideal.mem_span_singleton'] at hn
  cases' hn with c hc
  have basic_opens_eq := PrimeSpectrum.basicOpen_pow h (n + 1) (by omega)
  have i_basic_open := eqToHom basic_opens_eq ≫ homOfLE hDhV
  -- We claim that `(f * c) / h ^ (n+1)` is our desired representation
  use f * c, h ^ (n + 1), i_basic_open ≫ iVU, (basic_opens_eq.symm.le : _) hxDh
  rw [op_comp, Functor.map_comp] --, comp_apply, ← s_eq, res_const]
  -- Porting note: `comp_apply` can't be rewritten, so use a change
  change const R _ _ _ _ = (structureSheaf R).1.map i_basic_open.op
    ((structureSheaf R).1.map iVU.op s)
  rw [← s_eq, res_const]
  -- Note that the last rewrite here generated an additional goal, which was a parameter
  -- of `res_const`. We prove this goal first
  swap
  · intro y hy
    rw [basic_opens_eq] at hy
    exact (Set.Subset.trans hDhV hVDg : _) hy
  -- All that is left is a simple calculation
  apply const_ext
  rw [mul_assoc f c g, hc]
#align algebraic_geometry.structure_sheaf.locally_const_basic_open AlgebraicGeometry.StructureSheaf.locally_const_basicOpen

/-
Auxiliary lemma for surjectivity of `toBasicOpen`.
A local representation of a section `s` as fractions `a i / h i` on finitely many basic opens
`basicOpen (h i)` can be "normalized" in such a way that `a i * h j = h i * a j` for all `i, j`
-/
theorem normalize_finite_fraction_representation (U : Opens (PrimeSpectrum.Top R))
    (s : (structureSheaf R).1.obj (op U)) {ι : Type*} (t : Finset ι) (a h : ι → R)
    (iDh : ∀ i : ι, PrimeSpectrum.basicOpen (h i) ⟶ U)
    (h_cover : U ≤ ⨆ i ∈ t, PrimeSpectrum.basicOpen (h i))
    (hs :
      ∀ i : ι,
        (const R (a i) (h i) (PrimeSpectrum.basicOpen (h i)) fun y hy => hy) =
          (structureSheaf R).1.map (iDh i).op s) :
    ∃ (a' h' : ι → R) (iDh' : ∀ i : ι, PrimeSpectrum.basicOpen (h' i) ⟶ U),
      (U ≤ ⨆ i ∈ t, PrimeSpectrum.basicOpen (h' i)) ∧
        (∀ (i) (_ : i ∈ t) (j) (_ : j ∈ t), a' i * h' j = h' i * a' j) ∧
          ∀ i ∈ t,
            (structureSheaf R).1.map (iDh' i).op s =
              const R (a' i) (h' i) (PrimeSpectrum.basicOpen (h' i)) fun y hy => hy := by
  -- First we show that the fractions `(a i * h j) / (h i * h j)` and `(h i * a j) / (h i * h j)`
  -- coincide in the localization of `R` at `h i * h j`
  have fractions_eq :
    ∀ i j : ι,
      IsLocalization.mk' (Localization.Away (h i * h j))
        (a i * h j) ⟨h i * h j, Submonoid.mem_powers _⟩ =
      IsLocalization.mk' _ (h i * a j) ⟨h i * h j, Submonoid.mem_powers _⟩ := by
    intro i j
    let D := PrimeSpectrum.basicOpen (h i * h j)
    let iDi : D ⟶ PrimeSpectrum.basicOpen (h i) := homOfLE (PrimeSpectrum.basicOpen_mul_le_left _ _)
    let iDj : D ⟶ PrimeSpectrum.basicOpen (h j) :=
      homOfLE (PrimeSpectrum.basicOpen_mul_le_right _ _)
    -- Crucially, we need injectivity of `toBasicOpen`
    apply toBasicOpen_injective R (h i * h j)
    rw [toBasicOpen_mk', toBasicOpen_mk']
    simp only []
    -- Here, both sides of the equation are equal to a restriction of `s`
    trans
    on_goal 1 =>
      convert congr_arg ((structureSheaf R).1.map iDj.op) (hs j).symm using 1
      convert congr_arg ((structureSheaf R).1.map iDi.op) (hs i) using 1
    all_goals rw [res_const]; apply const_ext; ring
    -- The remaining two goals were generated during the rewrite of `res_const`
    -- These can be solved immediately
    exacts [PrimeSpectrum.basicOpen_mul_le_left _ _, PrimeSpectrum.basicOpen_mul_le_right _ _]
  -- From the equality in the localization, we obtain for each `(i,j)` some power `(h i * h j) ^ n`
  -- which equalizes `a i * h j` and `h i * a j`
  have exists_power :
    ∀ i j : ι, ∃ n : ℕ, a i * h j * (h i * h j) ^ n = h i * a j * (h i * h j) ^ n := by
    intro i j
    obtain ⟨⟨c, n, rfl⟩, hc⟩ := IsLocalization.eq.mp (fractions_eq i j)
    use n + 1
    rw [pow_succ]
    dsimp at hc
    convert hc using 1 <;> ring
  let n := fun p : ι × ι => (exists_power p.1 p.2).choose
  have n_spec := fun p : ι × ι => (exists_power p.fst p.snd).choose_spec
  -- We need one power `(h i * h j) ^ N` that works for *all* pairs `(i,j)`
  -- Since there are only finitely many indices involved, we can pick the supremum.
  let N := (t ×ˢ t).sup n
  have basic_opens_eq : ∀ i : ι, PrimeSpectrum.basicOpen (h i ^ (N + 1)) =
    PrimeSpectrum.basicOpen (h i) := fun i => PrimeSpectrum.basicOpen_pow _ _ (by omega)
  -- Expanding the fraction `a i / h i` by the power `(h i) ^ n` gives the desired normalization
  refine'
    ⟨fun i => a i * h i ^ N, fun i => h i ^ (N + 1), fun i => eqToHom (basic_opens_eq i) ≫ iDh i,
      _, _, _⟩
  · simpa only [basic_opens_eq] using h_cover
  · intro i hi j hj
    -- Here we need to show that our new fractions `a i / h i` satisfy the normalization condition
    -- Of course, the power `N` we used to expand the fractions might be bigger than the power
    -- `n (i, j)` which was originally chosen. We denote their difference by `k`
    have n_le_N : n (i, j) ≤ N := Finset.le_sup (Finset.mem_product.mpr ⟨hi, hj⟩)
    cases' Nat.le.dest n_le_N with k hk
    simp only [← hk, pow_add, pow_one]
    -- To accommodate for the difference `k`, we multiply both sides of the equation `n_spec (i, j)`
    -- by `(h i * h j) ^ k`
    convert congr_arg (fun z => z * (h i * h j) ^ k) (n_spec (i, j)) using 1 <;>
      · simp only [n, mul_pow]; ring
  -- Lastly, we need to show that the new fractions still represent our original `s`
  intro i _
  rw [op_comp, Functor.map_comp]
  -- Porting note: `comp_apply` can't be rewritten, so use a change
  change (structureSheaf R).1.map (eqToHom (basic_opens_eq _)).op
    ((structureSheaf R).1.map (iDh i).op s) = _
  rw [← hs, res_const]
  -- additional goal spit out by `res_const`
  swap
  · exact (basic_opens_eq i).le
  apply const_ext
  dsimp
  rw [pow_succ]
  ring
#align algebraic_geometry.structure_sheaf.normalize_finite_fraction_representation AlgebraicGeometry.StructureSheaf.normalize_finite_fraction_representation

open scoped Classical

open scoped BigOperators

-- Porting note: in the following proof there are two places where `⋃ i, ⋃ (hx : i ∈ _), ... `
-- though `hx` is not used in `...` part, it is still required to maintain the structure of
-- the original proof in mathlib3.
set_option linter.unusedVariables false in
-- The proof here follows the argument in Hartshorne's Algebraic Geometry, Proposition II.2.2.
theorem toBasicOpen_surjective (f : R) : Function.Surjective (toBasicOpen R f) := by
  intro s
  -- In this proof, `basicOpen f` will play two distinct roles: Firstly, it is an open set in the
  -- prime spectrum. Secondly, it is used as an indexing type for various families of objects
  -- (open sets, ring elements, ...). In order to make the distinction clear, we introduce a type
  -- alias `ι` that is used whenever we want think of it as an indexing type.
  let ι : Type u := PrimeSpectrum.basicOpen f
  -- First, we pick some cover of basic opens, on which we can represent `s` as a fraction
  choose a' h' iDh' hxDh' s_eq' using locally_const_basicOpen R (PrimeSpectrum.basicOpen f) s
  -- Since basic opens are compact, we can pass to a finite subcover
  obtain ⟨t, ht_cover'⟩ :=
    (PrimeSpectrum.isCompact_basicOpen f).elim_finite_subcover
      (fun i : ι => PrimeSpectrum.basicOpen (h' i)) (fun i => PrimeSpectrum.isOpen_basicOpen)
      -- Here, we need to show that our basic opens actually form a cover of `basicOpen f`
      fun x hx => by rw [Set.mem_iUnion]; exact ⟨⟨x, hx⟩, hxDh' ⟨x, hx⟩⟩
  simp only [← Opens.coe_iSup, SetLike.coe_subset_coe] at ht_cover'
  -- We use the normalization lemma from above to obtain the relation `a i * h j = h i * a j`
  obtain ⟨a, h, iDh, ht_cover, ah_ha, s_eq⟩ :=
    normalize_finite_fraction_representation R (PrimeSpectrum.basicOpen f)
      s t a' h' iDh' ht_cover' s_eq'
  clear s_eq' iDh' hxDh' ht_cover' a' h'
  -- Porting note: simp with `[← SetLike.coe_subset_coe, Opens.coe_iSup]` does not result in
  -- desired form
  rw [← SetLike.coe_subset_coe, Opens.coe_iSup] at ht_cover
  replace ht_cover : (PrimeSpectrum.basicOpen f : Set <| PrimeSpectrum R) ⊆
      ⋃ (i : ι) (x : i ∈ t), (PrimeSpectrum.basicOpen (h i) : Set _) := by
    convert ht_cover using 2
    exact funext fun j => by rw [Opens.coe_iSup]
  -- Next we show that some power of `f` is a linear combination of the `h i`
  obtain ⟨n, hn⟩ : f ∈ (Ideal.span (h '' ↑t)).radical := by
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.zeroLocus_span]
    -- Porting note: simp with `PrimeSpectrum.basicOpen_eq_zeroLocus_compl` does not work
    replace ht_cover : (PrimeSpectrum.zeroLocus {f})ᶜ ⊆
        ⋃ (i : ι) (x : i ∈ t), (PrimeSpectrum.zeroLocus {h i})ᶜ := by
      convert ht_cover
      · rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
      · simp only [Opens.iSup_mk, Opens.carrier_eq_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
    rw [Set.compl_subset_comm] at ht_cover
    -- Why doesn't `simp_rw` do this?
    simp_rw [Set.compl_iUnion, compl_compl, ← PrimeSpectrum.zeroLocus_iUnion,
      ← Finset.set_biUnion_coe, ← Set.image_eq_iUnion] at ht_cover
    apply PrimeSpectrum.vanishingIdeal_anti_mono ht_cover
    exact PrimeSpectrum.subset_vanishingIdeal_zeroLocus {f} (Set.mem_singleton f)
  replace hn := Ideal.mul_mem_right f _ hn
  erw [← pow_succ, Finsupp.mem_span_image_iff_total] at hn
  rcases hn with ⟨b, b_supp, hb⟩
  rw [Finsupp.total_apply_of_mem_supported R b_supp] at hb
  dsimp at hb
  -- Finally, we have all the ingredients.
  -- We claim that our preimage is given by `(∑ (i : ι) in t, b i * a i) / f ^ (n+1)`
  use
    IsLocalization.mk' (Localization.Away f) (∑ i : ι in t, b i * a i)
      (⟨f ^ (n + 1), n + 1, rfl⟩ : Submonoid.powers _)
  rw [toBasicOpen_mk']
  -- Since the structure sheaf is a sheaf, we can show the desired equality locally.
  -- Annoyingly, `Sheaf.eq_of_locally_eq'` requires an open cover indexed by a *type*, so we need to
  -- coerce our finset `t` to a type first.
  let tt := ((t : Set (PrimeSpectrum.basicOpen f)) : Type u)
  apply
    (structureSheaf R).eq_of_locally_eq' (fun i : tt => PrimeSpectrum.basicOpen (h i))
      (PrimeSpectrum.basicOpen f) fun i : tt => iDh i
  · -- This feels a little redundant, since already have `ht_cover` as a hypothesis
    -- Unfortunately, `ht_cover` uses a bounded union over the set `t`, while here we have the
    -- Union indexed by the type `tt`, so we need some boilerplate to translate one to the other
    intro x hx
    erw [TopologicalSpace.Opens.mem_iSup]
    have := ht_cover hx
    rw [← Finset.set_biUnion_coe, Set.mem_iUnion₂] at this
    rcases this with ⟨i, i_mem, x_mem⟩
    exact ⟨⟨i, i_mem⟩, x_mem⟩
  rintro ⟨i, hi⟩
  dsimp
  change (structureSheaf R).1.map _ _ = (structureSheaf R).1.map _ _
  rw [s_eq i hi, res_const]
  -- Again, `res_const` spits out an additional goal
  swap
  · intro y hy
    change y ∈ PrimeSpectrum.basicOpen (f ^ (n + 1))
    rw [PrimeSpectrum.basicOpen_pow f (n + 1) (by omega)]
    exact (leOfHom (iDh i) : _) hy
  -- The rest of the proof is just computation
  apply const_ext
  rw [← hb, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc, ah_ha j hj i hi]
  ring
#align algebraic_geometry.structure_sheaf.to_basic_open_surjective AlgebraicGeometry.StructureSheaf.toBasicOpen_surjective

instance isIso_toBasicOpen (f : R) :
    IsIso (show CommRingCat.of (Localization.Away f) ⟶ _ from toBasicOpen R f) :=
  haveI : IsIso ((forget CommRingCat).map
      (show CommRingCat.of (Localization.Away f) ⟶ _ from toBasicOpen R f)) :=
    (isIso_iff_bijective _).mpr ⟨toBasicOpen_injective R f, toBasicOpen_surjective R f⟩
  isIso_of_reflects_iso _ (forget CommRingCat)
#align algebraic_geometry.structure_sheaf.is_iso_to_basic_open AlgebraicGeometry.StructureSheaf.isIso_toBasicOpen

/-- The ring isomorphism between the structure sheaf on `basicOpen f` and the localization of `R`
at the submonoid of powers of `f`. -/
def basicOpenIso (f : R) :
    (structureSheaf R).1.obj (op (PrimeSpectrum.basicOpen f)) ≅
    CommRingCat.of (Localization.Away f) :=
  (asIso (show CommRingCat.of (Localization.Away f) ⟶ _ from toBasicOpen R f)).symm
#align algebraic_geometry.structure_sheaf.basic_open_iso AlgebraicGeometry.StructureSheaf.basicOpenIso

instance stalkAlgebra (p : PrimeSpectrum R) : Algebra R ((structureSheaf R).presheaf.stalk p) :=
  (toStalk R p).toAlgebra
#align algebraic_geometry.structure_sheaf.stalk_algebra AlgebraicGeometry.StructureSheaf.stalkAlgebra

@[simp]
theorem stalkAlgebra_map (p : PrimeSpectrum R) (r : R) :
    algebraMap R ((structureSheaf R).presheaf.stalk p) r = toStalk R p r :=
  rfl
#align algebraic_geometry.structure_sheaf.stalk_algebra_map AlgebraicGeometry.StructureSheaf.stalkAlgebra_map

/-- Stalk of the structure sheaf at a prime p as localization of R -/
instance IsLocalization.to_stalk (p : PrimeSpectrum R) :
    IsLocalization.AtPrime ((structureSheaf R).presheaf.stalk p) p.asIdeal := by
  convert (IsLocalization.isLocalization_iff_of_ringEquiv (S := Localization.AtPrime p.asIdeal) _
          (stalkIso R p).symm.commRingCatIsoToRingEquiv).mp
      Localization.isLocalization
  apply Algebra.algebra_ext
  intro
  rw [stalkAlgebra_map]
  congr 1
  change toStalk R p = _ ≫ (stalkIso R p).inv
  erw [Iso.eq_comp_inv]
  exact toStalk_comp_stalkToFiberRingHom R p
#align algebraic_geometry.structure_sheaf.is_localization.to_stalk AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk

instance openAlgebra (U : (Opens (PrimeSpectrum R))ᵒᵖ) : Algebra R ((structureSheaf R).val.obj U) :=
  (toOpen R (unop U)).toAlgebra
#align algebraic_geometry.structure_sheaf.open_algebra AlgebraicGeometry.StructureSheaf.openAlgebra

@[simp]
theorem openAlgebra_map (U : (Opens (PrimeSpectrum R))ᵒᵖ) (r : R) :
    algebraMap R ((structureSheaf R).val.obj U) r = toOpen R (unop U) r :=
  rfl
#align algebraic_geometry.structure_sheaf.open_algebra_map AlgebraicGeometry.StructureSheaf.openAlgebra_map

/-- Sections of the structure sheaf of Spec R on a basic open as localization of R -/
instance IsLocalization.to_basicOpen (r : R) :
    IsLocalization.Away r ((structureSheaf R).val.obj (op <| PrimeSpectrum.basicOpen r)) := by
  convert (IsLocalization.isLocalization_iff_of_ringEquiv (S := Localization.Away r) _
      (basicOpenIso R r).symm.commRingCatIsoToRingEquiv).mp
      Localization.isLocalization
  apply Algebra.algebra_ext
  intro x
  congr 1
  exact (localization_toBasicOpen R r).symm
#align algebraic_geometry.structure_sheaf.is_localization.to_basic_open AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen

instance to_basicOpen_epi (r : R) : Epi (toOpen R (PrimeSpectrum.basicOpen r)) :=
  ⟨fun _ _ h => IsLocalization.ringHom_ext (Submonoid.powers r) h⟩
#align algebraic_geometry.structure_sheaf.to_basic_open_epi AlgebraicGeometry.StructureSheaf.to_basicOpen_epi

@[elementwise]
theorem to_global_factors :
    toOpen R ⊤ =
      CommRingCat.ofHom (algebraMap R (Localization.Away (1 : R))) ≫
        toBasicOpen R (1 : R) ≫
        (structureSheaf R).1.map (eqToHom PrimeSpectrum.basicOpen_one.symm).op := by
  rw [← Category.assoc]
  change toOpen R ⊤ =
    (CommRingCat.ofHom <| (toBasicOpen R 1).comp (algebraMap R (Localization.Away 1))) ≫
    (structureSheaf R).1.map (eqToHom _).op
  unfold CommRingCat.ofHom
  rw [localization_toBasicOpen R, toOpen_res]
#align algebraic_geometry.structure_sheaf.to_global_factors AlgebraicGeometry.StructureSheaf.to_global_factors

instance isIso_to_global : IsIso (toOpen R ⊤) := by
  let hom := CommRingCat.ofHom (algebraMap R (Localization.Away (1 : R)))
  haveI : IsIso hom :=
    IsIso.of_iso (IsLocalization.atOne R (Localization.Away (1 : R))).toRingEquiv.toCommRingCatIso
  rw [to_global_factors R]
  infer_instance
#align algebraic_geometry.structure_sheaf.is_iso_to_global AlgebraicGeometry.StructureSheaf.isIso_to_global

/-- The ring isomorphism between the ring `R` and the global sections `Γ(X, 𝒪ₓ)`. -/
-- Porting note: was @[simps (config := { rhsMd := Tactic.Transparency.semireducible })]
@[simps!]
def globalSectionsIso : CommRingCat.of R ≅ (structureSheaf R).1.obj (op ⊤) :=
  asIso (toOpen R ⊤)
#align algebraic_geometry.structure_sheaf.global_sections_iso AlgebraicGeometry.StructureSheaf.globalSectionsIso

-- These lemmas have always been bad (#7657), but leanprover/lean4#2644 made `simp` start noticing
attribute [nolint simpNF] AlgebraicGeometry.StructureSheaf.globalSectionsIso_hom_apply_coe

@[simp]
theorem globalSectionsIso_hom (R : CommRingCat) : (globalSectionsIso R).hom = toOpen R ⊤ :=
  rfl
#align algebraic_geometry.structure_sheaf.global_sections_iso_hom AlgebraicGeometry.StructureSheaf.globalSectionsIso_hom

@[simp, reassoc, elementwise]
theorem toStalk_stalkSpecializes {R : Type*} [CommRing R] {x y : PrimeSpectrum R} (h : x ⤳ y) :
    toStalk R y ≫ (structureSheaf R).presheaf.stalkSpecializes h = toStalk R x := by
  dsimp [toStalk]; simp [-toOpen_germ]
#align algebraic_geometry.structure_sheaf.to_stalk_stalk_specializes AlgebraicGeometry.StructureSheaf.toStalk_stalkSpecializes

@[simp, reassoc, elementwise]
theorem localizationToStalk_stalkSpecializes {R : Type*} [CommRing R] {x y : PrimeSpectrum R}
    (h : x ⤳ y) :
    StructureSheaf.localizationToStalk R y ≫ (structureSheaf R).presheaf.stalkSpecializes h =
      CommRingCat.ofHom (PrimeSpectrum.localizationMapOfSpecializes h) ≫
        StructureSheaf.localizationToStalk R x := by
  apply IsLocalization.ringHom_ext (S := Localization.AtPrime y.asIdeal) y.asIdeal.primeCompl
  erw [RingHom.comp_assoc]
  conv_rhs => erw [RingHom.comp_assoc]
  dsimp [CommRingCat.ofHom, localizationToStalk, PrimeSpectrum.localizationMapOfSpecializes]
  rw [IsLocalization.lift_comp, IsLocalization.lift_comp, IsLocalization.lift_comp]
  exact toStalk_stalkSpecializes h
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.structure_sheaf.localizationToStalk_stalk_specializes AlgebraicGeometry.StructureSheaf.localizationToStalk_stalkSpecializes

@[simp, reassoc, elementwise]
theorem stalkSpecializes_stalk_to_fiber {R : Type*} [CommRing R] {x y : PrimeSpectrum R}
    (h : x ⤳ y) :
    (structureSheaf R).presheaf.stalkSpecializes h ≫ StructureSheaf.stalkToFiberRingHom R x =
      StructureSheaf.stalkToFiberRingHom R y ≫
      -- Porting note: `PrimeSpectrum.localizationMapOfSpecializes h` by itself is interpreted as a
      -- ring homomorphism, so it is changed in a way to force it being interpreted as categorical
      -- arrow.
      (show CommRingCat.of (Localization.AtPrime y.asIdeal) ⟶
        CommRingCat.of (Localization.AtPrime x.asIdeal)
        from PrimeSpectrum.localizationMapOfSpecializes h) := by
  change _ ≫ (StructureSheaf.stalkIso R x).hom = (StructureSheaf.stalkIso R y).hom ≫ _
  rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  exact localizationToStalk_stalkSpecializes h
#align algebraic_geometry.structure_sheaf.stalk_specializes_stalk_to_fiber AlgebraicGeometry.StructureSheaf.stalkSpecializes_stalk_to_fiber

section Comap

variable {R} {S : Type u} [CommRing S] {P : Type u} [CommRing P]

/--
Given a ring homomorphism `f : R →+* S`, an open set `U` of the prime spectrum of `R` and an open
set `V` of the prime spectrum of `S`, such that `V ⊆ (comap f) ⁻¹' U`, we can push a section `s`
on `U` to a section on `V`, by composing with `Localization.localRingHom _ _ f` from the left and
`comap f` from the right. Explicitly, if `s` evaluates on `comap f p` to `a / b`, its image on `V`
evaluates on `p` to `f(a) / f(b)`.

At the moment, we work with arbitrary dependent functions `s : Π x : U, Localizations R x`. Below,
we prove the predicate `isLocallyFraction` is preserved by this map, hence it can be extended to
a morphism between the structure sheaves of `R` and `S`.
-/
def comapFun (f : R →+* S) (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) (s : ∀ x : U, Localizations R x) (y : V) :
    Localizations S y :=
  Localization.localRingHom (PrimeSpectrum.comap f y.1).asIdeal _ f rfl
    (s ⟨PrimeSpectrum.comap f y.1, hUV y.2⟩ : _)
#align algebraic_geometry.structure_sheaf.comap_fun AlgebraicGeometry.StructureSheaf.comapFun

theorem comapFunIsLocallyFraction (f : R →+* S) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1)
    (s : ∀ x : U, Localizations R x) (hs : (isLocallyFraction R).toPrelocalPredicate.pred s) :
    (isLocallyFraction S).toPrelocalPredicate.pred (comapFun f U V hUV s) := by
  rintro ⟨p, hpV⟩
  -- Since `s` is locally fraction, we can find a neighborhood `W` of `PrimeSpectrum.comap f p`
  -- in `U`, such that `s = a / b` on `W`, for some ring elements `a, b : R`.
  rcases hs ⟨PrimeSpectrum.comap f p, hUV hpV⟩ with ⟨W, m, iWU, a, b, h_frac⟩
  -- We claim that we can write our new section as the fraction `f a / f b` on the neighborhood
  -- `(comap f) ⁻¹ W ⊓ V` of `p`.
  refine' ⟨Opens.comap (PrimeSpectrum.comap f) W ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, f a, f b, _⟩
  rintro ⟨q, ⟨hqW, hqV⟩⟩
  specialize h_frac ⟨PrimeSpectrum.comap f q, hqW⟩
  refine' ⟨h_frac.1, _⟩
  dsimp only [comapFun]
  erw [← Localization.localRingHom_to_map (PrimeSpectrum.comap f q).asIdeal, ← RingHom.map_mul,
    h_frac.2, Localization.localRingHom_to_map]
  rfl
#align algebraic_geometry.structure_sheaf.comap_fun_is_locally_fraction AlgebraicGeometry.StructureSheaf.comapFunIsLocallyFraction

/-- For a ring homomorphism `f : R →+* S` and open sets `U` and `V` of the prime spectra of `R` and
`S` such that `V ⊆ (comap f) ⁻¹ U`, the induced ring homomorphism from the structure sheaf of `R`
at `U` to the structure sheaf of `S` at `V`.

Explicitly, this map is given as follows: For a point `p : V`, if the section `s` evaluates on `p`
to the fraction `a / b`, its image on `V` evaluates on `p` to the fraction `f(a) / f(b)`.
-/
def comap (f : R →+* S) (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) :
    (structureSheaf R).1.obj (op U) →+* (structureSheaf S).1.obj (op V) where
  toFun s := ⟨comapFun f U V hUV s.1, comapFunIsLocallyFraction f U V hUV s.1 s.2⟩
  map_one' :=
    Subtype.ext <|
      funext fun p => by
        dsimp
        rw [comapFun, (sectionsSubring R (op U)).coe_one, Pi.one_apply, RingHom.map_one]
        rfl
  map_zero' :=
    Subtype.ext <|
      funext fun p => by
        dsimp
        rw [comapFun, (sectionsSubring R (op U)).coe_zero, Pi.zero_apply, RingHom.map_zero]
        rfl
  map_add' s t :=
    Subtype.ext <|
      funext fun p => by
        dsimp
        rw [comapFun, (sectionsSubring R (op U)).coe_add, Pi.add_apply, RingHom.map_add]
        rfl
  map_mul' s t :=
    Subtype.ext <|
      funext fun p => by
        dsimp
        rw [comapFun, (sectionsSubring R (op U)).coe_mul, Pi.mul_apply, RingHom.map_mul]
        rfl
#align algebraic_geometry.structure_sheaf.comap AlgebraicGeometry.StructureSheaf.comap

@[simp]
theorem comap_apply (f : R →+* S) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1)
    (s : (structureSheaf R).1.obj (op U)) (p : V) :
    (comap f U V hUV s).1 p =
      Localization.localRingHom (PrimeSpectrum.comap f p.1).asIdeal _ f rfl
        (s.1 ⟨PrimeSpectrum.comap f p.1, hUV p.2⟩ : _) :=
  rfl
#align algebraic_geometry.structure_sheaf.comap_apply AlgebraicGeometry.StructureSheaf.comap_apply

theorem comap_const (f : R →+* S) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) (a b : R)
    (hb : ∀ x : PrimeSpectrum R, x ∈ U → b ∈ x.asIdeal.primeCompl) :
    comap f U V hUV (const R a b U hb) =
      const S (f a) (f b) V fun p hpV => hb (PrimeSpectrum.comap f p) (hUV hpV) :=
  Subtype.eq <|
    funext fun p => by
      rw [comap_apply, const_apply, const_apply]
      erw [Localization.localRingHom_mk']
      rfl
#align algebraic_geometry.structure_sheaf.comap_const AlgebraicGeometry.StructureSheaf.comap_const

/-- For an inclusion `i : V ⟶ U` between open sets of the prime spectrum of `R`, the comap of the
identity from OO_X(U) to OO_X(V) equals as the restriction map of the structure sheaf.

This is a generalization of the fact that, for fixed `U`, the comap of the identity from OO_X(U)
to OO_X(U) is the identity.
-/
theorem comap_id_eq_map (U V : Opens (PrimeSpectrum.Top R)) (iVU : V ⟶ U) :
    (comap (RingHom.id R) U V fun p hpV => leOfHom iVU <| hpV) =
      (structureSheaf R).1.map iVU.op :=
  RingHom.ext fun s => Subtype.eq <| funext fun p => by
    rw [comap_apply]
    -- Unfortunately, we cannot use `Localization.localRingHom_id` here, because
    -- `PrimeSpectrum.comap (RingHom.id R) p` is not *definitionally* equal to `p`. Instead, we use
    -- that we can write `s` as a fraction `a/b` in a small neighborhood around `p`. Since
    -- `PrimeSpectrum.comap (RingHom.id R) p` equals `p`, it is also contained in the same
    -- neighborhood, hence `s` equals `a/b` there too.
    obtain ⟨W, hpW, iWU, h⟩ := s.2 (iVU p)
    obtain ⟨a, b, h'⟩ := h.eq_mk'
    obtain ⟨hb₁, s_eq₁⟩ := h' ⟨p, hpW⟩
    obtain ⟨hb₂, s_eq₂⟩ :=
      h' ⟨PrimeSpectrum.comap (RingHom.id _) p.1, hpW⟩
    dsimp only at s_eq₁ s_eq₂
    erw [s_eq₂, Localization.localRingHom_mk', ← s_eq₁, ← res_apply _ _ _ iVU]
#align algebraic_geometry.structure_sheaf.comap_id_eq_map AlgebraicGeometry.StructureSheaf.comap_id_eq_map

/--
The comap of the identity is the identity. In this variant of the lemma, two open subsets `U` and
`V` are given as arguments, together with a proof that `U = V`. This is useful when `U` and `V`
are not definitionally equal.
-/
theorem comap_id (U V : Opens (PrimeSpectrum.Top R)) (hUV : U = V) :
    (comap (RingHom.id R) U V fun p hpV => by rwa [hUV, PrimeSpectrum.comap_id]) =
      eqToHom (show (structureSheaf R).1.obj (op U) = _ by rw [hUV]) :=
  by erw [comap_id_eq_map U V (eqToHom hUV.symm), eqToHom_op, eqToHom_map]
#align algebraic_geometry.structure_sheaf.comap_id AlgebraicGeometry.StructureSheaf.comap_id

@[simp]
theorem comap_id' (U : Opens (PrimeSpectrum.Top R)) :
    (comap (RingHom.id R) U U fun p hpU => by rwa [PrimeSpectrum.comap_id]) = RingHom.id _ := by
  rw [comap_id U U rfl]; rfl
#align algebraic_geometry.structure_sheaf.comap_id' AlgebraicGeometry.StructureSheaf.comap_id'

theorem comap_comp (f : R →+* S) (g : S →+* P) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (W : Opens (PrimeSpectrum.Top P))
    (hUV : ∀ p ∈ V, PrimeSpectrum.comap f p ∈ U) (hVW : ∀ p ∈ W, PrimeSpectrum.comap g p ∈ V) :
    (comap (g.comp f) U W fun p hpW => hUV (PrimeSpectrum.comap g p) (hVW p hpW)) =
      (comap g V W hVW).comp (comap f U V hUV) :=
  RingHom.ext fun s =>
    Subtype.eq <|
      funext fun p => by
        rw [comap_apply]
        erw [Localization.localRingHom_comp _ (PrimeSpectrum.comap g p.1).asIdeal] <;>
        -- refl works here, because `PrimeSpectrum.comap (g.comp f) p` is defeq to
        -- `PrimeSpectrum.comap f (PrimeSpectrum.comap g p)`
        rfl
#align algebraic_geometry.structure_sheaf.comap_comp AlgebraicGeometry.StructureSheaf.comap_comp

@[elementwise, reassoc]
theorem toOpen_comp_comap (f : R →+* S) (U : Opens (PrimeSpectrum.Top R)) :
    (toOpen R U ≫ comap f U (Opens.comap (PrimeSpectrum.comap f) U) fun _ => id) =
      CommRingCat.ofHom f ≫ toOpen S _ :=
  RingHom.ext fun _ => Subtype.eq <| funext fun _ => Localization.localRingHom_to_map _ _ _ _ _
#align algebraic_geometry.structure_sheaf.to_open_comp_comap AlgebraicGeometry.StructureSheaf.toOpen_comp_comap

end Comap

end StructureSheaf

end AlgebraicGeometry
