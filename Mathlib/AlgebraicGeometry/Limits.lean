/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.AffineScheme

#align_import algebraic_geometry.limits from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# (Co)Limits of Schemes

We construct various limits and colimits in the category of schemes.

* The existence of fibred products was shown in `Mathlib/AlgebraicGeometry/Pullbacks.lean`.
* `Spec ℤ` is the terminal object.
* The preceding two results imply that `Scheme` has all finite limits.
* The empty scheme is the (strict) initial object.

## Todo

* Coproducts exists (and the forgetful functors preserve them).

-/

suppress_compilation

set_option linter.uppercaseLean3 false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- `Spec ℤ` is the terminal object in the category of schemes. -/
noncomputable def specZIsTerminal : IsTerminal (Scheme.Spec.obj (op <| CommRingCat.of ℤ)) :=
  @IsTerminal.isTerminalObj _ _ _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.zIsInitial)
#align algebraic_geometry.Spec_Z_is_terminal AlgebraicGeometry.specZIsTerminal

instance : HasTerminal Scheme :=
  hasTerminal_of_hasTerminal_of_preservesLimit Scheme.Spec

instance : IsAffine (⊤_ Scheme.{u}) :=
  isAffineOfIso (PreservesTerminal.iso Scheme.Spec).inv

instance : HasFiniteLimits Scheme :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

section Initial

/-- The map from the empty scheme. -/
@[simps]
def Scheme.emptyTo (X : Scheme.{u}) : ∅ ⟶ X :=
  ⟨{  base := ⟨fun x => PEmpty.elim x, by continuity⟩
      c := { app := fun U => CommRingCat.punitIsTerminal.from _ } }, fun x => PEmpty.elim x⟩
#align algebraic_geometry.Scheme.empty_to AlgebraicGeometry.Scheme.emptyTo

@[ext]
theorem Scheme.empty_ext {X : Scheme.{u}} (f g : ∅ ⟶ X) : f = g :=
  -- Porting note: `ext` regression
  -- see https://github.com/leanprover-community/mathlib4/issues/5229
  LocallyRingedSpace.Hom.ext _ _ <| PresheafedSpace.ext _ _ (by ext a; exact PEmpty.elim a) <|
    NatTrans.ext _ _ <| funext fun a => by aesop_cat
#align algebraic_geometry.Scheme.empty_ext AlgebraicGeometry.Scheme.empty_ext

theorem Scheme.eq_emptyTo {X : Scheme.{u}} (f : ∅ ⟶ X) : f = Scheme.emptyTo X :=
  Scheme.empty_ext f (Scheme.emptyTo X)
#align algebraic_geometry.Scheme.eq_empty_to AlgebraicGeometry.Scheme.eq_emptyTo

instance Scheme.hom_unique_of_empty_source (X : Scheme.{u}) : Unique (∅ ⟶ X) :=
  ⟨⟨Scheme.emptyTo _⟩, fun _ => Scheme.empty_ext _ _⟩

/-- The empty scheme is the initial object in the category of schemes. -/
def emptyIsInitial : IsInitial (∅ : Scheme.{u}) :=
  IsInitial.ofUnique _
#align algebraic_geometry.empty_is_initial AlgebraicGeometry.emptyIsInitial

@[simp]
theorem emptyIsInitial_to : emptyIsInitial.to = Scheme.emptyTo :=
  rfl
#align algebraic_geometry.empty_is_initial_to AlgebraicGeometry.emptyIsInitial_to

instance : IsEmpty Scheme.empty.carrier :=
  show IsEmpty PEmpty by infer_instance

instance spec_punit_isEmpty : IsEmpty (Scheme.Spec.obj (op <| CommRingCat.of PUnit)).carrier :=
  inferInstanceAs <| IsEmpty (PrimeSpectrum PUnit)
#align algebraic_geometry.Spec_punit_is_empty AlgebraicGeometry.spec_punit_isEmpty

instance (priority := 100) isOpenImmersion_of_isEmpty {X Y : Scheme} (f : X ⟶ Y)
    [IsEmpty X.carrier] : IsOpenImmersion f := by
  apply (config := { allowSynthFailures := true }) IsOpenImmersion.of_stalk_iso
  · exact .of_isEmpty (X := X.carrier) _
  · intro (i : X.carrier); exact isEmptyElim i
#align algebraic_geometry.is_open_immersion_of_is_empty AlgebraicGeometry.isOpenImmersion_of_isEmpty

instance (priority := 100) isIso_of_isEmpty {X Y : Scheme} (f : X ⟶ Y) [IsEmpty Y.carrier] :
    IsIso f := by
  haveI : IsEmpty X.carrier := f.1.base.1.isEmpty
  have : Epi f.1.base := by
    rw [TopCat.epi_iff_surjective]; rintro (x : Y.carrier)
    exact isEmptyElim x
  apply IsOpenImmersion.to_iso
#align algebraic_geometry.is_iso_of_is_empty AlgebraicGeometry.isIso_of_isEmpty

/-- A scheme is initial if its underlying space is empty . -/
noncomputable def isInitialOfIsEmpty {X : Scheme} [IsEmpty X.carrier] : IsInitial X :=
  emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)
#align algebraic_geometry.is_initial_of_is_empty AlgebraicGeometry.isInitialOfIsEmpty

/-- `Spec 0` is the initial object in the category of schemes. -/
noncomputable def specPunitIsInitial : IsInitial (Scheme.Spec.obj (op <| CommRingCat.of PUnit)) :=
  emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)
#align algebraic_geometry.Spec_punit_is_initial AlgebraicGeometry.specPunitIsInitial

instance (priority := 100) isAffine_of_isEmpty {X : Scheme} [IsEmpty X.carrier] : IsAffine X :=
  isAffineOfIso
    (inv (emptyIsInitial.to X) ≫ emptyIsInitial.to (Scheme.Spec.obj (op <| CommRingCat.of PUnit)))
#align algebraic_geometry.is_affine_of_is_empty AlgebraicGeometry.isAffine_of_isEmpty

instance : HasInitial Scheme :=
  -- Porting note: this instance was not needed
  haveI : (Y : Scheme) → Unique (Scheme.empty ⟶ Y) := Scheme.hom_unique_of_empty_source
  hasInitial_of_unique Scheme.empty

instance initial_isEmpty : IsEmpty (⊥_ Scheme).carrier :=
  ⟨fun x => ((initial.to Scheme.empty : _).1.base x).elim⟩
#align algebraic_geometry.initial_is_empty AlgebraicGeometry.initial_isEmpty

theorem bot_isAffineOpen (X : Scheme) : IsAffineOpen (⊥ : Opens X.carrier) := by
  convert rangeIsAffineOpenOfOpenImmersion (initial.to X)
  ext
  -- Porting note: added this `erw` to turn LHS to `False`
  erw [Set.mem_empty_iff_false]
  rw [false_iff_iff]
  exact fun x => isEmptyElim (show (⊥_ Scheme).carrier from x.choose)
#align algebraic_geometry.bot_is_affine_open AlgebraicGeometry.bot_isAffineOpen

instance : HasStrictInitialObjects Scheme :=
  hasStrictInitialObjects_of_initial_is_strict fun A f => by infer_instance

end Initial

end AlgebraicGeometry
