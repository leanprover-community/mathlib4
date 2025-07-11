/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.HomCongr

/-!
# Reflective functors

Basic properties of reflective functors, especially those relating to their essential image.

Note properties of reflective functors relating to limits and colimits are included in
`Mathlib/CategoryTheory/Monad/Limits.lean`.
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Category Adjunction

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

/--
A functor is *reflective*, or *a reflective inclusion*, if it is fully faithful and right adjoint.
-/
class Reflective (R : D ⥤ C) extends R.Full, R.Faithful where
  /-- a choice of a left adjoint to `R` -/
  L : C ⥤ D
  /-- `R` is a right adjoint -/
  adj : L ⊣ R

variable (i : D ⥤ C)

/-- The reflector `C ⥤ D` when `R : D ⥤ C` is reflective. -/
def reflector [Reflective i] : C ⥤ D := Reflective.L (R := i)

/-- The adjunction `reflector i ⊣ i` when `i` is reflective. -/
def reflectorAdjunction [Reflective i] : reflector i ⊣ i := Reflective.adj

instance [Reflective i] : i.IsRightAdjoint := ⟨_, ⟨reflectorAdjunction i⟩⟩

instance [Reflective i] : (reflector i).IsLeftAdjoint := ⟨_, ⟨reflectorAdjunction i⟩⟩

/-- A reflective functor is fully faithful. -/
def Functor.fullyFaithfulOfReflective [Reflective i] : i.FullyFaithful :=
  (reflectorAdjunction i).fullyFaithfulROfIsIsoCounit

-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.
/-- For a reflective functor `i` (with left adjoint `L`), with unit `η`, we have `η_iL = iL η`.
-/
theorem unit_obj_eq_map_unit [Reflective i] (X : C) :
    (reflectorAdjunction i).unit.app (i.obj ((reflector i).obj X)) =
      i.map ((reflector i).map ((reflectorAdjunction i).unit.app X)) := by
  rw [← cancel_mono (i.map ((reflectorAdjunction i).counit.app ((reflector i).obj X))),
    ← i.map_comp]
  simp

/--
When restricted to objects in `D` given by `i : D ⥤ C`, the unit is an isomorphism. In other words,
`η_iX` is an isomorphism for any `X` in `D`.
More generally this applies to objects essentially in the reflective subcategory, see
`Functor.essImage.unit_isIso`.
-/
example [Reflective i] {B : D} : IsIso ((reflectorAdjunction i).unit.app (i.obj B)) :=
  inferInstance

variable {i}

/-- If `A` is essentially in the image of a reflective functor `i`, then `η_A` is an isomorphism.
This gives that the "witness" for `A` being in the essential image can instead be given as the
reflection of `A`, with the isomorphism as `η_A`.

(For any `B` in the reflective subcategory, we automatically have that `ε_B` is an iso.)
-/
theorem Functor.essImage.unit_isIso [Reflective i] {A : C} (h : i.essImage A) :
    IsIso ((reflectorAdjunction i).unit.app A) := by
  rwa [isIso_unit_app_iff_mem_essImage]

/-- If `η_A` is a split monomorphism, then `A` is in the reflective subcategory. -/
theorem mem_essImage_of_unit_isSplitMono [Reflective i] {A : C}
    [IsSplitMono ((reflectorAdjunction i).unit.app A)] : i.essImage A := by
  let η : 𝟭 C ⟶ reflector i ⋙ i := (reflectorAdjunction i).unit
  haveI : IsIso (η.app (i.obj ((reflector i).obj A))) :=
    Functor.essImage.unit_isIso ((i.obj_mem_essImage _))
  have : Epi (η.app A) := by
    refine @epi_of_epi _ _ _ _ _ (retraction (η.app A)) (η.app A) ?_
    rw [show retraction _ ≫ η.app A = _ from η.naturality (retraction (η.app A))]
    apply epi_comp (η.app (i.obj ((reflector i).obj A)))
  haveI := isIso_of_epi_of_isSplitMono (η.app A)
  exact (reflectorAdjunction i).mem_essImage_of_unit_isIso A

/-- Composition of reflective functors. -/
instance Reflective.comp (F : C ⥤ D) (G : D ⥤ E) [Reflective F] [Reflective G] :
    Reflective (F ⋙ G) where
  L := reflector G ⋙ reflector F
  adj := (reflectorAdjunction G).comp (reflectorAdjunction F)

/-- (Implementation) Auxiliary definition for `unitCompPartialBijective`. -/
def unitCompPartialBijectiveAux [Reflective i] (A : C) (B : D) :
    (A ⟶ i.obj B) ≃ (i.obj ((reflector i).obj A) ⟶ i.obj B) :=
  ((reflectorAdjunction i).homEquiv _ _).symm.trans
    (Functor.FullyFaithful.ofFullyFaithful i).homEquiv

/-- The description of the inverse of the bijection `unitCompPartialBijectiveAux`. -/
theorem unitCompPartialBijectiveAux_symm_apply [Reflective i] {A : C} {B : D}
    (f : i.obj ((reflector i).obj A) ⟶ i.obj B) :
    (unitCompPartialBijectiveAux _ _).symm f = (reflectorAdjunction i).unit.app A ≫ f := by
  simp [unitCompPartialBijectiveAux, Adjunction.homEquiv_unit]

/-- If `i` has a reflector `L`, then the function `(i.obj (L.obj A) ⟶ B) → (A ⟶ B)` given by
precomposing with `η.app A` is a bijection provided `B` is in the essential image of `i`.
That is, the function `fun (f : i.obj (L.obj A) ⟶ B) ↦ η.app A ≫ f` is bijective,
as long as `B` is in the essential image of `i`.
This definition gives an equivalence: the key property that the inverse can be described
nicely is shown in `unitCompPartialBijective_symm_apply`.

This establishes there is a natural bijection `(A ⟶ B) ≃ (i.obj (L.obj A) ⟶ B)`. In other words,
from the point of view of objects in `D`, `A` and `i.obj (L.obj A)` look the same: specifically
that `η.app A` is an isomorphism.
-/
def unitCompPartialBijective [Reflective i] (A : C) {B : C} (hB : i.essImage B) :
    (A ⟶ B) ≃ (i.obj ((reflector i).obj A) ⟶ B) :=
  calc
    (A ⟶ B) ≃ (A ⟶ i.obj (Functor.essImage.witness hB)) := Iso.homCongr (Iso.refl _) hB.getIso.symm
    _ ≃ (i.obj _ ⟶ i.obj (Functor.essImage.witness hB)) := unitCompPartialBijectiveAux _ _
    _ ≃ (i.obj ((reflector i).obj A) ⟶ B) :=
      Iso.homCongr (Iso.refl _) (Functor.essImage.getIso hB)

@[simp]
theorem unitCompPartialBijective_symm_apply [Reflective i] (A : C) {B : C} (hB : i.essImage B)
    (f) : (unitCompPartialBijective A hB).symm f = (reflectorAdjunction i).unit.app A ≫ f := by
  simp [unitCompPartialBijective, unitCompPartialBijectiveAux_symm_apply]

theorem unitCompPartialBijective_symm_natural [Reflective i] (A : C) {B B' : C} (h : B ⟶ B')
    (hB : i.essImage B) (hB' : i.essImage B') (f : i.obj ((reflector i).obj A) ⟶ B) :
    (unitCompPartialBijective A hB').symm (f ≫ h) = (unitCompPartialBijective A hB).symm f ≫ h := by
  simp

theorem unitCompPartialBijective_natural [Reflective i] (A : C) {B B' : C} (h : B ⟶ B')
    (hB : i.essImage B) (hB' : i.essImage B') (f : A ⟶ B) :
    (unitCompPartialBijective A hB') (f ≫ h) = unitCompPartialBijective A hB f ≫ h := by
  rw [← Equiv.eq_symm_apply, unitCompPartialBijective_symm_natural A h, Equiv.symm_apply_apply]

instance [Reflective i] (X : Functor.EssImageSubcategory i) :
  IsIso (NatTrans.app (reflectorAdjunction i).unit X.obj) :=
Functor.essImage.unit_isIso X.property

-- These attributes are necessary to make automation work in `equivEssImageOfReflective`.
-- Making them global doesn't break anything elsewhere, but this is enough for now.
-- TODO: investigate further.
attribute [local simp 900] ObjectProperty.ι_map in
attribute [local ext] Functor.essImage_ext in
/-- If `i : D ⥤ C` is reflective, the inverse functor of `i ≌ F.essImage` can be explicitly
defined by the reflector. -/
@[simps]
def equivEssImageOfReflective [Reflective i] : D ≌ i.EssImageSubcategory where
  functor := i.toEssImage
  inverse := i.essImage.ι ⋙ reflector i
  unitIso := (asIso <| (reflectorAdjunction i).counit).symm
  counitIso := Functor.fullyFaithfulCancelRight i.essImage.ι <|
    NatIso.ofComponents (fun X ↦ (asIso ((reflectorAdjunction i).unit.app X.obj)).symm)

/--
A functor is *coreflective*, or *a coreflective inclusion*, if it is fully faithful and left
adjoint.
-/
class Coreflective (L : C ⥤ D) extends L.Full, L.Faithful where
  /-- a choice of a right adjoint to `L` -/
  R : D ⥤ C
  /-- `L` is a left adjoint -/
  adj : L ⊣ R

variable (j : C ⥤ D)

/-- The coreflector `D ⥤ C` when `L : C ⥤ D` is coreflective. -/
def coreflector [Coreflective j] : D ⥤ C := Coreflective.R (L := j)

/-- The adjunction `j ⊣ coreflector j` when `j` is coreflective. -/
def coreflectorAdjunction [Coreflective j] : j ⊣ coreflector j := Coreflective.adj

instance [Coreflective j] : j.IsLeftAdjoint := ⟨_, ⟨coreflectorAdjunction j⟩⟩

instance [Coreflective j] : (coreflector j).IsRightAdjoint := ⟨_, ⟨coreflectorAdjunction j⟩⟩

/-- A coreflective functor is fully faithful. -/
def Functor.fullyFaithfulOfCoreflective [Coreflective j] : j.FullyFaithful :=
  (coreflectorAdjunction j).fullyFaithfulLOfIsIsoUnit

lemma counit_obj_eq_map_counit [Coreflective j] (X : D) :
    (coreflectorAdjunction j).counit.app (j.obj ((coreflector j).obj X)) =
      j.map ((coreflector j).map ((coreflectorAdjunction j).counit.app X)) := by
  rw [← cancel_epi (j.map ((coreflectorAdjunction j).unit.app ((coreflector j).obj X))),
    ← j.map_comp]
  simp

example [Coreflective j] {B : C} : IsIso ((coreflectorAdjunction j).counit.app (j.obj B)) :=
  inferInstance

variable {j}

lemma Functor.essImage.counit_isIso [Coreflective j] {A : D} (h : j.essImage A) :
    IsIso ((coreflectorAdjunction j).counit.app A) := by
  rwa [isIso_counit_app_iff_mem_essImage]

lemma mem_essImage_of_counit_isSplitEpi [Coreflective j] {A : D}
    [IsSplitEpi ((coreflectorAdjunction j).counit.app A)] : j.essImage A := by
  let ε : coreflector j ⋙ j ⟶ 𝟭 D  := (coreflectorAdjunction j).counit
  haveI : IsIso (ε.app (j.obj ((coreflector j).obj A))) :=
    Functor.essImage.counit_isIso ((j.obj_mem_essImage _))
  have : Mono (ε.app A) := by
    refine @mono_of_mono _ _ _ _ _ (ε.app A) (section_ (ε.app A)) ?_
    rw [show ε.app A ≫ section_ _ = _ from (ε.naturality (section_ (ε.app A))).symm]
    apply mono_comp _ (ε.app (j.obj ((coreflector j).obj A)))
  haveI := isIso_of_mono_of_isSplitEpi (ε.app A)
  exact (coreflectorAdjunction j).mem_essImage_of_counit_isIso A

instance Coreflective.comp (F : C ⥤ D) (G : D ⥤ E) [Coreflective F] [Coreflective G] :
    Coreflective (F ⋙ G) where
  R := coreflector G ⋙ coreflector F
  adj := (coreflectorAdjunction F).comp (coreflectorAdjunction G)

end CategoryTheory
