/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# The category of commutative monoids in a braided monoidal category.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory MonoidalCategory MonObj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

variable (C) in
/-- A commutative monoid object internal to a monoidal category.
-/
structure CommMon_ where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [mon : MonObj X]
  [comm : IsCommMon X]

attribute [instance] CommMon_.mon CommMon_.comm

namespace CommMon_

/-- A commutative monoid object is a monoid object. -/
@[simps X]
def toMon_ (A : CommMon_ C) : Mon_ C := ⟨A.X⟩

variable (C) in
/-- The trivial commutative monoid object. We later show this is initial in `CommMon_ C`.
-/
@[simps!]
def trivial : CommMon_ C := { X := 𝟙_ C }

instance : Inhabited (CommMon_ C) :=
  ⟨trivial C⟩

variable {M : CommMon_ C}

instance : Category (CommMon_ C) :=
  InducedCategory.category CommMon_.toMon_

@[simp]
theorem id_hom (A : CommMon_ C) : Mon_.Hom.hom (𝟙 A) = 𝟙 A.X :=
  rfl

@[simp]
theorem comp_hom {R S T : CommMon_ C} (f : R ⟶ S) (g : S ⟶ T) :
    Mon_.Hom.hom (f ≫ g) = f.hom ≫ g.hom :=
  rfl

@[ext]
lemma hom_ext {A B : CommMon_ C} (f g : A ⟶ B) (h : f.hom = g.hom) : f = g :=
  Mon_.Hom.ext h

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/10688): the following two lemmas `id'` and `comp'`
-- have been added to ease automation;
@[simp]
lemma id' (A : CommMon_ C) : (𝟙 A : A.toMon_ ⟶ A.toMon_) = 𝟙 (A.toMon_) := rfl

@[simp]
lemma comp' {A₁ A₂ A₃ : CommMon_ C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    ((f ≫ g : A₁ ⟶ A₃) : A₁.toMon_ ⟶ A₃.toMon_) = @CategoryStruct.comp (Mon_ C) _ _ _ _ f g := rfl

section

variable (C)

/-- The forgetful functor from commutative monoid objects to monoid objects. -/
@[simps! obj_X]
def forget₂Mon_ : CommMon_ C ⥤ Mon_ C :=
  inducedFunctor CommMon_.toMon_

/-- The forgetful functor from commutative monoid objects to monoid objects
is fully faithful. -/
def fullyFaithfulForget₂Mon_ : (forget₂Mon_ C).FullyFaithful :=
  fullyFaithfulInducedFunctor _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

instance : (forget₂Mon_ C).Full := InducedCategory.full _
instance : (forget₂Mon_ C).Faithful := InducedCategory.faithful _

@[simp]
theorem forget₂Mon_obj_one (A : CommMon_ C) : η[((forget₂Mon_ C).obj A).X] = η[A.X] :=
  rfl

@[simp]
theorem forget₂Mon_obj_mul (A : CommMon_ C) : μ[((forget₂Mon_ C).obj A).X] = μ[A.X] :=
  rfl

@[simp]
theorem forget₂Mon_map_hom {A B : CommMon_ C} (f : A ⟶ B) : ((forget₂Mon_ C).map f).hom = f.hom :=
  rfl

@[deprecated (since := "2025-02-07")] alias forget₂_Mon_obj_one := forget₂Mon_obj_one
@[deprecated (since := "2025-02-07")] alias forget₂_Mon_obj_mul := forget₂Mon_obj_mul
@[deprecated (since := "2025-02-07")] alias forget₂_Mon_map_hom := forget₂Mon_map_hom

/-- The forgetful functor from commutative monoid objects to the ambient category. -/
@[simps!]
def forget : CommMon_ C ⥤ C :=
  forget₂Mon_ C ⋙ Mon_.forget C

instance : (forget C).Faithful where

@[simp]
theorem forget₂Mon_comp_forget : forget₂Mon_ C ⋙ Mon_.forget C = forget C := rfl

instance {M N : CommMon_ C} {f : M ⟶ N} [IsIso f] : IsIso f.hom :=
  inferInstanceAs <| IsIso <| (forget C).map f

end

/-- Construct an isomorphism of commutative monoid objects by giving a monoid isomorphism between
the underlying objects. -/
@[simps!]
def mkIso' {M N : C} (e : M ≅ N) [MonObj M] [IsCommMon M] [MonObj N] [IsCommMon N]
    [IsMon_Hom e.hom] : mk M ≅ mk N :=
  (fullyFaithfulForget₂Mon_ C).preimageIso (Mon_.mkIso' e)

/-- Construct an isomorphism of commutative monoid objects by giving an isomorphism between the
underlying objects and checking compatibility with unit and multiplication only in the forward
direction. -/
@[simps!]
abbrev mkIso {M N : CommMon_ C} (e : M.X ≅ N.X) (one_f : η[M.X] ≫ e.hom = η[N.X] := by cat_disch)
    (mul_f : μ[M.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[N.X] := by cat_disch) : M ≅ N :=
  have : IsMon_Hom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

instance uniqueHomFromTrivial (A : CommMon_ C) : Unique (trivial C ⟶ A) :=
  Mon_.uniqueHomFromTrivial A.toMon_

open CategoryTheory.Limits

instance : HasInitial (CommMon_ C) :=
  hasInitial_of_unique (trivial C)

end CommMon_

namespace CategoryTheory
variable
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
  {F F' : C ⥤ D} {G : D ⥤ E}

namespace Functor
section LaxBraided
variable [F.LaxBraided] [F'.LaxBraided] [G.LaxBraided]

open scoped Obj

instance isCommMon_obj {M : C} [MonObj M] [IsCommMon M] : IsCommMon (F.obj M) where
  mul_comm := by
    dsimp; rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsCommMon.mul_comm]

variable (F) in
/-- A lax braided functor takes commutative monoid objects to commutative monoid objects.

That is, a lax braided functor `F : C ⥤ D` induces a functor `CommMon_ C ⥤ CommMon_ D`.
-/
@[simps!]
def mapCommMon : CommMon_ C ⥤ CommMon_ D where
  obj A :=
    { F.mapMon.obj A.toMon_ with
      comm :=
        { mul_comm := by
            dsimp
            rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsCommMon.mul_comm] } }
  map f := F.mapMon.map f

@[simp]
theorem mapCommMon_id_one (A : CommMon_ C) :
    η[((𝟭 C).mapCommMon.obj A).X] = 𝟙 _ ≫ η[A.X] :=
  rfl

@[simp]
theorem mapCommMon_id_mul (A : CommMon_ C) :
    μ[((𝟭 C).mapCommMon.obj A).X] = 𝟙 _ ≫ μ[A.X] :=
  rfl

@[simp]
theorem comp_mapCommMon_one (A : CommMon_ C) :
    η[((F ⋙ G).mapCommMon.obj A).X] = LaxMonoidal.ε (F ⋙ G) ≫ (F ⋙ G).map η[A.X] :=
  rfl

@[simp]
theorem comp_mapCommMon_mul (A : CommMon_ C) :
    μ[((F ⋙ G).mapCommMon.obj A).X] = LaxMonoidal.μ (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[A.X] :=
  rfl

/-- The identity functor is also the identity on commutative monoid objects. -/
@[simps!]
def mapCommMonIdIso : mapCommMon (𝟭 C) ≅ 𝟭 (CommMon_ C) :=
  NatIso.ofComponents fun X ↦ CommMon_.mkIso (.refl _)

/-- The composition functor is also the composition on commutative monoid objects. -/
@[simps!]
def mapCommMonCompIso : (F ⋙ G).mapCommMon ≅ F.mapCommMon ⋙ G.mapCommMon :=
  NatIso.ofComponents fun X ↦ CommMon_.mkIso (.refl _)

variable (C D) in
/-- `mapCommMon` is functorial in the lax braided functor. -/
@[simps]
def mapCommMonFunctor : LaxBraidedFunctor C D ⥤ CommMon_ C ⥤ CommMon_ D where
  obj F := F.mapCommMon
  map α := { app A := .mk' (α.hom.app A.X) }
  map_comp _ _ := rfl

protected instance Faithful.mapCommMon [F.Faithful] : F.mapCommMon.Faithful where
  map_injective hfg := F.mapMon.map_injective hfg

/-- Natural transformations between functors lift to monoid objects. -/
@[simps!]
def mapCommMonNatTrans (f : F ⟶ F') [NatTrans.IsMonoidal f] : F.mapCommMon ⟶ F'.mapCommMon where
  app X := .mk' (f.app _)

/-- Natural isomorphisms between functors lift to monoid objects. -/
@[simps!]
def mapCommMonNatIso (e : F ≅ F') [NatTrans.IsMonoidal e.hom] : F.mapCommMon ≅ F'.mapCommMon :=
  NatIso.ofComponents fun X ↦ CommMon_.mkIso (e.app _)

end LaxBraided

section Braided
variable [F.Braided]

protected instance Full.mapCommMon [F.Full] [F.Faithful] : F.mapCommMon.Full where
  map_surjective := F.mapMon.map_surjective

/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then `Grp(F) : Grp C ⥤ Grp D` is fully
faithful too. -/
@[simps]
protected def FullyFaithful.mapCommMon (hF : F.FullyFaithful) : F.mapCommMon.FullyFaithful where
  preimage f := .mk <| hF.preimage f.hom

end Braided

end Functor

open Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Braided] [G.LaxBraided] [a.IsMonoidal]

/-- An adjunction of braided functors lifts to an adjunction of their lifts to commutative monoid
objects. -/
@[simps] def mapCommMon : F.mapCommMon ⊣ G.mapCommMon where
  unit := mapCommMonIdIso.inv ≫ mapCommMonNatTrans a.unit ≫ mapCommMonCompIso.hom
  counit := mapCommMonCompIso.inv ≫ mapCommMonNatTrans a.counit ≫ mapCommMonIdIso.hom

end Adjunction

namespace Equivalence

/-- An equivalence of categories lifts to an equivalence of their commutative monoid objects. -/
@[simps]
def mapCommMon (e : C ≌ D) [e.functor.Braided] [e.inverse.Braided] [e.IsMonoidal] :
    CommMon_ C ≌ CommMon_ D where
  functor := e.functor.mapCommMon
  inverse := e.inverse.mapCommMon
  unitIso := mapCommMonIdIso.symm ≪≫ mapCommMonNatIso e.unitIso ≪≫ mapCommMonCompIso
  counitIso := mapCommMonCompIso.symm ≪≫ mapCommMonNatIso e.counitIso ≪≫ mapCommMonIdIso

end CategoryTheory.Equivalence

namespace CommMon_

open CategoryTheory.LaxBraidedFunctor

namespace EquivLaxBraidedFunctorPUnit

variable (C) in
/-- Implementation of `CommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps]
def laxBraidedToCommMon : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ⥤ CommMon_ C where
  obj F := (F.mapCommMon : CommMon_ _ ⥤ CommMon_ C).obj (trivial (Discrete PUnit.{u+1}))
  map α := ((Functor.mapCommMonFunctor (Discrete PUnit) C).map α).app _

/-- Implementation of `CommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
def commMonToLaxBraidedObj (A : CommMon_ C) :
    Discrete PUnit.{u + 1} ⥤ C := (Functor.const _).obj A.X

instance (A : CommMon_ C) : (commMonToLaxBraidedObj A).LaxMonoidal where
  ε := η[A.X]
  «μ» _ _ := μ[A.X]

open Functor.LaxMonoidal

@[simp]
lemma commMonToLaxBraidedObj_ε (A : CommMon_ C) :
    ε (commMonToLaxBraidedObj A) = η[A.X] := rfl

@[simp]
lemma commMonToLaxBraidedObj_μ (A : CommMon_ C) (X Y) :
    «μ» (commMonToLaxBraidedObj A) X Y = μ[A.X] := rfl

instance (A : CommMon_ C) : (commMonToLaxBraidedObj A).LaxBraided where

variable (C)
/-- Implementation of `CommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps]
def commMonToLaxBraided : CommMon_ C ⥤ LaxBraidedFunctor (Discrete PUnit.{u + 1}) C where
  obj A := LaxBraidedFunctor.of (commMonToLaxBraidedObj A)
  map f :=
    { hom := { app := fun _ => f.hom }
      isMonoidal := { } }

/-- Implementation of `CommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
def unitIso :
    𝟭 (LaxBraidedFunctor (Discrete PUnit.{u + 1}) C) ≅
        laxBraidedToCommMon C ⋙ commMonToLaxBraided C :=
  NatIso.ofComponents
    (fun F ↦ LaxBraidedFunctor.isoOfComponents (fun _ ↦ F.mapIso (eqToIso (by ext))))
    (fun f ↦ by ext ⟨⟨⟩⟩; dsimp; simp)

@[simp]
theorem counitIso_aux_one (A : CommMon_ C) :
    η[((commMonToLaxBraided C ⋙ laxBraidedToCommMon C).obj A).X] = η[A.X] ≫ 𝟙 _ :=
  rfl

@[simp]
theorem counitIso_aux_mul (A : CommMon_ C) :
    μ[((commMonToLaxBraided C ⋙ laxBraidedToCommMon C).obj A).X] = μ[A.X] ≫ 𝟙 _ :=
  rfl

/-- Implementation of `CommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
def counitIso : commMonToLaxBraided C ⋙ laxBraidedToCommMon C ≅ 𝟭 (CommMon_ C) :=
  NatIso.ofComponents (fun F ↦ mkIso (Iso.refl _))

end EquivLaxBraidedFunctorPUnit

open EquivLaxBraidedFunctorPUnit

/-- Commutative monoid objects in `C` are "just" braided lax monoidal functors from the trivial
braided monoidal category to `C`.
-/
@[simps]
def equivLaxBraidedFunctorPUnit : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ≌ CommMon_ C where
  functor := laxBraidedToCommMon C
  inverse := commMonToLaxBraided C
  unitIso := unitIso C
  counitIso := counitIso C

end CommMon_
