/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# The category of commutative monoids in a braided monoidal category.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

variable (C) in
/-- A commutative monoid object internal to a monoidal category.
-/
structure CommMon where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [mon : MonObj X]
  [comm : IsCommMonObj X]

attribute [instance] CommMon.mon CommMon.comm

namespace CommMon

/-- A commutative monoid object is a monoid object. -/
@[simps X]
def toMon (A : CommMon C) : Mon C := ⟨A.X⟩

variable (C) in
/-- The trivial commutative monoid object. We later show this is initial in `CommMon C`.
-/
@[simps!]
def trivial : CommMon C := { X := 𝟙_ C }

instance : Inhabited (CommMon C) :=
  ⟨trivial C⟩

variable {M : CommMon C}

instance : Category (CommMon C) :=
  inferInstanceAs (Category (InducedCategory _ CommMon.toMon))

@[simp]
theorem id_hom (A : CommMon C) : Mon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.X :=
  rfl

@[simp]
theorem comp_hom {R S T : CommMon C} (f : R ⟶ S) (g : S ⟶ T) :
    Mon.Hom.hom (f ≫ g).hom = f.hom.hom ≫ g.hom.hom :=
  rfl

@[ext]
lemma hom_ext {A B : CommMon C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom) : f = g :=
  InducedCategory.hom_ext (Mon.Hom.ext h)

/-- Constructor for morphisms in `CommMon C`. -/
@[simps]
def homMk {A B : CommMon C} (f : A.toMon ⟶ B.toMon) : A ⟶ B where
  hom := f

section

variable (C)

/-- The forgetful functor from commutative monoid objects to monoid objects. -/
@[simps! obj_X]
def forget₂Mon : CommMon C ⥤ Mon C :=
  inducedFunctor CommMon.toMon

/-- The forgetful functor from commutative monoid objects to monoid objects
is fully faithful. -/
def fullyFaithfulForget₂Mon : (forget₂Mon C).FullyFaithful :=
  fullyFaithfulInducedFunctor _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

instance : (forget₂Mon C).Full := InducedCategory.full _
instance : (forget₂Mon C).Faithful := InducedCategory.faithful _

@[simp]
theorem forget₂Mon_obj_one (A : CommMon C) : η[((forget₂Mon C).obj A).X] = η[A.X] :=
  rfl

@[simp]
theorem forget₂Mon_obj_mul (A : CommMon C) : μ[((forget₂Mon C).obj A).X] = μ[A.X] :=
  rfl

@[simp]
theorem forget₂Mon_map_hom {A B : CommMon C} (f : A ⟶ B) :
    ((forget₂Mon C).map f).hom = f.hom.hom :=
  rfl

/-- The forgetful functor from commutative monoid objects to the ambient category. -/
@[simps!]
def forget : CommMon C ⥤ C :=
  forget₂Mon C ⋙ Mon.forget C

instance : (forget C).Faithful where

@[simp]
theorem forget₂Mon_comp_forget : forget₂Mon C ⋙ Mon.forget C = forget C := rfl

instance {M N : CommMon C} {f : M ⟶ N} [IsIso f] : IsIso f.hom.hom :=
  inferInstanceAs <| IsIso <| (forget C).map f

end

/-- Construct an isomorphism of commutative monoid objects by giving a monoid isomorphism between
the underlying objects. -/
@[simps!]
def mkIso' {M N : C} (e : M ≅ N) [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N]
    [IsMonHom e.hom] : mk M ≅ mk N :=
  (fullyFaithfulForget₂Mon C).preimageIso (Mon.mkIso' e)

/-- Construct an isomorphism of commutative monoid objects by giving an isomorphism between the
underlying objects and checking compatibility with unit and multiplication only in the forward
direction. -/
@[simps!]
abbrev mkIso {M N : CommMon C} (e : M.X ≅ N.X) (one_f : η[M.X] ≫ e.hom = η[N.X] := by cat_disch)
    (mul_f : μ[M.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[N.X] := by cat_disch) : M ≅ N :=
  have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

instance uniqueHomFromTrivial (A : CommMon C) : Unique (trivial C ⟶ A) :=
  Equiv.unique (show _ ≃ (Mon.trivial C ⟶ A.toMon) from
    InducedCategory.homEquiv)

open CategoryTheory.Limits

instance : HasInitial (CommMon C) :=
  hasInitial_of_unique (trivial C)

end CommMon

variable
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
  {F F' : C ⥤ D} {G : D ⥤ E}

namespace Functor
section LaxBraided
variable [F.LaxBraided] [F'.LaxBraided] [G.LaxBraided]

open scoped Obj

instance isCommMonObj_obj {M : C} [MonObj M] [IsCommMonObj M] : IsCommMonObj (F.obj M) where
  mul_comm := by
    dsimp; rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsCommMonObj.mul_comm]

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- A lax braided functor takes commutative monoid objects to commutative monoid objects.

That is, a lax braided functor `F : C ⥤ D` induces a functor `CommMon C ⥤ CommMon D`.
-/
@[simps!]
def mapCommMon : CommMon C ⥤ CommMon D where
  obj A :=
    { F.mapMon.obj A.toMon with
      comm :=
        { mul_comm := by
            dsimp
            rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsCommMonObj.mul_comm] } }
  map f := CommMon.homMk (F.mapMon.map f.hom)

@[simp]
theorem mapCommMon_id_one (A : CommMon C) :
    η[((𝟭 C).mapCommMon.obj A).X] = 𝟙 _ ≫ η[A.X] :=
  rfl

@[simp]
theorem mapCommMon_id_mul (A : CommMon C) :
    μ[((𝟭 C).mapCommMon.obj A).X] = 𝟙 _ ≫ μ[A.X] :=
  rfl

@[simp]
theorem comp_mapCommMon_one (A : CommMon C) :
    η[((F ⋙ G).mapCommMon.obj A).X] = LaxMonoidal.ε (F ⋙ G) ≫ (F ⋙ G).map η[A.X] :=
  rfl

@[simp]
theorem comp_mapCommMon_mul (A : CommMon C) :
    μ[((F ⋙ G).mapCommMon.obj A).X] = LaxMonoidal.μ (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[A.X] :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identity functor is also the identity on commutative monoid objects. -/
@[simps!]
def mapCommMonIdIso : mapCommMon (𝟭 C) ≅ 𝟭 (CommMon C) :=
  NatIso.ofComponents fun X ↦ CommMon.mkIso (.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- The composition functor is also the composition on commutative monoid objects. -/
@[simps!]
def mapCommMonCompIso : (F ⋙ G).mapCommMon ≅ F.mapCommMon ⋙ G.mapCommMon :=
  NatIso.ofComponents fun X ↦ CommMon.mkIso (.refl _)

set_option backward.isDefEq.respectTransparency false in
variable (C D) in
/-- `mapCommMon` is functorial in the lax braided functor. -/
@[simps]
def mapCommMonFunctor : LaxBraidedFunctor C D ⥤ CommMon C ⥤ CommMon D where
  obj F := F.mapCommMon
  map α := { app A := CommMon.homMk (.mk' (α.hom.hom.app A.X)) }

protected instance Faithful.mapCommMon [F.Faithful] : F.mapCommMon.Faithful where
  map_injective hfg :=
    (CommMon.forget₂Mon _ ⋙ F.mapMon).map_injective ((CommMon.forget₂Mon _).congr_map hfg)

set_option backward.isDefEq.respectTransparency false in
/-- Natural transformations between functors lift to monoid objects. -/
@[simps!]
def mapCommMonNatTrans (f : F ⟶ F') [NatTrans.IsMonoidal f] :
    F.mapCommMon ⟶ F'.mapCommMon where
  app X := CommMon.homMk (.mk' (f.app _))

set_option backward.isDefEq.respectTransparency false in
/-- Natural isomorphisms between functors lift to monoid objects. -/
@[simps!]
def mapCommMonNatIso (e : F ≅ F') [NatTrans.IsMonoidal e.hom] : F.mapCommMon ≅ F'.mapCommMon :=
  NatIso.ofComponents fun X ↦ CommMon.mkIso (e.app _)

end LaxBraided

section Braided
variable [F.Braided]

/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then
`CommMonCat(F) : CommMonCat C ⥤ CommMonCat D` is fully faithful too. -/
@[simps]
protected def FullyFaithful.mapCommMon (hF : F.FullyFaithful) : F.mapCommMon.FullyFaithful where
  preimage f := CommMon.homMk (hF.mapMon.preimage f.hom)

protected instance Full.mapCommMon [F.Full] [F.Faithful] : F.mapCommMon.Full :=
    (FullyFaithful.ofFullyFaithful F).mapCommMon.full

end Braided

end Functor

open Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Braided] [G.LaxBraided] [a.IsMonoidal]

set_option backward.isDefEq.respectTransparency false in
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
    CommMon C ≌ CommMon D where
  functor := e.functor.mapCommMon
  inverse := e.inverse.mapCommMon
  unitIso := mapCommMonIdIso.symm ≪≫ mapCommMonNatIso e.unitIso ≪≫ mapCommMonCompIso
  counitIso := mapCommMonCompIso.symm ≪≫ mapCommMonNatIso e.counitIso ≪≫ mapCommMonIdIso

end Equivalence

namespace CommMon

open LaxBraidedFunctor

namespace EquivLaxBraidedFunctorPUnit

variable (C) in
/-- Implementation of `CommMon.equivLaxBraidedFunctorPUnit`. -/
@[simps]
def laxBraidedToCommMon : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ⥤ CommMon C where
  obj F := (F.mapCommMon : CommMon _ ⥤ CommMon C).obj (trivial (Discrete PUnit.{u + 1}))
  map α := ((Functor.mapCommMonFunctor (Discrete PUnit) C).map α).app _

/-- Implementation of `CommMon.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
def commMonToLaxBraidedObj (A : CommMon C) :
    Discrete PUnit.{u + 1} ⥤ C := (Functor.const _).obj A.X

instance (A : CommMon C) : (commMonToLaxBraidedObj A).LaxMonoidal where
  ε := η[A.X]
  «μ» _ _ := μ[A.X]

open Functor.LaxMonoidal

@[simp]
lemma commMonToLaxBraidedObj_ε (A : CommMon C) :
    ε (commMonToLaxBraidedObj A) = η[A.X] := rfl

@[simp]
lemma commMonToLaxBraidedObj_μ (A : CommMon C) (X Y) :
    «μ» (commMonToLaxBraidedObj A) X Y = μ[A.X] := rfl

instance (A : CommMon C) : (commMonToLaxBraidedObj A).LaxBraided where

variable (C)

set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `CommMon.equivLaxBraidedFunctorPUnit`. -/
@[simps]
def commMonToLaxBraided : CommMon C ⥤ LaxBraidedFunctor (Discrete PUnit.{u + 1}) C where
  obj A := LaxBraidedFunctor.of (commMonToLaxBraidedObj A)
  map f :=
    { hom :=
      { hom := { app _ := f.hom.hom }
        isMonoidal := { } } }

set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `CommMon.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
def unitIso :
    𝟭 (LaxBraidedFunctor (Discrete PUnit.{u + 1}) C) ≅
        laxBraidedToCommMon C ⋙ commMonToLaxBraided C :=
  NatIso.ofComponents
    (fun F ↦ LaxBraidedFunctor.isoOfComponents (fun _ ↦ F.mapIso (eqToIso (by ext))))
    (fun f ↦ by ext ⟨⟨⟩⟩; dsimp; simp)

@[simp]
theorem counitIso_aux_one (A : CommMon C) :
    η[((commMonToLaxBraided C ⋙ laxBraidedToCommMon C).obj A).X] = η[A.X] ≫ 𝟙 _ :=
  rfl

@[simp]
theorem counitIso_aux_mul (A : CommMon C) :
    μ[((commMonToLaxBraided C ⋙ laxBraidedToCommMon C).obj A).X] = μ[A.X] ≫ 𝟙 _ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `CommMon.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
def counitIso : commMonToLaxBraided C ⋙ laxBraidedToCommMon C ≅ 𝟭 (CommMon C) :=
  NatIso.ofComponents (fun F ↦ mkIso (Iso.refl _))

end EquivLaxBraidedFunctorPUnit

open EquivLaxBraidedFunctorPUnit

/-- Commutative monoid objects in `C` are "just" braided lax monoidal functors from the trivial
braided monoidal category to `C`.
-/
@[simps]
def equivLaxBraidedFunctorPUnit : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ≌ CommMon C where
  functor := laxBraidedToCommMon C
  inverse := commMonToLaxBraided C
  unitIso := unitIso C
  counitIso := counitIso C

end CommMon
end CategoryTheory
