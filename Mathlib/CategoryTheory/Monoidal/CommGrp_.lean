/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.CategoryTheory.Monoidal.CommMon_

/-!
# The category of commutative groups in a Cartesian monoidal category
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory Mon Grp CommMon
open MonObj

variable (C : Type u₁) [Category.{v₁} C] [CartesianMonoidalCategory.{v₁} C] [BraidedCategory C]

/-- A commutative group object internal to a Cartesian monoidal category. -/
structure CommGrp where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [grp : GrpObj X]
  [comm : IsCommMonObj X]

@[deprecated (since := "2025-10-13")] alias CommGrp_ := CommGrp

attribute [instance] CommGrp.grp CommGrp.comm

namespace CommGrp

variable {C}

/-- A commutative group object is a group object. -/
@[simps X]
def toGrp (A : CommGrp C) : Grp C := ⟨A.X⟩

@[deprecated (since := "2025-10-13")] alias toGrp_ := toGrp

/-- A commutative group object is a commutative monoid object. -/
@[simps X]
def toCommMon (A : CommGrp C) : CommMon C := ⟨A.X⟩

@[deprecated (since := "2025-09-15")] alias toCommMon_ := toCommMon

/-- A commutative group object is a monoid object. -/
abbrev toMon (A : CommGrp C) : Mon C := (toCommMon A).toMon

@[deprecated (since := "2025-09-15")] alias toMon_ := toMon

variable (C) in
/-- The trivial commutative group object. -/
@[simps!]
def trivial : CommGrp C := { X := 𝟙_ C }

instance : Inhabited (CommGrp C) where
  default := trivial C

instance : Category (CommGrp C) :=
  inferInstanceAs (Category (InducedCategory _ CommGrp.toGrp))

@[simp]
theorem id_hom (A : CommGrp C) : (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.toGrp :=
  rfl

@[simp]
theorem comp_hom {R S T : CommGrp C} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[ext]
theorem hom_ext {A B : CommGrp C} (f g : A ⟶ B) (h : f.hom.hom.hom = g.hom.hom.hom) : f = g :=
  InducedCategory.hom_ext (Grp.hom_ext _ _ h)

@[deprecated (since := "2025-07-03")] alias id' := id_hom
@[deprecated (since := "2025-07-03")] alias comp' := comp_hom

section

variable (C)

/-- The forgetful functor from commutative group objects to group objects. -/
@[simps! obj_X]
def forget₂Grp : CommGrp C ⥤ Grp C :=
  inducedFunctor CommGrp.toGrp

@[deprecated (since := "2025-10-13")] alias forget₂Grp_ := forget₂Grp

/-- The forgetful functor from commutative group objects to group objects is fully faithful. -/
def fullyFaithfulForget₂Grp : (forget₂Grp C).FullyFaithful :=
  fullyFaithfulInducedFunctor _

@[deprecated (since := "2025-10-13")] alias fullyFaithfulForget₂Grp_ := fullyFaithfulForget₂Grp

instance : (forget₂Grp C).Full := InducedCategory.full _
instance : (forget₂Grp C).Faithful := InducedCategory.faithful _

@[simp]
theorem forget₂Grp_obj_one (A : CommGrp C) : η[((forget₂Grp C).obj A).X] = η[A.X] :=
  rfl

@[simp]
theorem forget₂Grp_obj_mul (A : CommGrp C) : μ[((forget₂Grp C).obj A).X] = μ[A.X] :=
  rfl

@[simp]
theorem forget₂Grp_map_hom {A B : CommGrp C} (f : A ⟶ B) :
    ((forget₂Grp C).map f).hom = f.hom.hom :=
  rfl

/-- The forgetful functor from commutative group objects to commutative monoid objects. -/
def forget₂CommMon : CommGrp C ⥤ CommMon C where
  obj G := CommMon.mk G.X
  map f := CommMon.homMk f.hom.hom

@[deprecated (since := "2025-09-15")] alias forget₂CommMon_ := forget₂CommMon

/-- The forgetful functor from commutative group objects to commutative monoid objects is fully
faithful. -/
def fullyFaithfulForget₂CommMon : (forget₂CommMon C).FullyFaithful where
  preimage f := InducedCategory.homMk (Grp.homMk' f.hom)

instance : (forget₂CommMon C).Full := (fullyFaithfulForget₂CommMon _).full
instance : (forget₂CommMon C).Faithful := (fullyFaithfulForget₂CommMon _).faithful

@[simp]
theorem forget₂CommMon_obj_one (A : CommGrp C) : η[((forget₂CommMon C).obj A).X] = η[A.X] :=
  rfl

@[simp]
theorem forget₂CommMon_obj_mul (A : CommGrp C) : μ[((forget₂CommMon C).obj A).X] = μ[A.X] :=
  rfl

@[simp]
theorem forget₂CommMon_map_hom {A B : CommGrp C} (f : A ⟶ B) :
    ((forget₂CommMon C).map f).hom = f.hom.hom :=
  rfl

/-- The forgetful functor from commutative group objects to the ambient category. -/
@[simps!]
def forget : CommGrp C ⥤ C :=
  forget₂Grp C ⋙ Grp.forget C

instance : (forget C).Faithful where

@[simp]
theorem forget₂Grp_comp_forget : forget₂Grp C ⋙ Grp.forget C = forget C := rfl

@[simp]
theorem forget₂CommMon_comp_forget : forget₂CommMon C ⋙ CommMon.forget C = forget C := rfl

instance {G H : CommGrp C} {f : G ⟶ H} [IsIso f] : IsIso f.hom :=
  inferInstanceAs (IsIso ((forget₂Grp C).map f))

instance {G H : CommGrp C} {f : G ⟶ H} [IsIso f] : IsIso f.hom.hom :=
  inferInstanceAs (IsIso ((forget₂Grp C ⋙ Grp.forget₂Mon C).map f))

end

/-- Construct an isomorphism of commutative group objects by giving a monoid isomorphism between the
underlying objects. -/
@[simps!]
def mkIso' {G H : C} (e : G ≅ H) [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
    [IsMonHom e.hom] : mk G ≅ mk H :=
  (fullyFaithfulForget₂Grp C).preimageIso (Grp.mkIso' e)

section

variable {G H : CommGrp C} (e : G.X ≅ H.X) (one_f : η[G.X] ≫ e.hom = η[H.X] := by cat_disch)
  (mul_f : μ[G.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[H.X] := by cat_disch)

/-- Construct an isomorphism of group objects by giving an isomorphism between the underlying
objects and checking compatibility with unit and multiplication only in the forward direction. -/
abbrev mkIso : G ≅ H :=
  have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

@[simp] lemma mkIso_hom_hom_hom_hom : (mkIso e one_f mul_f).hom.hom.hom.hom = e.hom := rfl
@[simp] lemma mkIso_inv_hom_hom_hom : (mkIso e one_f mul_f).inv.hom.hom.hom = e.inv := rfl

@[deprecated (since := "2025-07-03")] alias mkIso_hom_hom := mkIso_hom_hom_hom_hom
@[deprecated (since := "2025-07-03")] alias mkIso_inv_hom := mkIso_inv_hom_hom_hom

end

instance uniqueHomFromTrivial (A : CommGrp C) : Unique (trivial C ⟶ A) :=
  Equiv.unique (show _ ≃ (Grp.trivial C ⟶ A.toGrp) from
    InducedCategory.homEquiv)

instance : HasInitial (CommGrp C) :=
  hasInitial_of_unique (trivial C)

end CommGrp

namespace CategoryTheory
variable {C}
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  {E : Type u₃} [Category.{v₃} E] [CartesianMonoidalCategory E] [BraidedCategory E]

namespace Functor
variable {F F' : C ⥤ D} [F.Braided] [F'.Braided] {G : D ⥤ E} [G.Braided]

open Monoidal

variable (F) in
/-- A finite-product-preserving functor takes commutative group objects to commutative group
objects. -/
@[simps!]
def mapCommGrp : CommGrp C ⥤ CommGrp D where
  obj A :=
    { F.mapGrp.obj A.toGrp with
      comm :=
        { mul_comm := by
            dsimp
            rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsCommMonObj.mul_comm] } }
  map f := InducedCategory.homMk (F.mapGrp.map f.hom)

protected instance Faithful.mapCommGrp [F.Faithful] : F.mapCommGrp.Faithful where
  map_injective hfg :=
    (CommGrp.forget _ ⋙ F).map_injective ((CommGrp.forget _).congr_map hfg)

/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then
`CommGrpCat(F) : CommGrpCat C ⥤ CommGrpCat D` is fully faithful too. -/
@[simps]
protected def FullyFaithful.mapCommGrp (hF : F.FullyFaithful) : F.mapCommGrp.FullyFaithful where
  preimage f := InducedCategory.homMk (Grp.homMk' (hF.mapMon.preimage f.hom.hom))

protected instance Full.mapCommGrp [F.Full] [F.Faithful] : F.mapCommGrp.Full :=
  (FullyFaithful.ofFullyFaithful F).mapCommGrp.full

@[simp]
theorem mapCommGrp_id_one (A : CommGrp C) :
    η[((𝟭 C).mapCommGrp.obj A).X] = 𝟙 _ ≫ η[A.X] :=
  rfl

@[simp]
theorem mapCommpGrp_id_mul (A : CommGrp C) :
    μ[((𝟭 C).mapCommGrp.obj A).X] = 𝟙 _ ≫ μ[A.X] :=
  rfl

@[simp]
theorem comp_mapCommGrp_one (A : CommGrp C) :
    η[((F ⋙ G).mapCommGrp.obj A).X] = LaxMonoidal.ε (F ⋙ G) ≫ (F ⋙ G).map η[A.X] :=
  rfl

@[simp]
theorem comp_mapCommGrp_mul (A : CommGrp C) :
    μ[((F ⋙ G).mapCommGrp.obj A).X] = LaxMonoidal.μ (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[A.X] :=
  rfl

/-- The identity functor is also the identity on commutative group objects. -/
@[simps!]
def mapCommGrpIdIso : mapCommGrp (𝟭 C) ≅ 𝟭 (CommGrp C) :=
  NatIso.ofComponents (fun X ↦ CommGrp.mkIso (.refl _) (by simp)
    (by simp))

/-- The composition functor is also the composition on commutative group objects. -/
@[simps!]
def mapCommGrpCompIso : (F ⋙ G).mapCommGrp ≅ F.mapCommGrp ⋙ G.mapCommGrp :=
  NatIso.ofComponents fun X ↦ CommGrp.mkIso (.refl _)

/-- Natural transformations between functors lift to commutative group objects. -/
@[simps!]
def mapCommGrpNatTrans (f : F ⟶ F') : F.mapCommGrp ⟶ F'.mapCommGrp where
  app X := InducedCategory.homMk ((mapGrpNatTrans f).app X.toGrp)

/-- Natural isomorphisms between functors lift to commutative group objects. -/
@[simps!]
def mapCommGrpNatIso (e : F ≅ F') : F.mapCommGrp ≅ F'.mapCommGrp :=
  NatIso.ofComponents fun X ↦ CommGrp.mkIso (e.app _)

attribute [local instance] Functor.Braided.ofChosenFiniteProducts in
/-- `mapCommGrp` is functorial in the left-exact functor. -/
@[simps]
noncomputable def mapCommGrpFunctor : (C ⥤ₗ D) ⥤ CommGrp C ⥤ CommGrp D where
  obj F := F.1.mapCommGrp
  map α := mapCommGrpNatTrans α.hom

end Functor

open Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Braided] [G.Braided]

/-- An adjunction of braided functors lifts to an adjunction of their lifts to commutative group
objects. -/
@[simps] noncomputable def mapCommGrp : F.mapCommGrp ⊣ G.mapCommGrp where
  unit := mapCommGrpIdIso.inv ≫ mapCommGrpNatTrans a.unit ≫ mapCommGrpCompIso.hom
  counit := mapCommGrpCompIso.inv ≫ mapCommGrpNatTrans a.counit ≫ mapCommGrpIdIso.hom

end Adjunction

namespace Equivalence
variable (e : C ≌ D) [e.functor.Braided] [e.inverse.Braided]

/-- An equivalence of categories lifts to an equivalence of their commutative group objects. -/
@[simps] noncomputable def mapCommGrp : CommGrp C ≌ CommGrp D where
  functor := e.functor.mapCommGrp
  inverse := e.inverse.mapCommGrp
  unitIso := mapCommGrpIdIso.symm ≪≫ mapCommGrpNatIso e.unitIso ≪≫ mapCommGrpCompIso
  counitIso := mapCommGrpCompIso.symm ≪≫ mapCommGrpNatIso e.counitIso ≪≫ mapCommGrpIdIso

end CategoryTheory.Equivalence
