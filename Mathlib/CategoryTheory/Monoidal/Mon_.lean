/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Group.PUnit
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The category of monoids in a monoidal category.

We define monoids in a monoidal category `C` and show that the category of monoids is equivalent to
the category of lax monoidal functors from the unit monoidal category to `C`.  We also show that if
`C` is braided, then the category of monoids is naturally monoidal.

-/

universe v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
class Mon_Class (X : C) where
  /-- The unit morphism of a monoid object. -/
  one : 𝟙_ C ⟶ X
  /-- The multiplication morphism of a monoid object. -/
  mul : X ⊗ X ⟶ X
  /- For the names of the conditions below, the unprimed names are reserved for the version where
  the argument `X` is explicit. -/
  one_mul' : one ▷ X ≫ mul = (λ_ X).hom := by aesop_cat
  mul_one' : X ◁ one ≫ mul = (ρ_ X).hom := by aesop_cat
  -- Obviously there is some flexibility stating this axiom.
  -- This one has left- and right-hand sides matching the statement of `Monoid.mul_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  mul_assoc' : (mul ▷ X) ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul := by aesop_cat

namespace Mon_Class

@[inherit_doc] scoped notation "μ" => Mon_Class.mul
@[inherit_doc] scoped notation "μ["M"]" => Mon_Class.mul (X := M)
@[inherit_doc] scoped notation "η" => Mon_Class.one
@[inherit_doc] scoped notation "η["M"]" => Mon_Class.one (X := M)

/- The simp attribute is reserved for the unprimed versions. -/
attribute [reassoc] one_mul' mul_one' mul_assoc'

@[reassoc (attr := simp)]
theorem one_mul (X : C) [Mon_Class X] : η ▷ X ≫ μ = (λ_ X).hom := one_mul'

@[reassoc (attr := simp)]
theorem mul_one (X : C) [Mon_Class X] : X ◁ η ≫ μ = (ρ_ X).hom := mul_one'

@[reassoc (attr := simp)]
theorem mul_assoc (X : C) [Mon_Class X] : μ ▷ X ≫ μ = (α_ X X X).hom ≫ X ◁ μ ≫ μ := mul_assoc'

@[simps]
instance (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] : Mon_Class (𝟙_ C) where
  one := 𝟙 _
  mul := (λ_ _).hom
  mul_assoc' := by monoidal_coherence
  mul_one' := by monoidal_coherence

@[ext]
theorem ext {X : C} (h₁ h₂ : Mon_Class X) (H : h₁.mul = h₂.mul) : h₁ = h₂ := by
  suffices h₁.one = h₂.one by cases h₁; cases h₂; subst H this; rfl
  trans (λ_ _).inv ≫ (h₁.one ⊗ h₂.one) ≫ h₁.mul
  · simp [tensorHom_def, H, ← unitors_equal]
  · simp [tensorHom_def']

end Mon_Class

open scoped Mon_Class

variable {M N : C} [Mon_Class M] [Mon_Class N]

/-- The property that a morphism between monoid objects is a monoid morphism. -/
class IsMon_Hom (f : M ⟶ N) : Prop where
  one_hom (f) : η ≫ f = η := by aesop_cat
  mul_hom (f) : μ ≫ f = (f ⊗ f) ≫ μ := by aesop_cat

attribute [reassoc (attr := simp)] IsMon_Hom.one_hom IsMon_Hom.mul_hom

instance {M N : C} [Mon_Class M] [Mon_Class N] (f : M ≅ N) [IsMon_Hom f.hom] :
   IsMon_Hom f.inv where
  one_hom := by simp [Iso.comp_inv_eq]
  mul_hom := by simp [Iso.comp_inv_eq]

variable (C) in
/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
structure Mon_ where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  /-- The unit morphism of the monoid object -/
  one : 𝟙_ C ⟶ X
  /-- The multiplication morphism of a monoid object -/
  mul : X ⊗ X ⟶ X
  one_mul : (one ▷ X) ≫ mul = (λ_ X).hom := by aesop_cat
  mul_one : (X ◁ one) ≫ mul = (ρ_ X).hom := by aesop_cat
  -- Obviously there is some flexibility stating this axiom.
  -- This one has left- and right-hand sides matching the statement of `Monoid.mul_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  mul_assoc : (mul ▷ X) ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul := by aesop_cat

attribute [reassoc] Mon_.one_mul Mon_.mul_one

attribute [simp] Mon_.one_mul Mon_.mul_one

-- We prove a more general `@[simp]` lemma below.
attribute [reassoc (attr := simp)] Mon_.mul_assoc

namespace Mon_

/-- Construct an object of `Mon_ C` from an object `X : C` and `Mon_Class X` instance. -/
@[simps]
def mk' (X : C) [Mon_Class X] : Mon_ C where
  X := X
  one := η
  mul := μ

instance {M : Mon_ C} : Mon_Class M.X where
  one := M.one
  mul := M.mul
  one_mul' := M.one_mul
  mul_one' := M.mul_one
  mul_assoc' := M.mul_assoc

variable (C) in
/-- The trivial monoid object. We later show this is initial in `Mon_ C`.
-/
@[simps!]
def trivial : Mon_ C := mk' (𝟙_ C)

instance : Inhabited (Mon_ C) :=
  ⟨trivial C⟩

variable {M : Mon_ C}

@[simp]
theorem one_mul_hom {Z : C} (f : Z ⟶ M.X) : (M.one ⊗ f) ≫ M.mul = (λ_ Z).hom ≫ f := by
  rw [tensorHom_def'_assoc, M.one_mul, leftUnitor_naturality]

@[simp]
theorem mul_one_hom {Z : C} (f : Z ⟶ M.X) : (f ⊗ M.one) ≫ M.mul = (ρ_ Z).hom ≫ f := by
  rw [tensorHom_def_assoc, M.mul_one, rightUnitor_naturality]

theorem mul_assoc_flip :
    (M.X ◁ M.mul) ≫ M.mul = (α_ M.X M.X M.X).inv ≫ (M.mul ▷ M.X) ≫ M.mul := by simp

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : Mon_ C) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  one_hom : M.one ≫ hom = N.one := by aesop_cat
  mul_hom : M.mul ≫ hom = (hom ⊗ hom) ≫ N.mul := by aesop_cat

/-- Construct a morphism `M ⟶ N` of `Mon_ C` from a map `f : M ⟶ N` and a `IsMon_Hom f` instance. -/
abbrev Hom.mk' {M N : C} [Mon_Class M] [Mon_Class N] (f : M ⟶ N) [IsMon_Hom f] :
    Hom (.mk' M) (.mk' N) := .mk f

attribute [reassoc (attr := simp)] Hom.one_hom Hom.mul_hom

/-- The identity morphism on a monoid object. -/
@[simps]
def id (M : Mon_ C) : Hom M M where
  hom := 𝟙 M.X

instance homInhabited (M : Mon_ C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Mon_ C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

instance : Category (Mon_ C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

instance {M N : Mon_ C} (f : M ⟶ N) : IsMon_Hom f.hom := ⟨f.2, f.3⟩

@[ext]
lemma ext {X Y : Mon_ C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g :=
  Hom.ext w

@[simp]
theorem id_hom' (M : Mon_ C) : (𝟙 M : Hom M M).hom = 𝟙 M.X :=
  rfl

@[simp]
theorem comp_hom' {M N K : Mon_ C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl

section

variable (C)

/-- The forgetful functor from monoid objects to the ambient category. -/
@[simps]
def forget : Mon_ C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : (forget C).Faithful where

instance {A B : Mon_ C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom :=
  e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e := ⟨⟨{ hom := inv f.hom }, by aesop_cat⟩⟩

/-- Construct an isomorphism of monoids by giving an isomorphism between the underlying objects
and checking compatibility with unit and multiplication only in the forward direction.
-/
@[simps]
def mkIso' {M N : Mon_ C} (f : M.X ≅ N.X) [IsMon_Hom f.hom] : M ≅ N where
  hom := Hom.mk' f.hom
  inv := Hom.mk' f.inv

/-- Construct an isomorphism of monoids by giving an isomorphism between the underlying objects
and checking compatibility with unit and multiplication only in the forward direction.
-/
@[simps!]
def mkIso {M N : Mon_ C} (f : M.X ≅ N.X) (one_f : M.one ≫ f.hom = N.one := by aesop_cat)
    (mul_f : M.mul ≫ f.hom = (f.hom ⊗ f.hom) ≫ N.mul := by aesop_cat) : M ≅ N :=
  have : IsMon_Hom f.hom := ⟨one_f, mul_f⟩
  mkIso' f

@[simps]
instance uniqueHomFromTrivial (A : Mon_ C) : Unique (trivial C ⟶ A) where
  default :=
  { hom := A.one
    mul_hom := by simp [A.one_mul, unitors_equal] }
  uniq f := by
    ext
    simp only [trivial_X]
    rw [← Category.id_comp f.hom]
    erw [f.one_hom]

open CategoryTheory.Limits

instance : HasInitial (Mon_ C) :=
  hasInitial_of_unique (trivial C)

end Mon_

namespace CategoryTheory
variable
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
  {F F' : C ⥤ D} {G : D ⥤ E}

namespace Functor

section LaxMonoidal
variable [F.LaxMonoidal] [F'.LaxMonoidal] [G.LaxMonoidal] (X Y : C) [Mon_Class X] [Mon_Class Y]
  (f : X ⟶ Y) [IsMon_Hom f]

/-- The image of a monoid object under a lax monoidal functor is a monoid object. -/
abbrev obj.instMon_Class : Mon_Class (F.obj X) where
  one := ε F ≫ F.map η
  mul := LaxMonoidal.μ F X X ≫ F.map μ
  one_mul' := by simp [← F.map_comp]
  mul_one' := by simp [← F.map_comp]
  mul_assoc' := by
    simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, Mon_Class.mul_assoc]
    simp

attribute [local instance] obj.instMon_Class

@[reassoc, simp] lemma obj.η_def : (η : 𝟙_ D ⟶ F.obj X) = ε F ≫ F.map η := rfl

@[reassoc, simp] lemma obj.μ_def : μ = LaxMonoidal.μ F X X ≫ F.map μ := rfl

instance map.instIsMon_Hom : IsMon_Hom (F.map f) where
  one_hom := by simp [← map_comp]
  mul_hom := by simp [← map_comp]

-- TODO: mapMod F A : Mod A ⥤ Mod (F.mapMon A)
variable (F) in
/-- A lax monoidal functor takes monoid objects to monoid objects.

That is, a lax monoidal functor `F : C ⥤ D` induces a functor `Mon_ C ⥤ Mon_ D`.
-/
@[simps]
def mapMon : Mon_ C ⥤ Mon_ D where
  -- TODO: The following could be, but it leads to weird `erw`s later down the file
  -- obj A := .mk' (F.obj A.X)
  obj A :=
    { X := F.obj A.X
      one := ε F ≫ F.map A.one
      mul := «μ» F _ _ ≫ F.map A.mul
      one_mul := by
        simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
          LaxMonoidal.left_unitality]
        slice_lhs 3 4 => rw [← F.map_comp, A.one_mul]
      mul_one := by
        simp_rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc,
          LaxMonoidal.right_unitality]
        slice_lhs 3 4 => rw [← F.map_comp, A.mul_one]
      mul_assoc := by
        simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
          MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
        slice_lhs 3 4 => rw [← F.map_comp, A.mul_assoc]
        simp }
  map f := .mk' (F.map f.hom)

/-- The identity functor is also the identity on monoid objects. -/
@[simps!]
noncomputable def mapMonIdIso : mapMon (𝟭 C) ≅ 𝟭 (Mon_ C) :=
  NatIso.ofComponents fun X ↦ Mon_.mkIso (.refl _)

/-- The composition functor is also the composition on monoid objects. -/
@[simps!]
noncomputable def mapMonCompIso : (F ⋙ G).mapMon ≅ F.mapMon ⋙ G.mapMon :=
  NatIso.ofComponents fun X ↦ Mon_.mkIso (.refl _)

protected instance Faithful.mapMon [F.Faithful] : F.mapMon.Faithful where
  map_injective {_X _Y} _f _g hfg := Mon_.Hom.ext <| map_injective congr(($hfg).hom)

/-- Natural transformations between functors lift to monoid objects. -/
@[simps!]
noncomputable def mapMonNatTrans (f : F ⟶ F') [NatTrans.IsMonoidal f] : F.mapMon ⟶ F'.mapMon where
  app X := .mk (f.app _)

/-- Natural isomorphisms between functors lift to monoid objects. -/
@[simps!]
noncomputable def mapMonNatIso (e : F ≅ F') [NatTrans.IsMonoidal e.hom] : F.mapMon ≅ F'.mapMon :=
  NatIso.ofComponents fun X ↦ Mon_.mkIso (e.app _)

end LaxMonoidal

section Monoidal
variable [F.Monoidal]

attribute [local instance] obj.instMon_Class

protected instance Full.mapMon [F.Full] [F.Faithful] : F.mapMon.Full where
  map_surjective {X Y} f :=
    let ⟨g, hg⟩ := F.map_surjective f.hom
    ⟨{
      hom := g
      one_hom := F.map_injective <| by simpa [← hg, cancel_epi] using f.one_hom
      mul_hom := F.map_injective <| by simpa [← hg, cancel_epi] using f.mul_hom
    }, Mon_.Hom.ext hg⟩

instance FullyFaithful.isMon_Hom_preimage (hF : F.FullyFaithful) {X Y : C}
    [Mon_Class X] [Mon_Class Y] (f : F.obj X ⟶ F.obj Y) [IsMon_Hom f] :
    IsMon_Hom (hF.preimage f) where
  one_hom := hF.map_injective <| by simp [← obj.η_def_assoc, ← obj.η_def, ← cancel_epi (ε F)]
  mul_hom := hF.map_injective <| by
    simp [← obj.μ_def_assoc, ← obj.μ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)]

/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then `Mon(F) : Mon C ⥤ Mon D` is fully
faithful too. -/
protected def FullyFaithful.mapMon (hF : F.FullyFaithful) : F.mapMon.FullyFaithful where
  preimage {X Y} f := .mk' <| hF.preimage f.hom

end Monoidal

variable (C D) in
/-- `mapMon` is functorial in the lax monoidal functor. -/
@[simps] -- Porting note: added this, not sure how it worked previously without.
def mapMonFunctor : LaxMonoidalFunctor C D ⥤ Mon_ C ⥤ Mon_ D where
  obj F := F.mapMon
  map α := { app A := { hom := α.hom.app A.X } }
  map_comp _ _ := rfl

end Functor

open Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [a.IsMonoidal]

/-- An adjunction of monoidal functors lifts to an adjunction of their lifts to monoid objects. -/
@[simps] noncomputable def mapMon : F.mapMon ⊣ G.mapMon where
  unit := mapMonIdIso.inv ≫ mapMonNatTrans a.unit ≫ mapMonCompIso.hom
  counit := mapMonCompIso.inv ≫ mapMonNatTrans a.counit ≫ mapMonIdIso.hom

end Adjunction

namespace Equivalence

/-- An equivalence of categories lifts to an equivalence of their monoid objects. -/
@[simps]
noncomputable def mapMon (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal] :
    Mon_ C ≌ Mon_ D where
  functor := e.functor.mapMon
  inverse := e.inverse.mapMon
  unitIso := mapMonIdIso.symm ≪≫ mapMonNatIso e.unitIso ≪≫ mapMonCompIso
  counitIso := mapMonCompIso.symm ≪≫ mapMonNatIso e.counitIso ≪≫ mapMonIdIso

end CategoryTheory.Equivalence

namespace Mon_

namespace EquivLaxMonoidalFunctorPUnit

variable (C) in
/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def laxMonoidalToMon : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ⥤ Mon_ C where
  obj F := (F.mapMon : Mon_ _ ⥤ Mon_ C).obj (trivial (Discrete PUnit))
  map α := ((Functor.mapMonFunctor (Discrete PUnit) C).map α).app _

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def monToLaxMonoidalObj (A : Mon_ C) :
    Discrete PUnit.{u + 1} ⥤ C := (Functor.const _).obj A.X

instance (A : Mon_ C) : (monToLaxMonoidalObj A).LaxMonoidal where
  ε' := A.one
  μ' _ _ := A.mul

@[simp]
lemma monToLaxMonoidalObj_ε (A : Mon_ C) :
    ε (monToLaxMonoidalObj A) = A.one := rfl

@[simp]
lemma monToLaxMonoidalObj_μ (A : Mon_ C) (X Y) :
    «μ» (monToLaxMonoidalObj A) X Y = A.mul := rfl

variable (C)
/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def monToLaxMonoidal : Mon_ C ⥤ LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C where
  obj A := LaxMonoidalFunctor.of (monToLaxMonoidalObj A)
  map f :=
    { hom := { app _ := f.hom }
      isMonoidal := { } }

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def unitIso :
    𝟭 (LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C) ≅ laxMonoidalToMon C ⋙ monToLaxMonoidal C :=
  NatIso.ofComponents
    (fun F ↦ LaxMonoidalFunctor.isoOfComponents (fun _ ↦ F.mapIso (eqToIso (by ext))))

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def counitIso : monToLaxMonoidal C ⋙ laxMonoidalToMon C ≅ 𝟭 (Mon_ C) :=
  NatIso.ofComponents fun F ↦ mkIso (Iso.refl _)

end EquivLaxMonoidalFunctorPUnit

open EquivLaxMonoidalFunctorPUnit

attribute [local simp] eqToIso_map

/--
Monoid objects in `C` are "just" lax monoidal functors from the trivial monoidal category to `C`.
-/
@[simps]
def equivLaxMonoidalFunctorPUnit : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ≌ Mon_ C where
  functor := laxMonoidalToMon C
  inverse := monToLaxMonoidal C
  unitIso := unitIso C
  counitIso := counitIso C

end Mon_

namespace Mon_Class

/-!
In this section, we prove that the category of monoids in a braided monoidal category is monoidal.

Given two monoids `M` and `N` in a braided monoidal category `C`,
the multiplication on the tensor product `M.X ⊗ N.X` is defined in the obvious way:
it is the tensor product of the multiplications on `M` and `N`,
except that the tensor factors in the source come in the wrong order,
which we fix by pre-composing with a permutation isomorphism constructed from the braiding.

(There is a subtlety here: in fact there are two ways to do these,
using either the positive or negative crossing.)

A more conceptual way of understanding this definition is the following:
The braiding on `C` gives rise to a monoidal structure on
the tensor product functor from `C × C` to `C`.
A pair of monoids in `C` gives rise to a monoid in `C × C`,
which the tensor product functor by being monoidal takes to a monoid in `C`.
The permutation isomorphism appearing in the definition of
the multiplication on the tensor product of two monoids is
an instance of a more general family of isomorphisms
which together form a strength that equips the tensor product functor with a monoidal structure,
and the monoid axioms for the tensor product follow from the monoid axioms for the tensor factors
plus the properties of the strength (i.e., monoidal functor axioms).
The strength `tensorμ` of the tensor product functor has been defined in
`Mathlib/CategoryTheory/Monoidal/Braided.lean`.
Its properties, stated as independent lemmas in that module,
are used extensively in the proofs below.
Notice that we could have followed the above plan not only conceptually
but also as a possible implementation and
could have constructed the tensor product of monoids via `mapMon`,
but we chose to give a more explicit definition directly in terms of `tensorμ`.

To complete the definition of the monoidal category structure on the category of monoids,
we need to provide definitions of associator and unitors.
The obvious candidates are the associator and unitors from `C`,
but we need to prove that they are monoid morphisms, i.e., compatible with unit and multiplication.
These properties translate to the monoidality of the associator and unitors
(with respect to the monoidal structures on the functors they relate),
which have also been proved in `Mathlib/CategoryTheory/Monoidal/Braided.lean`.

-/

-- The proofs that associators and unitors preserve monoid units don't require braiding.
theorem one_associator {M N P : C} [Mon_Class M] [Mon_Class N] [Mon_Class P] :
    ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ η[N]) ⊗ η[P])) ≫ (α_ M N P).hom =
      (λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ (λ_ (𝟙_ C)).inv ≫ (η[N] ⊗ η[P])) := by
  simp only [Category.assoc, Iso.cancel_iso_inv_left]
  slice_lhs 1 3 => rw [← Category.id_comp (η : 𝟙_ C ⟶ P), tensor_comp]
  slice_lhs 2 3 => rw [associator_naturality]
  slice_rhs 1 2 => rw [← Category.id_comp η, tensor_comp]
  slice_lhs 1 2 => rw [tensorHom_id, ← leftUnitor_tensor_inv]
  rw [← cancel_epi (λ_ (𝟙_ C)).inv]
  slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
  simp

theorem one_leftUnitor {M : C} [Mon_Class M] :
    ((λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ η[M])) ≫ (λ_ M).hom = η := by
  simp

theorem one_rightUnitor {M : C} [Mon_Class M] :
    ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ 𝟙 (𝟙_ C))) ≫ (ρ_ M).hom = η := by
  simp [← unitors_equal]

section BraidedCategory

variable [BraidedCategory C]

theorem Mon_tensor_one_mul (M N : C) [Mon_Class M] [Mon_Class N] :
    (((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ η[N])) ▷ (M ⊗ N)) ≫
        tensorμ M N M N ≫ (μ ⊗ μ) =
      (λ_ (M ⊗ N)).hom := by
  simp only [comp_whiskerRight_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [← tensor_comp, one_mul, one_mul]
  symm
  exact tensor_left_unitality M N

theorem Mon_tensor_mul_one (M N : C) [Mon_Class M] [Mon_Class N] :
    (M ⊗ N) ◁ ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ η[N])) ≫
        tensorμ M N M N ≫ (μ[M] ⊗ μ[N]) =
      (ρ_ (M ⊗ N)).hom := by
  simp only [MonoidalCategory.whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_right]
  slice_lhs 3 4 => rw [← tensor_comp, mul_one, mul_one]
  symm
  exact tensor_right_unitality M N

theorem Mon_tensor_mul_assoc (M N : C) [Mon_Class M] [Mon_Class N] :
    ((tensorμ M N M N ≫ (μ ⊗ μ)) ▷ (M ⊗ N)) ≫
        tensorμ M N M N ≫ (μ ⊗ μ) =
      (α_ (M ⊗ N : C) (M ⊗ N) (M ⊗ N)).hom ≫
        ((M ⊗ N : C) ◁ (tensorμ M N M N ≫ (μ ⊗ μ))) ≫
          tensorμ M N M N ≫ (μ ⊗ μ) := by
  simp only [comp_whiskerRight_assoc, MonoidalCategory.whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [← tensor_comp, mul_assoc, mul_assoc, tensor_comp, tensor_comp]
  slice_lhs 1 3 => rw [tensor_associativity]
  slice_lhs 3 4 => rw [← tensorμ_natural_right]
  simp

theorem mul_associator {M N P : C} [Mon_Class M] [Mon_Class N] [Mon_Class P] :
    (tensorμ (M ⊗ N) P (M ⊗ N) P ≫
          (tensorμ M N M N ≫ (μ ⊗ μ) ⊗ μ)) ≫
        (α_ M N P).hom =
      ((α_ M N P).hom ⊗ (α_ M N P).hom) ≫
        tensorμ M (N ⊗ P) M (N ⊗ P) ≫
          (μ ⊗ tensorμ N P N P ≫ (μ ⊗ μ)) := by
  simp only [tensor_obj, prodMonoidal_tensorObj, Category.assoc]
  slice_lhs 2 3 => rw [← Category.id_comp μ[P], tensor_comp]
  slice_lhs 3 4 => rw [associator_naturality]
  slice_rhs 3 4 => rw [← Category.id_comp μ, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 1 3 => rw [associator_monoidal]
  simp only [Category.assoc]

theorem mul_leftUnitor {M : C} [Mon_Class M] :
    (tensorμ (𝟙_ C) M (𝟙_ C) M ≫ ((λ_ (𝟙_ C)).hom ⊗ μ)) ≫ (λ_ M).hom =
      ((λ_ M).hom ⊗ (λ_ M).hom) ≫ μ := by
  rw [← Category.comp_id (λ_ (𝟙_ C)).hom, ← Category.id_comp μ, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 1 3 => rw [← leftUnitor_monoidal]
  simp only [Category.assoc, Category.id_comp]

theorem mul_rightUnitor {M : C} [Mon_Class M] :
    (tensorμ M (𝟙_ C) M (𝟙_ C) ≫ (μ ⊗ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ M).hom =
      ((ρ_ M).hom ⊗ (ρ_ M).hom) ≫ μ := by
  rw [← Category.id_comp μ, ← Category.comp_id (λ_ (𝟙_ C)).hom, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  slice_lhs 1 3 => rw [← rightUnitor_monoidal]
  simp only [Category.assoc, Category.id_comp]

namespace tensorObj

@[simps]
instance {M N : C} [Mon_Class M] [Mon_Class N] : Mon_Class (M ⊗ N) where
  one := (λ_ (𝟙_ C)).inv ≫ (η ⊗ η)
  mul := tensorμ M N M N ≫ (μ ⊗ μ)
  one_mul' := Mon_tensor_one_mul M N
  mul_one' := Mon_tensor_mul_one M N
  mul_assoc' := Mon_tensor_mul_assoc M N

end tensorObj

open IsMon_Hom

variable {X Y Z W : C} [Mon_Class X] [Mon_Class Y] [Mon_Class Z] [Mon_Class W]

instance {f : X ⟶ Y} {g : Z ⟶ W} [IsMon_Hom f] [IsMon_Hom g] : IsMon_Hom (f ⊗ g) where
  one_hom := by
    dsimp
    slice_lhs 2 3 => rw [← tensor_comp, one_hom, one_hom]
  mul_hom := by
    dsimp
    slice_rhs 1 2 => rw [tensorμ_natural]
    slice_lhs 2 3 => rw [← tensor_comp, mul_hom, mul_hom, tensor_comp]
    simp only [Category.assoc]

instance : IsMon_Hom (𝟙 X) where

instance {f : Y ⟶ Z} [IsMon_Hom f] : IsMon_Hom (X ◁ f) where
  one_hom := by simpa using (inferInstanceAs <| IsMon_Hom (𝟙 X ⊗ f)).one_hom
  mul_hom := by simpa using (inferInstanceAs <| IsMon_Hom (𝟙 X ⊗ f)).mul_hom

instance {f : X ⟶ Y} [IsMon_Hom f] : IsMon_Hom (f ▷ Z) where
  one_hom := by simpa using (inferInstanceAs <| IsMon_Hom (f ⊗ (𝟙 Z))).one_hom
  mul_hom := by simpa using (inferInstanceAs <| IsMon_Hom (f ⊗ (𝟙 Z))).mul_hom

instance : IsMon_Hom (α_ X Y Z).hom :=
  ⟨one_associator, mul_associator⟩

instance : IsMon_Hom (λ_ X).hom :=
  ⟨one_leftUnitor, mul_leftUnitor⟩

instance : IsMon_Hom (ρ_ X).hom :=
  ⟨one_rightUnitor, mul_rightUnitor⟩

theorem one_braiding (X Y : C) [Mon_Class X] [Mon_Class Y] : η ≫ (β_ X Y).hom = η := by
  simp only [tensorObj.one_def, Category.assoc, BraidedCategory.braiding_naturality,
    braiding_tensorUnit_right, Iso.cancel_iso_inv_left]
  monoidal

end BraidedCategory

end Mon_Class

namespace Mon_

section BraidedCategory

variable [BraidedCategory C]

@[simps! tensorObj_X tensorHom_hom]
instance monMonoidalStruct : MonoidalCategoryStruct (Mon_ C) where
  tensorObj M N := mk' (M.X ⊗ N.X)
  tensorHom f g := Hom.mk' (f.hom ⊗ g.hom)
  whiskerRight f Y := Hom.mk' (f.hom ▷ Y.X)
  whiskerLeft X _ _ g := Hom.mk' (X.X ◁ g.hom)
  tensorUnit := mk' (𝟙_ C)
  associator M N P := mkIso' <| associator M.X N.X P.X
  leftUnitor M := mkIso' <| leftUnitor M.X
  rightUnitor M := mkIso' <| rightUnitor M.X

@[simp]
theorem tensorUnit_X : (𝟙_ (Mon_ C)).X = 𝟙_ C := rfl

@[simp]
theorem tensorUnit_one : (𝟙_ (Mon_ C)).one = 𝟙 (𝟙_ C) := rfl

@[simp]
theorem tensorUnit_mul : (𝟙_ (Mon_ C)).mul = (λ_ (𝟙_ C)).hom := rfl

@[simp]
theorem tensorObj_one (X Y : Mon_ C) : (X ⊗ Y).one = (λ_ (𝟙_ C)).inv ≫ (X.one ⊗ Y.one) := rfl

@[simp]
theorem tensorObj_mul (X Y : Mon_ C) :
    (X ⊗ Y).mul = tensorμ X.X Y.X X.X Y.X ≫ (X.mul ⊗ Y.mul) := rfl

@[simp]
theorem whiskerLeft_hom {X Y : Mon_ C} (f : X ⟶ Y) (Z : Mon_ C) :
    (f ▷ Z).hom = f.hom ▷ Z.X := by
  rfl

@[simp]
theorem whiskerRight_hom (X : Mon_ C) {Y Z : Mon_ C} (f : Y ⟶ Z) :
    (X ◁ f).hom = X.X ◁ f.hom := by
  rfl

@[simp]
theorem leftUnitor_hom_hom (X : Mon_ C) : (λ_ X).hom.hom = (λ_ X.X).hom := rfl

@[simp]
theorem leftUnitor_inv_hom (X : Mon_ C) : (λ_ X).inv.hom = (λ_ X.X).inv := rfl

@[simp]
theorem rightUnitor_hom_hom (X : Mon_ C) : (ρ_ X).hom.hom = (ρ_ X.X).hom := rfl

@[simp]
theorem rightUnitor_inv_hom (X : Mon_ C) : (ρ_ X).inv.hom = (ρ_ X.X).inv := rfl

@[simp]
theorem associator_hom_hom (X Y Z : Mon_ C) : (α_ X Y Z).hom.hom = (α_ X.X Y.X Z.X).hom := rfl

@[simp]
theorem associator_inv_hom (X Y Z : Mon_ C) : (α_ X Y Z).inv.hom = (α_ X.X Y.X Z.X).inv := rfl

@[simp]
theorem tensor_one (M N : Mon_ C) : (M ⊗ N).one = (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one) := rfl

@[simp]
theorem tensor_mul (M N : Mon_ C) : (M ⊗ N).mul =
    tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul) := rfl

instance monMonoidal : MonoidalCategory (Mon_ C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]

@[simps!]
instance {M N : C} [Mon_Class M] [Mon_Class N] : Mon_Class (M ⊗ N) :=
  inferInstanceAs <| Mon_Class (Mon_.mk' M ⊗ Mon_.mk' N).X

variable (C)

/-- The forgetful functor from `Mon_ C` to `C` is monoidal when `C` is monoidal. -/
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

@[simp] theorem forget_ε : ε (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_η : «η» (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_μ (X Y : Mon_ C) : «μ» (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl
@[simp] theorem forget_δ (X Y : Mon_ C) : δ (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl

end BraidedCategory

end Mon_

/-!
We next show that if `C` is symmetric, then `Mon_ C` is braided, and indeed symmetric.

Note that `Mon_ C` is *not* braided in general when `C` is only braided.

The more interesting construction is the 2-category of monoids in `C`,
bimodules between the monoids, and intertwiners between the bimodules.

When `C` is braided, that is a monoidal 2-category.
-/
section SymmetricCategory

variable [SymmetricCategory C]

namespace Mon_Class

theorem mul_braiding (X Y : C) [Mon_Class X] [Mon_Class Y] :
    μ ≫ (β_ X Y).hom = ((β_ X Y).hom ⊗ (β_ X Y).hom) ≫ μ := by
  dsimp
  simp only [tensorμ, Category.assoc, BraidedCategory.braiding_naturality,
    BraidedCategory.braiding_tensor_right, BraidedCategory.braiding_tensor_left,
    comp_whiskerRight, whisker_assoc, MonoidalCategory.whiskerLeft_comp, pentagon_assoc,
    pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
  slice_lhs 3 4 =>
    -- We use symmetry here:
    rw [← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight, SymmetricCategory.symmetry]
  simp only [id_whiskerRight, MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.assoc,
    pentagon_inv_assoc, Iso.hom_inv_id_assoc]
  slice_lhs 1 2 =>
    rw [← associator_inv_naturality_left]
  slice_lhs 2 3 =>
    rw [Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 2 3 =>
    rw [← associator_naturality_right]
  slice_lhs 1 2 =>
    rw [← tensorHom_def]
  simp only [Category.assoc]

instance {X Y : C} [Mon_Class X] [Mon_Class Y] : IsMon_Hom (β_ X Y).hom :=
  ⟨one_braiding X Y, mul_braiding X Y⟩

end Mon_Class

namespace Mon_

instance : SymmetricCategory (Mon_ C) where
  braiding X Y := mkIso' (β_ X.X Y.X)
  symmetry X Y := by
    ext
    simp [← SymmetricCategory.braiding_swap_eq_inv_braiding]

end Mon_

end SymmetricCategory

section

variable [BraidedCategory.{v₁} C]

/-- Predicate for a monoid object to be commutative. -/
class IsCommMon (X : C) [Mon_Class X] where
  mul_comm' : (β_ X X).hom ≫ μ = μ := by aesop_cat

open scoped Mon_Class

namespace IsCommMon

@[reassoc (attr := simp)]
theorem mul_comm (X : C) [Mon_Class X] [IsCommMon X] : (β_ X X).hom ≫ μ = μ := mul_comm'

end IsCommMon

end

/-!
Projects:
* Check that `Mon_ MonCat ≌ CommMonCat`, via the Eckmann-Hilton argument.
  (You'll have to hook up the cartesian monoidal structure on `MonCat` first,
  available in https://github.com/leanprover-community/mathlib3/pull/3463)
* More generally, check that `Mon_ (Mon_ C) ≌ CommMon_ C` when `C` is braided.
* Check that `Mon_ TopCat ≌ [bundled topological monoids]`.
* Check that `Mon_ AddCommGrp ≌ RingCat`.
  (We've already got `Mon_ (ModuleCat R) ≌ AlgCat R`,
  in `Mathlib/CategoryTheory/Monoidal/Internal/Module.lean`.)
* Can you transport this monoidal structure to `RingCat` or `AlgCat R`?
  How does it compare to the "native" one?
* Show that when `F` is a lax braided functor `C ⥤ D`, the functor `map_Mon F : Mon_ C ⥤ Mon_ D`
  is lax monoidal.
-/
