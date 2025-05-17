/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Group.PUnit
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Tactic.Widget.StringDiagram

/-!
# The category of monoids in a monoidal category.

We define monoids in a monoidal category `C` and show that the category of monoids is equivalent to
the category of lax monoidal functors from the unit monoidal category to `C`.  We also show that if
`C` is braided, then the category of monoids is naturally monoidal.

-/


universe v₁ v₂ u₁ u₂ u

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
  one_mul : (one ▷ X) ≫ mul = (λ_ X).hom := by aesop_cat
  mul_one : (X ◁ one) ≫ mul = (ρ_ X).hom := by aesop_cat
  -- Obviously there is some flexibility stating this axiom.
  -- This one has left- and right-hand sides matching the statement of `Monoid.mul_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  mul_assoc : (mul ▷ X) ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul := by aesop_cat

namespace Mon_Class

@[inherit_doc] scoped notation "μ" => Mon_Class.mul
@[inherit_doc] scoped notation "μ["M"]" => Mon_Class.mul (X := M)
@[inherit_doc] scoped notation "η" => Mon_Class.one
@[inherit_doc] scoped notation "η["M"]" => Mon_Class.one (X := M)

attribute [reassoc, simp] one_mul mul_one
attribute [reassoc (attr := simp)] mul_assoc

-- @[reassoc, simp]
-- theorem one_mul (X : C) [Mon_Class X] : (η ▷ X) ≫ μ = (λ_ X).hom := one_mul'

-- @[reassoc, simp]
-- theorem mul_one (X : C) [Mon_Class X] : (X ◁ η) ≫ μ = (ρ_ X).hom := mul_one'

-- -- We prove a more general `@[simp]` lemma below.
-- @[reassoc (attr := simp)]
-- theorem mul_assoc (X : C) [Mon_Class X] : (μ ▷ X) ≫ μ =
--  (α_ X X X).hom ≫ (X ◁ μ) ≫ μ := mul_assoc'

/-- The trivial monoid object. We later show this is initial in `Mon_Cat C`.
-/
@[simps]
instance trivial (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] : Mon_Class (𝟙_ C) where
  one := 𝟙 _
  mul := (λ_ _).hom
  mul_assoc := by monoidal_coherence
  mul_one := by monoidal_coherence

instance : Inhabited (Mon_Class (𝟙_ C)) :=
  ⟨trivial C⟩

variable {M : C}
variable [Mon_Class M]

@[simp]
theorem one_mul_hom {Z : C} (f : Z ⟶ M) : (η[M] ⊗ f) ≫ μ = (λ_ Z).hom ≫ f := by
  rw [tensorHom_def'_assoc, one_mul, leftUnitor_naturality]

@[simp]
theorem mul_one_hom {Z : C} (f : Z ⟶ M) : (f ⊗ η) ≫ μ = (ρ_ Z).hom ≫ f := by
  rw [tensorHom_def_assoc, mul_one, rightUnitor_naturality]

theorem mul_assoc_flip :
    (M ◁ μ) ≫ μ = (α_ M M M).inv ≫ (μ ▷ M) ≫ μ := by simp

end Mon_Class

open scoped Mon_Class

variable {M N : C} [Mon_Class M] [Mon_Class N]

/-- The property that a morphism between monoid objects is a monoid morphism. -/
class IsMon_Hom (f : M ⟶ N) : Prop where
  one_hom (f) : η ≫ f = η := by aesop_cat
  mul_hom (f) : μ ≫ f = (f ⊗ f) ≫ μ := by aesop_cat

attribute [reassoc (attr := simp)] IsMon_Hom.one_hom IsMon_Hom.mul_hom

open Mon_Class

/-- A morphism of monoid objects. -/
@[ext]
structure Mon_ClassHom (M N : C) [Mon_Class M] [Mon_Class N] where
  hom : M ⟶ N
  one_hom : η ≫ hom = η := by aesop_cat
  mul_hom : μ ≫ hom = (hom ⊗ hom) ≫ μ := by aesop_cat

-- class HomClass {M N : C} [Mon_Class M] [Mon_Class N] (f : M ⟶ N) : Prop where
--   one_hom : η ≫ f = η
--   mul_hom : μ ≫ f = (f ⊗ f) ≫ μ

attribute [reassoc (attr := simp)] Mon_ClassHom.one_hom Mon_ClassHom.mul_hom

/-- The identity morphism on a monoid object. -/
@[simps]
def Mon_ClassHom.id (M : C) [Mon_Class M] : Mon_ClassHom M M where
  hom := 𝟙 M

instance (M : C) [Mon_Class M] : Inhabited (Mon_ClassHom M M) :=
  ⟨.id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def Mon_ClassHom.comp {M N O : C} [Mon_Class M] [Mon_Class N] [Mon_Class O]
    (f : Mon_ClassHom M N) (g : Mon_ClassHom N O) : Mon_ClassHom M O where
  hom := f.hom ≫ g.hom

@[ext]
structure Mon_ClassIso (M N : C) [Mon_Class M] [Mon_Class N] extends M ≅ N, Mon_ClassHom M N
  -- iso : M ≅ N
  -- one_hom : η ≫ iso.hom = η := by aesop_cat
  -- mul_hom : μ ≫ iso.hom = (iso.hom ⊗ iso.hom) ≫ μ := by aesop_cat
  -- inv : Mon_ClassHom N M
  -- hom_inv_id : hom.hom ≫ inv.hom = 𝟙 M := by aesop_cat
  -- inv_hom_id : inv.hom ≫ hom.hom = 𝟙 N := by aesop_cat

initialize_simps_projections Mon_ClassIso (-hom, -inv, +toIso)

attribute [reassoc (attr := simp)] Mon_ClassIso.one_hom Mon_ClassIso.mul_hom

example (M N : C) [Mon_Class M] [Mon_Class N] (f : Mon_ClassIso M N) :
    f.toIso.hom = f.toMon_ClassHom.hom :=
  rfl

-- theorem Mon_ClassIso.

@[simps]
def Mon_ClassIso.symm {M N : C} [Mon_Class M] [Mon_Class N] (f : Mon_ClassIso M N) :
    Mon_ClassIso N M where
  toIso := f.toIso.symm
  one_hom := by simp [Iso.comp_inv_eq]
  mul_hom := by simp [Iso.comp_inv_eq]

-- @[simps?]
-- def Mon_ClassIso.toMon_ClassHom {M N : C} [Mon_Class M] [Mon_Class N] (f : Mon_ClassIso M N) :
--     Mon_ClassHom M N where
--   hom := f.iso.hom

-- attribute [simp] Mon_ClassIso.hom_inv_id Mon_ClassIso.inv_hom_id

structure Mon_Cat (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] where
  X : C
  [isMon_Class : Mon_Class X]

namespace Mon_Cat

open Mon_Class

attribute [instance] Mon_Cat.isMon_Class

instance : Inhabited (Mon_Cat C) :=
  ⟨⟨𝟙_ C⟩⟩

initialize_simps_projections Mon_Cat (-isMon_Class)

instance : Category.{v₁} (Mon_Cat C) where
  Hom M N := Mon_ClassHom M.X N.X
  id M := Mon_ClassHom.id M.X
  comp f g := Mon_ClassHom.comp f g

/-- Construct a morphism `M ⟶ N` of `Mon_ C` from a map `f : M ⟶ N` and a `IsMon_Hom f` instance. -/
abbrev Hom.mk' {M N : C} [Mon_Class M] [Mon_Class N] (f : M ⟶ N) [IsMon_Hom f] :
    (Mon_Cat.mk M) ⟶ (Mon_Cat.mk N) := .mk f

def mkHom {X Y : C} [Mon_Class X] [Mon_Class Y] (f : Mon_ClassHom X Y) :
    mk X ⟶ mk Y :=
  f

@[simp]
theorem mkHom_hom {X Y : C} [Mon_Class X] [Mon_Class Y] (f : Mon_ClassHom X Y) :
    (mkHom f).hom = f.hom :=
  rfl

-- Porting note: added, as `Hom.ext` does not apply to a morphism.
@[ext]
lemma ext' {X Y : Mon_Cat C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g :=
  Mon_ClassHom.ext w

@[simp]
theorem id_hom' {M : Mon_Cat C} : (𝟙 M : Mon_ClassHom M.X M.X).hom = 𝟙 M.X :=
  rfl

@[simp]
theorem comp_hom' {M N K : Mon_Cat C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[simps]
def mkIso {X Y : C} [Mon_Class X] [Mon_Class Y] (f : Mon_ClassIso X Y) :
    mk X ≅ mk Y where
  hom := mkHom f.toMon_ClassHom
  inv := mkHom f.symm.toMon_ClassHom

@[simps!]
def mkIso' {X Y : Mon_Cat C} (f : Mon_ClassIso X.X Y.X) :
    X ≅ Y :=
  mkIso f

section

variable (C)

/-- The forgetful functor from monoid objects to the ambient category. -/
@[simps]
def forget : Mon_Cat C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : (forget C).Faithful where

instance {A B : C} [Mon_Class A] [Mon_Class B] (f : Mon_ClassHom A B)
    [e : IsIso ((forget C).map (Mon_Cat.mkHom f))] :
    IsIso f.hom :=
  e

instance {A B : Mon_Cat C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] :
    IsIso f.hom :=
  e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e := ⟨⟨{ hom := inv f.hom }, by aesop_cat⟩⟩

instance uniqueHomFromTrivial (A : Mon_Cat C) : Unique (Mon_Cat.mk (𝟙_ C) ⟶ A) where
  default :=
  { hom := η
    mul_hom := by dsimp; simp [Mon_Class.one_mul, unitors_equal] }
  uniq f := by
    ext
    dsimp only [trivial_mul]
    rw [← Category.id_comp f.hom, ← trivial_one, f.one_hom]

open CategoryTheory.Limits

instance : HasInitial (Mon_Cat C) :=
  hasInitial_of_unique (mk (𝟙_ C))

end Mon_Cat

namespace Mon_Class

-- /-- Construct an isomorphism of monoids by giving an isomorphism between the underlying objects
-- and checking compatibility with unit and multiplication only in the forward direction.
-- -/
-- @[simps]
-- def mkIso {M N : C} [Mon_Class M] [Mon_Class N] (f : M ≅ N)
--     (one_f : η ≫ f.hom = η := by aesop_cat)
--     (mul_f : μ ≫ f.hom = (f.hom ⊗ f.hom) ≫ μ := by aesop_cat) :
--     Mon_ClassIso M N where
--   iso := f
--   toMon_ClassHom := {
--     hom := f.hom
--     one_hom := one_f
--     mul_hom := mul_f
--   }
  -- hom := { hom := f.hom }
  -- inv := {
  --   hom := f.inv
  --   one_hom := by rw [← one_f]; simp
  --   mul_hom := by
  --     rw [← cancel_mono f.hom]
  --     slice_rhs 2 3 => rw [mul_f]
  --     simp }

end Mon_Class

open Mon_Class

namespace CategoryTheory.Functor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D] (F : C ⥤ D)

section LaxMonoidal
variable [F.LaxMonoidal] (X Y : C) [Mon_Class X] [Mon_Class Y] (f : X ⟶ Y) [IsMon_Hom f]

/-- The image of a monoid object under a lax monoidal functor is a monoid object. -/
abbrev obj.instMon_Class : Mon_Class (F.obj X) where
  one := ε F ≫ F.map η
  mul := LaxMonoidal.μ F X X ≫ F.map μ
  one_mul := by simp [← F.map_comp]
  mul_one := by simp [← F.map_comp]
  mul_assoc := by
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

open Mon_Class

-- TODO: mapMod F A : Mod A ⥤ Mod (F.mapMonCat A)
/-- A lax monoidal functor takes monoid objects to monoid objects.

That is, a lax monoidal functor `F : C ⥤ D` induces a functor `Mon_Cat C ⥤ Mon_Class D`.
-/
@[simps]
def mapMonCat (F : C ⥤ D) [F.LaxMonoidal] : Mon_Cat C ⥤ Mon_Cat D where
  obj A := Mon_Cat.mk (F.obj A.X)
  map {A B} f := Mon_Cat.mkHom
    { hom := F.map f.hom
      one_hom := by dsimp; rw [Category.assoc, ← F.map_comp, f.one_hom]
      mul_hom := by
        dsimp
        rw [Category.assoc, LaxMonoidal.μ_natural_assoc, ← F.map_comp, ← F.map_comp,
          f.mul_hom] }

protected instance Faithful.mapMonCat [F.Faithful] : F.mapMonCat.Faithful where
  map_injective {_X _Y} _f _g hfg := Mon_Cat.ext' <| map_injective congr(($hfg).hom)

end LaxMonoidal

section Monoidal
variable [F.Monoidal]

attribute [local instance] obj.instMon_Class

protected instance Full.mapMon [F.Full] [F.Faithful] : F.mapMonCat.Full where
  map_surjective {X Y} f :=
    let ⟨g, hg⟩ := F.map_surjective f.hom
    ⟨{
      hom := g
      one_hom := F.map_injective <| by simpa [← hg, cancel_epi] using f.one_hom
      mul_hom := F.map_injective <| by simpa [← hg, cancel_epi] using f.mul_hom
    }, Mon_Cat.ext' hg⟩

instance FullyFaithful.isMon_Hom_preimage (hF : F.FullyFaithful) {X Y : C}
    [Mon_Class X] [Mon_Class Y] (f : F.obj X ⟶ F.obj Y) [IsMon_Hom f] :
    IsMon_Hom (hF.preimage f) where
  one_hom := hF.map_injective <| by simp [← obj.η_def_assoc, ← obj.η_def, ← cancel_epi (ε F)]
  mul_hom := hF.map_injective <| by
    simp [← obj.μ_def_assoc, ← obj.μ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)]

/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then `Mon(F) : Mon C ⥤ Mon D` is fully
faithful too. -/
protected def FullyFaithful.mapMon (hF : F.FullyFaithful) : F.mapMonCat.FullyFaithful where
  preimage {X Y} f := Mon_Cat.Hom.mk' <| hF.preimage f.hom

end Monoidal

variable (C D)

/-- `mapMonCat` is functorial in the lax monoidal functor. -/
@[simps] -- Porting note: added this, not sure how it worked previously without.
def mapMonCatFunctor : LaxMonoidalFunctor C D ⥤ Mon_Cat C ⥤ Mon_Cat D where
  obj F := F.mapMonCat
  map {F G} α := { app := fun A => { hom := α.hom.app A.X } }

end CategoryTheory.Functor

namespace Mon_Cat

open CategoryTheory.LaxMonoidalFunctor

namespace EquivLaxMonoidalFunctorPUnit

variable (C) in

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def laxMonoidalToMon : Functor (Discrete PUnit.{u + 1}) C ⥤ Mon_Cat C where
  obj F := (F.mapMonCat : Mon_Cat _ ⥤ Mon_Cat C).obj (.mk (𝟙_ (Discrete PUnit)))
  map α := ((mapMonCatFunctor (Discrete PUnit) C).map α).app _

-- @[simps]
def monToLaxMonoidalObj (A : C) : Functor (Discrete PUnit.{u + 1}) C where
  obj := fun _ => A
  map := fun _ => 𝟙 _

@[simps?]
instance (A : C) [Mon_Class A] : LaxMonoidal (monToLaxMonoidalObj A) where
  ε' := η[A]
  μ' := fun _ _ => μ[A]

@[simp]
lemma monToLaxMonoidalObj_ε (A : C) [Mon_Class A] :
    LaxMonoidal.ε (monToLaxMonoidalObj A) = η[A] := rfl

@[simp]
lemma monToLaxMonoidalObj_μ (A : C) [Mon_Class A] (X Y) :
    LaxMonoidal.μ (monToLaxMonoidalObj A) X Y = μ[A] := rfl

variable (C)

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def monToLaxMonoidal : Mon_Cat C ⥤ LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C where
  obj A := LaxMonoidalFunctor.of (monToLaxMonoidalObj A.X)
  map {X Y} f :=
    { hom := { app := fun _ => f.hom }
      isMonoidal := { } }

-- attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
--   CategoryTheory.Discrete.discreteCases

attribute [local simp] eqToIso_map

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def unitIso :
    𝟭 (LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C) ≅ laxMonoidalToMon C ⋙ monToLaxMonoidal C :=
  NatIso.ofComponents
    (fun F ↦ LaxMonoidalFunctor.isoOfComponents (fun _ ↦ F.mapIso (eqToIso (by ext))))


-- attribute [-simp] monToLaxMonoidalObj_toFunctor_obj in
/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def counitIso : monToLaxMonoidal C ⋙ laxMonoidalToMon C ≅ 𝟭 (Mon_Cat C) :=
  NatIso.ofComponents (fun F => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } })

end EquivLaxMonoidalFunctorPUnit

open EquivLaxMonoidalFunctorPUnit

attribute [local simp] eqToIso_map

/--
Monoid objects in `C` are "just" lax monoidal functors from the trivial monoidal category to `C`.
-/
@[simps]
def equivLaxMonoidalFunctorPUnit : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ≌ Mon_Cat C where
  functor := laxMonoidalToMon C
  inverse := monToLaxMonoidal C
  unitIso := unitIso C
  counitIso := counitIso C

end Mon_Cat

namespace Mon_Class

/-!
In this section, we prove that the category of monoids in a braided monoidal category is monoidal.

Given two monoids `M` and `N` in a braided monoidal category `C`,
the multiplication on the tensor product `M ⊗ N` is defined in the obvious way:
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
The strength `tensor_μ` of the tensor product functor has been defined in
`Mathlib.CategoryTheory.Monoidal.Braided`.
Its properties, stated as independent lemmas in that module,
are used extensively in the proofs below.
Notice that we could have followed the above plan not only conceptually
but also as a possible implementation and
could have constructed the tensor product of monoids via `mapMonCat`,
but we chose to give a more explicit definition directly in terms of `tensor_μ`.

To complete the definition of the monoidal category structure on the category of monoids,
we need to provide definitions of associator and unitors.
The obvious candidates are the associator and unitors from `C`,
but we need to prove that they are monoid morphisms, i.e., compatible with unit and multiplication.
These properties translate to the monoidality of the associator and unitors
(with respect to the monoidal structures on the functors they relate),
which have also been proved in `Mathlib.CategoryTheory.Monoidal.Braided`.

-/


-- variable {C}

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

@[simps]
instance {M N : C} [Mon_Class M] [Mon_Class N] : Mon_Class (M ⊗ N : C) where
  one := (λ_ (𝟙_ C)).inv ≫ (η ⊗ η)
  mul := tensorμ M N M N ≫ (μ ⊗ μ)
  one_mul := Mon_tensor_one_mul M N
  mul_one := Mon_tensor_mul_one M N
  mul_assoc := Mon_tensor_mul_assoc M N

@[simps]
def tensorHom {X₁ Y₁ X₂ Y₂ : C} [Mon_Class X₁] [Mon_Class Y₁] [Mon_Class X₂] [Mon_Class Y₂]
    (f : Mon_ClassHom X₁ Y₁) (g : Mon_ClassHom X₂ Y₂) :
     Mon_ClassHom (X₁ ⊗ X₂ : C) (Y₁ ⊗ Y₂) :=
  { hom := f.hom ⊗ g.hom
    one_hom := by
      dsimp
      slice_lhs 2 3 => rw [← tensor_comp, f.one_hom, g.one_hom]
    mul_hom := by
      dsimp
      slice_rhs 1 2 => rw [tensorμ_natural]
      slice_lhs 2 3 => rw [← tensor_comp, f.mul_hom, g.mul_hom, tensor_comp]
      simp only [Category.assoc] }

@[simps!]
def whiskerLeft (X : C) [Mon_Class X] {Y Z : C} [Mon_Class Y] [Mon_Class Z] (f : Mon_ClassHom Y Z) :
    Mon_ClassHom (X ⊗ Y : C) (X ⊗ Z) where
  hom := X ◁ f.hom
  one_hom := by simpa using (tensorHom (.id X) f).one_hom
  mul_hom := by simpa using (tensorHom (.id X) f).mul_hom

@[simps!]
def whiskerRight {X Y : C} [Mon_Class X] [Mon_Class Y]
    (f : Mon_ClassHom X Y) (Z : C) [Mon_Class Z] :
    Mon_ClassHom (X ⊗ Z : C) (Y ⊗ Z) where
  hom := f.hom ▷ Z
  one_hom := by simpa using (tensorHom f (.id Z)).one_hom
  mul_hom := by simpa using (tensorHom f (.id Z)).mul_hom

@[simps]
def associator (X Y Z : C) [Mon_Class X] [Mon_Class Y] [Mon_Class Z] :
    Mon_ClassIso ((X ⊗ Y) ⊗ Z : C) (X ⊗ (Y ⊗ Z)) where
  toIso := α_ X Y Z
  one_hom := one_associator
  mul_hom := mul_associator

@[simps]
def leftUnitor (X : C) [Mon_Class X] :
    Mon_ClassIso (𝟙_ C ⊗ X : C) X where
  toIso := λ_ X
  one_hom := one_leftUnitor
  mul_hom := mul_leftUnitor

@[simps]
def rightUnitor (X : C) [Mon_Class X] :
    Mon_ClassIso (X ⊗ 𝟙_ C : C) X where
  toIso := ρ_ X
  one_hom := one_rightUnitor
  mul_hom := mul_rightUnitor

theorem one_braiding (X Y : C) [Mon_Class X] [Mon_Class Y] : η ≫ (β_ X Y).hom = η := by
  simp only [instTensorObj_one, Category.assoc, BraidedCategory.braiding_naturality,
    braiding_tensorUnit_right, Iso.cancel_iso_inv_left]
  monoidal

end BraidedCategory

end Mon_Class

namespace Mon_Cat

section BraidedCategory

variable [BraidedCategory C]

@[simps!]
instance monMonoidalStruct : MonoidalCategoryStruct (Mon_Cat C) where
  tensorObj := fun M N ↦ Mon_Cat.mk (M.X ⊗ N.X)
  tensorHom := tensorHom
  whiskerRight := fun f Y => whiskerRight f Y.X
  whiskerLeft := fun X _ _ g => whiskerLeft X.X g
  tensorUnit := Mon_Cat.mk (𝟙_ C)
  associator := fun M N P ↦ Mon_Cat.mkIso <| associator M.X N.X P.X
  leftUnitor := fun M ↦ Mon_Cat.mkIso <| leftUnitor M.X
  rightUnitor := fun M ↦ Mon_Cat.mkIso <| rightUnitor M.X

instance monMonoidal : MonoidalCategory (Mon_Cat C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]

variable (C)

/-- The forgetful functor from `Mon_ C` to `C` is monoidal when `C` is monoidal. -/
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

@[simp] theorem forget_ε : LaxMonoidal.ε (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_η : OplaxMonoidal.η (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_μ (X Y : Mon_Cat C) : LaxMonoidal.μ (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl
@[simp] theorem forget_δ (X Y : Mon_Cat C) : OplaxMonoidal.δ (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl

end BraidedCategory

end Mon_Cat

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
  dsimp [tensorμ]
  simp only [tensor_μ, Category.assoc,
    BraidedCategory.braiding_naturality, BraidedCategory.braiding_tensor_right,
    BraidedCategory.braiding_tensor_left, comp_whiskerRight, whisker_assoc,
    MonoidalCategory.whiskerLeft_comp, pentagon_assoc, pentagon_inv_hom_hom_hom_inv_assoc,
    Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
  slice_lhs 3 4 =>
    -- We use symmetry here:
    rw [← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight, SymmetricCategory.symmetry]
  simp only [id_whiskerRight, MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.assoc,
    pentagon_inv_assoc, Iso.hom_inv_id_assoc]
  slice_lhs 1 2 =>
    rw [← associator_inv_naturality_left]
  slice_lhs 2 3 =>
    rw [CategoryTheory.Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 2 3 =>
    rw [← associator_naturality_right]
  slice_lhs 1 2 =>
    rw [← tensorHom_def]
  simp only [Category.assoc]

end Mon_Class

instance : SymmetricCategory (Mon_Cat C) where
  braiding := fun X Y =>
    Mon_Cat.mkIso' <| .mk (β_ X.X Y.X) (one_braiding X.X Y.X) (mul_braiding X.X Y.X)
  symmetry := fun X Y => by
    ext
    simp [← SymmetricCategory.braiding_swap_eq_inv_braiding]

end SymmetricCategory

/-!
Projects:
* Check that `Mon_ MonCat ≌ CommMonCat`, via the Eckmann-Hilton argument.
  (You'll have to hook up the cartesian monoidal structure on `MonCat` first,
  available in mathlib3#3463)
* More generally, check that `Mon_ (Mon_ C) ≌ CommMon_ C` when `C` is braided.
* Check that `Mon_ TopCat ≌ [bundled topological monoids]`.
* Check that `Mon_ AddCommGrp ≌ RingCat`.
  (We've already got `Mon_ (ModuleCat R) ≌ AlgebraCat R`,
  in `Mathlib.CategoryTheory.Monoidal.Internal.Module`.)
* Can you transport this monoidal structure to `RingCat` or `AlgebraCat R`?
  How does it compare to the "native" one?
* Show that when `F` is a lax braided functor `C ⥤ D`, the functor
  `map_Mon F : Mon_ C ⥤ Mon_ D` is lax monoidal.
-/
