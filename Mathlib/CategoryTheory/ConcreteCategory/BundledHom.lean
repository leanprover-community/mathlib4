/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yury Kudryashov

! This file was ported from Lean 3 source module category_theory.concrete_category.bundled_hom
! leanprover-community/mathlib commit 77ca1ed347337ecbafa9d9f4a55e330e44e9f9f8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled

/-!
# Category instances for algebraic structures that use bundled homs.

Many algebraic structures in Lean initially used unbundled homs (e.g. a bare function between types,
along with an `is_monoid_hom` typeclass), but the general trend is towards using bundled homs.

This file provides a basic infrastructure to define concrete categories using bundled homs, and
define forgetful functors between them.
-/


universe u

namespace CategoryTheory

variable {c : Type u → Type u} (hom : ∀ ⦃α β : Type u⦄ (_ : c α) (_ : c β), Type u)

/-- Class for bundled homs. Note that the arguments order follows that of lemmas for `monoid_hom`.
This way we can use `⟨@monoid_hom.to_fun, @monoid_hom.id ...⟩` in an instance. -/
structure BundledHom where
  toFun : ∀ {α β : Type u} (Iα : c α) (Iβ : c β), hom Iα Iβ → α → β
  id : ∀ {α : Type u} (I : c α), hom I I
  comp : ∀ {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ), hom Iβ Iγ → hom Iα Iβ → hom Iα Iγ
  hom_ext : ∀ {α β : Type u} (Iα : c α) (Iβ : c β), Function.Injective (toFun Iα Iβ) := by
   aesop_cat
  id_toFun : ∀ {α : Type u} (I : c α), toFun I I (id I) = _root_.id := by aesop_cat
  comp_toFun :
    ∀ {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ) (f : hom Iα Iβ) (g : hom Iβ Iγ),
      toFun Iα Iγ (comp Iα Iβ Iγ g f) = toFun Iβ Iγ g ∘ toFun Iα Iβ f := by
   aesop_cat
#align category_theory.bundled_hom CategoryTheory.BundledHom

attribute [class] BundledHom

attribute [simp] BundledHom.id_toFun BundledHom.comp_toFun

namespace BundledHom

variable [𝒞 : BundledHom hom]

-- porting note: include not needed
-- include 𝒞

/-- Every `@bundled_hom c _` defines a category with objects in `bundled c`.

This instance generates the type-class problem `bundled_hom ?m` (which is why this is marked as
`[nolint]`). Currently that is not a problem, as there are almost no instances of `bundled_hom`. -/
@[nolint dangerousInstance]
instance category : Category (Bundled c) := by
  refine' { Hom := fun X Y => @hom X Y X.str Y.str
            id := fun X => @BundledHom.id c hom 𝒞 X X.str
            comp := @fun X Y Z f g => @BundledHom.comp c hom 𝒞 X Y Z X.str Y.str Z.str g f
            comp_id := _
            id_comp := _
            assoc := _ } <;> intros <;> apply 𝒞.hom_ext <;>
    aesop_cat
#align category_theory.bundled_hom.category CategoryTheory.BundledHom.category

/-- A category given by `bundled_hom` is a concrete category.

This instance generates the type-class problem `bundled_hom ?m` (which is why this is marked as
`[nolint]`). Currently that is not a problem, as there are almost no instances of `bundled_hom`. -/
@[nolint dangerousInstance]
instance concreteCategory : ConcreteCategory.{u} (Bundled c)
    where
  Forget :=
    { obj := fun X => X
      map := @fun X Y f => 𝒞.toFun X.str Y.str f
      map_id := fun X => 𝒞.id_toFun X.str
      map_comp := by (intros; aesop_cat;erw [𝒞.comp_toFun]; rfl) }
  forget_faithful := { map_injective := by (intros; apply 𝒞.hom_ext }
#align category_theory.bundled_hom.concrete_category CategoryTheory.BundledHom.concreteCategory

variable {hom}

attribute [local instance] ConcreteCategory.hasCoeToFun

/-- A version of `has_forget₂.mk'` for categories defined using `@bundled_hom`. -/
def mkHasForget₂ {d : Type u → Type u} {hom_d : ∀ ⦃α β : Type u⦄ (Iα : d α) (Iβ : d β), Type u}
    [BundledHom hom_d] (obj : ∀ ⦃α⦄, c α → d α)
    (map : ∀ {X Y : Bundled c}, (X ⟶ Y) → ((Bundled.map obj X) ⟶ (Bundled.map obj Y)))
    (h_map : ∀ {X Y : Bundled c} (f : X ⟶ Y), (map f) = f) :
    HasForget₂ (Bundled c) (Bundled d) :=
  HasForget₂.mk' (Bundled.map @obj) (fun _ => rfl) (@map)
    (by intros <;> apply hEq_of_eq <;> apply h_map)
#align category_theory.bundled_hom.mk_has_forget₂ CategoryTheory.BundledHom.mkHasForget₂

variable {d : Type u → Type u}

variable (hom)

section

-- porting note: commented out
-- omit 𝒞

/-- The `hom` corresponding to first forgetting along `F`, then taking the `hom` associated to `c`.

For typical usage, see the construction of `CommMon` from `Mon`.
-/
@[reducible]
def MapHom (F : ∀ {α}, d α → c α) : ∀ ⦃α β : Type u⦄ (_ : d α) (_ : d β), Type u :=
  fun _ _ iα iβ => hom (F iα) (F iβ)
#align category_theory.bundled_hom.map_hom CategoryTheory.BundledHom.MapHom

end

/-- Construct the `bundled_hom` induced by a map between type classes.
This is useful for building categories such as `CommMon` from `Mon`.
-/
def map (F : ∀ {α}, d α → c α) : BundledHom (MapHom hom @F)
    where
  toFun α β {iα} {iβ} f := 𝒞.toFun (F iα) (F iβ) f
  id α {iα} := 𝒞.id (F iα)
  comp := @fun α β γ iα iβ iγ f g => 𝒞.comp (F iα) (F iβ) (F iγ) f g
  hom_ext := @fun α β iα iβ f g h => 𝒞.hom_ext (F iα) (F iβ) h
#align category_theory.bundled_hom.map CategoryTheory.BundledHom.map

section

-- porting note: commented out
--omit 𝒞

/-- We use the empty `parent_projection` class to label functions like `comm_monoid.to_monoid`,
which we would like to use to automatically construct `bundled_hom` instances from.

Once we've set up `Mon` as the category of bundled monoids,
this allows us to set up `CommMon` by defining an instance
```instance : parent_projection (comm_monoid.to_monoid) := ⟨⟩```
-/
class ParentProjection (F : ∀ {α}, d α → c α)
#align category_theory.bundled_hom.parent_projection CategoryTheory.BundledHom.ParentProjection

end

-- The `parent_projection` typeclass is just a marker, so won't be used.
@[nolint unusedArguments]
instance bundledHomOfParentProjection (F : ∀ {α}, d α → c α) [ParentProjection @F] :
    BundledHom (MapHom hom @F) :=
  map hom @F
#align category_theory.bundled_hom.bundled_hom_of_parent_projection CategoryTheory.BundledHom.bundledHomOfParentProjection

instance forget₂ (F : ∀ {α}, d α → c α) [ParentProjection @F] : HasForget₂ (Bundled d) (Bundled c)
    where forget₂ :=
    { obj := fun X => ⟨X, F X.2⟩
      map := @fun X Y f => f }
#align category_theory.bundled_hom.forget₂ CategoryTheory.BundledHom.forget₂

instance forget₂Full (F : ∀ {α}, d α → c α) [ParentProjection @F] :
    Full (CategoryTheory.forget₂ (Bundled d) (Bundled c)) where preimage X Y {f} := f
#align category_theory.bundled_hom.forget₂_full CategoryTheory.BundledHom.forget₂Full

end BundledHom

end CategoryTheory
