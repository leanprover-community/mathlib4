/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Yury Kudryashov
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled

/-!
# Category instances for algebraic structures that use bundled homs.

Many algebraic structures in Lean initially used unbundled homs (e.g. a bare function between types,
along with an `IsMonoidHom` typeclass), but the general trend is towards using bundled homs.

This file provides a basic infrastructure to define concrete categories using bundled homs, and
define forgetful functors between them.
-/


universe u

namespace CategoryTheory

variable {c : Type u → Type u} (hom : ∀ ⦃α β : Type u⦄ (_ : c α) (_ : c β), Type u)

/-- Class for bundled homs. Note that the arguments order follows that of lemmas for `MonoidHom`.
This way we can use `⟨@MonoidHom.toFun, @MonoidHom.id ...⟩` in an instance. -/
structure BundledHom where
  /-- the underlying map of a bundled morphism -/
  toFun : ∀ {α β : Type u} (Iα : c α) (Iβ : c β), hom Iα Iβ → α → β
  /-- the identity as a bundled morphism -/
  id : ∀ {α : Type u} (I : c α), hom I I
  /-- composition of bundled morphisms -/
  comp : ∀ {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ), hom Iβ Iγ → hom Iα Iβ → hom Iα Iγ
  /-- a bundled morphism is determined by the underlying map -/
  hom_ext : ∀ {α β : Type u} (Iα : c α) (Iβ : c β), Function.Injective (toFun Iα Iβ) := by
    aesop_cat
  /-- compatibility with identities -/
  id_toFun : ∀ {α : Type u} (I : c α), toFun I I (id I) = _root_.id := by aesop_cat
  /-- compatibility with the composition -/
  comp_toFun :
    ∀ {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ) (f : hom Iα Iβ) (g : hom Iβ Iγ),
      toFun Iα Iγ (comp Iα Iβ Iγ g f) = toFun Iβ Iγ g ∘ toFun Iα Iβ f := by
    aesop_cat

attribute [class] BundledHom

attribute [simp] BundledHom.id_toFun BundledHom.comp_toFun

namespace BundledHom

variable [𝒞 : BundledHom hom]

set_option synthInstance.checkSynthOrder false in
/-- Every `@BundledHom c _` defines a category with objects in `Bundled c`.

This instance generates the type-class problem `BundledHom ?m`.
Currently that is not a problem, as there are almost no instances of `BundledHom`.
-/
instance category : Category (Bundled c) where
  Hom := fun X Y => hom X.str Y.str
  id := fun X => BundledHom.id 𝒞 (α := X) X.str
  comp := fun {X Y Z} f g => BundledHom.comp 𝒞 (α := X) (β := Y) (γ := Z) X.str Y.str Z.str g f
  comp_id _ := by apply 𝒞.hom_ext; simp
  assoc _ _ _ := by apply 𝒞.hom_ext; aesop_cat
  id_comp _ := by apply 𝒞.hom_ext; simp

/-- A category given by `BundledHom` is a concrete category. -/
instance hasForget : HasForget.{u} (Bundled c) where
  forget :=
    { obj := fun X => X
      map := fun {X Y} f => 𝒞.toFun X.str Y.str f
      map_id := fun X => 𝒞.id_toFun X.str
      map_comp := fun f g => by erw [𝒞.comp_toFun]; rfl }
  forget_faithful := { map_injective := by (intros; apply 𝒞.hom_ext) }

/-- This unification hint helps `rw` to figure out how to apply statements about abstract
concrete categories to specific concrete categories. Crucially, it fires also at `reducible`
levels so `rw` can use it (and we don't have to use `erw`). -/
unif_hint (C : Bundled c) where
  ⊢ (CategoryTheory.forget (Bundled c)).obj C =?= Bundled.α C

variable {hom}

attribute [local instance] HasForget.instFunLike

/-- A version of `HasForget₂.mk'` for categories defined using `@BundledHom`. -/
def mkHasForget₂ {d : Type u → Type u} {hom_d : ∀ ⦃α β : Type u⦄ (_ : d α) (_ : d β), Type u}
    [BundledHom hom_d] (obj : ∀ ⦃α⦄, c α → d α)
    (map : ∀ {X Y : Bundled c}, (X ⟶ Y) → (Bundled.map @obj X ⟶ (Bundled.map @obj Y)))
    (h_map : ∀ {X Y : Bundled c} (f : X ⟶ Y), ⇑(map f) = ⇑f) :
    HasForget₂ (Bundled c) (Bundled d) :=
  HasForget₂.mk' (Bundled.map @obj) (fun _ => rfl) map (by
    intros X Y f
    rw [heq_eq_eq, forget_map_eq_coe, forget_map_eq_coe, h_map f])

variable {d : Type u → Type u}
variable (hom)

section

/-- The `hom` corresponding to first forgetting along `F`, then taking the `hom` associated to `c`.

For typical usage, see the construction of `CommMonCat` from `MonCat`.
-/
abbrev MapHom (F : ∀ {α}, d α → c α) : ∀ ⦃α β : Type u⦄ (_ : d α) (_ : d β), Type u :=
  fun _ _ iα iβ => hom (F iα) (F iβ)

end

/-- Construct the `CategoryTheory.BundledHom` induced by a map between type classes.
This is useful for building categories such as `CommMonCat` from `MonCat`.
-/
def map (F : ∀ {α}, d α → c α) : BundledHom (MapHom hom @F) where
  toFun _ _ {iα} {iβ} f := 𝒞.toFun (F iα) (F iβ) f
  id _ {iα} := 𝒞.id (F iα)
  comp := @fun _ _ _ iα iβ iγ f g => 𝒞.comp (F iα) (F iβ) (F iγ) f g
  hom_ext := @fun _ _ iα iβ _ _ h => 𝒞.hom_ext (F iα) (F iβ) h

section

/-- We use the empty `ParentProjection` class to label functions like `CommMonoid.toMonoid`,
which we would like to use to automatically construct `BundledHom` instances from.

Once we've set up `MonCat` as the category of bundled monoids,
this allows us to set up `CommMonCat` by defining an instance
```instance : ParentProjection (CommMonoid.toMonoid) := ⟨⟩```
-/
class ParentProjection (F : ∀ {α}, d α → c α) : Prop

end

-- The `ParentProjection` typeclass is just a marker, so won't be used.
@[nolint unusedArguments]
instance bundledHomOfParentProjection (F : ∀ {α}, d α → c α) [ParentProjection @F] :
    BundledHom (MapHom hom @F) :=
  map hom @F

instance forget₂ (F : ∀ {α}, d α → c α) [ParentProjection @F] :
    HasForget₂ (Bundled d) (Bundled c) where
  forget₂ :=
    { obj := fun X => ⟨X, F X.2⟩
      map := @fun _ _ f => f }

instance forget₂_full (F : ∀ {α}, d α → c α) [ParentProjection @F] :
    Functor.Full (CategoryTheory.forget₂ (Bundled d) (Bundled c)) where
  map_surjective f := ⟨f, rfl⟩

end BundledHom

end CategoryTheory
