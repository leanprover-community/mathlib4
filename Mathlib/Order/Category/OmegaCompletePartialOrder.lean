/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.ConcreteCategory.Basic

/-!
# Category of types with an omega complete partial order

In this file, we bundle the class `OmegaCompletePartialOrder` into a
concrete category and prove that continuous functions also form
an `OmegaCompletePartialOrder`.

## Main definitions

 * `ωCPO`
   * an instance of `Category` and `ConcreteCategory`

-/


open CategoryTheory

universe u v


/-- The category of types with an omega complete partial order. -/
structure ωCPO : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [str : OmegaCompletePartialOrder carrier]

attribute [instance] ωCPO.str

namespace ωCPO

open OmegaCompletePartialOrder

instance : CoeSort ωCPO Type* :=
  ⟨carrier⟩

/-- Construct a bundled ωCPO from the underlying type and typeclass. -/
abbrev of (α : Type*) [OmegaCompletePartialOrder α] : ωCPO where
  carrier := α

theorem coe_of (α : Type*) [OmegaCompletePartialOrder α] : ↥(of α) = α :=
  rfl

instance : LargeCategory.{u} ωCPO where
  Hom X Y := ContinuousHom X Y
  id X := ContinuousHom.id
  comp f g := g.comp f

instance : ConcreteCategory ωCPO (ContinuousHom · ·) where
  hom f := f
  ofHom f := f

instance : Inhabited ωCPO :=
  ⟨of PUnit⟩

section

open CategoryTheory.Limits

namespace HasProducts

/-- The pi-type gives a cone for a product. -/
def product {J : Type v} (f : J → ωCPO.{v}) : Fan f :=
  Fan.mk (of (∀ j, f j)) fun j => .mk (Pi.evalOrderHom j) fun _ => rfl

/-- The pi-type is a limit cone for the product. -/
def isProduct (J : Type v) (f : J → ωCPO) : IsLimit (product f) where
  lift s :=
    ⟨⟨fun t j => (s.π.app ⟨j⟩) t, fun _ _ h j => (s.π.app ⟨j⟩).monotone h⟩,
      fun x => funext fun j => (s.π.app ⟨j⟩).continuous x⟩
  uniq s m w := by
    ext t; funext j -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext t j`
    change m t j = (s.π.app ⟨j⟩) t
    rw [← w ⟨j⟩]
    rfl
  fac _ _ := rfl

instance (J : Type v) (f : J → ωCPO.{v}) : HasProduct f :=
  HasLimit.mk ⟨_, isProduct _ f⟩

end HasProducts

instance omegaCompletePartialOrderEqualizer {α β : Type*} [OmegaCompletePartialOrder α]
    [OmegaCompletePartialOrder β] (f g : α →𝒄 β) :
    OmegaCompletePartialOrder { a : α // f a = g a } :=
  OmegaCompletePartialOrder.subtype _ fun c hc => by
    rw [f.continuous, g.continuous]
    congr 1
    apply OrderHom.ext; funext x -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
    apply hc _ ⟨_, rfl⟩

namespace HasEqualizers

/-- The equalizer inclusion function as a `ContinuousHom`. -/
def equalizerι {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
    (f g : α →𝒄 β) : { a : α // f a = g a } →𝒄 α :=
  .mk (OrderHom.Subtype.val _) fun _ => rfl

/-- A construction of the equalizer fork. -/
def equalizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : Fork f g :=
  Fork.ofι (P := ωCPO.of { a // f a = g a }) (equalizerι f g)
    (ContinuousHom.ext _ _ fun x => x.2)

/-- The equalizer fork is a limit. -/
def isEqualizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : IsLimit (equalizer f g) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨{  toFun := fun x => ⟨s.ι x, by apply ContinuousHom.congr_fun s.condition⟩
        monotone' := fun _ _ h => s.ι.monotone h
        map_ωSup' := fun x => Subtype.ext (s.ι.continuous x)
      }, by ext; rfl, fun hm => by
      ext x : 2; apply Subtype.ext ?_ -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
      apply ContinuousHom.congr_fun hm⟩

end HasEqualizers

instance : HasProducts.{v} ωCPO.{v} :=
  fun _ => { has_limit := fun _ => hasLimitOfIso Discrete.natIsoFunctor.symm }

instance {X Y : ωCPO.{v}} (f g : X ⟶ Y) : HasLimit (parallelPair f g) :=
  HasLimit.mk ⟨_, HasEqualizers.isEqualizer f g⟩

instance : HasEqualizers ωCPO.{v} :=
  hasEqualizers_of_hasLimit_parallelPair _

instance : HasLimits ωCPO.{v} :=
  has_limits_of_hasEqualizers_and_products

end

end ωCPO
