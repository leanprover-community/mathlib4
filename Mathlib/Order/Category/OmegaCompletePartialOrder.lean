/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module order.category.omega_complete_partial_order
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.OmegaCompletePartialOrder
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom

/-!
# Category of types with a omega complete partial order

In this file, we bundle the class `omega_complete_partial_order` into a
concrete category and prove that continuous functions also form
a `omega_complete_partial_order`.

## Main definitions

 * `ωCPO`
   * an instance of `category` and `concrete_category`

 -/


open CategoryTheory

universe u v

/-- The category of types with a omega complete partial order. -/
def ωCPO : Type (u + 1) :=
  Bundled OmegaCompletePartialOrder
#align ωCPO ωCPO

namespace ωCPO

open OmegaCompletePartialOrder

instance : BundledHom @ContinuousHom
    where
  toFun := @ContinuousHom.Simps.apply
  id := @ContinuousHom.id
  comp := @ContinuousHom.comp
  hom_ext := @ContinuousHom.coe_inj

deriving instance LargeCategory, ConcreteCategory for ωCPO

instance : CoeSort ωCPO (Type _) :=
  Bundled.hasCoeToSort

/-- Construct a bundled ωCPO from the underlying type and typeclass. -/
def of (α : Type _) [OmegaCompletePartialOrder α] : ωCPO :=
  Bundled.of α
#align ωCPO.of ωCPO.of

@[simp]
theorem coe_of (α : Type _) [OmegaCompletePartialOrder α] : ↥(of α) = α :=
  rfl
#align ωCPO.coe_of ωCPO.coe_of

instance : Inhabited ωCPO :=
  ⟨of PUnit⟩

instance (α : ωCPO) : OmegaCompletePartialOrder α :=
  α.str

section

open CategoryTheory.Limits

namespace HasProducts

/-- The pi-type gives a cone for a product. -/
def product {J : Type v} (f : J → ωCPO.{v}) : Fan f :=
  Fan.mk (of (∀ j, f j)) fun j => ContinuousHom.ofMono (Pi.evalOrderHom j) fun c => rfl
#align ωCPO.has_products.product ωCPO.HasProducts.product

/-- The pi-type is a limit cone for the product. -/
def isProduct (J : Type v) (f : J → ωCPO) : IsLimit (product f)
    where
  lift s :=
    ⟨⟨fun t j => s.π.app ⟨j⟩ t, fun x y h j => (s.π.app ⟨j⟩).Monotone h⟩, fun x =>
      funext fun j => (s.π.app ⟨j⟩).Continuous x⟩
  uniq s m w := by
    ext t j
    change m t j = s.π.app ⟨j⟩ t
    rw [← w ⟨j⟩]
    rfl
  fac s j := by cases j; tidy
#align ωCPO.has_products.is_product ωCPO.HasProducts.isProduct

instance (J : Type v) (f : J → ωCPO.{v}) : HasProduct f :=
  HasLimit.mk ⟨_, isProduct _ f⟩

end HasProducts

instance omegaCompletePartialOrderEqualizer {α β : Type _} [OmegaCompletePartialOrder α]
    [OmegaCompletePartialOrder β] (f g : α →𝒄 β) :
    OmegaCompletePartialOrder { a : α // f a = g a } :=
  OmegaCompletePartialOrder.subtype _ fun c hc =>
    by
    rw [f.continuous, g.continuous]
    congr 1
    ext
    apply hc _ ⟨_, rfl⟩
#align ωCPO.omega_complete_partial_order_equalizer ωCPO.omegaCompletePartialOrderEqualizer

namespace HasEqualizers

/-- The equalizer inclusion function as a `continuous_hom`. -/
def equalizerι {α β : Type _} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
    (f g : α →𝒄 β) : { a : α // f a = g a } →𝒄 α :=
  ContinuousHom.ofMono (OrderHom.Subtype.val _) fun c => rfl
#align ωCPO.has_equalizers.equalizer_ι ωCPO.HasEqualizers.equalizerι

/-- A construction of the equalizer fork. -/
def equalizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : Fork f g :=
  @Fork.ofι _ _ _ _ _ _ (ωCPO.of { a // f a = g a }) (equalizerι f g)
    (ContinuousHom.ext _ _ fun x => x.2)
#align ωCPO.has_equalizers.equalizer ωCPO.HasEqualizers.equalizer

/-- The equalizer fork is a limit. -/
def isEqualizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : IsLimit (equalizer f g) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨{  toFun := fun x => ⟨s.ι x, by apply continuous_hom.congr_fun s.condition⟩
        monotone' := fun x y h => s.ι.Monotone h
        cont := fun x => Subtype.ext (s.ι.Continuous x) }, by ext; rfl, fun m hm =>
      by
      ext
      apply continuous_hom.congr_fun hm⟩
#align ωCPO.has_equalizers.is_equalizer ωCPO.HasEqualizers.isEqualizer

end HasEqualizers

instance : HasProducts.{v} ωCPO.{v} := fun J =>
  { HasLimit := fun F => hasLimitOfIso Discrete.natIsoFunctor.symm }

instance {X Y : ωCPO.{v}} (f g : X ⟶ Y) : HasLimit (parallelPair f g) :=
  HasLimit.mk ⟨_, HasEqualizers.isEqualizer f g⟩

instance : HasEqualizers ωCPO.{v} :=
  hasEqualizers_of_hasLimit_parallelPair _

instance : HasLimits ωCPO.{v} :=
  has_limits_of_hasEqualizers_and_products

end

end ωCPO

