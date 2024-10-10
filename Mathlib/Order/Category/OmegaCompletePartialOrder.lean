/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom

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
def ωCPO : Type (u + 1) :=
  Bundled OmegaCompletePartialOrder

namespace ωCPO

open OmegaCompletePartialOrder

instance : BundledHom @ContinuousHom where
  toFun := @ContinuousHom.Simps.apply
  id := @ContinuousHom.id
  comp := @ContinuousHom.comp
  hom_ext := @ContinuousHom.coe_inj

-- Porting note: `deriving instance ConcreteCategory` didn't work.
deriving instance LargeCategory for ωCPO
instance : ConcreteCategory ωCPO := by unfold ωCPO; infer_instance

instance : CoeSort ωCPO Type* :=
  Bundled.coeSort

/-- Construct a bundled ωCPO from the underlying type and typeclass. -/
def of (α : Type*) [OmegaCompletePartialOrder α] : ωCPO :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type*) [OmegaCompletePartialOrder α] : ↥(of α) = α :=
  rfl

instance : Inhabited ωCPO :=
  ⟨of PUnit⟩

instance (α : ωCPO) : OmegaCompletePartialOrder α :=
  α.str

section

open CategoryTheory.Limits

namespace HasProducts

/-- The pi-type gives a cone for a product. -/
def product {J : Type v} (f : J → ωCPO.{v}) : Fan f :=
  Fan.mk (of (∀ j, f j)) fun j => .mk (Pi.evalOrderHom j) fun _ => rfl

/-- The pi-type is a limit cone for the product. -/
def isProduct (J : Type v) (f : J → ωCPO) : IsLimit (product f) where
  lift s :=
    -- Porting note: Original proof didn't have `.toFun`
    ⟨⟨fun t j => (s.π.app ⟨j⟩).toFun t, fun x y h j => (s.π.app ⟨j⟩).monotone h⟩,
      fun x => funext fun j => (s.π.app ⟨j⟩).continuous x⟩
  uniq s m w := by
    ext t; funext j -- Porting note: Originally `ext t j`
    change m.toFun t j = (s.π.app ⟨j⟩).toFun t
    rw [← w ⟨j⟩]
    rfl
  fac s j := rfl

instance (J : Type v) (f : J → ωCPO.{v}) : HasProduct f :=
  HasLimit.mk ⟨_, isProduct _ f⟩

end HasProducts

instance omegaCompletePartialOrderEqualizer {α β : Type*} [OmegaCompletePartialOrder α]
    [OmegaCompletePartialOrder β] (f g : α →𝒄 β) :
    OmegaCompletePartialOrder { a : α // f a = g a } :=
  OmegaCompletePartialOrder.subtype _ fun c hc => by
    rw [f.continuous, g.continuous]
    congr 1
    apply OrderHom.ext; funext x -- Porting note: Originally `ext`
    apply hc _ ⟨_, rfl⟩

namespace HasEqualizers

/-- The equalizer inclusion function as a `ContinuousHom`. -/
def equalizerι {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
    (f g : α →𝒄 β) : { a : α // f a = g a } →𝒄 α :=
  .mk (OrderHom.Subtype.val _) fun _ => rfl

/-- A construction of the equalizer fork. -/
-- Porting note: Changed `{ a // f a = g a }` to `{ a // f.toFun a = g.toFun a }`
def equalizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : Fork f g :=
  Fork.ofι (P := ωCPO.of { a // f.toFun a = g.toFun a }) (equalizerι f g)
    (ContinuousHom.ext _ _ fun x => x.2)

/-- The equalizer fork is a limit. -/
def isEqualizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : IsLimit (equalizer f g) :=
  Fork.IsLimit.mk' _ fun s =>
    -- Porting note: Changed `s.ι x` to `s.ι.toFun x`
    ⟨{  toFun := fun x => ⟨s.ι.toFun x, by apply ContinuousHom.congr_fun s.condition⟩
        monotone' := fun x y h => s.ι.monotone h
        map_ωSup' := fun x => Subtype.ext (s.ι.continuous x)
      }, by ext; rfl, fun hm => by
      apply ContinuousHom.ext _ _ fun x => Subtype.ext ?_ -- Porting note: Originally `ext`
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
