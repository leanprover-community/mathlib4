/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Nailin Guan
-/
import Mathlib.Topology.Algebra.Equicontinuity
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.UniformSpace.Ascoli

/-!

# Continuous Monoid Homs

This file defines the space of continuous homomorphisms between two topological groups.

## Main definitions

* `ContinuousMonoidHom A B`: The continuous homomorphisms `A →* B`.
* `ContinuousAddMonoidHom A B`: The continuous additive homomorphisms `A →+ B`.
-/

section

open Function Topology
open scoped Pointwise

variable (F A B C D E : Type*) [Monoid A] [Monoid B] [Monoid C] [Monoid D] [CommGroup E]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [TopologicalSpace E] [TopologicalGroup E]

/-- The type of continuous additive monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : ContinuousAddMonoidHom A B)`,
you should parametrize
over `(F : Type*) [FunLike F A B] [ContinuousMapClass F A B] [AddMonoidHomClass F A B] (f : F)`.

When you extend this structure,
make sure to extend `ContinuousMapClass` and/or `AddMonoidHomClass`, if needed. -/
structure ContinuousAddMonoidHom (A B : Type*) [AddMonoid A] [AddMonoid B] [TopologicalSpace A]
  [TopologicalSpace B] extends A →+ B, C(A, B)

/-- The type of continuous monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : ContinuousMonoidHom A B)`,
you should parametrize
over `(F : Type*) [FunLike F A B] [ContinuousMapClass F A B] [MonoidHomClass F A B] (f : F)`.

When you extend this structure,
make sure to extend `ContinuousMapClass` and/or `MonoidHomClass`, if needed. -/
@[to_additive "The type of continuous additive monoid homomorphisms from `A` to `B`."]
structure ContinuousMonoidHom extends A →* B, C(A, B)

section

/-- `ContinuousAddMonoidHomClass F A B` states that `F` is a type of continuous additive monoid
homomorphisms.

Deprecated and changed from a `class` to a `structure`.
Use `[AddMonoidHomClass F A B] [ContinuousMapClass F A B]` instead. -/
structure ContinuousAddMonoidHomClass (A B : outParam Type*) [AddMonoid A] [AddMonoid B]
    [TopologicalSpace A] [TopologicalSpace B] [FunLike F A B]
    extends AddMonoidHomClass F A B, ContinuousMapClass F A B : Prop

/-- `ContinuousMonoidHomClass F A B` states that `F` is a type of continuous monoid
homomorphisms.

Deprecated and changed from a `class` to a `structure`.
Use `[MonoidHomClass F A B] [ContinuousMapClass F A B]` instead. -/
@[to_additive (attr := deprecated "Use `[MonoidHomClass F A B] [ContinuousMapClass F A B]` instead."
  (since := "2024-10-08"))]
structure ContinuousMonoidHomClass (A B : outParam Type*) [Monoid A] [Monoid B]
    [TopologicalSpace A] [TopologicalSpace B] [FunLike F A B]
    extends MonoidHomClass F A B, ContinuousMapClass F A B : Prop

end

/-- Reinterpret a `ContinuousMonoidHom` as a `MonoidHom`. -/
add_decl_doc ContinuousMonoidHom.toMonoidHom

/-- Reinterpret a `ContinuousAddMonoidHom` as an `AddMonoidHom`. -/
add_decl_doc ContinuousAddMonoidHom.toAddMonoidHom

/-- Reinterpret a `ContinuousMonoidHom` as a `ContinuousMap`. -/
add_decl_doc ContinuousMonoidHom.toContinuousMap

/-- Reinterpret a `ContinuousAddMonoidHom` as a `ContinuousMap`. -/
add_decl_doc ContinuousAddMonoidHom.toContinuousMap

namespace ContinuousMonoidHom

/-- The type of continuous monoid homomorphisms from `A` to `B`.-/
infixr:25 " →ₜ+ " => ContinuousAddMonoidHom
/-- The type of continuous monoid homomorphisms from `A` to `B`.-/
infixr:25 " →ₜ* " => ContinuousMonoidHom

variable {A B C D E}

@[to_additive]
instance instFunLike : FunLike ((A →ₜ* B)) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨ _ , _ ⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨ _ , _ ⟩, _⟩, _⟩ := g
    congr

@[to_additive]
instance instMonoidHomClass : MonoidHomClass ((A →ₜ* B)) A B where
  map_mul f := f.map_mul'
  map_one f := f.map_one'

@[to_additive]
instance instContinuousMapClass : ContinuousMapClass ((A →ₜ* B)) A B where
  map_continuous f := f.continuous_toFun

@[to_additive (attr := simp)]
lemma coe_toMonoidHom (f : (A →ₜ* B)) : f.toMonoidHom = f := rfl

@[to_additive (attr := simp)]
lemma coe_toContinuousMap (f : (A →ₜ* B)) : f.toContinuousMap = f := rfl

section

variable {A B : Type*} [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B]
  {F : Type*} [FunLike F A B]

/-- Turn an element of a type `F` satisfying `MonoidHomClass F A B` and `ContinuousMapClass F A B`
into a`ContinuousMonoidHom`. This is declared as the default coercion from `F` to
`(A →ₜ* B)`. -/
@[to_additive (attr := coe) "Turn an element of a type `F` satisfying
`AddMonoidHomClass F A B` and `ContinuousMapClass F A B` into a`ContinuousAddMonoidHom`.
This is declared as the default coercion from `F` to `ContinuousAddMonoidHom A B`."]
def toContinuousMonoidHom [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F) :
    (A →ₜ* B) :=
  { MonoidHomClass.toMonoidHom f with }

/-- Any type satisfying `MonoidHomClass` and `ContinuousMapClass` can be cast into
`ContinuousMnoidHom` via `ContinuousMonoidHom.toContinuousMonoidHom`. -/
@[to_additive "Any type satisfying `AddMonoidHomClass` and `ContinuousMapClass` can be cast into
`ContinuousAddMonoidHom` via `ContinuousAddMonoidHom.toContinuousAddMonoidHom`."]
instance [MonoidHomClass F A B] [ContinuousMapClass F A B] : CoeOut F ((A →ₜ* B)) :=
  ⟨ContinuousMonoidHom.toContinuousMonoidHom⟩

@[to_additive (attr := simp)]
lemma coe_coe [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F) :
    ⇑(f : (A →ₜ* B)) = f := rfl

@[to_additive (attr := simp, norm_cast)]
lemma toMonoidHom_toContinuousMonoidHom [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F) :
    ((f : (A →ₜ* B)) : A →* B) = f := rfl

@[to_additive (attr := simp, norm_cast)]
lemma toContinuousMap_toContinuousMonoidHom [MonoidHomClass F A B] [ContinuousMapClass F A B]
    (f : F) : ((f : (A →ₜ* B)) : C(A, B)) = f := rfl

end

@[to_additive (attr := ext)]
theorem ext {f g : (A →ₜ* B)} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[to_additive]
theorem toContinuousMap_injective : Injective (toContinuousMap : _ → C(A, B)) := fun f g h =>
  ext <| by convert DFunLike.ext_iff.1 h

@[deprecated (since := "2024-10-08")] protected alias mk' := mk

@[deprecated (since := "2024-10-08")]
protected alias _root_.ContinuousAddMonoidHom.mk' := ContinuousAddMonoidHom.mk

set_option linter.existingAttributeWarning false in
attribute [to_additive existing] ContinuousMonoidHom.mk'

/-- Composition of two continuous homomorphisms. -/
@[to_additive (attr := simps!) "Composition of two continuous homomorphisms."]
def comp (g : B →ₜ* C) (f : (A →ₜ* B)) : A →ₜ* C :=
  ⟨g.toMonoidHom.comp f.toMonoidHom, (map_continuous g).comp (map_continuous f)⟩

/-- Product of two continuous homomorphisms on the same space. -/
@[to_additive (attr := simps!) prod "Product of two continuous homomorphisms on the same space."]
def prod (f : (A →ₜ* B)) (g : A →ₜ* C) : A →ₜ* (B × C) :=
  ⟨f.toMonoidHom.prod g.toMonoidHom, f.continuous_toFun.prod_mk g.continuous_toFun⟩

/-- Product of two continuous homomorphisms on different spaces. -/
@[to_additive (attr := simps!) prodMap
  "Product of two continuous homomorphisms on different spaces."]
def prodMap (f : A →ₜ* C) (g : B →ₜ* D) :
    (A × B) →ₜ* (C × D) :=
  ⟨f.toMonoidHom.prodMap g.toMonoidHom, f.continuous_toFun.prodMap g.continuous_toFun⟩

@[deprecated (since := "2024-10-05")] alias prod_map := prodMap
@[deprecated (since := "2024-10-05")]
alias _root_.ContinuousAddMonoidHom.sum_map := ContinuousAddMonoidHom.prodMap

set_option linter.existingAttributeWarning false in
attribute [to_additive existing] prod_map

variable (A B C D E)

/-- The trivial continuous homomorphism. -/
@[to_additive (attr := simps!) "The trivial continuous homomorphism."]
def one : (A →ₜ* B) :=
  ⟨1, continuous_const⟩

@[to_additive]
instance : Inhabited ((A →ₜ* B)) :=
  ⟨one A B⟩

/-- The identity continuous homomorphism. -/
@[to_additive (attr := simps!) "The identity continuous homomorphism."]
def id : A →ₜ* A := ⟨.id A, continuous_id⟩

/-- The continuous homomorphism given by projection onto the first factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by projection onto the first factor."]
def fst : (A × B) →ₜ* A := ⟨MonoidHom.fst A B, continuous_fst⟩

/-- The continuous homomorphism given by projection onto the second factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by projection onto the second factor."]
def snd : (A × B) →ₜ* B :=
  ⟨MonoidHom.snd A B, continuous_snd⟩

/-- The continuous homomorphism given by inclusion of the first factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by inclusion of the first factor."]
def inl : A →ₜ* (A × B) :=
  prod (id A) (one A B)

/-- The continuous homomorphism given by inclusion of the second factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by inclusion of the second factor."]
def inr : B →ₜ* (A × B) :=
  prod (one B A) (id B)

/-- The continuous homomorphism given by the diagonal embedding. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by the diagonal embedding."]
def diag : A →ₜ* (A × A) := prod (id A) (id A)

/-- The continuous homomorphism given by swapping components. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by swapping components."]
def swap : (A × B) →ₜ* (B × A) := prod (snd A B) (fst A B)

/-- The continuous homomorphism given by multiplication. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by addition."]
def mul : (E × E) →ₜ* E := ⟨mulMonoidHom, continuous_mul⟩

/-- The continuous homomorphism given by inversion. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by negation."]
def inv : E →ₜ* E := ⟨invMonoidHom, continuous_inv⟩

variable {A B C D E}

/-- Coproduct of two continuous homomorphisms to the same space. -/
@[to_additive (attr := simps!) "Coproduct of two continuous homomorphisms to the same space."]
def coprod (f : A →ₜ* E) (g : B →ₜ* E) :
    (A × B) →ₜ* E :=
  (mul E).comp (f.prodMap g)

@[to_additive]
instance : CommGroup (A →ₜ* E) where
  mul f g := (mul E).comp (f.prod g)
  mul_comm f g := ext fun x => mul_comm (f x) (g x)
  mul_assoc f g h := ext fun x => mul_assoc (f x) (g x) (h x)
  one := one A E
  one_mul f := ext fun x => one_mul (f x)
  mul_one f := ext fun x => mul_one (f x)
  inv f := (inv E).comp f
  inv_mul_cancel f := ext fun x => inv_mul_cancel (f x)

@[to_additive]
instance : TopologicalSpace ((A →ₜ* B)) :=
  TopologicalSpace.induced toContinuousMap ContinuousMap.compactOpen

variable (A B C D E)

@[to_additive]
theorem isInducing_toContinuousMap :
    IsInducing (toContinuousMap : (A →ₜ* B) → C(A, B)) := ⟨rfl⟩

@[deprecated (since := "2024-10-28")] alias inducing_toContinuousMap := isInducing_toContinuousMap

@[to_additive]
theorem isEmbedding_toContinuousMap :
    IsEmbedding (toContinuousMap : (A →ₜ* B) → C(A, B)) :=
  ⟨isInducing_toContinuousMap A B, toContinuousMap_injective⟩

@[deprecated (since := "2024-10-26")]
alias embedding_toContinuousMap := isEmbedding_toContinuousMap

@[to_additive]
instance instContinuousEvalConst : ContinuousEvalConst ((A →ₜ* B)) A B :=
  .of_continuous_forget (isInducing_toContinuousMap A B).continuous

@[to_additive]
instance instContinuousEval [LocallyCompactPair A B] :
    ContinuousEval ((A →ₜ* B)) A B :=
  .of_continuous_forget (isInducing_toContinuousMap A B).continuous

@[to_additive]
lemma range_toContinuousMap :
    Set.range (toContinuousMap : (A →ₜ* B) → C(A, B)) =
      {f : C(A, B) | f 1 = 1 ∧ ∀ x y, f (x * y) = f x * f y} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun f ↦ ⟨map_one f, map_mul f⟩) ?_
  rintro f ⟨h1, hmul⟩
  exact ⟨{ f with map_one' := h1, map_mul' := hmul }, rfl⟩

@[to_additive]
theorem isClosedEmbedding_toContinuousMap [ContinuousMul B] [T2Space B] :
    IsClosedEmbedding (toContinuousMap : (A →ₜ* B) → C(A, B)) where
  toIsEmbedding := isEmbedding_toContinuousMap A B
  isClosed_range := by
    simp only [range_toContinuousMap, Set.setOf_and, Set.setOf_forall]
    refine .inter (isClosed_singleton.preimage (continuous_eval_const 1)) <|
      isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ ?_
    exact isClosed_eq (continuous_eval_const (x * y)) <|
      .mul (continuous_eval_const x) (continuous_eval_const y)

@[deprecated (since := "2024-10-20")]
alias closedEmbedding_toContinuousMap := isClosedEmbedding_toContinuousMap

variable {A B C D E}

@[to_additive]
instance [T2Space B] : T2Space ((A →ₜ* B)) :=
  (isEmbedding_toContinuousMap A B).t2Space

@[to_additive]
instance : TopologicalGroup (A →ₜ* E) :=
  let hi := isInducing_toContinuousMap A E
  let hc := hi.continuous
  { continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (Continuous.prodMap hc hc))
    continuous_inv := hi.continuous_iff.mpr (continuous_inv.comp hc) }

@[to_additive]
theorem continuous_of_continuous_uncurry {A : Type*} [TopologicalSpace A]
    (f : A → B →ₜ* C) (h : Continuous (Function.uncurry fun x y => f x y)) :
    Continuous f :=
  (isInducing_toContinuousMap _ _).continuous_iff.mpr
    (ContinuousMap.continuous_of_continuous_uncurry _ h)

@[to_additive]
theorem continuous_comp [LocallyCompactSpace B] :
    Continuous fun f : (A →ₜ* B) × (B →ₜ* C) => f.2.comp f.1 :=
  (isInducing_toContinuousMap A C).continuous_iff.2 <|
    ContinuousMap.continuous_comp'.comp
      ((isInducing_toContinuousMap A B).prodMap (isInducing_toContinuousMap B C)).continuous

@[to_additive]
theorem continuous_comp_left (f : (A →ₜ* B)) :
    Continuous fun g : B →ₜ* C => g.comp f :=
  (isInducing_toContinuousMap A C).continuous_iff.2 <|
    f.toContinuousMap.continuous_precomp.comp (isInducing_toContinuousMap B C).continuous

@[to_additive]
theorem continuous_comp_right (f : B →ₜ* C) :
    Continuous fun g : (A →ₜ* B) => f.comp g :=
  (isInducing_toContinuousMap A C).continuous_iff.2 <|
    f.toContinuousMap.continuous_postcomp.comp (isInducing_toContinuousMap A B).continuous

variable (E)

/-- `ContinuousMonoidHom _ f` is a functor. -/
@[to_additive "`ContinuousAddMonoidHom _ f` is a functor."]
def compLeft (f : (A →ₜ* B)) : (B →ₜ* E) →ₜ* (A →ₜ* E) where
  toFun g := g.comp f
  map_one' := rfl
  map_mul' _g _h := rfl
  continuous_toFun := f.continuous_comp_left

variable (A) {E}

/-- `ContinuousMonoidHom f _` is a functor. -/
@[to_additive "`ContinuousAddMonoidHom f _` is a functor."]
def compRight {B : Type*} [CommGroup B] [TopologicalSpace B] [TopologicalGroup B] (f : B →ₜ* E) :
    (A →ₜ* B) →ₜ* (A →ₜ* E) where
  toFun g := f.comp g
  map_one' := ext fun _a => map_one f
  map_mul' g h := ext fun a => map_mul f (g a) (h a)
  continuous_toFun := f.continuous_comp_right

variable {A B C D : Type _} [CommGroup A] [TopologicalSpace A] [CommGroup B] [TopologicalSpace B]
  [CommGroup C] [TopologicalSpace C] [CommGroup D] [TopologicalSpace D]

@[to_additive] lemma mul_comp [TopologicalGroup B] (φ ψ : A →ₜ* B) (ξ : C →ₜ* A) :
    (φ * ψ).comp ξ = φ.comp ξ * ψ.comp ξ := rfl

@[to_additive] lemma div_comp [TopologicalGroup B] (φ ψ : A →ₜ* B) (ξ : C →ₜ* A) :
    (φ / ψ).comp ξ = φ.comp ξ / ψ.comp ξ := rfl

@[to_additive] lemma comp_mul [TopologicalGroup B] (φ ψ : A →ₜ* B) (ξ : B →ₜ* C)
    [TopologicalGroup C] : ξ.comp (φ * ψ) = ξ.comp φ * ξ.comp ψ := by
  ext
  apply map_mul ξ

@[to_additive] lemma mul_apply [TopologicalGroup B] (φ ψ : A →ₜ* B) (x : A) :
    (φ * ψ) x = φ x * ψ x := rfl

@[to_additive] lemma inv_apply [TopologicalGroup B] (φ : A →ₜ* B) (x : A) :
    (φ⁻¹) x = (φ x)⁻¹ := rfl

@[to_additive] lemma coe_apply (φ : A →ₜ* B) (a : A) : φ.toMonoidHom a = φ a := rfl

@[to_additive] lemma div_apply [TopologicalGroup B] (φ ψ : A →ₜ* B) (x : A) :
    (φ / ψ) x = φ x / ψ x := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  rfl

@[to_additive] lemma coe_div [TopologicalGroup B] (φ ψ : A →ₜ* B) :
    (φ / ψ).toMonoidHom = φ / ψ := by
  ext
  apply div_apply

@[to_additive] lemma coe_comp (φ : A →ₜ* B) (ψ : B →ₜ* C) :
    (ψ.comp φ).toMonoidHom = ψ.toMonoidHom.comp φ.toMonoidHom := rfl

@[to_additive] lemma comp_apply (φ : A →ₜ* B) (ψ : B →ₜ* C) (x : A) : ψ.comp φ x = ψ (φ x) := rfl

@[to_additive] lemma one_apply (a : A) [TopologicalGroup B] : (1 : A →ₜ* B) a = 1 := by rfl

@[to_additive] lemma coe_eq_one [TopologicalGroup B] (φ : A →ₜ* B) : φ.toMonoidHom = 1 ↔ φ = 1 := by
  constructor
  · intro h
    ext
    rw [←coe_apply, h, one_apply, MonoidHom.one_apply]
  · intro h
    exact h ▸ (rfl : (1 : A →* B) = 1)

@[to_additive] lemma comp_div [TopologicalGroup B] [TopologicalGroup C] (φ ψ : A →ₜ* B)
    (ξ : B →ₜ* C)  : ξ.comp (φ / ψ) = ξ.comp φ / ξ.comp ψ := by
  ext
  rw [comp_apply, div_apply, div_apply, comp_apply,comp_apply, map_div]

@[to_additive] lemma range_le_ker_iff (φ : A →ₜ* B) (ψ : B →ₜ* C) [TopologicalGroup C] :
    φ.range ≤ ψ.ker ↔ ψ.comp φ = 1 := by
  rw [MonoidHom.range_le_ker_iff, ←coe_comp, coe_eq_one]

@[to_additive] lemma id_comp (φ : A →ₜ* B) : (ContinuousMonoidHom.id B).comp φ = φ := by rfl

@[to_additive] lemma comp_assoc (φ : A →ₜ* B) (ψ : B →ₜ* C) (γ : C →ₜ* D) :
    (γ.comp ψ).comp φ = γ.comp (ψ.comp φ) := rfl

@[to_additive] lemma mem_ker (φ : A →ₜ* B) (a : A) : a ∈ φ.ker ↔ φ a = 1 := by rfl

variable {X : Type} [TopologicalSpace X] [TopologicalGroup A] [TopologicalGroup B]
  [TopologicalGroup C]

/--
The continuous homomorphism from a commutative topological group `A` to `C(X,A)`,
taking an element `a : A` to the constant function `fun _ ↦ a`.
-/
@[to_additive] def constₜ  : A →ₜ* C(X,A) where
  toFun             := ContinuousMap.const X
  map_one'          := rfl
  map_mul' _ _      := rfl
  continuous_toFun  := ContinuousMap.continuous_const'

@[to_additive, simp] lemma constₜ_apply₂ (m : A) (x : X) : constₜ m x = m := rfl

/--
Multiplicative functoriality of `C(X,A)` in `A`.
-/
@[to_additive "Additive functoriality of `C(X,A)` in `A`."]
def mapₜ : (A →ₜ* B) →* (C(X,A) →ₜ* C(X,B)) where
  toFun φ := {
    toFun             := φ.toContinuousMap.comp
    map_one'          := by ext; simp
    map_mul' _ _      := by ext; simp
    continuous_toFun  := ContinuousMap.continuous_postcomp φ.toContinuousMap
  }
  map_one'     := rfl
  map_mul' _ _  := rfl

variable (X)

@[to_additive] lemma mapₜ_apply₂ (φ : A →ₜ* B) (f : C(X,A)) : mapₜ φ f = φ.toContinuousMap.comp f :=
  rfl

@[to_additive,simp] lemma mapₜ_apply₃ (φ : A →ₜ* B) (f : C(X,A)) (x : X) : mapₜ φ f x = φ (f x) :=
  rfl

@[to_additive] lemma mapₜ_comp  (φ : A →ₜ* B) (ψ : B →ₜ* C) :
    mapₜ (ψ.comp φ) = (mapₜ ψ).comp (mapₜ φ (X := X)) := rfl

@[to_additive,simp] lemma mapₜ_id : mapₜ (id A) = id C(X,A) := rfl

/--
For any continuous group homomorphism $φ : M \to N$ and any topological space `X`,
we have a commutative square
$$\begin{matrix} M & \to & N \\ \downarrow && \downarrow \\ C(X,M) & \to & C(X,N)$$.
The vertical maps are `constₜ` and the lower horizontal map is `mapₜ G φ`.
-/
@[to_additive]
lemma mapₜ_comp_constₜ (φ : A →ₜ* B) : (mapₜ φ).comp constₜ = constₜ (X := X).comp φ := rfl

section LocallyCompact

variable {X Y : Type*} [TopologicalSpace X] [Group X] [TopologicalGroup X]
  [UniformSpace Y] [CommGroup Y] [UniformGroup Y] [T0Space Y] [CompactSpace Y]

@[to_additive]
theorem locallyCompactSpace_of_equicontinuousAt (U : Set X) (V : Set Y)
    (hU : IsCompact U) (hV : V ∈ nhds (1 : Y))
    (h : EquicontinuousAt (fun f : {f : X →* Y | Set.MapsTo f U V} ↦ (f : X → Y)) 1) :
    LocallyCompactSpace (X →ₜ* Y) := by
  replace h := equicontinuous_of_equicontinuousAt_one _ h
  obtain ⟨W, hWo, hWV, hWc⟩ := local_compact_nhds hV
  let S1 : Set (X →* Y) := {f | Set.MapsTo f U W}
  let S2 : Set (X →ₜ* Y) := {f | Set.MapsTo f U W}
  let S3 : Set C(X, Y) := (↑) '' S2
  let S4 : Set (X → Y) := (↑) '' S3
  replace h : Equicontinuous ((↑) : S1 → X → Y) :=
    h.comp (Subtype.map _root_.id fun f hf ↦ hf.mono_right hWV)
  have hS4 : S4 = (↑) '' S1 := by
    ext
    constructor
    · rintro ⟨-, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, h.continuous ⟨f, hf⟩⟩, ⟨⟨f, h.continuous ⟨f, hf⟩⟩, hf, rfl⟩, rfl⟩
  replace h : Equicontinuous ((↑) : S3 → X → Y) := by
    rw [equicontinuous_iff_range, ← Set.image_eq_range] at h ⊢
    rwa [← hS4] at h
  replace hS4 : S4 = Set.pi U (fun _ ↦ W) ∩ Set.range ((↑) : (X →* Y) → (X → Y)) := by
    simp_rw [hS4, Set.ext_iff, Set.mem_image, S1, Set.mem_setOf_eq]
    exact fun f ↦ ⟨fun ⟨g, hg, hf⟩ ↦ hf ▸ ⟨hg, g, rfl⟩, fun ⟨hg, g, hf⟩ ↦ ⟨g, hf ▸ hg, hf⟩⟩
  replace hS4 : IsClosed S4 :=
    hS4.symm ▸ (isClosed_set_pi (fun _ _ ↦ hWc.isClosed)).inter (MonoidHom.isClosed_range_coe X Y)
  have hS2 : (interior S2).Nonempty := by
    let T : Set (X →ₜ* Y) := {f | Set.MapsTo f U (interior W)}
    have h1 : T.Nonempty := ⟨1, fun _ _ ↦ mem_interior_iff_mem_nhds.mpr hWo⟩
    have h2 : T ⊆ S2 := fun f hf ↦ hf.mono_right interior_subset
    have h3 : IsOpen T := isOpen_induced (ContinuousMap.isOpen_setOf_mapsTo hU isOpen_interior)
    exact h1.mono (interior_maximal h2 h3)
  exact TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group
    ⟨⟨S2, (isInducing_toContinuousMap X Y).isCompact_iff.mpr
      (ArzelaAscoli.isCompact_of_equicontinuous S3 hS4.isCompact h)⟩, hS2⟩

variable [LocallyCompactSpace X]

@[to_additive]
theorem locallyCompactSpace_of_hasBasis (V : ℕ → Set Y)
    (hV : ∀ {n x}, x ∈ V n → x * x ∈ V n → x ∈ V (n + 1))
    (hVo : Filter.HasBasis (nhds 1) (fun _ ↦ True) V) :
    LocallyCompactSpace (X →ₜ* Y) := by
  obtain ⟨U0, hU0c, hU0o⟩ := exists_compact_mem_nhds (1 : X)
  let U_aux : ℕ → {S : Set X | S ∈ nhds 1} :=
    Nat.rec ⟨U0, hU0o⟩ <| fun _ S ↦ let h := exists_closed_nhds_one_inv_eq_mul_subset S.2
      ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  let U : ℕ → Set X := fun n ↦ (U_aux n).1
  have hU1 : ∀ n, U n ∈ nhds 1 := fun n ↦ (U_aux n).2
  have hU2 : ∀ n, U (n + 1) * U (n + 1) ⊆ U n :=
    fun n ↦ (Classical.choose_spec (exists_closed_nhds_one_inv_eq_mul_subset (U_aux n).2)).2.2.2
  have hU3 : ∀ n, U (n + 1) ⊆ U n :=
    fun n x hx ↦ hU2 n (mul_one x ▸ Set.mul_mem_mul hx (mem_of_mem_nhds (hU1 (n + 1))))
  have hU4 : ∀ f : X →* Y, Set.MapsTo f (U 0) (V 0) → ∀ n, Set.MapsTo f (U n) (V n) := by
    intro f hf n
    induction' n with n ih
    · exact hf
    · exact fun x hx ↦ hV (ih (hU3 n hx)) (map_mul f x x ▸ ih (hU2 n (Set.mul_mem_mul hx hx)))
  apply locallyCompactSpace_of_equicontinuousAt (U 0) (V 0) hU0c (hVo.mem_of_mem trivial)
  rw [hVo.uniformity_of_nhds_one.equicontinuousAt_iff_right]
  refine fun n _ ↦ Filter.eventually_iff_exists_mem.mpr ⟨U n, hU1 n, fun x hx ⟨f, hf⟩ ↦ ?_⟩
  rw [Set.mem_setOf_eq, map_one, div_one]
  exact hU4 f hf n hx

end LocallyCompact

end ContinuousMonoidHom

end

section

/-!

# Continuous MulEquiv

This section defines the space of continuous isomorphisms between two topological groups.

## Main definitions

-/

universe u v

variable (G : Type u) [TopologicalSpace G] (H : Type v) [TopologicalSpace H]

/-- The structure of two-sided continuous isomorphisms between additive groups.
Note that both the map and its inverse have to be continuous. -/
structure ContinuousAddEquiv [Add G] [Add H] extends G ≃+ H , G ≃ₜ H

/-- The structure of two-sided continuous isomorphisms between groups.
Note that both the map and its inverse have to be continuous. -/
@[to_additive "The structure of two-sided continuous isomorphisms between additive groups.
Note that both the map and its inverse have to be continuous."]
structure ContinuousMulEquiv [Mul G] [Mul H] extends G ≃* H , G ≃ₜ H

/-- The homeomorphism induced from a two-sided continuous isomorphism of groups. -/
add_decl_doc ContinuousMulEquiv.toHomeomorph

/-- The homeomorphism induced from a two-sided continuous isomorphism additive groups. -/
add_decl_doc ContinuousAddEquiv.toHomeomorph

@[inherit_doc]
infixl:25 " ≃ₜ* " => ContinuousMulEquiv

@[inherit_doc]
infixl:25 " ≃ₜ+ " => ContinuousAddEquiv

section

namespace ContinuousMulEquiv

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [Mul M] [Mul N]

section coe

@[to_additive]
instance : EquivLike (M ≃ₜ* N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    exact MulEquiv.ext_iff.mpr (congrFun h₁)

@[to_additive]
instance : MulEquivClass (M ≃ₜ* N) M N where
  map_mul f := f.map_mul'

@[to_additive]
instance : HomeomorphClass (M ≃ₜ* N) M N where
  map_continuous f := f.continuous_toFun
  inv_continuous f := f.continuous_invFun

/-- Two continuous multiplicative isomorphisms agree if they are defined by the
same underlying function. -/
@[to_additive (attr := ext)
  "Two continuous additive isomorphisms agree if they are defined by the same underlying function."]
theorem ext {f g : M ≃ₜ* N} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[to_additive (attr := simp)]
theorem coe_mk (f : M ≃* N) (hf1 hf2) : ⇑(mk f hf1 hf2) = f := rfl

@[to_additive]
theorem toEquiv_eq_coe (f : M ≃ₜ* N) : f.toEquiv = f :=
  rfl

@[to_additive (attr := simp)]
theorem toMulEquiv_eq_coe (f : M ≃ₜ* N) : f.toMulEquiv = f :=
  rfl

@[to_additive]
theorem toHomeomorph_eq_coe (f : M ≃ₜ* N) : f.toHomeomorph = f :=
  rfl

/-- Makes a continuous multiplicative isomorphism from
a homeomorphism which preserves multiplication. -/
@[to_additive "Makes an continuous additive isomorphism from
a homeomorphism which preserves addition."]
def mk' (f : M ≃ₜ N) (h : ∀ x y, f (x * y) = f x * f y) : M ≃ₜ* N :=
  ⟨⟨f.toEquiv,h⟩, f.continuous_toFun, f.continuous_invFun⟩

set_option linter.docPrime false in -- This is about `ContinuousMulEquiv.mk'`
@[simp]
lemma coe_mk' (f : M ≃ₜ N) (h : ∀ x y, f (x * y) = f x * f y)  : ⇑(mk' f h) = f := rfl

end coe

section bijective

@[to_additive]
protected theorem bijective (e : M ≃ₜ* N) : Function.Bijective e :=
  EquivLike.bijective e

@[to_additive]
protected theorem injective (e : M ≃ₜ* N) : Function.Injective e :=
  EquivLike.injective e

@[to_additive]
protected theorem surjective (e : M ≃ₜ* N) : Function.Surjective e :=
  EquivLike.surjective e

@[to_additive]
theorem apply_eq_iff_eq (e : M ≃ₜ* N) {x y : M} : e x = e y ↔ x = y :=
  e.injective.eq_iff

end bijective

section refl

variable (M)

/-- The identity map is a continuous multiplicative isomorphism. -/
@[to_additive (attr := refl) "The identity map is a continuous additive isomorphism."]
def refl : M ≃ₜ* M :=
  { MulEquiv.refl _ with }

@[to_additive]
instance : Inhabited (M ≃ₜ* M) := ⟨ContinuousMulEquiv.refl M⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_refl : ↑(refl M) = id := rfl

@[to_additive (attr := simp)]
theorem refl_apply (m : M) : refl M m = m := rfl

end refl

section symm

/-- The inverse of a ContinuousMulEquiv. -/
@[to_additive (attr := symm) "The inverse of a ContinuousAddEquiv."]
def symm (cme : M ≃ₜ* N) : N ≃ₜ* M :=
  { cme.toMulEquiv.symm with
  continuous_toFun := cme.continuous_invFun
  continuous_invFun := cme.continuous_toFun }
initialize_simps_projections ContinuousMulEquiv (toFun → apply, invFun → symm_apply)

@[to_additive]
theorem invFun_eq_symm {f : M ≃ₜ* N} : f.invFun = f.symm := rfl

@[to_additive (attr := simp)]
theorem coe_toHomeomorph_symm (f : M ≃ₜ* N) : (f : M ≃ₜ N).symm = (f.symm : N ≃ₜ M) := rfl

@[to_additive (attr := simp)]
theorem equivLike_inv_eq_symm (f : M ≃ₜ* N) : EquivLike.inv f = f.symm := rfl

@[to_additive (attr := simp)]
theorem symm_symm (f : M ≃ₜ* N) : f.symm.symm = f := rfl

/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/
@[to_additive (attr := simp) "`e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`."]
theorem apply_symm_apply (e : M ≃ₜ* N) (y : N) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y

/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/
@[to_additive (attr := simp) "`e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`."]
theorem symm_apply_apply (e : M ≃ₜ* N) (x : M) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]
theorem symm_comp_self (e : M ≃ₜ* N) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[to_additive (attr := simp)]
theorem self_comp_symm (e : M ≃ₜ* N) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[to_additive]
theorem apply_eq_iff_symm_apply (e : M ≃ₜ* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
  e.toEquiv.apply_eq_iff_eq_symm_apply

@[to_additive]
theorem symm_apply_eq (e : M ≃ₜ* N) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

@[to_additive]
theorem eq_symm_apply (e : M ≃ₜ* N) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[to_additive]
theorem eq_comp_symm {α : Type*} (e : M ≃ₜ* N) (f : N → α) (g : M → α) :
    f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

@[to_additive]
theorem comp_symm_eq {α : Type*} (e : M ≃ₜ* N) (f : N → α) (g : M → α) :
    g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g

@[to_additive]
theorem eq_symm_comp {α : Type*} (e : M ≃ₜ* N) (f : α → M) (g : α → N) :
    f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g

@[to_additive]
theorem symm_comp_eq {α : Type*} (e : M ≃ₜ* N) (f : α → M) (g : α → N) :
    e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g

end symm

section trans

variable {L : Type*} [Mul L] [TopologicalSpace L]

/-- The composition of two ContinuousMulEquiv. -/
@[to_additive "The composition of two ContinuousAddEquiv."]
def trans (cme1 : M ≃ₜ* N) (cme2 : N ≃ₜ* L) : M ≃ₜ* L :=
  { cme1.toMulEquiv.trans cme2.toMulEquiv with
  continuous_toFun := by convert Continuous.comp cme2.continuous_toFun cme1.continuous_toFun
  continuous_invFun := by convert Continuous.comp cme1.continuous_invFun cme2.continuous_invFun }

@[to_additive (attr := simp)]
theorem coe_trans (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) : ↑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

@[to_additive (attr := simp)]
theorem trans_apply (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) := rfl

@[to_additive (attr := simp)]
theorem symm_trans_apply (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (l : L) :
    (e₁.trans e₂).symm l = e₁.symm (e₂.symm l) := rfl

@[to_additive (attr := simp)]
theorem symm_trans_self (e : M ≃ₜ* N) : e.symm.trans e = refl N :=
  DFunLike.ext _ _ e.apply_symm_apply

@[to_additive (attr := simp)]
theorem self_trans_symm (e : M ≃ₜ* N) : e.trans e.symm = refl M :=
  DFunLike.ext _ _ e.symm_apply_apply

end trans

section unique

/-- The `MulEquiv` between two monoids with a unique element. -/
@[to_additive "The `AddEquiv` between two `AddMonoid`s with a unique element."]
def ofUnique {M N} [Unique M] [Unique N] [Mul M] [Mul N]
    [TopologicalSpace M] [TopologicalSpace N] : M ≃ₜ* N :=
  { MulEquiv.ofUnique with
  continuous_toFun := by continuity
  continuous_invFun := by continuity }

/-- There is a unique monoid homomorphism between two monoids with a unique element. -/
@[to_additive "There is a unique additive monoid homomorphism between two additive monoids with
  a unique element."]
instance {M N} [Unique M] [Unique N] [Mul M] [Mul N]
    [TopologicalSpace M] [TopologicalSpace N] : Unique (M ≃ₜ* N) where
  default := ofUnique
  uniq _ := ext fun _ ↦ Subsingleton.elim _ _

end unique

end ContinuousMulEquiv

end

end
