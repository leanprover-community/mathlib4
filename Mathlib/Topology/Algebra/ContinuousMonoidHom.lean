/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning

! This file was ported from Lean 3 source module topology.algebra.continuous_monoid_hom
! leanprover-community/mathlib commit 6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.Circle
import Mathbin.Topology.ContinuousFunction.Algebra

/-!

# Continuous Monoid Homs

This file defines the space of continuous homomorphisms between two topological groups.

## Main definitions

* `continuous_monoid_hom A B`: The continuous homomorphisms `A →* B`.
* `continuous_add_monoid_hom A B`: The continuous additive homomorphisms `A →+ B`.
-/


open Pointwise

open Function

variable (F A B C D E : Type _) [Monoid A] [Monoid B] [Monoid C] [Monoid D] [CommGroup E]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [TopologicalSpace E] [TopologicalGroup E]

/-- The type of continuous additive monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : continuous_add_monoid_hom A B)`,
you should parametrize over `(F : Type*) [continuous_add_monoid_hom_class F A B] (f : F)`.

When you extend this structure, make sure to extend `continuous_add_monoid_hom_class`. -/
structure ContinuousAddMonoidHom (A B : Type _) [AddMonoid A] [AddMonoid B] [TopologicalSpace A]
  [TopologicalSpace B] extends A →+ B where
  continuous_toFun : Continuous to_fun
#align continuous_add_monoid_hom ContinuousAddMonoidHom

/-- The type of continuous monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : continuous_monoid_hom A B)`,
you should parametrize over `(F : Type*) [continuous_monoid_hom_class F A B] (f : F)`.

When you extend this structure, make sure to extend `continuous_add_monoid_hom_class`. -/
@[to_additive]
structure ContinuousMonoidHom extends A →* B where
  continuous_toFun : Continuous to_fun
#align continuous_monoid_hom ContinuousMonoidHom
#align continuous_add_monoid_hom ContinuousAddMonoidHom

section

/-- `continuous_add_monoid_hom_class F A B` states that `F` is a type of continuous additive monoid
homomorphisms.

You should also extend this typeclass when you extend `continuous_add_monoid_hom`. -/
class ContinuousAddMonoidHomClass (A B : Type _) [AddMonoid A] [AddMonoid B] [TopologicalSpace A]
  [TopologicalSpace B] extends AddMonoidHomClass F A B where
  map_continuous (f : F) : Continuous f
#align continuous_add_monoid_hom_class ContinuousAddMonoidHomClass

/-- `continuous_monoid_hom_class F A B` states that `F` is a type of continuous additive monoid
homomorphisms.

You should also extend this typeclass when you extend `continuous_monoid_hom`. -/
@[to_additive]
class ContinuousMonoidHomClass extends MonoidHomClass F A B where
  map_continuous (f : F) : Continuous f
#align continuous_monoid_hom_class ContinuousMonoidHomClass
#align continuous_add_monoid_hom_class ContinuousAddMonoidHomClass

attribute [to_additive ContinuousAddMonoidHomClass.toAddMonoidHomClass]
  ContinuousMonoidHomClass.toMonoidHomClass

end

/-- Reinterpret a `continuous_monoid_hom` as a `monoid_hom`. -/
add_decl_doc ContinuousMonoidHom.toMonoidHom

/-- Reinterpret a `continuous_add_monoid_hom` as an `add_monoid_hom`. -/
add_decl_doc ContinuousAddMonoidHom.toAddMonoidHom

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) ContinuousMonoidHomClass.toContinuousMapClass
    [ContinuousMonoidHomClass F A B] : ContinuousMapClass F A B :=
  { ‹ContinuousMonoidHomClass F A B› with }
#align continuous_monoid_hom_class.to_continuous_map_class ContinuousMonoidHomClass.toContinuousMapClass
#align continuous_add_monoid_hom_class.to_continuous_map_class ContinuousAddMonoidHomClass.to_continuous_map_class

namespace ContinuousMonoidHom

variable {A B C D E}

@[to_additive]
instance : ContinuousMonoidHomClass (ContinuousMonoidHom A B) A B
    where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_continuous f := f.continuous_toFun

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
@[to_additive
      "Helper instance for when there's too many metavariables to apply\n`fun_like.has_coe_to_fun` directly."]
instance : CoeFun (ContinuousMonoidHom A B) fun _ => A → B :=
  FunLike.hasCoeToFun

@[to_additive, ext]
theorem ext {f g : ContinuousMonoidHom A B} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h
#align continuous_monoid_hom.ext ContinuousMonoidHom.ext
#align continuous_add_monoid_hom.ext ContinuousAddMonoidHom.ext

/-- Reinterpret a `continuous_monoid_hom` as a `continuous_map`. -/
@[to_additive "Reinterpret a `continuous_add_monoid_hom` as a `continuous_map`."]
def toContinuousMap (f : ContinuousMonoidHom A B) : C(A, B) :=
  { f with }
#align continuous_monoid_hom.to_continuous_map ContinuousMonoidHom.toContinuousMap
#align continuous_add_monoid_hom.to_continuous_map ContinuousAddMonoidHom.toContinuousMap

@[to_additive]
theorem toContinuousMap_injective : Injective (toContinuousMap : _ → C(A, B)) := fun f g h =>
  ext <| by convert FunLike.ext_iff.1 h
#align continuous_monoid_hom.to_continuous_map_injective ContinuousMonoidHom.toContinuousMap_injective
#align continuous_add_monoid_hom.to_continuous_map_injective ContinuousAddMonoidHom.toContinuousMap_injective

/-- Construct a `continuous_monoid_hom` from a `continuous` `monoid_hom`. -/
@[to_additive "Construct a `continuous_add_monoid_hom` from a `continuous` `add_monoid_hom`.",
  simps]
def mk' (f : A →* B) (hf : Continuous f) : ContinuousMonoidHom A B :=
  { f with continuous_toFun := hf }
#align continuous_monoid_hom.mk' ContinuousMonoidHom.mk'
#align continuous_add_monoid_hom.mk' ContinuousAddMonoidHom.mk'

/-- Composition of two continuous homomorphisms. -/
@[to_additive "Composition of two continuous homomorphisms.", simps]
def comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) : ContinuousMonoidHom A C :=
  mk' (g.toMonoidHom.comp f.toMonoidHom) (g.continuous_toFun.comp f.continuous_toFun)
#align continuous_monoid_hom.comp ContinuousMonoidHom.comp
#align continuous_add_monoid_hom.comp ContinuousAddMonoidHom.comp

/-- Product of two continuous homomorphisms on the same space. -/
@[to_additive "Product of two continuous homomorphisms on the same space.", simps]
def prod (f : ContinuousMonoidHom A B) (g : ContinuousMonoidHom A C) :
    ContinuousMonoidHom A (B × C) :=
  mk' (f.toMonoidHom.Prod g.toMonoidHom) (f.continuous_toFun.prod_mk g.continuous_toFun)
#align continuous_monoid_hom.prod ContinuousMonoidHom.prod
#align continuous_add_monoid_hom.sum ContinuousAddMonoidHom.sum

/-- Product of two continuous homomorphisms on different spaces. -/
@[to_additive "Product of two continuous homomorphisms on different spaces.", simps]
def prodMap (f : ContinuousMonoidHom A C) (g : ContinuousMonoidHom B D) :
    ContinuousMonoidHom (A × B) (C × D) :=
  mk' (f.toMonoidHom.Prod_map g.toMonoidHom) (f.continuous_toFun.Prod_map g.continuous_toFun)
#align continuous_monoid_hom.prod_map ContinuousMonoidHom.prodMap
#align continuous_add_monoid_hom.sum_map ContinuousAddMonoidHom.sumMap

variable (A B C D E)

/-- The trivial continuous homomorphism. -/
@[to_additive "The trivial continuous homomorphism.", simps]
def one : ContinuousMonoidHom A B :=
  mk' 1 continuous_const
#align continuous_monoid_hom.one ContinuousMonoidHom.one
#align continuous_add_monoid_hom.zero ContinuousAddMonoidHom.zero

@[to_additive]
instance : Inhabited (ContinuousMonoidHom A B) :=
  ⟨one A B⟩

/-- The identity continuous homomorphism. -/
@[to_additive "The identity continuous homomorphism.", simps]
def id : ContinuousMonoidHom A A :=
  mk' (MonoidHom.id A) continuous_id
#align continuous_monoid_hom.id ContinuousMonoidHom.id
#align continuous_add_monoid_hom.id ContinuousAddMonoidHom.id

/-- The continuous homomorphism given by projection onto the first factor. -/
@[to_additive "The continuous homomorphism given by projection onto the first factor.", simps]
def fst : ContinuousMonoidHom (A × B) A :=
  mk' (MonoidHom.fst A B) continuous_fst
#align continuous_monoid_hom.fst ContinuousMonoidHom.fst
#align continuous_add_monoid_hom.fst ContinuousAddMonoidHom.fst

/-- The continuous homomorphism given by projection onto the second factor. -/
@[to_additive "The continuous homomorphism given by projection onto the second factor.", simps]
def snd : ContinuousMonoidHom (A × B) B :=
  mk' (MonoidHom.snd A B) continuous_snd
#align continuous_monoid_hom.snd ContinuousMonoidHom.snd
#align continuous_add_monoid_hom.snd ContinuousAddMonoidHom.snd

/-- The continuous homomorphism given by inclusion of the first factor. -/
@[to_additive "The continuous homomorphism given by inclusion of the first factor.", simps]
def inl : ContinuousMonoidHom A (A × B) :=
  prod (id A) (one A B)
#align continuous_monoid_hom.inl ContinuousMonoidHom.inl
#align continuous_add_monoid_hom.inl ContinuousAddMonoidHom.inl

/-- The continuous homomorphism given by inclusion of the second factor. -/
@[to_additive "The continuous homomorphism given by inclusion of the second factor.", simps]
def inr : ContinuousMonoidHom B (A × B) :=
  prod (one B A) (id B)
#align continuous_monoid_hom.inr ContinuousMonoidHom.inr
#align continuous_add_monoid_hom.inr ContinuousAddMonoidHom.inr

/-- The continuous homomorphism given by the diagonal embedding. -/
@[to_additive "The continuous homomorphism given by the diagonal embedding.", simps]
def diag : ContinuousMonoidHom A (A × A) :=
  prod (id A) (id A)
#align continuous_monoid_hom.diag ContinuousMonoidHom.diag
#align continuous_add_monoid_hom.diag ContinuousAddMonoidHom.diag

/-- The continuous homomorphism given by swapping components. -/
@[to_additive "The continuous homomorphism given by swapping components.", simps]
def swap : ContinuousMonoidHom (A × B) (B × A) :=
  prod (snd A B) (fst A B)
#align continuous_monoid_hom.swap ContinuousMonoidHom.swap
#align continuous_add_monoid_hom.swap ContinuousAddMonoidHom.swap

/-- The continuous homomorphism given by multiplication. -/
@[to_additive "The continuous homomorphism given by addition.", simps]
def mul : ContinuousMonoidHom (E × E) E :=
  mk' mulMonoidHom continuous_mul
#align continuous_monoid_hom.mul ContinuousMonoidHom.mul
#align continuous_add_monoid_hom.add ContinuousAddMonoidHom.add

/-- The continuous homomorphism given by inversion. -/
@[to_additive "The continuous homomorphism given by negation.", simps]
def inv : ContinuousMonoidHom E E :=
  mk' invMonoidHom continuous_inv
#align continuous_monoid_hom.inv ContinuousMonoidHom.inv
#align continuous_add_monoid_hom.neg ContinuousAddMonoidHom.neg

variable {A B C D E}

/-- Coproduct of two continuous homomorphisms to the same space. -/
@[to_additive "Coproduct of two continuous homomorphisms to the same space.", simps]
def coprod (f : ContinuousMonoidHom A E) (g : ContinuousMonoidHom B E) :
    ContinuousMonoidHom (A × B) E :=
  (mul E).comp (f.Prod_map g)
#align continuous_monoid_hom.coprod ContinuousMonoidHom.coprod
#align continuous_add_monoid_hom.coprod ContinuousAddMonoidHom.coprod

@[to_additive]
instance : CommGroup (ContinuousMonoidHom A E)
    where
  mul f g := (mul E).comp (f.Prod g)
  mul_comm f g := ext fun x => mul_comm (f x) (g x)
  mul_assoc f g h := ext fun x => mul_assoc (f x) (g x) (h x)
  one := one A E
  one_mul f := ext fun x => one_mul (f x)
  mul_one f := ext fun x => mul_one (f x)
  inv f := (inv E).comp f
  mul_left_inv f := ext fun x => mul_left_inv (f x)

@[to_additive]
instance : TopologicalSpace (ContinuousMonoidHom A B) :=
  TopologicalSpace.induced toContinuousMap ContinuousMap.compactOpen

variable (A B C D E)

@[to_additive]
theorem inducing_toContinuousMap : Inducing (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) :=
  ⟨rfl⟩
#align continuous_monoid_hom.inducing_to_continuous_map ContinuousMonoidHom.inducing_toContinuousMap
#align continuous_add_monoid_hom.inducing_to_continuous_map ContinuousAddMonoidHom.inducing_toContinuousMap

@[to_additive]
theorem embedding_toContinuousMap :
    Embedding (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) :=
  ⟨inducing_toContinuousMap A B, toContinuousMap_injective⟩
#align continuous_monoid_hom.embedding_to_continuous_map ContinuousMonoidHom.embedding_toContinuousMap
#align continuous_add_monoid_hom.embedding_to_continuous_map ContinuousAddMonoidHom.embedding_toContinuousMap

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (U V W) -/
@[to_additive]
theorem closedEmbedding_toContinuousMap [ContinuousMul B] [T2Space B] :
    ClosedEmbedding (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) :=
  ⟨embedding_toContinuousMap A B,
    ⟨by
      suffices
        Set.range (to_continuous_map : ContinuousMonoidHom A B → C(A, B)) =
          ({ f | f '' {1} ⊆ {1}ᶜ } ∪
              ⋃ (x) (y) (U) (V) (W) (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W) (h :
                Disjoint (U * V) W),
                { f | f '' {x} ⊆ U } ∩ { f | f '' {y} ⊆ V } ∩ { f | f '' {x * y} ⊆ W })ᶜ
        by
        rw [this, compl_compl]
        refine' (ContinuousMap.isOpen_gen isCompact_singleton isOpen_compl_singleton).union _
        repeat' apply isOpen_iUnion; intro
        repeat' apply IsOpen.inter
        all_goals apply ContinuousMap.isOpen_gen isCompact_singleton; assumption
      simp_rw [Set.compl_union, Set.compl_iUnion, Set.image_singleton, Set.singleton_subset_iff,
        Set.ext_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
      refine' fun f => ⟨_, _⟩
      · rintro ⟨f, rfl⟩
        exact
          ⟨fun h => h (map_one f), fun x y U V W hU hV hW h ⟨⟨hfU, hfV⟩, hfW⟩ =>
            h.le_bot ⟨Set.mul_mem_mul hfU hfV, (congr_arg (· ∈ W) (map_mul f x y)).mp hfW⟩⟩
      · rintro ⟨hf1, hf2⟩
        suffices ∀ x y, f (x * y) = f x * f y by
          refine'
            ⟨({ f with
                  map_one' := of_not_not hf1
                  map_mul' := this } :
                ContinuousMonoidHom A B),
              ContinuousMap.ext fun _ => rfl⟩
        intro x y
        contrapose! hf2
        obtain ⟨UV, W, hUV, hW, hfUV, hfW, h⟩ := t2_separation hf2.symm
        have hB := @continuous_mul B _ _ _
        obtain ⟨U, V, hU, hV, hfU, hfV, h'⟩ :=
          is_open_prod_iff.mp (hUV.preimage hB) (f x) (f y) hfUV
        refine' ⟨x, y, U, V, W, hU, hV, hW, h.mono_left _, ⟨hfU, hfV⟩, hfW⟩
        rintro _ ⟨x, y, hx : (x, y).1 ∈ U, hy : (x, y).2 ∈ V, rfl⟩
        exact h' ⟨hx, hy⟩⟩⟩
#align continuous_monoid_hom.closed_embedding_to_continuous_map ContinuousMonoidHom.closedEmbedding_toContinuousMap
#align continuous_add_monoid_hom.closed_embedding_to_continuous_map ContinuousAddMonoidHom.closedEmbedding_toContinuousMap

variable {A B C D E}

@[to_additive]
instance [T2Space B] : T2Space (ContinuousMonoidHom A B) :=
  (embedding_toContinuousMap A B).T2Space

@[to_additive]
instance : TopologicalGroup (ContinuousMonoidHom A E) :=
  let hi := inducing_toContinuousMap A E
  let hc := hi.Continuous
  { continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (Continuous.prod_map hc hc))
    continuous_inv := hi.continuous_iff.mpr (continuous_inv.comp hc) }

@[to_additive]
theorem continuous_of_continuous_uncurry {A : Type _} [TopologicalSpace A]
    (f : A → ContinuousMonoidHom B C) (h : Continuous (Function.uncurry fun x y => f x y)) :
    Continuous f :=
  (inducing_toContinuousMap _ _).continuous_iff.mpr
    (ContinuousMap.continuous_of_continuous_uncurry _ h)
#align continuous_monoid_hom.continuous_of_continuous_uncurry ContinuousMonoidHom.continuous_of_continuous_uncurry
#align continuous_add_monoid_hom.continuous_of_continuous_uncurry ContinuousAddMonoidHom.continuous_of_continuous_uncurry

@[to_additive]
theorem continuous_comp [LocallyCompactSpace B] :
    Continuous fun f : ContinuousMonoidHom A B × ContinuousMonoidHom B C => f.2.comp f.1 :=
  (inducing_toContinuousMap A C).continuous_iff.2 <|
    ContinuousMap.continuous_comp'.comp
      ((inducing_toContinuousMap A B).prod_mk (inducing_toContinuousMap B C)).Continuous
#align continuous_monoid_hom.continuous_comp ContinuousMonoidHom.continuous_comp
#align continuous_add_monoid_hom.continuous_comp ContinuousAddMonoidHom.continuous_comp

@[to_additive]
theorem continuous_comp_left (f : ContinuousMonoidHom A B) :
    Continuous fun g : ContinuousMonoidHom B C => g.comp f :=
  (inducing_toContinuousMap A C).continuous_iff.2 <|
    f.toContinuousMap.continuous_comp_left.comp (inducing_toContinuousMap B C).Continuous
#align continuous_monoid_hom.continuous_comp_left ContinuousMonoidHom.continuous_comp_left
#align continuous_add_monoid_hom.continuous_comp_left ContinuousAddMonoidHom.continuous_comp_left

@[to_additive]
theorem continuous_comp_right (f : ContinuousMonoidHom B C) :
    Continuous fun g : ContinuousMonoidHom A B => f.comp g :=
  (inducing_toContinuousMap A C).continuous_iff.2 <|
    f.toContinuousMap.continuous_comp.comp (inducing_toContinuousMap A B).Continuous
#align continuous_monoid_hom.continuous_comp_right ContinuousMonoidHom.continuous_comp_right
#align continuous_add_monoid_hom.continuous_comp_right ContinuousAddMonoidHom.continuous_comp_right

variable (E)

/-- `continuous_monoid_hom _ f` is a functor. -/
@[to_additive "`continuous_add_monoid_hom _ f` is a functor."]
def compLeft (f : ContinuousMonoidHom A B) :
    ContinuousMonoidHom (ContinuousMonoidHom B E) (ContinuousMonoidHom A E)
    where
  toFun g := g.comp f
  map_one' := rfl
  map_mul' g h := rfl
  continuous_toFun := f.continuous_comp_left
#align continuous_monoid_hom.comp_left ContinuousMonoidHom.compLeft
#align continuous_add_monoid_hom.comp_left ContinuousAddMonoidHom.compLeft

variable (A) {E}

/-- `continuous_monoid_hom f _` is a functor. -/
@[to_additive "`continuous_add_monoid_hom f _` is a functor."]
def compRight {B : Type _} [CommGroup B] [TopologicalSpace B] [TopologicalGroup B]
    (f : ContinuousMonoidHom B E) :
    ContinuousMonoidHom (ContinuousMonoidHom A B) (ContinuousMonoidHom A E)
    where
  toFun g := f.comp g
  map_one' := ext fun a => map_one f
  map_mul' g h := ext fun a => map_mul f (g a) (h a)
  continuous_toFun := f.continuous_comp_right
#align continuous_monoid_hom.comp_right ContinuousMonoidHom.compRight
#align continuous_add_monoid_hom.comp_right ContinuousAddMonoidHom.compRight

end ContinuousMonoidHom

/-- The Pontryagin dual of `A` is the group of continuous homomorphism `A → circle`. -/
def PontryaginDual :=
  ContinuousMonoidHom A circle deriving TopologicalSpace, T2Space, CommGroup, TopologicalGroup,
  Inhabited
#align pontryagin_dual PontryaginDual

variable {A B C D E}

namespace PontryaginDual

open ContinuousMonoidHom

noncomputable instance : ContinuousMonoidHomClass (PontryaginDual A) A circle :=
  ContinuousMonoidHom.continuousMonoidHomClass

/-- `pontryagin_dual` is a functor. -/
noncomputable def map (f : ContinuousMonoidHom A B) :
    ContinuousMonoidHom (PontryaginDual B) (PontryaginDual A) :=
  f.compLeft circle
#align pontryagin_dual.map PontryaginDual.map

@[simp]
theorem map_apply (f : ContinuousMonoidHom A B) (x : PontryaginDual B) (y : A) :
    map f x y = x (f y) :=
  rfl
#align pontryagin_dual.map_apply PontryaginDual.map_apply

@[simp]
theorem map_one : map (one A B) = one (PontryaginDual B) (PontryaginDual A) :=
  ext fun x => ext fun y => map_one x
#align pontryagin_dual.map_one PontryaginDual.map_one

@[simp]
theorem map_comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) :
    map (comp g f) = comp (map f) (map g) :=
  ext fun x => ext fun y => rfl
#align pontryagin_dual.map_comp PontryaginDual.map_comp

@[simp]
theorem map_mul (f g : ContinuousMonoidHom A E) : map (f * g) = map f * map g :=
  ext fun x => ext fun y => map_mul x (f y) (g y)
#align pontryagin_dual.map_mul PontryaginDual.map_mul

variable (A B C D E)

/-- `continuous_monoid_hom.dual` as a `continuous_monoid_hom`. -/
noncomputable def mapHom [LocallyCompactSpace E] :
    ContinuousMonoidHom (ContinuousMonoidHom A E)
      (ContinuousMonoidHom (PontryaginDual E) (PontryaginDual A))
    where
  toFun := map
  map_one' := map_one
  map_mul' := map_mul
  continuous_toFun := continuous_of_continuous_uncurry _ continuous_comp
#align pontryagin_dual.map_hom PontryaginDual.mapHom

end PontryaginDual

