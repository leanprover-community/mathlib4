/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.ContinuousFunction.Algebra

#align_import topology.algebra.continuous_monoid_hom from "leanprover-community/mathlib"@"6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f"

/-!

# Continuous Monoid Homs

This file defines the space of continuous homomorphisms between two topological groups.

## Main definitions

* `ContinuousMonoidHom A B`: The continuous homomorphisms `A →* B`.
* `ContinuousAddMonoidHom A B`: The continuous additive homomorphisms `A →+ B`.
-/


open Pointwise Function

variable (F A B C D E : Type*) [Monoid A] [Monoid B] [Monoid C] [Monoid D] [CommGroup E]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [TopologicalSpace E] [TopologicalGroup E]

/-- The type of continuous additive monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : ContinuousAddMonoidHom A B)`,
you should parametrize over `(F : Type*) [ContinuousAddMonoidHomClass F A B] (f : F)`.

When you extend this structure, make sure to extend `ContinuousAddMonoidHomClass`. -/
structure ContinuousAddMonoidHom (A B : Type*) [AddMonoid A] [AddMonoid B] [TopologicalSpace A]
  [TopologicalSpace B] extends A →+ B where
  /-- Proof of continuity of the Hom. -/
  continuous_toFun : @Continuous A B _ _ toFun

/-- The type of continuous monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : ContinuousMonoidHom A B)`,
you should parametrize over `(F : Type*) [ContinuousMonoidHomClass F A B] (f : F)`.

When you extend this structure, make sure to extend `ContinuousAddMonoidHomClass`. -/
@[to_additive "The type of continuous additive monoid homomorphisms from `A` to `B`."]
structure ContinuousMonoidHom extends A →* B where
  /-- Proof of continuity of the Hom. -/
  continuous_toFun : @Continuous A B _ _ toFun

section

/-- `ContinuousAddMonoidHomClass F A B` states that `F` is a type of continuous additive monoid
homomorphisms.

You should also extend this typeclass when you extend `ContinuousAddMonoidHom`. -/
-- porting note : Changed A B to outParam to help synthesizing order
class ContinuousAddMonoidHomClass (A B : outParam (Type*)) [AddMonoid A] [AddMonoid B]
  [TopologicalSpace A] [TopologicalSpace B] extends AddMonoidHomClass F A B where
  /-- Proof of the continuity of the map. -/
  map_continuous (f : F) : Continuous f

/-- `ContinuousMonoidHomClass F A B` states that `F` is a type of continuous additive monoid
homomorphisms.

You should also extend this typeclass when you extend `ContinuousMonoidHom`. -/
-- porting note : Changed A B to outParam to help synthesizing order
@[to_additive]
class ContinuousMonoidHomClass (A B : outParam (Type*)) [Monoid A] [Monoid B]
    [TopologicalSpace A] [TopologicalSpace B] extends MonoidHomClass F A B where
  /-- Proof of the continuity of the map. -/
  map_continuous (f : F) : Continuous f

end

/-- Reinterpret a `ContinuousMonoidHom` as a `MonoidHom`. -/
add_decl_doc ContinuousMonoidHom.toMonoidHom

/-- Reinterpret a `ContinuousAddMonoidHom` as an `AddMonoidHom`. -/
add_decl_doc ContinuousAddMonoidHom.toAddMonoidHom

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) ContinuousMonoidHomClass.toContinuousMapClass
    [ContinuousMonoidHomClass F A B] : ContinuousMapClass F A B :=
  { ‹ContinuousMonoidHomClass F A B› with }

namespace ContinuousMonoidHom

variable {A B C D E}

@[to_additive]
instance ContinuousMonoidHom.ContinuousMonoidHomClass :
  ContinuousMonoidHomClass (ContinuousMonoidHom A B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨ _ , _ ⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨ _ , _ ⟩, _⟩, _⟩ := g
    congr

  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_continuous f := f.continuous_toFun

/-- Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun`
directly. -/
@[to_additive
      "Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun`."]
instance : CoeFun (ContinuousMonoidHom A B) fun _ => A → B :=
  FunLike.hasCoeToFun

@[to_additive (attr := ext)]
theorem ext {f g : ContinuousMonoidHom A B} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h

/-- Reinterpret a `ContinuousMonoidHom` as a `ContinuousMap`. -/
@[to_additive "Reinterpret a `ContinuousAddMonoidHom` as a `ContinuousMap`."]
def toContinuousMap (f : ContinuousMonoidHom A B) : C(A, B) :=
  { f with }

@[to_additive]
theorem toContinuousMap_injective : Injective (toContinuousMap : _ → C(A, B)) := fun f g h =>
  ext <| by convert FunLike.ext_iff.1 h

-- porting note: Removed simps because given definition is not a constructor application
/-- Construct a `ContinuousMonoidHom` from a `Continuous` `MonoidHom`. -/
@[to_additive "Construct a `ContinuousAddMonoidHom` from a `Continuous` `AddMonoidHom`."]
def mk' (f : A →* B) (hf : Continuous f) : ContinuousMonoidHom A B :=
  { f with continuous_toFun := (hf : Continuous f.toFun)}

/-- Composition of two continuous homomorphisms. -/
@[to_additive (attr := simps!) "Composition of two continuous homomorphisms."]
def comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) : ContinuousMonoidHom A C :=
  mk' (g.toMonoidHom.comp f.toMonoidHom) (g.continuous_toFun.comp f.continuous_toFun)

/-- Product of two continuous homomorphisms on the same space. -/
@[to_additive (attr := simps!) "Product of two continuous homomorphisms on the same space."]
def prod (f : ContinuousMonoidHom A B) (g : ContinuousMonoidHom A C) :
    ContinuousMonoidHom A (B × C) :=
  mk' (f.toMonoidHom.prod g.toMonoidHom) (f.continuous_toFun.prod_mk g.continuous_toFun)

/-- Product of two continuous homomorphisms on different spaces. -/
@[to_additive (attr := simps!) "Product of two continuous homomorphisms on different spaces."]
def prod_map (f : ContinuousMonoidHom A C) (g : ContinuousMonoidHom B D) :
    ContinuousMonoidHom (A × B) (C × D) :=
  mk' (f.toMonoidHom.prodMap g.toMonoidHom) (f.continuous_toFun.prod_map g.continuous_toFun)

variable (A B C D E)

/-- The trivial continuous homomorphism. -/
@[to_additive (attr := simps!) "The trivial continuous homomorphism."]
def one : ContinuousMonoidHom A B :=
  mk' 1 continuous_const

@[to_additive]
instance : Inhabited (ContinuousMonoidHom A B) :=
  ⟨one A B⟩

/-- The identity continuous homomorphism. -/
@[to_additive (attr := simps!) "The identity continuous homomorphism."]
def id : ContinuousMonoidHom A A :=
  mk' (MonoidHom.id A) continuous_id

/-- The continuous homomorphism given by projection onto the first factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by projection onto the first factor."]
def fst : ContinuousMonoidHom (A × B) A :=
  mk' (MonoidHom.fst A B) continuous_fst

/-- The continuous homomorphism given by projection onto the second factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by projection onto the second factor."]
def snd : ContinuousMonoidHom (A × B) B :=
  mk' (MonoidHom.snd A B) continuous_snd

/-- The continuous homomorphism given by inclusion of the first factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by inclusion of the first factor."]
def inl : ContinuousMonoidHom A (A × B) :=
  prod (id A) (one A B)

/-- The continuous homomorphism given by inclusion of the second factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by inclusion of the second factor."]
def inr : ContinuousMonoidHom B (A × B) :=
  prod (one B A) (id B)

/-- The continuous homomorphism given by the diagonal embedding. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by the diagonal embedding."]
def diag : ContinuousMonoidHom A (A × A) :=
  prod (id A) (id A)

/-- The continuous homomorphism given by swapping components. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by swapping components."]
def swap : ContinuousMonoidHom (A × B) (B × A) :=
  prod (snd A B) (fst A B)

/-- The continuous homomorphism given by multiplication. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by addition."]
def mul : ContinuousMonoidHom (E × E) E :=
  mk' mulMonoidHom continuous_mul

/-- The continuous homomorphism given by inversion. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by negation."]
def inv : ContinuousMonoidHom E E :=
  mk' invMonoidHom continuous_inv

variable {A B C D E}

/-- Coproduct of two continuous homomorphisms to the same space. -/
@[to_additive (attr := simps!) "Coproduct of two continuous homomorphisms to the same space."]
def coprod (f : ContinuousMonoidHom A E) (g : ContinuousMonoidHom B E) :
    ContinuousMonoidHom (A × B) E :=
  (mul E).comp (f.prod_map g)

@[to_additive]
instance : CommGroup (ContinuousMonoidHom A E) where
  mul f g := (mul E).comp (f.prod g)
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

@[to_additive]
theorem embedding_toContinuousMap :
    Embedding (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) :=
  ⟨inducing_toContinuousMap A B, toContinuousMap_injective⟩

@[to_additive]
theorem closedEmbedding_toContinuousMap [ContinuousMul B] [T2Space B] :
    ClosedEmbedding (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) :=
  ⟨embedding_toContinuousMap A B,
    ⟨by
      suffices
        Set.range (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) =
          ({ f | f '' {1} ⊆ {1}ᶜ } ∪
              ⋃ (x) (y) (U) (V) (W) (_ : IsOpen U) (_ : IsOpen V) (_ : IsOpen W) (_ :
                Disjoint (U * V) W),
                { f | f '' {x} ⊆ U } ∩ { f | f '' {y} ⊆ V } ∩ { f | f '' {x * y} ⊆ W } :
                  Set C(A , B))ᶜ by
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
          ⟨fun h => h (map_one f), fun x y U V W _hU _hV _hW h ⟨⟨hfU, hfV⟩, hfW⟩ =>
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
          isOpen_prod_iff.mp (hUV.preimage hB) (f x) (f y) hfUV
        refine' ⟨x, y, U, V, W, hU, hV, hW, h.mono_left _, ⟨hfU, hfV⟩, hfW⟩
        rintro _ ⟨x, y, hx : (x, y).1 ∈ U, hy : (x, y).2 ∈ V, rfl⟩
        exact h' ⟨hx, hy⟩⟩⟩

variable {A B C D E}

@[to_additive]
instance [T2Space B] : T2Space (ContinuousMonoidHom A B) :=
  (embedding_toContinuousMap A B).t2Space

@[to_additive]
instance : TopologicalGroup (ContinuousMonoidHom A E) :=
  let hi := inducing_toContinuousMap A E
  let hc := hi.continuous
  { continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (Continuous.prod_map hc hc))
    continuous_inv := hi.continuous_iff.mpr (continuous_inv.comp hc) }

@[to_additive]
theorem continuous_of_continuous_uncurry {A : Type*} [TopologicalSpace A]
    (f : A → ContinuousMonoidHom B C) (h : Continuous (Function.uncurry fun x y => f x y)) :
    Continuous f :=
  (inducing_toContinuousMap _ _).continuous_iff.mpr
    (ContinuousMap.continuous_of_continuous_uncurry _ h)

@[to_additive]
theorem continuous_comp [LocallyCompactSpace B] :
    Continuous fun f : ContinuousMonoidHom A B × ContinuousMonoidHom B C => f.2.comp f.1 :=
  (inducing_toContinuousMap A C).continuous_iff.2 <|
    ContinuousMap.continuous_comp'.comp
      ((inducing_toContinuousMap A B).prod_map (inducing_toContinuousMap B C)).continuous

@[to_additive]
theorem continuous_comp_left (f : ContinuousMonoidHom A B) :
    Continuous fun g : ContinuousMonoidHom B C => g.comp f :=
  (inducing_toContinuousMap A C).continuous_iff.2 <|
    f.toContinuousMap.continuous_comp_left.comp (inducing_toContinuousMap B C).continuous

@[to_additive]
theorem continuous_comp_right (f : ContinuousMonoidHom B C) :
    Continuous fun g : ContinuousMonoidHom A B => f.comp g :=
  (inducing_toContinuousMap A C).continuous_iff.2 <|
    f.toContinuousMap.continuous_comp.comp (inducing_toContinuousMap A B).continuous

variable (E)

/-- `ContinuousMonoidHom _ f` is a functor. -/
@[to_additive "`ContinuousAddMonoidHom _ f` is a functor."]
def compLeft (f : ContinuousMonoidHom A B) :
    ContinuousMonoidHom (ContinuousMonoidHom B E) (ContinuousMonoidHom A E) where
  toFun g := g.comp f
  map_one' := rfl
  map_mul' _g _h := rfl
  continuous_toFun := f.continuous_comp_left

variable (A) {E}

/-- `ContinuousMonoidHom f _` is a functor. -/
@[to_additive "`ContinuousAddMonoidHom f _` is a functor."]
def compRight {B : Type*} [CommGroup B] [TopologicalSpace B] [TopologicalGroup B]
    (f : ContinuousMonoidHom B E) :
    ContinuousMonoidHom (ContinuousMonoidHom A B) (ContinuousMonoidHom A E) where
  toFun g := f.comp g
  map_one' := ext fun _a => map_one f
  map_mul' g h := ext fun a => map_mul f (g a) (h a)
  continuous_toFun := f.continuous_comp_right

end ContinuousMonoidHom



/-- The Pontryagin dual of `A` is the group of continuous homomorphism `A → circle`. -/
def PontryaginDual :=
  ContinuousMonoidHom A circle

-- porting note: `deriving` doesn't derive these instances
instance : TopologicalSpace (PontryaginDual A) :=
  (inferInstance : TopologicalSpace (ContinuousMonoidHom A circle))

instance : T2Space (PontryaginDual A) :=
  (inferInstance : T2Space (ContinuousMonoidHom A circle))

-- porting note: instance is now noncomputable
noncomputable instance : CommGroup (PontryaginDual A) :=
  (inferInstance : CommGroup (ContinuousMonoidHom A circle))

instance : TopologicalGroup (PontryaginDual A) :=
  (inferInstance : TopologicalGroup (ContinuousMonoidHom A circle))

-- porting note: instance is now noncomputable
noncomputable instance : Inhabited (PontryaginDual A) :=
  (inferInstance : Inhabited (ContinuousMonoidHom A circle))


variable {A B C D E}

namespace PontryaginDual

open ContinuousMonoidHom

noncomputable instance : ContinuousMonoidHomClass (PontryaginDual A) A circle :=
  ContinuousMonoidHom.ContinuousMonoidHomClass

/-- `PontryaginDual` is a functor. -/
noncomputable def map (f : ContinuousMonoidHom A B) :
    ContinuousMonoidHom (PontryaginDual B) (PontryaginDual A) :=
  f.compLeft circle

@[simp]
theorem map_apply (f : ContinuousMonoidHom A B) (x : PontryaginDual B) (y : A) :
    map f x y = x (f y) :=
  rfl

@[simp]
theorem map_one : map (one A B) = one (PontryaginDual B) (PontryaginDual A) :=
  ext fun x => ext (fun _y => OneHomClass.map_one x)

@[simp]
theorem map_comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) :
    map (comp g f) = ContinuousMonoidHom.comp (map f) (map g) :=
  ext fun _x => ext fun _y => rfl


@[simp]
nonrec theorem map_mul (f g : ContinuousMonoidHom A E) : map (f * g) = map f * map g :=
  ext fun x => ext fun y => map_mul x (f y) (g y)

variable (A B C D E)

/-- `ContinuousMonoidHom.dual` as a `ContinuousMonoidHom`. -/
noncomputable def mapHom [LocallyCompactSpace E] :
    ContinuousMonoidHom (ContinuousMonoidHom A E)
      (ContinuousMonoidHom (PontryaginDual E) (PontryaginDual A)) where
  toFun := map
  map_one' := map_one
  map_mul' := map_mul
  continuous_toFun := continuous_of_continuous_uncurry _ continuous_comp

end PontryaginDual
