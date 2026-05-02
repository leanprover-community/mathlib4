/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Order.Filter.Cofinite  -- shake: keep (used in notation only)
public import Mathlib.Algebra.Module.Pi

/-!
# Restricted products of sets, groups and rings

We define the **restricted product** of `R : ι → Type*` of types, relative to
a family of subsets `A : (i : ι) → Set (R i)` and a filter `𝓕 : Filter ι`. This
is the set of all `x : Π i, R i` such that the set `{j | x j ∈ A j}` belongs to `𝓕`.
We denote it by `Πʳ i, [R i, A i]_[𝓕]`.

The main case of interest, which we shall refer to as the "classical restricted product",
is that of `𝓕 = cofinite`. Recall that this is the filter of all subsets of `ι`, which are
*cofinite* in the sense that they have finite complement.
Hence, the associated restricted product is the set of all `x : Π i, R i` such that
`x j ∈ A j` for all but finitely many `j`s. We denote it simply by `Πʳ i, [R i, A i]`.

Another notable case is that of the principal filter `𝓕 = 𝓟 s` corresponding to some subset `s`
of `ι`. The associated restricted product `Πʳ i, [R i, A i]_[𝓟 s]` is the set of all
`x : Π i, R i` such that `x j ∈ A j` for all `j ∈ s`. Put another way, this is just
`(Π i ∈ s, A i) × (Π i ∉ s, R i)`, modulo the obvious isomorphism.

We endow these types with the obvious algebraic structures. We also show various compatibility
results.

See also the file `Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean`, which
puts the structure of a topological space on a restricted product of topological spaces.

## Main definitions

* `RestrictedProduct`: the restricted product of a family `R` of types, relative to a family `A` of
  subsets and a filter `𝓕` on the indexing set. This is denoted `Πʳ i, [R i, A i]_[𝓕]`,
  or simply `Πʳ i, [R i, A i]` when `𝓕 = cofinite`.
* `RestrictedProduct.instDFunLike`: interpret an element of `Πʳ i, [R i, A i]_[𝓕]` as an element
  of `Π i, R i` using the `DFunLike` machinery.
* `RestrictedProduct.structureMap`: the inclusion map from `Π i, A i` to `Πʳ i, [R i, A i]_[𝓕]`.

## Notation

* `Πʳ i, [R i, A i]_[𝓕]` is `RestrictedProduct R A 𝓕`.
* `Πʳ i, [R i, A i]` is `RestrictedProduct R A cofinite`.

## Tags

restricted product, adeles, ideles
-/

@[expose] public section

open Set Filter

variable {ι : Type*}
variable (R : ι → Type*) (A : (i : ι) → Set (R i))

/-!
## Definition and elementary maps
-/

/-- The **restricted product** of a family `R : ι → Type*` of types, relative to subsets
`A : (i : ι) → Set (R i)` and the filter `𝓕 : Filter ι`, is the set of all `x : Π i, R i`
such that the set `{j | x j ∈ A j}` belongs to `𝓕`. We denote it by `Πʳ i, [R i, A i]_[𝓕]`.

The most common use case is with `𝓕 = cofinite`, in which case the restricted product is the set
of all `x : Π i, R i` such that `x j ∈ A j` for all but finitely many `j`. We denote it simply
by `Πʳ i, [R i, A i]`.

Similarly, if `S` is a principal filter, the restricted product `Πʳ i, [R i, A i]_[𝓟 s]`
is the set of all `x : Π i, R i` such that `∀ j ∈ S, x j ∈ A j`. -/
def RestrictedProduct (𝓕 : Filter ι) : Type _ := {x : Π i, R i // ∀ᶠ i in 𝓕, x i ∈ A i}

open Batteries.ExtendedBinder

/-- `Πʳ i, [R i, A i]_[𝓕]` is `RestrictedProduct R A 𝓕`. -/
scoped[RestrictedProduct]
notation3 "Πʳ " (...) ", " "[" r:(scoped R => R)", " a:(scoped A => A) "]_[" f "]" =>
  RestrictedProduct r a f

/-- `Πʳ i, [R i, A i]` is `RestrictedProduct R A cofinite`. -/
scoped[RestrictedProduct]
notation3 "Πʳ " (...) ", " "[" r:(scoped R => R)", " a:(scoped A => A) "]" =>
  RestrictedProduct r a cofinite

namespace RestrictedProduct

open scoped RestrictedProduct

variable {𝓕 𝓖 : Filter ι}

instance : DFunLike (Πʳ i, [R i, A i]_[𝓕]) ι R where
  coe x i := x.1 i
  coe_injective' _ _ := Subtype.ext

variable {R A} in
/-- Constructor for `RestrictedProduct`. -/
abbrev mk (x : Π i, R i) (hx : ∀ᶠ i in 𝓕, x i ∈ A i) : Πʳ i, [R i, A i]_[𝓕] :=
  ⟨x, hx⟩

@[simp]
lemma mk_apply (x : Π i, R i) (hx : ∀ᶠ i in 𝓕, x i ∈ A i) (i : ι) :
    (mk x hx) i = x i := rfl

@[ext]
lemma ext {x y : Πʳ i, [R i, A i]_[𝓕]} (h : ∀ i, x i = y i) : x = y :=
  Subtype.ext <| funext h

lemma range_coe :
    range ((↑) : Πʳ i, [R i, A i]_[𝓕] → Π i, R i) = {x | ∀ᶠ i in 𝓕, x i ∈ A i} :=
  Subtype.range_val_subtype

lemma range_coe_principal {S : Set ι} :
    range ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) = S.pi A :=
  range_coe R A

@[simp] lemma eventually (x : Πʳ i, [R i, A i]_[𝓕]) : ∀ᶠ i in 𝓕, x i ∈ A i := x.2

variable (𝓕) in
/-- The *structure map* of the restricted product is the obvious inclusion from `Π i, A i`
into `Πʳ i, [R i, A i]_[𝓕]`. -/
def structureMap (x : Π i, A i) : Πʳ i, [R i, A i]_[𝓕] :=
  ⟨fun i ↦ x i, .of_forall fun i ↦ (x i).2⟩

@[simp]
lemma structureMap_apply {x : Π i, A i} (i : ι) :
    structureMap R A 𝓕 x i = x i :=
  rfl

/-- If `𝓕 ≤ 𝓖`, the restricted product `Πʳ i, [R i, A i]_[𝓖]` is naturally included in
`Πʳ i, [R i, A i]_[𝓕]`. This is the corresponding map. -/
def inclusion (h : 𝓕 ≤ 𝓖) (x : Πʳ i, [R i, A i]_[𝓖]) :
    Πʳ i, [R i, A i]_[𝓕] :=
  ⟨x, x.2.filter_mono h⟩

@[simp]
lemma inclusion_apply (h : 𝓕 ≤ 𝓖) {x : Πʳ i, [R i, A i]_[𝓖]} (i : ι) :
    inclusion R A h x i = x i :=
  rfl

variable (𝓕) in
lemma inclusion_eq_id : inclusion R A (le_refl 𝓕) = id := rfl

lemma exists_inclusion_eq_of_eventually (h : 𝓕 ≤ 𝓖) {x : Πʳ i, [R i, A i]_[𝓕]}
    (hx𝓖 : ∀ᶠ i in 𝓖, x i ∈ A i) :
    ∃ x' : Πʳ i, [R i, A i]_[𝓖], inclusion R A h x' = x :=
  ⟨⟨x.1, hx𝓖⟩, rfl⟩

lemma exists_structureMap_eq_of_forall {x : Πʳ i, [R i, A i]_[𝓕]}
    (hx : ∀ i, x.1 i ∈ A i) :
    ∃ x' : Π i, A i, structureMap R A 𝓕 x' = x :=
  ⟨fun i ↦ ⟨x i, hx i⟩, rfl⟩

lemma range_inclusion (h : 𝓕 ≤ 𝓖) :
    Set.range (inclusion R A h) = {x | ∀ᶠ i in 𝓖, x i ∈ A i} :=
  subset_antisymm (range_subset_iff.mpr fun x ↦ x.2)
    (fun _ hx ↦ mem_range.mpr <| exists_inclusion_eq_of_eventually R A h hx)

@[simp]
lemma coe_comp_inclusion (h : 𝓕 ≤ 𝓖) :
    DFunLike.coe ∘ inclusion R A h = DFunLike.coe :=
  rfl

lemma image_coe_preimage_inclusion_subset (h : 𝓕 ≤ 𝓖)
    (U : Set Πʳ i, [R i, A i]_[𝓕]) : (⇑) '' inclusion R A h ⁻¹' U ⊆ (⇑) '' U :=
  fun _ ⟨x, hx, hx'⟩ ↦ ⟨inclusion R A h x, hx, hx'⟩

lemma range_structureMap :
    Set.range (structureMap R A 𝓕) = {f | ∀ i, f.1 i ∈ A i} :=
  subset_antisymm (range_subset_iff.mpr fun x i ↦ (x i).2)
    (fun _ hx ↦ mem_range.mpr <| exists_structureMap_eq_of_forall R A hx)

@[simp]
lemma coe_comp_structureMap :
    DFunLike.coe ∘ structureMap R A 𝓕 = fun x i ↦ (x i).val :=
  rfl

section Algebra
/-!
## Algebraic instances on restricted products

In this section, we endow the restricted product with its algebraic instances.
To avoid any unnecessary coercions, we use subobject classes for the subset `B i` of each `R i`.
-/

variable {S : ι → Type*} -- subobject type
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}

@[to_additive]
instance [Π i, One (R i)] [∀ i, OneMemClass (S i) (R i)] : One (Πʳ i, [R i, B i]_[𝓕]) where
  one := ⟨fun _ ↦ 1, .of_forall fun _ ↦ one_mem _⟩

@[to_additive (attr := simp)]
lemma one_apply [Π i, One (R i)] [∀ i, OneMemClass (S i) (R i)] (i : ι) :
    (1 : Πʳ i, [R i, B i]_[𝓕]) i = 1 :=
  rfl

@[to_additive]
instance [Π i, Inv (R i)] [∀ i, InvMemClass (S i) (R i)] : Inv (Πʳ i, [R i, B i]_[𝓕]) where
  inv x := ⟨fun i ↦ (x i)⁻¹, x.2.mono fun _ ↦ inv_mem⟩

@[to_additive (attr := simp)]
lemma inv_apply [Π i, Inv (R i)] [∀ i, InvMemClass (S i) (R i)]
    (x : Πʳ i, [R i, B i]_[𝓕]) (i : ι) : (x⁻¹) i = (x i)⁻¹ :=
  rfl

@[to_additive]
instance [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)] : Mul (Πʳ i, [R i, B i]_[𝓕]) where
  mul x y := ⟨fun i ↦ x i * y i, y.2.mp (x.2.mono fun _ ↦ mul_mem)⟩

@[to_additive (attr := simp)]
lemma mul_apply [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)]
    (x y : Πʳ i, [R i, B i]_[𝓕]) (i : ι) : (x * y) i = x i * y i :=
  rfl

@[to_additive]
instance {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)] :
    SMul G (Πʳ i, [R i, B i]_[𝓕]) where
  smul g x := ⟨fun i ↦ g • (x i), x.2.mono fun _ ↦ SMulMemClass.smul_mem g⟩

@[to_additive (attr := simp)]
lemma smul_apply {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)] (g : G)
    (x : Πʳ i, [R i, B i]_[𝓕]) (i : ι) : (g • x) i = g • x i :=
  rfl

@[to_additive]
instance [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Div (Πʳ i, [R i, B i]_[𝓕]) where
  div x y := ⟨fun i ↦ x i / y i, y.2.mp (x.2.mono fun _ ↦ div_mem)⟩

@[to_additive (attr := simp)]
lemma div_apply [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)]
    (x y : Πʳ i, [R i, B i]_[𝓕]) (i : ι) : (x / y) i = x i / y i :=
  rfl

@[to_additive]
instance instPow [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    Pow (Πʳ i, [R i, B i]_[𝓕]) ℕ where
  pow x n := ⟨fun i ↦ x i ^ n, x.2.mono fun _ hi ↦ pow_mem hi n⟩

@[to_additive]
lemma pow_apply [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)]
    (x : Πʳ i, [R i, B i]_[𝓕]) (n : ℕ) (i : ι) : (x ^ n) i = x i ^ n :=
  rfl

@[to_additive]
instance [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    Monoid (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.monoid _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[to_additive]
instance [Π i, CommMonoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    CommMonoid (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.commMonoid _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[to_additive]
instance instZPow [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Pow (Πʳ i, [R i, B i]_[𝓕]) ℤ where
  pow x n := ⟨fun i ↦ x i ^ n, x.2.mono fun _ hi ↦ zpow_mem hi n⟩

@[to_additive]
lemma zpow_apply [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)]
    (x : Πʳ i, [R i, B i]_[𝓕]) (n : ℤ) (i : ι) : (x ^ n) i = x i ^ n :=
  rfl

instance [Π i, AddMonoidWithOne (R i)] [∀ i, AddSubmonoidWithOneClass (S i) (R i)] :
    NatCast (Πʳ i, [R i, B i]_[𝓕]) where
  natCast n := ⟨fun _ ↦ n, .of_forall fun _ ↦ natCast_mem _ n⟩

@[to_additive]
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Group (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.group _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[to_additive]
instance [Π i, CommGroup (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    CommGroup (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.commGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    IntCast (Πʳ i, [R i, B i]_[𝓕]) where
  intCast n := ⟨fun _ ↦ n, .of_forall fun _ ↦ intCast_mem _ n⟩

instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    Ring (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.ring _ rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

instance [Π i, CommRing (R i)] [∀ i, SubringClass (S i) (R i)] :
    CommRing (Πʳ i, [R i, B i]_[𝓕]) where
  mul_comm _ _ := DFunLike.coe_injective <| funext (fun _ ↦ mul_comm _ _)

variable {R} in
/-- The coercion from the restricted product of monoids `A i` to the (normal) product
is a monoid homomorphism. -/
@[to_additive /-- The coercion from the restricted product of additive monoids `A i` to the
(normal) product is an additive monoid homomorphism. -/]
def coeMonoidHom [∀ i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    Πʳ i, [R i, B i]_[𝓕] →* Π i, R i where
  toFun := (↑)
  map_one' := rfl
  map_mul' _ _ := rfl

instance {R₀ : Type*} [Semiring R₀] [Π i, AddCommMonoid (R i)] [Π i, Module R₀ (R i)]
    [∀ i, AddSubmonoidClass (S i) (R i)] [∀ i, SMulMemClass (S i) R₀ (R i)] :
  Module R₀ (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.module R₀ (M := Π i, R i) coeAddMonoidHom (fun _ _ ↦ rfl)

end Algebra

section eval

variable {S : ι → Type*}
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}

/-- `RestrictedProduct.evalMonoidHom j` is the monoid homomorphism from the restricted
product `Πʳ i, [R i, B i]_[𝓕]` to the component `R j`.
-/
@[to_additive /-- `RestrictedProduct.evalAddMonoidHom j` is the monoid homomorphism from the
restricted product `Πʳ i, [R i, B i]_[𝓕]` to the component `R j`. -/]
def evalMonoidHom (j : ι) [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    (Πʳ i, [R i, B i]_[𝓕]) →* R j where
  toFun x := x j
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
lemma evalMonoidHom_apply [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)]
    (x : Πʳ i, [R i, B i]_[𝓕]) (j : ι) : evalMonoidHom R j x = x j :=
  rfl

/-- `RestrictedProduct.evalRingHom j` is the ring homomorphism from the restricted
product `Πʳ i, [R i, B i]_[𝓕]` to the component `R j`.
-/
def evalRingHom (j : ι) [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    (Πʳ i, [R i, B i]_[𝓕]) →+* R j where
  __ := evalMonoidHom R j
  __ := evalAddMonoidHom R j

@[simp]
lemma evalRingHom_apply [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)]
    (x : Πʳ i, [R i, B i]_[𝓕]) (j : ι) : evalRingHom R j x = x j :=
  rfl

end eval

section map

variable {ι₁ ι₂ : Type*}
variable (R₁ : ι₁ → Type*) (R₂ : ι₂ → Type*)
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}
variable {S₁ : ι₁ → Type*} {S₂ : ι₂ → Type*}
variable [Π i, SetLike (S₁ i) (R₁ i)] [Π j, SetLike (S₂ j) (R₂ j)]
variable {B₁ : Π i, S₁ i} {B₂ : Π j, S₂ j}
variable (f : ι₂ → ι₁) (hf : Tendsto f 𝓕₂ 𝓕₁)

section set

variable (φ : ∀ j, R₁ (f j) → R₂ j) (hφ : ∀ᶠ j in 𝓕₂, MapsTo (φ j) (A₁ (f j)) (A₂ j))

/--
Given two restricted products `Πʳ (i : ι₁), [R₁ i, A₁ i]_[𝓕₁]` and `Πʳ (j : ι₂), [R₂ j, A₂ j]_[𝓕₂]`,
`RestrictedProduct.mapAlong` gives a function between them. The data needed is a
function `f : ι₂ → ι₁` such that `𝓕₂` tends to `𝓕₁` along `f`, and functions `φ j : R₁ (f j) → R₂ j`
sending `A₁ (f j)` into `A₂ j` for an `𝓕₂`-large set of `j`'s.

See also `mapAlongMonoidHom`, `mapAlongAddMonoidHom` and `mapAlongRingHom` for variants.
-/
def mapAlong (x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) : Πʳ j, [R₂ j, A₂ j]_[𝓕₂] :=
  ⟨fun j ↦ φ j (x (f j)), by
  filter_upwards [hf.eventually x.2, hφ] using fun _ h1 h2 ↦ h2 h1⟩

@[simp]
lemma mapAlong_apply (x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) (j : ι₂) :
    x.mapAlong R₁ R₂ f hf φ hφ j = φ j (x (f j)) :=
  rfl

-- variant of `mapAlong` where the index set is constant

/-- The maps between restricted products over a fixed index type,
given maps on the factors. -/
def map {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)} (φ : (i : ι) → G i → H i)
    (hφ : ∀ᶠ i in 𝓕, MapsTo (φ i) (C i) (D i))
    (x : Πʳ i, [G i, C i]_[𝓕]) : (Πʳ i, [H i, D i]_[𝓕]) :=
  mapAlong G H id Filter.tendsto_id φ hφ x

@[simp]
lemma map_apply {G H : ι → Type*} {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)} (φ : (i : ι) → G i → H i)
    (hφ : ∀ᶠ i in 𝓕, MapsTo (φ i) (C i) (D i))
    (x : Πʳ i, [G i, C i]_[𝓕]) (j : ι) :
    x.map φ hφ j = φ j (x j) :=
  rfl

end set

section monoid

variable [Π i, Monoid (R₁ i)] [Π i, Monoid (R₂ i)] [∀ i, SubmonoidClass (S₁ i) (R₁ i)]
    [∀ i, SubmonoidClass (S₂ i) (R₂ i)] (φ : ∀ j, R₁ (f j) →* R₂ j)
    (hφ : ∀ᶠ j in 𝓕₂, MapsTo (φ j) (B₁ (f j)) (B₂ j))

/--
Given two restricted products `Πʳ (i : ι₁), [R₁ i, B₁ i]_[𝓕₁]` and `Πʳ (j : ι₂), [R₂ j, B₂ j]_[𝓕₂]`
of monoids, `RestrictedProduct.mapAlongMonoidHom` gives a monoid homomorphism between them.
The data needed is a function `f : ι₂ → ι₁` such that `𝓕₂` tends to `𝓕₁` along `f`, and monoid
homomorphisms `φ j : R₁ (f j) → R₂ j` sending `B₁ (f j)` into `B₂ j` for an `𝓕₂`-large set of `j`'s.
-/
@[to_additive
/-- Given two restricted products `Πʳ (i : ι₁), [R₁ i, B₁ i]_[𝓕₁]` and
`Πʳ (j : ι₂), [R₂ j, B₂ j]_[𝓕₂]` of additive monoids, `RestrictedProduct.mapAlongAddMonoidHom`
gives an additive monoid homomorphism between them. The data needed is a function `f : ι₂ → ι₁` such
that `𝓕₂` tends to `𝓕₁` along `f`, and additive monoid homomorphisms `φ j : R₁ (f j) → R₂ j`
sending `B₁ (f j)` into `B₂ j` for an `𝓕₂`-large set of `j`'s. -/]
def mapAlongMonoidHom : Πʳ i, [R₁ i, B₁ i]_[𝓕₁] →* Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  toFun := mapAlong R₁ R₂ f hf (fun j r ↦ φ j r) hφ
  map_one' := by
    ext i
    exact map_one (φ i)
  map_mul' x y := by
    ext i
    exact map_mul (φ i) _ _

@[to_additive (attr := simp)]
lemma mapAlongMonoidHom_apply (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂) :
    x.mapAlongMonoidHom R₁ R₂ f hf φ hφ j = φ j (x (f j)) :=
  rfl

end monoid

section ring

variable [Π i, Ring (R₁ i)] [Π i, Ring (R₂ i)] [∀ i, SubringClass (S₁ i) (R₁ i)]
    [∀ i, SubringClass (S₂ i) (R₂ i)] (φ : ∀ j, R₁ (f j) →+* R₂ j)
    (hφ : ∀ᶠ j in 𝓕₂, MapsTo (φ j) (B₁ (f j)) (B₂ j))

/--
Given two restricted products of rings `Πʳ (i : ι₁), [R₁ i, B₁ i]_[𝓕₁]` and
`Πʳ (j : ι₂), [R₂ j, B₂ j]_[𝓕₂]`, `RestrictedProduct.mapAlongRingHom` gives a
ring homomorphism between them. The data needed is a
function `f : ι₂ → ι₁` such that `𝓕₂` tends to `𝓕₁` along `f`, and ring homomorphisms
`φ j : R₁ (f j) → R₂ j` sending `B₁ (f j)` into `B₂ j` for an `𝓕₂`-large set of `j`'s.
-/
def mapAlongRingHom : Πʳ i, [R₁ i, B₁ i]_[𝓕₁] →+* Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  __ := mapAlongMonoidHom R₁ R₂ f hf (fun j ↦ φ j) hφ
  __ := mapAlongAddMonoidHom R₁ R₂ f hf (fun j ↦ φ j) hφ

@[simp]
lemma mapAlongRingHom_apply (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂) :
    x.mapAlongRingHom R₁ R₂ f hf φ hφ j = φ j (x (f j)) :=
  rfl

end ring

end map

section single

variable {S : ι → Type*} {G : ι → Type*} [Π i, SetLike (S i) (G i)] (A : (i : ι) → (S i))
  [DecidableEq ι]

section one

variable [∀ i, One (G i)] [∀ i, OneMemClass (S i) (G i)] (i : ι)

/-- The function supported at `i`, with value `x` there, and `1` elsewhere. -/
@[to_additive
/-- The function supported at `i`, with value `x` there, and `0` elsewhere. -/]
def mulSingle (x : G i) : Πʳ i, [G i, A i] where
  val := Pi.mulSingle i x
  property := by
    filter_upwards [show {i}ᶜ ∈ Filter.cofinite by simp]
    simp_all

@[to_additive (attr := simp)]
lemma coe_mulSingle_apply (x : G i) (j : ι) : mulSingle A i x j = Pi.mulSingle i x j := rfl
@[to_additive] lemma comp_mulSingle : (↑) ∘ mulSingle A i = Pi.mulSingle (M := G) i := by ext; simp

@[to_additive]
lemma mulSingle_injective : (mulSingle A i).Injective :=
  (comp_mulSingle A _ ▸ Pi.mulSingle_injective i).of_comp

@[to_additive]
lemma mulSingle_inj {x y : G i} : mulSingle A i x = mulSingle A i y ↔ x = y :=
  (mulSingle_injective A i).eq_iff

@[to_additive]
lemma mulSingle_eq_same (r : G i) : mulSingle A i r i = r := Pi.mulSingle_eq_same i r

@[to_additive]
lemma mulSingle_eq_of_ne {i j : ι} (r : G i) (h : j ≠ i) : mulSingle A i r j = 1 :=
  Pi.mulSingle_eq_of_ne h r

@[to_additive]
lemma mulSingle_eq_of_ne' {i j : ι} (r : G i) (h : i ≠ j) : mulSingle A i r j = 1 :=
  Pi.mulSingle_eq_of_ne' h r

@[to_additive (attr := simp)]
lemma mulSingle_one : mulSingle A i 1 = 1 := by ext; simp

@[to_additive (attr := simp)]
lemma mulSingle_eq_one_iff {x : G i} : mulSingle A i x = 1 ↔ x = 1 :=
  Subtype.ext_iff.trans Pi.mulSingle_eq_one_iff

@[to_additive]
lemma mulSingle_ne_one_iff {x : G i} : mulSingle A i x ≠ 1 ↔ x ≠ 1 :=
  Subtype.coe_ne_coe.symm.trans Pi.mulSingle_ne_one_iff

end one

@[to_additive]
lemma mulSingle_mul [∀ i, MulOneClass (G i)] [∀ i, OneMemClass (S i) (G i)]
    [∀ i, MulMemClass (S i) (G i)] (i : ι) (r s : G i) :
    mulSingle A i (r * s) = mulSingle A i r * mulSingle A i s := by
  ext; simp [Pi.mulSingle_mul]

@[simp]
lemma mul_single [∀ i, MulZeroClass (G i)] [∀ i, ZeroMemClass (S i) (G i)]
    [∀ i, MulMemClass (S i) (G i)] (i : ι) (r : G i) (x : Πʳ i, [G i, A i]) :
    single A i (x i * r) = x * single A i r := by
  ext j
  rcases eq_or_ne i j with rfl | hne; · simp
  simp [single_eq_of_ne' A _ hne]

@[simp]
lemma single_mul [∀ i, MulZeroClass (G i)] [∀ i, ZeroMemClass (S i) (G i)]
    [∀ i, MulMemClass (S i) (G i)] (i : ι) (r : G i) (x : Πʳ i, [G i, A i]) :
    single A i (r * x i) = single A i r * x := by
  ext j
  rcases eq_or_ne i j with rfl | hne; · simp
  simp [single_eq_of_ne' A _ hne]

@[to_additive]
lemma mulSingle_inv [∀ i, Group (G i)] [∀ i, SubgroupClass (S i) (G i)]
    (i : ι) (r : G i) :
    mulSingle A i r⁻¹ = (mulSingle A i r)⁻¹ := by
  ext; simp [Pi.mulSingle_inv]

@[to_additive]
lemma mulSingle_div [∀ i, Group (G i)] [∀ i, SubgroupClass (S i) (G i)]
    (i : ι) (r s : G i) :
    mulSingle A i (r / s) = mulSingle A i r / mulSingle A i s := by
  ext; simp [Pi.mulSingle_div]

@[to_additive]
lemma mulSingle_pow [∀ i, Monoid (G i)] [∀ i, SubmonoidClass (S i) (G i)]
    (i : ι) (r : G i) (n : ℕ) :
    mulSingle A i (r ^ n) = mulSingle A i r ^ n := by
  ext; simp [Pi.mulSingle_pow, RestrictedProduct.pow_apply]

@[to_additive]
lemma mulSingle_zpow [∀ i, Group (G i)] [∀ i, SubgroupClass (S i) (G i)]
    (i : ι) (r : G i) (n : ℤ) :
    mulSingle A i (r ^ n) = mulSingle A i r ^ n := by
  ext; simp [Pi.mulSingle_zpow, RestrictedProduct.zpow_apply]

end single

end RestrictedProduct
