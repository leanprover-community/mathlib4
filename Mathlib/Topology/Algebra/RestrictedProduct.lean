/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Restricted products of sets, groups and rings, and their topology

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

We endow these types with the obvious algebraic structures, as well as their natural topology,
which we describe below. We also show various compatibility results.

In particular, with the theory of adeles in mind, we show that if each `R i` is a locally compact
topological ring with open subring `A i`, and if all but finitely many of the `A i`s are also
compact, then `Πʳ i, [R i, A i]` is a locally compact topological ring.

## Main definitions

* `RestrictedProduct`: the restricted product of a family `R` of types, relative to a family `A` of
subsets and a filter `𝓕` on the indexing set. This is denoted `Πʳ i, [R i, A i]_[𝓕]`,
or simply `Πʳ i, [R i, A i]` when `𝓕 = cofinite`.
* `RestrictedProduct.instDFunLike`: interpret an element of `Πʳ i, [R i, A i]_[𝓕]` as an element
of `Π i, R i` using the `DFunLike` machinery.
* `RestrictedProduct.structureMap`: the inclusion map from `Π i, A i` to `Πʳ i, [R i, A i]_[𝓕]`.
* `RestrictedProduct.topologicalSpace`: the `TopologicalSpace` instance on `Πʳ i, [R i, A i]_[𝓕]`.

## Topology on the restricted product

The topology on the restricted product `Πʳ i, [R i, A i]_[𝓕]` is defined in the following way:
1. If `𝓕` is some principal filter `𝓟 s`, recall that `Πʳ i, [R i, A i]_[𝓟 s]` is canonically
identified with `(Π i ∈ s, A i) × (Π i ∉ s, R i)`. We endow it with the product topology,
which is also the topology induced from the full product `Π i, R i`.
2. In general, we note that `𝓕` is the infimum of the principal filters coarser than `𝓕`. We
then endow `Πʳ i, [R i, A i]_[𝓕]` with the inductive limit / final topology associated to the
inclusion maps `Πʳ i, [R i, A i]_[𝓟 s] → Πʳ i, [R i, A i]_[𝓕]` where `𝓕 ≤ 𝓟 s`.

In particular:
* On the classical restricted product, with respect to the cofinite filter, this corresponds to
taking the inductive limit of the `Πʳ i, [R i, A i]_[𝓟 s]` over all *cofinite* sets `s : Set ι`.
* If `𝓕 = 𝓟 s` is a principal filter, this second step clearly does not change the topology, since
`s` belongs to the indexing set of the inductive limit.

Taking advantage of that second remark, we do not actually declare an instance specific to
principal filters. Instead, we provide directly the general instance (corresponding to step 2 above)
as `RestrictedProduct.topologicalSpace`. We then prove that, for a principal filter, the
map to the full product is an inducing (`RestrictedProduct.isEmbedding_coe_of_principal`),
and that the topology for a general `𝓕` is indeed the expected inductive limit
(`RestrictedProduct.topologicalSpace_eq_iSup`).

## Main statements

* `RestrictedProduct.isEmbedding_coe_of_principal`: for any set `S`, `Πʳ i, [R i, A i]_[𝓟 S]`
is endowed with the subset topology coming from `Π i, R i`.
* `RestrictedProduct.topologicalSpace_eq_iSup`: the topology on `Πʳ i, [R i, A i]_[𝓕]` is the
inductive limit / final topology associated to the natural maps
`Πʳ i, [R i, A i]_[𝓟 S] → Πʳ i, [R i, A i]_[𝓕]`, where `𝓕 ≤ 𝓟 S`.
* `RestrictedProduct.continuous_dom`: a map from `Πʳ i, [R i, A i]_[𝓕]` is continuous
*if and only if* its restriction to each `Πʳ i, [R i, A i]_[𝓟 s]` (with `𝓕 ≤ 𝓟 s`) is continuous.
* `RestrictedProduct.continuous_dom_prod_left`: assume that each `A i` is an **open** subset of
`R i`. Then, for any topological space `Y`, a map from `Y × Πʳ i, [R i, A i]` is continuous
*if and only if* its restriction to each `Y × Πʳ i, [R i, A i]_[𝓟 S]` (with `S` cofinite)
is continuous.

* `RestrictedProduct.isTopologicalGroup`: if each `R i` is a topological group and each `A i` is an
open subgroup of `R i`, then `Πʳ i, [R i, A i]` is a topological group.
* `RestrictedProduct.isTopologicalRing`: if each `R i` is a topological ring and each `A i` is an
open subring of `R i`, then `Πʳ i, [R i, A i]` is a topological ring.
* `RestrictedProduct.continuousSMul`: if some topological monoid `G` acts on each `M i`, and each
`A i` is stable for that action, then the natural action of `G` on `Πʳ i, [M i, A i]` is also
continuous. In particular, if each `M i` is a topological `R`-module and each `A i` is an open
sub-`R`-module of `M i`, then `Πʳ i, [M i, A i]` is a topological `R`-module.

* `RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite`:  if each `R i` is weakly locally
compact, each `A i` is open, and all but finitely many `A i`s are also compact, then the
restricted product `Πʳ i, [R i, A i]` is weakly locally compact.
* `RestrictedProduct.locallyCompactSpace_of_group`: assume that each `R i` is a locally compact
group with `A i` an open subgroup. Assume also that all but finitely many `A i`s are compact.
Then the restricted product `Πʳ i, [R i, A i]` is a locally compact group.

## Notation

* `Πʳ i, [R i, A i]_[𝓕]` is `RestrictedProduct R A 𝓕`.
* `Πʳ i, [R i, A i]` is `RestrictedProduct R A cofinite`.

## Implementation details

Outside of principal filters and the cofinite filter, the topology we define on the restricted
product does not seem well-behaved. While declaring a single instance is practical, it may conflict
with more interesting topologies in some other cases. Thus, future contributions should not
restrain from specializing these instances to principal and cofinite filters if necessary.

## Tags

restricted product, adeles, ideles
-/

open Set Topology Filter

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
notation3 "Πʳ "(...)", ""["r:(scoped R => R)", "a:(scoped A => A)"]_[" f "]" =>
  RestrictedProduct r a f

/-- `Πʳ i, [R i, A i]` is `RestrictedProduct R A cofinite`. -/
scoped[RestrictedProduct]
notation3"Πʳ "(...)", ""["r:(scoped R => R)", "a:(scoped A => A)"]" =>
  RestrictedProduct r a cofinite

namespace RestrictedProduct

open scoped RestrictedProduct

variable {𝓕 𝓖 : Filter ι} {S T : Set ι}

instance : DFunLike (Πʳ i, [R i, A i]_[𝓕]) ι R where
  coe x i := x.1 i
  coe_injective' _ _ := Subtype.ext

lemma range_coe :
    range ((↑) : Πʳ i, [R i, A i]_[𝓕] → Π i, R i) = {x | ∀ᶠ i in 𝓕, x i ∈ A i} :=
  Subtype.range_val_subtype

lemma range_coe_principal :
    range ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) = S.pi A :=
  range_coe R A

variable (𝓕) in
/-- The *structure map* of the restricted product is the obvious inclusion from `Π i, A i`
into `Πʳ i, [R i, A i]_[𝓕]`. -/
def structureMap (x : Π i, A i) : Πʳ i, [R i, A i]_[𝓕] :=
  ⟨fun i ↦ x i, .of_forall fun i ↦ (x i).2⟩

/-- If `𝓕 ≤ 𝓖`, the restricted product `Πʳ i, [R i, A i]_[𝓖]` is naturally included in
`Πʳ i, [R i, A i]_[𝓕]`. This is the corresponding map. -/
def inclusion (h : 𝓕 ≤ 𝓖) (x : Πʳ i, [R i, A i]_[𝓖]) :
    Πʳ i, [R i, A i]_[𝓕] :=
  ⟨x, x.2.filter_mono h⟩

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

lemma range_structureMap :
    Set.range (structureMap R A 𝓕) = {f | ∀ i, f.1 i ∈ A i} :=
  subset_antisymm (range_subset_iff.mpr fun x i ↦ (x i).2)
    (fun _ hx ↦ mem_range.mpr <| exists_structureMap_eq_of_forall R A hx)

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

@[to_additive]
instance [Π i, Inv (R i)] [∀ i, InvMemClass (S i) (R i)] : Inv (Πʳ i, [R i, B i]_[𝓕]) where
  inv x := ⟨fun i ↦ (x i)⁻¹, x.2.mono fun _ ↦ inv_mem⟩

@[to_additive]
instance [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)] : Mul (Πʳ i, [R i, B i]_[𝓕]) where
  mul x y := ⟨fun i ↦ x i * y i, y.2.mp (x.2.mono fun _ ↦ mul_mem)⟩

@[to_additive]
instance {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)] :
    SMul G (Πʳ i, [R i, B i]_[𝓕]) where
  smul g x := ⟨fun i ↦ g • (x i), x.2.mono fun _ ↦ SMulMemClass.smul_mem g⟩

@[to_additive]
instance [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Div (Πʳ i, [R i, B i]_[𝓕]) where
  div x y := ⟨fun i ↦ x i / y i, y.2.mp (x.2.mono fun _ ↦ div_mem)⟩

instance [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    Pow (Πʳ i, [R i, B i]_[𝓕]) ℕ where
  pow x n := ⟨fun i ↦ x i ^ n, x.2.mono fun _ hi ↦ pow_mem hi n⟩

instance [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Pow (Πʳ i, [R i, B i]_[𝓕]) ℤ where
  pow x n := ⟨fun i ↦ x i ^ n, x.2.mono fun _ hi ↦ zpow_mem hi n⟩

instance [Π i, AddMonoidWithOne (R i)] [∀ i, AddSubmonoidWithOneClass (S i) (R i)] :
    NatCast (Πʳ i, [R i, B i]_[𝓕]) where
  natCast n := ⟨fun _ ↦ n, .of_forall fun _ ↦ natCast_mem _ n⟩

instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    IntCast (Πʳ i, [R i, B i]_[𝓕]) where
  intCast n := ⟨fun _ ↦ n, .of_forall fun _ ↦ intCast_mem _ n⟩

instance [Π i, AddGroup (R i)] [∀ i, AddSubgroupClass (S i) (R i)] :
    AddGroup (Πʳ i, [R i, B i]_[𝓕]) :=
  haveI : ∀ i, SMulMemClass (S i) ℤ (R i) := fun _ ↦ AddSubgroupClass.zsmulMemClass
  haveI : ∀ i, SMulMemClass (S i) ℕ (R i) := fun _ ↦ AddSubmonoidClass.nsmulMemClass
  DFunLike.coe_injective.addGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[to_additive existing]
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Group (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.group _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    Ring (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.ring _ rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

instance [Π i, CommRing (R i)] [∀ i, SubringClass (S i) (R i)] :
    CommRing (Πʳ i, [R i, B i]_[𝓕]) where
  mul_comm _ _ := DFunLike.coe_injective <| funext (fun _ ↦ mul_comm _ _)

end Algebra

section Topology
/-!
## Topology on the restricted product

The topology on the restricted product `Πʳ i, [R i, A i]_[𝓕]` is defined in the following way:
1. If `𝓕` is some principal filter `𝓟 s`, recall that `Πʳ i, [R i, A i]_[𝓟 s]` is canonically
identified with `(Π i ∈ s, A i) × (Π i ∉ s, R i)`. We endow it with the product topology,
which is also the topology induced from the full product `Π i, R i`.
2. In general, we note that `𝓕` is the infimum of the principal filters coarser than `𝓕`. We
then endow `Πʳ i, [R i, A i]_[𝓕]` with the inductive limit / final topology associated to the
inclusion maps `Πʳ i, [R i, A i]_[𝓟 s] → Πʳ i, [R i, A i]_[𝓕]` where `𝓕 ≤ 𝓟 s`.

In particular:
* On the classical restricted product, with respect to the cofinite filter, this corresponds to
taking the inductive limit of the `Πʳ i, [R i, A i]_[𝓟 s]` over all *cofinite* sets `s : Set ι`.
* If `𝓕 = 𝓟 s` is a principal filter, this second step clearly does not change the topology, since
`s` belongs to the indexing set of the inductive limit.

Taking advantage of that second remark, we do not actually declare an instance specific to
principal filters. Instead, we provide directly the general instance (corresponding to step 2 above)
as `RestrictedProduct.topologicalSpace`. We then prove that, for a principal filter, the
map to the full product is an inducing (`RestrictedProduct.isEmbedding_coe_of_principal`),
and that the topology for a general `𝓕` is indeed the expected inductive limit
(`RestrictedProduct.topologicalSpace_eq_iSup`).

Note: outside of these two cases, this topology on the restricted product does not seem
well-behaved. While declaring a single instance is practical, it may conflict with more interesting
topologies in some other cases. Thus, future contributions should not restrain from specializing
these instances to principal and cofinite filters if necessary.
-/

/-!
### Definition of the topology
-/

variable {R A R' A'}
variable {𝓕 : Filter ι}
variable [∀ i, TopologicalSpace (R i)]

variable (R A 𝓕) in
instance topologicalSpace : TopologicalSpace (Πʳ i, [R i, A i]_[𝓕]) :=
  ⨆ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S), .coinduced (inclusion R A hS)
    (.induced ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) inferInstance)

theorem continuous_coe :
    Continuous ((↑) : Πʳ i, [R i, A i]_[𝓕] → Π i, R i) :=
  continuous_iSup_dom.mpr fun _ ↦ continuous_iSup_dom.mpr fun _ ↦
    continuous_coinduced_dom.mpr continuous_induced_dom

theorem continuous_inclusion {𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) :
    Continuous (inclusion R A h) := by
  simp_rw [continuous_iff_coinduced_le, topologicalSpace, coinduced_iSup, coinduced_compose]
  exact iSup₂_le fun S hS ↦ le_iSup₂_of_le S (le_trans h hS) le_rfl

instance [∀ i, T0Space (R i)] : T0Space (Πʳ i, [R i, A i]_[𝓕]) :=
  t0Space_of_injective_of_continuous DFunLike.coe_injective continuous_coe

instance [∀ i, T1Space (R i)] : T1Space (Πʳ i, [R i, A i]_[𝓕]) :=
  t1Space_of_injective_of_continuous DFunLike.coe_injective continuous_coe

instance [∀ i, T2Space (R i)] : T2Space (Πʳ i, [R i, A i]_[𝓕]) :=
  .of_injective_continuous DFunLike.coe_injective continuous_coe

section principal
/-!
### Topological facts in the principal case
-/

variable {S : Set ι}

theorem topologicalSpace_eq_of_principal :
    topologicalSpace R A (𝓟 S) =
      .induced ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) inferInstance :=
  le_antisymm (continuous_iff_le_induced.mp continuous_coe) <|
    (le_iSup₂_of_le S le_rfl <| by rw [inclusion_eq_id R A (𝓟 S), @coinduced_id])

theorem topologicalSpace_eq_of_top :
    topologicalSpace R A ⊤ =
      .induced ((↑) : Πʳ i, [R i, A i]_[⊤] → Π i, R i) inferInstance :=
  principal_univ ▸ topologicalSpace_eq_of_principal

theorem topologicalSpace_eq_of_bot :
    topologicalSpace R A ⊥ =
      .induced ((↑) : Πʳ i, [R i, A i]_[⊥] → Π i, R i) inferInstance :=
  principal_empty ▸ topologicalSpace_eq_of_principal

theorem isEmbedding_coe_of_principal :
    IsEmbedding ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) where
  eq_induced := topologicalSpace_eq_of_principal
  injective := DFunLike.coe_injective

theorem isEmbedding_coe_of_top :
    IsEmbedding ((↑) : Πʳ i, [R i, A i]_[⊤] → Π i, R i) :=
  principal_univ ▸ isEmbedding_coe_of_principal

theorem isEmbedding_coe_of_bot :
    IsEmbedding ((↑) : Πʳ i, [R i, A i]_[⊥] → Π i, R i) :=
  principal_empty ▸ isEmbedding_coe_of_principal

theorem continuous_rng_of_principal {X : Type*} [TopologicalSpace X]
    {f : X → Πʳ i, [R i, A i]_[𝓟 S]} :
    Continuous f ↔ Continuous ((↑) ∘ f : X → Π i, R i) :=
  isEmbedding_coe_of_principal.continuous_iff

theorem continuous_rng_of_top {X : Type*} [TopologicalSpace X]
    {f : X → Πʳ i, [R i, A i]_[⊤]} :
    Continuous f ↔ Continuous ((↑) ∘ f : X → Π i, R i) :=
  isEmbedding_coe_of_top.continuous_iff

theorem continuous_rng_of_bot {X : Type*} [TopologicalSpace X]
    {f : X → Πʳ i, [R i, A i]_[⊥]} :
    Continuous f ↔ Continuous ((↑) ∘ f : X → Π i, R i) :=
  isEmbedding_coe_of_bot.continuous_iff

/-- The obvious bijection between `Πʳ i, [R i, A i]_[⊤]` and `Π i, A i` is a homeomorphism. -/
def homeoTop : (Π i, A i) ≃ₜ (Πʳ i, [R i, A i]_[⊤]) where
  toFun f := ⟨fun i ↦ f i, fun i ↦ (f i).2⟩
  invFun f i := ⟨f i, f.2 i⟩
  continuous_toFun := continuous_rng_of_top.mpr <| continuous_pi fun i ↦
      continuous_subtype_val.comp <| continuous_apply i
  continuous_invFun := continuous_pi fun i ↦ continuous_induced_rng.mpr <|
    (continuous_apply i).comp continuous_coe
  left_inv _ := rfl
  right_inv _ := rfl

/-- The obvious bijection between `Πʳ i, [R i, A i]_[⊥]` and `Π i, R i` is a homeomorphism. -/
def homeoBot : (Π i, R i) ≃ₜ (Πʳ i, [R i, A i]_[⊥]) where
  toFun f := ⟨fun i ↦ f i, eventually_bot⟩
  invFun f i := f i
  continuous_toFun := continuous_rng_of_bot.mpr <| continuous_pi fun i ↦ continuous_apply i
  continuous_invFun := continuous_pi fun i ↦ (continuous_apply i).comp continuous_coe
  left_inv _ := rfl
  right_inv _ := rfl

/-- Assume that `S` is a subset of `ι` with finite complement, that each `R i` is weakly locally
compact, and that `A i` is *compact* for all `i ∈ S`. Then the restricted product
`Πʳ i, [R i, A i]_[𝓟 S]` is locally compact.

Note: we spell "`S` has finite complement" as `cofinite ≤ 𝓟 S`. -/
theorem weaklyLocallyCompactSpace_of_principal [∀ i, WeaklyLocallyCompactSpace (R i)]
    (hS : cofinite ≤ 𝓟 S) (hAcompact : ∀ i ∈ S, IsCompact (A i)) :
    WeaklyLocallyCompactSpace (Πʳ i, [R i, A i]_[𝓟 S]) where
  exists_compact_mem_nhds := fun x ↦ by
    rw [le_principal_iff, mem_cofinite] at hS
    classical
    have : ∀ i, ∃ K, IsCompact K ∧ K ∈ 𝓝 (x i) := fun i ↦ exists_compact_mem_nhds (x i)
    choose K K_compact hK using this
    set Q : Set (Π i, R i) := univ.pi (fun i ↦ if i ∈ S then A i else K i) with Q_def
    have Q_compact : IsCompact Q := isCompact_univ_pi fun i ↦ by
      split_ifs with his
      · exact hAcompact i his
      · exact K_compact i
    set U : Set (Π i, R i) := Sᶜ.pi K
    have U_nhds : U ∈ 𝓝 (x : Π i, R i) := set_pi_mem_nhds hS fun i _ ↦ hK i
    have QU : (↑) ⁻¹' U ⊆ ((↑) ⁻¹' Q : Set (Πʳ i, [R i, A i]_[𝓟 S])) := fun y H i _ ↦ by
      dsimp only
      split_ifs with hi
      · exact y.2 hi
      · exact H i hi
    refine ⟨((↑) ⁻¹' Q), ?_, mem_of_superset ?_ QU⟩
    · refine isEmbedding_coe_of_principal.isCompact_preimage_iff ?_ |>.mpr Q_compact
      simp_rw [range_coe_principal, Q_def, pi_if, mem_univ, true_and]
      exact inter_subset_left
    · simpa only [isEmbedding_coe_of_principal.nhds_eq_comap] using preimage_mem_comap U_nhds

instance [∀ i, WeaklyLocallyCompactSpace (R i)] [hS : Fact (cofinite ≤ 𝓟 S)]
    [hAcompact : ∀ i, CompactSpace (A i)] :
    WeaklyLocallyCompactSpace (Πʳ i, [R i, A i]_[𝓟 S]) :=
  weaklyLocallyCompactSpace_of_principal hS.out
    fun _ _ ↦ isCompact_iff_compactSpace.mpr inferInstance

end principal

section general
/-!
### Topological facts in the general case
-/

variable (𝓕) in
theorem topologicalSpace_eq_iSup :
    topologicalSpace R A 𝓕 = ⨆ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S),
      .coinduced (inclusion R A hS) (topologicalSpace R A (𝓟 S)) := by
  simp_rw [topologicalSpace_eq_of_principal, topologicalSpace]

/-- The **universal property** of the topology on the restricted product: a map from
`Πʳ i, [R i, A i]_[𝓕]` is continuous *iff* its restriction to each `Πʳ i, [R i, A i]_[𝓟 s]`
(with `𝓕 ≤ 𝓟 s`) is continuous.

See also `RestrictedProduct.continuous_dom_prod_left`. -/
theorem continuous_dom {X : Type*} [TopologicalSpace X]
    {f : Πʳ i, [R i, A i]_[𝓕] → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S), Continuous (f ∘ inclusion R A hS) := by
  simp_rw [topologicalSpace_eq_of_principal, continuous_iSup_dom, continuous_coinduced_dom]

theorem isEmbedding_inclusion_principal {S : Set ι} (hS : 𝓕 ≤ 𝓟 S) :
    IsEmbedding (inclusion R A hS) :=
  .of_comp (continuous_inclusion hS) continuous_coe isEmbedding_coe_of_principal

theorem isEmbedding_inclusion_top :
    IsEmbedding (inclusion R A (le_top : 𝓕 ≤ ⊤)) :=
  .of_comp (continuous_inclusion _) continuous_coe isEmbedding_coe_of_top

/-- `Π i, A i` has the subset topology from the restricted product. -/
theorem isEmbedding_structureMap :
    IsEmbedding (structureMap R A 𝓕) :=
  isEmbedding_inclusion_top.comp homeoTop.isEmbedding

end general

section cofinite
/-!
### Topological facts in the case where `𝓕 = cofinite` and all `A i`s are open

The classical restricted product, associated to the cofinite filter, satisfies more topological
properties when each `A i` is an open subset of `R i`. The key fact is that each
`Πʳ i, [R i, A i]_[𝓟 S]` (with `S` cofinite) then embeds **as an open subset** in
`Πʳ i, [R i, A i]`.

This allows us to prove a "universal property with parameters", expressing that for any
arbitrary topolgical space `X` (of "parameters"), the product `X × Πʳ i, [R i, A i]`
is still the inductive limit of the `X × Πʳ i, [R i, A i]_[𝓟 S]` for `S` cofinite.

This fact, which is **not true** for a general inductive limit, will allow us to prove continuity
of functions of two variables (e.g algebraic operations), which would otherwise be inaccessible.
-/

variable (hAopen : ∀ i, IsOpen (A i))

include hAopen in
theorem isOpen_forall_imp_mem_of_principal {S : Set ι} (hS : cofinite ≤ 𝓟 S) {p : ι → Prop} :
    IsOpen {f : Πʳ i, [R i, A i]_[𝓟 S] | ∀ i, p i → f.1 i ∈ A i} := by
  rw [le_principal_iff] at hS
  convert isOpen_set_pi (hS.inter_of_left {i | p i}) (fun i _ ↦ hAopen i) |>.preimage continuous_coe
  ext f
  refine ⟨fun H i hi ↦ H i hi.2, fun H i hiT ↦ ?_⟩
  by_cases hiS : i ∈ S
  · exact f.2 hiS
  · exact H i ⟨hiS, hiT⟩

include hAopen in
theorem isOpen_forall_mem_of_principal {S : Set ι} (hS : cofinite ≤ 𝓟 S) :
    IsOpen {f : Πʳ i, [R i, A i]_[𝓟 S] | ∀ i, f.1 i ∈ A i} := by
  convert isOpen_forall_imp_mem_of_principal hAopen hS (p := fun _ ↦ True)
  simp

include hAopen in
theorem isOpen_forall_imp_mem {p : ι → Prop} :
    IsOpen {f : Πʳ i, [R i, A i] | ∀ i, p i → f.1 i ∈ A i} := by
  simp_rw [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  exact fun S hS ↦ isOpen_forall_imp_mem_of_principal hAopen hS

include hAopen in
theorem isOpen_forall_mem :
    IsOpen {f : Πʳ i, [R i, A i] | ∀ i, f.1 i ∈ A i} := by
  simp_rw [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  exact fun S hS ↦ isOpen_forall_mem_of_principal hAopen hS

include hAopen in
theorem isOpenEmbedding_inclusion_principal {S : Set ι} (hS : cofinite ≤ 𝓟 S) :
    IsOpenEmbedding (inclusion R A hS) where
  toIsEmbedding := isEmbedding_inclusion_principal hS
  isOpen_range := by
    rw [range_inclusion]
    exact isOpen_forall_imp_mem hAopen

include hAopen in
/-- `Π i, A i` is homeomorphic to an open subset of the restricted product. -/
theorem isOpenEmbedding_structureMap :
    IsOpenEmbedding (structureMap R A cofinite) where
  toIsEmbedding := isEmbedding_structureMap
  isOpen_range := by
    rw [range_structureMap]
    exact isOpen_forall_mem hAopen

include hAopen in
theorem nhds_eq_map_inclusion {S : Set ι} (hS : cofinite ≤ 𝓟 S)
    (x : Πʳ i, [R i, A i]_[𝓟 S]) :
    (𝓝 (inclusion R A hS x)) = map (inclusion R A hS) (𝓝 x) := by
  rw [isOpenEmbedding_inclusion_principal hAopen hS |>.map_nhds_eq x]

include hAopen in
theorem nhds_eq_map_structureMap
    (x : Π i, A i) :
    (𝓝 (structureMap R A cofinite x)) = map (structureMap R A cofinite) (𝓝 x) := by
  rw [isOpenEmbedding_structureMap hAopen |>.map_nhds_eq x]

include hAopen in
/-- If each `R i` is weakly locally compact, each `A i` is open, and all but finitely many `A i`s
are also compact, then the restricted product `Πʳ i, [R i, A i]` is weakly locally compact. -/
theorem weaklyLocallyCompactSpace_of_cofinite [∀ i, WeaklyLocallyCompactSpace (R i)]
    (hAcompact : ∀ᶠ i in cofinite, IsCompact (A i)) :
    WeaklyLocallyCompactSpace (Πʳ i, [R i, A i]) where
  exists_compact_mem_nhds := fun x ↦ by
    set S := {i | IsCompact (A i) ∧ x i ∈ A i}
    have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr (hAcompact.and x.2)
    have hSx : ∀ i ∈ S, x i ∈ A i := fun i hi ↦ hi.2
    have hSA : ∀ i ∈ S, IsCompact (A i) := fun i hi ↦ hi.1
    haveI := weaklyLocallyCompactSpace_of_principal hS hSA
    rcases exists_inclusion_eq_of_eventually R A hS hSx with ⟨x', hxx'⟩
    rw [← hxx', nhds_eq_map_inclusion hAopen]
    rcases exists_compact_mem_nhds x' with ⟨K, K_compact, hK⟩
    exact ⟨inclusion R A hS '' K, K_compact.image (continuous_inclusion hS), image_mem_map hK⟩

instance [hAopen : Fact (∀ i, IsOpen (A i))] [∀ i, WeaklyLocallyCompactSpace (R i)]
    [hAcompact : ∀ i, CompactSpace (A i)] :
    WeaklyLocallyCompactSpace (Πʳ i, [R i, A i]) :=
  weaklyLocallyCompactSpace_of_cofinite hAopen.out <|
    .of_forall fun _ ↦ isCompact_iff_compactSpace.mpr inferInstance

include hAopen in
/-- The **universal property with parameters** of the topology on the restricted product:
for any topological space `Y` of "parameters", a map from `(Πʳ i, [R i, A i]) × Y` is continuous
*iff* its restriction to each `(Πʳ i, [R i, A i]_[𝓟 S]) × Y` (with `S` cofinite) is continuous. -/
theorem continuous_dom_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Πʳ i, [R i, A i] × Y → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : cofinite ≤ 𝓟 S),
      Continuous (f ∘ (Prod.map (inclusion R A hS) id)) := by
  refine ⟨fun H S hS ↦ H.comp ((continuous_inclusion hS).prodMap continuous_id),
    fun H ↦ ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨x, y⟩
  set S : Set ι := {i | x i ∈ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr x.2
  have hxS : ∀ i ∈ S, x i ∈ A i := fun i hi ↦ hi
  rcases exists_inclusion_eq_of_eventually R A hS hxS with ⟨x', hxx'⟩
  rw [← hxx', nhds_prod_eq, nhds_eq_map_inclusion hAopen hS x',
    ← map_id (f := 𝓝 y), prod_map_map_eq, ← nhds_prod_eq, tendsto_map'_iff]
  exact H S hS |>.tendsto ⟨x', y⟩

-- TODO: get from the previous one instead of copy-pasting
include hAopen in
/-- The **universal property with parameters** of the topology on the restricted product:
for any topological space `Y` of "parameters", a map from `Y × Πʳ i, [R i, A i]` is continuous
*iff* its restriction to each `Y × Πʳ i, [R i, A i]_[𝓟 S]` (with `S` cofinite) is continuous. -/
theorem continuous_dom_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y × Πʳ i, [R i, A i] → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : cofinite ≤ 𝓟 S),
      Continuous (f ∘ (Prod.map id (inclusion R A hS))) := by
  refine ⟨fun H S hS ↦ H.comp (continuous_id.prodMap (continuous_inclusion hS)),
    fun H ↦ ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨y, x⟩
  set S : Set ι := {i | x i ∈ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr x.2
  have hxS : ∀ i ∈ S, x i ∈ A i := fun i hi ↦ hi
  rcases exists_inclusion_eq_of_eventually R A hS hxS with ⟨x', hxx'⟩
  rw [← hxx', nhds_prod_eq, nhds_eq_map_inclusion hAopen hS x',
    ← map_id (f := 𝓝 y), prod_map_map_eq, ← nhds_prod_eq, tendsto_map'_iff]
  exact H S hS |>.tendsto ⟨y, x'⟩

include hAopen in
/-- A map from `Πʳ i, [R i, A i] × Πʳ i, [R' i, A' i]` is continuous
*iff* its restriction to each `Πʳ i, [R i, A i]_[𝓟 S] × Πʳ i, [R' i, A' i]_[𝓟 S]`
(with `S` cofinite) is continuous.

This is the key result for continuity of multiplication and addition. -/
theorem continuous_dom_prod {R' : ι → Type*} {A' : (i : ι) → Set (R' i)}
    [∀ i, TopologicalSpace (R' i)] (hAopen' : ∀ i, IsOpen (A' i))
    {X : Type*} [TopologicalSpace X]
    {f : Πʳ i, [R i, A i] × Πʳ i, [R' i, A' i] → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : cofinite ≤ 𝓟 S),
      Continuous (f ∘ (Prod.map (inclusion R A hS) (inclusion R' A' hS))) := by
  simp_rw [continuous_dom_prod_right hAopen, continuous_dom_prod_left hAopen']
  refine ⟨fun H S hS ↦ H S hS S hS, fun H S hS T hT ↦ ?_⟩
  set U := S ∩ T
  have hU : cofinite ≤ 𝓟 (S ∩ T) := inf_principal ▸ le_inf hS hT
  have hSU : 𝓟 U ≤ 𝓟 S := principal_mono.mpr inter_subset_left
  have hTU : 𝓟 U ≤ 𝓟 T := principal_mono.mpr inter_subset_right
  exact (H U hU).comp ((continuous_inclusion hSU).prodMap (continuous_inclusion hTU))

end cofinite

end Topology

section Compatibility
/-!
## Compatibility properties between algebra and topology
-/

variable {S : ι → Type*} -- subobject type
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}
variable {T : Set ι} {𝓕 : Filter ι}
variable [Π i, TopologicalSpace (R i)]

section general

@[to_additive]
instance [Π i, Inv (R i)] [∀ i, InvMemClass (S i) (R i)] [∀ i, ContinuousInv (R i)] :
    ContinuousInv (Πʳ i, [R i, B i]_[𝓕]) where
  continuous_inv := by
    rw [continuous_dom]
    intro T hT
    haveI : ContinuousInv (Πʳ i, [R i, B i]_[𝓟 T]) :=
      isEmbedding_coe_of_principal.continuousInv fun _ ↦ rfl
    exact (continuous_inclusion hT).comp continuous_inv

@[to_additive]
instance {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)]
    [∀ i, ContinuousConstSMul G (R i)] :
    ContinuousConstSMul G (Πʳ i, [R i, B i]_[𝓕]) where
  continuous_const_smul g := by
    rw [continuous_dom]
    intro T hT
    haveI : ContinuousConstSMul G (Πʳ i, [R i, B i]_[𝓟 T]) :=
      isEmbedding_coe_of_principal.continuousConstSMul id rfl
    exact (continuous_inclusion hT).comp (continuous_const_smul g)

end general

section principal

@[to_additive]
instance [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)] [∀ i, ContinuousMul (R i)] :
    ContinuousMul (Πʳ i, [R i, B i]_[𝓟 T]) :=
  let φ : Πʳ i, [R i, B i]_[𝓟 T] →ₙ* Π i, R i :=
  { toFun := (↑)
    map_mul' := fun _ _ ↦ rfl }
  isEmbedding_coe_of_principal.continuousMul φ

@[to_additive]
instance {G : Type*} [TopologicalSpace G] [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)]
    [∀ i, ContinuousSMul G (R i)] :
    ContinuousSMul G (Πʳ i, [R i, B i]_[𝓟 T]) :=
  isEmbedding_coe_of_principal.continuousSMul continuous_id rfl

@[to_additive]
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] [∀ i, IsTopologicalGroup (R i)] :
    IsTopologicalGroup (Πʳ i, [R i, B i]_[𝓟 T]) where

instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] [∀ i, IsTopologicalRing (R i)] :
    IsTopologicalRing (Πʳ i, [R i, B i]_[𝓟 T]) where

end principal

section cofinite

theorem nhds_zero_eq_map_ofPre [Π i, Zero (R i)] [∀ i, ZeroMemClass (S i) (R i)]
    (hBopen : ∀ i, IsOpen (B i : Set (R i))) (hT : cofinite ≤ 𝓟 T) :
    (𝓝 (inclusion R (fun i ↦ B i) hT 0)) = map (inclusion R (fun i ↦ B i) hT) (𝓝 0) :=
  nhds_eq_map_inclusion hBopen hT 0

theorem nhds_zero_eq_map_structureMap [Π i, Zero (R i)] [∀ i, ZeroMemClass (S i) (R i)]
    (hBopen : ∀ i, IsOpen (B i : Set (R i))) :
    (𝓝 (structureMap R (fun i ↦ B i) cofinite 0)) =
      map (structureMap R (fun i ↦ B i) cofinite) (𝓝 0) :=
  nhds_eq_map_structureMap hBopen 0

-- TODO: Make `IsOpen` a class like `IsClosed` ?
variable [hBopen : Fact (∀ i, IsOpen (B i : Set (R i)))]

@[to_additive]
instance [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)] [∀ i, ContinuousMul (R i)] :
    ContinuousMul (Πʳ i, [R i, B i]) where
  continuous_mul := by
    rw [continuous_dom_prod hBopen.out hBopen.out]
    exact fun S hS ↦ (continuous_inclusion hS).comp continuous_mul

@[to_additive]
instance continuousSMul {G : Type*} [TopologicalSpace G] [Π i, SMul G (R i)]
    [∀ i, SMulMemClass (S i) G (R i)] [∀ i, ContinuousSMul G (R i)] :
    ContinuousSMul G (Πʳ i, [R i, B i]) where
  continuous_smul := by
    rw [continuous_dom_prod_left hBopen.out]
    exact fun S hS ↦ (continuous_inclusion hS).comp continuous_smul

@[to_additive]
instance isTopologicalGroup [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)]
    [∀ i, IsTopologicalGroup (R i)] :
    IsTopologicalGroup (Πʳ i, [R i, B i]) where

instance isTopologicalRing [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)]
    [∀ i, IsTopologicalRing (R i)] :
    IsTopologicalRing (Πʳ i, [R i, B i]) where

/-- Assume that each `R i` is a locally compact group with `A i` an open subgroup.
Assume also that all but finitely many `A i`s are compact.
Then the restricted product `Πʳ i, [R i, A i]` is a locally compact group. -/
@[to_additive
"Assume that each `R i` is a locally compact additive group with `A i` an open subgroup.
Assume also that all but finitely many `A i`s are compact.
Then the restricted product `Πʳ i, [R i, A i]` is a locally compact additive group."]
theorem locallyCompactSpace_of_group [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)]
    [∀ i, IsTopologicalGroup (R i)] [∀ i, LocallyCompactSpace (R i)]
    (hBcompact : ∀ᶠ i in cofinite, IsCompact (B i : Set (R i))) :
    LocallyCompactSpace (Πʳ i, [R i, B i]) :=
  haveI : WeaklyLocallyCompactSpace (Πʳ i, [R i, B i]) :=
    weaklyLocallyCompactSpace_of_cofinite hBopen.out hBcompact
  inferInstance

open Pointwise in
@[to_additive]
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] [∀ i, IsTopologicalGroup (R i)]
    [hAcompact : ∀ i, CompactSpace (B i)] : LocallyCompactSpace (Πʳ i, [R i, B i]) :=
  -- TODO: extract as a lemma
  haveI : ∀ i, WeaklyLocallyCompactSpace (R i) := fun i ↦ .mk fun x ↦
    ⟨x • (B i : Set (R i)), .smul _ (isCompact_iff_compactSpace.mpr inferInstance),
      hBopen.out i |>.smul _ |>.mem_nhds <| by
      simpa using smul_mem_smul_set (a := x) (one_mem (B i))⟩
  locallyCompactSpace_of_group _ <| .of_forall fun _ ↦ isCompact_iff_compactSpace.mpr inferInstance

end cofinite

end Compatibility

end RestrictedProduct
