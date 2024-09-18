/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao
-/
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.NormalClosure
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Topology.Algebra.Category.ProfiniteGrp

/-!

# Galois Group as a Profinite Group

In this file, we prove that in a field extension `K/k`, there is a continuous isomorphism between
`Gal(K/k)` the limit of `Gal(L/k)`, where `L` is a finite galois intermediate field ordered by
inverse inclusion, thus making `Gal(K/k)` profinite because the limit is profinite.

# Main definitions and results

In `K/k`

* `FiniteGaloisIntermediateField` : The type of finite Galois intermediateField of `K/k`

* `finGal L` : For a `FiniteGaloisIntermediateField` `L`, make `Gal(L/k)` into a FiniteGrp

* `finGalMap L₁ ⟶ L₂` : For `FiniteGaloisIntermediateField` `L₁ L₂` ordered by inverse inclusion,
  giving the restriction of `Gal(L₁/k)` to `Gal(L₂/k)`

* `finGalFunctor` : Mapping `FiniteGaloisIntermediateField` ordered by inverse inclusion to its
  corresponding Galois Group as FiniteGrp

# TODO

* `FiniteGaloisIntermediateField` should be a `ConditionallyCompleteLattice` but isn't proved yet.

-/

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

open scoped Topology in
private lemma krullTopology_mem_nhds_one (s : Set (L ≃ₐ[F] L)) :
    s ∈ 𝓝 1 ↔ ∃ S : IntermediateField F L,
    FiniteDimensional F S ∧ (S.fixingSubgroup : Set (L ≃ₐ[F] L)) ⊆ s := by
  rw [GroupFilterBasis.nhds_one_eq]
  constructor
  · rintro ⟨-, ⟨-, ⟨S, fin, rfl⟩, rfl⟩, hS⟩
    exact ⟨S, fin, hS⟩
  · rintro ⟨S, fin, hS⟩
    exact ⟨S.fixingSubgroup, ⟨S.fixingSubgroup, ⟨S, fin, rfl⟩, rfl⟩, hS⟩

open CategoryTheory Topology Opposite
open scoped IntermediateField

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/--The type of finite Galois intermediateField of `K/k`-/
@[ext]
structure FiniteGaloisIntermediateField where
  /--extend from `IntermediateField`-/
  val : IntermediateField k K
  [to_finiteDimensional : FiniteDimensional k val]
  [to_isGalois : IsGalois k val]

namespace FiniteGaloisIntermediateField

attribute [coe] val

instance : Coe (FiniteGaloisIntermediateField k K) (IntermediateField k K) where
  coe := val

instance : CoeSort (FiniteGaloisIntermediateField k K) (Type _) where
  coe L := L.val

instance (L : FiniteGaloisIntermediateField k K) : FiniteDimensional k L.val :=
  L.to_finiteDimensional

instance (L : FiniteGaloisIntermediateField k K) : IsGalois k L.val := L.to_isGalois

variable {k K}

lemma val_injective : Function.Injective (val (k := k) (K := K)) := by
  rintro ⟨⟩ ⟨⟩ eq
  simpa only [mk.injEq] using eq

/--Make the Finite Galois IntermediateField of `K/k` into an lattice-/

instance (L₁ L₂ : IntermediateField k K) [IsGalois k L₁] [IsGalois k L₂] :
    IsGalois k ↑(L₁ ⊔ L₂) := {}

instance (L₁ L₂ : IntermediateField k K) [FiniteDimensional k L₁] :
    FiniteDimensional k ↑(L₁ ⊓ L₂) :=
  .of_injective (IntermediateField.inclusion inf_le_left).toLinearMap
    (IntermediateField.inclusion inf_le_left).injective

instance (L₁ L₂ : IntermediateField k K) [FiniteDimensional k L₂] :
    FiniteDimensional k ↑(L₁ ⊓ L₂) :=
  .of_injective (IntermediateField.inclusion inf_le_right).toLinearMap
    (IntermediateField.inclusion inf_le_right).injective

instance (L₁ L₂ : IntermediateField k K) [Algebra.IsSeparable k L₁] :
    Algebra.IsSeparable k ↑(L₁ ⊓ L₂) :=
  .of_algHom _ _ (IntermediateField.inclusion inf_le_left)

instance (L₁ L₂ : IntermediateField k K) [Algebra.IsSeparable k L₂] :
    Algebra.IsSeparable k ↑(L₁ ⊓ L₂) :=
  .of_algHom _ _ (IntermediateField.inclusion inf_le_right)

instance (L₁ L₂ : IntermediateField k K) [IsGalois k L₁] [IsGalois k L₂] :
    IsGalois k ↑(L₁ ⊓ L₂) := {}

instance : Sup (FiniteGaloisIntermediateField k K) where
  sup L₁ L₂ := .mk <| L₁.val ⊔ L₂.val

instance : Inf (FiniteGaloisIntermediateField k K) where
  inf L₁ L₂ := .mk <| L₁.val ⊓ L₂.val

instance : Lattice (FiniteGaloisIntermediateField k K) :=
  val_injective.lattice _ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : OrderBot (FiniteGaloisIntermediateField k K) where
  bot := .mk ⊥
  bot_le _ := bot_le (α := IntermediateField _ _)

variable (k) in
/--Define the finite Galois closure of adjoining a finite set-/
noncomputable def adjoin [IsGalois k K] (s : Set K) [Finite s] :
    FiniteGaloisIntermediateField k K where
  val := normalClosure k (IntermediateField.adjoin k (s : Set K)) K
  to_finiteDimensional :=
    letI : FiniteDimensional k (IntermediateField.adjoin k (s : Set K)) :=
      IntermediateField.finiteDimensional_adjoin <| fun z _ =>
        IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic z)
    normalClosure.is_finiteDimensional k (IntermediateField.adjoin k (s : Set K)) K
  to_isGalois := IsGalois.normalClosure k (IntermediateField.adjoin k (s : Set K)) K

lemma adjoin_val [IsGalois k K] (s : Set K) [Finite s] :
    (FiniteGaloisIntermediateField.adjoin k s).val =
    normalClosure k (IntermediateField.adjoin k s) K :=
  rfl

variable (k) in
lemma subset_adjoin [IsGalois k K] (s : Set K) [Finite s] :
    s ⊆ (adjoin k s).val := by
  intro x hx
  apply IntermediateField.le_normalClosure
  simp only [IntermediateField.adjoin, Set.union_insert, Set.union_singleton,
    IntermediateField.mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring]
  apply Subfield.subset_closure
  simp only [Set.mem_union, Set.mem_range, hx, or_true]

@[simp]
theorem adjoin_le_iff [IsGalois k K] {s : Set K} [Finite s]
    {L : FiniteGaloisIntermediateField k K} : adjoin k s ≤ L ↔ s ≤ L.val := by
  show normalClosure _ _ _ ≤ L.val ↔ _
  rw [← IntermediateField.adjoin_le_iff, IntermediateField.normalClosure_le_iff_of_normal]

theorem adjoin_simple_le_iff [IsGalois k K] {x : K} {L : FiniteGaloisIntermediateField k K} :
    adjoin k {x} ≤ L ↔ x ∈ L.val := by
  simp only [adjoin_le_iff, Set.le_eq_subset, Set.singleton_subset_iff, SetLike.mem_coe]

@[simp]
theorem adjoin_map [IsGalois k K] (f : K →ₐ[k] K) (s : Set K) [Finite s] :
    adjoin k (f '' s) = adjoin k s := by
  apply val_injective; dsimp [adjoin_val]
  rw [← IntermediateField.adjoin_map, IntermediateField.normal_map]

@[simp]
theorem adjoin_simple_map [IsGalois k K] (f : K →ₐ[k] K) (x : K) :
    adjoin k {f x} = adjoin k {x} := by
  simpa only [Set.image_singleton] using adjoin_map f { x }

@[simp]
theorem adjoin_simple_map' [IsGalois k K] (f : K ≃ₐ[k] K) (x : K) :
    adjoin k {f x} = adjoin k {x} :=
  adjoin_simple_map (f : K →ₐ[k] K) x

/--For a `FiniteGaloisIntermediateField` `L`, make `Gal(L/k)` into a FiniteGrp-/
def finGal (L : FiniteGaloisIntermediateField k K) : FiniteGrp :=
  letI := AlgEquiv.fintype k L
  FiniteGrp.of <| L ≃ₐ[k] L

/--For `FiniteGaloisIntermediateField` `L₁ L₂` ordered by inverse inclusion,
  giving the restriction of `Gal(L₁/k)` to `Gal(L₂/k)`-/
noncomputable def finGalMap {L₁ L₂ : (FiniteGaloisIntermediateField k K)ᵒᵖ}
    (le : L₁ ⟶ L₂) : L₁.unop.finGal ⟶ L₂.unop.finGal :=
  haveI : Normal k L₂.unop := IsGalois.to_normal
  letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom le.1)
  haveI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  FiniteGrp.ofHom (AlgEquiv.restrictNormalHom (F := k) (K₁ := L₁.unop) L₂.unop)

namespace finGalMap

lemma map_id (L : (FiniteGaloisIntermediateField k K)ᵒᵖ) :
    (finGalMap (𝟙 L)) = 𝟙 L.unop.finGal :=
  AlgEquiv.restrictNormalHom_id _ _

lemma map_comp {L₁ L₂ L₃ : (FiniteGaloisIntermediateField k K)ᵒᵖ}
    (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) : finGalMap (f ≫ g) = finGalMap f ≫ finGalMap g := by
  iterate 2
    induction L₁ with | _ L₁ => ?_
    induction L₂ with | _ L₂ => ?_
    induction L₃ with | _ L₃ => ?_
  letI : Algebra L₃ L₂ := RingHom.toAlgebra (Subsemiring.inclusion g.unop.le)
  letI : Algebra L₂ L₁ := RingHom.toAlgebra (Subsemiring.inclusion f.unop.le)
  letI : Algebra L₃ L₁ := RingHom.toAlgebra (Subsemiring.inclusion (g.unop.le.trans f.unop.le))
  haveI : IsScalarTower k L₂ L₁ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsScalarTower k L₃ L₁ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsScalarTower k L₃ L₂ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsScalarTower L₃ L₂ L₁ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  apply IsScalarTower.algEquivRestrictNormalHom_eq k L₃ L₂ L₁

end finGalMap

variable (k K) in
/--Mapping `FiniteGaloisIntermediateField` ordered by inverse inclusion to its
  corresponding Galois Group as FiniteGrp-/
noncomputable def finGalFunctor : (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ FiniteGrp where
  obj L := L.unop.finGal
  map := finGalMap
  map_id := finGalMap.map_id
  map_comp := finGalMap.map_comp

end FiniteGaloisIntermediateField
