/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yuyang Zhao, Jujian Zhang
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

/-!

* `union_eq_univ` : In `K/k`, the union of all the `FiniteGaloisIntermediateField` is equal to `K`,
  Furthermore, there is also a `FiniteGaloisIntermediateField` containing any tuple `(x,y)`

* `HomtoLimit` : Based on the canonical projection from `Gal(K/k)` to any `Gal(L/k)`
  where `L` is a `FiniteGaloisIntermediateField`, it can be easily verified that
  the projections are compatible with the morphisms on `FiniteGaloisIntermediateField`
  (ordered by inverse inclusion)

* `ContinuousMulEquiv` : A ContinuousMulEquiv from `Gal(K/k)` to `lim Gal(L/k)`
  where `L` is `FiniteGaloisIntermediateField`, ordered by inverse inclusion.
  The proof consists of three main parts:
  1. Injectivity :
    Notice that the coordinate at the normal closure of simple extension of `x`
    is different for two element of `Gal(K/k)` mapping `x` differently.
  2. Surjectivity :
    A lemma is needed (lift): for an element `g` in `lim Gal(L/k)` and any two
    `FiniteGaloisIntermediateField` `L₁ L₂` containing an element`x`,
    `g` in the coordinate of `L₁` and `L₂` maps `x` to the same element of `K`.
    Then by defining the image of `g` in `Gal(K/k)` pointwise in `K` and use the lemma repeatedly,
    we can get an AlgHom. With the bijectivity of the AlgHom in an algebraic extension, it can be
    made into an element of `Gal(K/k)`
  3. Two-sided continuity : Notice that `Gal(K/k)` is `T2`,
    `lim Gal(L/k)` ordered by inverse inclusion is Profinite thus compact, we only need
    continuity from `lim Gal(L/k)` to `Gal(K/k)`, which only needs continuity at `1`.
    It can be easily verified by checking the preimage of GroupFilterBasis is open.

* `Profinite` ：`Gal(K/k)` is continuously isomorphic (as a topological group) to `lim Gal(L/k)`
  where `L` is `FiniteGaloisIntermediateField`, ordered by inverse inclusion, thus `Profinite`

-/

open FiniteGaloisIntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace InfiniteGalois

variable (k K) in
noncomputable abbrev profinGalFunctor : (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ ProfiniteGrp :=
    (finGalFunctor k K) ⋙ forget₂ FiniteGrp ProfiniteGrp

variable (k K) in
/--Define the homomorphism from `Gal(K/k)` to `lim Gal(L/k)` where `L` is a
  `FiniteGaloisIntermediateField` ordered by inverse inclusion. This homomorphism is given by the
  canonical projection from `Gal(K/k)` to `Gal(L/k)` viewing the limit as a
  subgroup of the product space. -/
@[simps]
noncomputable def homtoLimit : (K ≃ₐ[k] K) →* ProfiniteGrp.ofLimit (profinGalFunctor k K) where
  toFun σ := {
    val := fun L => (AlgEquiv.restrictNormalHom L.unop) σ
    property := fun L₁ L₂ π ↦ by
      dsimp [finGalFunctor, finGalMap]
      letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion π.1.le)
      letI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
      letI : IsScalarTower L₂.unop L₁.unop K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
      apply (IsScalarTower.algEquivRestrictNormalHom_apply k L₂.unop L₁.unop σ).symm }
  map_one' := by
    simp only [map_one]
    rfl
  map_mul' x y := by
    simp only [map_mul]
    rfl

lemma restrict_eq (σ : K ≃ₐ[k] K) (x : K) (Lx : FiniteGaloisIntermediateField k K)
    (hLx : x ∈ Lx.val) : σ x = (AlgEquiv.restrictNormalHom Lx σ) ⟨x, hLx⟩ := by
  have := AlgEquiv.restrictNormal_commutes σ Lx ⟨x, hLx⟩
  convert this
  exact id this.symm

/--Define the coordinate map from `lim Gal(L/k)` to a specific `Gal(L/k)`-/
def proj (L : FiniteGaloisIntermediateField k K) :
    ProfiniteGrp.ofLimit (profinGalFunctor k K) →* (L.val ≃ₐ[k] L.val) where
  toFun g := g.val (op L)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
lemma finGalFunctor_proj (g : ProfiniteGrp.ofLimit (profinGalFunctor k K))
    {L₁ L₂ : FiniteGaloisIntermediateField k K} (h : L₁ ⟶ L₂) :
    (finGalFunctor k K).map h.op (proj L₂ g) = proj L₁ g :=
  g.prop h.op

lemma proj_lift (L : FiniteGaloisIntermediateField k K)
    (g : ProfiniteGrp.ofLimit (profinGalFunctor k K)) (x : L)
    (L' : FiniteGaloisIntermediateField k K) (h : L ≤ L') :
    (proj L g x).val = (proj L' g ⟨x, h x.2⟩).val := by
  induction L with | _ L => ?_
  induction L' with | _ L' => ?_
  letI : Algebra L L' := RingHom.toAlgebra (Subsemiring.inclusion h)
  letI : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← finGalFunctor_proj g h.hom]
  show (algebraMap L' K (algebraMap L L' (AlgEquiv.restrictNormal (proj (mk L') g) L x))) = _
  rw [AlgEquiv.restrictNormal_commutes (proj (mk L') g) L]
  rfl

lemma proj_lift_adjoin_simple [IsGalois k K]
    (g : ProfiniteGrp.ofLimit (profinGalFunctor k K))
    (x : K) (y : adjoin k {x}) (L : FiniteGaloisIntermediateField k K) (h : x ∈ L.val) :
    (proj (adjoin k {x}) g y).val = (proj L g ⟨y, adjoin_simple_le_iff.mpr h y.2⟩).val :=
  proj_lift _ g y _ _

/--Define a function from `K` to `K` pointwise using a family of compatible elements of
  `Gal(L/k)` where `L` is a `FiniteGaloisIntermediateField`-/
noncomputable def toAlgEquivAux [IsGalois k K]
    (g : ProfiniteGrp.ofLimit (profinGalFunctor k K)) : K → K :=
  fun x ↦ (proj (adjoin k {x}) g ⟨x, subset_adjoin _ _ (by simp only [Set.mem_singleton_iff])⟩).val

lemma toAlgEquivAux_def [IsGalois k K] (g : ProfiniteGrp.ofLimit (profinGalFunctor k K))
    (x : K) (L : FiniteGaloisIntermediateField k K) (hx : x ∈ L.val) :
    toAlgEquivAux g x = (proj L g ⟨x, hx⟩).val :=
  proj_lift_adjoin_simple g _ _ L hx

lemma mk_toAlgEquivAux [IsGalois k K] (g : ProfiniteGrp.ofLimit (profinGalFunctor k K))
    (x : K) (L : FiniteGaloisIntermediateField k K) (hx' : toAlgEquivAux g x ∈ L.val)
    (hx : x ∈ L.val) : (⟨toAlgEquivAux g x, hx'⟩ : L.val) = proj L g ⟨x, hx⟩ := by
  rw [Subtype.eq_iff, Subtype.coe_mk, toAlgEquivAux_def]

lemma toAlgEquivAux_eq_liftNormal [IsGalois k K]
    (g : ProfiniteGrp.ofLimit (profinGalFunctor k K))
    (x : K) (L : FiniteGaloisIntermediateField k K) (hx : x ∈ L.val) :
    toAlgEquivAux g x = (proj L g).liftNormal K x := by
  rw [toAlgEquivAux_def g x L hx]
  exact (AlgEquiv.liftNormal_commutes (proj L g) _ ⟨x, hx⟩).symm

protected lemma AlgEquiv.aut_inv (ϕ : L ≃ₐ[F] L) : ϕ⁻¹ = ϕ.symm := rfl

/--Making `toAlgEquivAux` into an algEquiv by using `proj_lift` repeatedly-/
@[simps]
noncomputable def toAlgEquiv [IsGalois k K] (g : ProfiniteGrp.ofLimit (profinGalFunctor k K)) :
    K ≃ₐ[k] K where
  toFun := toAlgEquivAux g
  invFun := toAlgEquivAux g⁻¹
  left_inv x := by
    let L := adjoin k {x, toAlgEquivAux g x}
    have hx : x ∈ L.val := subset_adjoin _ _ (by simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff, true_or])
    have hx' : toAlgEquivAux g x ∈ L.val := subset_adjoin _ _ (by simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff, or_true])
    simp only [toAlgEquivAux_def _ _ L hx', map_inv, AlgEquiv.aut_inv,
      mk_toAlgEquivAux g x L hx' hx, AlgEquiv.symm_apply_apply]
  right_inv x := by
    let L := adjoin k {x, toAlgEquivAux g⁻¹ x}
    have hx : x ∈ L.val := subset_adjoin _ _ (by simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff, true_or])
    have hx' : toAlgEquivAux g⁻¹ x ∈ L.val := subset_adjoin _ _ (by simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff, or_true])
    simp only [toAlgEquivAux_def _ _ L hx', mk_toAlgEquivAux g⁻¹ x L hx' hx, map_inv,
      AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  map_mul' x y := by
    dsimp
    have hx : x ∈ (adjoin k {x, y}).val := subset_adjoin _ _ (by simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff, true_or])
    have hy : y ∈ (adjoin k {x, y}).val := subset_adjoin _ _ (by simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff, or_true])
    rw [toAlgEquivAux_eq_liftNormal g x (adjoin k {x, y}) hx,
      toAlgEquivAux_eq_liftNormal g y (adjoin k {x, y}) hy,
      toAlgEquivAux_eq_liftNormal g (x * y) (adjoin k {x, y}) (mul_mem hx hy), map_mul]
  map_add' x y := by
    have hx : x ∈ (adjoin k {x, y}).val := subset_adjoin _ _ (by simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff, true_or])
    have hy : y ∈ (adjoin k {x, y}).val := subset_adjoin _ _ (by simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff, or_true])
    simp only [toAlgEquivAux_eq_liftNormal g x (adjoin k {x, y}) hx,
      toAlgEquivAux_eq_liftNormal g y (adjoin k {x, y}) hy,
      toAlgEquivAux_eq_liftNormal g (x + y) (adjoin k {x, y}) (add_mem hx hy), map_add]
  commutes' x := by
    simp only [toAlgEquivAux_eq_liftNormal g _ ⊥ (algebraMap_mem _ x), AlgEquiv.commutes]

variable (k K) in
/--Making `HomtoLimit` into a mulEquiv-/
noncomputable def mulEquivtoLimit [IsGalois k K] :
    (K ≃ₐ[k] K) ≃* ProfiniteGrp.ofLimit (profinGalFunctor k K) where
  toFun := homtoLimit k K
  map_mul' := map_mul _
  invFun := toAlgEquiv
  left_inv := fun f ↦ AlgEquiv.ext fun x =>
    AlgEquiv.restrictNormal_commutes f (adjoin k {x}).val ⟨x, _⟩
  right_inv := fun g ↦ by
    apply Subtype.val_injective
    ext L
    show (toAlgEquiv g).restrictNormal _ = _
    ext x
    have : ((toAlgEquiv g).restrictNormal L.unop) x = (toAlgEquiv g) x.1 := by
      convert AlgEquiv.restrictNormal_commutes (toAlgEquiv g) L.unop x
    simp_rw [this]
    exact proj_lift_adjoin_simple _ _ _ _ x.2

lemma limtoGalContinuous [IsGalois k K] : Continuous (mulEquivtoLimit k K).symm := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _ )
  simp only [map_one, krullTopology_mem_nhds_one]
  intro H ⟨L, _, hO2⟩
  set L' : FiniteGaloisIntermediateField k K := mk <| normalClosure k L K
  have lecl := IntermediateField.le_normalClosure L
  have : L'.val.fixingSubgroup ≤ L.fixingSubgroup := fun σ h => (mem_fixingSubgroup_iff
    (K ≃ₐ[k] K)).mpr (fun y hy => ((mem_fixingSubgroup_iff (K ≃ₐ[k] K)).mp h) y (lecl hy))
  have le1 : (mulEquivtoLimit k K).symm ⁻¹' L.fixingSubgroup ⊆ (mulEquivtoLimit k K).symm ⁻¹' H :=
    fun ⦃a⦄ => fun b => hO2 b
  have le : (mulEquivtoLimit k K).symm ⁻¹' L'.val.fixingSubgroup ⊆ (mulEquivtoLimit k K).symm ⁻¹' H
    := fun ⦃a⦄ b ↦ le1 (this b)
  apply mem_nhds_iff.mpr
  use (mulEquivtoLimit k K).symm ⁻¹' L'.val.fixingSubgroup
  simp only [le, true_and]
  constructor
  · have : (mulEquivtoLimit k K).symm ⁻¹' L'.val.fixingSubgroup =
        mulEquivtoLimit k K '' (L'.val.fixingSubgroup : Set (K ≃ₐ[k] K)) := by
      ext σ
      constructor
      · intro h
        use (mulEquivtoLimit k K).symm σ
        simp only [h.out , MulEquiv.apply_symm_apply, and_self]
      · rintro ⟨_, h1, h2⟩
        simp only [← h2, Set.mem_preimage, MulEquiv.symm_apply_apply, h1]
    rw [this]
    let fix1 : Set ((L : (FiniteGaloisIntermediateField k K)ᵒᵖ) → (profinGalFunctor k K).obj L) :=
      {x : ((L : (FiniteGaloisIntermediateField k K)ᵒᵖ) → (profinGalFunctor k K).obj L)
        | x (op L') = 1}
    have C : Continuous (fun (x : (L : (FiniteGaloisIntermediateField k K)ᵒᵖ) →
      (profinGalFunctor k K).obj L) ↦ x (op L')) :=
      continuous_apply (op L')
    have : mulEquivtoLimit k K '' L'.val.fixingSubgroup = Set.preimage Subtype.val fix1 := by
      ext x
      constructor
      · rintro ⟨α, hα1, hα2⟩
        simp only [Set.mem_preimage,←hα2, fix1, Set.mem_setOf_eq, mulEquivtoLimit, homtoLimit,
          MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk]
        apply AlgEquiv.ext
        intro x
        apply Subtype.val_injective
        rw [← restrict_eq α x.1 L' x.2, AlgEquiv.one_apply]
        exact hα1 x
      · intro h
        simp only [Set.mem_preimage] at h
        use (mulEquivtoLimit _ _).symm x
        simp only [SetLike.mem_coe, MulEquiv.apply_symm_apply, and_true]
        apply (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).mpr
        intro y hy
        simp only [AlgEquiv.smul_def]
        have fix := h.out
        set Aut := (mulEquivtoLimit _ _).symm x
        have : mulEquivtoLimit _ _ Aut = x := by simp only [Aut, MulEquiv.apply_symm_apply]
        simp only [← this, mulEquivtoLimit, homtoLimit, MonoidHom.coe_mk, OneHom.coe_mk,
          MulEquiv.coe_mk, Equiv.coe_fn_mk] at fix
        have fix_y : AlgEquiv.restrictNormalHom L' Aut ⟨y, hy⟩ = ⟨y, hy⟩ := by
          simp only [fix, AlgEquiv.one_apply]
        rw [restrict_eq Aut y L' hy, fix_y]
    have op : IsOpen fix1 := C.isOpen_preimage {1} trivial
    exact this ▸ (isOpen_induced op)
  · simp only [Set.mem_preimage, map_one, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
    Subgroup.mem_toSubmonoid]
    exact congrFun rfl

instance [IsGalois k K] : T2Space (K ≃ₐ[k] K) := krullTopology_t2

variable (k K)

/--Turning mulEquivtoLimit, viewed as a bijection, into a homeomorphism-/
noncomputable def limtoGalHomeo [IsGalois k K] : (ProfiniteGrp.ofLimit (profinGalFunctor k K)) ≃ₜ
    (K ≃ₐ[k] K) := Continuous.homeoOfEquivCompactToT2 limtoGalContinuous

instance [IsGalois k K] : CompactSpace (K ≃ₐ[k] K) :=
  Homeomorph.compactSpace (limtoGalHomeo k K)

instance [IsGalois k K] : TotallyDisconnectedSpace (K ≃ₐ[k] K) :=
  Homeomorph.totallyDisconnectedSpace (limtoGalHomeo k K)

/--Turning `mulEquivtoLimit` into a continuousMulEquiv-/
noncomputable def continuousMulEquivtoLimit [IsGalois k K] :
    ContinuousMulEquiv (K ≃ₐ[k] K) (ProfiniteGrp.ofLimit (profinGalFunctor k K)) where
  toMulEquiv := mulEquivtoLimit k K
  continuous_toFun := (limtoGalHomeo _ _).continuous_invFun
  continuous_invFun := (limtoGalHomeo _ _).continuous_toFun

/--Turning `Gal(K/k)` into a profinite group using the continuousMulEquiv above-/
noncomputable def ProfiniteGalGrp [IsGalois k K] : ProfiniteGrp :=
  ProfiniteGrp.ofContinuousMulEquivProfiniteGrp (continuousMulEquivtoLimit k K).symm

variable {k K} in
theorem restrictNormalHomContinuous (L : IntermediateField k K) [Normal k L] :
    Continuous (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) L) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _ )
  rw [map_one]
  intro N hN
  rw [krullTopology_mem_nhds_one] at hN
  obtain ⟨L', _, hO⟩ := hN
  letI : FiniteDimensional k L' :=
    Module.Finite.equiv <| AlgEquiv.toLinearEquiv <| IntermediateField.lift_algEquiv L L'
  apply mem_nhds_iff.mpr
  use (IntermediateField.lift L').fixingSubgroup
  constructor
  · intro x hx
    rw [Set.mem_preimage]
    apply hO
    simp only [SetLike.mem_coe] at hx ⊢
    rw [IntermediateField.mem_fixingSubgroup_iff] at hx ⊢
    intro y hy
    have := AlgEquiv.restrictNormal_commutes x L y
    dsimp at this
    rw [hx y.1 ((IntermediateField.mem_lift y).mpr hy)] at this
    exact SetLike.coe_eq_coe.mp this
  · exact ⟨by apply IntermediateField.fixingSubgroup_isOpen, congrFun rfl⟩

end InfiniteGalois
