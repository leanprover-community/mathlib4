/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yuyang Zhao, Jujian Zhang
-/

import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!

# Galois Group as a profinite group

In this file, we prove that given a field extension `K/k`, there is a continuous isomorphism between
`Gal(K/k)` and the limit of `Gal(L/k)`, where `L` is a finite Galois intermediate field ordered by
inverse inclusion, thus making `Gal(K/k)` profinite as a limit of finite groups.

# Main definitions and results

In a field extension `K/k`

* `finGaloisGroup L` : The (finite) Galois group `Gal(L/k)` associated to a
  `L : FiniteGaloisIntermediateField k K` `L`.

* `finGaloisGroupMap` : For `FiniteGaloisIntermediateField` s `L₁` and `L₂` with `L₂ ≤ L₁`
  giving the restriction of `Gal(L₁/k)` to `Gal(L₂/k)`

* `finGaloisGroupFunctor` : The functor from `FiniteGaloisIntermediateField`
  (ordered by reverse inclusion) to `FiniteGrp`, mapping each `FiniteGaloisIntermediateField L`
  to `Gal (L/k)`.

* `InfiniteGalois.algEquivToLimit` : The homomorphism from `K ≃ₐ[k] K` to
  `limit (asProfiniteGaloisGroupFunctor k K)`, induced by the projections from `Gal(K/k)` to
  any `Gal(L/k)` where `L` is a `FiniteGaloisIntermediateField`.

* `InfiniteGalois.limitToAlgEquiv` : The inverse of `InfiniteGalois.algEquivToLimit`, in which
  the elements of `K ≃ₐ[k] K` are constructed pointwise.

* `InfiniteGalois.mulEquivToLimit` : The mulEquiv obtained from combining the above two.

* `InfiniteGalois.mulEquivToLimit_continuous` : The inverse of `InfiniteGalois.mulEquivToLimit`
  is continuous.

* `InfiniteGalois.continuousMulEquivToLimit` ：The `ContinuousMulEquiv` between `Gal(K/k)` and
  `limit (asProfiniteGaloisGroupFunctor k K)` given by `InfiniteGalois.mulEquivToLimit`

* `InfiniteGalois.ProfiniteGalGrp` : `Gal(K/k)` as a profinite group as there is
  a `ContinuousMulEquiv` to a `ProfiniteGrp` given above.

* `InfiniteGalois.restrictNormalHomContinuous` : Any `restrictNormalHom` is continuous.

-/

open CategoryTheory Opposite

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section Profinite

/-- The (finite) Galois group `Gal(L / k)` associated to a
`L : FiniteGaloisIntermediateField k K` `L`. -/
def FiniteGaloisIntermediateField.finGaloisGroup (L : FiniteGaloisIntermediateField k K) :
    FiniteGrp :=
  letI := AlgEquiv.fintype k L
  FiniteGrp.of <| L ≃ₐ[k] L

/-- For `FiniteGaloisIntermediateField` s `L₁` and `L₂` with `L₂ ≤ L₁`
  the restriction homomorphism from `Gal(L₁/k)` to `Gal(L₂/k)` -/
noncomputable def finGaloisGroupMap {L₁ L₂ : (FiniteGaloisIntermediateField k K)ᵒᵖ}
    (le : L₁ ⟶ L₂) : L₁.unop.finGaloisGroup ⟶ L₂.unop.finGaloisGroup :=
  haveI : Normal k L₂.unop := IsGalois.to_normal
  letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom le.1)
  haveI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  FiniteGrp.ofHom (AlgEquiv.restrictNormalHom L₂.unop)

namespace finGaloisGroupMap

@[simp]
lemma map_id (L : (FiniteGaloisIntermediateField k K)ᵒᵖ) :
    (finGaloisGroupMap (𝟙 L)) = 𝟙 L.unop.finGaloisGroup :=
  ConcreteCategory.ext (AlgEquiv.restrictNormalHom_id _ _)

@[simp]
lemma map_comp {L₁ L₂ L₃ : (FiniteGaloisIntermediateField k K)ᵒᵖ} (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) :
    finGaloisGroupMap (f ≫ g) = finGaloisGroupMap f ≫ finGaloisGroupMap g := by
  iterate 2
    induction L₁ with | _ L₁ => ?_
    induction L₂ with | _ L₂ => ?_
    induction L₃ with | _ L₃ => ?_
  algebraize [Subsemiring.inclusion g.unop.le, Subsemiring.inclusion f.unop.le,
    Subsemiring.inclusion (g.unop.le.trans f.unop.le)]
  have : IsScalarTower k L₂ L₁ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k L₃ L₁ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k L₃ L₂ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower L₃ L₂ L₁ := IsScalarTower.of_algebraMap_eq' rfl
  ext : 1
  apply IsScalarTower.AlgEquiv.restrictNormalHom_comp k L₃ L₂ L₁

end finGaloisGroupMap

variable (k K) in
/-- The functor from `FiniteGaloisIntermediateField` (ordered by reverse inclusion) to `FiniteGrp`,
mapping each `FiniteGaloisIntermediateField` `L` to `Gal (L/k)` -/
noncomputable def finGaloisGroupFunctor : (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ FiniteGrp where
  obj L := L.unop.finGaloisGroup
  map := finGaloisGroupMap
  map_id := finGaloisGroupMap.map_id
  map_comp := finGaloisGroupMap.map_comp

open FiniteGaloisIntermediateField ProfiniteGrp

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace InfiniteGalois

variable (k K) in
/-- The composition of `finGaloisGroupFunctor` with
the forgetful functor from `FiniteGrp` to `ProfiniteGrp`. -/
noncomputable abbrev asProfiniteGaloisGroupFunctor :
    (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ ProfiniteGrp :=
  (finGaloisGroupFunctor k K) ⋙ forget₂ FiniteGrp ProfiniteGrp

variable (k K) in
/--
The homomorphism from `Gal(K/k)` to `lim Gal(L/k)` where `L` is a
`FiniteGaloisIntermediateField k K` ordered by inverse inclusion. It is induced by the
canonical projections from `Gal(K/k)` to `Gal(L/k)`.
-/
noncomputable def algEquivToLimit : (K ≃ₐ[k] K) →* limit (asProfiniteGaloisGroupFunctor k K) where
  toFun σ := {
    val := fun L ↦ σ.restrictNormalHom L.unop
    property := fun {L₁ L₂} π ↦ by
      algebraize [Subsemiring.inclusion π.1.le]
      have : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
      have : IsScalarTower L₂.unop L₁.unop K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
      apply (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L₂.unop L₁.unop σ).symm }
  map_one' := by
    simp only [map_one]
    rfl
  map_mul' x y := by
    simp only [map_mul]
    rfl

theorem restrictNormalHom_continuous (L : IntermediateField k K) [Normal k L] :
    Continuous (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) L) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _ )
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨L', _, hO⟩ := hN
  have := Module.Finite.equiv <| AlgEquiv.toLinearEquiv <| IntermediateField.liftAlgEquiv L'
  apply mem_nhds_iff.mpr
  use (IntermediateField.lift L').fixingSubgroup
  constructor
  · intro x hx
    apply hO
    simp only [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hx ⊢
    intro y hy
    have := AlgEquiv.restrictNormal_commutes x L y
    dsimp at this
    rw [hx y.1 ((IntermediateField.mem_lift y).mpr hy)] at this
    exact SetLike.coe_eq_coe.mp this
  · exact ⟨IntermediateField.fixingSubgroup_isOpen (IntermediateField.lift L') , congrFun rfl⟩

lemma algEquivToLimit_continuous : Continuous (algEquivToLimit k K) := by
  rw [continuous_induced_rng]
  refine continuous_pi (fun L ↦ ?_)
  convert restrictNormalHom_continuous L.unop.1
  exact (DiscreteTopology.eq_bot (α := L.unop ≃ₐ[k] L.unop)).symm

/-- The projection map from `lim Gal(L/k)` to a specific `Gal(L/k)`. -/
noncomputable def proj (L : FiniteGaloisIntermediateField k K) :
    limit (asProfiniteGaloisGroupFunctor k K) →* (L ≃ₐ[k] L) where
  toFun g := g.val (op L)
  map_one' := rfl
  map_mul' _ _ := rfl

lemma finGaloisGroupFunctor_map_proj_eq_proj (g : limit (asProfiniteGaloisGroupFunctor k K))
    {L₁ L₂ : FiniteGaloisIntermediateField k K} (h : L₁ ⟶ L₂) :
    (finGaloisGroupFunctor k K).map h.op (proj L₂ g) = proj L₁ g :=
  g.prop h.op

lemma proj_of_le (L : FiniteGaloisIntermediateField k K)
    (g : limit (asProfiniteGaloisGroupFunctor k K)) (x : L)
    (L' : FiniteGaloisIntermediateField k K) (h : L ≤ L') :
    (proj L g x).val = (proj L' g ⟨x, h x.2⟩).val := by
  induction L with | _ L => ?_
  induction L' with | _ L' => ?_
  letI : Algebra L L' := RingHom.toAlgebra (Subsemiring.inclusion h)
  letI : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← finGaloisGroupFunctor_map_proj_eq_proj g h.hom]
  show (algebraMap L' K (algebraMap L L' (AlgEquiv.restrictNormal (proj (mk L') g) L x))) = _
  rw [AlgEquiv.restrictNormal_commutes (proj (mk L') g) L]
  rfl

lemma proj_adjoin_singleton_val [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K))
    (x : K) (y : adjoin k {x}) (L : FiniteGaloisIntermediateField k K)
    (h : x ∈ L.toIntermediateField) :
    (proj (adjoin k {x}) g y).val = (proj L g ⟨y, adjoin_simple_le_iff.mpr h y.2⟩).val :=
  proj_of_le _ g y _ _

/-- A function from `K` to `K` defined pointwise using a family of compatible elements of
`Gal(L/k)` where `L` is a `FiniteGaloisIntermediateField` -/
private noncomputable def toAlgEquivAux [IsGalois k K]
    (g : limit (asProfiniteGaloisGroupFunctor k K)) : K → K :=
  fun x ↦ (proj (adjoin k {x}) g ⟨x, subset_adjoin _ _ (by simp only [Set.mem_singleton_iff])⟩).val

lemma toAlgEquivAux_eq_proj_of_mem [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K))
    (x : K) (L : FiniteGaloisIntermediateField k K) (hx : x ∈ L.toIntermediateField) :
    toAlgEquivAux g x = (proj L g ⟨x, hx⟩).val :=
  proj_adjoin_singleton_val g _ _ L hx

lemma mk_toAlgEquivAux [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K)) (x : K)
    (L : FiniteGaloisIntermediateField k K) (hx' : toAlgEquivAux g x ∈ L.toIntermediateField)
    (hx : x ∈ L.toIntermediateField) :
    (⟨toAlgEquivAux g x, hx'⟩ : L.toIntermediateField) = proj L g ⟨x, hx⟩ := by
  rw [Subtype.eq_iff, Subtype.coe_mk, toAlgEquivAux_eq_proj_of_mem]

lemma toAlgEquivAux_eq_liftNormal [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K))
    (x : K) (L : FiniteGaloisIntermediateField k K) (hx : x ∈ L.toIntermediateField) :
    toAlgEquivAux g x = (proj L g).liftNormal K x := by
  rw [toAlgEquivAux_eq_proj_of_mem g x L hx]
  exact (AlgEquiv.liftNormal_commutes (proj L g) _ ⟨x, hx⟩).symm

/-- `toAlgEquivAux` as an `AlgEquiv`.
It is done by using above lifting lemmas on bigger `FiniteGaloisIntermediateField`. -/
@[simps]
noncomputable def limitToAlgEquiv [IsGalois k K]
    (g : limit (asProfiniteGaloisGroupFunctor k K)) : K ≃ₐ[k] K where
  toFun := toAlgEquivAux g
  invFun := toAlgEquivAux g⁻¹
  left_inv x := by
    let L := adjoin k {x, toAlgEquivAux g x}
    have hx : x ∈ L.1 := subset_adjoin _ _ (Set.mem_insert x {toAlgEquivAux g x})
    have hx' : toAlgEquivAux g x ∈ L.1 := subset_adjoin _ _ (Set.mem_insert_of_mem x rfl)
    simp only [toAlgEquivAux_eq_proj_of_mem _ _ L hx', map_inv, AlgEquiv.aut_inv,
      mk_toAlgEquivAux g x L hx' hx, AlgEquiv.symm_apply_apply]
  right_inv x := by
    let L := adjoin k {x, toAlgEquivAux g⁻¹ x}
    have hx : x ∈ L.1 := subset_adjoin _ _ (Set.mem_insert x {toAlgEquivAux g⁻¹ x})
    have hx' : toAlgEquivAux g⁻¹ x ∈ L.1 := subset_adjoin _ _ (Set.mem_insert_of_mem x rfl)
    simp only [toAlgEquivAux_eq_proj_of_mem _ _ L hx', mk_toAlgEquivAux g⁻¹ x L hx' hx, map_inv,
      AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  map_mul' x y := by
    have hx : x ∈ (adjoin k {x, y}).1 := subset_adjoin _ _ (Set.mem_insert x {y})
    have hy : y ∈ (adjoin k {x, y}).1 := subset_adjoin _ _ (Set.mem_insert_of_mem x rfl)
    rw [toAlgEquivAux_eq_liftNormal g x (adjoin k {x, y}) hx,
      toAlgEquivAux_eq_liftNormal g y (adjoin k {x, y}) hy,
      toAlgEquivAux_eq_liftNormal g (x * y) (adjoin k {x, y}) (mul_mem hx hy), map_mul]
  map_add' x y := by
    have hx : x ∈ (adjoin k {x, y}).1 := subset_adjoin _ _ (Set.mem_insert x {y})
    have hy : y ∈ (adjoin k {x, y}).1 := subset_adjoin _ _ (Set.mem_insert_of_mem x rfl)
    simp only [toAlgEquivAux_eq_liftNormal g x (adjoin k {x, y}) hx,
      toAlgEquivAux_eq_liftNormal g y (adjoin k {x, y}) hy,
      toAlgEquivAux_eq_liftNormal g (x + y) (adjoin k {x, y}) (add_mem hx hy), map_add]
  commutes' x := by
    simp only [toAlgEquivAux_eq_liftNormal g _ ⊥ (algebraMap_mem _ x), AlgEquiv.commutes]

variable (k K) in
/-- `algEquivToLimit` as a `MulEquiv`. -/
noncomputable def mulEquivToLimit [IsGalois k K] :
    (K ≃ₐ[k] K) ≃* limit (asProfiniteGaloisGroupFunctor k K) where
  toFun := algEquivToLimit k K
  map_mul' := map_mul _
  invFun := limitToAlgEquiv
  left_inv := fun f ↦ AlgEquiv.ext fun x ↦
    AlgEquiv.restrictNormal_commutes f (adjoin k {x}).1 ⟨x, _⟩
  right_inv := fun g ↦ by
    apply Subtype.val_injective
    ext L
    show (limitToAlgEquiv g).restrictNormal _ = _
    ext x
    have : ((limitToAlgEquiv g).restrictNormal L.unop) x = (limitToAlgEquiv g) x.1 := by
      exact AlgEquiv.restrictNormal_commutes (limitToAlgEquiv g) L.unop x
    simp_rw [this]
    exact proj_adjoin_singleton_val _ _ _ _ x.2

open scoped Topology in
lemma krullTopology_mem_nhds_one_iff_of_isGalois [IsGalois k K] (A : Set (K ≃ₐ[k] K)) :
    A ∈ 𝓝 1 ↔ ∃ (L : FiniteGaloisIntermediateField k K), (L.fixingSubgroup : Set _) ⊆ A := by
  rw [krullTopology_mem_nhds_one_iff_of_normal]
  exact ⟨fun ⟨L, _, hL, hsub⟩ ↦ ⟨{ toIntermediateField := L, isGalois := ⟨⟩ }, hsub⟩,
    fun ⟨L, hL⟩ ↦ ⟨L, inferInstance, inferInstance, hL⟩⟩

lemma isOpen_mulEquivToLimit_image_fixingSubgroup [IsGalois k K]
    (L : FiniteGaloisIntermediateField k K) : IsOpen (mulEquivToLimit k K '' L.fixingSubgroup) := by
  let fix1 : Set (Π L, (asProfiniteGaloisGroupFunctor k K).obj L) := {f | f (op L) = 1}
  suffices mulEquivToLimit k K '' L.1.fixingSubgroup = Set.preimage Subtype.val fix1 by
    rw [this]
    exact (isOpen_induced <| (continuous_apply (op L)).isOpen_preimage {1} trivial)
  ext x
  obtain ⟨σ, rfl⟩ := (mulEquivToLimit k K).surjective x
  simpa using FiniteGaloisIntermediateField.mem_fixingSubgroup_iff _ _

lemma mulEquivToLimit_symm_continuous [IsGalois k K] : Continuous (mulEquivToLimit k K).symm := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _ )
  simp only [map_one, krullTopology_mem_nhds_one_iff_of_isGalois, ← MulEquiv.coe_toEquiv_symm,
    ← MulEquiv.toEquiv_eq_coe, ← (mulEquivToLimit k K).image_eq_preimage]
  intro H ⟨L, le⟩
  rw [mem_nhds_iff]
  use mulEquivToLimit k K '' L.1.fixingSubgroup
  simp only [isOpen_mulEquivToLimit_image_fixingSubgroup L]
  simpa [one_mem] using Set.image_subset_iff.mp (Set.image_mono le)

variable (k K)

/-- The `ContinuousMulEquiv` between `K ≃ₐ[k] K` and `lim Gal(L/k)` where `L` is a
  `FiniteGaloisIntermediateField` ordered by inverse inclusion, obtained
  from `InfiniteGalois.mulEquivToLimit` -/
noncomputable def continuousMulEquivToLimit [IsGalois k K] :
    (K ≃ₐ[k] K) ≃ₜ* limit (asProfiniteGaloisGroupFunctor k K) where
  toMulEquiv := mulEquivToLimit k K
  continuous_toFun := algEquivToLimit_continuous
  continuous_invFun := mulEquivToLimit_symm_continuous

instance [IsGalois k K] : CompactSpace (K ≃ₐ[k] K) :=
  (continuousMulEquivToLimit k K).symm.compactSpace

/-- `Gal(K/k)` as a profinite group as there is
a `ContinuousMulEquiv` to a `ProfiniteGrp` given above -/
noncomputable def profiniteGalGrp [IsGalois k K] : ProfiniteGrp :=
  ProfiniteGrp.of (K ≃ₐ[k] K)

/-- The categorical isomorphism between `profiniteGalGrp` and `lim Gal(L/k)` where `L` is a
  `FiniteGaloisIntermediateField` ordered by inverse inclusion -/
noncomputable def profiniteGalGrpIsoLimit [IsGalois k K] :
    profiniteGalGrp k K ≅ limit (asProfiniteGaloisGroupFunctor k K) :=
  ContinuousMulEquiv.toProfiniteGrpIso (continuousMulEquivToLimit k K)

end InfiniteGalois

end Profinite
