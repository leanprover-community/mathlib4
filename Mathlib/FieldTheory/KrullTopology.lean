/-
Copyright (c) 2022 Sebastian Monnet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Monnet, Aaron Liu
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
-- this `import` is only used in the deprecated material at the bottom of the file
-- it should be removed when the deprecated material is removed
public import Mathlib.Topology.Algebra.FilterBasis

import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.UniformSpace.Separation

/-!
# Krull topology

We define the Krull topology on `Gal(L/K)` for an arbitrary field extension `L/K`, whose basic
open neighborhoods of `1` are given by `E.fixingSubgroup`, where `E` ranges over intermediate
field between `L` and `K` such that `E/K` is finitely generated.

## Main Definitions

- `krullTopology K L`. Given a field extension `L/K`, this is the topology on `Gal(L/K)`.

## Main Results

- `krullTopology_t2 K L`. For an integral field extension `L/K`, the topology `krullTopology K L`
  is Hausdorff.

- `krullTopology_isTotallySeparated K L`. For an integral field extension `L/K`, the topology
  `krullTopology K L` is totally separated.

- `stabilizer_isOpen_of_isIntegral`: For an integral field extension `L/K`, the stabilizer
  in `Gal(L/K)` of any element in `L` is open for the Krull topology.

## Notation

- In docstrings, we will write `Gal(L/E)` to denote the fixing subgroup of an intermediate field
  `E`. That is, `Gal(L/E)` is the subgroup of `Gal(L/K)` consisting of automorphisms that fix
  every element of `E`. In particular, we distinguish between `Gal(L/E)` and `Gal(L/E)`, since the
  former is defined to be a subgroup of `Gal(L/K)`, while the latter is a group in its own right.

## Implementation Notes

We first define a `UniformGroup` structure on `Gal(L/K)`,
and use this to construct the Krull topology.
This lets us use the uniform structure to easily prove compactness of the Krull topology,
by showing it is complete and totally bounded.
-/

public section

open Filter
open scoped Pointwise Uniformity

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable (K L) in
/-- For a field extension `L/K`, we equiv `Gal(L/K)` with the left uniform structure. -/
@[no_expose]
instance : UniformSpace Gal(L/K) := .ofCore
  { uniformity := ⨅ x : L, 𝓟 {p | p.1 x = p.2 x}
    refl := le_iInf fun _ => principal_mono.2 (SetRel.id_subset_iff.2 ⟨fun _ => rfl⟩)
    symm := tendsto_iInf_iInf fun _ => Set.MapsTo.tendsto fun _ => Eq.symm
    comp := le_iInf fun x => lift'_le (mem_iInf_of_mem x (mem_principal_self _))
      (principal_mono.2 (SetRel.isTrans_iff_comp_subset_self.1 ⟨fun _ _ _ => Eq.trans⟩)) }

theorem krullTopology_uniformity_def : 𝓤 Gal(L/K) = ⨅ x : L, 𝓟 {p | p.1 x = p.2 x} := (rfl)

open SetRel in
theorem krullTopology_mem_uniformity_iff {s : SetRel Gal(L/K) Gal(L/K)} :
    s ∈ 𝓤 Gal(L/K) ↔ ∃ u : Finset L, ∀ σ τ : Gal(L/K), Set.EqOn σ τ u → σ ~[s] τ := by
  rw [krullTopology_uniformity_def, Filter.mem_iInf_finite]
  refine exists_congr fun u => ?_
  rw [Filter.iInf_principal_finset, Filter.mem_principal, Set.subset_def, Prod.forall]
  refine forall_congr' fun σ => forall_congr' fun τ => imp_congr_left ?_
  rw [Set.mem_iInter₂]
  rfl

variable (K L) in
/-- For a field extension `L/K`, `krullTopology K L` is the topological space structure on
`Gal(L/K)` induced by the uniform structure. -/
instance krullTopology : TopologicalSpace Gal(L/K) := inferInstance

variable (K L) in
/-- For a field extension `L/K`, the Krull topology on `Gal(L/K)` makes it a topological group. -/
@[stacks 0BMJ "We define the Krull topology directly without proving the universal property"]
instance : IsLeftUniformGroup Gal(L/K) where
  continuous_mul := by
    rw [Uniform.continuous_iff'_left]
    intro p
    rw [nhds_eq_comap_uniformity', uniformity_prod, comap_inf, comap_comap, comap_comap,
      krullTopology_uniformity_def, comap_iInf, comap_iInf, tendsto_iInf]
    intro x
    rw [tendsto_principal, eventually_inf]
    refine ⟨{στ | στ.1 (p.2 x) = p.1 (p.2 x)}, ?_, {στ | στ.2 x = p.2 x}, ?_, ?_⟩
    · exact mem_iInf_of_mem (p.2 x) (by simp)
    · exact mem_iInf_of_mem x (by simp)
    · simp +contextual
  continuous_inv := by
    rw [Uniform.continuous_iff'_right]
    intro p
    rw [nhds_eq_comap_uniformity', krullTopology_uniformity_def, comap_iInf, tendsto_iInf]
    intro x
    apply tendsto_iInf' (p.symm x)
    rw [comap_principal, tendsto_principal_principal]
    intro σ hp
    apply σ.eq_symm_apply.mpr
    simpa using hp
  uniformity_eq := by
    rw [nhds_eq_comap_uniformity, comap_comap, krullTopology_uniformity_def, comap_iInf]
    refine iInf_congr fun x => ?_
    simp [AlgEquiv.eq_symm_apply]

-- open IntermediateField in
-- variable (K L) in
-- /-- For a field extension `L/K`, the Krull topology on `Gal(L/K)` makes it a topological group. -/
-- @[stacks 0BMJ "We define the Krull topology directly without proving the universal property"]
-- instance : IsUniformGroup Gal(L/K) where
--   uniformContinuous_div s hs := by
--     rw [krullTopology_mem_uniformity_iff] at hs
--     obtain ⟨F, _, hF⟩ := hs
--     rw [uniformity_prod_eq_prod, map_map, mem_map, mem_prod_self_iff]
--     refine ⟨{p | Set.EqOn p.1 p.2 (normalClosure K F L)}, ?_, ?_⟩
--     · rw [krullTopology_mem_uniformity_iff]
--       exact ⟨_, inferInstance, fun _ _ h => h⟩
--     rw [Set.prod_subset_iff]
--     intro σ hσ τ hτ
--     simp only [Set.mem_preimage, Function.comp_apply]
--     refine hF _ _ fun x hx => ?_
--     simp only [div_eq_mul_inv, AlgEquiv.mul_apply, AlgEquiv.coe_inv]
--     have hn : τ.1.symm x ∈ normalClosure K F L := by
--       have h : (AlgHom.comp τ.1.symm (IsScalarTower.toAlgHom K F L)).fieldRange ≤
--           normalClosure K F L := AlgHom.fieldRange_le_normalClosure _
--       exact h (by simpa using hx)
--     rw [hσ hn, σ.2.injective.eq_iff, AlgEquiv.eq_symm_apply, ← hτ hn, τ.1.apply_symm_apply]

open IntermediateField in
open scoped Topology in
lemma krullTopology_mem_nhds_one_iff' {s : Set Gal(L/K)} :
    s ∈ 𝓝 1 ↔ ∃ E : IntermediateField K L, E.FG ∧ (E.fixingSubgroup : Set Gal(L/K)) ⊆ s := by
  rw [nhds_eq_comap_uniformity', ← le_principal_iff, comap_le_iff_le_kernMap,
    kernMap_principal, le_principal_iff, krullTopology_mem_uniformity_iff]
  simp_rw [← Prod.forall', ← Set.ofPred_subset_ofPred, Prod.eta, Set.ofPred_mem_eq,
    Set.subset_kernImage_iff, Set.preimage_ofPred_eq, Set.ofPred_subset,
    FG, existsAndEq, true_and, Set.subset_def, SetLike.mem_coe,
    IntermediateField.mem_fixingSubgroup_iff, Set.EqOn, AlgEquiv.one_apply]
  refine exists_congr fun u => forall_congr' fun σ => imp_congr_left ?_
  revert σ
  have hst (σ : Gal(L/K)) (x : L) : σ x = x ↔ x ∈ fixedField (Subgroup.zpowers σ) := by
    rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← adjoin_le_iff, le_iff_le,
      Subgroup.zpowers_le, ← AlgEquiv.smul_def, ← MulAction.mem_stabilizer_iff]
    revert σ
    rw [← SetLike.ext_iff, le_antisymm_iff, ← le_iff_le, adjoin_simple_le_iff]
    constructor
    · simp
    · intro σ hσ
      simpa using hσ ⟨x, mem_adjoin_simple_self K x⟩
  simp_rw [hst, ← Set.ofPred_subset_ofPred, SetLike.setOfPred_mem_eq,
    Set.ofPred_mem_eq, SetLike.coe_subset_coe, adjoin_le_iff, forall_true_iff]

open IntermediateField in
open scoped Topology in
lemma krullTopology_mem_nhds_one_iff [Algebra.IsAlgebraic K L] {s : Set Gal(L/K)} :
    s ∈ 𝓝 1 ↔ ∃ E : IntermediateField K L,
    FiniteDimensional K E ∧ (E.fixingSubgroup : Set Gal(L/K)) ⊆ s := by
  rw [krullTopology_mem_nhds_one_iff']
  refine exists_congr fun E => and_congr_left' ?_
  rw [← IntermediateField.essFiniteType_iff]
  exact ⟨fun _ => Algebra.finite_of_essFiniteType_of_isAlgebraic, fun _ => inferInstance⟩

open scoped Topology in
lemma krullTopology_mem_nhds_one_iff_of_normal [Normal K L] {s : Set Gal(L/K)} :
    s ∈ 𝓝 1 ↔ ∃ E : IntermediateField K L,
    FiniteDimensional K E ∧ Normal K E ∧ (E.fixingSubgroup : Set Gal(L/K)) ⊆ s := by
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨fun ⟨E, _, hE⟩ ↦ ?_, fun ⟨E, hE⟩ ↦ ⟨E, hE.1, hE.2.2⟩⟩
  use (IntermediateField.normalClosure K E L)
  simp only [normalClosure.is_finiteDimensional K E L, normalClosure.normal K E L, true_and]
  exact le_trans (E.fixingSubgroup_antitone E.le_normalClosure) hE

section KrullT2

open scoped Topology Filter

/-- Let `L/E/K` be a tower of fields with `E/K` finitely generated.
Then `Gal(L/E)` is an open subgroup of `Gal(L/K)`. -/
theorem IntermediateField.isOpen_fixingSubgroup (E : IntermediateField K L)
    [Algebra.EssFiniteType K E] : IsOpen (E.fixingSubgroup : Set Gal(L/K)) :=
  Subgroup.isOpen_of_mem_nhds _ (krullTopology_mem_nhds_one_iff'.2
    ⟨E, essFiniteType_iff.1 ‹_›, subset_rfl⟩)

@[deprecated (since := "2026-03-05")]
alias IntermediateField.fixingSubgroup_isOpen := IntermediateField.isOpen_fixingSubgroup

/-- Given a tower of fields `L/E/K`, the subgroup `Gal(L/E) ≤ Gal(L/K)` is closed. -/
theorem IntermediateField.isClosed_fixingSubgroup (E : IntermediateField K L) :
    IsClosed (E.fixingSubgroup : Set Gal(L/K)) := by
  have hx (x : E) : IsClosed ((adjoin K {(x : L)}).fixingSubgroup : Set Gal(L/K)) :=
    have : Algebra.EssFiniteType K (adjoin K {(x : L)}) :=
      essFiniteType_iff.2 (fg_adjoin_of_finite (Set.finite_singleton _))
    Subgroup.isClosed_of_isOpen _ (isOpen_fixingSubgroup _)
  convert isClosed_iInter hx
  ext g
  simp only [SetLike.mem_coe, mem_fixingSubgroup_iff, Set.mem_iInter, Subtype.forall]
  exact ⟨fun h a ha x hx => h x (adjoin_simple_le_iff.2 ha hx),
    fun h x hx => h x hx x (mem_adjoin_simple_self K x)⟩

@[deprecated (since := "2026-03-05")]
alias IntermediateField.fixingSubgroup_isClosed := IntermediateField.isClosed_fixingSubgroup

end KrullT2

section TotallySeparated

instance : TotallySeparatedSpace Gal(L/K) := by
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro σ τ h_diff
  have hστ : σ⁻¹ * τ ≠ 1 := by rwa [Ne, inv_mul_eq_one]
  rcases DFunLike.exists_ne hστ with ⟨x, hx : (σ⁻¹ * τ) x ≠ x⟩
  let E := IntermediateField.adjoin K ({x} : Set L)
  have fg : Algebra.EssFiniteType K E :=
    IntermediateField.essFiniteType_iff.2
      (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton _))
  refine ⟨σ • E.fixingSubgroup,
    ⟨E.isClosed_fixingSubgroup.leftCoset σ, E.isOpen_fixingSubgroup.leftCoset σ⟩,
    ⟨1, E.fixingSubgroup.one_mem', mul_one σ⟩, ?_⟩
  simp only [Set.mem_compl_iff, mem_leftCoset_iff, SetLike.mem_coe,
    IntermediateField.mem_fixingSubgroup_iff, not_forall]
  exact ⟨x, IntermediateField.mem_adjoin_simple_self K x, hx⟩

/-- The Krull topology on `Gal(L/K)` is Hausdorff. -/
instance krullTopology_t2 : T2Space Gal(L/K) := TotallySeparatedSpace.t2Space

/-- The Krull topology on `Gal(L/K)` is totally separated. -/
@[deprecated TotallySeparatedSpace.isTotallySeparated_univ (since := "2026-03-05")]
theorem krullTopology_isTotallySeparated :
    IsTotallySeparated (Set.univ : Set Gal(L/K)) :=
  (totallySeparatedSpace_iff _).mp inferInstance

end TotallySeparated

variable (K L) in
instance krullTopology_discreteUniformity_of_essFiniteType
    [Algebra.EssFiniteType K L] : DiscreteUniformity Gal(L/K) := by
  rw [discreteUniformity_iff_eq_principal_setRelId, le_antisymm_iff,
    and_iff_left refl_le_uniformity, krullTopology_uniformity_def]
  obtain ⟨s, hs⟩ := IntermediateField.fg_top K L
  rw [Filter.le_principal_iff, Filter.mem_iInf_finite]
  refine ⟨s, ?_⟩
  rw [Filter.iInf_principal_finset, Filter.mem_principal]
  intro p hp
  rw [Set.mem_iInter₂] at hp
  have hpe (x : L) : p.1 x = p.2 x ↔
      x ∈ IntermediateField.fixedField (Subgroup.zpowers (p.1⁻¹ * p.2)) := by
    rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← IntermediateField.adjoin_le_iff,
      IntermediateField.le_iff_le, Subgroup.zpowers_le, ← p.1.eq_symm_apply,
      ← AlgEquiv.coe_inv, ← AlgEquiv.mul_apply, ← AlgEquiv.smul_def, eq_comm,
      ← MulAction.mem_stabilizer_iff]
    generalize p.1⁻¹ * p.2 = σ
    revert σ
    rw [← SetLike.ext_iff, le_antisymm_iff, ← IntermediateField.le_iff_le,
      IntermediateField.adjoin_simple_le_iff]
    constructor
    · simp
    · intro σ hσ
      simpa using hσ ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  ext x
  have hx : x ∈ (⊤ : IntermediateField K L) := IntermediateField.mem_top
  rw [hpe]
  revert x hx
  rw [← SetLike.le_def, ← hs, IntermediateField.adjoin_le_iff]
  intro x hx
  rw [SetLike.mem_coe, ← hpe]
  exact hp x hx

theorem AlgEquiv.totallyBounded_fixingSubgroup
    (E : IntermediateField K L) [Algebra.IsAlgebraic E L] :
    TotallyBounded (E.fixingSubgroup : Set Gal(L/K)) := by
  intro U hU
  rw [krullTopology_mem_uniformity_iff] at hU
  obtain ⟨s, hs⟩ := hU
  let F := IntermediateField.adjoin E (s : Set L)
  have : IsScalarTower K F L := ⟨fun a b c => smul_assoc a b.1 c⟩
  have : FiniteDimensional E F :=
    IntermediateField.finiteDimensional_adjoin fun _ _ => Algebra.IsIntegral.isIntegral _
  let f (σ : Gal(L/E)) : F →ₐ[E] L := σ.toAlgHom.comp (IsScalarTower.toAlgHom E F L)
  refine ⟨Set.range (AlgEquiv.restrictScalars K ∘ Function.invFun f),
    Set.finite_range _, fun σ hσ => ?_⟩
  let σE := E.fixingSubgroupEquiv ⟨σ, hσ⟩
  rw [Set.biUnion_range]
  refine Set.mem_iUnion_of_mem (f σE) (hs σ _ fun x hx => ?_)
  let xE : F := ⟨x, IntermediateField.mem_adjoin_of_mem E hx⟩
  have hf : f (Function.invFun f (f σE)) xE = f σE xE :=
    DFunLike.congr_fun (Function.invFun_eq ⟨σE, rfl⟩) xE
  -- TODO: add API for `IntermediateField.fixingSubgroup`
  simpa [f, σE, xE, IntermediateField.fixingSubgroupEquiv] using hf.symm

variable (K L) in
theorem AlgEquiv.totallyBounded_univ [Algebra.IsAlgebraic K L] :
    TotallyBounded (Set.univ : Set Gal(L/K)) := by
  rw [← Subgroup.coe_top, ← IntermediateField.fixingSubgroup_bot]
  exact AlgEquiv.totallyBounded_fixingSubgroup ⊥

variable (K L) in
open IntermediateField in
instance [Algebra.IsIntegral K L] : CompactSpace Gal(L/K) where
  isCompact_univ := by
    stop
    apply (AlgEquiv.totallyBounded_univ K L).isCompact_of_isComplete
    intro f hf _
    rw [cauchy_iff] at hf
    obtain ⟨_, hf⟩ := hf
    replace hf (F : IntermediateField K L) (_ : FiniteDimensional K F) :
        ∃ σ : Gal(L/K), ∀ᶠ τ : Gal(L/K) in f, Set.EqOn σ τ F := by
      obtain ⟨t, hf, ht⟩ := hf {p | Set.EqOn p.1 p.2 F}
        (krullTopology_mem_uniformity_iff.2 ⟨F, ‹_›, fun _ _ h => h⟩)
      obtain ⟨σ, hσ⟩ := Filter.nonempty_of_mem hf
      exact ⟨σ, Filter.eventually_of_mem hf fun τ hτ => @ht (σ, τ) ⟨hσ, hτ⟩⟩
    have h (x : L) : ∃ y, ∀ᶠ τ in f, y = τ x :=
      (hf (adjoin K {x}) (adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x))).elim
        fun σ hσ => ⟨σ x, hσ.mono fun τ hτ => hτ (mem_adjoin_simple_self K x)⟩
    choose s hs using h
    let σ : Gal(L/K) := .ofBijective
      { toFun := s
        map_zero' := (hs 0).exists.elim fun _ h => by simp [h]
        map_one' := (hs 1).exists.elim fun _ h => by simp [h]
        commutes' x := (hs (algebraMap K L x)).exists.elim fun _ h => by simp [h]
        map_add' x y := by
          obtain ⟨τ, hτ⟩ := ((hs x).and ((hs y).and (hs (x + y)))).exists
          simp [hτ.1, hτ.2.1, hτ.2.2]
        map_mul' x y := by
          obtain ⟨τ, hτ⟩ := ((hs x).and ((hs y).and (hs (x * y)))).exists
          simp [hτ.1, hτ.2.1, hτ.2.2] } <| by
      refine ⟨RingHom.injective _, fun x => ?_⟩
      obtain ⟨τ, hτ⟩ :=
        ((Filter.eventually_all_finite ((minpoly K x).rootSet_finite L)).2
          fun y hy => hs y).exists
      suffices h : τ.symm x ∈ (minpoly K x).rootSet L from ⟨τ.symm x, by simp [hτ (τ.symm x) h]⟩
      rw [Polynomial.mem_rootSet_of_ne (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)),
        Polynomial.aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval, map_zero]
    refine ⟨σ, Set.mem_univ σ, fun U hU => ?_⟩
    rw [← map_mul_left_nhds_one, Filter.mem_map, krullTopology_mem_nhds_one_iff] at hU
    obtain ⟨F, _, hF⟩ := hU
    rw [← Set.image_subset_iff] at hF
    refine Filter.mem_of_superset ?_ hF
    obtain ⟨σ', hσ'⟩ := hf F ‹_›
    have eq : Set.EqOn σ σ' F := fun x hx =>
      ((hs x).and hσ').exists.elim fun _ h => h.1.trans (h.2 hx).symm
    filter_upwards [hσ'] with τ hτ using
      ⟨_, (F.mem_fixingSubgroup_iff _).2 fun x hx =>
        by simp [AlgEquiv.symm_apply_eq, eq hx, hτ hx], mul_inv_cancel_left σ τ⟩

section MulAction

/-- The stabilizer in `Gal(L/K)` of any element in `L` is open for the Krull topology. -/
theorem stabilizer_isOpen_of_isIntegral (x : L) :
    IsOpen (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) := by
  open IntermediateField in
  let E := adjoin K {x}
  have hL : Algebra.EssFiniteType K E := IntermediateField.essFiniteType_iff.2
    (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton _))
  convert! isOpen_fixingSubgroup E
  ext g
  simpa using (forall_mem_adjoin_smul_eq_self_iff K (S := {x}) g).symm

end MulAction

section deprecated

/-!
The definitions and theorems in this section were formerly implementation details
used in the definition of the Krull topology. Since the Krull topology is now defined in
terms of the uniform group structure on `Gal(L/K)`, they are now unused,
and have been deprecated without replacement.

When this section is removed then the `public import Mathlib.Topology.Algebra.FilterBasis` at
the top of this file should be removed too.
-/

/-- Given a field extension `L/K`, `finiteExts K L` is the set of
intermediate field extensions `L/E/K` such that `E/K` is finite. -/
@[deprecated "deprecated without replacement" (since := "2026-03-05")]
def finiteExts (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L] :
    Set (IntermediateField K L) :=
  {E | FiniteDimensional K E}

/-- Given a field extension `L/K`, `fixedByFinite K L` is the set of
subsets `Gal(L/E)` of `Gal(L/K)`, where `E/K` is finite. -/
@[deprecated "deprecated without replacement" (since := "2026-03-05")]
def fixedByFinite (K L : Type*) [Field K] [Field L] [Algebra K L] : Set (Subgroup Gal(L/K)) :=
  IntermediateField.fixingSubgroup '' finiteExts K L

/-- If `L/K` is a field extension, then we have `Gal(L/K) ∈ fixedByFinite K L`. -/
@[deprecated "deprecated without replacement" (since := "2026-03-05")]
theorem top_fixedByFinite {K L : Type*} [Field K] [Field L] [Algebra K L] :
    ⊤ ∈ fixedByFinite K L :=
  ⟨⊥, IntermediateField.instFiniteSubtypeMemBot K, IntermediateField.fixingSubgroup_bot⟩

/-- Given a field extension `L/K`, `galBasis K L` is the filter basis on `Gal(L/K)` whose sets
are `Gal(L/E)` for intermediate fields `E` with `E/K` finite dimensional. -/
@[deprecated "deprecated without replacement" (since := "2026-03-05")]
def galBasis (K L : Type*) [Field K] [Field L] [Algebra K L] : FilterBasis Gal(L/K) where
  sets := (fun g => g.carrier) '' fixedByFinite K L
  nonempty := ⟨⊤, ⊤, top_fixedByFinite, rfl⟩
  inter_sets := by
    rintro _ _ ⟨_, ⟨E1, h_E1, rfl⟩, rfl⟩ ⟨_, ⟨E2, h_E2, rfl⟩, rfl⟩
    have : FiniteDimensional K E1 := h_E1
    have : FiniteDimensional K E2 := h_E2
    refine ⟨(E1 ⊔ E2).fixingSubgroup.carrier, ⟨_, ⟨_, E1.finiteDimensional_sup E2, rfl⟩, rfl⟩, ?_⟩
    exact Set.subset_inter (E1.fixingSubgroup_le le_sup_left) (E2.fixingSubgroup_le le_sup_right)

/-- A subset of `Gal(L/K)` is a member of `galBasis K L` if and only if it is the underlying set
of `Gal(L/E)` for some finite subextension `E/K`. -/
@[deprecated "deprecated without replacement" (since := "2026-03-05")]
theorem mem_galBasis_iff (K L : Type*) [Field K] [Field L] [Algebra K L] (U : Set Gal(L/K)) :
    U ∈ galBasis K L ↔ U ∈ (fun g => g.carrier) '' fixedByFinite K L :=
  Iff.rfl

/-- For a field extension `L/K`, `galGroupBasis K L` is the group filter basis on `Gal(L/K)`
whose sets are `Gal(L/E)` for finite subextensions `E/K`. -/
@[instance_reducible, deprecated "deprecated without replacement" (since := "2026-03-05")]
def galGroupBasis (K L : Type*) [Field K] [Field L] [Algebra K L] :
    GroupFilterBasis Gal(L/K) where
  toFilterBasis := galBasis K L
  one' := fun ⟨H, _, h2⟩ => h2 ▸ H.one_mem
  mul' {U} hU :=
    ⟨U, hU, by
      rcases hU with ⟨H, _, rfl⟩
      rintro x ⟨a, haH, b, hbH, rfl⟩
      exact H.mul_mem haH hbH⟩
  inv' {U} hU :=
    ⟨U, hU, by
      rcases hU with ⟨H, _, rfl⟩
      exact fun _ => H.inv_mem'⟩
  conj' := by
    rintro σ U ⟨H, ⟨E, hE, rfl⟩, rfl⟩
    let F : IntermediateField K L := E.map σ.symm.toAlgHom
    refine ⟨F.fixingSubgroup.carrier, ⟨⟨F.fixingSubgroup, ⟨F, ?_, rfl⟩, rfl⟩, fun g hg => ?_⟩⟩
    · have : FiniteDimensional K E := hE
      exact IntermediateField.finiteDimensional_map σ.symm.toAlgHom
    change σ * g * σ⁻¹ ∈ E.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change σ (g (σ⁻¹ x)) = x
    have h_in_F : σ⁻¹ x ∈ F := ⟨x, hx, by dsimp⟩
    have h_g_fix : g (σ⁻¹ x) = σ⁻¹ x := by
      rw [Subgroup.mem_carrier, IntermediateField.mem_fixingSubgroup_iff F g] at hg
      exact hg (σ⁻¹ x) h_in_F
    rw [h_g_fix]
    change σ (σ⁻¹ x) = x
    exact AlgEquiv.apply_symm_apply σ x

end deprecated
