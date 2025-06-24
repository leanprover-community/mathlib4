/-
Copyright (c) 2022 Sebastian Monnet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Monnet
-/
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Krull topology

We define the Krull topology on `L ≃ₐ[K] L` for an arbitrary field extension `L/K`. In order to do
this, we first define a `GroupFilterBasis` on `L ≃ₐ[K] L`, whose sets are `E.fixingSubgroup` for
all intermediate fields `E` with `E/K` finite dimensional.

## Main Definitions

- `finiteExts K L`. Given a field extension `L/K`, this is the set of intermediate fields that are
  finite-dimensional over `K`.

- `fixedByFinite K L`. Given a field extension `L/K`, `fixedByFinite K L` is the set of
  subsets `Gal(L/E)` of `Gal(L/K)`, where `E/K` is finite

- `galBasis K L`. Given a field extension `L/K`, this is the filter basis on `L ≃ₐ[K] L` whose
  sets are `Gal(L/E)` for intermediate fields `E` with `E/K` finite.

- `galGroupBasis K L`. This is the same as `galBasis K L`, but with the added structure
  that it is a group filter basis on `L ≃ₐ[K] L`, rather than just a filter basis.

- `krullTopology K L`. Given a field extension `L/K`, this is the topology on `L ≃ₐ[K] L`, induced
  by the group filter basis `galGroupBasis K L`.

## Main Results

- `krullTopology_t2 K L`. For an integral field extension `L/K`, the topology `krullTopology K L`
  is Hausdorff.

- `krullTopology_totallyDisconnected K L`. For an integral field extension `L/K`, the topology
  `krullTopology K L` is totally disconnected.

- `IntermediateField.finrank_eq_fixingSubgroup_index`: given a Galois extension `K/k` and an
  intermediate field `L`, the `[L : k]` as a natural number is equal to the index of the
  fixing subgroup of `L`.

## Notations

- In docstrings, we will write `Gal(L/E)` to denote the fixing subgroup of an intermediate field
  `E`. That is, `Gal(L/E)` is the subgroup of `L ≃ₐ[K] L` consisting of automorphisms that fix
  every element of `E`. In particular, we distinguish between `L ≃ₐ[E] L` and `Gal(L/E)`, since the
  former is defined to be a subgroup of `L ≃ₐ[K] L`, while the latter is a group in its own right.

## Implementation Notes

- `krullTopology K L` is defined as an instance for type class inference.
-/

open scoped Pointwise

/-- Given a field extension `L/K`, `finiteExts K L` is the set of
intermediate field extensions `L/E/K` such that `E/K` is finite. -/
def finiteExts (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L] :
    Set (IntermediateField K L) :=
  {E | FiniteDimensional K E}

/-- Given a field extension `L/K`, `fixedByFinite K L` is the set of
subsets `Gal(L/E)` of `L ≃ₐ[K] L`, where `E/K` is finite. -/
def fixedByFinite (K L : Type*) [Field K] [Field L] [Algebra K L] : Set (Subgroup (L ≃ₐ[K] L)) :=
  IntermediateField.fixingSubgroup '' finiteExts K L

@[deprecated (since := "2025-03-16")]
alias IntermediateField.finiteDimensional_bot := IntermediateField.instFiniteSubtypeMemBot

@[deprecated (since := "2025-03-12")]
alias IntermediateField.fixingSubgroup.bot := IntermediateField.fixingSubgroup_bot

/-- If `L/K` is a field extension, then we have `Gal(L/K) ∈ fixedByFinite K L`. -/
theorem top_fixedByFinite {K L : Type*} [Field K] [Field L] [Algebra K L] :
    ⊤ ∈ fixedByFinite K L :=
  ⟨⊥, IntermediateField.instFiniteSubtypeMemBot K, IntermediateField.fixingSubgroup_bot⟩

@[deprecated (since := "2025-03-16")]
alias finiteDimensional_sup := IntermediateField.finiteDimensional_sup

/-- Given a field extension `L/K`, `galBasis K L` is the filter basis on `L ≃ₐ[K] L` whose sets
are `Gal(L/E)` for intermediate fields `E` with `E/K` finite dimensional. -/
def galBasis (K L : Type*) [Field K] [Field L] [Algebra K L] : FilterBasis (L ≃ₐ[K] L) where
  sets := (fun g => g.carrier) '' fixedByFinite K L
  nonempty := ⟨⊤, ⊤, top_fixedByFinite, rfl⟩
  inter_sets := by
    rintro _ _ ⟨_, ⟨E1, h_E1, rfl⟩, rfl⟩ ⟨_, ⟨E2, h_E2, rfl⟩, rfl⟩
    have : FiniteDimensional K E1 := h_E1
    have : FiniteDimensional K E2 := h_E2
    refine ⟨(E1 ⊔ E2).fixingSubgroup.carrier, ⟨_, ⟨_, E1.finiteDimensional_sup E2, rfl⟩, rfl⟩, ?_⟩
    exact Set.subset_inter (E1.fixingSubgroup_le le_sup_left) (E2.fixingSubgroup_le le_sup_right)

/-- A subset of `L ≃ₐ[K] L` is a member of `galBasis K L` if and only if it is the underlying set
of `Gal(L/E)` for some finite subextension `E/K`. -/
theorem mem_galBasis_iff (K L : Type*) [Field K] [Field L] [Algebra K L] (U : Set (L ≃ₐ[K] L)) :
    U ∈ galBasis K L ↔ U ∈ (fun g => g.carrier) '' fixedByFinite K L :=
  Iff.rfl

/-- For a field extension `L/K`, `galGroupBasis K L` is the group filter basis on `L ≃ₐ[K] L`
whose sets are `Gal(L/E)` for finite subextensions `E/K`. -/
def galGroupBasis (K L : Type*) [Field K] [Field L] [Algebra K L] :
    GroupFilterBasis (L ≃ₐ[K] L) where
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
    have h_in_F : σ⁻¹ x ∈ F := ⟨x, hx, by dsimp; rw [← AlgEquiv.invFun_eq_symm]; rfl⟩
    have h_g_fix : g (σ⁻¹ x) = σ⁻¹ x := by
      rw [Subgroup.mem_carrier, IntermediateField.mem_fixingSubgroup_iff F g] at hg
      exact hg (σ⁻¹ x) h_in_F
    rw [h_g_fix]
    change σ (σ⁻¹ x) = x
    exact AlgEquiv.apply_symm_apply σ x

/-- For a field extension `L/K`, `krullTopology K L` is the topological space structure on
`L ≃ₐ[K] L` induced by the group filter basis `galGroupBasis K L`. -/
instance krullTopology (K L : Type*) [Field K] [Field L] [Algebra K L] :
    TopologicalSpace (L ≃ₐ[K] L) :=
  GroupFilterBasis.topology (galGroupBasis K L)

/-- For a field extension `L/K`, the Krull topology on `L ≃ₐ[K] L` makes it a topological group. -/
@[stacks 0BMJ "We define Krull topology directly without proving the universal property"]
instance (K L : Type*) [Field K] [Field L] [Algebra K L] : IsTopologicalGroup (L ≃ₐ[K] L) :=
  GroupFilterBasis.isTopologicalGroup (galGroupBasis K L)

open scoped Topology in
lemma krullTopology_mem_nhds_one_iff (K L : Type*) [Field K] [Field L] [Algebra K L]
    (s : Set (L ≃ₐ[K] L)) : s ∈ 𝓝 1 ↔ ∃ E : IntermediateField K L,
    FiniteDimensional K E ∧ (E.fixingSubgroup : Set (L ≃ₐ[K] L)) ⊆ s := by
  rw [GroupFilterBasis.nhds_one_eq]
  constructor
  · rintro ⟨-, ⟨-, ⟨E, fin, rfl⟩, rfl⟩, hE⟩
    exact ⟨E, fin, hE⟩
  · rintro ⟨E, fin, hE⟩
    exact ⟨E.fixingSubgroup, ⟨E.fixingSubgroup, ⟨E, fin, rfl⟩, rfl⟩, hE⟩

open scoped Topology in
lemma krullTopology_mem_nhds_one_iff_of_normal (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Normal K L] (s : Set (L ≃ₐ[K] L)) : s ∈ 𝓝 1 ↔ ∃ E : IntermediateField K L,
    FiniteDimensional K E ∧ Normal K E ∧ (E.fixingSubgroup : Set (L ≃ₐ[K] L)) ⊆ s := by
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨fun ⟨E, _, hE⟩ ↦ ?_, fun ⟨E, hE⟩ ↦ ⟨E, hE.1, hE.2.2⟩⟩
  use (IntermediateField.normalClosure K E L)
  simp only [normalClosure.is_finiteDimensional K E L, normalClosure.normal K E L, true_and]
  exact le_trans (E.fixingSubgroup_antitone E.le_normalClosure) hE

section KrullT2

open scoped Topology Filter

/-- Let `L/E/K` be a tower of fields with `E/K` finite. Then `Gal(L/E)` is an open subgroup of
  `L ≃ₐ[K] L`. -/
theorem IntermediateField.fixingSubgroup_isOpen {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] :
    IsOpen (E.fixingSubgroup : Set (L ≃ₐ[K] L)) := by
  have h_basis : E.fixingSubgroup.carrier ∈ galGroupBasis K L :=
    ⟨E.fixingSubgroup, ⟨E, ‹_›, rfl⟩, rfl⟩
  have h_nhds := GroupFilterBasis.mem_nhds_one (galGroupBasis K L) h_basis
  exact Subgroup.isOpen_of_mem_nhds _ h_nhds

/-- Given a tower of fields `L/E/K`, with `E/K` finite, the subgroup `Gal(L/E) ≤ L ≃ₐ[K] L` is
  closed. -/
theorem IntermediateField.fixingSubgroup_isClosed {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] :
    IsClosed (E.fixingSubgroup : Set (L ≃ₐ[K] L)) :=
  OpenSubgroup.isClosed ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩

/-- If `L/K` is an algebraic extension, then the Krull topology on `L ≃ₐ[K] L` is Hausdorff. -/
theorem krullTopology_t2 {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] : T2Space (L ≃ₐ[K] L) :=
  { t2 := fun f g hfg => by
      let φ := f⁻¹ * g
      obtain ⟨x, hx⟩ := DFunLike.exists_ne hfg
      have hφx : φ x ≠ x := by
        apply ne_of_apply_ne f
        change f (f.symm (g x)) ≠ f x
        rw [AlgEquiv.apply_symm_apply f (g x), ne_comm]
        exact hx
      let E : IntermediateField K L := IntermediateField.adjoin K {x}
      let h_findim : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral x)
      let H := E.fixingSubgroup
      have h_basis : (H : Set (L ≃ₐ[K] L)) ∈ galGroupBasis K L := ⟨H, ⟨E, ⟨h_findim, rfl⟩⟩, rfl⟩
      have h_nhds := GroupFilterBasis.mem_nhds_one (galGroupBasis K L) h_basis
      rw [mem_nhds_iff] at h_nhds
      rcases h_nhds with ⟨W, hWH, hW_open, hW_1⟩
      refine ⟨f • W, g • W,
        ⟨hW_open.leftCoset f, hW_open.leftCoset g, ⟨1, hW_1, mul_one _⟩, ⟨1, hW_1, mul_one _⟩, ?_⟩⟩
      rw [Set.disjoint_left]
      rintro σ ⟨w1, hw1, h⟩ ⟨w2, hw2, rfl⟩
      dsimp at h
      rw [eq_inv_mul_iff_mul_eq.symm, ← mul_assoc, mul_inv_eq_iff_eq_mul.symm] at h
      have h_in_H : w1 * w2⁻¹ ∈ H := H.mul_mem (hWH hw1) (H.inv_mem (hWH hw2))
      rw [h] at h_in_H
      change φ ∈ E.fixingSubgroup at h_in_H
      rw [IntermediateField.mem_fixingSubgroup_iff] at h_in_H
      specialize h_in_H x
      have hxE : x ∈ E := by
        apply IntermediateField.subset_adjoin
        apply Set.mem_singleton
      exact hφx (h_in_H hxE) }

end KrullT2

section TotallySeparated

instance {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L] :
    TotallySeparatedSpace (L ≃ₐ[K] L) := by
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro σ τ h_diff
  have hστ : σ⁻¹ * τ ≠ 1 := by rwa [Ne, inv_mul_eq_one]
  rcases DFunLike.exists_ne hστ with ⟨x, hx : (σ⁻¹ * τ) x ≠ x⟩
  let E := IntermediateField.adjoin K ({x} : Set L)
  haveI := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral (R := K) x)
  refine ⟨σ • E.fixingSubgroup,
    ⟨E.fixingSubgroup_isClosed.leftCoset σ, E.fixingSubgroup_isOpen.leftCoset σ⟩,
    ⟨1, E.fixingSubgroup.one_mem', mul_one σ⟩, ?_⟩
  simp only [Set.mem_compl_iff, mem_leftCoset_iff, SetLike.mem_coe,
    IntermediateField.mem_fixingSubgroup_iff, not_forall]
  exact ⟨x, IntermediateField.mem_adjoin_simple_self K x, hx⟩

/-- If `L/K` is an algebraic field extension, then the Krull topology on `L ≃ₐ[K] L` is
  totally disconnected. -/
theorem krullTopology_isTotallySeparated {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] : IsTotallySeparated (Set.univ : Set (L ≃ₐ[K] L)) :=
  (totallySeparatedSpace_iff _).mp inferInstance

@[deprecated (since := "2025-04-03")]
alias krullTopology_totallyDisconnected := krullTopology_isTotallySeparated

end TotallySeparated

instance krullTopology_discreteTopology_of_finiteDimensional (K L : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] : DiscreteTopology (L ≃ₐ[K] L) := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  change IsOpen ((⊥ : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L))
  rw [← IntermediateField.fixingSubgroup_top]
  exact IntermediateField.fixingSubgroup_isOpen ⊤

namespace IntermediateField

variable {k E : Type*} (K : Type*) [Field k] [Field E] [Field K]
  [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K] (L : IntermediateField k E)

/-- If `K / E / k` is a field extension tower with `E / k` normal,
`L` is an intermediate field of `E / k`, then the fixing subgroup of `L` viewed as an
intermediate field of `K / k` is equal to the preimage of the fixing subgroup of `L` viewed as an
intermediate field of `E / k` under the natural map `Aut(K / k) → Aut(E / k)`
(`AlgEquiv.restrictNormalHom`). -/
theorem map_fixingSubgroup [Normal k E] :
    (L.map (IsScalarTower.toAlgHom k E K)).fixingSubgroup =
      L.fixingSubgroup.comap (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E) := by
  ext f
  simp only [Subgroup.mem_comap, mem_fixingSubgroup_iff]
  constructor
  · rintro h x hx
    change f.restrictNormal E x = x
    apply_fun _ using (algebraMap E K).injective
    rw [AlgEquiv.restrictNormal_commutes]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    replace h := congr(algebraMap E K $(show f.restrictNormal E x = x from h x hx))
    rwa [AlgEquiv.restrictNormal_commutes] at h

/-- If `K / E / k` is a field extension tower with `E / k` and `K / k` normal,
`L` is an intermediate field of `E / k`, then the index of the fixing subgroup of `L` viewed as an
intermediate field of `K / k` is equal to the index of the fixing subgroup of `L` viewed as an
intermediate field of `E / k`. -/
theorem map_fixingSubgroup_index [Normal k E] [Normal k K] :
    (L.map (IsScalarTower.toAlgHom k E K)).fixingSubgroup.index = L.fixingSubgroup.index := by
  rw [L.map_fixingSubgroup K, L.fixingSubgroup.index_comap_of_surjective
    (AlgEquiv.restrictNormalHom_surjective _)]

variable {K} in
/-- If `K / k` is a Galois extension, `L` is an intermediate field of `K / k`, then `[L : k]`
as a natural number is equal to the index of the fixing subgroup of `L`. -/
theorem finrank_eq_fixingSubgroup_index (L : IntermediateField k K) [IsGalois k K] :
    Module.finrank k L = L.fixingSubgroup.index := by
  wlog hnfd : FiniteDimensional k L generalizing L
  · rw [Module.finrank_of_infinite_dimensional hnfd]
    by_contra! h
    replace h : L.fixingSubgroup.FiniteIndex := ⟨h.symm⟩
    obtain ⟨L', hfd, hL'⟩ :=
      exists_lt_finrank_of_infinite_dimensional hnfd L.fixingSubgroup.index
    let i := (liftAlgEquiv L').toLinearEquiv
    replace hfd := i.finiteDimensional
    rw [i.finrank_eq, this _ hfd] at hL'
    exact (Subgroup.index_antitone <| fixingSubgroup_le <|
      IntermediateField.lift_le L').not_gt hL'
  let E := normalClosure k L K
  have hle : L ≤ E := by simpa only [fieldRange_val] using L.val.fieldRange_le_normalClosure
  let L' := restrict hle
  have h := Module.finrank_mul_finrank k ↥L' ↥E
  classical
  rw [← IsGalois.card_fixingSubgroup_eq_finrank L', ← IsGalois.card_aut_eq_finrank k E] at h
  nth_rw 2 [Fintype.card_eq_nat_card] at h
  rw [← L'.fixingSubgroup.index_mul_card, Nat.card_eq_fintype_card,
    Nat.mul_left_inj Fintype.card_ne_zero] at h
  rw [(restrict_algEquiv hle).toLinearEquiv.finrank_eq, h, ← L'.map_fixingSubgroup_index K]
  congr 2
  exact lift_restrict hle

end IntermediateField
