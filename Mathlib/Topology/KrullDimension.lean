/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li, Alessandro D'Angelo
-/
module

public import Mathlib.Order.KrullDimension
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sober
public import Mathlib.Topology.NoetherianSpace

/-!
# The Krull dimension of a topological space

The Krull dimension of a topological space is the order-theoretic Krull dimension applied to the
collection of all its subsets that are closed and irreducible. Unfolding this definition, it is
the length of longest series of closed irreducible subsets ordered by inclusion.

## Main results

- `topologicalKrullDim_subspace_le`: For any subspace Y ⊆ X, we have dim(Y) ≤ dim(X)

## Implementation notes

The proofs use order-preserving maps between posets of irreducible closed sets to establish
dimension inequalities.
-/

@[expose] public section

open Set Order TopologicalSpace Topology TopologicalSpace.IrreducibleCloseds

/--
The Krull dimension of a topological space is the supremum of lengths of chains of
closed irreducible sets.
-/
noncomputable def topologicalKrullDim (T : Type*) [TopologicalSpace T] : WithBot ℕ∞ :=
  krullDim (IrreducibleCloseds T)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-!
### Main dimension theorems -/

/-- If `f : Y → X` is inducing, then `dim(Y) ≤ dim(X)`. -/
theorem Topology.IsInducing.topologicalKrullDim_le {f : Y → X} (hf : IsInducing f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X :=
  krullDim_le_of_strictMono _ (map_strictMono_of_isInducing hf)

/-- The topological Krull dimension is invariant under homeomorphisms -/
theorem IsHomeomorph.topologicalKrullDim_eq (f : X → Y) (h : IsHomeomorph f) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  have fwd : topologicalKrullDim X ≤ topologicalKrullDim Y :=
    h.isInducing.topologicalKrullDim_le
  have bwd : topologicalKrullDim Y ≤ topologicalKrullDim X :=
    (h.homeomorph f).symm.isInducing.topologicalKrullDim_le
  le_antisymm fwd bwd

/-- The topological Krull dimension of any subspace is at most the dimension of the
ambient space. -/
theorem topologicalKrullDim_subspace_le (X : Type*) [TopologicalSpace X] (Y : Set X) :
    topologicalKrullDim Y ≤ topologicalKrullDim X :=
  IsInducing.subtypeVal.topologicalKrullDim_le

theorem topologicalKrullDim_zero_of_discreteTopology
    (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    topologicalKrullDim X ≤ 0 := by
  refine krullDim_nonpos_iff_forall_isMax.mpr fun Z Y h ↦ (h.antisymm' fun x hx ↦ ?_).le
  obtain ⟨z, hz⟩ := Z.2.nonempty
  rwa [DiscreteTopology.isDiscrete.subsingleton_of_isPreirreducible Y.2.isPreirreducible hx (h hz)]

lemma Topology.IsOpenEmbedding.coheight_map {f : X → Y} (hf : IsOpenEmbedding f)
    (Z : TopologicalSpace.IrreducibleCloseds X) :
    Order.coheight (map f hf.continuous Z) = Order.coheight Z := by
  rw [← coheight_orderIso (orderIsoOfIsOpenEmbedding f hf) Z]
  refine .symm (coheight_eq_of_strictMono Subtype.val (Subtype.strictMono_coe _) ?_ _)
  intro a b hlt
  exact ⟨⟨b, a.2.mono (Set.preimage_mono hlt.le)⟩, hlt, rfl⟩

attribute [local instance] specializationOrder in
lemma Topology.IsOpenEmbedding.coheight_eq [QuasiSober Y] [T0Space Y] [QuasiSober X] [T0Space X]
    {x : X} (f : X → Y) (hf : IsOpenEmbedding f) : coheight (f x) = coheight x := by
  rw [← coheight_orderIso (irreducibleSetEquivPoints (α := Y)).symm (f x),
    ← coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm x,
    ← Topology.IsOpenEmbedding.coheight_map hf]
  congr
  ext : 1
  simp [closure_image_closure hf.continuous]

section Coheight

attribute [local instance] specializationOrder in
/--
In a sober space `X`, the set of points of coheight `0` in the specialization order is order
isomorphic to the set of irreducible components of `X`.
-/
noncomputable
def coheightZeroSetOrderIsoIrreducibleComponents [QuasiSober X] [T0Space X] :
    {x : X | coheight x = 0} ≃o irreducibleComponents X := by
  have univIso : Subtype (fun _ : X ↦ (⊤ : Prop)) ≃o X :=
    { Equiv.subtypeUnivEquiv fun _ ↦ trivial with map_rel_iff' := Iff.rfl }
  have : {x : X | coheight x = 0} = {x : X | Maximal ⊤ x} := by simp [maximal_iff_isMax]
  rw [irreducibleComponents_eq_maximals_closed, this]
  exact OrderIso.mapSetOfPredMaximal <| OrderIso.trans
    (OrderIso.trans univIso (irreducibleSetEquivPoints (α := X)).symm) <|
    TopologicalSpace.IrreducibleCloseds.orderIsoSubtype' X

attribute [local instance] specializationPreorder in
/--
In a quasi-sober irreducible space `X`, a point of a non-dense subset `p` which has coheight `1`
in `X` has coheight `0` in `p`.
-/
lemma QuasiSober.coheight_eq_zero_subset_of_coheight_eq_one [QuasiSober X] [IrreducibleSpace X]
    {p : Set X} (hp : closure p ≠ univ) :
    {x ∈ p | coheight x = 1} ⊆ Subtype.val '' {x : p | coheight x = 0} := by
  have hsm : StrictMono (WithTop.recTopCoe (genericPoint X) (Subtype.val : p → X)) :=
    WithTop.strictMono_iff.mpr
      ⟨Subtype.strictMono_coe p, QuasiSober.val_lt_genericPoint_of_closure_ne_univ hp⟩
  rintro x ⟨hx, kx⟩
  exact ⟨⟨x, hx⟩, coheight_zero_of_coheight_one_of_strictMono _ hsm ⟨x, hx⟩
    (by simpa using kx), rfl⟩

attribute [local instance] specializationPreorder in
/--
In a quasi-sober, irreducible, `T0` space `X`, a Noetherian quasi-sober subspace `p` whose closure
is not all of `X` contains only finitely many points of coheight `1` (in the specialization order
of `X`).
-/
lemma TopologicalSpace.NoetherianSpace.finite_coheight_one_of_closure_ne_univ
    [QuasiSober X] [IrreducibleSpace X] {p : Set X} [T0Space p]
    [NoetherianSpace p] [QuasiSober p] (hp : closure p ≠ univ) :
    {x ∈ p | coheight x = 1}.Finite := by
  have h : {x : p | coheight x = 0}.Finite := by
    rw [← specializationPreorder_subtype]
    exact finite_coe_iff.mp <| (Equiv.finite_iff
      (coheightZeroSetOrderIsoIrreducibleComponents (X := p)).toEquiv).mpr
      NoetherianSpace.finite_irreducibleComponents
  exact (h.image Subtype.val).subset
    (QuasiSober.coheight_eq_zero_subset_of_coheight_eq_one hp)

end Coheight
