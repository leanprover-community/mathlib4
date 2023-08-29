/-
Copyright (c) 2022 Sebastian Monnet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Monnet
-/
import Mathlib.FieldTheory.Galois
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Tactic.ByContra

#align_import field_theory.krull_topology from "leanprover-community/mathlib"@"039a089d2a4b93c761b234f3e5f5aeb752bac60f"

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

## Notations

- In docstrings, we will write `Gal(L/E)` to denote the fixing subgroup of an intermediate field
  `E`. That is, `Gal(L/E)` is the subgroup of `L ≃ₐ[K] L` consisting of automorphisms that fix
  every element of `E`. In particular, we distinguish between `L ≃ₐ[E] L` and `Gal(L/E)`, since the
  former is defined to be a subgroup of `L ≃ₐ[K] L`, while the latter is a group in its own right.

## Implementation Notes

- `krullTopology K L` is defined as an instance for type class inference.
-/


open scoped Classical

/-- Mapping intermediate fields along algebra equivalences preserves the partial order -/
theorem IntermediateField.map_mono {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L]
    [Algebra K M] {E1 E2 : IntermediateField K L} (e : L ≃ₐ[K] M) (h12 : E1 ≤ E2) :
    E1.map e.toAlgHom ≤ E2.map e.toAlgHom :=
  Set.image_subset e h12
#align intermediate_field.map_mono IntermediateField.map_mono

/-- Mapping intermediate fields along the identity does not change them -/
theorem IntermediateField.map_id {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) : E.map (AlgHom.id K L) = E :=
  SetLike.coe_injective <| Set.image_id _
#align intermediate_field.map_id IntermediateField.map_id

/-- Mapping a finite dimensional intermediate field along an algebra equivalence gives
a finite-dimensional intermediate field. -/
instance im_finiteDimensional {K L : Type*} [Field K] [Field L] [Algebra K L]
    {E : IntermediateField K L} (σ : L ≃ₐ[K] L) [FiniteDimensional K E] :
    FiniteDimensional K (E.map σ.toAlgHom) :=
  LinearEquiv.finiteDimensional (IntermediateField.intermediateFieldMap σ E).toLinearEquiv
#align im_finite_dimensional im_finiteDimensional

/-- Given a field extension `L/K`, `finiteExts K L` is the set of
intermediate field extensions `L/E/K` such that `E/K` is finite -/
def finiteExts (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L] :
    Set (IntermediateField K L) :=
  {E | FiniteDimensional K E}
#align finite_exts finiteExts

/-- Given a field extension `L/K`, `fixedByFinite K L` is the set of
subsets `Gal(L/E)` of `L ≃ₐ[K] L`, where `E/K` is finite -/
def fixedByFinite (K L : Type*) [Field K] [Field L] [Algebra K L] : Set (Subgroup (L ≃ₐ[K] L)) :=
  IntermediateField.fixingSubgroup '' finiteExts K L
#align fixed_by_finite fixedByFinite

/-- For a field extension `L/K`, the intermediate field `K` is finite-dimensional over `K` -/
theorem IntermediateField.finiteDimensional_bot (K L : Type*) [Field K] [Field L] [Algebra K L] :
    FiniteDimensional K (⊥ : IntermediateField K L) :=
  finiteDimensional_of_rank_eq_one IntermediateField.rank_bot
#align intermediate_field.finite_dimensional_bot IntermediateField.finiteDimensional_bot

/-- This lemma says that `Gal(L/K) = L ≃ₐ[K] L` -/
theorem IntermediateField.fixingSubgroup.bot {K L : Type*} [Field K] [Field L] [Algebra K L] :
    IntermediateField.fixingSubgroup (⊥ : IntermediateField K L) = ⊤ := by
  ext f
  -- ⊢ f ∈ fixingSubgroup ⊥ ↔ f ∈ ⊤
  refine' ⟨fun _ => Subgroup.mem_top _, fun _ => _⟩
  -- ⊢ f ∈ fixingSubgroup ⊥
  rintro ⟨x, hx : x ∈ (⊥ : IntermediateField K L)⟩
  -- ⊢ f • ↑{ val := x, property := hx } = ↑{ val := x, property := hx }
  rw [IntermediateField.mem_bot] at hx
  -- ⊢ f • ↑{ val := x, property := hx✝ } = ↑{ val := x, property := hx✝ }
  rcases hx with ⟨y, rfl⟩
  -- ⊢ f • ↑{ val := ↑(algebraMap K L) y, property := hx } = ↑{ val := ↑(algebraMap …
  exact f.commutes y
  -- 🎉 no goals
#align intermediate_field.fixing_subgroup.bot IntermediateField.fixingSubgroup.bot

/-- If `L/K` is a field extension, then we have `Gal(L/K) ∈ fixedByFinite K L` -/
theorem top_fixedByFinite {K L : Type*} [Field K] [Field L] [Algebra K L] :
    ⊤ ∈ fixedByFinite K L :=
  ⟨⊥, IntermediateField.finiteDimensional_bot K L, IntermediateField.fixingSubgroup.bot⟩
#align top_fixed_by_finite top_fixedByFinite

/-- If `E1` and `E2` are finite-dimensional intermediate fields, then so is their compositum.
This rephrases a result already in mathlib so that it is compatible with our type classes -/
theorem finiteDimensional_sup {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E1 E2 : IntermediateField K L) (_ : FiniteDimensional K E1) (_ : FiniteDimensional K E2) :
    FiniteDimensional K (↥(E1 ⊔ E2)) :=
  IntermediateField.finiteDimensional_sup E1 E2
#align finite_dimensional_sup finiteDimensional_sup

/-- An element of `L ≃ₐ[K] L` is in `Gal(L/E)` if and only if it fixes every element of `E`-/
theorem IntermediateField.mem_fixingSubgroup_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (σ : L ≃ₐ[K] L) : σ ∈ E.fixingSubgroup ↔ ∀ x : L, x ∈ E → σ x = x :=
  ⟨fun hσ x hx => hσ ⟨x, hx⟩, fun h ⟨x, hx⟩ => h x hx⟩
#align intermediate_field.mem_fixing_subgroup_iff IntermediateField.mem_fixingSubgroup_iff

/-- The map `E ↦ Gal(L/E)` is inclusion-reversing -/
theorem IntermediateField.fixingSubgroup.antimono {K L : Type*} [Field K] [Field L] [Algebra K L]
    {E1 E2 : IntermediateField K L} (h12 : E1 ≤ E2) : E2.fixingSubgroup ≤ E1.fixingSubgroup := by
  rintro σ hσ ⟨x, hx⟩
  -- ⊢ σ • ↑{ val := x, property := hx } = ↑{ val := x, property := hx }
  exact hσ ⟨x, h12 hx⟩
  -- 🎉 no goals
#align intermediate_field.fixing_subgroup.antimono IntermediateField.fixingSubgroup.antimono

/-- Given a field extension `L/K`, `galBasis K L` is the filter basis on `L ≃ₐ[K] L` whose sets
are `Gal(L/E)` for intermediate fields `E` with `E/K` finite dimensional -/
def galBasis (K L : Type*) [Field K] [Field L] [Algebra K L] : FilterBasis (L ≃ₐ[K] L) where
  sets := (fun g => g.carrier) '' fixedByFinite K L
  nonempty := ⟨⊤, ⊤, top_fixedByFinite, rfl⟩
  inter_sets := by
    rintro X Y ⟨H1, ⟨E1, h_E1, rfl⟩, rfl⟩ ⟨H2, ⟨E2, h_E2, rfl⟩, rfl⟩
    -- ⊢ ∃ z, z ∈ (fun g => g.carrier) '' fixedByFinite K L ∧ z ⊆ (fun g => g.carrier …
    use (IntermediateField.fixingSubgroup (E1 ⊔ E2)).carrier
    -- ⊢ (IntermediateField.fixingSubgroup (E1 ⊔ E2)).toSubmonoid.toSubsemigroup.carr …
    refine' ⟨⟨_, ⟨_, finiteDimensional_sup E1 E2 h_E1 h_E2, rfl⟩, rfl⟩, _⟩
    -- ⊢ (IntermediateField.fixingSubgroup (E1 ⊔ E2)).toSubmonoid.toSubsemigroup.carr …
    rw [Set.subset_inter_iff]
    -- ⊢ (IntermediateField.fixingSubgroup (E1 ⊔ E2)).toSubmonoid.toSubsemigroup.carr …
    exact
      ⟨IntermediateField.fixingSubgroup.antimono le_sup_left,
        IntermediateField.fixingSubgroup.antimono le_sup_right⟩
#align gal_basis galBasis

/-- A subset of `L ≃ₐ[K] L` is a member of `galBasis K L` if and only if it is the underlying set
of `Gal(L/E)` for some finite subextension `E/K`-/
theorem mem_galBasis_iff (K L : Type*) [Field K] [Field L] [Algebra K L] (U : Set (L ≃ₐ[K] L)) :
    U ∈ galBasis K L ↔ U ∈ (fun g => g.carrier) '' fixedByFinite K L :=
  Iff.rfl
#align mem_gal_basis_iff mem_galBasis_iff

/-- For a field extension `L/K`, `galGroupBasis K L` is the group filter basis on `L ≃ₐ[K] L`
whose sets are `Gal(L/E)` for finite subextensions `E/K` -/
def galGroupBasis (K L : Type*) [Field K] [Field L] [Algebra K L] :
    GroupFilterBasis (L ≃ₐ[K] L) where
  toFilterBasis := galBasis K L
  one' := fun ⟨H, _, h2⟩ => h2 ▸ H.one_mem
  mul' {U} hU :=
    ⟨U, hU, by
      rcases hU with ⟨H, _, rfl⟩
      -- ⊢ (fun g => g.carrier) H * (fun g => g.carrier) H ⊆ (fun g => g.carrier) H
      rintro x ⟨a, b, haH, hbH, rfl⟩
      -- ⊢ (fun x x_1 => x * x_1) a b ∈ (fun g => g.carrier) H
      exact H.mul_mem haH hbH⟩
      -- 🎉 no goals
  inv' {U} hU :=
    ⟨U, hU, by
      rcases hU with ⟨H, _, rfl⟩
      -- ⊢ (fun g => g.carrier) H ⊆ (fun x => x⁻¹) ⁻¹' (fun g => g.carrier) H
      exact fun _ => H.inv_mem'⟩
      -- 🎉 no goals
  conj' := by
    rintro σ U ⟨H, ⟨E, hE, rfl⟩, rfl⟩
    -- ⊢ ∃ V, V ∈ (galBasis K L).sets ∧ V ⊆ (fun x => σ * x * σ⁻¹) ⁻¹' (fun g => g.ca …
    let F : IntermediateField K L := E.map σ.symm.toAlgHom
    -- ⊢ ∃ V, V ∈ (galBasis K L).sets ∧ V ⊆ (fun x => σ * x * σ⁻¹) ⁻¹' (fun g => g.ca …
    refine' ⟨F.fixingSubgroup.carrier, ⟨⟨F.fixingSubgroup, ⟨F, _, rfl⟩, rfl⟩, fun g hg => _⟩⟩
    -- ⊢ F ∈ finiteExts K L
    · have : FiniteDimensional K E := hE
      -- ⊢ F ∈ finiteExts K L
      apply im_finiteDimensional σ.symm
      -- 🎉 no goals
    change σ * g * σ⁻¹ ∈ E.fixingSubgroup
    -- ⊢ σ * g * σ⁻¹ ∈ IntermediateField.fixingSubgroup E
    rw [IntermediateField.mem_fixingSubgroup_iff]
    -- ⊢ ∀ (x : L), x ∈ E → ↑(σ * g * σ⁻¹) x = x
    intro x hx
    -- ⊢ ↑(σ * g * σ⁻¹) x = x
    change σ (g (σ⁻¹ x)) = x
    -- ⊢ ↑σ (↑g (↑σ⁻¹ x)) = x
    have h_in_F : σ⁻¹ x ∈ F := ⟨x, hx, by dsimp; rw [← AlgEquiv.invFun_eq_symm]; rfl⟩
    -- ⊢ ↑σ (↑g (↑σ⁻¹ x)) = x
    have h_g_fix : g (σ⁻¹ x) = σ⁻¹ x := by
      rw [Subgroup.mem_carrier, IntermediateField.mem_fixingSubgroup_iff F g] at hg
      exact hg (σ⁻¹ x) h_in_F
    rw [h_g_fix]
    -- ⊢ ↑σ (↑σ⁻¹ x) = x
    change σ (σ⁻¹ x) = x
    -- ⊢ ↑σ (↑σ⁻¹ x) = x
    exact AlgEquiv.apply_symm_apply σ x
    -- 🎉 no goals
#align gal_group_basis galGroupBasis

/-- For a field extension `L/K`, `krullTopology K L` is the topological space structure on
`L ≃ₐ[K] L` induced by the group filter basis `galGroupBasis K L` -/
instance krullTopology (K L : Type*) [Field K] [Field L] [Algebra K L] :
    TopologicalSpace (L ≃ₐ[K] L) :=
  GroupFilterBasis.topology (galGroupBasis K L)
#align krull_topology krullTopology

/-- For a field extension `L/K`, the Krull topology on `L ≃ₐ[K] L` makes it a topological group. -/
instance (K L : Type*) [Field K] [Field L] [Algebra K L] : TopologicalGroup (L ≃ₐ[K] L) :=
  GroupFilterBasis.isTopologicalGroup (galGroupBasis K L)

section KrullT2

open scoped Topology Filter

/-- Let `L/E/K` be a tower of fields with `E/K` finite. Then `Gal(L/E)` is an open subgroup of
  `L ≃ₐ[K] L`. -/
theorem IntermediateField.fixingSubgroup_isOpen {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] :
    IsOpen (E.fixingSubgroup : Set (L ≃ₐ[K] L)) := by
  have h_basis : E.fixingSubgroup.carrier ∈ galGroupBasis K L :=
    ⟨E.fixingSubgroup, ⟨E, ‹_›, rfl⟩, rfl⟩
  have h_nhd := GroupFilterBasis.mem_nhds_one (galGroupBasis K L) h_basis
  -- ⊢ IsOpen ↑(fixingSubgroup E)
  exact Subgroup.isOpen_of_mem_nhds _ h_nhd
  -- 🎉 no goals
#align intermediate_field.fixing_subgroup_is_open IntermediateField.fixingSubgroup_isOpen

/-- Given a tower of fields `L/E/K`, with `E/K` finite, the subgroup `Gal(L/E) ≤ L ≃ₐ[K] L` is
  closed. -/
theorem IntermediateField.fixingSubgroup_isClosed {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] :
    IsClosed (E.fixingSubgroup : Set (L ≃ₐ[K] L)) :=
  OpenSubgroup.isClosed ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩
#align intermediate_field.fixing_subgroup_is_closed IntermediateField.fixingSubgroup_isClosed

/-- If `L/K` is an algebraic extension, then the Krull topology on `L ≃ₐ[K] L` is Hausdorff. -/
theorem krullTopology_t2 {K L : Type*} [Field K] [Field L] [Algebra K L]
    (h_int : Algebra.IsIntegral K L) : T2Space (L ≃ₐ[K] L) :=
  { t2 := fun f g hfg => by
      let φ := f⁻¹ * g
      -- ⊢ ∃ u v, IsOpen u ∧ IsOpen v ∧ f ∈ u ∧ g ∈ v ∧ Disjoint u v
      cases' FunLike.exists_ne hfg with x hx
      -- ⊢ ∃ u v, IsOpen u ∧ IsOpen v ∧ f ∈ u ∧ g ∈ v ∧ Disjoint u v
      have hφx : φ x ≠ x := by
        apply ne_of_apply_ne f
        change f (f.symm (g x)) ≠ f x
        rw [AlgEquiv.apply_symm_apply f (g x), ne_comm]
        exact hx
      let E : IntermediateField K L := IntermediateField.adjoin K {x}
      -- ⊢ ∃ u v, IsOpen u ∧ IsOpen v ∧ f ∈ u ∧ g ∈ v ∧ Disjoint u v
      let h_findim : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional (h_int x)
      -- ⊢ ∃ u v, IsOpen u ∧ IsOpen v ∧ f ∈ u ∧ g ∈ v ∧ Disjoint u v
      let H := E.fixingSubgroup
      -- ⊢ ∃ u v, IsOpen u ∧ IsOpen v ∧ f ∈ u ∧ g ∈ v ∧ Disjoint u v
      have h_basis : (H : Set (L ≃ₐ[K] L)) ∈ galGroupBasis K L := ⟨H, ⟨E, ⟨h_findim, rfl⟩⟩, rfl⟩
      -- ⊢ ∃ u v, IsOpen u ∧ IsOpen v ∧ f ∈ u ∧ g ∈ v ∧ Disjoint u v
      have h_nhd := GroupFilterBasis.mem_nhds_one (galGroupBasis K L) h_basis
      -- ⊢ ∃ u v, IsOpen u ∧ IsOpen v ∧ f ∈ u ∧ g ∈ v ∧ Disjoint u v
      rw [mem_nhds_iff] at h_nhd
      -- ⊢ ∃ u v, IsOpen u ∧ IsOpen v ∧ f ∈ u ∧ g ∈ v ∧ Disjoint u v
      rcases h_nhd with ⟨W, hWH, hW_open, hW_1⟩
      -- ⊢ ∃ u v, IsOpen u ∧ IsOpen v ∧ f ∈ u ∧ g ∈ v ∧ Disjoint u v
      refine' ⟨leftCoset f W, leftCoset g W,
        ⟨hW_open.leftCoset f, hW_open.leftCoset g, ⟨1, hW_1, mul_one _⟩, ⟨1, hW_1, mul_one _⟩, _⟩⟩
      rw [Set.disjoint_left]
      -- ⊢ ∀ ⦃a : L ≃ₐ[K] L⦄, a ∈ leftCoset f W → ¬a ∈ leftCoset g W
      rintro σ ⟨w1, hw1, h⟩ ⟨w2, hw2, rfl⟩
      -- ⊢ False
      rw [eq_inv_mul_iff_mul_eq.symm, ← mul_assoc, mul_inv_eq_iff_eq_mul.symm] at h
      -- ⊢ False
      have h_in_H : w1 * w2⁻¹ ∈ H := H.mul_mem (hWH hw1) (H.inv_mem (hWH hw2))
      -- ⊢ False
      rw [h] at h_in_H
      -- ⊢ False
      change φ ∈ E.fixingSubgroup at h_in_H
      -- ⊢ False
      rw [IntermediateField.mem_fixingSubgroup_iff] at h_in_H
      -- ⊢ False
      specialize h_in_H x
      -- ⊢ False
      have hxE : x ∈ E := by
        apply IntermediateField.subset_adjoin
        apply Set.mem_singleton
      exact hφx (h_in_H hxE) }
      -- 🎉 no goals
#align krull_topology_t2 krullTopology_t2

end KrullT2

section TotallyDisconnected

/-- If `L/K` is an algebraic field extension, then the Krull topology on `L ≃ₐ[K] L` is
  totally disconnected. -/
theorem krullTopology_totallyDisconnected {K L : Type*} [Field K] [Field L] [Algebra K L]
    (h_int : Algebra.IsIntegral K L) : IsTotallyDisconnected (Set.univ : Set (L ≃ₐ[K] L)) := by
  apply isTotallyDisconnected_of_clopen_set
  -- ⊢ Pairwise fun x y => ∃ U, IsClopen U ∧ x ∈ U ∧ ¬y ∈ U
  intro σ τ h_diff
  -- ⊢ ∃ U, IsClopen U ∧ σ ∈ U ∧ ¬τ ∈ U
  have hστ : σ⁻¹ * τ ≠ 1 := by rwa [Ne.def, inv_mul_eq_one]
  -- ⊢ ∃ U, IsClopen U ∧ σ ∈ U ∧ ¬τ ∈ U
  rcases FunLike.exists_ne hστ with ⟨x, hx : (σ⁻¹ * τ) x ≠ x⟩
  -- ⊢ ∃ U, IsClopen U ∧ σ ∈ U ∧ ¬τ ∈ U
  let E := IntermediateField.adjoin K ({x} : Set L)
  -- ⊢ ∃ U, IsClopen U ∧ σ ∈ U ∧ ¬τ ∈ U
  haveI := IntermediateField.adjoin.finiteDimensional (h_int x)
  -- ⊢ ∃ U, IsClopen U ∧ σ ∈ U ∧ ¬τ ∈ U
  refine' ⟨leftCoset σ E.fixingSubgroup,
    ⟨E.fixingSubgroup_isOpen.leftCoset σ, E.fixingSubgroup_isClosed.leftCoset σ⟩,
    ⟨1, E.fixingSubgroup.one_mem', mul_one σ⟩, _⟩
  simp only [mem_leftCoset_iff, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff,
    not_forall]
  exact ⟨x, IntermediateField.mem_adjoin_simple_self K x, hx⟩
  -- 🎉 no goals
#align krull_topology_totally_disconnected krullTopology_totallyDisconnected

end TotallyDisconnected
