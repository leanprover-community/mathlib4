/-
Copyright (c) 2024 Anatole Dedeker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedeker, Etienne Marion, Florestan Martin-Baillon, Vincent Guirardel
-/
import Mathlib.Topology.ProperMap
import Mathlib.GroupTheory.Subgroup.Actions
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Defs.Sequences
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Proper group action

In this file we define proper action of a group on a topological space, and we prove that in this
case the quotient space is T2. We also give equivalent definitions of proper action using
ultrafilters and show the transfer of proper action to a closed subgroup.
We give sufficent conditions on the topological space such that the action is properly discontinuous
(see `ProperlyDiscontinuousSMul`) if and only if it is continuous in
the first variable (see `ContinuousConstSMul`) and proper in the sense defined here.

## Main definitions

* `ProperSMul` : a group `G` acts properly on a topological space `X`
  if the map `(g, x) ↦ (g • x, x)` is proper, in the sense defined in `IsProperMap`.

## Main statements

* `t2Space_of_ProperSMul`: If a group `G` acts properly on a topological space `X`,
  then the quotient space is Hausdorff (T2).
* `t2Space_of_properSMul_of_t2Group`: If a T2 group acts properly on a topological space,
  then this topological space is T2.
* `ProperlyDiscontinuousSMul_iff_ProperSMul`: If a discrete group acts on a T2 space `X` such that
  `X × X` is compactly generated, then the action is properly discontinuous if and only if it is
  continuous in the second variable and proper. This in particular true if `X` is locally compact
  or first-countable.

## Implementation notes

Concerning `ProperlyDiscontinuousSMul_iff_ProperSMul`, this result should be the only one needed
to link properly discontinuous and proper actions, however the notion of compactly generated space
is not yet in Mathlib so it is used as an intermediate result to prove
`WeaklyLocallyCompactSpace.isProperMap_iff_isCompact_preimage` and
`SequentialSpace.isProperMap_iff_isCompact_preimage`.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]

## Tags

Hausdorff, group action, proper action
-/

open Filter Topology Set Prod

/-- Proper group action in the sense of Bourbaki:
the map `G × X → X × X` is a proper map (see `isProperMap`). -/
@[mk_iff]
class ProperVAdd (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [AddGroup G]
    [AddAction G X] : Prop where
  /-- Proper group action in the sense of Bourbaki:
  the map `G × X → X × X` is a proper map (see `isProperMap`). -/
  isProperMap_vadd_pair' : IsProperMap (fun gx ↦ ⟨gx.1 +ᵥ gx.2, gx.2⟩ : G × X → X × X)

/-- Proper group action in the sense of Bourbaki:
the map `G × X → X × X` is a proper map (see `isProperMap`). -/
@[to_additive existing, mk_iff]
class ProperSMul (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [Group G]
    [MulAction G X] : Prop where
  /-- Proper group action in the sense of Bourbaki:
  the map `G × X → X × X` is a proper map (see `isProperMap`). -/
  isProperMap_smul_pair' : IsProperMap (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X)

attribute [to_additive existing] properSMul_iff

/-- By definition, if G acts properly on X then
the map `G × X → X × X` is a proper map. -/
@[to_additive "By definition, if G acts properly on X then
the map `G × X → X × X` is a proper map."]
lemma isProperMap_smul_pair (G X : Type*) [Group G] [MulAction G X]
    [TopologicalSpace G] [TopologicalSpace X] [ProperSMul G X] :
    IsProperMap (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) :=
  ProperSMul.isProperMap_smul_pair'

variable {G X Y Z : Type*} [Group G] [MulAction G X] [MulAction G Y]
variable [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace Z]

/-- If a group acts properly then in particularl it acts continuously. -/
@[to_additive "If a group acts properly then in particularl it acts continuously."]
instance continuousSmul_of_properSMul [ProperSMul G X] : ContinuousSMul G X where
  continuous_smul := (isProperMap_smul_pair G X).continuous.fst

/-- A group `G` acts properly on a topological space `X` if and only if for all ultrafilters
`𝒰` on `X × G`, if `𝒰` converges to `(x₁, x₂)` along the map `(g, x) ↦ (g • x, x)`,
then there exists `g : G` such that `g • x₂ = x₁` and `𝒰.fst` converges to `g`. -/
@[to_additive "A group acts `G` properly on a topological space `X` if and only if
for all ultrafilters `𝒰` on `X`, if `𝒰` converges to `(x₁, x₂)`
along the map `(g, x) ↦ (g • x, x)`, then there exists `g : G` such that `g • x₂ = x₁`
and `𝒰.fst` converges to `g`."]
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto : ProperSMul G X ↔ ContinuousSMul G X ∧
    (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
    Tendsto (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) 𝒰 (𝓝 (x₁, x₂)) →
    ∃ g : G, g • x₂ = x₁ ∧ Tendsto Prod.fst (𝒰 : Filter (G × X)) (𝓝 g)) := by
  constructor
  · refine fun h ↦ ⟨inferInstance, fun 𝒰 x₁ x₂ h' ↦ ?_⟩
    rw [properSMul_iff, isProperMap_iff_ultrafilter] at h
    rcases h.2 h' with ⟨gx, hgx1, hgx2⟩
    refine ⟨gx.1, ?_, (continuous_fst.tendsto gx).mono_left hgx2⟩
    simp only [Prod.mk.injEq] at hgx1
    rw [← hgx1.2, hgx1.1]
  · rintro ⟨cont, h⟩
    rw [properSMul_iff, isProperMap_iff_ultrafilter]
    refine ⟨by fun_prop, fun 𝒰 (x₁, x₂) hxx ↦ ?_⟩
    rcases h 𝒰 x₁ x₂ hxx with ⟨g, hg1, hg2⟩
    refine ⟨(g, x₂), by rw [hg1], ?_⟩
    rw [nhds_prod_eq, 𝒰.le_prod]
    exact ⟨hg2, (continuous_snd.tendsto _).comp hxx⟩

/-- A group `G` acts properly on a T2 topological space `X` if and only if for all ultrafilters
`𝒰` on `X × G`, if `𝒰` converges to `(x₁, x₂)` along the map `(g, x) ↦ (g • x, x)`,
then there exists `g : G` such that `𝒰.fst` converges to `g`. -/
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto_t2 [T2Space X] : ProperSMul G X ↔
    ContinuousSMul G X ∧
    (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
    Tendsto (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) 𝒰 (𝓝 (x₁, x₂)) →
    ∃ g : G, Tendsto Prod.fst (𝒰 : Filter (G × X)) (𝓝 g)) := by
  rw [properSMul_iff_continuousSMul_ultrafilter_tendsto]
  refine and_congr_right fun hc ↦ ?_
  congrm ∀ 𝒰 x₁ x₂ hxx, ∃ g, ?_
  exact and_iff_right_of_imp fun hg ↦ tendsto_nhds_unique
    (hg.smul ((continuous_snd.tendsto _).comp hxx)) ((continuous_fst.tendsto _).comp hxx)

/-- If `G` acts properly on `X`, then the quotient space is Hausdorff (T2). -/
@[to_additive "If `G` acts properly on `X`, then the quotient space is Hausdorff (T2)."]
theorem t2Space_of_ProperSMul (hproper:ProperSMul G X) :
    T2Space (Quotient (MulAction.orbitRel G X)) := by
  rw [t2_iff_isClosed_diagonal] -- T2 if the diagonal is closed
  set R := MulAction.orbitRel G X -- the orbit relation
  set XmodG := Quotient R -- the quotient
  set π : X → XmodG := Quotient.mk' -- the projection
  have hpiopen: IsOpenMap π := -- the projection is open
    isOpenMap_quotient_mk'_mul
  have picont : Continuous π := continuous_quotient_mk' -- π is continuous
  have pisurj : Function.Surjective π := by apply surjective_quotient_mk' -- π is surjective
  set pipi := Prod.map π π
  have pipiopen : IsOpenMap pipi := IsOpenMap.prod hpiopen hpiopen -- π × π open
  have pipisurj : (Function.Surjective (pipi) ) :=  -- π × π surj
    Function.Surjective.Prod_map pisurj pisurj
  have pipipquotient := -- π × π is q QuotientMap because open, continuous and surj
    IsOpenMap.to_quotientMap pipiopen (Continuous.prod_map picont picont) pipisurj
  rw [<-QuotientMap.isClosed_preimage pipipquotient] -- closed iff preimage closed
  set gr' := pipi ⁻¹' diagonal (Quotient R) -- preimage of the diag
  set m : G × X → X × X := fun (g,x) => (g • x, x)
  set gr := range m -- graph of the orbit relation
  have r_eq_r' : gr' = gr := by -- the preimage of the diag is the graph of the relation
    ext ⟨x,y⟩
    conv_lhs => -- we work only on the left hand side for now
      rw [mem_preimage]
      rw [mem_diagonal_iff]
      change (π x = π y)  --↔ (x, y) ∈ gr
      rw [Quotient.eq']
      change ((MulAction.orbitRel G X).Rel x y)-- ↔ (x, y) ∈ gr
      rw [MulAction.orbitRel_apply]
      rw [MulAction.orbit]
      change (∃ g : G, g • y = x)
    conv_rhs =>
      rw [mem_range]
      simp
    simp [m]
  rw [r_eq_r']
  exact hproper.isProperMap_smul_pair'.isClosedMap.closed_range

/-- If a T2 group acts properly on a topological space, then this topological space is T2. -/
@[to_additive "If a T2 group acts properly on a topological space,
then this topological space is T2."]
theorem t2Space_of_properSMul_of_t2Group [h_proper : ProperSMul G X] [T2Space G] : T2Space X := by
  let f := fun x : X ↦ ((1 : G), x)
  have proper_f : IsProperMap f := by
    apply isProperMap_of_closedEmbedding
    rw [closedEmbedding_iff]
    constructor
    · let g := fun gx : G × X ↦ gx.2
      have : Function.LeftInverse g f := fun x ↦ by simp
      exact this.embedding (by fun_prop) (by fun_prop)
    · have : range f = ({1} ×ˢ univ) := by simp
      rw [this]
      exact isClosed_singleton.prod isClosed_univ
  rw [t2_iff_isClosed_diagonal]
  let g := fun gx : G × X ↦ (gx.1 • gx.2, gx.2)
  have proper_g : IsProperMap g := (properSMul_iff G X).1 h_proper
  have : g ∘ f = fun x ↦ (x, x) := by ext x <;> simp
  have range_gf : range (g ∘ f) = diagonal X := by simp [this]
  rw [← range_gf]
  exact (proper_f.comp proper_g).closed_range

/-- If two groups `H` and `G` act on a topological space `X` such that `G` acts properly and
there exists a group homomorphims `H → G` which is a closed embedding compatible with the actions,
then `H` also acts properly on `X`. -/
@[to_additive "If two groups `H` and `G` act on a topological space `X` such that `G` acts properly
and there exists a group homomorphims `H → G` which is a closed embedding compatible with the
actions, then `H` also acts properly on `X`."]
theorem properSMul_of_closed_embedding {H : Type*} [Group H] [MulAction H X] [TopologicalSpace H]
    [ProperSMul G X] (f : H →* G) (f_clemb : ClosedEmbedding f)
    (f_compat : ∀ (h : H) (x : X), f h • x = h • x) : ProperSMul H X where
  isProperMap_smul_pair' := by
    have := isProperMap_of_closedEmbedding f_clemb
    have h : IsProperMap (Prod.map f (fun x : X ↦ x)) := IsProperMap.prod_map this isProperMap_id
    have : (fun hx : H × X ↦ (hx.1 • hx.2, hx.2)) = (fun hx ↦ (f hx.1 • hx.2, hx.2)) := by
      simp [f_compat]
    rw [this]
    exact h.comp <| isProperMap_smul_pair G X

/-- If `H` is a closed subgroup of `G` and `G` acts properly on X then so does `H`. -/
@[to_additive "If `H` is a closed subgroup of `G` and `G` acts properly on X then so does `H`."]
instance {H : Subgroup G} [ProperSMul G X] [H_closed : IsClosed (H : Set G)] : ProperSMul H X :=
  properSMul_of_closed_embedding H.subtype H_closed.closedEmbedding_subtype_val fun _ _ ↦ rfl

/-- If a discrete group acts on a T2 space `X` such that `X × X` is compactly generated,
then the action is properly discontinuous if and only if it is continuous in the second variable
and proper. -/
theorem ProperlyDiscontinuousSMul_iff_ProperSMul [T2Space X] [DiscreteTopology G]
    [ContinuousConstSMul G X]
    (compactlyGenerated : ∀ s : Set (X × X), IsClosed s ↔ ∀ ⦃K⦄, IsCompact K → IsClosed (s ∩ K)) :
    ProperlyDiscontinuousSMul G X ↔ ProperSMul G X := by
  constructor
  · intro h
    rw [properSMul_iff]
    -- We have to show that `f : (g, x) ↦ (g • x, x)` is proper.
    -- Continuity follows from continuity of `g • ·` and the fact that `G` has the
    -- discrete topology, thanks to `continuous_of_partial_of_discrete`.
    -- Because `X × X` is compactly generated, to show that f is proper
    -- it is enough to show that the preimage of a compact set `K` is compact.
    refine (isProperMap_iff_isCompact_preimage compactlyGenerated).2
      ⟨(continuous_prod_mk.2
      ⟨continuous_prod_of_discrete_left.2 continuous_const_smul, by fun_prop⟩),
      fun K hK ↦ ?_⟩
    -- We set `K' := pr₁(K) ∪ pr₂(K)`, which is compact because `K` is compact and `pr₁` and
    -- `pr₂` are continuous. We halso have that `K ⊆ K' × K'`, and `K` is closed because `X` is T2.
    -- Therefore `f ⁻¹ (K)` is also closed and `f ⁻¹ (K) ⊆ f ⁻¹ (K' × K')`, thus it suffices to
    -- show that `f ⁻¹ (K' × K')` is compact.
    let K' := fst '' K ∪ snd '' K
    have hK' : IsCompact K' := (hK.image continuous_fst).union (hK.image continuous_snd)
    let E := {g : G | Set.Nonempty ((g • ·) '' K' ∩ K')}
    -- The set `E` is finite because the action is properly discontinuous.
    have fin : Set.Finite E := by
      simp_rw [E, nonempty_iff_ne_empty]
      exact h.finite_disjoint_inter_image hK' hK'
    -- Therefore we can rewrite `f ⁻¹ (K' × K')` as a finite union of compact sets.
    have : (fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) ⁻¹' (K' ×ˢ K') =
        ⋃ g ∈ E, {g} ×ˢ ((g⁻¹ • ·) '' K' ∩ K') := by
      ext gx
      simp only [mem_preimage, mem_prod, nonempty_def, mem_inter_iff, mem_image,
        exists_exists_and_eq_and, mem_setOf_eq, singleton_prod, iUnion_exists, biUnion_and',
        mem_iUnion, exists_prop, E]
      constructor
      · exact fun ⟨gx_mem, x_mem⟩ ↦ ⟨gx.2, x_mem, gx.1, gx_mem,
          ⟨gx.2, ⟨⟨gx.1 • gx.2, gx_mem, by simp⟩, x_mem⟩, rfl⟩⟩
      · rintro ⟨x, -, g, -, ⟨-, ⟨⟨x', x'_mem, rfl⟩, ginvx'_mem⟩, rfl⟩⟩
        exact ⟨by simpa, by simpa⟩
    -- Indeed each set in this finite union is the product of a singleton and
    -- the intersection of the compact `K'` with its image by some element `g`, and this image is
    -- compact because `g • ·` is continuous.
    have : IsCompact ((fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) ⁻¹' (K' ×ˢ K')) :=
      this ▸ fin.isCompact_biUnion fun g hg ↦
        isCompact_singleton.prod <| (hK'.image <| continuous_const_smul _).inter hK'
    -- We conclude as explained above.
    exact this.of_isClosed_subset (hK.isClosed.preimage <|
      continuous_prod_mk.2
      ⟨continuous_prod_of_discrete_left.2 continuous_const_smul, by fun_prop⟩) <|
      preimage_mono fun x hx ↦ ⟨Or.inl ⟨x, hx, rfl⟩, Or.inr ⟨x, hx, rfl⟩⟩
  · intro h; constructor
    intro K L hK hL
    simp_rw [← nonempty_iff_ne_empty]
    -- We want to show that a subset of `G` is finite, but as `G` has the discrete topology it
    -- is enough to show that this subset is compact.
    apply IsCompact.finite_of_discrete
    -- Now set `h : (g, x) ↦ (g⁻¹ • x, x)`, because `f` is proper by hypothesis, so is `h`.
    have : IsProperMap (fun gx : G × X ↦ (gx.1⁻¹ • gx.2, gx.2)) :=
      (IsProperMap.prod_map (Homeomorph.isProperMap (Homeomorph.inv G)) isProperMap_id).comp <|
        isProperMap_smul_pair ..
    --But we also have that `{g | Set.Nonempty ((g • ·) '' K ∩ L)} = h ⁻¹ (K × L)`, which
    -- concludes the proof.
    have eq : {g | Set.Nonempty ((g • ·) '' K ∩ L)} =
        fst '' ((fun gx : G × X ↦ (gx.1⁻¹ • gx.2, gx.2)) ⁻¹' (K ×ˢ L)) := by
      simp_rw [nonempty_def]
      ext g; constructor
      · exact fun ⟨_, ⟨x, x_mem, rfl⟩, hx⟩ ↦ ⟨(g, g • x), ⟨by simpa, hx⟩, rfl⟩
      · rintro ⟨gx, hgx, rfl⟩
        exact ⟨gx.2, ⟨gx.1⁻¹ • gx.2, hgx.1, by simp⟩, hgx.2⟩
    exact eq ▸ IsCompact.image (this.isCompact_preimage <| hK.prod hL) continuous_fst

/-- If a discrete group acts on a T2 and locally compact space `X`,
then the action is properly discontinuous if and only if it is continuous in the second variable
and proper. -/
theorem WeaklyLocallyCompactSpace.ProperlyDiscontinuousSMul_iff_ProperSMul [T2Space X]
    [WeaklyLocallyCompactSpace X] [DiscreteTopology G] [ContinuousConstSMul G X] :
    ProperlyDiscontinuousSMul G X ↔ ProperSMul G X :=
  _root_.ProperlyDiscontinuousSMul_iff_ProperSMul
    (fun _ ↦ compactlyGenerated_of_weaklyLocallyCompactSpace)

/-- If a discrete group acts on a T2 and first-countable space `X`,
then the action is properly discontinuous if and only if it is continuous in the second variable
and proper. -/
theorem FirstCountableTopology.ProperlyDiscontinuousSMul_iff_ProperSMul [T2Space X]
    [FirstCountableTopology X] [DiscreteTopology G] [ContinuousConstSMul G X] :
    ProperlyDiscontinuousSMul G X ↔ ProperSMul G X :=
  _root_.ProperlyDiscontinuousSMul_iff_ProperSMul (fun _ ↦ compactlyGenerated_of_sequentialSpace)
