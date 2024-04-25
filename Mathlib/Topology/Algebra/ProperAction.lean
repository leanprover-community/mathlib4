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
import  Mathlib.Topology.Algebra.Group.Basic

/-!
# Proper Action

In this file we define proper action of a group on a topological space, and we prove that in this
case the quotient space is T2. We also give equivalent definitions of proper action using
ultrafilters and show the transfer of proper action to a closed subgroup.

## Main definitions

* `ProperSMul` : a group `G` acts properly on a topological space `X`
  if the map `(g, x) ↦ (g • x, x)` is proper, in the sense defined in `IsProperMap`.

## Main statements

* `t2Space_of_ProperSMul`: If a group `G` acts properly on a topological space `X`,
  then the quotient space is Hausdorff (T2).
* `t2Space_of_properSMul_of_t2Group`: If a T2 group acts properly on a topological space,
  then this topological space is T2.

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/


open Filter Topology Set Prod

/-- Additive version of proper action in the sense of Bourbaki:
the map `G×X→ X×X` is a proper map `isProperMap`
-/
@[mk_iff]
class ProperVAdd (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [AddGroup G]
    [AddAction G X] : Prop where
  /-- Additive version of proper action in the sense of Bourbaki:
the map `G×X→ X×X` is a proper map `isProperMap`  -/
  isProperMap_vadd_pair' : IsProperMap (fun gx ↦ ⟨gx.1 +ᵥ gx.2, gx.2⟩ : G × X → X × X)

/-- Proper action in the sense of Bourbaki:
the map `G×X→ X×X` is a proper map `isProperMap`
-/
@[to_additive existing, mk_iff]
class ProperSMul (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [Group G]
    [MulAction G X] : Prop where
  isProperMap_smul_pair' : IsProperMap (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X)

attribute [to_additive existing] properSMul_iff

/-- By definition, if G acts properly on X
the map `G×X→ X×X` is a proper map `isProperMap`
-/
@[to_additive]
lemma isProperMap_smul_pair (G X : Type*) [Group G] [MulAction G X]
    [TopologicalSpace G] [TopologicalSpace X] [ProperSMul G X] :
    IsProperMap (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) :=
  ProperSMul.isProperMap_smul_pair'

variable {G X Y Z W : Type*} [Group G] [MulAction G X] [MulAction G Y]
variable [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace Z] [TopologicalSpace W]

@[to_additive]
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
  · refine' fun h ↦ ⟨inferInstance, fun 𝒰 x₁ x₂ h' ↦ _⟩
    rw [properSMul_iff, isProperMap_iff_ultrafilter] at h
    rcases h.2 h' with ⟨gx, hgx1, hgx2⟩
    refine' ⟨gx.1, _, (continuous_fst.tendsto gx).mono_left hgx2⟩
    simp only [Prod.mk.injEq] at hgx1
    rw [← hgx1.2, hgx1.1]
  · rintro ⟨cont, h⟩
    rw [properSMul_iff, isProperMap_iff_ultrafilter]
    refine' ⟨by fun_prop, fun 𝒰 (x₁, x₂) hxx ↦ _⟩
    rcases h 𝒰 x₁ x₂ hxx with ⟨g, hg1, hg2⟩
    refine' ⟨(g, x₂), by rw [hg1], _⟩
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
      have : Function.LeftInverse g f := by intro x; simp
      exact Function.LeftInverse.embedding this (by fun_prop) (by fun_prop)
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
lemma properSMul_of_closed_embedding {H : Type*} [Group H] [MulAction H X] [TopologicalSpace H]
    [ProperSMul G X] (f : H →* G) (f_clemb : ClosedEmbedding f)
    (f_compat : ∀ (h : H) (x : X), f h • x = h • x) : ProperSMul H X where
  isProperMap_smul_pair' := by
    have := isProperMap_of_closedEmbedding f_clemb
    have : IsProperMap (Prod.map f (fun x : X ↦ x)) := IsProperMap.prod_map this isProperMap_id
    have : (fun hx : H × X ↦ (hx.1 • hx.2, hx.2)) = (fun hx ↦ (f hx.1 • hx.2, hx.2)) := by
      simp [f_compat]
    rw [this]
    change IsProperMap ((fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) ∘ (Prod.map f (fun x ↦ x)))
    apply IsProperMap.comp
    assumption
    exact isProperMap_smul_pair G X

/-- If `H` is a closed subgroup of `G` and `G` acts properly on X then so does `H`. -/
@[to_additive "If `H` is a closed subgroup of `G` and `G` acts properly on X then so does `H`."]
instance {H : Subgroup G} [ProperSMul G X] [H_closed : IsClosed (H : Set G)] : ProperSMul H X :=
  properSMul_of_closed_embedding (Subgroup.subtype H)
    H_closed.closedEmbedding_subtype_val fun _ _ ↦ rfl

/-
Some suggestions of things to prove,
taken from Kapovich
-/



lemma tendsTo_comp_continuous
    {lx: Filter X} {f : X → Y} {g : Y → Z} {y : Y}
    (H : Tendsto f lx (𝓝 y)) (hg: Continuous g) :
    Tendsto (g ∘ f) lx (𝓝 (g y)) := by
  apply Tendsto.comp _ H
  exact hg.tendsto y

/-- If `Y` is Hausdorff and compactly generated, then proper maps `X → Y` are exactly
continuous maps such that the preimage of any compact set is compact. -/
theorem isProperMap_iff_isCompact_preimage' [T2Space Y]
    (compactlyGenerated : ∀ s : Set Y, IsClosed s ↔ ∀ ⦃K⦄, IsCompact K → IsClosed (s ∩ K))
    {f : X → Y} :
    IsProperMap f ↔ Continuous f ∧ ∀ ⦃K⦄, IsCompact K → IsCompact (f ⁻¹' K) :=
  ⟨fun hf ↦ ⟨hf.continuous, fun _ ↦ hf.isCompact_preimage⟩,
    fun ⟨hf, h⟩ ↦ isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨hf, fun _ hs ↦ (compactlyGenerated _).2
    fun _ hK ↦ image_inter_preimage .. ▸ (((h hK).inter_left hs).image hf).isClosed,
    fun _ ↦ h isCompact_singleton⟩⟩

theorem compactlyGenerated_of_sequentialSpace [T2Space X] [SequentialSpace X] {s : Set X} :
    IsClosed s ↔ ∀ ⦃K⦄, IsCompact K → IsClosed (s ∩ K) := by
  refine' ⟨fun hs K hK ↦ hs.inter hK.isClosed,
    fun h ↦ SequentialSpace.isClosed_of_seq _ fun u p hu hup ↦
    mem_of_mem_inter_left ((h hup.isCompact_insert_range).mem_of_tendsto hup _)⟩
  simp only [mem_inter_iff, mem_insert_iff, mem_range, exists_apply_eq_apply, or_true, and_true,
    eventually_atTop, ge_iff_le]
  exact ⟨0, fun n _ ↦ hu n⟩

theorem continuous_of_partial_of_discrete [DiscreteTopology X] (f : X × Y → Z)
    (h : ∀ x, Continuous fun y ↦ f (x, y)) : Continuous f := by
  rw [continuous_def]
  intro s hs
  have : f ⁻¹' s = ⋃ x, {x} ×ˢ ((fun y : Y ↦ f (x, y)) ⁻¹' s) := by
    ext xy; constructor
    · exact fun hxy ↦ mem_iUnion.2 ⟨xy.1, mem_prod.2 ⟨mem_singleton _, hxy⟩⟩
    · intro hxy
      rcases mem_iUnion.1 hxy with ⟨x', hx'⟩
      rw [mem_prod, ← hx'.1] at hx'
      exact hx'.2
  exact this ▸ isOpen_iUnion fun x ↦ (isOpen_discrete _).prod <| (h x).isOpen_preimage s hs

/--
If `X` is T2, `G` is discrete, `X × X` is compactly generated
and the action is constantly continuous,
then the naive definition of proper action is equivalent to the good definition.
-/
theorem naiveProper_iff_ProperSMul_of_t2_of_compactlyGenerated [T2Space X] [DiscreteTopology G]
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
    refine' (isProperMap_iff_isCompact_preimage' compactlyGenerated).2
      ⟨(continuous_prod_mk.2
      ⟨continuous_of_partial_of_discrete _ continuous_const_smul, by fun_prop⟩),
      fun K hK ↦ _⟩
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
      ⟨continuous_of_partial_of_discrete _ continuous_const_smul, by fun_prop⟩) <|
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

/-- If `X` and `Y` are T2 and first countable, then the naive definition
of proper map is equivalent to the good definition. -/
theorem properMap_of_naiveProper_T2_FirstCountable
    [FirstCountableTopology X]
    [T2Space Y] [SequentialSpace Y]
    (f : X → Y) (hcont: Continuous f)
    (h : ∀ (K : Set Y), (IsCompact K → IsCompact (f ⁻¹' K))) : IsProperMap f := by
  --intro h
  -- a map is proper iff it is closed and the fibers are compacts
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨hcont, ?_, ?_ ⟩
  · rw [IsClosedMap]
    intro U closed_U
    -- in a first countable space, a set is closed iff sequentially closed
    apply IsSeqClosed.isClosed
    -- introduce a converging sequence in the image f(U)
    intro seq y seq_in_image seq_conv
    -- pullback this sequence to a sequence in U
    choose s' hs using seq_in_image
    have s'_in_U := fun n ↦ (hs n).1
    have seq_factor : seq = f ∘ s' := by
      ext n
      --simp?
      rw [<-(hs n).2]
      rfl
    -- the sequence and its limit is compact, so is its preimage by properness
    set cluster_seq := (insert y (range seq))
    have preim_comp := h cluster_seq (Tendsto.isCompact_insert_range seq_conv)
    have s'_im : ∀ n, s' n ∈ (preimage f cluster_seq) := by
      intro n
      --simp
      change (f ∘ s') n ∈ cluster_seq
      rw [<-seq_factor]
      right
      simp
    -- by compactness we have a converging subsequence
    obtain ⟨a, _, φ, hstrict, htendsto ⟩ := IsCompact.tendsto_subseq preim_comp s'_im
    -- tedious rewriting
    have fs'_tendsto : Tendsto ((f ∘ s') ∘ φ) atTop (𝓝 (f a)) :=
      tendsTo_comp_continuous htendsto hcont
    rw [<- seq_factor] at fs'_tendsto
    replace hconv := seq_conv.comp (StrictMono.tendsto_atTop hstrict)
    have aU : a ∈ U := by
      -- a closed set is sequencially closed
      have hUseq := IsClosed.isSeqClosed closed_U
      have hs3 : ∀ c, (s' ∘ φ) c ∈ U := by
        intro c
        simp only [Function.comp_apply]
        specialize s'_in_U (φ c)
        assumption
      -- the limit of s' ∘ φ is still in U
      specialize hUseq hs3 htendsto
      assumption
    use a, aU
    --constructor
    --· assumption
    -- by uniqueness of limits, y=f(a)
    rw [tendsto_nhds_unique hconv fs'_tendsto]
  · intro y
    exact h {y} isCompact_singleton
