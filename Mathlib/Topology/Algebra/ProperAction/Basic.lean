/-
Copyright (c) 2024 Anatole Dedeker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedeker, Etienne Marion, Florestan Martin-Baillon, Vincent Guirardel
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.LocalAtTarget

/-!
# Proper group action

In this file we define proper action of a group on a topological space, and we prove that in this
case the quotient space is T2. We also give equivalent definitions of proper action using
ultrafilters and show the transfer of proper action to a closed subgroup.

## Main definitions

* `ProperSMul` : a group `G` acts properly on a topological space `X`
  if the map `(g, x) ↦ (g • x, x)` is proper, in the sense of `IsProperMap`.

## Main statements

* `t2Space_quotient_mulAction_of_properSMul`: If a group `G` acts properly
  on a topological space `X`, then the quotient space is Hausdorff (T2).
* `t2Space_of_properSMul_of_t1Group`: If a T1 group acts properly on a topological space,
  then this topological space is T2.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]

## Tags

Hausdorff, group action, proper action
-/
set_option backward.defeqAttrib.useBackward true

public section

open Filter Topology Set Prod

/-- Proper group action in the sense of Bourbaki:
the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
class ProperVAdd (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [AddGroup G]
    [AddAction G X] : Prop where
  /-- Proper group action in the sense of Bourbaki:
  the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
  isProperMap_vadd_pair : IsProperMap (fun gx ↦ (gx.1 +ᵥ gx.2, gx.2) : G × X → X × X)

/-- Proper group action in the sense of Bourbaki:
the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
@[to_additive existing (attr := mk_iff)]
class ProperSMul (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [Group G]
    [MulAction G X] : Prop where
  /-- Proper group action in the sense of Bourbaki:
  the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
  isProperMap_smul_pair : IsProperMap (fun gx ↦ (gx.1 • gx.2, gx.2) : G × X → X × X)

attribute [to_additive existing] properSMul_iff

variable {G X : Type*} [Group G] [MulAction G X]
variable [TopologicalSpace G] [TopologicalSpace X]

/-- If a group acts properly then in particular it acts continuously. -/
@[to_additive /-- If a group acts properly then in particular it acts continuously. -/]
-- See note [lower instance property]
instance (priority := 100) ProperSMul.toContinuousSMul [ProperSMul G X] : ContinuousSMul G X where
  continuous_smul := isProperMap_smul_pair.continuous.fst

/-- A group `G` acts properly on a topological space `X` if and only if for all ultrafilters
`𝒰` on `X × G`, if `𝒰` converges to `(x₁, x₂)` along the map `(g, x) ↦ (g • x, x)`,
then there exists `g : G` such that `g • x₂ = x₁` and `𝒰.fst` converges to `g`. -/
@[to_additive /-- An additive group `G` acts properly on a topological space `X` if and only if
for all ultrafilters `𝒰` on `X`, if `𝒰` converges to `(x₁, x₂)`
along the map `(g, x) ↦ (g • x, x)`, then there exists `g : G` such that `g • x₂ = x₁`
and `𝒰.fst` converges to `g`. -/]
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto :
    ProperSMul G X ↔ ContinuousSMul G X ∧
      (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
        Tendsto (fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) 𝒰 (𝓝 (x₁, x₂)) →
        ∃ g : G, g • x₂ = x₁ ∧ Tendsto (Prod.fst : G × X → G) 𝒰 (𝓝 g)) := by
  refine ⟨fun h ↦ ⟨inferInstance, fun 𝒰 x₁ x₂ h' ↦ ?_⟩, fun ⟨cont, h⟩ ↦ ?_⟩
  · rw [properSMul_iff, isProperMap_iff_ultrafilter] at h
    rcases h.2 h' with ⟨gx, hgx1, hgx2⟩
    refine ⟨gx.1, ?_, (continuous_fst.tendsto gx).mono_left hgx2⟩
    simp only [Prod.mk.injEq] at hgx1
    rw [← hgx1.2, hgx1.1]
  · rw [properSMul_iff, isProperMap_iff_ultrafilter]
    refine ⟨by fun_prop, fun 𝒰 (x₁, x₂) hxx ↦ ?_⟩
    rcases h 𝒰 x₁ x₂ hxx with ⟨g, hg1, hg2⟩
    refine ⟨(g, x₂), by simp_rw [hg1], ?_⟩
    rw [nhds_prod_eq, 𝒰.le_prod]
    exact ⟨hg2, (continuous_snd.tendsto _).comp hxx⟩

/-- A group `G` acts properly on a T2 topological space `X` if and only if for all ultrafilters
`𝒰` on `X × G`, if `𝒰` converges to `(x₁, x₂)` along the map `(g, x) ↦ (g • x, x)`,
then there exists `g : G` such that `𝒰.fst` converges to `g`. -/
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto_t2 [T2Space X] :
    ProperSMul G X ↔ ContinuousSMul G X ∧
      (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
        Tendsto (fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) 𝒰 (𝓝 (x₁, x₂)) →
        ∃ g : G, Tendsto (Prod.fst : G × X → G) 𝒰 (𝓝 g)) := by
  rw [properSMul_iff_continuousSMul_ultrafilter_tendsto]
  refine and_congr_right fun hc ↦ ?_
  congrm ∀ 𝒰 x₁ x₂ hxx, ∃ g, ?_
  exact and_iff_right_of_imp fun hg ↦ tendsto_nhds_unique
    (hg.smul ((continuous_snd.tendsto _).comp hxx)) ((continuous_fst.tendsto _).comp hxx)

/-- If `G` acts properly on `X`, then the quotient space is Hausdorff (T2). -/
@[to_additive /-- If `G` acts properly on `X`, then the quotient space is Hausdorff (T2). -/]
instance t2Space_quotient_mulAction_of_properSMul [ProperSMul G X] :
    T2Space (Quotient (MulAction.orbitRel G X)) := by
  rw [t2_iff_isClosed_diagonal]
  set R := MulAction.orbitRel G X
  let π : X → Quotient R := Quotient.mk'
  have : IsOpenQuotientMap (Prod.map π π) :=
    MulAction.isOpenQuotientMap_quotientMk.prodMap MulAction.isOpenQuotientMap_quotientMk
  rw [← this.isQuotientMap.isClosed_preimage]
  convert ProperSMul.isProperMap_smul_pair.isClosedMap.isClosed_range
  · ext ⟨x₁, x₂⟩
    simp only [mem_preimage, map_apply, mem_diagonal_iff, mem_range, Prod.mk.injEq, Prod.exists,
      exists_eq_right]
    rw [Quotient.eq', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  all_goals infer_instance

/-- If a T1 group acts properly on a topological space, then this topological space is T2. -/
@[to_additive /-- If a T1 group acts properly on a topological space,
then this topological space is T2. -/]
theorem t2Space_of_properSMul_of_t1Group [h_proper : ProperSMul G X] [T1Space G] : T2Space X := by
  let f := fun x : X ↦ ((1 : G), x)
  have proper_f : IsProperMap f := by
    refine IsClosedEmbedding.isProperMap ⟨isEmbedding_prodMkRight 1, ?_⟩
    have : range f = ({1} ×ˢ univ) := by simp [f, Set.singleton_prod]
    rw [this]
    exact isClosed_singleton.prod isClosed_univ
  rw [t2_iff_isClosed_diagonal]
  let g := fun gx : G × X ↦ (gx.1 • gx.2, gx.2)
  have proper_g : IsProperMap g := (properSMul_iff G X).1 h_proper
  have : g ∘ f = fun x ↦ (x, x) := by ext x <;> simp [f, g]
  have range_gf : range (g ∘ f) = diagonal X := by simp [this]
  rw [← range_gf]
  exact (proper_g.comp proper_f).isClosed_range

/-- If two groups `H` and `G` act on a topological space `X` such that `G` acts properly and
there exists a group homomorphism `H → G` which is a closed embedding compatible with the actions,
then `H` also acts properly on `X`. -/
@[to_additive /-- If two groups `H` and `G` act on a topological space `X` such that `G` acts
properly and there exists a group homomorphism `H → G` which is a closed embedding compatible with
the actions, then `H` also acts properly on `X`. -/]
theorem properSMul_of_isClosedEmbedding {H : Type*} [Group H] [MulAction H X] [TopologicalSpace H]
    [ProperSMul G X] (f : H →* G) (f_clemb : IsClosedEmbedding f)
    (f_compat : ∀ (h : H) (x : X), f h • x = h • x) : ProperSMul H X where
  isProperMap_smul_pair := by
    have h : IsProperMap (Prod.map f (fun x : X ↦ x)) := f_clemb.isProperMap.prodMap isProperMap_id
    have : (fun hx : H × X ↦ (hx.1 • hx.2, hx.2)) = (fun hx ↦ (f hx.1 • hx.2, hx.2)) := by
      simp [f_compat]
    rw [this]
    exact ProperSMul.isProperMap_smul_pair.comp h

/-- If `H` is a closed subgroup of `G` and `G` acts properly on `X`, then so does `H`. -/
@[to_additive
/-- If `H` is a closed subgroup of `G` and `G` acts properly on `X`, then so does `H`. -/]
instance {H : Subgroup G} [ProperSMul G X] [H_closed : IsClosed (H : Set G)] : ProperSMul H X :=
  properSMul_of_isClosedEmbedding H.subtype H_closed.isClosedEmbedding_subtypeVal fun _ _ ↦ rfl

/-- The action `G ↷ G` by left translations is proper. -/
@[to_additive
/-- The action `G ↷ G` by left translations is proper. -/]
instance [IsTopologicalGroup G] : ProperSMul G G where
  isProperMap_smul_pair := by
    let Φ : G × G ≃ₜ G × G :=
    { toFun := fun gh ↦ (gh.1 * gh.2, gh.2)
      invFun := fun gh ↦ (gh.1 * gh.2⁻¹, gh.2)
      left_inv := fun _ ↦ by simp
      right_inv := fun _ ↦ by simp }
    exact Φ.isProperMap

open MulOpposite in
/-- The action `Gᵐᵒᵖ ↷ G` by right translations is proper. -/
@[to_additive
/-- The action `Gᵃᵒᵖ ↷ G` by right translations is proper. -/]
instance [IsTopologicalGroup G] : ProperSMul Gᵐᵒᵖ G where
  isProperMap_smul_pair := by
    let Φ : Gᵐᵒᵖ × G ≃ₜ G × G :=
    { toFun := fun gh ↦ (gh.2 * (unop gh.1), gh.2)
      invFun := fun gh ↦ (op (gh.2⁻¹ * gh.1), gh.2)
      left_inv := fun _ ↦ by simp
      right_inv := fun _ ↦ by simp }
    exact Φ.isProperMap

/-- Given a closed subgroup `H` of a topological group `G`, the right action of `H` on `G`
is proper. Note that the corresponding statement for the left action can be proven by
`inferInstance`. -/
@[to_additive /-- Given a closed subgroup `H` of an additive topological group `G`, the right
action of `H` on `G` is proper. Note that the corresponding statement for the left action can be
proven by `inferInstance`. -/]
instance [IsTopologicalGroup G] {H : Subgroup G} [H_closed : IsClosed (H : Set G)] :
    ProperSMul H.op G :=
  have : IsClosed (H.op : Set Gᵐᵒᵖ) := H_closed.preimage MulOpposite.continuous_unop
  inferInstance

@[to_additive]
instance QuotientGroup.instT2Space [IsTopologicalGroup G] {H : Subgroup G} [IsClosed (H : Set G)] :
    T2Space (G ⧸ H) :=
  t2Space_quotient_mulAction_of_properSMul

/-- If `G` acts on `X` properly, then the map `G × T → X × T, (g, t) ↦ (g • t, t)` is still
proper for *any* subset `T` of `X`. -/
@[to_additive
/-- If `G` acts on `X` properly, then the map `G × T → X × T, (g, t) ↦ (g +ᵥ t, t)` is still
proper for *any* subset `T` of `X`. -/]
lemma ProperSMul.isProperMap_smul_pair_set [ProperSMul G X] {t : Set X} :
    IsProperMap (fun (gx : G × t) ↦ ((gx.1 • gx.2, gx.2) : X × t)) := by
  let Φ : G × X → X × X := fun gx ↦ (gx.1 • gx.2, gx.2)
  have Φ_proper : IsProperMap Φ := ProperSMul.isProperMap_smul_pair
  let α : G × t ≃ₜ (Φ ⁻¹' (snd ⁻¹' t)) :=
    have : univ ×ˢ t = Φ ⁻¹' (snd ⁻¹' t) := by ext; simp [Φ]
    Homeomorph.Set.univ G |>.symm.prodCongr (.refl t) |>.trans
      ((Homeomorph.Set.prod _ t).symm) |>.trans (Homeomorph.setCongr this)
  let β : X × t ≃ₜ (snd ⁻¹' t) :=
    Homeomorph.Set.univ X |>.symm.prodCongr (.refl t) |>.trans
      ((Homeomorph.Set.prod _ t).symm) |>.trans (Homeomorph.setCongr univ_prod)
  exact β.symm.isProperMap.comp (Φ_proper.restrictPreimage (snd ⁻¹' t)) |>.comp α.isProperMap

open Pointwise in
/-- If `G` acts on `X` properly, the set `s • t` is closed when `s : Set G` is *closed* and
`t : Set X` is *compact*.

See also `IsClosed.smul_left_of_isCompact` for a version with the assumptions on `s` and `t`
reversed. -/
@[to_additive
/-- If `G` acts on `X` properly, the set `s +ᵥ t` is closed when `s : Set G` is *closed* and
`t : Set X` is *compact*. In particular, this applies when the action comes from an
`IsTopologicalAddTorsor`.

See also `IsClosed.vadd_left_of_isCompact` for a version with the assumptions on `s` and `t`
reversed. -/]
theorem IsClosed.smul_right_of_isCompact [ProperSMul G X] {s : Set G} {t : Set X} (hs : IsClosed s)
    (ht : IsCompact t) : IsClosed (s • t) := by
  let Ψ : G × t → X × t := fun gx ↦ (gx.1 • gx.2, gx.2)
  have Ψ_proper : IsProperMap Ψ := ProperSMul.isProperMap_smul_pair_set
  have : s • t = (fst ∘ Ψ) '' (fst ⁻¹' s) :=
    subset_antisymm
      (smul_subset_iff.mpr fun g hg x hx ↦ mem_image_of_mem (fst ∘ Ψ) (x := ⟨g, ⟨x, hx⟩⟩) hg)
      (image_subset_iff.mpr fun ⟨g, ⟨x, hx⟩⟩ hg ↦ smul_mem_smul hg hx)
  rw [this]
  have : CompactSpace t := isCompact_iff_compactSpace.mp ht
  exact (isProperMap_fst_of_compactSpace.comp Ψ_proper).isClosedMap _ (hs.preimage continuous_fst)

/-! One may expect `IsClosed.smul_right_of_isCompact` to hold for arbitrary continuous actions,
but such a lemma can't be true in this level of generality. For a counterexample, consider
`ℚ` acting on `ℝ` by translation, and let `s : Set ℚ := univ`, `t : set ℝ := {0}`. Then `s` is
closed and `t` is compact, but `s +ᵥ t` is the set of all rationals, which is definitely not
closed in `ℝ`. -/

open Pointwise in
/-- If `G` acts properly on `X`, then for each pair of compacts `U, V ⊆ X`,
the set of `g` such that `g • U` intersects `V` is compact.

See `MulAction.properSMul_iff_isCompact_setOf_inter_nonempty` for the two-way implication
under additional conditions on `G` and `X`. -/
@[to_additive /-- If `G` acts properly on `X`, then for each pair of compacts `U, V ⊆ X`,
the set of `g` such that `g +ᵥ U` intersects `V` is compact.

See `AddAction.properVAdd_iff_isCompact_setOf_inter_nonempty` for the two-way implication
under additional conditions on `G` and `X`. -/]
lemma ProperSMul.isCompact_setOf_inter_nonempty
    {G : Type*} [Group G] [MulAction G X] [TopologicalSpace G] [ProperSMul G X]
    {U V : Set X} (hU : IsCompact U) (hV : IsCompact V) :
    IsCompact {g : G | (g • U ∩ V).Nonempty} := by
  convert ((ProperSMul.isProperMap_smul_pair (G := G)).isCompact_preimage
    (hV.prod hU)).image continuous_fst
  ext g
  suffices (∃ v, v ∈ g • U ∧ v ∈ V) ↔ ∃ u, g • u ∈ V ∧ u ∈ U by simpa
  rw [← (MulAction.toPerm g).exists_congr_right]
  simp [and_comm]

/-- If `G` acts transitively on `X`, and the orbit map of a point in `X` is a proper map, then the
action is proper. -/
@[to_additive]
lemma MulAction.properSMul_of_proper_orbitMap
    [ContinuousSMul G X] [IsTopologicalGroup G] [MulAction.IsPretransitive G X]
    {x : X} (hx : IsProperMap fun g : G ↦ g • x) : ProperSMul G X := by
  constructor
  let f : G × G → G × X := Prod.map id (fun g ↦ g • x)
  have hfsurj : f.Surjective := Function.surjective_id.prodMap (surjective_smul G x)
  refine isProperMap_of_comp_of_surj (by fun_prop) (by fun_prop) ?_ hfsurj
  simpa [Function.comp_def, Prod.map_apply, mul_smul]
    using (hx.prodMap hx).comp (ProperSMul.isProperMap_smul_pair (G := G))

end
