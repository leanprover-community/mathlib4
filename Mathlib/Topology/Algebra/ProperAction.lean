/-
Copyright (c) 2024 Anatole Dedeker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedeker, Etienne Marion, Florestan Martin-Baillon, Vincent Guirardel
-/

import Mathlib.Topology.ProperMap
import Mathlib.GroupTheory.Subgroup.Actions
import Mathlib.Topology.Algebra.MulAction

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

open Filter Topology

variable {G X Y Z W : Type*} [Group G] [MulAction G X] [MulAction G Y]
variable [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace Z] [TopologicalSpace W]

@[to_additive]
instance continuousSmul_of_properSMul [ProperSMul G X] : ContinuousSMul G X where
  continuous_smul := (isProperMap_smul_pair G X).continuous.fst

/-- A group `G` acts properly on a topological space `X` if and only if for all ultrafilters`𝒰` on `X × G`, if `𝒰` converges to `(x₁, x₂)` along the map `(g, x) ↦ (g • x, x)`,
then there exists `g : G` such that `g • x₂ = x₁` and `𝒰.fst` converges to `g`. -/
@[to_additive "A group acts `G` properly on a topological space `X` if and only if
for all ultrafilters `𝒰` on `X`, if `𝒰` converges to `(x₁, x₂)`
along the map `(g, x) ↦ (g • x, x)`, then there exists `g : G` such that `g • x₂ = x₁`
and `𝒰.fst` converges to `g`."]
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto : ProperSMul G X ↔ ContinuousSMul G X
    ∧ (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
    Tendsto (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) 𝒰 (𝓝 (x₁, x₂)) →
    ∃ g : G, g • x₂ = x₁ ∧ Tendsto Prod.fst (𝒰 : Filter (G × X)) (𝓝 g)) := by
  constructor
  · intro h
    refine ⟨by infer_instance, fun 𝒰 x₁ x₂ h' ↦ ?_⟩
    rw [properSMul_iff, isProperMap_iff_ultrafilter] at h
    have ⟨(g, x), hgx1, hgx2⟩ := h.2 h'
    use g
    constructor
    · simp at hgx1
      rw [← hgx1.2, hgx1.1]
    · have := continuous_fst.tendsto (g, x)
      rw [Tendsto] at *
      calc
        map Prod.fst ↑𝒰 ≤ map Prod.fst (𝓝 (g, x)) := map_mono hgx2
        _               ≤ 𝓝 (g, x).1 := this
  · rintro ⟨cont, h⟩
    rw [properSMul_iff, isProperMap_iff_ultrafilter]
    refine ⟨by fun_prop, fun 𝒰 (x₁, x₂) hxx ↦ ?_⟩
    rcases h 𝒰 x₁ x₂ hxx with ⟨g, hg1, hg2⟩
    use (g, x₂)
    refine ⟨by rw [hg1], ?_⟩
    rw [nhds_prod_eq, 𝒰.le_prod]
    refine ⟨hg2, ?_⟩
    change Tendsto (Prod.snd ∘ (fun gx : G × X ↦ (gx.1 • gx.2, gx.2))) ↑𝒰 (𝓝 (Prod.snd (x₁, x₂)))
    apply Filter.Tendsto.comp
    apply Continuous.tendsto
    exact continuous_snd
    assumption

/-- A group `G` acts properly on a T2 topological space `X` if and only if for all ultrafilters
`𝒰` on `X × G`, if `𝒰` converges to `(x₁, x₂)` along the map `(g, x) ↦ (g • x, x)`,
then there exists `g : G` such that `𝒰.fst` converges to `g`. -/
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto_t2 [T2Space X] : ProperSMul G X ↔
    ContinuousSMul G X ∧
    (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
    Tendsto (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) 𝒰 (𝓝 (x₁, x₂)) →
    ∃ g : G, Tendsto Prod.fst (𝒰 : Filter (G × X)) (𝓝 g)) := by
  constructor
  · intro h
    have := properSMul_iff_continuousSMul_ultrafilter_tendsto.1 h
    refine ⟨this.1, fun 𝒰 x₁ x₂ h' ↦ ?_⟩
    rcases this.2 𝒰 x₁ x₂ h' with ⟨g, _, hg⟩
    exact ⟨g, hg⟩
  · rintro ⟨cont, h⟩
    rw [properSMul_iff, isProperMap_iff_ultrafilter_of_t2]
    refine ⟨by fun_prop, fun 𝒰 (x₁, x₂) hxx ↦ ?_⟩
    rcases h 𝒰 x₁ x₂ hxx with ⟨g, hg⟩
    use (g, x₂)
    rw [nhds_prod_eq, 𝒰.le_prod]
    refine ⟨by assumption, ?_⟩
    change Tendsto (Prod.snd ∘ (fun gx : G × X ↦ (gx.1 • gx.2, gx.2))) ↑𝒰 (𝓝 (Prod.snd (x₁, x₂)))
    apply Filter.Tendsto.comp
    apply Continuous.tendsto
    exact continuous_snd
    assumption

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
  set gr' := pipi ⁻¹' Set.diagonal (Quotient R) -- preimage of the diag
  set m : G × X → X × X := fun (g,x) => (g • x, x)
  set gr := Set.range m -- graph of the orbit relation
  have r_eq_r' : gr' = gr := by -- the preimage of the diag is the graph of the relation
    ext ⟨x,y⟩
    conv_lhs => -- we work only on the left hand side for now
      rw [Set.mem_preimage]
      rw [Set.mem_diagonal_iff]
      change (π x = π y)  --↔ (x, y) ∈ gr
      rw [Quotient.eq']
      change ((MulAction.orbitRel G X).Rel x y)-- ↔ (x, y) ∈ gr
      rw [MulAction.orbitRel_apply]
      rw [MulAction.orbit]
      change (∃ g : G, g • y = x)
    conv_rhs =>
      rw [Set.mem_range]
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
    · have : Set.range f = ({1} ×ˢ Set.univ) := by simp
      rw [this]
      exact IsClosed.prod isClosed_singleton isClosed_univ
  rw [t2_iff_isClosed_diagonal]
  let g := fun gx : G × X ↦ (gx.1 • gx.2, gx.2)
  have proper_g : IsProperMap g := (properSMul_iff G X).1 h_proper
  have : g ∘ f = fun x ↦ (x, x) := by ext x <;> simp
  have range_gf : Set.range (g ∘ f) = Set.diagonal X := by simp [this]
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
instance {H : Subgroup G} [ProperSMul G X] [H_closed : IsClosed (H : Set G)] : ProperSMul H X where
  isProperMap_smul_pair' := by
    have : IsProperMap (fun hx : H × X ↦ ((hx.1, hx.2) : G × X)) := by
      change IsProperMap (Prod.map ((↑) : H → G) (fun x ↦ x))
      exact IsProperMap.prod_map (isProperMap_subtype_val_of_closed H_closed) isProperMap_id
    have : IsProperMap (fun hx : H × X ↦ (hx.1 • hx.2, hx.2)) := by
      change IsProperMap ((fun gx ↦ (gx.1 • gx.2, gx.2)) ∘
        (fun hx : H × X ↦ ((hx.1, hx.2) : G × X)))
      exact this.comp (isProperMap_smul_pair G X)
    assumption

/-
Some suggestions of things to prove,
taken from Kapovich
-/

/-
If `X` is T2 and first countable,
then the naive definition
of proper action is equivalent to the good definition
(Kapovich Th 11)
-/
theorem naiveProper_of_ProperSMul_T2_FirstCountable
    [T2Space X] [FirstCountableTopology X] :
    ProperlyDiscontinuousSMul G X ↔ ProperSMul G X
    := by sorry

/-
If `X` and `Y` are T2 and first countable,
then the naive definition
of proper map is equivalent to the good definition
-/
theorem properMap_of_naiveProper_T2_FirstCountable
    [T2Space X] [FirstCountableTopology X]
    [T2Space Y] [FirstCountableTopology Y]
    (f : X → Y):
    ∀ (K : Set Y), (IsCompact K → IsCompact (f ⁻¹' K))
    → IsProperMap f
    := by
  sorry
