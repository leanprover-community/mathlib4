/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Patrick Massot, Johannes Hölzl
-/
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Constructions of new uniform groups from old ones
-/

variable {G H hom : Type*} [Group G] [Group H]

section LatticeOps

@[to_additive]
theorem isUniformGroup_sInf {us : Set (UniformSpace G)} (h : ∀ u ∈ us, @IsUniformGroup G u _) :
    @IsUniformGroup G (sInf us) _ :=
  @IsUniformGroup.mk G (_) _ <|
    uniformContinuous_sInf_rng.mpr fun u hu =>
      uniformContinuous_sInf_dom₂ hu hu (@IsUniformGroup.uniformContinuous_div G u _ (h u hu))

@[deprecated (since := "2025-03-31")] alias uniformAddGroup_sInf := isUniformAddGroup_sInf
@[to_additive existing, deprecated
  (since := "2025-03-31")] alias uniformGroup_sInf := isUniformGroup_sInf

@[to_additive]
theorem isUniformGroup_iInf {ι : Sort*} {us' : ι → UniformSpace G}
    (h' : ∀ i, @IsUniformGroup G (us' i) _) : @IsUniformGroup G (⨅ i, us' i) _ := by
  rw [← sInf_range]
  exact isUniformGroup_sInf (Set.forall_mem_range.mpr h')

@[deprecated (since := "2025-03-31")] alias uniformAddGroup_iInf := isUniformAddGroup_iInf
@[to_additive existing, deprecated
  (since := "2025-03-31")] alias uniformGroup_iInf := isUniformGroup_iInf

@[to_additive]
theorem isUniformGroup_inf {u₁ u₂ : UniformSpace G} (h₁ : @IsUniformGroup G u₁ _)
    (h₂ : @IsUniformGroup G u₂ _) : @IsUniformGroup G (u₁ ⊓ u₂) _ := by
  rw [inf_eq_iInf]
  refine isUniformGroup_iInf fun b => ?_
  cases b <;> assumption

@[deprecated (since := "2025-03-31")] alias uniformAddGroup_inf := isUniformAddGroup_inf
@[to_additive existing, deprecated
  (since := "2025-03-31")] alias uniformGroup_inf := isUniformGroup_inf

end LatticeOps

section Comap

@[to_additive]
lemma IsUniformInducing.isUniformGroup [UniformSpace G] [UniformSpace H]
    [IsUniformGroup H] [FunLike hom G H] [MonoidHomClass hom G H]
    (f : hom) (hf : IsUniformInducing f) :
    IsUniformGroup G where
  uniformContinuous_div := by
    simp_rw [hf.uniformContinuous_iff, Function.comp_def, map_div]
    exact uniformContinuous_div.comp (hf.uniformContinuous.prodMap hf.uniformContinuous)

@[deprecated (since := "2025-03-30")]
alias IsUniformInducing.uniformAddGroup := IsUniformInducing.isUniformAddGroup
@[to_additive existing, deprecated (since := "2025-03-30")]
alias IsUniformInducing.uniformGroup := IsUniformInducing.isUniformGroup

@[to_additive]
protected theorem IsUniformGroup.comap {u : UniformSpace H} [IsUniformGroup H]
    [FunLike hom G H] [MonoidHomClass hom G H] (f : hom) :
    @IsUniformGroup G (u.comap f) _ :=
  letI : UniformSpace G := u.comap f; IsUniformInducing.isUniformGroup f ⟨rfl⟩

end Comap

section PiProd

@[to_additive]
instance Prod.instIsUniformGroup [UniformSpace G] [hG : IsUniformGroup G]
    [UniformSpace H] [hH : IsUniformGroup H] :
    IsUniformGroup (G × H) := by
  rw [instUniformSpaceProd]
  exact isUniformGroup_inf (.comap <| MonoidHom.fst G H) (.comap <| MonoidHom.snd G H)

@[deprecated (since := "2025-03-31")] alias Prod.instUniformAddGroup :=
  Prod.instIsUniformAddGroup
@[to_additive existing, deprecated
  (since := "2025-03-31")] alias Prod.instUniformGroup := Prod.instIsUniformGroup

@[to_additive]
instance Pi.instIsUniformGroup {ι : Type*} {G : ι → Type*} [∀ i, UniformSpace (G i)]
    [∀ i, Group (G i)] [∀ i, IsUniformGroup (G i)] : IsUniformGroup (∀ i, G i) := by
  rw [Pi.uniformSpace_eq]
  exact isUniformGroup_iInf fun i ↦ .comap (Pi.evalMonoidHom G i)

end PiProd

section DiscreteUniformity

/-- The discrete uniformity makes a group a `IsUniformGroup. -/
@[to_additive /-- The discrete uniformity makes an additive group a `IsUniformAddGroup`. -/]
instance [UniformSpace G] [DiscreteUniformity G] : IsUniformGroup G where
  uniformContinuous_div := DiscreteUniformity.uniformContinuous (G × G) fun p ↦ p.1 / p.2

end DiscreteUniformity
