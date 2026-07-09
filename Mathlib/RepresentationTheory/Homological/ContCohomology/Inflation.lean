/-
Copyright (c) 2026 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill
-/
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Inflation maps in continuous cohomology

Let `N` be a normal subgroup of a topological group `G`. For a topological representation `π`
of `G`, the `N`-invariant vectors of `π` form a representation of the quotient group `G ⧸ N`;
this construction is functorial in `π`. The inflation map `Hⁿ(G ⧸ N, π^N) ⟶ Hⁿ(G, π)` on
continuous cohomology is obtained by restricting along the quotient map `G → G ⧸ N` and then
composing with the map induced by the inclusion `π^N → π`.

## Main definitions

* `ContRepresentation.relInvariants N`: the `R`-submodule of `N`-invariant vectors of a
  continuous representation.
* `TopRep.relInvariantsFunctor R N`: the functor `TopRep R G ⥤ TopRep R (G ⧸ N)` sending a
  topological representation of `G` to the induced representation of `G ⧸ N` on its
  `N`-invariants.
* `ContinuousCohomology.inflNatTrans R N n`: the inflation maps in degree `n`, as a natural
  transformation `relInvariantsFunctor R N ⋙ HₜFunct R (G ⧸ N) n ⟶ HₜFunct R G n`.
-/

universe u₁ u₂ u₃
open CategoryTheory
  TopRep
  ContRepresentation

variable {R : Type u₁} [Ring R]
variable {G H : Type u₂} [Group G] [Group H]

namespace ContRepresentation

variable {V W : Type u₃} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [Module R V] (ρ : ContRepresentation R G V)
    [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [Module R W]
    (ρ' : ContRepresentation R G W) (N : Subgroup G)

/--
For `ρ : ContRepresentation R G V` and a subgroup `N` of `G`,
`ρ.relInvariants N` is the `R`-submodule of `V` consisting of the `N`-invariant elements.
-/
def relInvariants : Submodule R V where
  carrier := {v : V | ∀ n ∈ N, ρ n v = v}
  add_mem' h₁ h₂ _ h  := by rw [map_add, h₁, h₂] <;> exact h
  zero_mem' _ _       := map_zero _
  smul_mem' _ _ h _ _ := by rwa [map_smul, h]

variable [hN : N.Normal]
lemma rho_mem_relInvariants {v : V} (hv : v ∈ ρ.relInvariants N) (g : G) :
    ρ g v ∈ ρ.relInvariants N := by
  intro n hn
  rw [← mul_apply_eq_comp, ← map_mul, show n * g = g * (g⁻¹ * n * g) by simp [mul_assoc],
    map_mul, mul_apply_eq_comp, hv _ (hN.conj_mem' n hn g)]

/-- For a normal subgroup `N` of `G`, `ρ.relInvariantsRho N` is the representation of `G` on
the `N`-invariants `ρ.relInvariants N` induced by `ρ`. -/
@[simps] def relInvariantsRho : ContRepresentation R G (ρ.relInvariants N) := ⟨{
  toFun g       := (ρ g).restrict (fun _ hv ↦ ρ.rho_mem_relInvariants N hv g)
  map_one'      := by ext; simp
  map_mul' _ _  := by ext; simp
}⟩

/-- A continuous intertwining map `f : ρ →ⁱL ρ'` restricts to a continuous intertwining map
`ρ.relInvariantsRho N →ⁱL ρ'.relInvariantsRho N` on `N`-invariants. -/
def relInvariantsIntertwining (f : ρ →ⁱL ρ') :
    ρ.relInvariantsRho N →ⁱL ρ'.relInvariantsRho N where
  toContinuousLinearMap := f.toContinuousLinearMap.restrict (by
    intro v hv n hn
    have := (f.isIntertwining n v).symm
    rwa [hv n hn] at this)
  isIntertwining' g := by
    ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_restrict_apply]
    exact f.isIntertwining g v

lemma le_relInvariantsRho_ker : N ≤ (ρ.relInvariantsRho N).toMonoidHom.ker := by
  intro n hn
  rw [MonoidHom.mem_ker]
  ext ⟨_,hv⟩
  apply hv _ hn

/-- The representation of `G ⧸ N` on the `N`-invariants `ρ.relInvariants N`, obtained by
factoring `ρ.relInvariantsRho N` through the quotient map `G → G ⧸ N`. -/
def relInvariantsInfl : ContRepresentation R (G ⧸ N) (ρ.relInvariants N) :=
  ⟨QuotientGroup.lift N (ρ.relInvariantsRho N) (ρ.le_relInvariantsRho_ker N)⟩

/-- The continuous intertwining map `ρ.relInvariantsInfl N →ⁱL ρ'.relInvariantsInfl N` of
`G ⧸ N`-representations induced by a continuous intertwining map `f : ρ →ⁱL ρ'`. -/
def relInvariantsIntertwining' (f : ρ →ⁱL ρ') :
    ρ.relInvariantsInfl N →ⁱL ρ'.relInvariantsInfl N where
  toContinuousLinearMap := (relInvariantsIntertwining ρ ρ' N f).toContinuousLinearMap
  isIntertwining' g := by
    obtain ⟨g',rfl⟩ := g.exists_rep
    apply (relInvariantsIntertwining ρ ρ' N f).isIntertwining'

end ContRepresentation

variable [TopologicalSpace R] (N : Subgroup G) [N.Normal] (R)

namespace TopRep

/-- The functor `TopRep R G ⥤ TopRep R (G ⧸ N)` sending a topological representation of `G` to
the induced representation of `G ⧸ N` on its `N`-invariants. -/
abbrev relInvariantsFunctor : TopRep R G ⥤ TopRep R (G ⧸ N) where
  obj rep       := TopRep.of (rep.ρ.relInvariantsInfl N)
  map f         := TopRep.ofHom (relInvariantsIntertwining' _ _ N f.hom)

variable {R} in
/-- The inclusion into `π` of the `N`-invariants of `π`, regarded as a `G`-representation by
restriction along the quotient map `G → G ⧸ N`. This is the component at `π` of `inflι`. -/
def inflιapp (π : TopRep R G) :
    (res (QuotientGroup.mk' N)) ((relInvariantsFunctor R N).obj π) ⟶ π :=
  TopRep.ofHom {
    toFun := Subtype.val
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    isIntertwining' _ := rfl
  }

variable {R N} in
@[simp] lemma inflιapp_apply {π : TopRep R G}
    (v : (res (QuotientGroup.mk' N)) ((relInvariantsFunctor R N).obj π))
    : (inflιapp N π).hom v = ↑v := rfl

/-- The natural transformation whose component at a topological representation `π` of `G` is the
inclusion of the `N`-invariants of `π`, regarded as a `G`-representation by restriction along the
quotient map `G → G ⧸ N`. -/
abbrev inflι :
    (relInvariantsFunctor R N ⋙ resFunctor (QuotientGroup.mk' N)) ⟶ 𝟭 (TopRep R G) where
  app := inflιapp N
  naturality _ _ _ := rfl

end TopRep

variable [TopologicalSpace G] [IsTopologicalGroup G]

noncomputable section
namespace ContinuousCohomology

/-- The inflation map from the `n`-th continuous cohomology of the `G ⧸ N`-representation on the
`N`-invariants of `π` to the `n`-th continuous cohomology of `π`. -/
def inflApp (n : ℕ) (π : TopRep R G) : Hₜ n ((relInvariantsFunctor R N).obj π) ⟶ Hₜ n π :=
  (resNatTrans R (QuotientTopGroup.mk N) n).app ((relInvariantsFunctor R N).obj π)
  ≫ (HₜFunct R G n).map ((inflι R N).app π)

/-- Abstract form of `inflApp_naturality`: given `α : K ⟶ L ⋙ H` and `ι : Φ ⋙ L ⟶ 𝟭 A`, the
maps `α.app (Φ.obj π) ≫ H.map (ι.app π)` are natural in `π`. Stating this for opaque functors
keeps the elaboration of the concrete instance below cheap. -/
private lemma inflApp_naturality_aux {A B M : Type*} [Category A] [Category B] [Category M]
    (Φ : A ⥤ B) (K : B ⥤ M) (L : B ⥤ A) (H : A ⥤ M)
    (α : K ⟶ L ⋙ H) (ι : Φ ⋙ L ⟶ 𝟭 A) {π₁ π₂ : A} (f : π₁ ⟶ π₂) :
    (Φ ⋙ K).map f ≫ (α.app (Φ.obj π₂) ≫ H.map (ι.app π₂)) =
      (α.app (Φ.obj π₁) ≫ H.map (ι.app π₁)) ≫ H.map f := by
  have h := (Functor.whiskerLeft Φ α ≫ Functor.whiskerRight ι H).naturality f
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.id_map, Category.assoc] at h ⊢
  exact h

/-- The components `inflApp N n` are natural in the representation: they intertwine the
functorial maps on continuous cohomology. -/
lemma inflApp_naturality (n : ℕ) {π₁ π₂ : TopRep R G} (f : π₁ ⟶ π₂) :
    (relInvariantsFunctor R N ⋙ HₜFunct R (G ⧸ N) n).map f ≫ inflApp R N n π₂ =
      inflApp R N n π₁ ≫ (HₜFunct R G n).map f :=
  inflApp_naturality_aux (relInvariantsFunctor R N) (HₜFunct R (G ⧸ N) n)
    (resFunctor (QuotientGroup.mk' N)) (HₜFunct R G n)
    (resNatTrans R (QuotientTopGroup.mk N) n) (inflι R N) f

/-- The inflation maps `inflApp N n` as a natural transformation
`relInvariantsFunctor N ⋙ HₜFunct R (G ⧸ N) n ⟶ HₜFunct R G n`. -/
noncomputable abbrev inflNatTrans (n : ℕ) :
    relInvariantsFunctor R N ⋙ HₜFunct R (G ⧸ N) n ⟶ HₜFunct R G n where
  app            := inflApp R N n
  naturality _ _ f := inflApp_naturality R N n f

end ContinuousCohomology
end
