/-
Copyright (c) 2026 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import Mathlib.Topology.Algebra.Group.Quotient

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

@[expose] public section

universe u₁ u₂ u₃
open CategoryTheory
  TopRep
  ContRepresentation

variable {R : Type u₁} [Ring R]
variable {G H : Type u₂} [Monoid G] [Monoid H]

variable [TopologicalSpace R] (N : Submonoid G) [N.Normal] (R)

namespace TopRep

/-- The functor `TopRep R G ⥤ TopRep R (G ⧸ N)` sending a topological representation of `G` to
the induced representation of `G ⧸ N` on its `N`-invariants. -/
abbrev relInvariantsFunctor : TopRep R G ⥤ TopRep R (G ⧸ N) where
  obj rep       := TopRep.of (rep.ρ.relInvariantsInfl N)
  map f         := TopRep.ofHom (relInvariantsIntertwining' N f.hom)

variable {R} in
/-- The inclusion into `π` of the `N`-invariants of `π`, regarded as a `G`-representation by
restriction along the quotient map `G → G ⧸ N`. This is the component at `π` of `inflι`. -/
def inflιapp (π : TopRep R G) :
    (res N.mkQ) ((relInvariantsFunctor R N).obj π) ⟶ π :=
  TopRep.ofHom {
    toFun := Subtype.val
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    isIntertwining' _ := rfl
  }

variable {R N} in
@[simp] lemma inflιapp_apply {π : TopRep R G}
    (v : res N.mkQ ((relInvariantsFunctor R N).obj π))
    : (inflιapp N π).hom v = ↑v := rfl

/-- The natural transformation whose component at a topological representation `π` of `G` is the
inclusion of the `N`-invariants of `π`, regarded as a `G`-representation by restriction along the
quotient map `G → G ⧸ N`. -/
abbrev inflι :
    (relInvariantsFunctor R N ⋙ resFunctor N.mkQ) ⟶ 𝟭 (TopRep R G) where
  app := inflιapp N
  naturality _ _ _ := rfl

end TopRep

variable [TopologicalSpace G] [SeparatelyContinuousMul G]

noncomputable section
namespace ContinuousCohomology

/-- The inflation map from the `n`-th continuous cohomology of the `G ⧸ N`-representation on the
`N`-invariants of `π` to the `n`-th continuous cohomology of `π`. -/
def inflApp (n : ℕ) (π : TopRep R G) : Hₜ n ((relInvariantsFunctor R N).obj π) ⟶ Hₜ n π :=
  (resNatTrans R (QuotientTopMonoid.mk N) n).app ((relInvariantsFunctor R N).obj π)
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
    (resFunctor N.mkQ) (HₜFunct R G n)
    (resNatTrans R (QuotientTopMonoid.mk N) n) (inflι R N) f

/-- The inflation maps `inflApp N n` as a natural transformation
`relInvariantsFunctor N ⋙ HₜFunct R (G ⧸ N) n ⟶ HₜFunct R G n`. -/
noncomputable abbrev inflNatTrans (n : ℕ) :
    relInvariantsFunctor R N ⋙ HₜFunct R (G ⧸ N) n ⟶ HₜFunct R G n where
  app            := inflApp R N n
  naturality _ _ f := inflApp_naturality R N n f

end ContinuousCohomology
end
end
