/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Adam Topaz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Preserves

/-!
# The big Zariski site of schemes

In this file, we define the Zariski topology, as a Grothendieck topology on the
category `Scheme.{u}`: this is `Scheme.zariskiTopology.{u}`. If `X : Scheme.{u}`,
the Zariski topology on `Over X` can be obtained as `Scheme.zariskiTopology.over X`
(see `CategoryTheory.Sites.Over`.).

TODO:
* If `Y : Scheme.{u}`, define a continuous functor from the category of opens of `Y`
  to `Over Y`, and show that a presheaf on `Over Y` is a sheaf for the Zariski topology
  iff its "restriction" to the topological space `Z` is a sheaf for all `Z : Over Y`.
* We should have good notions of (pre)sheaves of `Type (u + 1)` (e.g. associated
  sheaf functor, pushforward, pullbacks) on `Scheme.{u}` for this topology. However,
  some constructions in the `CategoryTheory.Sites` folder currently assume that
  the site is a small category: this should be generalized. As a result,
  this big Zariski site can considered as a test case of the Grothendieck topology API
  for future applications to étale cohomology.

-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

/-- The Zariski pretopology on the category of schemes. -/
def zariskiPretopology : Pretopology Scheme.{u} :=
  pretopology @IsOpenImmersion

/-- The Zariski topology on the category of schemes. -/
abbrev zariskiTopology : GrothendieckTopology Scheme.{u} :=
  grothendieckTopology IsOpenImmersion

lemma zariskiTopology_eq : zariskiTopology.{u} = zariskiPretopology.toGrothendieck :=
  Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck.symm

instance subcanonical_zariskiTopology : zariskiTopology.Subcanonical := by
  apply GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
  intro X
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y S hS x hx
  obtain ⟨(𝓤 : OpenCover Y), rfl⟩ := exists_cover_of_mem_pretopology hS
  let e : Y ⟶ X := 𝓤.glueMorphisms (fun j => x (𝓤.f _) (.mk _)) <| by
    intro i j
    apply hx
    exact Limits.pullback.condition
  refine ⟨e, ?_, ?_⟩
  · rintro Z e ⟨j⟩
    dsimp [e]
    rw [𝓤.ι_glueMorphisms]
  · intro e' h
    apply 𝓤.hom_ext
    intro j
    rw [𝓤.ι_glueMorphisms]
    exact h (𝓤.f j) (.mk j)

end Scheme

/-- Zariski sheaves preserve products. -/
lemma preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology {F : Scheme.{u}ᵒᵖ ⥤ Type v}
    {ι : Type*} [Small.{u} ι] [Small.{v} ι] (hF : Presieve.IsSheaf Scheme.zariskiTopology F) :
    PreservesLimitsOfShape (Discrete ι) F := by
  apply (config := { allowSynthFailures := true }) preservesLimitsOfShape_of_discrete
  intro X
  have (i : ι) : Mono (Cofan.inj (Sigma.cocone (Discrete.functor <| unop ∘ X)) i) :=
    inferInstanceAs <| Mono (Sigma.ι _ _)
  refine Presieve.preservesProduct_of_isSheafFor F ?_ initialIsInitial
      (Sigma.cocone (Discrete.functor <| unop ∘ X)) (coproductIsCoproduct' _) ?_ ?_
  · apply hF.isSheafFor
    convert (⊥_ Scheme).bot_mem_grothendieckTopology
    rw [eq_bot_iff]
    rintro Y f ⟨g, _, _, ⟨i⟩, _⟩
    exact i.elim
  · intro i j
    exact CoproductDisjoint.isPullback_of_isInitial
      (coproductIsCoproduct' <| Discrete.functor <| unop ∘ X) initialIsInitial
  · exact hF.isSheafFor _ (sigmaOpenCover _).mem_grothendieckTopology

/-- Let `F` be a locally directed diagram of open immersions, i.e., a diagram of schemes
for which whenever `xᵢ ∈ Fᵢ` and `xⱼ ∈ Fⱼ` map to the same `xₖ ∈ Fₖ`, there exists
some `xₗ ∈ Fₗ` that maps to `xᵢ` and `xⱼ` (e.g, the diagram indexing a coproduct).
Then the colimit inclusions are a Zariski covering. -/
lemma ofArrows_ι_mem_zariskiTopology_of_isColimit {J : Type*} [Category J]
    (F : J ⥤ Scheme.{u}) [∀ {i j : J} (f : i ⟶ j), IsOpenImmersion (F.map f)]
    [(F.comp Scheme.forget).IsLocallyDirected] [Quiver.IsThin J] [Small.{u} J]
    (c : Cocone F) (hc : IsColimit c) :
    Sieve.ofArrows _ c.ι.app ∈ Scheme.zariskiTopology c.pt := by
  let iso : c.pt ≅ colimit F := hc.coconePointUniqueUpToIso (colimit.isColimit F)
  rw [← GrothendieckTopology.pullback_mem_iff_of_isIso (i := iso.inv)]
  apply GrothendieckTopology.superset_covering _ ?_ ?_
  · exact Sieve.ofArrows _ (colimit.ι F)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    exact ⟨_, 𝟙 _, c.ι.app i, ⟨i⟩, by simp [iso]⟩
  · exact (Scheme.IsLocallyDirected.openCover F).mem_grothendieckTopology

end AlgebraicGeometry
