/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Characterization of (pre)stacks for a pretopology

-/

@[expose] public section

universe t t' v' v u' u

namespace CategoryTheory

open Limits Opposite Bicategory

namespace Pseudofunctor

open DescentData

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

section

variable {J : GrothendieckTopology C} [F.IsPrestack J]

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {ι' : Type t'} {X' : ι' → C} {f' : ∀ j, X' j ⟶ S}
  {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)} (w : ∀ j, p' j ≫ f (α j) = f' j)
  (hf' : Sieve.ofArrows _ f' ∈ J S)

include hf'

open LocallyDiscreteOpToCat in
lemma faithful_pullFunctor :
    (pullFunctor F (f := f) (p := 𝟙 _) (f' := f') (p' := p') (by cat_disch)).Faithful where
  map_injective {D₁ D₂ φ φ'} hφ := by
    ext i
    refine F.presheafHomObjHomEquiv.injective ?_i
    have : (Sieve.overEquiv (Over.mk (𝟙 (X i)))).symm
      (Sieve.pullback (f i) (Sieve.ofArrows X' f')) ∈ J.over (X i) _ := by
      simpa only [J.mem_over_iff, Equiv.apply_symm_apply] using J.pullback_stable (f i) hf'
    refine (((isSheaf_iff_isSheaf_of_type _ _).1
      (IsPrestack.isSheaf _ _ _)).isSeparated _ this).ext ?_
    rintro Z g ⟨Y, p, c, ⟨j⟩, hp⟩
    dsimp at p hp
    have : g.left = Z.hom := by simpa using Over.w g
    have (ψ : D₁ ⟶ D₂) :
      (F.presheafHom _ _).map g.op (F.presheafHomObjHomEquiv (ψ.hom i)) =
        D₁.hom (Z.hom ≫ f i) Z.hom (p ≫ p' j) ≫
          pullHom ((F.map (p' j).op.toLoc).toFunctor.map (ψ.hom (α j))) p _ _ ≫
          D₂.hom (Z.hom ≫ f i) (p ≫ p' j) Z.hom := by
      dsimp [presheafHomObjHomEquiv]
      sorry
    replace hφ := congr_fun (congr_arg DescentData.Hom.hom hφ) j
    dsimp at hφ
    simp only [this, hφ]

lemma full_pullFunctor :
    (pullFunctor F (f := f) (p := 𝟙 _) (f' := f') (p' := p') (by cat_disch)).Full := by
  sorry

noncomputable def fullyFaithfulPullFunctor :
    (pullFunctor F (f := f) (p := 𝟙 _) (f' := f') (p' := p') (by cat_disch)).FullyFaithful := by
  have := F.faithful_pullFunctor w hf'
  have := F.full_pullFunctor w hf'
  exact Functor.FullyFaithful.ofFullyFaithful _

end

section

variable {F} [HasPullbacks C] {J : Pretopology C}

lemma IsPrestack.of_pretopology
    (hF : ∀ (S : C) (R : Presieve S) (hR : R ∈ J S),
      (F.toDescentData (fun (f : R.category) ↦ f.obj.hom)).FullyFaithful) :
    F.IsPrestack J.toGrothendieck := by
  sorry

lemma IsStack.of_pretopology
    (hF : ∀ (S : C) (R : Presieve S) (_ : R ∈ J S),
      (F.toDescentData (fun (f : R.category) ↦ f.obj.hom)).IsEquivalence) :
    F.IsStack J.toGrothendieck := by
  have : F.IsPrestack J.toGrothendieck := .of_pretopology (fun S R hR ↦ by
    have := hF S R hR
    exact Functor.FullyFaithful.ofFullyFaithful _)
  constructor
  rintro S R ⟨R', hR', h⟩
  have := hF S R' hR'
  let G := F.toDescentData (fun (f : R.arrows.category) ↦ f.obj.hom)
  let G' := F.toDescentData (fun (f : R'.category) ↦ f.obj.hom)
  obtain ⟨H, hH, ⟨e⟩⟩ :
      ∃ (H : _ ⥤ _) (_ : H.FullyFaithful), Nonempty (G ⋙ H ≅ G') :=
    ⟨pullFunctor (p := 𝟙 _) (α := fun i ↦ ⟨i.obj, h _ i.property⟩)
      (p' := fun _ ↦ 𝟙 _) _ (by simp),
        F.fullyFaithfulPullFunctor (J := J.toGrothendieck) (by simp) ⟨R', hR', fun _ g hg ↦
          ⟨_, 𝟙 _, g, .mk (ι := R'.category) ⟨Over.mk g, hg⟩, by simp⟩⟩,
        ⟨toDescentDataCompPullFunctorIso _ _ ≪≫
          (Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId _)) _) ≪≫
            Functor.leftUnitor _⟩⟩
  exact ⟨fun D ↦ ⟨_, ⟨hH.preimageIso (e.app _ ≪≫ G'.objObjPreimageIso (H.obj D))⟩⟩⟩

end

end Pseudofunctor

end CategoryTheory
