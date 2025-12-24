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

open DescentData LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

section

variable {J : GrothendieckTopology C} [F.IsPrestack J]

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {ι' : Type t'} {X' : ι' → C} {f' : ∀ j, X' j ⟶ S}
  {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)} (w : ∀ j, p' j ≫ f (α j) = f' j)
  (hf' : Sieve.ofArrows _ f' ∈ J S)

include hf' in
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

namespace full_pullFunctor

variable {F} {D₁ D₂ : F.DescentData f}
  (φ : (pullFunctor F (p := 𝟙 _) (f' := f') (p' := p') (by cat_disch)).obj D₁ ⟶
    (pullFunctor F (p := 𝟙 _) (f' := f') (p' := p') (by cat_disch)).obj D₂)

variable (f f') in
abbrev sieve (i : ι) : Sieve (Over.mk (𝟙 (X i))) :=
  (Sieve.overEquiv (Over.mk (𝟙 (X i)))).symm
    (Sieve.pullback (f i) (Sieve.ofArrows X' f'))

include hf' in
variable (f) in
lemma sieve_mem (i : ι) : sieve f f' i ∈ J.over _ _ := by
  simpa only [J.mem_over_iff, Equiv.apply_symm_apply] using J.pullback_stable (f i) hf'

lemma mem_sieve {i : ι} {Z : C} (q : Z ⟶ X i) ⦃j : ι'⦄ (a : Z ⟶ X' j)
    (fac : a ≫ f' j = q ≫ f i) :
    sieve f f' i (Over.homMk q : Over.mk q ⟶ Over.mk (𝟙 (X i))) :=
  ⟨_, a, f' j, ⟨j⟩, fac⟩

namespace sieve

variable {i : ι} {Z : C} {q : Z ⟶ X i}
  (hq : sieve f f' i (Over.homMk q : Over.mk q ⟶ Over.mk (𝟙 X i)))

include hq in
lemma exists_fac : ∃ (j : ι') (a : Z ⟶ X' j), a ≫ f' j = q ≫ f i := by
  obtain ⟨_, q, _, ⟨j⟩, fac⟩ := hq
  exact ⟨j, q, fac⟩

noncomputable def idx : ι' := (exists_fac hq).choose

noncomputable def a : Z ⟶ X' (idx hq) := (exists_fac hq).choose_spec.choose

lemma fac : (a hq) ≫ f' (idx hq) = q ≫ f i := (exists_fac hq).choose_spec.choose_spec

end sieve

def mor ⦃i : ι⦄ {Z : C} (q : Z ⟶ X i) ⦃j : ι'⦄ (a : Z ⟶ X' j)
    (fac : a ≫ f' j = q ≫ f i) :
    (presheafHom F (D₁.obj i) (D₂.obj i)).obj (op (Over.mk q)) :=
  D₁.hom (q ≫ f i) q (a ≫ p' j) ≫ pullHom (φ.hom j) a _ _ ≫ D₂.hom (q ≫ f i) (a ≫ p' j) q

include w φ in
lemma mor_precomp ⦃i : ι⦄ {Z : C} (q : Z ⟶ X i) ⦃j : ι'⦄ (a : Z ⟶ X' j)
    (fac : a ≫ f' j = q ≫ f i) {Z' : C} (r : Z' ⟶ Z)
    (r' : Z' ⟶ X i) (hr' : r ≫ q = r')
    (a' : Z' ⟶ X' j) (ha' : r ≫ a = a') :
    mor w φ r' a' (by cat_disch) =
      (presheafHom F (D₁.obj i) (D₂.obj i)).map (Over.homMk r).op (mor w φ q a fac) := by
  sorry

lemma mor_unique ⦃i : ι⦄ {Z : C} (q : Z ⟶ X i)
    ⦃j₁ : ι'⦄ (a₁ : Z ⟶ X' j₁) (fac₁ : a₁ ≫ f' j₁ = q ≫ f i)
    ⦃j₂ : ι'⦄ (a₂ : Z ⟶ X' j₂) (fac₂ : a₂ ≫ f' j₂ = q ≫ f i) :
    mor w φ q a₁ fac₁ = mor w φ q a₂ fac₂ := by
  sorry

noncomputable def familyOfElements (i : ι) :
    Presieve.FamilyOfElements (presheafHom F (D₁.obj i) (D₂.obj i)) (sieve f f' i).arrows :=
  fun Z q hq ↦
    mor w φ _ _ (sieve.fac (f := f) (f' := f') (q := Z.hom) (by
      convert hq
      ext
      simpa using (Over.w q).symm))

lemma familyOfElements_eq {i : ι} {Z : Over (X i)} (g : Z ⟶ Over.mk (𝟙 (X i)))
    ⦃j : ι'⦄ (a : Z.left ⟶ X' j) (fac : a ≫ f' j = Z.hom ≫ f i) :
    familyOfElements w φ i g (by
      rw [show g = Over.homMk Z.hom by ext; simpa using Over.w g]
      exact mem_sieve _ _ fac) = mor w φ _ _ fac :=
  mor_unique _ _ _ _ _ _ _

lemma _root_.CategoryTheory.Over.homMk_surjective {S : C} {X Y : Over S} (f : X ⟶ Y) :
    ∃ (g : X.left ⟶ Y.left) (hg : g ≫ Y.hom = X.hom), f = Over.homMk g :=
  ⟨f.left, by simp⟩

lemma compatible_familyOfElements (i : ι) :
    (familyOfElements w φ i).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
  obtain rfl : f₁ = Over.homMk Y₁.hom := by ext; simpa using Over.w f₁
  obtain rfl : f₂ = Over.homMk Y₂.hom := by ext; simpa using Over.w f₂
  obtain ⟨g₁, hg₁, rfl⟩ := Over.homMk_surjective g₁
  obtain ⟨g₂, hg₂, rfl⟩ := Over.homMk_surjective g₂
  obtain ⟨_, a₁, _, ⟨j₁⟩, fac₁⟩ := h₁
  obtain ⟨_, a₂, _, ⟨j₂⟩, fac₂⟩ := h₂
  dsimp at a₁ a₂ fac₁ fac₂
  rw [familyOfElements_eq _ _ _ _ fac₁, familyOfElements_eq _ _ _ _ fac₂,
    ← mor_precomp w φ Y₁.hom a₁ fac₁ _ _ hg₁ _ rfl,
    ← mor_precomp w φ Y₂.hom a₂ fac₂ _ _ hg₂ _ rfl]
  apply mor_unique

include hf' in
noncomputable def hom (i : ι) : D₁.obj i ⟶ D₂.obj i := by
  refine F.presheafHomObjHomEquiv.symm
    (Presieve.IsSheafFor.amalgamate (Presieve.IsSheaf.isSheafFor _
    ((isSheaf_iff_isSheaf_of_type _ _).1 (IsPrestack.isSheaf J _ _)) _ ?_) _
    (compatible_familyOfElements w φ i))
  rw [J.mem_over_iff]
  refine J.superset_covering ?_ (J.pullback_stable (f i) hf')
  simp only [Sieve.generate_sieve]
  rintro Z g ⟨_, q, _, ⟨j⟩, fac⟩
  exact ⟨Over.mk g, Over.homMk g, 𝟙 _, ⟨_, q, _, ⟨j⟩, by simpa⟩, by simp⟩

end full_pullFunctor

include w hf' in
lemma full_pullFunctor :
    (pullFunctor F (f := f) (p := 𝟙 _) (f' := f') (p' := p') (by cat_disch)).Full where
  map_surjective {D₁ D₂} φ :=
    ⟨{ hom := fun i ↦ full_pullFunctor.hom w hf' φ i, comm := sorry }, by
      sorry⟩

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
