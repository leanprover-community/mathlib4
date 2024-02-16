import Mathlib.CategoryTheory.MorphismProperty

universe w v u

namespace CategoryTheory

open Category Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

def IsStableUnderColimitsOfShape (J : Type _) [Category J] : Prop :=
  ∀ (X₁ X₂ : J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f),
      W (h₁.desc (Cocone.mk _ (f ≫ c₂.ι)))

variable {W}

lemma IsStableUnderColimitsOfShape.lim_map {J : Type _} [Category J]
  (hW : W.IsStableUnderColimitsOfShape J) {X Y : J ⥤ C}
  (f : X ⟶ Y) [HasColimitsOfShape J C]
  (hf : W.functorCategory _ f) : W (colim.map f) :=
  hW X Y _ _ (colimit.isColimit X) (colimit.isColimit Y) f hf

variable (W)

abbrev IsStableUnderCoproductsOfShape (J : Type _) :=
  W.IsStableUnderColimitsOfShape (Discrete J)

def IsStableUnderCoproductOfSize := ∀ (J : Type w), W.IsStableUnderCoproductsOfShape J

abbrev IsStableUnderCoproducts := IsStableUnderCoproductOfSize.{v} W

structure IsStableUnderRetract : Prop where
  mem_of_retract' (f g : Arrow C) (i : f ⟶ g) (p : g ⟶ f)
    (hip : i ≫ p = 𝟙 f) (hg : W g.hom) : W f.hom

variable (C) in
lemma IsStableUnderRetract.monomorphisms : (monomorphisms C).IsStableUnderRetract where
  mem_of_retract' f g i p hip hg :=
    { right_cancellation := fun a b h => by
        have : Mono g.hom := hg
        have : a ≫ i.left = b ≫ i.left := by
          rw [← cancel_mono g.hom]
          simp [reassoc_of% h]
        replace this := this =≫ p.left
        replace hip : i.left ≫ p.left = 𝟙 _ := by
          rw [← Arrow.comp_left, hip, Arrow.id_left]
        simpa only [Functor.id_obj, assoc, hip, comp_id] using this }

variable {W} in
lemma IsStableUnderRetract.mem_of_retract (hW : W.IsStableUnderRetract)
    {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (i : Arrow.mk f ⟶ Arrow.mk f') (p : Arrow.mk f' ⟶ Arrow.mk f) (hip: i ≫ p = 𝟙 _)
    (hf' : W f') : W f :=
  hW.mem_of_retract' _ _ i p hip hf'

structure IsStableUnderInfiniteComposition : Prop where
  mem (X : ℕ ⥤ C) (hX : ∀ (n : ℕ), W (X.map (homOfLE (Nat.le_add_right n 1))))
    (c : Cocone X) (hc : IsColimit c) : W (c.ι.app 0)

class IsGabrielZismanSaturated [W.IsMultiplicative] where
  subset_mono : W ⊆ monomorphisms C
  iso_subset : isomorphisms C ⊆ W
  stableUnderCobaseChange : W.StableUnderCobaseChange
  isStableUnderRetract : W.IsStableUnderRetract
  isStableUnderCoproducts : W.IsStableUnderCoproducts
  isStableUnderInfiniteComposition : W.IsStableUnderInfiniteComposition

inductive gabrielZismanSaturation : MorphismProperty C :=
  | of_mem {X Y : C} (f : X ⟶ Y) (hf : W f) : gabrielZismanSaturation f
  | of_iso {X Y : C} (e : X ≅ Y) : gabrielZismanSaturation e.hom
  | of_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : gabrielZismanSaturation f)
      (hg : gabrielZismanSaturation g) : gabrielZismanSaturation (f ≫ g)
  | of_isPushout {A A' B B' : C} (f : A ⟶ A') (g : A ⟶ B) (f' : B ⟶ B') (g' : A' ⟶ B')
      (h : IsPushout g f f' g') (hf : gabrielZismanSaturation f) : gabrielZismanSaturation f'
  | of_retract {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') (i : Arrow.mk f ⟶ Arrow.mk f')
      (p : Arrow.mk f' ⟶ Arrow.mk f) (hip : i ≫ p = 𝟙 _) (hf' : gabrielZismanSaturation f') :
      gabrielZismanSaturation f
  | of_infinite_composition (X : ℕ ⥤ C)
      (hX : ∀ (n : ℕ), gabrielZismanSaturation (X.map (homOfLE (Nat.le_add_right n 1))))
      (c : Cocone X) (hc : IsColimit c) : gabrielZismanSaturation (c.ι.app 0)
  | of_coproduct {J : Type v} (X₁ X₂ : Discrete J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂)
      (_ : gabrielZismanSaturation.functorCategory (Discrete J) f):
      gabrielZismanSaturation (h₁.desc (Cocone.mk _ (f ≫ c₂.ι)))

instance : W.gabrielZismanSaturation.ContainsIdentities where
  id_mem' X := gabrielZismanSaturation.of_iso (Iso.refl X)

instance : W.gabrielZismanSaturation.IsMultiplicative where
  stableUnderComposition _ _ _ _ _ hf hg :=
    gabrielZismanSaturation.of_comp _ _ hf hg

section

instance : ContainsIdentities (monomorphisms C) where
  id_mem' _ := monomorphisms.infer_property _

instance : IsMultiplicative (monomorphisms C) where
  stableUnderComposition _ _ _ f g hf hg := by
    have : Mono f := hf
    have : Mono g := hg
    exact mono_comp f g

lemma IsGabrielZismanSaturated.monomorphisms
    (hmono₁ : (monomorphisms C).StableUnderCobaseChange)
    (hmono₂ : (monomorphisms C).IsStableUnderCoproducts)
    (hmono₃ : (monomorphisms C).IsStableUnderInfiniteComposition) :
    IsGabrielZismanSaturated (monomorphisms C) where
  subset_mono _ _ _ := id
  iso_subset _ _ f hf := by
    have : IsIso f := hf
    apply monomorphisms.infer_property
  stableUnderCobaseChange := hmono₁
  isStableUnderRetract := IsStableUnderRetract.monomorphisms C
  isStableUnderCoproducts := hmono₂
  isStableUnderInfiniteComposition := hmono₃

end

lemma subset_gabrielZismanSaturation : W ⊆ W.gabrielZismanSaturation :=
  fun _ _ _ hf => gabrielZismanSaturation.of_mem _ hf

lemma gabrielZismanSaturation_subset_iff (W₁ W₂ : MorphismProperty C) [W₂.IsMultiplicative]
    [W₂.IsGabrielZismanSaturated] :
    W₁.gabrielZismanSaturation ⊆ W₂ ↔ W₁ ⊆ W₂ := by
  constructor
  · intro h X Y f hf
    exact h _ (subset_gabrielZismanSaturation _ _ hf)
  · intro h X Y f hf
    induction hf with
      | of_mem f hf => exact h _ hf
      | of_iso f => exact IsGabrielZismanSaturated.iso_subset _ (isomorphisms.infer_property _)
      | of_comp f g _ _ hf hg => exact W₂.comp_mem _ _ hf hg
      | of_isPushout f g f' g' h _ hf =>
          exact IsGabrielZismanSaturated.stableUnderCobaseChange h hf
      | of_retract f f' i p hip _ h =>
          exact IsGabrielZismanSaturated.isStableUnderRetract.mem_of_retract f f' i p hip h
      | of_infinite_composition X _ c hc h =>
          exact IsGabrielZismanSaturated.isStableUnderInfiniteComposition.mem X h c hc
      | of_coproduct X₁ X₂ c₁ c₂ h₁ h₂ f _ h =>
          exact IsGabrielZismanSaturated.isStableUnderCoproducts _ X₁ X₂ c₁ c₂ h₁ h₂ f h

lemma gabrielZismanSaturation_isGabrielZismanSaturated
    (hW : W ⊆ monomorphisms C)
    [(monomorphisms C).IsGabrielZismanSaturated] :
    (W.gabrielZismanSaturation).IsGabrielZismanSaturated where
  subset_mono := by simpa only [gabrielZismanSaturation_subset_iff] using hW
  iso_subset _ _ f hf := by
    have : IsIso f := hf
    exact gabrielZismanSaturation.of_iso (asIso f)
  stableUnderCobaseChange _ _ _ _ f g f' g' h hf :=
    gabrielZismanSaturation.of_isPushout _ _ _ _ h hf
  isStableUnderRetract :=
    ⟨fun f g i p hip hg => gabrielZismanSaturation.of_retract _ _ _ _ hip hg⟩
  isStableUnderCoproducts J := gabrielZismanSaturation.of_coproduct
  isStableUnderInfiniteComposition :=
    ⟨gabrielZismanSaturation.of_infinite_composition⟩

end MorphismProperty

end CategoryTheory
