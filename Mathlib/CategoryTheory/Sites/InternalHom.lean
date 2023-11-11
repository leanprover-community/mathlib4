import Mathlib.CategoryTheory.Sites.Over

namespace CategoryTheory

open Category

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {A : Type*} [Category A]

section

variable {I : Type*} {X : C} (Y : I → C) (f : ∀ i, Y i ⟶ X)

abbrev Sieve.ofArrows : Sieve X :=
    Sieve.generate (Presieve.ofArrows Y f)

lemma Sieve.mem_ofArrows_iff {W : C} (g : W ⟶ X) :
    Sieve.ofArrows Y f g ↔ ∃ (i : I) (a : W ⟶ Y i), g = a ≫ f i := by
  dsimp [Sieve.ofArrows]
  constructor
  · rintro ⟨T, a, b, ⟨i⟩, rfl⟩
    exact ⟨i, a, rfl⟩
  · rintro ⟨i, a, rfl⟩
    exact ⟨_, a, f i, ⟨i⟩, rfl⟩

end

namespace Presheaf

lemma IsSheaf.ext_of_arrows {F : Cᵒᵖ ⥤ A} (hF : IsSheaf J F) {I : Type*} {X : C}
    (Y : I → C) (f : ∀ i, Y i ⟶ X)
    (hf : Sieve.ofArrows Y f ∈ J X)
    {W : A} {a b : W ⟶ F.obj (Opposite.op X)}
    (h : ∀ (i : I), a ≫ F.map (f i).op = b ≫ F.map (f i).op) :
    a = b := by
  apply hF.hom_ext ⟨_, hf⟩
  rintro ⟨W, g, T, p, q, ⟨i⟩, rfl⟩
  dsimp
  simp only [Functor.map_comp, reassoc_of% (h i)]

section

variable (F G : Cᵒᵖ ⥤ A)

@[simps obj]
def internalHom : Cᵒᵖ ⥤ Type _ where
  obj X := (Over.forget X.unop).op ⋙ F ⟶ (Over.forget X.unop).op ⋙ G
  map f := whiskerLeft (Over.map f.unop).op
  map_id := by
    rintro ⟨X⟩
    dsimp
    ext φ ⟨Y⟩
    simpa [Over.mapId] using φ.naturality ((@Over.mapId _ _ X).hom.app Y).op
  map_comp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f : Y ⟶ X⟩ ⟨g : Z ⟶ Y⟩
    dsimp
    ext φ ⟨W⟩
    simpa [Over.mapComp] using φ.naturality ((Over.mapComp g f).hom.app W).op

lemma InternalHom.isAmalgamation_iff {X : C} (S : Sieve X) {T : Type _}
    (x : Presieve.FamilyOfElements (internalHom F G ⋙ coyoneda.obj (Opposite.op T)) S)
    (hx : x.Compatible) (y : T → (internalHom F G).obj ⟨X⟩) :
    x.IsAmalgamation y ↔ ∀ (t : T) (Y : C) (g : Y ⟶ X) (hg : S g),
      (y t).app ⟨Over.mk g⟩ = (x g hg t).app  ⟨Over.mk (𝟙 Y)⟩ := by
  constructor
  · intro h t Y g hg
    rw [← h g hg]
    dsimp [internalHom]
    congr
    simp
  · intro h Y g hg
    dsimp [internalHom] at y ⊢
    ext t ⟨W⟩
    dsimp
    refine' (h t W.left (W.hom ≫ g) (S.downward_closed hg _)).trans _
    dsimp
    have H := hx (𝟙 _) W.hom (S.downward_closed hg W.hom) hg (by simp)
    dsimp at H
    erw [Functor.map_id, comp_id] at H
    rw [H]
    dsimp [internalHom, Over.map, Comma.mapRight]
    congr
    cases W
    simp

/-lemma internalHom_isSheaf (hG : IsSheaf J G) : IsSheaf J (internalHom F G) := by
  intro T X S hS x hx
  apply exists_unique_of_exists_of_unique
  · sorry
  · intro y₁ y₂ hy₁ hy₂
    dsimp at y₁ y₂ ⊢
    ext (t : T) ⟨W⟩
    dsimp
    sorry-/

end

end Presheaf

namespace Sheaf


end Sheaf



end CategoryTheory
