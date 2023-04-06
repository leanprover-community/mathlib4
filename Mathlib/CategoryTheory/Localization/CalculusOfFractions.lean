import Mathlib.CategoryTheory.Localization.Opposite

namespace CategoryTheory

namespace MorphismProperty

variable {C D : Type _} [Category C] [Category D] (L : C ⥤ D) {W : MorphismProperty C}

structure HasLeftCalculusOfFractions.ToSq {X' X Y : C} (s : X ⟶ X') (hs : W s) (u : X ⟶ Y) :=
(obj : C)
(g : X' ⟶ obj)
(s' : Y ⟶ obj)
(hs : W s')
(fac : u ≫ s' = s ≫ g)

structure HasRightCalculusOfFractions.ToSq {X Y Y' : C} (s : Y' ⟶ Y) (hs : W s) (u : X ⟶ Y) :=
(obj : C)
(g : obj ⟶ Y')
(s' : obj ⟶ X)
(hs : W s')
(fac : s' ≫ u = g ≫ s)

variable (W)

class HasLeftCalculusOfFractions : Prop :=
  multiplicative : W.IsMultiplicative := by infer_instance
  nonempty_toSq : ∀ ⦃X' X Y : C⦄ (s : X ⟶ X') (hs : W s) (u : X ⟶ Y),
    Nonempty (HasLeftCalculusOfFractions.ToSq s hs u)
  ext : ∀ ⦃X' X Y : C⦄ (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X) (_ : W s)
    (_ : s ≫ f₁ = s ≫ f₂), ∃ (Y' : C) (t : Y ⟶ Y') (_ : W t), f₁ ≫ t = f₂ ≫ t

class HasRightCalculusOfFractions : Prop :=
  multiplicative : W.IsMultiplicative := by infer_instance
  nonempty_toSq : ∀ ⦃X Y Y' : C⦄ (s : Y' ⟶ Y) (hs : W s) (u : X ⟶ Y),
    Nonempty (HasRightCalculusOfFractions.ToSq s hs u)
  ext : ∀ ⦃X Y Y' : C⦄ (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y') (_ : W s)
    (_ : f₁ ≫ s = f₂ ≫ s), ∃ (X' : C) (t : X' ⟶ X) (_ : W t), t ≫ f₁ = t ≫ f₂

attribute [instance] HasLeftCalculusOfFractions.multiplicative
  HasRightCalculusOfFractions.multiplicative

variable {W}

noncomputable def HasLeftCalculusOfFractions.toSq {X' X Y : C} (s : X ⟶ X') (hs : W s) (u : X ⟶ Y)
    [HasLeftCalculusOfFractions W] : HasLeftCalculusOfFractions.ToSq s hs u :=
  (HasLeftCalculusOfFractions.nonempty_toSq s hs u).some

noncomputable def HasRightCalculusOfFractions.toSq {X Y Y' : C} (s : Y' ⟶ Y) (hs : W s) (u : X ⟶ Y)
    [HasRightCalculusOfFractions W] : HasRightCalculusOfFractions.ToSq s hs u :=
  (HasRightCalculusOfFractions.nonempty_toSq s hs u).some

variable (W)

lemma HasLeftCalculusOfFractions.op [HasLeftCalculusOfFractions W] :
    W.op.HasRightCalculusOfFractions where
  nonempty_toSq := fun _ _ _ s hs u => ⟨by
    let h := HasLeftCalculusOfFractions.toSq s.unop hs u.unop
    exact ⟨_, h.g.op, h.s'.op, h.hs, Quiver.Hom.unop_inj h.fac⟩⟩
  ext := fun _ _ _ f₁ f₂ s hs fac => by
    obtain ⟨X', t, ht, eq⟩ := HasLeftCalculusOfFractions.ext f₁.unop f₂.unop s.unop hs
      (Quiver.Hom.op_inj fac)
    exact ⟨_, t.op, ht, Quiver.Hom.unop_inj eq⟩

lemma HasLeftCalculusOfFractions.unop (W : MorphismProperty Cᵒᵖ) [HasLeftCalculusOfFractions W] :
    W.unop.HasRightCalculusOfFractions where
  multiplicative := IsMultiplicative.unop W
  nonempty_toSq := fun _ _ _ s hs u => ⟨by
    let h := HasLeftCalculusOfFractions.toSq s.op hs u.op
    exact ⟨_, h.g.unop, h.s'.unop, h.hs, Quiver.Hom.op_inj h.fac⟩⟩
  ext := fun _ _ _ f₁ f₂ s hs fac => by
    obtain ⟨X', t, ht, eq⟩ := HasLeftCalculusOfFractions.ext f₁.op f₂.op s.op hs
      (Quiver.Hom.unop_inj fac)
    exact ⟨_, t.unop, ht, Quiver.Hom.op_inj eq⟩

lemma HasRightCalculusOfFractions.op [HasRightCalculusOfFractions W] :
    W.op.HasLeftCalculusOfFractions where
  nonempty_toSq := fun _ _ _ s hs u => ⟨by
    let h := HasRightCalculusOfFractions.toSq s.unop hs u.unop
    exact ⟨_, h.g.op, h.s'.op, h.hs, Quiver.Hom.unop_inj h.fac⟩⟩
  ext := fun _ _ _ f₁ f₂ s hs fac => by
    obtain ⟨X', t, ht, eq⟩ := HasRightCalculusOfFractions.ext f₁.unop f₂.unop s.unop hs
      (Quiver.Hom.op_inj fac)
    exact ⟨_, t.op, ht, Quiver.Hom.unop_inj eq⟩

lemma HasRightCalculusOfFractions.unop (W : MorphismProperty Cᵒᵖ) [HasRightCalculusOfFractions W] :
    W.unop.HasLeftCalculusOfFractions where
  multiplicative := IsMultiplicative.unop W
  nonempty_toSq := fun _ _ _ s hs u => ⟨by
    let h := HasRightCalculusOfFractions.toSq s.op hs u.op
    exact ⟨_, h.g.unop, h.s'.unop, h.hs, Quiver.Hom.op_inj h.fac⟩⟩
  ext := fun _ _ _ f₁ f₂ s hs fac => by
    obtain ⟨X', t, ht, eq⟩ := HasRightCalculusOfFractions.ext f₁.op f₂.op s.op hs
      (Quiver.Hom.unop_inj fac)
    exact ⟨_, t.unop, ht, Quiver.Hom.op_inj eq⟩

attribute [instance] HasLeftCalculusOfFractions.op HasRightCalculusOfFractions.op

namespace HasLeftCalculusOfFractions

variable [W.HasLeftCalculusOfFractions] [L.IsLocalization W]

lemma fac {X Y : C} (f : L.obj X ⟶ L.obj Y) :
  ∃ (Z : C) (g : X ⟶ Z) (s : Y ⟶ Z) (hs : W s),
    f = L.map g ≫ (Localization.isoOfHom L W s hs).inv := by
  have h : HasLeftCalculusOfFractions W := inferInstance
  sorry

lemma map_eq_iff {X Y : C} (f₁ f₂ : X ⟶ Y) :
    L.map f₁ = L.map f₂ ↔ ∃ (Z : C) (s : Y ⟶ Z) (hs : W s), f₁ ≫ s = f₂ ≫ s := by
  have h : HasLeftCalculusOfFractions W := inferInstance
  constructor
  . sorry
  . rintro ⟨Z, s, hs, fac⟩
    rw [← cancel_mono (Localization.isoOfHom L W s hs).hom]
    dsimp
    simp only [← L.map_comp, fac]
end HasLeftCalculusOfFractions

namespace HasRightCalculusOfFractions

variable [W.HasRightCalculusOfFractions] [L.IsLocalization W]

lemma fac {X Y : C} (f : L.obj X ⟶ L.obj Y) :
  ∃ (Z : C) (g : Z ⟶ Y) (s : Z ⟶ X) (hs : W s),
    f = (Localization.isoOfHom L W s hs).inv ≫ L.map g := by
  obtain ⟨Z, g, s, hs, fac⟩ := HasLeftCalculusOfFractions.fac L.op W.op f.op
  refine' ⟨_, g.unop, s.unop, hs, Quiver.Hom.op_inj _⟩
  rw [← cancel_mono (Localization.isoOfHom (Functor.op L) (MorphismProperty.op W) s hs).hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id] at fac
  rw [← cancel_mono (Localization.isoOfHom L W (Quiver.Hom.unop s) hs).hom.op, ← op_comp, ← op_comp,
    Iso.hom_inv_id_assoc, op_comp]
  exact fac

lemma map_eq_iff {X Y : C} (f₁ f₂ : X ⟶ Y) :
    L.map f₁ = L.map f₂ ↔ ∃ (Z : C) (s : Z ⟶ X) (_ : W s), s ≫ f₁ = s ≫ f₂ := by
  refine' Iff.trans _ ((HasLeftCalculusOfFractions.map_eq_iff L.op W.op f₁.op f₂.op).trans _)
  . constructor
    . apply Quiver.Hom.unop_inj
    . apply Quiver.Hom.op_inj
  . constructor
    . rintro ⟨Z, s, hs, fac⟩
      exact ⟨_, s.unop, hs, Quiver.Hom.op_inj fac⟩
    . rintro ⟨Z, s, hs, fac⟩
      exact ⟨_, s.op, hs, Quiver.Hom.unop_inj fac⟩

end HasRightCalculusOfFractions

end MorphismProperty

end CategoryTheory
