import Mathlib.CategoryTheory.Localization.Opposite

namespace CategoryTheory

namespace MorphismProperty

variable {C D : Type _} [Category C] [Category D] (L : C ⥤ D) {W : MorphismProperty C}

structure HasLeftCalculusOfFractions.ToSq {X' X Y : C} (s : X ⟶ X') (hs : W s) (u : X ⟶ Y) :=
(obj : C)
(g : X' ⟶ obj)
(s' : Y ⟶ obj)
(hs' : W s')
(fac : u ≫ s' = s ≫ g)

structure HasRightCalculusOfFractions.ToSq {X Y Y' : C} (s : Y' ⟶ Y) (hs : W s) (u : X ⟶ Y) :=
(obj : C)
(g : obj ⟶ Y')
(s' : obj ⟶ X)
(hs' : W s')
(fac : s' ≫ u = g ≫ s)

attribute [reassoc] HasLeftCalculusOfFractions.ToSq.fac
  HasRightCalculusOfFractions.ToSq.fac

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
    exact ⟨_, h.g.op, h.s'.op, h.hs', Quiver.Hom.unop_inj h.fac⟩⟩
  ext := fun _ _ _ f₁ f₂ s hs fac => by
    obtain ⟨X', t, ht, eq⟩ := HasLeftCalculusOfFractions.ext f₁.unop f₂.unop s.unop hs
      (Quiver.Hom.op_inj fac)
    exact ⟨_, t.op, ht, Quiver.Hom.unop_inj eq⟩

lemma HasLeftCalculusOfFractions.unop (W : MorphismProperty Cᵒᵖ) [HasLeftCalculusOfFractions W] :
    W.unop.HasRightCalculusOfFractions where
  multiplicative := IsMultiplicative.unop W
  nonempty_toSq := fun _ _ _ s hs u => ⟨by
    let h := HasLeftCalculusOfFractions.toSq s.op hs u.op
    exact ⟨_, h.g.unop, h.s'.unop, h.hs', Quiver.Hom.op_inj h.fac⟩⟩
  ext := fun _ _ _ f₁ f₂ s hs fac => by
    obtain ⟨X', t, ht, eq⟩ := HasLeftCalculusOfFractions.ext f₁.op f₂.op s.op hs
      (Quiver.Hom.unop_inj fac)
    exact ⟨_, t.unop, ht, Quiver.Hom.op_inj eq⟩

lemma HasRightCalculusOfFractions.op [HasRightCalculusOfFractions W] :
    W.op.HasLeftCalculusOfFractions where
  nonempty_toSq := fun _ _ _ s hs u => ⟨by
    let h := HasRightCalculusOfFractions.toSq s.unop hs u.unop
    exact ⟨_, h.g.op, h.s'.op, h.hs', Quiver.Hom.unop_inj h.fac⟩⟩
  ext := fun _ _ _ f₁ f₂ s hs fac => by
    obtain ⟨X', t, ht, eq⟩ := HasRightCalculusOfFractions.ext f₁.unop f₂.unop s.unop hs
      (Quiver.Hom.op_inj fac)
    exact ⟨_, t.op, ht, Quiver.Hom.unop_inj eq⟩

lemma HasRightCalculusOfFractions.unop (W : MorphismProperty Cᵒᵖ) [HasRightCalculusOfFractions W] :
    W.unop.HasLeftCalculusOfFractions where
  multiplicative := IsMultiplicative.unop W
  nonempty_toSq := fun _ _ _ s hs u => ⟨by
    let h := HasRightCalculusOfFractions.toSq s.op hs u.op
    exact ⟨_, h.g.unop, h.s'.unop, h.hs', Quiver.Hom.op_inj h.fac⟩⟩
  ext := fun _ _ _ f₁ f₂ s hs fac => by
    obtain ⟨X', t, ht, eq⟩ := HasRightCalculusOfFractions.ext f₁.op f₂.op s.op hs
      (Quiver.Hom.unop_inj fac)
    exact ⟨_, t.unop, ht, Quiver.Hom.op_inj eq⟩

attribute [instance] HasLeftCalculusOfFractions.op HasRightCalculusOfFractions.op

namespace HasLeftCalculusOfFractions

section

structure Roof (X Y : C) :=
(Z : C)
(f : X ⟶ Z)
(s : Y ⟶ Z)
(hs : W s)

@[simps]
def Roof.ofHom [ContainsIdentities W] {X Y : C} (f : X ⟶ Y) : Roof W X Y :=
  ⟨Y, f, 𝟙 Y, ContainsIdentities.mem W Y⟩

variable {W}

def roofRel ⦃X Y : C⦄ (z₁ z₂ : Roof W X Y) : Prop :=
  ∃ (Z₃ : C)  (t₁ : z₁.Z ⟶ Z₃) (t₂ : z₂.Z ⟶ Z₃) (_ : z₁.s ≫ t₁ = z₂.s ≫ t₂)
    (_ : z₁.f ≫ t₁ = z₂.f ≫ t₂), W (z₁.s ≫ t₁)

namespace roofRel

lemma refl {X Y : C} (z : Roof W X Y) : roofRel z z :=
  ⟨z.Z, 𝟙 _, 𝟙 _, rfl, rfl, by simpa only [Category.comp_id] using z.hs⟩

lemma symm {X Y : C} {z₁ z₂ : Roof W X Y} (h : roofRel z₁ z₂) : roofRel z₂ z₁ := by
  obtain ⟨Z₃, t₁, t₂, hst, hft, ht⟩ := h
  exact ⟨Z₃, t₂, t₁, hst.symm, hft.symm, by simpa only [← hst] using ht⟩

lemma trans {X Y : C} {z₁ z₂ z₃ : Roof W X Y} (h₁₂ : roofRel z₁ z₂) (h₂₃ : roofRel z₂ z₃)
    [HasLeftCalculusOfFractions W] :
    roofRel z₁ z₃ := by
  obtain ⟨Z₄, t₁, t₂, hst, hft, ht⟩ := h₁₂
  obtain ⟨Z₅, u₂, u₃, hsu, hfu, hu⟩ := h₂₃
  obtain ⟨Z₆, v₄, v₅, hv₅, fac⟩ := toSq (z₁.s ≫ t₁) ht (z₃.s ≫ u₃)
  simp only [Category.assoc] at fac
  have eq : z₂.s ≫ u₂ ≫ v₅  = z₂.s ≫ t₂ ≫ v₄ := by
    simpa only [← reassoc_of% hsu, reassoc_of% hst] using fac
  obtain ⟨Z₇, w, hw, fac'⟩ := ext _ _ _ z₂.hs eq
  simp only [Category.assoc] at fac'
  refine' ⟨Z₇, t₁ ≫ v₄ ≫ w, u₃ ≫ v₅ ≫ w, _, _, _⟩
  . rw [reassoc_of% fac]
  . rw [reassoc_of% hft, ← fac', reassoc_of% hfu]
  . rw [← reassoc_of% fac, ← reassoc_of% hsu, ← Category.assoc]
    exact IsMultiplicative.comp _ _ _ hu (IsMultiplicative.comp _ _ _ hv₅ hw)

end roofRel

variable [W.HasLeftCalculusOfFractions]

instance {X Y : C} : IsEquiv (Roof W X Y) (fun z₁ z₂ => roofRel z₁ z₂) where
  refl := roofRel.refl
  symm := fun _ _ => roofRel.symm
  trans := fun _ _ _ h₁₂ h₂₃ => roofRel.trans h₁₂ h₂₃

namespace Roof

def comp₀ {X Y Z : C} (z : Roof W X Y) (z' : Roof W Y Z)
    (sq : ToSq z.s z.hs z'.f) : Roof W X Z := by
  refine' ⟨sq.obj, z.f ≫ sq.g, z'.s ≫ sq.s',
    IsMultiplicative.comp _ _ _ z'.hs sq.hs'⟩

lemma comp₀_rel {X Y Z : C} (z : Roof W X Y) (z' : Roof W Y Z)
    (sq sq' : ToSq z.s z.hs z'.f) : roofRel (z.comp₀ z' sq) (z.comp₀ z' sq') := by
  have H := toSq sq.s' sq.hs' sq'.s'
  have eq : z.s ≫ sq.g ≫ H.g = z.s ≫ sq'.g ≫ H.s' := by
    rw [← sq.fac_assoc, ← sq'.fac_assoc, H.fac]
  obtain ⟨Y, t, ht, fac⟩ := ext _ _ _ z.hs eq
  simp only [Category.assoc] at fac
  refine' ⟨Y, H.g ≫ t, H.s' ≫ t, _, _, _⟩
  . dsimp [comp₀]
    simp only [Category.assoc, H.fac_assoc]
  . dsimp [comp₀]
    simp only [Category.assoc, ← fac]
  . dsimp [comp₀]
    simp only [Category.assoc, ← H.fac_assoc]
    exact IsMultiplicative.comp _ _ _ z'.hs
      (IsMultiplicative.comp _ _ _ sq'.hs'
      (IsMultiplicative.comp _ _ _ H.hs' ht))

end Roof

variable (W)

def Hom (X Y : C) := Quot (fun (z₁ z₂ : Roof W X Y) => roofRel z₁ z₂)

variable {W}

noncomputable def Roof.comp {X Y Z : C} (z : Roof W X Y) (z' : Roof W Y Z) :
    Hom W X Z :=
  Quot.mk _ (z.comp₀ z' (toSq _ _ _ ))

lemma Roof.comp_eq {X Y Z : C} (z : Roof W X Y) (z' : Roof W Y Z)
    (sq : ToSq z.s z.hs z'.f) : z.comp z' = Quot.mk _ (z.comp₀ z' sq) :=
  Quot.sound (Roof.comp₀_rel z z' _ _)

noncomputable def Hom.comp {X Y Z : C} :
    Hom W X Y → Hom W Y Z → Hom W X Z := by
  refine' Quot.lift₂ (fun z z' => Roof.comp z z') _ _
  . sorry
  . sorry

lemma Hom.comp_eq {X Y Z : C} (z : Roof W X Y) (z' : Roof W Y Z)
    (sq : ToSq z.s z.hs z'.f) :
      Hom.comp (Quot.mk _ z) (Quot.mk _ z') =
        Quot.mk _ (Roof.comp₀ z z' sq) :=
  Roof.comp_eq _ _ _

structure Localization (W : MorphismProperty C) :=
(obj : C)

noncomputable instance : Category (Localization W) where
  Hom X Y := Hom W X.obj Y.obj
  id X := Quot.mk _ (Roof.ofHom _ (𝟙 X.obj))
  comp f g := Hom.comp f g
  id_comp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨f⟩
    dsimp [Hom.comp]
    let sq : ToSq (𝟙 X) (ContainsIdentities.mem W _) f.f :=
      ⟨f.Z, f.f, 𝟙 _, ContainsIdentities.mem W _, by simp⟩
    rw [Roof.comp_eq (Roof.ofHom _ (𝟙 X)) f sq]
    dsimp [Roof.comp₀]
    congr <;> simp
  comp_id := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨f⟩
    dsimp [Hom.comp]
    let sq : ToSq f.s f.hs (𝟙 Y) :=
      ⟨f.Z, 𝟙 _, f.s, f.hs, by simp⟩
    rw [Roof.comp_eq f (Roof.ofHom _ (𝟙 Y)) sq]
    dsimp [Roof.comp₀]
    congr <;> simp
  assoc := sorry

end

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
