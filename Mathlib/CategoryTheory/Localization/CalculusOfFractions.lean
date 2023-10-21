import Mathlib.CategoryTheory.Localization.Opposite

namespace CategoryTheory

namespace Functor

lemma congr_map_conjugate {C D : Type _} [Category C] [Category D] {F₁ F₂ : C ⥤ D}
    (h : F₁ = F₂) {X Y : C} (f : X ⟶ Y) :
    F₁.map f = eqToHom (by congr) ≫ F₂.map f ≫ eqToHom (by symm; congr) := by
  subst h
  simp

end Functor

namespace MorphismProperty

variable {C D : Type _} [Category C] [Category D] (L : C ⥤ D) {W : MorphismProperty C}

structure HasLeftCalculusOfFractions.ToSq {X' X Y : C} (s : X ⟶ X') (hs : W s) (u : X ⟶ Y) where
  obj : C
  g : X' ⟶ obj
  s' : Y ⟶ obj
  hs' : W s'
  fac : u ≫ s' = s ≫ g

structure HasRightCalculusOfFractions.ToSq {X Y Y' : C} (s : Y' ⟶ Y) (hs : W s) (u : X ⟶ Y) where
  obj : C
  g : obj ⟶ Y'
  s' : obj ⟶ X
  hs' : W s'
  fac : s' ≫ u = g ≫ s

attribute [reassoc] HasLeftCalculusOfFractions.ToSq.fac
  HasRightCalculusOfFractions.ToSq.fac

variable (W)

class HasLeftCalculusOfFractions extends W.IsMultiplicative : Prop :=
  --multiplicative : W.IsMultiplicative := by infer_instance
  nonempty_toSq : ∀ ⦃X' X Y : C⦄ (s : X ⟶ X') (hs : W s) (u : X ⟶ Y),
    Nonempty (HasLeftCalculusOfFractions.ToSq s hs u)
  ext : ∀ ⦃X' X Y : C⦄ (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X) (_ : W s)
    (_ : s ≫ f₁ = s ≫ f₂), ∃ (Y' : C) (t : Y ⟶ Y') (_ : W t), f₁ ≫ t = f₂ ≫ t

class HasRightCalculusOfFractions extends W.IsMultiplicative : Prop :=
  --multiplicative : W.IsMultiplicative := by infer_instance
  nonempty_toSq : ∀ ⦃X Y Y' : C⦄ (s : Y' ⟶ Y) (hs : W s) (u : X ⟶ Y),
    Nonempty (HasRightCalculusOfFractions.ToSq s hs u)
  ext : ∀ ⦃X Y Y' : C⦄ (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y') (_ : W s)
    (_ : f₁ ≫ s = f₂ ≫ s), ∃ (X' : C) (t : X' ⟶ X) (_ : W t), t ≫ f₁ = t ≫ f₂

--attribute [instance] HasLeftCalculusOfFractions.multiplicative
--  HasRightCalculusOfFractions.multiplicative

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
    W.unop.HasRightCalculusOfFractions := by
  have : W.unop.IsMultiplicative := IsMultiplicative.unop W
  exact {
    nonempty_toSq := fun _ _ _ s hs u => ⟨by
      let h := HasLeftCalculusOfFractions.toSq s.op hs u.op
      exact ⟨_, h.g.unop, h.s'.unop, h.hs', Quiver.Hom.op_inj h.fac⟩⟩
    ext := fun _ _ _ f₁ f₂ s hs fac => by
      obtain ⟨X', t, ht, eq⟩ := HasLeftCalculusOfFractions.ext f₁.op f₂.op s.op hs
        (Quiver.Hom.unop_inj fac)
      exact ⟨_, t.unop, ht, Quiver.Hom.op_inj eq⟩ }

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
    W.unop.HasLeftCalculusOfFractions := by
  have : W.unop.IsMultiplicative := IsMultiplicative.unop W
  exact {
    nonempty_toSq := fun _ _ _ s hs u => ⟨by
      let h := HasRightCalculusOfFractions.toSq s.op hs u.op
      exact ⟨_, h.g.unop, h.s'.unop, h.hs', Quiver.Hom.op_inj h.fac⟩⟩
    ext := fun _ _ _ f₁ f₂ s hs fac => by
      obtain ⟨X', t, ht, eq⟩ := HasRightCalculusOfFractions.ext f₁.op f₂.op s.op hs
        (Quiver.Hom.unop_inj fac)
      exact ⟨_, t.unop, ht, Quiver.Hom.op_inj eq⟩ }

attribute [instance] HasLeftCalculusOfFractions.op HasRightCalculusOfFractions.op

namespace HasLeftCalculusOfFractions

structure Roof (X Y : C) :=
(Z : C)
(f : X ⟶ Z)
(s : Y ⟶ Z)
(hs : W s)

@[simps]
def Roof.ofHom [ContainsIdentities W] {X Y : C} (f : X ⟶ Y) : Roof W X Y :=
  ⟨Y, f, 𝟙 Y, W.id_mem Y⟩

variable {W}

@[simps]
def Roof.inv {X Y : C} (s : X ⟶ Y) (hs : W s) : Roof W Y X := ⟨Y, 𝟙 Y, s, hs⟩

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
  · rw [reassoc_of% fac]
  · rw [reassoc_of% hft, ← fac', reassoc_of% hfu]
  · rw [← reassoc_of% fac, ← reassoc_of% hsu, ← Category.assoc]
    exact W.comp_mem _ _ hu (W.comp_mem _ _ hv₅ hw)

end roofRel

variable [W.HasLeftCalculusOfFractions]

instance {X Y : C} : IsEquiv (Roof W X Y) (fun z₁ z₂ => roofRel z₁ z₂) where
  refl := roofRel.refl
  symm := fun _ _ => roofRel.symm
  trans := fun _ _ _ h₁₂ h₂₃ => roofRel.trans h₁₂ h₂₃

namespace Roof

def comp₀ {X Y Z : C} (z : Roof W X Y) (z' : Roof W Y Z)
    (sq : ToSq z.s z.hs z'.f) : Roof W X Z :=
  ⟨sq.obj, z.f ≫ sq.g, z'.s ≫ sq.s', W.comp_mem _ _ z'.hs sq.hs'⟩

lemma comp₀_rel {X Y Z : C} (z : Roof W X Y) (z' : Roof W Y Z)
    (sq sq' : ToSq z.s z.hs z'.f) : roofRel (z.comp₀ z' sq) (z.comp₀ z' sq') := by
  have H := toSq sq.s' sq.hs' sq'.s'
  have eq : z.s ≫ sq.g ≫ H.g = z.s ≫ sq'.g ≫ H.s' := by
    rw [← sq.fac_assoc, ← sq'.fac_assoc, H.fac]
  obtain ⟨Y, t, ht, fac⟩ := ext _ _ _ z.hs eq
  simp only [Category.assoc] at fac
  refine' ⟨Y, H.g ≫ t, H.s' ≫ t, _, _, _⟩
  · dsimp [comp₀]
    simp only [Category.assoc, H.fac_assoc]
  · dsimp [comp₀]
    simp only [Category.assoc, ← fac]
  · dsimp [comp₀]
    simp only [Category.assoc, ← H.fac_assoc]
    exact W.comp_mem _ _ z'.hs (W.comp_mem _ _ sq'.hs' (W.comp_mem _ _ H.hs' ht))

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

lemma Roof.ofHom_comp {X Y Z : C} (f : X ⟶ Y) (g : Roof W Y Z) :
    Roof.comp (Roof.ofHom W f) g = Quot.mk _ ⟨g.Z, f ≫ g.f, g.s, g.hs⟩ := by
  let sq : ToSq (𝟙 Y) (W.id_mem Y) g.f :=
    ⟨_, g.f, 𝟙 _, W.id_mem _, by simp⟩
  rw [Roof.comp_eq (Roof.ofHom W f) g sq]
  dsimp [comp₀]
  congr
  simp

variable (W)

lemma Roof.ofHom_comp_ofHom {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Roof.comp (Roof.ofHom W f) (Roof.ofHom W g) = Quot.mk _ (Roof.ofHom W (f ≫ g)) :=
  Roof.ofHom_comp _ _

variable {W}

noncomputable def Hom.comp {X Y Z : C} :
    Hom W X Y → Hom W Y Z → Hom W X Z := by
  refine' Quot.lift₂ (fun z z' => Roof.comp z z') _ _
  · rintro z₁₂ z₂₃ z₂₃' ⟨Y, t, t', hst, hft, ht⟩
    have sq := toSq z₁₂.s z₁₂.hs z₂₃.f
    have sq' := toSq z₁₂.s z₁₂.hs z₂₃'.f
    have H₀ := toSq sq.s' sq.hs' t
    have H₀' := toSq sq'.s' sq'.hs' t'
    have H₁ := toSq H₀.s' H₀.hs' H₀'.s'
    have eq : z₁₂.s ≫ sq.g ≫ H₀.g ≫ H₁.g = z₁₂.s ≫ sq'.g ≫ H₀'.g ≫ H₁.s' := by
      rw [← sq.fac_assoc, ← sq'.fac_assoc, ← H₀.fac_assoc, ← H₀'.fac_assoc,
        reassoc_of% hft, H₁.fac]
    obtain ⟨Z, u, hu, fac⟩ := ext _ _ _ z₁₂.hs eq
    simp only [Category.assoc] at fac
    dsimp
    rw [Roof.comp_eq _ _ sq, Roof.comp_eq _ _ sq']
    apply Quot.sound
    refine' ⟨Z, H₀.g ≫ H₁.g ≫ u, H₀'.g ≫ H₁.s' ≫ u, _, _, _⟩
    · simp only [Roof.comp₀, Category.assoc, ← H₀.fac_assoc, ← H₀'.fac_assoc,
        reassoc_of% hst, reassoc_of% H₁.fac]
    · simp only [Roof.comp₀, Category.assoc, fac]
    · simp only [Roof.comp₀, Category.assoc]
      rw [← H₀.fac_assoc, ← H₁.fac_assoc, ← Category.assoc]
      exact W.comp_mem _ _ ht
        (W.comp_mem _ _ H₀'.hs'
        (W.comp_mem _ _ H₁.hs' hu))
  · rintro z₁₂ z₁₂' z₂₃ ⟨Y, t, t', hst, hft, ht⟩
    have sq := toSq z₁₂.s z₁₂.hs z₂₃.f
    have sq' := toSq z₁₂'.s z₁₂'.hs z₂₃.f
    have H := toSq (z₁₂.s ≫ t) ht (z₂₃.f ≫ sq.s')
    have H' := toSq (z₁₂'.s ≫ t') (show W _ by rw [← hst]; exact ht) (z₂₃.f ≫ sq'.s')
    let z : Roof W X Z := ⟨H.obj, z₁₂.f ≫ t ≫ H.g, z₂₃.s ≫ sq.s' ≫ H.s',
      W.comp_mem _ _ z₂₃.hs (W.comp_mem _ _ sq.hs' H.hs')⟩
    let z' : Roof W X Z := ⟨H'.obj, z₁₂'.f ≫ t' ≫ H'.g, z₂₃.s ≫ sq'.s' ≫ H'.s',
      W.comp_mem _ _ z₂₃.hs (W.comp_mem _ _ sq'.hs' H'.hs')⟩
    dsimp
    rw [Roof.comp_eq _ _ sq, Roof.comp_eq _ _ sq']
    apply Quot.sound
    refine' roofRel.trans _ (roofRel.trans (_ : roofRel z z') (symm _))
    · have eq : z₁₂.s ≫ sq.g ≫ H.s' = z₁₂.s ≫ t ≫ H.g := by
        have h := H.fac
        simp only [Category.assoc] at h
        rw [← h, sq.fac_assoc]
      obtain ⟨Z, u, hu, fac⟩ := ext _ _ _ z₁₂.hs eq
      simp only [Category.assoc] at fac
      refine' ⟨Z, H.s' ≫ u, u, _, _, _⟩
      · simp only [Roof.comp₀, Category.assoc, Category.comp_id]
      · simp only [Roof.comp₀, Category.assoc, Category.comp_id, fac]
      · simp only [Roof.comp₀, Category.assoc]
        exact W.comp_mem _ _ z₂₃.hs
          (W.comp_mem _ _ sq.hs'
          (W.comp_mem _ _ H.hs' hu))
    · have T := toSq (sq.s' ≫ H.s') (W.comp_mem _ _ sq.hs' H.hs') (sq'.s' ≫ H'.s')
      have Tfac := T.fac
      have fac := H.fac
      have fac' := H'.fac
      simp only [Category.assoc] at Tfac fac fac'
      have eq : z₁₂.s ≫ t ≫ H.g ≫ T.g = z₁₂.s ≫ t ≫ H'.g ≫ T.s' := by
        simp only [reassoc_of% hst, ← reassoc_of% fac', Tfac, reassoc_of% fac]
      obtain ⟨Z, u, hu, fac''⟩ := ext _ _ _ z₁₂.hs eq
      simp only [Category.assoc] at fac''
      refine' ⟨Z, T.g ≫ u, T.s' ≫ u, _, _, _⟩
      · simp only [Category.assoc, reassoc_of% Tfac]
      · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, fac'', reassoc_of% hft]
      · simp only [Category.assoc, ← reassoc_of% Tfac]
        exact W.comp_mem _ _ z₂₃.hs
          (W.comp_mem _ _ sq'.hs'
          (W.comp_mem _ _ H'.hs'
          (W.comp_mem _ _ T.hs' hu)))
    · have eq : z₁₂'.s ≫ sq'.g ≫ H'.s' = z₁₂'.s ≫ t' ≫ H'.g := by
        have h := H'.fac
        simp only [Category.assoc] at h
        rw [← h, sq'.fac_assoc]
      obtain ⟨Z, u, hu, fac⟩ := ext _ _ _ z₁₂'.hs eq
      simp only [Category.assoc] at fac
      refine' ⟨Z, H'.s' ≫ u, u, _, _, _⟩
      · simp only [Roof.comp₀, Category.assoc, Category.comp_id]
      · simp only [Roof.comp₀, Category.assoc, Category.comp_id, fac]
      · simp only [Roof.comp₀, Category.assoc]
        exact W.comp_mem _ _ z₂₃.hs
          (W.comp_mem _ _ sq'.hs'
          (W.comp_mem _ _ H'.hs' hu))

lemma Hom.comp_eq {X Y Z : C} (z : Roof W X Y) (z' : Roof W Y Z)
    (sq : ToSq z.s z.hs z'.f) :
      Hom.comp (Quot.mk _ z) (Quot.mk _ z') =
        Quot.mk _ (Roof.comp₀ z z' sq) :=
  Roof.comp_eq _ _ _

-- the category `Localization W` that is constructed when `[HasLeftCalculusOfFractions W]` should
-- not be used: it is introduced only in order to prove the lemmas
-- `HasLeftCalculusOfFractions.fac` and `HasLeftCalculusOfFractions.map_eq_iff`
structure Localization (W : MorphismProperty C) :=
(obj : C)

namespace Localization

variable (W)

noncomputable instance : Category (Localization W) where
  Hom X Y := Hom W X.obj Y.obj
  id X := Quot.mk _ (Roof.ofHom _ (𝟙 X.obj))
  comp f g := Hom.comp f g
  id_comp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨f⟩
    dsimp [Hom.comp]
    let sq : ToSq (𝟙 X) (W.id_mem _) f.f :=
      ⟨f.Z, f.f, 𝟙 _, W.id_mem _, by simp⟩
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
  assoc := by
    rintro ⟨X₁⟩ ⟨X₂⟩ ⟨X₃⟩ ⟨X₄⟩ ⟨f₁₂ : Roof W X₁ X₂⟩
      ⟨f₂₃ : Roof W X₂ X₃⟩ ⟨f₃₄ : Roof W X₃ X₄⟩
    have sq₁₃ := toSq f₁₂.s f₁₂.hs f₂₃.f
    have sq₂₄ := toSq f₂₃.s f₂₃.hs f₃₄.f
    have sq := toSq sq₁₃.s' sq₁₃.hs' sq₂₄.g
    change Hom.comp (Hom.comp _ _) _ = Hom.comp _ (Hom.comp _ _)
    rw [Hom.comp_eq f₁₂ f₂₃ sq₁₃, Hom.comp_eq f₂₃ f₃₄ sq₂₄,
      Hom.comp_eq (Roof.comp₀ f₁₂ f₂₃ sq₁₃) f₃₄
      ⟨sq.obj, sq.g, sq₂₄.s' ≫ sq.s', W.comp_mem _ _ sq₂₄.hs' sq.hs', by
        simp only [Roof.comp₀, Category.assoc, sq₂₄.fac_assoc, sq.fac]⟩,
      Hom.comp_eq f₁₂ (Roof.comp₀ f₂₃ f₃₄ sq₂₄)
      ⟨sq.obj, sq₁₃.g ≫ sq.g, sq.s', sq.hs', by
        simp only [Roof.comp₀, Category.assoc, sq.fac, sq₁₃.fac_assoc]⟩]
    dsimp [Roof.comp₀]
    simp only [Category.assoc]

variable {W}

lemma comp_eq {X Y Z : Localization W} (f : X ⟶ Y) (g : Y ⟶ Z) :
  f ≫ g = Hom.comp f g := rfl

lemma id_eq (X : Localization W) :
  𝟙 X = Quot.mk _ (Roof.ofHom _ (𝟙 X.obj)) := rfl

def homOfRoof {X Y : C} (z : Roof W X Y) : (⟨X⟩ : Localization W) ⟶ ⟨Y⟩ :=
  Quot.mk _ z

variable (W)

def Q : C ⥤ Localization W where
  obj X := ⟨X⟩
  map f := homOfRoof (Roof.ofHom _ f)
  map_id _ := rfl
  map_comp f g := by
    symm
    apply Roof.ofHom_comp_ofHom W f g

variable {W}

noncomputable def Qinv {X Y : C} (s : X ⟶ Y) (hs : W s) : (Q W).obj Y ⟶ (Q W).obj X :=
  homOfRoof (Roof.inv s hs)

@[reassoc]
lemma Qinv_comp {X Y : C} (s : X ⟶ Y) (hs : W s) : Qinv s hs ≫ (Q W).map s = 𝟙 _ := by
  dsimp only [Qinv, comp_eq, id_eq]
  erw [Hom.comp_eq (Roof.inv s hs) (Roof.ofHom W s)
    ⟨Y, 𝟙 Y, 𝟙 Y, W.id_mem _, rfl⟩]
  simp [Roof.comp₀, Roof.ofHom]
  rfl

@[reassoc]
lemma comp_Qinv {X Y : C} (s : X ⟶ Y) (hs : W s) : (Q W).map s ≫ Qinv s hs = 𝟙 _ := by
  dsimp only [Qinv, comp_eq, id_eq]
  erw [Hom.comp_eq (Roof.ofHom W s) (Roof.inv s hs)
    ⟨Y, 𝟙 Y, 𝟙 Y, W.id_mem _, rfl⟩]
  dsimp [Roof.comp₀]
  apply Quot.sound
  refine' ⟨Y, 𝟙 Y, s, by simp, _ , by simpa using hs⟩
  · simp only [Category.comp_id, Roof.ofHom_Z, Roof.ofHom_f]
    erw [Category.id_comp]

noncomputable def iso {X Y : C} (s : X ⟶ Y) (hs : W s) : (Q W).obj X ≅ (Q W).obj Y where
  hom := (Q W).map s
  inv := Qinv s hs
  hom_inv_id := comp_Qinv s hs
  inv_hom_id := Qinv_comp s hs

lemma isIso_Qmap {X Y : C} (s : X ⟶ Y) (hs : W s) : IsIso ((Q W).map s) :=
  IsIso.of_iso (iso s hs)

instance {X Y : C} (s : X ⟶ Y) (hs : W s) : IsIso (Qinv s hs) :=
  IsIso.of_iso (iso s hs).symm

lemma facOfRoof {X Y : C} (z : Roof W X Y) :
    homOfRoof z = (Q W).map z.f ≫ Qinv z.s z.hs := by
  dsimp only [Qinv, comp_eq, homOfRoof, Q]
  erw [Hom.comp_eq (Roof.ofHom W z.f) (Roof.inv z.s z.hs)
    ⟨_, 𝟙 _, 𝟙 _, W.id_mem _, rfl⟩]
  dsimp [Roof.comp₀]
  apply Quot.sound
  exact ⟨z.Z, 𝟙 _, 𝟙 _, by simp, by simp, by simpa using z.hs⟩

variable (W)

lemma inverts : W.IsInvertedBy (Q W) := fun _ _ s hs => isIso_Qmap s hs

variable {E : Type _} [Category E]
variable {W}

noncomputable def lift (F : C ⥤ E) (hF : W.IsInvertedBy F) : Localization W ⥤ E := by
  haveI : ∀ {X Y : C} (z : Roof W X Y), IsIso (F.map z.s) := fun z => hF z.s z.hs
  exact
  { obj := fun ⟨X⟩ => F.obj X
    map := by
      rintro ⟨X⟩ ⟨Y⟩
      refine' Quot.lift (fun z => F.map z.f ≫ inv (F.map z.s))
        (fun z z' ⟨Z₃, t₁, t₂, hs, hf, hst⟩ => by
          dsimp
          haveI : IsIso (F.map (z.s ≫ t₁)) := hF _ hst
          haveI : IsIso (F.map (z'.s ≫ t₂)) := by
            rw [← hs]
            infer_instance
          have eq₁ : inv (F.map z.s) = F.map t₁ ≫ inv (F.map (z.s ≫ t₁)) := by
            rw [← cancel_mono (F.map (z.s ≫ t₁)), ← cancel_epi (F.map z.s),
              Category.assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id, Category.comp_id,
              F.map_comp]
          have eq₂ : inv (F.map z'.s) = F.map t₂ ≫ inv (F.map (z'.s ≫ t₂)) := by
            rw [← cancel_mono (F.map (z'.s ≫ t₂)), ← cancel_epi (F.map z'.s),
              Category.assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id, Category.comp_id,
              F.map_comp]
          rw [eq₁, ← F.map_comp_assoc, hf, F.map_comp, Category.assoc]
          simp only [hs, eq₂])
    map_id := by
      rintro ⟨X⟩
      dsimp [id_eq]
      simp
    map_comp := by
      rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f : Roof W X Y⟩ ⟨g : Roof W Y Z⟩
      dsimp
      have sq := toSq f.s f.hs g.f
      haveI : IsIso (F.map sq.s') := hF _ sq.hs'
      haveI : IsIso (F.map (g.s ≫ sq.s')) := by
        rw [F.map_comp]
        infer_instance
      rw [comp_eq, Hom.comp_eq f g sq]
      dsimp [Roof.comp₀]
      rw [← cancel_mono (F.map (g.s ≫ sq.s')), Category.assoc, Category.assoc, Category.assoc,
        Category.assoc, IsIso.inv_hom_id, Category.comp_id, F.map_comp g.s, IsIso.inv_hom_id_assoc,
        ← F.map_comp, sq.fac, F.map_comp f.s, IsIso.inv_hom_id_assoc, F.map_comp] }

lemma fac (F : C ⥤ E) (hF : W.IsInvertedBy F) : (Q W) ⋙ lift F hF = F :=
  Functor.ext (fun X => rfl) (fun X Y f => by simp [lift, Q, homOfRoof])

lemma uniq (F₁ F₂ : Localization W ⥤ E) (h : Q W ⋙ F₁ = Q W ⋙ F₂) : F₁ = F₂ := by
  refine' Functor.ext _ _
  · rintro ⟨X⟩
    exact Functor.congr_obj h X
  · rintro ⟨X⟩ ⟨Y⟩ ⟨f : Roof W X Y⟩
    have eq := facOfRoof f
    dsimp only [homOfRoof] at eq
    have eq' : F₂.map (Qinv f.s f.hs) = eqToHom (Functor.congr_obj h.symm f.Z) ≫
        F₁.map (Qinv f.s f.hs) ≫ eqToHom (Functor.congr_obj h Y) := by
      haveI : IsIso (((Q W) ⋙ F₂).map f.s) := by
        haveI : IsIso ((Q W).map f.s) := inverts _ _ f.hs
        dsimp
        infer_instance
      rw [← cancel_mono (((Q W) ⋙ F₂).map f.s)]
      erw [← F₂.map_comp, Qinv_comp, F₂.map_id, Functor.congr_map_conjugate h.symm f.s]
      simp only [Functor.comp_obj, Functor.comp_map, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, ← F₁.map_comp_assoc, Qinv_comp, F₁.map_id, eqToHom_trans]
    simp only [eq, Functor.map_comp]
    erw [Functor.congr_map_conjugate h f.f, eq']
    simp

variable (W E)

noncomputable def strictUniversalPropertyFixedTarget :
    Localization.StrictUniversalPropertyFixedTarget (Q W) W E where
  inverts := inverts W
  lift := lift
  fac := fac
  uniq := uniq

instance : (Q W).IsLocalization W :=
  Functor.IsLocalization.mk' _ _ (strictUniversalPropertyFixedTarget W _)
    (strictUniversalPropertyFixedTarget W _)

end Localization

variable [W.HasLeftCalculusOfFractions] [L.IsLocalization W]

instance {X Y : C} (z : Roof W X Y) : IsIso (L.map z.s) :=
  CategoryTheory.Localization.inverts L W _ z.hs

noncomputable def Roof.map {X Y : C} (z : Roof W X Y) (L : C ⥤ D) [L.IsLocalization W] :
    L.obj X ⟶ L.obj Y :=
  L.map z.f ≫ CategoryTheory.inv (L.map z.s)

variable (W)

@[simp]
lemma Roof.map_ofHom {X Y : C} (f : X ⟶ Y) (L : C ⥤ D) [L.IsLocalization W] :
    (Roof.ofHom W f).map L = L.map f := by
  simp [Roof.map]

variable {W}

lemma Roof.map_eq {X Y : C} (z : Roof W X Y) (L : C ⥤ D) [L.IsLocalization W] :
  z.map L = (Localization.compUniqFunctor (HasLeftCalculusOfFractions.Localization.Q W) L W).inv.app _ ≫
    ((CategoryTheory.Localization.uniq _ L W).functor.map (Localization.homOfRoof z)) ≫
    ((Localization.compUniqFunctor _ _ W)).hom.app _  := by
  let E := CategoryTheory.Localization.uniq (HasLeftCalculusOfFractions.Localization.Q W) L W
  let e : Localization.Q W ⋙ E.functor ≅ L := Localization.compUniqFunctor _ _ W
  change L.map z.f ≫ _ = e.inv.app X ≫ E.functor.map (Localization.homOfRoof z) ≫ e.hom.app Y
  rw [← cancel_mono (L.map z.s), Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    ← cancel_epi (e.hom.app X), Category.assoc, Category.assoc, Iso.hom_inv_id_app_assoc,
    Localization.facOfRoof, E.functor.map_comp, Category.assoc, ← e.hom.naturality z.s,
    Functor.comp_map, ← E.functor.map_comp_assoc _ ((Localization.Q W).map z.s),
    Localization.Qinv_comp, E.functor.map_id, Category.id_comp]
  exact (e.hom.naturality z.f).symm

variable (W)

lemma fac' {X Y : C} (f : L.obj X ⟶ L.obj Y) :
    ∃ (z : Roof W X Y), f = z.map L := by
  let E := CategoryTheory.Localization.uniq
    (HasLeftCalculusOfFractions.Localization.Q W) L W
  let e : _ ⋙ E.functor ≅ L := Localization.compUniqFunctor _ _ _
  obtain ⟨f', rfl⟩ : ∃ (f' : E.functor.obj ⟨X⟩ ⟶ E.functor.obj ⟨Y⟩),
      f = e.inv.app _ ≫ f' ≫ e.hom.app _ :=
    ⟨e.hom.app _ ≫ f ≫ e.inv.app _, by simp⟩
  obtain ⟨⟨z : Roof W X Y⟩,
    hz : E.functor.map (Localization.homOfRoof z) = _⟩ := E.functor.map_surjective f'
  exact ⟨z, by simp only [← hz, Roof.map_eq]⟩

lemma fac {X Y : C} (f : L.obj X ⟶ L.obj Y) :
  ∃ (Z : C) (g : X ⟶ Z) (s : Y ⟶ Z) (hs : W s),
    f = L.map g ≫ (Localization.isoOfHom L W s hs).inv := by
  obtain ⟨z, hz⟩ := fac' L W f
  exact ⟨_, z.f, z.s, z.hs, hz⟩

lemma map_eq_iff' {X Y : C} (z₁ z₂ : Roof W X Y) :
    z₁.map L = z₂.map L ↔ roofRel z₁ z₂ := by
  have H : Localization.homOfRoof z₁ = Localization.homOfRoof z₂ ↔ roofRel z₁ z₂ := by
    constructor
    · intro h
      dsimp only [Localization.homOfRoof] at h
      rw [Quot.eq] at h
      induction' h with _ _ _ _ _ _ _ h₁ _ _ _ _ _ h₂ h₃
      · assumption
      · apply refl
      · exact h₁.symm
      · exact h₂.trans h₃
    · apply Quot.sound
  refine' Iff.trans _ H
  simp only [Roof.map_eq]
  constructor
  · intro h
    apply (CategoryTheory.Localization.uniq (Localization.Q W) L W).functor.map_injective
    simpa only [NatIso.cancel_natIso_inv_left, NatIso.cancel_natIso_hom_right
      (Localization.compUniqFunctor (Localization.Q W) L W)] using h
  · intro h
    rw [h]

lemma map_eq_iff {X Y : C} (f₁ f₂ : X ⟶ Y) :
    L.map f₁ = L.map f₂ ↔ ∃ (Z : C) (s : Y ⟶ Z) (_ : W s), f₁ ≫ s = f₂ ≫ s := by
  constructor
  · intro h
    have h' : (Roof.ofHom W f₁).map L = (Roof.ofHom W f₂).map L := by simpa using h
    rw [map_eq_iff'] at h'
    obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h'
    dsimp at t₁ t₂ hst hft ht
    simp only [Category.id_comp] at hst ht
    subst hst
    exact ⟨Z, t₁, ht, hft⟩
  · rintro ⟨Z, s, hs, fac⟩
    rw [← cancel_mono (Localization.isoOfHom L W s hs).hom]
    dsimp
    simp only [← L.map_comp, fac]

lemma exists_lift_arrow (f : Arrow D) : ∃ (g : Arrow C), Nonempty (f ≅ L.mapArrow.obj g) := by
  have : EssSurj L := Localization.essSurj L W
  let e₁ := L.objObjPreimageIso f.left
  let e₂ := L.objObjPreimageIso f.right
  let f' := e₁.hom ≫ f.hom ≫ e₂.inv
  obtain ⟨X, g, s, hs, eq⟩ := fac L W f'
  refine' ⟨Arrow.mk g, ⟨Arrow.isoMk e₁.symm (e₂.symm ≪≫ Localization.isoOfHom L W s hs) _⟩⟩
  dsimp
  simp only [← cancel_mono ((Localization.isoOfHom L W s hs).inv), Category.assoc, ← eq,
    Functor.id_obj, Iso.inv_hom_id_assoc]
  erw [(Localization.isoOfHom L W s hs).hom_inv_id, Category.comp_id]

noncomputable def liftMap₁ {X Y : D} (f : X ⟶ Y) : C :=
  (exists_lift_arrow L W (Arrow.mk f)).choose.left
noncomputable def liftMap₂ {X Y : D} (f : X ⟶ Y) : C :=
  (exists_lift_arrow L W (Arrow.mk f)).choose.right
noncomputable def liftMap {X Y : D} (f : X ⟶ Y) : liftMap₁ L W f ⟶ liftMap₂ L W f :=
  (exists_lift_arrow L W (Arrow.mk f)).choose.hom
noncomputable def mapLiftMapIso {X Y : D} (f : X ⟶ Y) :
  Arrow.mk f ≅ Arrow.mk (L.map (liftMap L W f)) :=
  (exists_lift_arrow L W (Arrow.mk f)).choose_spec.some
noncomputable def liftMapIso₁ {X Y : D} (f : X ⟶ Y) : X ≅ L.obj (liftMap₁ L W f) :=
  Arrow.leftFunc.mapIso (mapLiftMapIso L W f)
noncomputable def liftMapIso₂ {X Y : D} (f : X ⟶ Y) : Y ≅ L.obj (liftMap₂ L W f) :=
  Arrow.rightFunc.mapIso (mapLiftMapIso L W f)

lemma liftMap_fac {X Y : D} (f : X ⟶ Y) : f ≫ (liftMapIso₂ L W f).hom =
    (liftMapIso₁ L W f).hom ≫ L.map (liftMap L W f) :=
  (mapLiftMapIso L W f).hom.w.symm

lemma essSurj_mapArrow : EssSurj L.mapArrow := ⟨fun f =>
  ⟨Arrow.mk (liftMap L W f.hom), ⟨(mapLiftMapIso L W f.hom).symm⟩⟩⟩

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
  · constructor
    · apply Quiver.Hom.unop_inj
    · apply Quiver.Hom.op_inj
  · constructor
    · rintro ⟨Z, s, hs, fac⟩
      exact ⟨_, s.unop, hs, Quiver.Hom.op_inj fac⟩
    · rintro ⟨Z, s, hs, fac⟩
      exact ⟨_, s.op, hs, Quiver.Hom.unop_inj fac⟩

end HasRightCalculusOfFractions

end MorphismProperty

end CategoryTheory
