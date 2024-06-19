/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions
import Mathlib.CategoryTheory.Localization.HasLocalization
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Logic.Equiv.TransferInstance

/-!
# The preadditive category structure on the localized category

In this file, it is shown that if `W : MorphismProperty C` has a left calculus
of fractions, and `C` is preadditive, then the localized category is preadditive,
and the localization functor is additive.

Let `L : C ⥤ D` be a localization functor for `W`. We first construct an abelian
group structure on `L.obj X ⟶ L.obj Y` for `X` and `Y` in `C`. The addition
is defined using representatives of two morphisms in `L` as left fractions with
the same denominator thanks to the lemmas in
`CategoryTheory.Localization.CalculusOfFractions.Fractions`.
As `L` is essentially surjective, we finally transport these abelian group structures
to `X' ⟶ Y'` for all `X'` and `Y'` in `D`.

Preadditive category instances are defined on the categories `W.Localization`
(and `W.Localization'`) under the assumption the `W` has a left calculus of fractions.
(It would be easy to deduce from the results in this file that if `W` has a right calculus
of fractions, then the localized category can also be equipped with
a preadditive structure, but only one of these two constructions can be made an instance!)

-/

namespace CategoryTheory

open MorphismProperty Preadditive

variable {C D : Type*} [Category C] [Category D] [Preadditive C] (L : C ⥤ D)
  {W : MorphismProperty C} [L.IsLocalization W] [W.HasLeftCalculusOfFractions]

namespace MorphismProperty

/-- The opposite of a left fraction. -/
abbrev LeftFraction.neg {X Y : C} (φ : W.LeftFraction X Y) :
    W.LeftFraction X Y where
  Y' := φ.Y'
  f := -φ.f
  s := φ.s
  hs := φ.hs

namespace LeftFraction₂

variable {X Y : C} (φ : W.LeftFraction₂ X Y)

/-- The sum of two left fractions with the same denominator. -/
abbrev add : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f + φ.f'
  s := φ.s
  hs := φ.hs

@[simp]
lemma symm_add : φ.symm.add = φ.add := by
  dsimp [add, symm]
  congr 1
  apply add_comm

end LeftFraction₂

end MorphismProperty

variable (W)

namespace Localization

namespace Preadditive

section ImplementationDetails

/-! The definitions in this section (like `neg'` and `add'`) should never be used
directly. These are auxiliary definitions in order to construct the preadditive
structure `Localization.preadditive` (which is made irreducible). The user
should only rely on the fact that the localization functor is additive, as this
completely determines the preadditive structure on the localized category when
there is a calculus of left fractions. -/

variable {X Y Z : C}
variable {L}

/-- The opposite of a map `L.obj X ⟶ L.obj Y` when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions. -/
noncomputable def neg' (f : L.obj X ⟶ L.obj Y) : L.obj X ⟶ L.obj Y :=
  (exists_leftFraction L W f).choose.neg.map L (inverts L W)

lemma neg'_eq (f : L.obj X ⟶ L.obj Y) (φ : W.LeftFraction X Y)
    (hφ : f = φ.map L (inverts L W)) :
    neg' W f = φ.neg.map L (inverts L W) := by
  obtain ⟨φ₀, rfl, hφ₀⟩ : ∃ (φ₀ : W.LeftFraction X Y)
    (_ : f = φ₀.map L (inverts L W)),
      neg' W f = φ₀.neg.map L (inverts L W) :=
    ⟨_, (exists_leftFraction L W f).choose_spec, rfl⟩
  rw [MorphismProperty.LeftFraction.map_eq_iff] at hφ
  obtain ⟨Y', t₁, t₂, hst, hft, ht⟩ := hφ
  have := inverts L W _ ht
  rw [← cancel_mono (L.map (φ₀.s ≫ t₁))]
  nth_rw 1 [L.map_comp]
  rw [hφ₀, hst, LeftFraction.map_comp_map_s_assoc, L.map_comp,
    LeftFraction.map_comp_map_s_assoc, ← L.map_comp, ← L.map_comp,
    neg_comp, neg_comp, hft]

/-- The addition of two maps `L.obj X ⟶ L.obj Y` when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions. -/
noncomputable def add' (f₁ f₂ : L.obj X ⟶ L.obj Y) : L.obj X ⟶ L.obj Y :=
  (exists_leftFraction₂ L W f₁ f₂).choose.add.map L (inverts L W)

lemma add'_eq (f₁ f₂ : L.obj X ⟶ L.obj Y) (φ : W.LeftFraction₂ X Y)
    (hφ₁ : f₁ = φ.fst.map L (inverts L W))
    (hφ₂ : f₂ = φ.snd.map L (inverts L W)) :
    add' W f₁ f₂ = φ.add.map L (inverts L W) := by
  obtain ⟨φ₀, rfl, rfl, hφ₀⟩ : ∃ (φ₀ : W.LeftFraction₂ X Y)
    (_ : f₁ = φ₀.fst.map L (inverts L W))
    (_ : f₂ = φ₀.snd.map L (inverts L W)),
    add' W f₁ f₂ = φ₀.add.map L (inverts L W) :=
    ⟨(exists_leftFraction₂ L W f₁ f₂).choose,
      (exists_leftFraction₂ L W f₁ f₂).choose_spec.1,
      (exists_leftFraction₂ L W f₁ f₂).choose_spec.2, rfl⟩
  obtain ⟨Z, t₁, t₂, hst, hft, hft', ht⟩ := (LeftFraction₂.map_eq_iff L W φ₀ φ).1 ⟨hφ₁, hφ₂⟩
  have := inverts L W _ ht
  rw [hφ₀, ← cancel_mono (L.map (φ₀.s ≫ t₁))]
  nth_rw 2 [hst]
  rw [L.map_comp, L.map_comp, LeftFraction.map_comp_map_s_assoc,
    LeftFraction.map_comp_map_s_assoc, ← L.map_comp, ← L.map_comp,
    add_comp, add_comp, hft, hft']

lemma add'_comm (f₁ f₂ : L.obj X ⟶ L.obj Y) :
    add' W f₁ f₂ = add' W f₂ f₁ := by
  obtain ⟨α, h₁, h₂⟩ := exists_leftFraction₂ L W f₁ f₂
  rw [add'_eq W f₁ f₂ α h₁ h₂, add'_eq W f₂ f₁ α.symm h₂ h₁, α.symm_add]

lemma add'_zero (f : L.obj X ⟶ L.obj Y) :
    add' W f (L.map 0) = f := by
  obtain ⟨α, hα⟩ := exists_leftFraction L W f
  rw [add'_eq W f (L.map 0) (LeftFraction₂.mk α.f 0 α.s α.hs) hα, hα]; swap
  · have := inverts L W _ α.hs
    rw [← cancel_mono (L.map α.s), ← L.map_comp, Limits.zero_comp,
      LeftFraction.map_comp_map_s]
  dsimp [LeftFraction₂.add]
  rw [add_zero]

lemma zero_add' (f : L.obj X ⟶ L.obj Y) :
    add' W (L.map 0) f = f := by
  rw [add'_comm, add'_zero]

lemma add'_left_neg' (f : L.obj X ⟶ L.obj Y) :
    add' W (neg' W f) f = L.map 0 := by
  obtain ⟨α, rfl⟩ := exists_leftFraction L W f
  have := inverts L W _ α.hs
  rw [add'_eq W _ _ (LeftFraction₂.mk (-α.f) α.f α.s α.hs) (neg'_eq W _ _ rfl) rfl]
  simp only [← cancel_mono (L.map α.s), LeftFraction.map_comp_map_s, ← L.map_comp,
    Limits.zero_comp, add_left_neg]

lemma add'_assoc (f₁ f₂ f₃ : L.obj X ⟶ L.obj Y) :
    add' W (add' W f₁ f₂) f₃ = add' W f₁ (add' W f₂ f₃) := by
  obtain ⟨α, h₁, h₂, h₃⟩ := exists_leftFraction₃ L W f₁ f₂ f₃
  rw [add'_eq W f₁ f₂ α.forgetThd h₁ h₂, add'_eq W f₂ f₃ α.forgetFst h₂ h₃,
    add'_eq W _ _ (LeftFraction₂.mk (α.f + α.f') α.f'' α.s α.hs) rfl h₃,
    add'_eq W _ _ (LeftFraction₂.mk α.f (α.f' + α.f'') α.s α.hs) h₁ rfl]
  dsimp [LeftFraction₂.add]
  rw [add_assoc]

@[reassoc (attr := simp)]
lemma add'_comp (f₁ f₂ : L.obj X ⟶ L.obj Y) (g : L.obj Y ⟶ L.obj Z) :
    add' W f₁ f₂ ≫ g = add' W (f₁ ≫ g) (f₂ ≫ g) := by
  obtain ⟨α, h₁, h₂⟩ := exists_leftFraction₂ L W f₁ f₂
  obtain ⟨β, hβ⟩ := exists_leftFraction L W g
  obtain ⟨γ, hγ⟩ := (RightFraction.mk _ α.hs β.f).exists_leftFraction
  dsimp at hγ
  rw [add'_eq W f₁ f₂ α h₁ h₂, add'_eq W (f₁ ≫ g) (f₂ ≫ g)
    (LeftFraction₂.mk (α.f ≫ γ.f) (α.f' ≫ γ.f) (β.s ≫ γ.s)
    (W.comp_mem _ _ β.hs γ.hs))]; rotate_left
  · rw [h₁, hβ]
    exact LeftFraction.map_comp_map_eq_map _ _ _ hγ _
  · rw [h₂, hβ]
    exact LeftFraction.map_comp_map_eq_map _ _ _ hγ _
  rw [hβ, LeftFraction.map_comp_map_eq_map _ _ γ hγ]
  dsimp [LeftFraction₂.add]
  rw [add_comp]

@[reassoc (attr := simp)]
lemma comp_add' (f : L.obj X ⟶ L.obj Y) (g₁ g₂ : L.obj Y ⟶ L.obj Z) :
    f ≫ add' W g₁ g₂ = add' W (f ≫ g₁) (f ≫ g₂) := by
  obtain ⟨α, hα⟩ := exists_leftFraction L W f
  obtain ⟨β, hβ₁, hβ₂⟩ := exists_leftFraction₂ L W g₁ g₂
  obtain ⟨γ, hγ₁, hγ₂⟩ := (RightFraction₂.mk _ α.hs β.f β.f').exists_leftFraction₂
  dsimp at hγ₁ hγ₂
  rw [add'_eq W g₁ g₂ β hβ₁ hβ₂, add'_eq W (f ≫ g₁) (f ≫ g₂)
    (LeftFraction₂.mk (α.f ≫ γ.f) (α.f ≫ γ.f') (β.s ≫ γ.s) (W.comp_mem _ _ β.hs γ.hs))
    (by simpa only [hα, hβ₁] using LeftFraction.map_comp_map_eq_map α β.fst γ.fst hγ₁ L)
    (by simpa only [hα, hβ₂] using LeftFraction.map_comp_map_eq_map α β.snd γ.snd hγ₂ L),
    hα, LeftFraction.map_comp_map_eq_map α β.add γ.add
      (by simp only [add_comp, hγ₁, hγ₂, comp_add])]
  dsimp [LeftFraction₂.add]
  rw [comp_add]

@[simp]
lemma add'_map (f₁ f₂ : X ⟶ Y) :
    add' W (L.map f₁) (L.map f₂) = L.map (f₁ + f₂) :=
  (add'_eq W (L.map f₁) (L.map f₂) (LeftFraction₂.mk f₁ f₂ (𝟙 _) (W.id_mem _))
    (LeftFraction.map_ofHom _ _ _ _).symm (LeftFraction.map_ofHom _ _ _ _).symm).trans
    (LeftFraction.map_ofHom _ _ _ _)

variable (L X Y)

/-- The abelian group structure on `L.obj X ⟶ L.obj Y` when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions. -/
noncomputable def addCommGroup' : AddCommGroup (L.obj X ⟶ L.obj Y) := by
  letI : Zero (L.obj X ⟶ L.obj Y) := ⟨L.map 0⟩
  letI : Add (L.obj X ⟶ L.obj Y) := ⟨add' W⟩
  letI : Neg (L.obj X ⟶ L.obj Y) := ⟨neg' W⟩
  exact
    { add_assoc := add'_assoc _
      add_zero := add'_zero _
      add_comm := add'_comm _
      zero_add := zero_add' _
      add_left_neg := add'_left_neg' _
      nsmul := nsmulRec
      zsmul := zsmulRec }

variable {X Y}

variable {L}
variable {X' Y' Z' : D} (eX : L.obj X ≅ X') (eY : L.obj Y ≅ Y') (eZ : L.obj Z ≅ Z')

/-- The bijection `(X' ⟶ Y') ≃ (L.obj X ⟶ L.obj Y)` induced by isomorphisms
`eX : L.obj X ≅ X'` and `eY : L.obj Y ≅ Y'`. -/
@[simps]
def homEquiv : (X' ⟶ Y') ≃ (L.obj X ⟶ L.obj Y) where
  toFun f := eX.hom ≫ f ≫ eY.inv
  invFun g := eX.inv ≫ g ≫ eY.hom
  left_inv _ := by simp
  right_inv _ := by simp

/-- The addition of morphisms in `D`, when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions. -/
noncomputable def add (f₁ f₂ : X' ⟶ Y') : X' ⟶ Y' :=
  (homEquiv eX eY).symm (add' W (homEquiv eX eY f₁) (homEquiv eX eY f₂))

@[reassoc]
lemma add_comp (f₁ f₂ : X' ⟶ Y') (g : Y' ⟶ Z') :
    add W eX eY f₁ f₂ ≫ g = add W eX eZ (f₁ ≫ g) (f₂ ≫ g) := by
  obtain ⟨f₁, rfl⟩ := (homEquiv eX eY).symm.surjective f₁
  obtain ⟨f₂, rfl⟩ := (homEquiv eX eY).symm.surjective f₂
  obtain ⟨g, rfl⟩ := (homEquiv eY eZ).symm.surjective g
  simp [add]

@[reassoc]
lemma comp_add (f : X' ⟶ Y') (g₁ g₂ : Y' ⟶ Z') :
    f ≫ add W eY eZ g₁ g₂ = add W eX eZ (f ≫ g₁) (f ≫ g₂) := by
  obtain ⟨f, rfl⟩ := (homEquiv eX eY).symm.surjective f
  obtain ⟨g₁, rfl⟩ := (homEquiv eY eZ).symm.surjective g₁
  obtain ⟨g₂, rfl⟩ := (homEquiv eY eZ).symm.surjective g₂
  simp [add]

lemma add_eq_add {X'' Y'' : C} (eX' : L.obj X'' ≅ X') (eY' : L.obj Y'' ≅ Y')
    (f₁ f₂ : X' ⟶ Y') :
    add W eX eY f₁ f₂ = add W eX' eY' f₁ f₂ := by
  have h₁ := comp_add W eX' eX eY (𝟙 _) f₁ f₂
  have h₂ := add_comp W eX' eY eY' f₁ f₂ (𝟙 _)
  simp only [Category.id_comp] at h₁
  simp only [Category.comp_id] at h₂
  rw [h₁, h₂]

variable (L X' Y') in
/-- The abelian group structure on morphisms in `D`, when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions. -/
noncomputable def addCommGroup : AddCommGroup (X' ⟶ Y') := by
  have := Localization.essSurj L W
  letI := addCommGroup' L W (L.objPreimage X') (L.objPreimage Y')
  exact Equiv.addCommGroup (homEquiv (L.objObjPreimageIso X') (L.objObjPreimageIso Y'))

lemma add_eq (f₁ f₂ : X' ⟶ Y') :
    letI := addCommGroup L W X' Y'
    f₁ + f₂ = add W eX eY f₁ f₂ := by
  apply add_eq_add

variable (L)

lemma map_add (f₁ f₂ : X ⟶ Y) :
    letI := addCommGroup L W (L.obj X) (L.obj Y)
    L.map (f₁ + f₂) = L.map f₁ + L.map f₂ := by
  rw [add_eq W (Iso.refl _) (Iso.refl _) (L.map f₁) (L.map f₂)]
  simp [add]

end ImplementationDetails

end Preadditive

/-- The preadditive structure on `D`, when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions. -/
noncomputable def preadditive : Preadditive D where
  homGroup := Preadditive.addCommGroup L W
  add_comp _ _ _ _ _ _ := by apply Preadditive.add_comp
  comp_add _ _ _ _ _ _ := by apply Preadditive.comp_add

lemma functor_additive :
    letI := preadditive L W
    L.Additive :=
  letI := preadditive L W
  ⟨by apply Preadditive.map_add⟩

attribute [irreducible] preadditive

noncomputable instance : Preadditive W.Localization := preadditive W.Q W

instance : W.Q.Additive := functor_additive W.Q W

variable [W.HasLocalization]

noncomputable instance : Preadditive W.Localization' := preadditive W.Q' W

instance : W.Q'.Additive := functor_additive W.Q' W

end Localization

end CategoryTheory
