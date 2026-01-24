/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# Localization with respect to a Serre class

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

variable [Abelian C]

namespace ObjectProperty

variable (P : ObjectProperty C) [P.IsSerreClass]

@[nolint unusedArguments]
structure SerreClassLocalization (P : ObjectProperty C) [P.IsSerreClass] : Type u where
  obj : C

namespace SerreClassLocalization

variable {P} (X Y Z T : P.SerreClassLocalization)

namespace Hom

structure DefDomain where
  {src : C}
  i : src ⟶ X.obj
  mono_i : Mono i := by infer_instance
  hi : P.isoModSerre i
  {tgt : C}
  p : Y.obj ⟶ tgt
  epi_p : Epi p := by infer_instance
  hp : P.isoModSerre p

namespace DefDomain

attribute [instance] mono_i epi_p

@[simps]
def top : DefDomain X Y where
  i := 𝟙 X.obj
  hi := MorphismProperty.id_mem _ _
  p := 𝟙 Y.obj
  hp := MorphismProperty.id_mem _ _

variable {X Y Z T} (d₁ d₂ d₃ : DefDomain X Y)

structure Hom where
  ι : d₁.src ⟶ d₂.src
  ι_i : ι ≫ d₂.i = d₁.i := by cat_disch
  π : d₂.tgt ⟶ d₁.tgt
  p_π : d₂.p ≫ π = d₁.p := by cat_disch

namespace Hom

attribute [reassoc (attr := simp)] ι_i p_π

@[simps]
def id (d : DefDomain X Y) : Hom d d where
  ι := 𝟙 _
  π := 𝟙 _

variable {d₁ d₂ d₃} in
@[simps]
def comp (φ : Hom d₁ d₂) (ψ : Hom d₂ d₃) : Hom d₁ d₃ where
  ι := φ.ι ≫ ψ.ι
  π := ψ.π ≫ φ.π

variable (φ : Hom d₁ d₂)

instance : Mono φ.ι := mono_of_mono_fac φ.ι_i

instance : Epi φ.π := epi_of_epi_fac φ.p_π

instance : Subsingleton (Hom d₁ d₂) where
  allEq φ ψ := by
    suffices φ.ι = ψ.ι ∧ φ.π = ψ.π by cases φ; cases ψ; aesop
    constructor
    · simp [← cancel_mono d₂.i]
    · simp [← cancel_epi d₂.p]

instance : Category (DefDomain X Y) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

instance : Quiver.IsThin (DefDomain X Y) :=
  fun d₁ d₂ ↦ inferInstanceAs (Subsingleton (Hom d₁ d₂))

end Hom

@[simp] lemma id_ι (d : DefDomain X Y) : Hom.ι (𝟙 d) = 𝟙 _ := rfl
@[simp] lemma id_π (d : DefDomain X Y) : Hom.π (𝟙 d) = 𝟙 _ := rfl

section

variable {d₁ d₂ d₃}

@[simp] lemma comp_ι (f : d₁ ⟶ d₂) (g : d₂ ⟶ d₃) : (f ≫ g).ι = f.ι ≫ g.ι := rfl
@[simp] lemma comp_π (f : d₁ ⟶ d₂) (g : d₂ ⟶ d₃) : (f ≫ g).π = g.π ≫ f.π := rfl

end

lemma exists_min :
    ∃ (d : DefDomain X Y), Nonempty (d ⟶ d₁) ∧ Nonempty (d ⟶ d₂) := by
  let d : DefDomain X Y :=
    { src := pullback d₁.i d₂.i
      i := pullback.fst _ _ ≫ d₁.i
      hi := MorphismProperty.comp_mem _ _ _
          (MorphismProperty.pullback_fst _ _ d₂.hi) d₁.hi
      tgt := pushout d₁.p d₂.p
      p := d₁.p ≫ pushout.inl _ _
      hp := MorphismProperty.comp_mem _ _ _ d₁.hp
          (MorphismProperty.pushout_inl _ _ d₂.hp) }
  exact ⟨d, ⟨{ ι := pullback.fst _ _, π := pushout.inl _ _ }⟩, ⟨
    { ι := pullback.snd _ _,
      ι_i := pullback.condition.symm
      π := pushout.inr _ _
      p_π := pushout.condition.symm }⟩⟩

structure CompStruct (d₁₂ : DefDomain X Y) (d₂₃ : DefDomain Y Z) (d₁₃ : DefDomain X Z) where
  ι : d₁₃.src ⟶ d₁₂.src
  ι_i : ι ≫ d₁₂.i = d₁₃.i := by cat_disch
  π : d₂₃.tgt ⟶ d₁₃.tgt
  p_π : d₂₃.p ≫ π = d₁₃.p := by cat_disch
  obj : C
  toObj : d₂₃.src ⟶ obj
  fromObj : obj ⟶ d₁₂.tgt
  fac : toObj ≫ fromObj = d₂₃.i ≫ d₁₂.p := by cat_disch
  epi_toObj : Epi toObj := by infer_instance
  mono_toObj : Mono toObj := by infer_instance

namespace CompStruct

variable {d₁₂ : DefDomain X Y} {d₂₃ : DefDomain Y Z} {d₁₃ : DefDomain X Z}
  (h : CompStruct d₁₂ d₂₃ d₁₃)

instance : Mono h.ι := mono_of_mono_fac h.ι_i

instance : Epi h.π := epi_of_epi_fac h.p_π

-- is this useful without additional conditions?
lemma nonempty (d₁₂ : DefDomain X Y) (d₂₃ : DefDomain Y Z) :
    ∃ (d₁₃ : DefDomain X Z), Nonempty (CompStruct d₁₂ d₂₃ d₁₃) :=
  ⟨{i := d₁₂.i
    hi := d₁₂.hi
    p := d₂₃.p
    hp := d₂₃.hp }, sorry⟩

end CompStruct

end DefDomain

variable {X Y} in
abbrev restrict {d₁ d₂ : DefDomain X Y} (φ : d₁ ⟶ d₂) (f : d₂.src ⟶ d₂.tgt) :
    d₁.src ⟶ d₁.tgt :=
  φ.ι ≫ f ≫ φ.π

end Hom

abbrev Hom' := Σ (d : Hom.DefDomain X Y), d.src ⟶ d.tgt

section

variable {X Y Z T}

abbrev Hom'.mk {d : Hom.DefDomain X Y} (φ : d.src ⟶ d.tgt) : Hom' X Y := ⟨d, φ⟩

lemma Hom'.mk_surjective (a : Hom' X Y) :
    ∃ (d : Hom.DefDomain X Y) (φ : d.src ⟶ d.tgt), a = .mk φ :=
  ⟨a.1, a.2, rfl⟩

end

inductive Hom'Rel : Hom' X Y → Hom' X Y → Prop
  | restrict (d₁ d₂ : Hom.DefDomain X Y) (φ : d₁ ⟶ d₂) (f : d₂.src ⟶ d₂.tgt) :
      Hom'Rel ⟨d₂, f⟩ ⟨d₁, Hom.restrict φ f⟩

def Hom := Quot (Hom'Rel X Y)

namespace Hom

variable {X Y Z T}

def mk {d : Hom.DefDomain X Y} (φ : d.src ⟶ d.tgt) : Hom X Y :=
  Quot.mk _ (.mk φ)

lemma quotMk_eq_quotMk_iff {x y : Hom' X Y} :
    Quot.mk (Hom'Rel X Y) x = Quot.mk (Hom'Rel X Y) y ↔
      ∃ (d : DefDomain X Y) (φ₁ : d ⟶ x.1) (φ₂ : d ⟶ y.1),
        restrict φ₁ x.2 = restrict φ₂ y.2 := by
  constructor
  · intro h
    rw [Quot.eq] at h
    induction h with
    | rel _ _ h =>
      obtain ⟨d₁, d₂, φ, f⟩ := h
      exact ⟨d₁, φ, 𝟙 _, by simp [restrict]⟩
    | refl x =>
      exact ⟨_, 𝟙 _, 𝟙 _, by simp [restrict]⟩
    | symm _ _ _ h =>
      obtain ⟨_, _, _, eq⟩ := h
      exact ⟨_, _, _, eq.symm⟩
    | trans _ _ _ _ _ h₁₂ h₂₃ =>
      obtain ⟨d₁₂, φ₁, φ₂, eq₁₂⟩ := h₁₂
      obtain ⟨d₂₃, ψ₂, ψ₃, eq₂₃⟩ := h₂₃
      obtain ⟨d, ⟨i₁₂⟩, ⟨i₂₃⟩⟩ := DefDomain.exists_min d₁₂ d₂₃
      refine ⟨d, i₁₂ ≫ φ₁, i₂₃ ≫ ψ₃, ?_⟩
      simp only [restrict] at eq₁₂ eq₂₃
      simp only [restrict, DefDomain.comp_ι, DefDomain.comp_π, assoc]
      have hι := congr_arg DefDomain.Hom.ι (Subsingleton.elim (i₁₂ ≫ φ₂) (i₂₃ ≫ ψ₂))
      have hπ := congr_arg DefDomain.Hom.π (Subsingleton.elim (i₁₂ ≫ φ₂) (i₂₃ ≫ ψ₂))
      dsimp at hι hπ
      rw [reassoc_of% eq₁₂, ← reassoc_of% eq₂₃, reassoc_of% hι, hπ]
  · obtain ⟨d₁, f₁, rfl⟩ := x.mk_surjective
    obtain ⟨d₂, f₂, rfl⟩ := y.mk_surjective
    rintro ⟨d, φ₁, φ₂, h⟩
    trans mk (Hom.restrict φ₁ f₁)
    · exact (Quot.sound (by constructor))
    · rw [h]
      exact (Quot.sound (by constructor)).symm

lemma ext_iff {d₁ d₂ : DefDomain X Y} (f₁ : d₁.src ⟶ d₁.tgt) (f₂ : d₂.src ⟶ d₂.tgt) :
    mk f₁ = mk f₂ ↔ ∃ (d : DefDomain X Y) (φ₁ : d ⟶ d₁) (φ₂ : d ⟶ d₂),
      restrict φ₁ f₁ = restrict φ₂ f₂ := by
  apply quotMk_eq_quotMk_iff

variable (P) in
def ofHom {X Y : C} (f : X ⟶ Y) : Hom (P := P) ⟨X⟩ ⟨Y⟩ :=
  mk (d := DefDomain.top _ _) f

variable (X) in
abbrev id : Hom X X := ofHom P (𝟙 X.obj)

variable {d₁₂ : DefDomain X Y} {d₂₃ : DefDomain Y Z}
    (a : d₁₂.src ⟶ d₁₂.tgt) (b : d₂₃.src ⟶ d₂₃.tgt)

structure CompStruct {d₁₃ : DefDomain X Z}
    (h : DefDomain.CompStruct d₁₂ d₂₃ d₁₃) where
  α : d₁₃.src ⟶ h.obj
  β : h.obj ⟶ d₁₃.tgt
  hα : α ≫ h.fromObj = h.ι ≫ a
  hβ : h.toObj ≫ β = b ≫ h.π

namespace CompStruct

lemma nonempty : ∃ (d₁₃ : DefDomain X Z)
    (h : DefDomain.CompStruct d₁₂ d₂₃ d₁₃), Nonempty (CompStruct a b h) := by
  sorry

variable {a b}
def comp {d₁₃ : DefDomain X Z}
    {h : DefDomain.CompStruct d₁₂ d₂₃ d₁₃} (γ : CompStruct a b h) :
    Hom X Z :=
  Hom.mk (d := d₁₃) (γ.α ≫ γ.β)

end CompStruct

end Hom

variable {X Y Z}

namespace Hom'

variable (f : Hom' X Y) (g : Hom' Y Z)

noncomputable def comp.defDomain : Hom.DefDomain X Z :=
  (Hom.CompStruct.nonempty f.2 g.2).choose

noncomputable def comp.defDomainCompStruct :
    Hom.DefDomain.CompStruct f.1 g.1 (defDomain f g) :=
  (Hom.CompStruct.nonempty f.2 g.2).choose_spec.choose

noncomputable def comp.compStruct :
    Hom.CompStruct f.2 g.2 (defDomainCompStruct f g) :=
  (Hom.CompStruct.nonempty f.2 g.2).choose_spec.choose_spec.some

noncomputable def comp : Hom X Z := (comp.compStruct f g).comp

end Hom'

namespace Hom

noncomputable def comp : Hom X Y → Hom Y Z → Hom X Z :=
  Quot.lift₂ Hom'.comp sorry sorry

@[simp]
lemma id_comp (f : Hom X Y) : (Hom.id X).comp f = f := sorry

@[simp]
lemma comp_id (f : Hom X Y) : f.comp (.id Y) = f := sorry

@[simp]
lemma assoc (f : Hom X Y) (g : Hom Y Z) (h : Hom Z T) :
    (f.comp g).comp h = f.comp (g.comp h) := sorry

end Hom

noncomputable instance : Category P.SerreClassLocalization where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

end SerreClassLocalization

def toSerreClassLocalization : C ⥤ P.SerreClassLocalization where
  obj X := ⟨X⟩
  map f := .ofHom P f
  map_id _ := rfl
  map_comp := sorry

/-! Alternative approach, in two steps:
1) Localization w.r.t. `epimorphisms C ⊓ P.isoModSerre` using a left calculus of fractions
2) Localize the resulting category using a right calculus of fractions
-/

namespace IsSerreClass

namespace Localization

instance : (P.isoModSerre ⊓ .epimorphisms _).HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ :=
    ⟨{s := pushout.inl φ.f φ.s
      f := pushout.inr φ.f φ.s,
      hs := MorphismProperty.pushout_inl _ _ φ.hs}, pushout.condition⟩
  ext _ _ _ f₁ f₂ s hs eq := by
    have : Epi s := hs.2
    exact ⟨_, 𝟙 _, MorphismProperty.id_mem _ _, by simpa [cancel_epi] using eq⟩

variable {D : Type*} [Category* D]
  (L : C ⥤ D)

def LocEpi := (P.isoModSerre ⊓ .epimorphisms _).Localization
  deriving Category

def QEpi : C ⥤ LocEpi P := (P.isoModSerre ⊓ .epimorphisms _).Q

variable {P} in
lemma QEpi_obj_surjective : Function.Surjective (QEpi P).obj :=
  (Localization.Construction.objEquiv _).surjective

instance : (QEpi P).IsLocalization (P.isoModSerre ⊓ .epimorphisms _) :=
  inferInstanceAs ((MorphismProperty.Q _).IsLocalization _)

instance : (QEpi P).EssSurj :=
  Localization.essSurj _ (P.isoModSerre ⊓ .epimorphisms _)

def mapIsoModSerreInterEpi :
    MorphismProperty (LocEpi P) :=
  fun ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩ f ↦ ∃ (Z : C) (g : X ⟶ Z) (s : Y ⟶ Z) (_ : P.isoModSerre g)
    (_ : (P.isoModSerre ⊓ .epimorphisms _) s),
        f ≫ (QEpi P).map s = (QEpi P).map g

lemma mapIsoModSerreInterEpi_iff {X Y : C} (f : (QEpi P).obj X ⟶ (QEpi P).obj Y) :
    mapIsoModSerreInterEpi P f ↔ ∃ (Z : C) (g : X ⟶ Z) (s : Y ⟶ Z) (_ : P.isoModSerre g)
      (_ : (P.isoModSerre ⊓ .epimorphisms _) s), f ≫ (QEpi P).map s = (QEpi P).map g :=
  Iff.rfl

lemma mapIsoModSerreInterEpi.map {X Y : C} (f : X ⟶ Y) (hf : P.isoModSerre f) :
    mapIsoModSerreInterEpi P ((QEpi P).map f) := by
  rw [mapIsoModSerreInterEpi_iff]
  exact ⟨_, f, 𝟙 _, hf, MorphismProperty.id_mem _ _, by simp⟩

instance : (mapIsoModSerreInterEpi P).RespectsIso := by
  sorry

instance : (mapIsoModSerreInterEpi P).IsMultiplicative where
  id_mem X := by
    obtain ⟨X, rfl⟩ := QEpi_obj_surjective X
    rw [← Functor.map_id]
    exact mapIsoModSerreInterEpi.map _ _ (MorphismProperty.id_mem _ _)
  comp_mem := sorry

instance : (mapIsoModSerreInterEpi P).HasRightCalculusOfFractions where
  exists_rightFraction := by
    let L := QEpi P
    suffices ∀ {X Y Z : C} (f : L.obj X ⟶ L.obj Z) (s : L.obj Y ⟶ L.obj Z)
      (hs : mapIsoModSerreInterEpi P s),
        ∃ (ψ : (mapIsoModSerreInterEpi P).RightFraction (L.obj X) (L.obj Y)),
          ψ.s ≫ f = ψ.f ≫ s by
      intro X Y φ
      let eX := L.objObjPreimageIso X
      let eY := L.objObjPreimageIso Y
      let eY' := L.objObjPreimageIso φ.Y'
      obtain ⟨ψ, fac⟩ := this (eX.hom ≫ φ.f ≫ eY'.inv) (eY.hom ≫ φ.s ≫ eY'.inv)
        ((MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk eY eY')).2 φ.hs)
      exact
        ⟨{s := ψ.s ≫ eX.hom
          f := ψ.f ≫ eY.hom
          hs := (MorphismProperty.arrow_mk_iso_iff _
            (by exact Arrow.isoMk (Iso.refl _) eX)).1 ψ.hs }, by simpa [← cancel_mono eY'.inv]⟩
    intro X Y Z f s hs
    obtain ⟨φf, rfl⟩ := Localization.exists_leftFraction L (P.isoModSerre ⊓ .epimorphisms _) f
    obtain ⟨φs, rfl⟩ := Localization.exists_leftFraction L (P.isoModSerre ⊓ .epimorphisms _) s
    let W := pushout φf.s φs.s
    let f' : X ⟶ W := φf.f ≫ pushout.inl _ _
    let s' : Y ⟶ W := φs.f ≫ pushout.inr _ _
    refine ⟨{
      X' := L.obj (pullback f' s')
      s := L.map (pullback.fst _ _)
      hs := by
        refine mapIsoModSerreInterEpi.map P _
          (MorphismProperty.pullback_fst _ _
            (MorphismProperty.comp_mem _ _ _ ?_ (MorphismProperty.pushout_inr _ _ φf.hs.1)))
        sorry
      f := L.map (pullback.snd _ _) }, ?_⟩
    have := Localization.inverts L (P.isoModSerre ⊓ .epimorphisms _) φf.s φf.hs
    have := Localization.inverts L (P.isoModSerre ⊓ .epimorphisms _)
      (pushout.inl φf.s φs.s) (MorphismProperty.pushout_inl _ _ φs.hs)
    rw [← cancel_mono (L.map φf.s), assoc, MorphismProperty.LeftFraction.map_comp_map_s,
      ← cancel_mono (L.map (pushout.inl φf.s φs.s)), assoc, assoc, assoc,
      ← L.map_comp, ← L.map_comp, pullback.condition,
      ← L.map_comp, pushout.condition, L.map_comp, L.map_comp, L.map_comp,
      MorphismProperty.LeftFraction.map_comp_map_s_assoc]
  ext := sorry

end Localization

end IsSerreClass

end ObjectProperty

end CategoryTheory
