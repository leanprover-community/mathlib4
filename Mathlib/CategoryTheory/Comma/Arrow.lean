/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Comma.Basic

/-!
# The category of arrows

The category of arrows, with morphisms commutative squares.
We set this up as a specialization of the comma category `Comma L R`,
where `L` and `R` are both the identity functor.

## Tags

comma, arrow
-/

@[expose] public section



namespace CategoryTheory

universe v u

-- morphism levels before object levels. See note [category theory universes].
variable {T : Type u} [Category.{v} T]

variable (T) in
/-- The arrow category of `T` has as objects all morphisms in `T` and as morphisms commutative
squares in `T`. -/
def Arrow := Comma (𝟭 T) (𝟭 T)

/-- The type of morphisms in the category `Arrow T`. -/
protected def Arrow.Hom (f g : Arrow T) := CommaMorphism f g

instance : Quiver (Arrow T) where
  Hom := Arrow.Hom

instance : Category (Arrow T) :=
  inferInstanceAs <| Category (Comma (𝟭 T) (𝟭 T))

namespace Arrow

/-- The left object of an arrow. -/
abbrev left (X : Arrow T) : T := Comma.left X

/-- The right object of an arrow. -/
abbrev right (X : Arrow T) : T := Comma.right X

/-- Given `X : Arrow T`, this is the morphism `X.left ⟶ X.right`. -/
abbrev hom (X : Arrow T) : X.left ⟶ X.right := Comma.hom X

/-- The left part of a morphism in the category of arrows. -/
abbrev Hom.left {X Y : Arrow T} (f : X ⟶ Y) : X.left ⟶ Y.left := CommaMorphism.left f

/-- The right part of a morphism in the category of arrows. -/
abbrev Hom.right {X Y : Arrow T} (f : X ⟶ Y) : X.right ⟶ Y.right := CommaMorphism.right f

@[ext]
lemma hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) :
    f = g :=
  CommaMorphism.ext h₁ h₂

@[simp]
theorem id_left (f : Arrow T) : Arrow.Hom.left (𝟙 f) = 𝟙 f.left :=
  rfl

@[simp]
theorem id_right (f : Arrow T) : Arrow.Hom.right (𝟙 f) = 𝟙 f.right :=
  rfl

@[simp, reassoc]
theorem comp_left {X Y Z : Arrow T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).left = f.left ≫ g.left := rfl

@[simp, reassoc]
theorem comp_right {X Y Z : Arrow T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).right = f.right ≫ g.right := rfl

/-- An object in the arrow category is simply a morphism in `T`. -/
@[simps]
def mk {X Y : T} (f : X ⟶ Y) : Arrow T where
  left := X
  right := Y
  hom := f

@[simp]
theorem mk_eq (f : Arrow T) : Arrow.mk f.hom = f := by
  cases f
  rfl

lemma mk_surjective (f : Arrow T) :
    ∃ (X Y : T) (g : X ⟶ Y), f = Arrow.mk g :=
  ⟨_, _, f.hom, rfl⟩

theorem mk_injective (A B : T) :
    Function.Injective (Arrow.mk : (A ⟶ B) → Arrow T) := fun f g h => by
  cases h
  rfl

theorem mk_inj (A B : T) {f g : A ⟶ B} : Arrow.mk f = Arrow.mk g ↔ f = g :=
  (mk_injective A B).eq_iff

instance {X Y : T} : CoeOut (X ⟶ Y) (Arrow T) where
  coe := mk

@[reassoc (attr := simp high)]
theorem w {f g : Arrow T} (sq : f ⟶ g) : sq.left ≫ g.hom = f.hom ≫ sq.right :=
  CommaMorphism.w sq

@[reassoc]
lemma Hom.w {f g : Arrow T} (sq : f ⟶ g) : sq.left ≫ g.hom = f.hom ≫ sq.right := by
  simp

theorem hom.congr_left {f g : Arrow T} {φ₁ φ₂ : f ⟶ g} (h : φ₁ = φ₂) : φ₁.left = φ₂.left := by
  rw [h]

theorem hom.congr_right {f g : Arrow T} {φ₁ φ₂ : f ⟶ g} (h : φ₁ = φ₂) : φ₁.right = φ₂.right := by
  simp [h]

theorem iso_w {f g : Arrow T} (e : f ≅ g) : g.hom = e.inv.left ≫ f.hom ≫ e.hom.right := by
  simp [← Arrow.comp_right]

theorem iso_w' {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z} (e : Arrow.mk f ≅ Arrow.mk g) :
    g = e.inv.left ≫ f ≫ e.hom.right :=
  iso_w e

lemma eqToHom_left {X Y : Arrow T} (h : X = Y) :
    (eqToHom h).left = eqToHom (by rw [h]) := by subst h; rfl

lemma eqToHom_right {X Y : Arrow T} (h : X = Y) :
    (eqToHom h).right = eqToHom (by rw [h]) := by subst h; rfl

lemma mk_eq_mk_iff {X Y X' Y' : T} (f : X ⟶ Y) (f' : X' ⟶ Y') :
    Arrow.mk f = Arrow.mk f' ↔
      ∃ (hX : X = X') (hY : Y = Y'), f = eqToHom hX ≫ f' ≫ eqToHom hY.symm := by
  constructor
  · intro h
    refine ⟨congr_arg Arrow.left h, congr_arg Arrow.right h, ?_⟩
    simpa [eqToHom_left, eqToHom_right] using iso_w (eqToIso h.symm)
  · rintro ⟨rfl, rfl, h⟩
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h
    rw [h]

lemma ext {f g : Arrow T}
    (h₁ : f.left = g.left) (h₂ : f.right = g.right)
    (h₃ : f.hom = eqToHom h₁ ≫ g.hom ≫ eqToHom h₂.symm) : f = g :=
  (mk_eq_mk_iff _ _).2 (by simp_all)

@[simp]
lemma arrow_mk_comp_eqToHom {X Y Y' : T} (f : X ⟶ Y) (h : Y = Y') :
    Arrow.mk (f ≫ eqToHom h) = Arrow.mk f :=
  ext rfl h.symm (by simp)

@[simp]
lemma arrow_mk_eqToHom_comp {X' X Y : T} (f : X ⟶ Y) (h : X' = X) :
    Arrow.mk (eqToHom h ≫ f) = Arrow.mk f :=
  ext h rfl (by simp)

/-- A morphism in the arrow category is a commutative square connecting two objects of the arrow
    category. -/
@[simps]
def homMk {f g : Arrow T} (u : f.left ⟶ g.left) (v : f.right ⟶ g.right)
    (w : u ≫ g.hom = f.hom ≫ v := by cat_disch) : f ⟶ g where
  left := u
  right := v
  w := w

/-- We can also build a morphism in the arrow category out of any commutative square in `T`. -/
@[simps]
def homMk' {X Y : T} {f : X ⟶ Y} {P Q : T} {g : P ⟶ Q} (u : X ⟶ P) (v : Y ⟶ Q)
    (w : u ≫ g = f ≫ v := by cat_disch) :
    Arrow.mk f ⟶ Arrow.mk g where
  left := u
  right := v
  w := w

@[reassoc]
theorem w_mk_left {X Y : T} {f : X ⟶ Y} {g : Arrow T} (sq : mk f ⟶ g) :
    dsimp% sq.left ≫ g.hom = f ≫ sq.right :=
  sq.w

@[reassoc (attr := simp)]
theorem w_mk_right {f : Arrow T} {X Y : T} {g : X ⟶ Y} (sq : f ⟶ mk g) :
    dsimp% sq.left ≫ g = f.hom ≫ sq.right :=
  sq.w

@[reassoc]
theorem w_mk {X Y X' Y' : T} {f : X ⟶ Y} {g : X' ⟶ Y'} (sq : mk f ⟶ mk g) :
    dsimp% sq.left ≫ g = f ≫ sq.right :=
  sq.w

theorem isIso_of_isIso_left_of_isIso_right {f g : Arrow T} (ff : f ⟶ g) [IsIso ff.left]
    [IsIso ff.right] : IsIso ff where
  out := ⟨homMk (inv ff.left) (inv ff.right), by cat_disch⟩

/-- Create an isomorphism between arrows,
by providing isomorphisms between the domains and codomains,
and a proof that the square commutes. -/
@[simps!]
def isoMk {f g : Arrow T} (l : f.left ≅ g.left) (r : f.right ≅ g.right)
    (h : l.hom ≫ g.hom = f.hom ≫ r.hom := by cat_disch) : f ≅ g :=
  Comma.isoMk l r h

/-- A variant of `Arrow.isoMk` that creates an iso between two `Arrow.mk`s with a better type
signature. -/
abbrev isoMk' {W X Y Z : T} (f : W ⟶ X) (g : Y ⟶ Z) (e₁ : W ≅ Y) (e₂ : X ≅ Z)
    (h : e₁.hom ≫ g = f ≫ e₂.hom := by cat_disch) : Arrow.mk f ≅ Arrow.mk g :=
  Arrow.isoMk e₁ e₂ h

section

variable {f g : Arrow T} (sq : f ⟶ g)

instance isIso_left [IsIso sq] : IsIso sq.left :=
  ⟨(inv sq).left, by simp [← comp_left]⟩

instance isIso_right [IsIso sq] : IsIso sq.right :=
  ⟨(inv sq).right, by simp [← comp_right]⟩

lemma isIso_of_isIso' {f g : Arrow T} (sq : f ⟶ g) [IsIso sq] [IsIso f.hom] :
    IsIso g.hom := by
  rw [iso_w (asIso sq)]
  infer_instance

lemma isIso_of_isIso {X Y : T} {f : X ⟶ Y} {g : Arrow T} (sq : mk f ⟶ g) [IsIso sq] [IsIso f] :
    IsIso g.hom := by
  have : IsIso (mk f).hom := by assumption
  apply isIso_of_isIso' sq

lemma isIso_hom_iff_isIso_hom_of_isIso {f g : Arrow T} (sq : f ⟶ g) [IsIso sq] :
    IsIso f.hom ↔ IsIso g.hom :=
  ⟨fun _ => isIso_of_isIso' sq, fun _ => isIso_of_isIso' (inv sq)⟩

lemma isIso_iff_isIso_of_isIso {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z} (sq : mk f ⟶ mk g) [IsIso sq] :
    IsIso f ↔ IsIso g :=
  isIso_hom_iff_isIso_hom_of_isIso sq

lemma isIso_hom_iff_isIso_of_isIso {Y Z : T} {f : Arrow T} {g : Y ⟶ Z} (sq : f ⟶ mk g) [IsIso sq] :
    IsIso f.hom ↔ IsIso g :=
  isIso_hom_iff_isIso_hom_of_isIso sq

@[simp]
theorem inv_left [IsIso sq] : (inv sq).left = inv sq.left :=
  IsIso.eq_inv_of_hom_inv_id (by simp [← comp_left])

@[simp]
theorem inv_right [IsIso sq] : (inv sq).right = inv sq.right :=
  IsIso.eq_inv_of_hom_inv_id (by simp [← comp_right])

theorem left_hom_inv_right [IsIso sq] : sq.left ≫ g.hom ≫ inv sq.right = f.hom := by
  simp only [← Category.assoc, IsIso.comp_inv_eq, w]

theorem inv_left_hom_right [IsIso sq] : inv sq.left ≫ f.hom ≫ sq.right = g.hom := by
  simp only [w, IsIso.inv_comp_eq]

instance mono_left [Mono sq] : Mono sq.left where
  right_cancellation {Z} φ ψ h := by
    let aux : (Z ⟶ f.left) → (Arrow.mk (𝟙 Z) ⟶ f) := fun φ =>
      { left := φ
        right := φ ≫ f.hom }
    have : ∀ g, (aux g).right = g ≫ f.hom := fun g => rfl
    change (aux φ).left = (aux ψ).left
    congr 1
    rw [← cancel_mono sq]
    ext
    · exact h
    · simp [this, ← Arrow.w_mk_right, reassoc_of% h]

instance epi_right [Epi sq] : Epi sq.right where
  left_cancellation {Z} φ ψ h := by
    let aux : (g.right ⟶ Z) → (g ⟶ Arrow.mk (𝟙 Z)) := fun φ =>
      Arrow.homMk (g.hom ≫ φ) φ
    change (aux φ).right = (aux ψ).right
    congr 1
    rw [← cancel_epi sq]
    ext
    · simp only [comp_left, comp_left, aux, mk_left, homMk_left, w_assoc, h]
    · exact h

@[reassoc (attr := simp)]
lemma hom_inv_id_left (e : f ≅ g) : e.hom.left ≫ e.inv.left = 𝟙 _ := by
  rw [← comp_left, e.hom_inv_id, id_left]

@[reassoc (attr := simp)]
lemma inv_hom_id_left (e : f ≅ g) : e.inv.left ≫ e.hom.left = 𝟙 _ := by
  rw [← comp_left, e.inv_hom_id, id_left]

@[reassoc (attr := simp)]
lemma hom_inv_id_right (e : f ≅ g) : e.hom.right ≫ e.inv.right = 𝟙 _ := by
  rw [← comp_right, e.hom_inv_id, id_right]

@[reassoc (attr := simp)]
lemma inv_hom_id_right (e : f ≅ g) : e.inv.right ≫ e.hom.right = 𝟙 _ := by
  rw [← comp_right, e.inv_hom_id, id_right]

end

/-- Given a square from an arrow `i` to an isomorphism `p`, express the source part of `sq`
in terms of the inverse of `p`. -/
@[simp]
theorem square_to_iso_invert (i : Arrow T) {X Y : T} (p : X ≅ Y) (sq : i ⟶ Arrow.mk p.hom) :
    i.hom ≫ sq.right ≫ p.inv = sq.left := by
  simpa only [mk_right, Category.assoc] using (Iso.comp_inv_eq p).mpr (Arrow.w_mk_right sq).symm

/-- Given a square from an isomorphism `i` to an arrow `p`, express the target part of `sq`
in terms of the inverse of `i`. -/
theorem square_from_iso_invert {X Y : T} (i : X ≅ Y) (p : Arrow T) (sq : Arrow.mk i.hom ⟶ p) :
    i.inv ≫ sq.left ≫ p.hom = sq.right := by
  simp [Arrow.w_mk_left]

variable {C : Type u} [Category.{v} C]

/-- A helper construction: given a square between `i` and `f ≫ g`, produce a square between
`i` and `g`, whose top leg uses `f`:
```
A  → X
     ↓f
↓i   Y             --> A → Y
     ↓g                ↓i  ↓g
B  → Z                 B → Z
```
-/
@[simps!]
def squareToSnd {X Y Z : C} {i : Arrow C} {f : X ⟶ Y} {g : Y ⟶ Z} (sq : i ⟶ Arrow.mk (f ≫ g)) :
    i ⟶ Arrow.mk g :=
  Arrow.homMk (sq.left ≫ f) (sq.right) (by simp [w_mk sq])

/-- The functor sending an arrow to its source. -/
@[simps!]
def leftFunc : Arrow C ⥤ C :=
  Comma.fst _ _

/-- The functor sending an arrow to its target. -/
@[simps!]
def rightFunc : Arrow C ⥤ C :=
  Comma.snd _ _

/-- The natural transformation from `leftFunc` to `rightFunc`, given by the arrow itself. -/
@[simps]
def leftToRight : (leftFunc : Arrow C ⥤ C) ⟶ rightFunc where app f := f.hom

end Arrow

namespace Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A functor `C ⥤ D` induces a functor between the corresponding arrow categories. -/
@[simps]
def mapArrow (F : C ⥤ D) : Arrow C ⥤ Arrow D where
  obj a := Arrow.mk (F.map a.hom)
  map f := Arrow.homMk (F.map f.left) (F.map f.right) (by simp [← Functor.map_comp])

variable (C D)

/-- The functor `(C ⥤ D) ⥤ (Arrow C ⥤ Arrow D)` which sends
a functor `F : C ⥤ D` to `F.mapArrow`. -/
@[simps]
def mapArrowFunctor : (C ⥤ D) ⥤ (Arrow C ⥤ Arrow D) where
  obj F := F.mapArrow
  map τ := { app f := Arrow.homMk (τ.app _) (τ.app _) }

variable {C D}

/-- The equivalence of categories `Arrow C ≌ Arrow D` induced by an equivalence `C ≌ D`. -/
@[simps]
def mapArrowEquivalence (e : C ≌ D) : Arrow C ≌ Arrow D where
  functor := e.functor.mapArrow
  inverse := e.inverse.mapArrow
  unitIso := Functor.mapIso (mapArrowFunctor C C) e.unitIso
  counitIso := Functor.mapIso (mapArrowFunctor D D) e.counitIso

instance isEquivalence_mapArrow (F : C ⥤ D) [IsEquivalence F] :
    IsEquivalence F.mapArrow :=
  (mapArrowEquivalence (asEquivalence F)).isEquivalence_functor

end Functor

variable {C D : Type*} [Category* C] [Category* D]

/-- The images of `f : Arrow C` by two isomorphic functors `F : C ⥤ D` are
isomorphic arrows in `D`. -/
def Arrow.isoOfNatIso {F G : C ⥤ D} (e : F ≅ G)
    (f : Arrow C) : F.mapArrow.obj f ≅ G.mapArrow.obj f :=
  Arrow.isoMk (e.app f.left) (e.app f.right)

variable (T)

/-- `Arrow T` is equivalent to a sigma type. -/
@[simps!]
def Arrow.equivSigma :
    Arrow T ≃ Σ (X Y : T), X ⟶ Y where
  toFun f := ⟨_, _, f.hom⟩
  invFun x := Arrow.mk x.2.2

/-- The equivalence `Arrow (Discrete S) ≃ S`. -/
def Arrow.discreteEquiv (S : Type u) : Arrow (Discrete S) ≃ S where
  toFun f := f.left.as
  invFun s := Arrow.mk (𝟙 (Discrete.mk s))
  left_inv := by
    rintro ⟨⟨_⟩, ⟨_⟩, f⟩
    obtain rfl := Discrete.eq_of_hom f
    rfl

/-- Extensionality lemma for functors `C ⥤ D` which uses as an assumption
that the induced maps `Arrow C → Arrow D` coincide. -/
lemma Arrow.functor_ext {F G : C ⥤ D} (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    F.mapArrow.obj (Arrow.mk f) = G.mapArrow.obj (Arrow.mk f)) :
    F = G :=
  Functor.ext (fun X ↦ congr_arg Comma.left (h (𝟙 X))) (fun X Y f ↦ by
    have := h f
    simp only [Functor.mapArrow_obj, mk_eq_mk_iff] at this
    tauto)

end CategoryTheory
