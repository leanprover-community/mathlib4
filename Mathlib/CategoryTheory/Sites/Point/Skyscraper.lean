/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Skyscraper sheaves

Let `Φ` be a point of a site `(C, J)`. In this file, we construct the
skyscraper sheaf functor `skyscraperSheafFunctor : A ⥤ Sheaf J A` and
show that it is a right adjoint to `Φ.sheafFiber : Sheaf J A ⥤ A`.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A]
  [HasProducts.{w} A]

/-- Given a point `Φ` on a site `(C, J)`, this is the skyscraper presheaf functor
`A ⥤ Cᵒᵖ ⥤ A`. -/
@[simps!]
noncomputable def skyscraperPresheafFunctor : A ⥤ Cᵒᵖ ⥤ A :=
  Functor.flip (Φ.fiber.op ⋙ piFunctor.{w}.flip)

/-- Given a point `Φ` on a site `(C, J)`, and an object `M` of a category `A`,
this is the skyscraper presheaf with value `M`: it sends `X : C` to the
product of copies of `M` indexed by `Φ.fiber.obj X`. -/
noncomputable abbrev skyscraperPresheaf (M : A) :
    Cᵒᵖ ⥤ A :=
  Φ.skyscraperPresheafFunctor.obj M

section

variable {P Q : Cᵒᵖ ⥤ A} {M N : A} [HasColimitsOfSize.{w, w} A]

/-- If `Φ` is a point of a site `(C, J)`, `P : Cᵒᵖ ⥤ A` and `M : A`, this is
the bijection `(Φ.presheafFiber.obj P ⟶ M) ≃ (P ⟶ Φ.skyscraperPresheaf M)`
that is part of the adjunction `skyscraperPresheafAdjunction`. -/
@[simps -isSimp apply_app symm_apply]
noncomputable def skyscraperPresheafHomEquiv :
    (Φ.presheafFiber.obj P ⟶ M) ≃ (P ⟶ Φ.skyscraperPresheaf M) where
  toFun f :=
    { app X := Pi.lift (fun x ↦ Φ.toPresheafFiber X.unop x P ≫ f)
      naturality {X Y} g := by
        dsimp
        ext y
        have := Φ.toPresheafFiber_w g.unop y P
        dsimp at this
        simp [reassoc_of% this] }
  invFun g := Φ.presheafFiberDesc (fun X x ↦ g.app (op X) ≫ Pi.π _ x) (by simp)
  left_inv f := by cat_disch
  right_inv g := by cat_disch

@[reassoc (attr := simp)]
lemma toPresheafFiber_skyscraperPresheafHomEquiv_symm
    (g : P ⟶ Φ.skyscraperPresheaf M) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.skyscraperPresheafHomEquiv.symm g =
      g.app (op X) ≫ Pi.π _ x := by
  simp [skyscraperPresheafHomEquiv_symm_apply]

@[reassoc]
lemma skyscraperPresheafHomEquiv_naturality_left_symm
    (f : P ⟶ Q) (g : Q ⟶ Φ.skyscraperPresheaf M) :
    Φ.skyscraperPresheafHomEquiv.symm (f ≫ g) =
      Φ.presheafFiber.map f ≫ Φ.skyscraperPresheafHomEquiv.symm g := by
  cat_disch

@[reassoc (attr := simp)]
lemma skyscraperPresheafHomEquiv_app_π
    (f : Φ.presheafFiber.obj P ⟶ M) (X : C) (x : Φ.fiber.obj X) :
    (Φ.skyscraperPresheafHomEquiv f).app (op X) ≫ Pi.π (fun (_ : Φ.fiber.obj X) ↦ M) x =
      Φ.toPresheafFiber X x P ≫ f := by
  simp [skyscraperPresheafHomEquiv_apply_app]

@[reassoc]
lemma skyscraperPresheafHomEquiv_naturality_right
    (f : Φ.presheafFiber.obj P ⟶ M) (g : M ⟶ N) :
    Φ.skyscraperPresheafHomEquiv (f ≫ g) =
      Φ.skyscraperPresheafHomEquiv f ≫ Φ.skyscraperPresheafFunctor.map g := by
  ext
  dsimp
  ext
  dsimp
  rw [skyscraperPresheafHomEquiv_app_π]
  dsimp
  rw [Category.assoc, Pi.map_π, skyscraperPresheafHomEquiv_app_π_assoc]

end

section

variable [HasColimitsOfSize.{w, w} A]

/-- Given a point of a site, the skyscraper presheaf functor is right adjoint
to the fiber functor on presheaves. -/
noncomputable def skyscraperPresheafAdjunction [HasColimitsOfSize.{w, w} A] :
    Φ.presheafFiber (A := A) ⊣ Φ.skyscraperPresheafFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := Φ.skyscraperPresheafHomEquiv
      homEquiv_naturality_left_symm _ _ := Φ.skyscraperPresheafHomEquiv_naturality_left_symm _ _
      homEquiv_naturality_right _ _ := Φ.skyscraperPresheafHomEquiv_naturality_right _ _ }

@[simp]
lemma skyscraperPresheafAdjunction_homEquiv_apply {P : Cᵒᵖ ⥤ A} {M : A}
    (f : Φ.presheafFiber.obj P ⟶ M) :
    Φ.skyscraperPresheafAdjunction.homEquiv _ _ f =
      Φ.skyscraperPresheafHomEquiv f := by
  simp [skyscraperPresheafAdjunction]

@[simp]
lemma skyscraperPresheafAdjunction_homEquiv_symm_apply {P : Cᵒᵖ ⥤ A} {M : A}
    (f : P ⟶ Φ.skyscraperPresheaf M) :
    (Φ.skyscraperPresheafAdjunction.homEquiv _ _).symm f =
      Φ.skyscraperPresheafHomEquiv.symm f := by
  simp [skyscraperPresheafAdjunction]

end

variable {Φ} in
private lemma isSheaf_skyscraperPresheaf_aux
    {M : A} {X : C} (R : Sieve X) (hR : R ∈ J X)
    (s : Cone (R.arrows.diagram.op ⋙ Φ.skyscraperPresheaf M)) :
    ∃ (l : s.pt ⟶ ∏ᶜ fun (_ : Φ.fiber.obj X) ↦ M),
      ∀ (j : R.arrows.category) (y : Φ.fiber.obj j.obj.left),
        l ≫ Pi.π _ (Φ.fiber.map j.obj.hom y) = s.π.app (op j) ≫ Pi.π _ y := by
  suffices ∀ (x : Φ.fiber.obj X), ∃ (l : s.pt ⟶ M),
      ∀ ⦃Y : C⦄ (g : Y ⟶ X) (hg : R g) (y : Φ.fiber.obj Y) (hy : Φ.fiber.map g y = x),
        s.π.app (op (Presieve.categoryMk _ _ hg)) ≫ Pi.π _ y = l by
    choose l hl using this
    exact ⟨Pi.lift l, fun j y ↦ by simpa using (hl _ j.obj.hom  j.property y rfl).symm⟩
  intro x
  obtain ⟨Y₁, f₁, hf₁, y₁, hy₁⟩ := Φ.jointly_surjective _ hR x
  refine ⟨s.π.app (op (Presieve.categoryMk _ _ hf₁)) ≫ Pi.π _ y₁,
    fun Y₂ f₂ hf₂ y₂ hy₂ ↦ ?_⟩
  obtain ⟨Z, p₁, p₂, z, fac, hz₁, hz₂⟩ :
      ∃ (Z : C) (p₁ : Z ⟶ Y₁) (p₂ : Z ⟶ Y₂) (z : Φ.fiber.obj Z), p₁ ≫ f₁ = p₂ ≫ f₂ ∧
        Φ.fiber.map p₁ z = y₁ ∧ Φ.fiber.map p₂ z = y₂ := by
    let α₁ : Φ.fiber.elementsMk _ y₁ ⟶ Φ.fiber.elementsMk _ x := ⟨f₁, hy₁⟩
    let α₂ : Φ.fiber.elementsMk _ y₂ ⟶ Φ.fiber.elementsMk _ x := ⟨f₂, hy₂⟩
    obtain ⟨z, q₁, q₂, fac⟩ := IsCofiltered.cospan α₁ α₂
    rw [Subtype.ext_iff] at fac
    exact ⟨z.1, q₁.1, q₂.1, z.2, fac, by simp, by simp⟩
  let φ₁ : Presieve.categoryMk _ _ (R.downward_closed hf₁ p₁) ⟶
      Presieve.categoryMk _ _ hf₁ :=
    ObjectProperty.homMk (Over.homMk p₁)
  let φ₂ : Presieve.categoryMk _ _ (R.downward_closed hf₁ p₁) ⟶
      Presieve.categoryMk _ _ hf₂ :=
    ObjectProperty.homMk (Over.homMk p₂)
  simpa [hz₁, hz₂, φ₁, φ₂] using
    (Cone.w s φ₂.op =≫ Pi.π _ z).trans (Cone.w s φ₁.op =≫ Pi.π _ z).symm

lemma isSheaf_skyscraperPresheaf (M : A) :
    Presheaf.IsSheaf J (Φ.skyscraperPresheaf M) := by
  rw [Presheaf.isSheaf_iff_isLimit]
  intro X R hR
  exact ⟨{
    lift s := (isSheaf_skyscraperPresheaf_aux R hR s).choose
    fac s j := by
      dsimp
      ext y
      simpa using (isSheaf_skyscraperPresheaf_aux R hR s).choose_spec _ y
    uniq s m hm := by
      dsimp at hm ⊢
      ext x
      obtain ⟨Y, g, hg, y, rfl⟩ := Φ.jointly_surjective _ hR x
      have := (isSheaf_skyscraperPresheaf_aux R hR s).choose_spec
        (Presieve.categoryMk _ _ hg) y
      dsimp at this
      simp [this, ← hm (op (Presieve.categoryMk _ _ hg))] }⟩

/-- Given a point `Φ` of a site `(C, J)`, this is the skyscraper sheaf functor
`A ⥤ Sheaf J A`. -/
@[simps]
noncomputable def skyscraperSheafFunctor : A ⥤ Sheaf J A where
  obj M := ⟨Φ.skyscraperPresheaf M, Φ.isSheaf_skyscraperPresheaf M⟩
  map f := ⟨Φ.skyscraperPresheafFunctor.map f⟩

/-- Given a point `Φ` on a site `(C, J)`, and an object `M` of a category `A`,
this is the skyscraper sheaf with value `M`: it sends `X : C` to the
product of copies of `M` indexed by `Φ.fiber.obj X`. -/
noncomputable abbrev skyscraperSheaf (M : A) :
    Sheaf J A :=
  Φ.skyscraperSheafFunctor.obj M

variable [HasColimitsOfSize.{w, w} A]

/-- Given a point of a site, the skyscraper sheaf functor is right adjoint
to the fiber functor on sheaves. -/
noncomputable def skyscraperSheafAdjunction :
    Φ.sheafFiber (A := A) ⊣ Φ.skyscraperSheafFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv F M :=
        Φ.skyscraperPresheafHomEquiv.trans
          ((fullyFaithfulSheafToPresheaf J A).homEquiv (Y := Φ.skyscraperSheaf M)).symm
      homEquiv_naturality_left_symm f g :=
        Φ.skyscraperPresheafHomEquiv_naturality_left_symm f.val g.val
      homEquiv_naturality_right f g := by
        ext : 1
        exact Φ.skyscraperPresheafHomEquiv_naturality_right f g }

@[simp]
lemma skyscraperSheafAdjunction_homEquiv_apply_val {F : Sheaf J A} {M : A}
    (f : Φ.presheafFiber.obj F.val ⟶ M) :
    letI e : (Φ.presheafFiber.obj F.val ⟶ M) ≃ _ := Φ.skyscraperSheafAdjunction.homEquiv F M
    letI a : F.val ⟶ Φ.skyscraperPresheaf M := (e f).val
    a = Φ.skyscraperPresheafHomEquiv f := by
  simp [skyscraperSheafAdjunction, Functor.FullyFaithful.homEquiv]

@[simp]
lemma skyscraperSheafAdjunction_homEquiv_symm_apply {F : Sheaf J A} {M : A}
    (f : F ⟶ Φ.skyscraperSheaf M) :
    letI e : (Φ.presheafFiber.obj F.val ⟶ M) ≃ _ := Φ.skyscraperSheafAdjunction.homEquiv F M
    e.symm f = Φ.skyscraperPresheafHomEquiv.symm f.val := by
  simp [skyscraperSheafAdjunction, Functor.FullyFaithful.homEquiv]

end CategoryTheory.GrothendieckTopology.Point
