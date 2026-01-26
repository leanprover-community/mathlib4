/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# The equalizer of two morphisms of functors, as a subfunctor

If `F₁` and `F₂` are type-valued functors, `A : Subfunctor F₁`, and
`f` and `g` are two morphisms `A.toFunctor ⟶ F₂`, we introduce
`Subcomplex.equalizer f g`, which is the subfunctor of `F₁` contained in `A`
where `f` and `g` coincide.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {F₁ F₂ : C ⥤ Type w} {A : Subfunctor F₁}
  (f g : A.toFunctor ⟶ F₂)

namespace Subfunctor

/-- The equalizer of two morphisms of type-valued functors of types of the form
`A.toFunctor ⟶ F₂` with `A : Subfunctor F₁`, as a subcomplex of `F₁`. -/
@[simps -isSimp]
protected def equalizer : Subfunctor F₁ where
  obj U := setOf (fun x ↦ ∃ (hx : x ∈ A.obj _), f.app _ ⟨x, hx⟩ = g.app _ ⟨x, hx⟩)
  map φ x := by
    rintro ⟨hx, h⟩
    exact ⟨A.map _ hx,
      (FunctorToTypes.naturality _ _ f φ ⟨x, hx⟩).trans (Eq.trans (by rw [h])
        (FunctorToTypes.naturality _ _ g φ ⟨x, hx⟩).symm)⟩

attribute [local simp] equalizer_obj

lemma equalizer_le : Subfunctor.equalizer f g ≤ A :=
  fun _ _ h ↦ h.1

@[simp]
lemma equalizer_self : Subfunctor.equalizer f f = A := by aesop

lemma mem_equalizer_iff {i : C} (x : A.toFunctor.obj i) :
    x.1 ∈ (Subfunctor.equalizer f g).obj i ↔ f.app i x = g.app i x := by
  simp

lemma range_le_equalizer_iff {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor) :
    range (φ ≫ A.ι) ≤ Subfunctor.equalizer f g ↔ φ ≫ f = φ ≫ g := by
  rw [NatTrans.ext_iff]
  simp [le_def, Set.subset_def, funext_iff, CategoryTheory.types_ext_iff]

lemma equalizer_eq_iff :
    Subfunctor.equalizer f g = A ↔ f = g := by
  have := range_le_equalizer_iff f g (𝟙 _)
  simp only [Category.id_comp, range_ι] at this
  rw [← this]
  constructor
  · intro h
    rw [h]
  · intro h
    exact le_antisymm (equalizer_le f g) h

/-- Given two morphisms `f` and `g` in `A.toFunctor ⟶ F₂`, this is the monomorphism
of functors corresponding to the inclusion `Subfunctor.equalizer f g ≤ A`. -/
def equalizer.ι : (Subfunctor.equalizer f g).toFunctor ⟶ A.toFunctor :=
  homOfLe (equalizer_le f g)

instance : Mono (equalizer.ι f g) := by
  dsimp [equalizer.ι]
  infer_instance

@[reassoc (attr := simp)]
lemma equalizer.ι_ι : equalizer.ι f g ≫ A.ι = (Subfunctor.equalizer f g).ι := rfl

@[reassoc]
lemma equalizer.condition : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g := by
  simp [← range_le_equalizer_iff]

/-- Given two morphisms `f` and `g` in `A.toFunctor ⟶ F₂`, if `φ : G ⟶ A.toFunctor`
is such that `φ ≫ f = φ ≫ g`, then this is the lifted morphism
`G ⟶ (Subfunctor.equalizer f g).toFunctor`. This is part of the universal
property of the equalizer that is satisfied by
the functor `(Subfunctor.equalizer f g).toFunctor`. -/
def equalizer.lift {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor)
    (w : φ ≫ f = φ ≫ g) :
    G ⟶ (Subfunctor.equalizer f g).toFunctor :=
  Subfunctor.lift (φ ≫ A.ι) (by simpa only [range_le_equalizer_iff] using w)

@[reassoc (attr := simp)]
lemma equalizer.lift_ι' {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor)
    (w : φ ≫ f = φ ≫ g) :
    equalizer.lift f g φ w ≫ (Subfunctor.equalizer f g).ι = φ ≫ A.ι :=
  rfl

@[reassoc (attr := simp)]
lemma equalizer.lift_ι {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor)
    (w : φ ≫ f = φ ≫ g) :
    equalizer.lift f g φ w ≫ equalizer.ι f g = φ :=
  rfl

/-- The (limit) fork which expresses `(Subfunctor.equalizer f g).toFunctor` as
the equalizer of `f` and `g`. -/
@[simps! pt]
def equalizer.fork : Limits.Fork f g :=
  Limits.Fork.ofι (equalizer.ι f g) (equalizer.condition f g)

@[simp]
lemma equalizer.fork_ι :
    (equalizer.fork f g).ι = equalizer.ι f g := rfl

/-- `(Subfunctor.equalizer f g).toFunctor` is the equalizer of `f` and `g`. -/
def equalizer.forkIsLimit : Limits.IsLimit (equalizer.fork f g) :=
  Limits.Fork.IsLimit.mk _
    (fun s ↦ equalizer.lift _ _ s.ι s.condition)
    (fun s ↦ by dsimp)
    (fun s m hm ↦ by simp [← cancel_mono (Subfunctor.equalizer f g).ι, ← hm])

@[deprecated (since := "2025-12-11")] alias Subpresheaf.equalizer := Subfunctor.equalizer
@[deprecated (since := "2025-12-11")] alias Subpresheaf.equalizer_le := equalizer_le
@[deprecated (since := "2025-12-11")] alias Subpresheaf.equalizer_self := equalizer_self
@[deprecated (since := "2025-12-11")] alias Subpresheaf.mem_equalizer_iff := mem_equalizer_iff
@[deprecated (since := "2025-12-11")] alias Subpresheaf.range_le_equalizer_iff :=
  range_le_equalizer_iff
@[deprecated (since := "2025-12-11")] alias Subpresheaf.equalizer_eq_iff := equalizer_eq_iff
@[deprecated (since := "2025-12-11")] alias Subpresheaf.equalizer.ι := equalizer.ι
@[deprecated (since := "2025-12-11")] alias Subpresheaf.equalizer.ι_ι := equalizer.ι_ι
@[deprecated (since := "2025-12-11")] alias Subpresheaf.equalizer.condition := equalizer.condition
@[deprecated (since := "2025-12-11")] alias Subpresheaf.equalizer.lift := equalizer.lift
@[deprecated (since := "2025-12-11")] alias Subpresheaf.equalizer.lift_ι' := equalizer.lift_ι'
@[deprecated (since := "2025-12-11")] alias Subpresheaf.equalizer.lift_ι := equalizer.lift_ι
@[deprecated (since := "2025-12-11")] alias Subpresheaf.equalizer.fork := equalizer.fork
@[deprecated (since := "2025-12-11")] alias Subpresheaf.equalizer.fork_ι := equalizer.fork_ι
@[deprecated (since := "2025-12-11")] alias Subpresheaf.equalizer.forkIsLimit :=
  equalizer.forkIsLimit

end Subfunctor

end CategoryTheory
