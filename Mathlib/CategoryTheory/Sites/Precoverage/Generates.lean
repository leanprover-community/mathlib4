/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.Precoverage.Subsheaf
public import Mathlib.Logic.Small.Set

/-!
# Generators of a Grothendieck topology

Let `K` be a precoverage and `J` a Grothendieck topology on a category `C`. We
say `K` generates `J` if for every presheaf `F` on `C`, it is a sheaf for `J` if and only
if it is a sheaf for every covering in `K`.

If `K` generates `J`, then `J` is the smallest Grothendieck topology containing `K`. The converse
only holds if `K` is a coverage or a pretopology.

## Implementation details

For `C : Type u` and `Category.{v} C`, the definition of `Precoverage.Generates` quantifies over
presheafs `Cᵒᵖ ⥤ Type max u v`. We then show that this implies that the condition holds
for all presheafs `Cᵒᵖ ⥤ Type w`.
-/

@[expose] public section

universe t t' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {A : Type*} [Category* A]
  {K : Precoverage C} {J : GrothendieckTopology C}

namespace Precoverage

/-- A precoverage `K` generates the topology `J` if a presheaf on `C` is a sheaf
for `K` if and only if it is a sheaf for `J`. -/
structure Generates (K : Precoverage C) (J : GrothendieckTopology C) : Prop where
  le_toPrecoverage : K ≤ J.toPrecoverage
  isSheaf_of_forall_max (F : Cᵒᵖ ⥤ Type (max u v)) (H : ∀ ⦃X : C⦄, ∀ R ∈ K X, R.IsSheafFor F) :
    Presieve.IsSheaf J F

variable {K : Precoverage C} {J : GrothendieckTopology C}

lemma Generates.generate_mem (H : K.Generates J) {X : C} {R : Presieve X} (h : R ∈ K X) :
    .generate R ∈ J X :=
  H.le_toPrecoverage _ h

private lemma Generates.isSheaf_of_forall_aux (h : K.Generates J) (F : Cᵒᵖ ⥤ Type w)
    (H : ∀ ⦃X : C⦄, ∀ R ∈ K X, Presieve.IsSheafFor F R)
    [∀ (Z : C), _root_.Small.{max u v} (F.obj (.op Z))] :
    Presieve.IsSheaf J F := by
  intro X S hS
  let F' : Cᵒᵖ ⥤ Type max u v := FunctorToTypes.shrink F
  let e (X : C) : F.obj (.op X) ≃ F'.obj (.op X) := equivShrink _
  have he (X Y : C) (f : X ⟶ Y) (x : F.obj (.op Y)) :
      (e X) (F.map f.op x) = F'.map f.op (e Y x) := by
    simp [e, F']
  rw [Presieve.isSheafFor_iff_of_nat_equiv e he] at ⊢
  refine h.isSheaf_of_forall_max F' (fun X R hR ↦ ?_) _ hS
  rw [← Presieve.isSheafFor_iff_of_nat_equiv e he]
  exact H _ hR

/-- If `K` generates `J`, then any presheaf `Cᵒᵖ ⥤ Type w` that satisfies the sheaf
condition for all `K`-coverings, is a `J`-sheaf. -/
lemma Generates.isSheaf_of_forall (h : K.Generates J) (F : Cᵒᵖ ⥤ Type w)
    (H : ∀ ⦃X : C⦄, ∀ R ∈ K X, Presieve.IsSheafFor F R) :
    Presieve.IsSheaf J F := by
  /- By assumption, the statement holds for `w = max u v`. The idea of the proof is
  to construct a suitable `Type max u v` valued subsheaf of `F` for each covering sieve `S` in
  `J` and every family of sections over `S` to check the necessary conditions.
  We explain existence below, uniqueness works similary. -/
  intro X S hS
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨?_, ?_⟩
  · intro x t₁ t₂ ht₁ ht₂
    let 𝒮 (Z : C) : Set (F.obj (.op Z)) :=
      .range (fun (g : { g : Z ⟶ X | S.arrows g }) ↦ x _ g.2) ∪
      .range (fun (g : Z ⟶ X) ↦ F.map g.op t₁) ∪ .range (fun (g : Z ⟶ X) ↦ F.map g.op t₂)
    let Q : Subfunctor F := K.subsheafify 𝒮
    have (Z : C) : _root_.Small.{max u v} (Q.toFunctor.obj (Opposite.op Z)) :=
      small_subsheafify_of_small H _ inferInstance _
    have hQ : Presieve.IsSheaf J Q.toFunctor :=
      h.isSheaf_of_forall_aux _ fun X R hR ↦ isSheafFor_subsheafify _ hR (H _ hR)
    let x' : S.arrows.FamilyOfElements Q.toFunctor :=
      fun Z g hg ↦ ⟨x g hg, .base <| .inl <| .inl ⟨⟨g, hg⟩, rfl⟩⟩
    have ht₁' : t₁ ∈ Q.obj (.op X) := .base (.inl <| .inr ⟨𝟙 _, by simp⟩)
    have ht₂' : t₂ ∈ Q.obj (.op X) := .base (.inr ⟨𝟙 _, by simp⟩)
    have : (⟨t₁, ht₁'⟩ : Q.obj _) = ⟨t₂, ht₂'⟩ :=
      (hQ _ hS).isSeparatedFor x' ⟨_, ht₁'⟩ ⟨_, ht₂'⟩ (.of_mono Q.ι ht₁) (.of_mono Q.ι ht₂)
    simp_all
  · -- Let `x` be a compatible family of elements over `S`. We need to show it glues.
    intro x hx
    -- Let `𝒮` be the family of subsets consisting of the family of elements `x`.
    let 𝒮 (Z : C) := Set.range (fun (g : { g : Z ⟶ X | S.arrows g }) ↦ x _ g.2)
    /- Let `Q` be the smallest `K`-subsheaf of `K` containing `𝒮`. This is `max u v`-small, because
    `𝒮` is `max u v`-small. -/
    let Q : Subfunctor F := K.subsheafify 𝒮
    have (Z : C) : _root_.Small.{max u v} (Q.toFunctor.obj (Opposite.op Z)) :=
      small_subsheafify_of_small H _ inferInstance _
    have hQ : Presieve.IsSheaf J Q.toFunctor :=
      h.isSheaf_of_forall_aux _ fun X R hR ↦ isSheafFor_subsheafify _ hR (H _ hR)
    /- By assumption, `Q` is a `J`-sheaf, so the family of sections `x` glues and gives rise
    to an amalgamation of `x` in `F`. -/
    obtain ⟨t, ht, _⟩ := hQ _ hS (fun Z g hg ↦ ⟨x g hg, .base ⟨⟨g, hg⟩, rfl⟩⟩) (.of_mono Q.ι hx)
    exact ⟨t.val, ht.map Q.ι⟩

/-- If `K` generates `J`, then any presheaf is a sheaf if and only if it is a sheaf
for all `K`-covers. -/
lemma Generates.isSheaf_type_iff (H : K.Generates J) {F : Cᵒᵖ ⥤ Type w} :
    Presieve.IsSheaf J F ↔ ∀ ⦃X : C⦄, ∀ R ∈ K X, Presieve.IsSheafFor F R := by
  refine ⟨fun h X R hR ↦ ?_, fun h ↦ H.isSheaf_of_forall _ h⟩
  rw [Presieve.isSheafFor_iff_generate]
  exact h _ (H.le_toPrecoverage _ hR)

/--
If `K` generates `J`, then `J` is equal to the smallest Grothendieck topology containing `K`.
The converse is false, but holds if `K` is a coverage, see `CategoryTheory.Coverage.generates_iff`.
-/
lemma Generates.toGrothendieck_eq (H : K.Generates J) : K.toGrothendieck = J := by
  refine le_antisymm ?_ ?_
  · rw [toGrothendieck_le_iff_le_toPrecoverage]
    exact H.le_toPrecoverage
  · apply CategoryTheory.le_topology_of_closedSieves_isSheaf
    rw [H.isSheaf_type_iff]
    intro X R hR
    rw [Presieve.isSheafFor_iff_generate]
    exact classifier_isSheaf K.toGrothendieck _ (K.generate_mem_toGrothendieck hR)

lemma Generates.isSheaf_iff (H : K.Generates J) {F : Cᵒᵖ ⥤ A} :
    Presheaf.IsSheaf J F ↔ ∀ ⦃X : C⦄, ∀ R ∈ K X, ∀ (M : A),
      Presieve.IsSheafFor (F ⋙ coyoneda.obj (.op M)) R := by
  grind [Presheaf.IsSheaf, H.isSheaf_type_iff]

end Precoverage

/-- If `K` is a coverage, it generates the smallest Grothendieck topology containing `K`. -/
lemma Coverage.generates_toGrothendieck (K : Coverage C) : K.Generates K.toGrothendieck where
  le_toPrecoverage := by
    rw [← Precoverage.toGrothendieck_le_iff_le_toPrecoverage, ← toGrothendieck_toPrecoverage]
  isSheaf_of_forall_max F h := by rwa [Presieve.isSheaf_coverage]

lemma Coverage.generates_iff {K : Coverage C} : K.Generates J ↔ K.toGrothendieck = J := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [← Coverage.toGrothendieck_toPrecoverage]
    exact h.toGrothendieck_eq
  · rintro rfl
    exact Coverage.generates_toGrothendieck _

end CategoryTheory
