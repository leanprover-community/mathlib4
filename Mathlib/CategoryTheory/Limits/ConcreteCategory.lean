/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz
-/
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.Tactic.ApplyFun

#align_import category_theory.limits.concrete_category from "leanprover-community/mathlib"@"c3019c79074b0619edb4b27553a91b2e82242395"

/-!
# Facts about (co)limits of functors into concrete categories
-/


universe w v v' u

open CategoryTheory

namespace CategoryTheory.Limits

attribute [local instance] ConcreteCategory.funLike ConcreteCategory.hasCoeToSort

section Limits

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C] {J : Type w} [Category.{v'} J]
  (F : J ⥤ C) [PreservesLimit F (forget C)] [UnivLE.{w, v}]

theorem Concrete.to_product_injective_of_isLimit {D : Cone F} (hD : IsLimit D) :
    Function.Injective fun (x : D.pt) (j : J) => D.π.app j x := by
  intro x₁ x₂ h
  apply (Types.isLimitEquivSections (isLimitOfPreserves _ hD)).injective
  ext j
  rw [Types.isLimitEquivSections_apply, Types.isLimitEquivSections_apply]
  exact congr_fun h j
#align category_theory.limits.concrete.to_product_injective_of_is_limit CategoryTheory.Limits.Concrete.to_product_injective_of_isLimit

theorem Concrete.isLimit_ext {D : Cone F} (hD : IsLimit D) (x y : D.pt) :
    (∀ j, D.π.app j x = D.π.app j y) → x = y := fun h =>
  Concrete.to_product_injective_of_isLimit _ hD (funext h)
#align category_theory.limits.concrete.is_limit_ext CategoryTheory.Limits.Concrete.isLimit_ext

theorem Concrete.limit_ext [HasLimit F] (x y : ↑(limit F)) :
    (∀ j, limit.π F j x = limit.π F j y) → x = y :=
  Concrete.isLimit_ext F (limit.isLimit _) _ _
#align category_theory.limits.concrete.limit_ext CategoryTheory.Limits.Concrete.limit_ext

section WidePullback

open WidePullback

open WidePullbackShape

theorem Concrete.widePullback_ext {B : C} {ι : Type w} {X : ι → C} (f : ∀ j : ι, X j ⟶ B)
    [HasWidePullback B X f] [PreservesLimit (wideCospan B X f) (forget C)]
    (x y : ↑(widePullback B X f)) (h₀ : base f x = base f y) (h : ∀ j, π f j x = π f j y) :
    x = y := by
  apply Concrete.limit_ext
  rintro (_ | j)
  · exact h₀
  · apply h
#align category_theory.limits.concrete.wide_pullback_ext CategoryTheory.Limits.Concrete.widePullback_ext

theorem Concrete.widePullback_ext' {B : C} {ι : Type w} [Nonempty ι] {X : ι → C}
    (f : ∀ j : ι, X j ⟶ B) [HasWidePullback.{w} B X f]
    [PreservesLimit (wideCospan B X f) (forget C)] (x y : ↑(widePullback B X f))
    (h : ∀ j, π f j x = π f j y) : x = y := by
  apply Concrete.widePullback_ext _ _ _ _ h
  inhabit ι
  simp only [← π_arrow f default, comp_apply, h]
#align category_theory.limits.concrete.wide_pullback_ext' CategoryTheory.Limits.Concrete.widePullback_ext'

end WidePullback

section Multiequalizer

theorem Concrete.multiequalizer_ext {I : MulticospanIndex.{w} C} [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] (x y : ↑(multiequalizer I))
    (h : ∀ t : I.L, Multiequalizer.ι I t x = Multiequalizer.ι I t y) : x = y := by
  apply Concrete.limit_ext
  rintro (a | b)
  · apply h
  · rw [← limit.w I.multicospan (WalkingMulticospan.Hom.fst b), comp_apply, comp_apply]
    simp [h]
#align category_theory.limits.concrete.multiequalizer_ext CategoryTheory.Limits.Concrete.multiequalizer_ext

/-- An auxiliary equivalence to be used in `multiequalizerEquiv` below.-/
def Concrete.multiequalizerEquivAux (I : MulticospanIndex C) :
    (I.multicospan ⋙ forget C).sections ≃
    { x : ∀ i : I.L, I.left i // ∀ i : I.R, I.fst i (x _) = I.snd i (x _) } where
  toFun x :=
    ⟨fun i => x.1 (WalkingMulticospan.left _), fun i => by
      have a := x.2 (WalkingMulticospan.Hom.fst i)
      have b := x.2 (WalkingMulticospan.Hom.snd i)
      rw [← b] at a
      exact a⟩
  invFun x :=
    { val := fun j =>
        match j with
        | WalkingMulticospan.left a => x.1 _
        | WalkingMulticospan.right b => I.fst b (x.1 _)
      property := by
        rintro (a | b) (a' | b') (f | f | f)
        · simp
        · rfl
        · dsimp
          exact (x.2 b').symm
        · simp }
  left_inv := by
    intro x; ext (a | b)
    · rfl
    · rw [← x.2 (WalkingMulticospan.Hom.fst b)]
      rfl
  right_inv := by
    intro x
    ext i
    rfl
#align category_theory.limits.concrete.multiequalizer_equiv_aux CategoryTheory.Limits.Concrete.multiequalizerEquivAux

/-- The equivalence between the noncomputable multiequalizer and
the concrete multiequalizer. -/
noncomputable def Concrete.multiequalizerEquiv (I : MulticospanIndex.{w} C) [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] :
    (multiequalizer I : C) ≃
      { x : ∀ i : I.L, I.left i // ∀ i : I.R, I.fst i (x _) = I.snd i (x _) } :=
  (Types.isLimitEquivSections (isLimitOfPreserves (forget C)
    (limit.isLimit I.multicospan))).trans (Concrete.multiequalizerEquivAux I)
#align category_theory.limits.concrete.multiequalizer_equiv CategoryTheory.Limits.Concrete.multiequalizerEquiv

@[simp]
theorem Concrete.multiequalizerEquiv_apply (I : MulticospanIndex.{w} C) [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] (x : ↑(multiequalizer I)) (i : I.L) :
    ((Concrete.multiequalizerEquiv I) x : ∀ i : I.L, I.left i) i = Multiequalizer.ι I i x := by
  dsimp [multiequalizerEquiv, multiequalizerEquivAux]
  apply Types.isLimitEquivSections_apply
#align category_theory.limits.concrete.multiequalizer_equiv_apply CategoryTheory.Limits.Concrete.multiequalizerEquiv_apply

end Multiequalizer

-- TODO: Add analogous lemmas about products and equalizers.
end Limits

section Colimits

-- We don't mark this as an `@[ext]` lemma as we don't always want to work elementwise.
theorem cokernel_funext {C : Type*} [Category C] [HasZeroMorphisms C] [ConcreteCategory C]
    {M N K : C} {f : M ⟶ N} [HasCokernel f] {g h : cokernel f ⟶ K}
    (w : ∀ n : N, g (cokernel.π f n) = h (cokernel.π f n)) : g = h := by
  ext x
  simpa using w x
#align category_theory.limits.cokernel_funext CategoryTheory.Limits.cokernel_funext

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C] {J : Type w} [Category.{v'} J]
  (F : J ⥤ C) [PreservesColimit F (forget C)] [UnivLE.{w, v}]

theorem Concrete.from_union_surjective_of_isColimit {D : Cocone F} (hD : IsColimit D) :
    let ff : (Σj : J, F.obj j) → D.pt := fun a => D.ι.app a.1 a.2
    Function.Surjective ff := by
  dsimp
  intro x
  obtain ⟨j, y, rfl⟩ := Types.jointly_surjective _ (isColimitOfPreserves (forget C) hD) x
  exact ⟨⟨j, y⟩, rfl⟩
#align category_theory.limits.concrete.from_union_surjective_of_is_colimit CategoryTheory.Limits.Concrete.from_union_surjective_of_isColimit

theorem Concrete.isColimit_exists_rep {D : Cocone F} (hD : IsColimit D) (x : D.pt) :
    ∃ (j : J) (y : F.obj j), D.ι.app j y = x := by
  obtain ⟨a, rfl⟩ := Concrete.from_union_surjective_of_isColimit F hD x
  exact ⟨a.1, a.2, rfl⟩
#align category_theory.limits.concrete.is_colimit_exists_rep CategoryTheory.Limits.Concrete.isColimit_exists_rep

theorem Concrete.colimit_exists_rep [HasColimit F] (x : ↑(colimit F)) :
    ∃ (j : J) (y : F.obj j), colimit.ι F j y = x :=
  Concrete.isColimit_exists_rep F (colimit.isColimit _) x
#align category_theory.limits.concrete.colimit_exists_rep CategoryTheory.Limits.Concrete.colimit_exists_rep

theorem Concrete.cocone_rep_eq_of_exists (D : Cocone F) {i j : J}
    (x : F.obj i) (y : F.obj j) (h : ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y) :
    D.ι.app i x = D.ι.app j y := by
  obtain ⟨k, f, g, eq⟩ := h
  have hf := congr_fun (Functor.congr_map (forget C) (D.ι.naturality f)) x
  have hg := congr_fun (Functor.congr_map (forget C) (D.ι.naturality g)) y
  dsimp at hf hg
  simp only [Category.comp_id] at hf hg
  refine' hf.symm.trans (Eq.trans _ hg)
  simp only [Functor.map_comp]
  change D.ι.app k (F.map f x) = D.ι.app k (F.map g y)
  rw [eq]
#align category_theory.limits.concrete.is_colimit_rep_eq_of_exists CategoryTheory.Limits.Concrete.cocone_rep_eq_of_exists

theorem Concrete.colimit_rep_eq_of_exists [HasColimit F] {i j : J} (x : F.obj i) (y : F.obj j)
    (h : ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y) :
    colimit.ι F i x = colimit.ι F j y :=
  Concrete.cocone_rep_eq_of_exists F _ x y h
#align category_theory.limits.concrete.colimit_rep_eq_of_exists CategoryTheory.Limits.Concrete.colimit_rep_eq_of_exists

section FilteredColimits

variable [IsFiltered J]

theorem Concrete.isColimit_exists_of_rep_eq {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : F.obj i) (y : F.obj j) (h : D.ι.app _ x = D.ι.app _ y) :
    ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (forget C) hD)).1 h
#align category_theory.limits.concrete.is_colimit_exists_of_rep_eq CategoryTheory.Limits.Concrete.isColimit_exists_of_rep_eq

theorem Concrete.isColimit_rep_eq_iff_exists {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : F.obj i) (y : F.obj j) :
    D.ι.app i x = D.ι.app j y ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  ⟨Concrete.isColimit_exists_of_rep_eq _ hD _ _, Concrete.cocone_rep_eq_of_exists _ D _ _⟩
#align category_theory.limits.concrete.is_colimit_rep_eq_iff_exists CategoryTheory.Limits.Concrete.isColimit_rep_eq_iff_exists

theorem Concrete.colimit_exists_of_rep_eq [HasColimit F] {i j : J} (x : F.obj i) (y : F.obj j)
    (h : colimit.ι F _ x = colimit.ι F _ y) :
    ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  Concrete.isColimit_exists_of_rep_eq F (colimit.isColimit _) x y h
#align category_theory.limits.concrete.colimit_exists_of_rep_eq CategoryTheory.Limits.Concrete.colimit_exists_of_rep_eq

theorem Concrete.colimit_rep_eq_iff_exists [HasColimit F] {i j : J} (x : F.obj i) (y : F.obj j) :
    colimit.ι F i x = colimit.ι F j y ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  ⟨Concrete.colimit_exists_of_rep_eq _ _ _, Concrete.colimit_rep_eq_of_exists _ _ _⟩
#align category_theory.limits.concrete.colimit_rep_eq_iff_exists CategoryTheory.Limits.Concrete.colimit_rep_eq_iff_exists

end FilteredColimits

section WidePushout

open WidePushout

open WidePushoutShape

theorem Concrete.widePushout_exists_rep {B : C} {α : Type _} {X : α → C} (f : ∀ j : α, B ⟶ X j)
    [HasWidePushout.{v} B X f] [PreservesColimit (wideSpan B X f) (forget C)]
    (x : ↑(widePushout B X f)) : (∃ y : B, head f y = x) ∨ ∃ (i : α) (y : X i), ι f i y = x := by
  obtain ⟨_ | j, y, rfl⟩ := Concrete.colimit_exists_rep _ x
  · left
    use y
    rfl
  · right
    use j, y
    rfl
#align category_theory.limits.concrete.wide_pushout_exists_rep CategoryTheory.Limits.Concrete.widePushout_exists_rep

theorem Concrete.widePushout_exists_rep' {B : C} {α : Type _} [Nonempty α] {X : α → C}
    (f : ∀ j : α, B ⟶ X j) [HasWidePushout.{v} B X f] [PreservesColimit (wideSpan B X f) (forget C)]
    (x : ↑(widePushout B X f)) : ∃ (i : α) (y : X i), ι f i y = x := by
  rcases Concrete.widePushout_exists_rep f x with (⟨y, rfl⟩ | ⟨i, y, rfl⟩)
  · inhabit α
    use default, f _ y
    simp only [← arrow_ι _ default, comp_apply]
  · use i, y
#align category_theory.limits.concrete.wide_pushout_exists_rep' CategoryTheory.Limits.Concrete.widePushout_exists_rep'

end WidePushout

-- TODO: Add analogous lemmas about coproducts and coequalizers.
end Colimits

end CategoryTheory.Limits
