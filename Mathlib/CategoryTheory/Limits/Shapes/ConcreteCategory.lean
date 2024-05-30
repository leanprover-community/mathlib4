/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Scott Morrison, Adam Topaz
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.ConcreteCategory
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Limits in concrete categories

In this file, we combine the description of limits in `Types` and the API about
the preservation of products and pullbacks in order to describe these limits in a
concrete category `C`.

If `F : J → C` is a family of objects in `C`, we define a bijection
`Limits.Concrete.productEquiv F : (forget C).obj (∏ᶜ F) ≃ ∀ j, F j`.

Similarly, if `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S` are two morphisms, the elements
in `pullback f₁ f₂` are identified by `Limits.Concrete.pullbackEquiv`
to compatible tuples of elements in `X₁ × X₂`.

Some results are also obtained for the terminal object, binary products,
wide-pullbacks, wide-pushouts, multiequalizers and cokernels.

-/

universe w v u t r

namespace CategoryTheory.Limits.Concrete

attribute [local instance] ConcreteCategory.instFunLike ConcreteCategory.hasCoeToSort

variable {C : Type u} [Category.{v} C]

section Products

section ProductEquiv

variable [ConcreteCategory.{max w v} C] {J : Type w} (F : J → C)
  [HasProduct F] [PreservesLimit (Discrete.functor F) (forget C)]

/-- The equivalence `(forget C).obj (∏ᶜ F) ≃ ∀ j, F j` if `F : J → C` is a family of objects
in a concrete category `C`. -/
noncomputable def productEquiv : (forget C).obj (∏ᶜ F) ≃ ∀ j, F j :=
  ((PreservesProduct.iso (forget C) F) ≪≫ (Types.productIso.{w, v} (fun j => F j))).toEquiv

@[simp]
lemma productEquiv_apply_apply (x : (forget C).obj (∏ᶜ F)) (j : J) :
    productEquiv F x j = Pi.π F j x :=
  congr_fun (piComparison_comp_π (forget C) F j) x

@[simp]
lemma productEquiv_symm_apply_π (x : ∀ j, F j) (j : J) :
    Pi.π F j ((productEquiv F).symm x) = x j := by
  rw [← productEquiv_apply_apply, Equiv.apply_symm_apply]

end ProductEquiv

section ProductExt

variable {J : Type w} (f : J → C) [HasProduct f] {D : Type t} [Category.{r} D]
  [ConcreteCategory.{max w r} D] (F : C ⥤ D)
  [PreservesLimit (Discrete.functor f) F]
  [HasProduct fun j => F.obj (f j)]
  [PreservesLimitsOfShape WalkingCospan (forget D)]
  [PreservesLimit (Discrete.functor fun b ↦ F.toPrefunctor.obj (f b)) (forget D)]

lemma Pi.map_ext (x y : F.obj (∏ᶜ f : C))
    (h : ∀ i, F.map (Pi.π f i) x = F.map (Pi.π f i) y) : x = y := by
  apply ConcreteCategory.injective_of_mono_of_preservesPullback (PreservesProduct.iso F f).hom
  apply @Concrete.limit_ext.{w, r, t} D
    _ _ (Discrete J) _ _ _ _ (piComparison F _ x) (piComparison F _ y)
  intro ⟨(j : J)⟩
  show ((forget D).map (piComparison F f) ≫ (forget D).map (limit.π _ _)) x =
    ((forget D).map (piComparison F f) ≫ (forget D).map _) y
  rw [← (forget D).map_comp, piComparison_comp_π]
  exact h j

end ProductExt

end Products

section Terminal

variable [ConcreteCategory.{w} C]

/-- If `forget C` preserves terminals and `X` is terminal, then `(forget C).obj X` is a
singleton. -/
noncomputable def uniqueOfTerminalOfPreserves [PreservesLimit (Functor.empty.{0} C) (forget C)]
    (X : C) (h : IsTerminal X) : Unique ((forget C).obj X) :=
  Types.isTerminalEquivUnique ((forget C).obj X) <| IsTerminal.isTerminalObj (forget C) X h

/-- If `forget C` reflects terminals and `(forget C).obj X` is a singleton, then `X` is terminal. -/
noncomputable def terminalOfUniqueOfReflects [ReflectsLimit (Functor.empty.{0} C) (forget C)]
    (X : C) (h : Unique ((forget C).obj X)) : IsTerminal X :=
  IsTerminal.isTerminalOfObj (forget C) X <| (Types.isTerminalEquivUnique ((forget C).obj X)).symm h

/-- The equivalence `IsTerminal X ≃ Unique ((forget C).obj X)` if the forgetful functor
preserves and reflects terminals. -/
noncomputable def terminalIffUnique [PreservesLimit (Functor.empty.{0} C) (forget C)]
    [ReflectsLimit (Functor.empty.{0} C) (forget C)] (X : C) :
    IsTerminal X ≃ Unique ((forget C).obj X) :=
  (IsTerminal.isTerminalIffObj (forget C) X).trans <| Types.isTerminalEquivUnique _

variable (C)
variable [HasTerminal C] [PreservesLimit (Functor.empty.{0} C) (forget C)]

/-- The equivalence `(forget C).obj (⊤_ C) ≃ PUnit` when `C` is a concrete category. -/
noncomputable def terminalEquiv : (forget C).obj (⊤_ C) ≃ PUnit :=
  (PreservesTerminal.iso (forget C) ≪≫ Types.terminalIso).toEquiv

noncomputable instance : Unique ((forget C).obj (⊤_ C)) where
  default := (terminalEquiv C).symm PUnit.unit
  uniq _ := (terminalEquiv C).injective (Subsingleton.elim _ _)

end Terminal

section Initial

variable [ConcreteCategory.{w} C]

/-- If `forget C` preserves initials and `X` is initial, then `(forget C).obj X` is empty. -/
lemma empty_of_initial_of_preserves [PreservesColimit (Functor.empty.{0} C) (forget C)] (X : C)
    (h : Nonempty (IsInitial X)) : IsEmpty ((forget C).obj X) := by
  rw [← Types.initial_iff_empty]
  exact Nonempty.map (IsInitial.isInitialObj (forget C) _) h

/-- If `forget C` reflects initials and `(forget C).obj X` is empty, then `X` is initial. -/
lemma initial_of_empty_of_reflects [ReflectsColimit (Functor.empty.{0} C) (forget C)] (X : C)
    (h : IsEmpty ((forget C).obj X)) : Nonempty (IsInitial X) :=
  Nonempty.map (IsInitial.isInitialOfObj (forget C) _) <|
    (Types.initial_iff_empty ((forget C).obj X)).mpr h

/-- If `forget C` preserves and reflects initials, then `X` is initial if and only if
`(forget C).obj X` is empty. -/
lemma initial_iff_empty_of_preserves_of_reflects [PreservesColimit (Functor.empty.{0} C) (forget C)]
    [ReflectsColimit (Functor.empty.{0} C) (forget C)] (X : C) :
    Nonempty (IsInitial X) ↔ IsEmpty ((forget C).obj X) := by
  rw [← Types.initial_iff_empty, (IsInitial.isInitialIffObj (forget C) X).nonempty_congr]

end Initial

section BinaryProducts

variable [ConcreteCategory.{w} C] (X₁ X₂ : C) [HasBinaryProduct X₁ X₂]
  [PreservesLimit (pair X₁ X₂) (forget C)]

/-- The equivalence `(forget C).obj (X₁ ⨯ X₂) ≃ ((forget C).obj X₁) × ((forget C).obj X₂)`
if `X₁` and `X₂` are objects in a concrete category `C`. -/
noncomputable def prodEquiv : (forget C).obj (X₁ ⨯ X₂) ≃ X₁ × X₂ :=
  (PreservesLimitPair.iso (forget C) X₁ X₂ ≪≫ Types.binaryProductIso _ _).toEquiv

@[simp]
lemma prodEquiv_apply_fst (x : (forget C).obj (X₁ ⨯ X₂)) :
    (prodEquiv X₁ X₂ x).fst = (Limits.prod.fst : X₁ ⨯ X₂ ⟶ X₁) x :=
  congr_fun (prodComparison_fst (forget C) X₁ X₂) x

@[simp]
lemma prodEquiv_apply_snd (x : (forget C).obj (X₁ ⨯ X₂)) :
    (prodEquiv X₁ X₂ x).snd = (Limits.prod.snd : X₁ ⨯ X₂ ⟶ X₂) x :=
  congr_fun (prodComparison_snd (forget C) X₁ X₂) x

@[simp]
lemma prodEquiv_symm_apply_fst (x : X₁ × X₂) :
    (Limits.prod.fst : X₁ ⨯ X₂ ⟶ X₁) ((prodEquiv X₁ X₂).symm x) = x.1 := by
  obtain ⟨y, rfl⟩ := (prodEquiv X₁ X₂).surjective x
  simp

@[simp]
lemma prodEquiv_symm_apply_snd (x : X₁ × X₂) :
    (Limits.prod.snd : X₁ ⨯ X₂ ⟶ X₂) ((prodEquiv X₁ X₂).symm x) = x.2 := by
  obtain ⟨y, rfl⟩ := (prodEquiv X₁ X₂).surjective x
  simp

end BinaryProducts

section Pullbacks

variable [ConcreteCategory.{v} C] {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    [HasPullback f₁ f₂] [PreservesLimit (cospan f₁ f₂) (forget C)]

/-- In a concrete category `C`, given two morphisms `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S`,
the elements in `pullback f₁ f₁` can be identified to compatible tuples of
elements in `X₁` and `X₂`. -/
noncomputable def pullbackEquiv :
    (forget C).obj (pullback f₁ f₂) ≃ { p : X₁ × X₂ // f₁ p.1 = f₂ p.2 } :=
  (PreservesPullback.iso (forget C) f₁ f₂ ≪≫
    Types.pullbackIsoPullback ((forget C).map f₁) ((forget C).map f₂)).toEquiv

/-- Constructor for elements in a pullback in a concrete category. -/
noncomputable def pullbackMk (x₁ : X₁) (x₂ : X₂) (h : f₁ x₁ = f₂ x₂) :
    (forget C).obj (pullback f₁ f₂) :=
  (pullbackEquiv f₁ f₂).symm ⟨⟨x₁, x₂⟩, h⟩

lemma pullbackMk_surjective (x : (forget C).obj (pullback f₁ f₂)) :
    ∃ (x₁ : X₁) (x₂ : X₂) (h : f₁ x₁ = f₂ x₂), x = pullbackMk f₁ f₂ x₁ x₂ h := by
  obtain ⟨⟨⟨x₁, x₂⟩, h⟩, rfl⟩ := (pullbackEquiv f₁ f₂).symm.surjective x
  exact ⟨x₁, x₂, h, rfl⟩

@[simp]
lemma pullbackMk_fst (x₁ : X₁) (x₂ : X₂) (h : f₁ x₁ = f₂ x₂) :
    @pullback.fst _ _ _ _ _ f₁ f₂ _ (pullbackMk f₁ f₂ x₁ x₂ h) = x₁ :=
  (congr_fun (PreservesPullback.iso_inv_fst (forget C) f₁ f₂) _).trans
    (congr_fun (Types.pullbackIsoPullback_inv_fst ((forget C).map f₁) ((forget C).map f₂)) _)

@[simp]
lemma pullbackMk_snd (x₁ : X₁) (x₂ : X₂) (h : f₁ x₁ = f₂ x₂) :
    @pullback.snd _ _ _ _ _ f₁ f₂ _ (pullbackMk f₁ f₂ x₁ x₂ h) = x₂ :=
  (congr_fun (PreservesPullback.iso_inv_snd (forget C) f₁ f₂) _).trans
    (congr_fun (Types.pullbackIsoPullback_inv_snd ((forget C).map f₁) ((forget C).map f₂)) _)

end Pullbacks

section WidePullback

variable [ConcreteCategory.{max w v} C]

open WidePullback

open WidePullbackShape

theorem widePullback_ext {B : C} {ι : Type w} {X : ι → C} (f : ∀ j : ι, X j ⟶ B)
    [HasWidePullback B X f] [PreservesLimit (wideCospan B X f) (forget C)]
    (x y : ↑(widePullback B X f)) (h₀ : base f x = base f y) (h : ∀ j, π f j x = π f j y) :
    x = y := by
  apply Concrete.limit_ext
  rintro (_ | j)
  · exact h₀
  · apply h
#align category_theory.limits.concrete.wide_pullback_ext CategoryTheory.Limits.Concrete.widePullback_ext

theorem widePullback_ext' {B : C} {ι : Type w} [Nonempty ι] {X : ι → C}
    (f : ∀ j : ι, X j ⟶ B) [HasWidePullback.{w} B X f]
    [PreservesLimit (wideCospan B X f) (forget C)] (x y : ↑(widePullback B X f))
    (h : ∀ j, π f j x = π f j y) : x = y := by
  apply Concrete.widePullback_ext _ _ _ _ h
  inhabit ι
  simp only [← π_arrow f default, comp_apply, h]
#align category_theory.limits.concrete.wide_pullback_ext' CategoryTheory.Limits.Concrete.widePullback_ext'

end WidePullback

section Multiequalizer

variable [ConcreteCategory.{max w v} C]

theorem multiequalizer_ext {I : MulticospanIndex.{w} C} [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] (x y : ↑(multiequalizer I))
    (h : ∀ t : I.L, Multiequalizer.ι I t x = Multiequalizer.ι I t y) : x = y := by
  apply Concrete.limit_ext
  rintro (a | b)
  · apply h
  · rw [← limit.w I.multicospan (WalkingMulticospan.Hom.fst b), comp_apply, comp_apply]
    simp [h]
#align category_theory.limits.concrete.multiequalizer_ext CategoryTheory.Limits.Concrete.multiequalizer_ext

/-- An auxiliary equivalence to be used in `multiequalizerEquiv` below. -/
def multiequalizerEquivAux (I : MulticospanIndex C) :
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
noncomputable def multiequalizerEquiv (I : MulticospanIndex.{w} C) [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] :
    (multiequalizer I : C) ≃
      { x : ∀ i : I.L, I.left i // ∀ i : I.R, I.fst i (x _) = I.snd i (x _) } :=
  letI h1 := limit.isLimit I.multicospan
  letI h2 := isLimitOfPreserves (forget C) h1
  letI E := h2.conePointUniqueUpToIso (Types.limitConeIsLimit.{w, v} _)
  Equiv.trans E.toEquiv (Concrete.multiequalizerEquivAux.{w, v} I)
#align category_theory.limits.concrete.multiequalizer_equiv CategoryTheory.Limits.Concrete.multiequalizerEquiv

@[simp]
theorem multiequalizerEquiv_apply (I : MulticospanIndex.{w} C) [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] (x : ↑(multiequalizer I)) (i : I.L) :
    ((Concrete.multiequalizerEquiv I) x : ∀ i : I.L, I.left i) i = Multiequalizer.ι I i x :=
  rfl
#align category_theory.limits.concrete.multiequalizer_equiv_apply CategoryTheory.Limits.Concrete.multiequalizerEquiv_apply

end Multiequalizer

section WidePushout

open WidePushout

open WidePushoutShape

variable [ConcreteCategory.{v} C]

theorem widePushout_exists_rep {B : C} {α : Type _} {X : α → C} (f : ∀ j : α, B ⟶ X j)
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

theorem widePushout_exists_rep' {B : C} {α : Type _} [Nonempty α] {X : α → C}
    (f : ∀ j : α, B ⟶ X j) [HasWidePushout.{v} B X f] [PreservesColimit (wideSpan B X f) (forget C)]
    (x : ↑(widePushout B X f)) : ∃ (i : α) (y : X i), ι f i y = x := by
  rcases Concrete.widePushout_exists_rep f x with (⟨y, rfl⟩ | ⟨i, y, rfl⟩)
  · inhabit α
    use default, f _ y
    simp only [← arrow_ι _ default, comp_apply]
  · use i, y
#align category_theory.limits.concrete.wide_pushout_exists_rep' CategoryTheory.Limits.Concrete.widePushout_exists_rep'

end WidePushout

-- We don't mark this as an `@[ext]` lemma as we don't always want to work elementwise.
theorem cokernel_funext {C : Type*} [Category C] [HasZeroMorphisms C] [ConcreteCategory C]
    {M N K : C} {f : M ⟶ N} [HasCokernel f] {g h : cokernel f ⟶ K}
    (w : ∀ n : N, g (cokernel.π f n) = h (cokernel.π f n)) : g = h := by
  ext x
  simpa using w x
#align category_theory.limits.cokernel_funext CategoryTheory.Limits.Concrete.cokernel_funext

-- TODO: Add analogous lemmas about coproducts and coequalizers.

end CategoryTheory.Limits.Concrete
