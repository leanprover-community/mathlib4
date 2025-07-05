/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kim Morrison, Adam Topaz
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Shapes
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Limits in concrete categories

In this file, we combine the description of limits in `Types` and the API about
the preservation of products and pullbacks in order to describe these limits in a
concrete category `C`.

If `F : J → C` is a family of objects in `C`, we define a bijection
`Limits.Concrete.productEquiv F : ToType (∏ᶜ F) ≃ ∀ j, ToType (F j)`.

Similarly, if `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S` are two morphisms, the elements
in `pullback f₁ f₂` are identified by `Limits.Concrete.pullbackEquiv`
to compatible tuples of elements in `X₁ × X₂`.

Some results are also obtained for the terminal object, binary products,
wide-pullbacks, wide-pushouts, multiequalizers and cokernels.

-/

universe s w w' v u t r

namespace CategoryTheory.Limits.Concrete

variable {C : Type u} [Category.{v} C]

section Products

section ProductEquiv

variable {FC : C → C → Type*} {CC : C → Type max w v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{max w v} C FC] {J : Type w} (F : J → C)
  [HasProduct F] [PreservesLimit (Discrete.functor F) (forget C)]

/-- The equivalence `ToType (∏ᶜ F) ≃ ∀ j, ToType (F j)` if `F : J → C` is a family of objects
in a concrete category `C`. -/
noncomputable def productEquiv : ToType (∏ᶜ F) ≃ ∀ j, ToType (F j) :=
  ((PreservesProduct.iso (forget C) F) ≪≫ (Types.productIso.{w, v} fun j => ToType (F j))).toEquiv

@[simp]
lemma productEquiv_apply_apply (x : ToType (∏ᶜ F)) (j : J) :
    productEquiv F x j = Pi.π F j x :=
  congr_fun (piComparison_comp_π (forget C) F j) x

@[simp]
lemma productEquiv_symm_apply_π (x : ∀ j, ToType (F j)) (j : J) :
    Pi.π F j ((productEquiv F).symm x) = x j := by
  rw [← productEquiv_apply_apply, Equiv.apply_symm_apply]

end ProductEquiv

section ProductExt

variable {J : Type w} (f : J → C) [HasProduct f] {D : Type t} [Category.{r} D]
variable {FD : D → D → Type*} {DD : D → Type max w r} [∀ X Y, FunLike (FD X Y) (DD X) (DD Y)]
variable [ConcreteCategory.{max w r} D FD] (F : C ⥤ D)
  [PreservesLimit (Discrete.functor f) F]
  [HasProduct fun j => F.obj (f j)]
  [PreservesLimitsOfShape WalkingCospan (forget D)]
  [PreservesLimit (Discrete.functor fun b ↦ F.toPrefunctor.obj (f b)) (forget D)]

lemma Pi.map_ext (x y : ToType (F.obj (∏ᶜ f : C)))
    (h : ∀ i, F.map (Pi.π f i) x = F.map (Pi.π f i) y) : x = y := by
  apply ConcreteCategory.injective_of_mono_of_preservesPullback (PreservesProduct.iso F f).hom
  apply Concrete.limit_ext _ (piComparison F _ x) (piComparison F _ y)
  intro ⟨j⟩
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, piComparison_comp_π]
  exact h j

end ProductExt

end Products

section Terminal

variable {FC : C → C → Type*} {CC : C → Type w} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{w} C FC]

/-- If `forget C` preserves terminals and `X` is terminal, then `ToType X` is a
singleton. -/
noncomputable def uniqueOfTerminalOfPreserves [PreservesLimit (Functor.empty.{0} C) (forget C)]
    (X : C) (h : IsTerminal X) : Unique (ToType X) :=
  Types.isTerminalEquivUnique (ToType X) <| IsTerminal.isTerminalObj (forget C) X h

/-- If `forget C` reflects terminals and `ToType X` is a singleton, then `X` is terminal. -/
noncomputable def terminalOfUniqueOfReflects [ReflectsLimit (Functor.empty.{0} C) (forget C)]
    (X : C) (h : Unique (ToType X)) : IsTerminal X :=
  IsTerminal.isTerminalOfObj (forget C) X <| (Types.isTerminalEquivUnique (ToType X)).symm h

/-- The equivalence `IsTerminal X ≃ Unique (ToType X)` if the forgetful functor
preserves and reflects terminals. -/
noncomputable def terminalIffUnique [PreservesLimit (Functor.empty.{0} C) (forget C)]
    [ReflectsLimit (Functor.empty.{0} C) (forget C)] (X : C) :
    IsTerminal X ≃ Unique (ToType X) :=
  (IsTerminal.isTerminalIffObj (forget C) X).trans <| Types.isTerminalEquivUnique _

variable (C)
variable [HasTerminal C] [PreservesLimit (Functor.empty.{0} C) (forget C)]

/-- The equivalence `ToType (⊤_ C) ≃ PUnit` when `C` is a concrete category. -/
noncomputable def terminalEquiv : ToType (⊤_ C) ≃ PUnit :=
  (PreservesTerminal.iso (forget C) ≪≫ Types.terminalIso).toEquiv

noncomputable instance : Unique (ToType (⊤_ C)) where
  default := (terminalEquiv C).symm PUnit.unit
  uniq _ := (terminalEquiv C).injective (Subsingleton.elim _ _)

end Terminal

section Initial

variable {FC : C → C → Type*} {CC : C → Type w} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{w} C FC]

/-- If `forget C` preserves initials and `X` is initial, then `ToType X` is empty. -/
lemma empty_of_initial_of_preserves [PreservesColimit (Functor.empty.{0} C) (forget C)] (X : C)
    (h : Nonempty (IsInitial X)) : IsEmpty (ToType X) := by
  rw [← Types.initial_iff_empty]
  exact Nonempty.map (IsInitial.isInitialObj (forget C) _) h

/-- If `forget C` reflects initials and `ToType X` is empty, then `X` is initial. -/
lemma initial_of_empty_of_reflects [ReflectsColimit (Functor.empty.{0} C) (forget C)] (X : C)
    (h : IsEmpty (ToType X)) : Nonempty (IsInitial X) :=
  Nonempty.map (IsInitial.isInitialOfObj (forget C) _) <|
    (Types.initial_iff_empty (ToType X)).mpr h

/-- If `forget C` preserves and reflects initials, then `X` is initial if and only if
`ToType X` is empty. -/
lemma initial_iff_empty_of_preserves_of_reflects [PreservesColimit (Functor.empty.{0} C) (forget C)]
    [ReflectsColimit (Functor.empty.{0} C) (forget C)] (X : C) :
    Nonempty (IsInitial X) ↔ IsEmpty (ToType X) := by
  rw [← Types.initial_iff_empty, (IsInitial.isInitialIffObj (forget C) X).nonempty_congr]
  rfl

end Initial

section BinaryProducts

variable {FC : C → C → Type*} {CC : C → Type w} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{w} C FC] (X₁ X₂ : C) [HasBinaryProduct X₁ X₂]
  [PreservesLimit (pair X₁ X₂) (forget C)]

/-- The equivalence `ToType (X₁ ⨯ X₂) ≃ (ToType X₁) × (ToType X₂)`
if `X₁` and `X₂` are objects in a concrete category `C`. -/
noncomputable def prodEquiv : ToType (X₁ ⨯ X₂) ≃ ToType X₁ × ToType X₂ :=
  (PreservesLimitPair.iso (forget C) X₁ X₂ ≪≫ Types.binaryProductIso _ _).toEquiv

@[simp]
lemma prodEquiv_apply_fst (x : ToType (X₁ ⨯ X₂)) :
    (prodEquiv X₁ X₂ x).fst = (Limits.prod.fst : X₁ ⨯ X₂ ⟶ X₁) x :=
  congr_fun (prodComparison_fst (forget C) X₁ X₂) x

@[simp]
lemma prodEquiv_apply_snd (x : ToType (X₁ ⨯ X₂)) :
    (prodEquiv X₁ X₂ x).snd = (Limits.prod.snd : X₁ ⨯ X₂ ⟶ X₂) x :=
  congr_fun (prodComparison_snd (forget C) X₁ X₂) x

@[simp]
lemma prodEquiv_symm_apply_fst (x : ToType X₁ × ToType X₂) :
    (Limits.prod.fst : X₁ ⨯ X₂ ⟶ X₁) ((prodEquiv X₁ X₂).symm x) = x.1 := by
  obtain ⟨y, rfl⟩ := (prodEquiv X₁ X₂).surjective x
  simp

@[simp]
lemma prodEquiv_symm_apply_snd (x : ToType X₁ × ToType X₂) :
    (Limits.prod.snd : X₁ ⨯ X₂ ⟶ X₂) ((prodEquiv X₁ X₂).symm x) = x.2 := by
  obtain ⟨y, rfl⟩ := (prodEquiv X₁ X₂).surjective x
  simp

end BinaryProducts

section Pullbacks

variable {FC : C → C → Type*} {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{v} C FC]
variable {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    [HasPullback f₁ f₂] [PreservesLimit (cospan f₁ f₂) (forget C)]

/-- In a concrete category `C`, given two morphisms `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S`,
the elements in `pullback f₁ f₁` can be identified to compatible tuples of
elements in `X₁` and `X₂`. -/
noncomputable def pullbackEquiv :
    ToType (pullback f₁ f₂) ≃ { p : ToType X₁ × ToType X₂ // f₁ p.1 = f₂ p.2 } :=
  (PreservesPullback.iso (forget C) f₁ f₂ ≪≫
    Types.pullbackIsoPullback ⇑(ConcreteCategory.hom f₁) ⇑(ConcreteCategory.hom f₂)).toEquiv

/-- Constructor for elements in a pullback in a concrete category. -/
noncomputable def pullbackMk (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂) :
    ToType (pullback f₁ f₂) :=
  (pullbackEquiv f₁ f₂).symm ⟨⟨x₁, x₂⟩, h⟩

lemma pullbackMk_surjective (x : ToType (pullback f₁ f₂)) :
    ∃ (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂), x = pullbackMk f₁ f₂ x₁ x₂ h := by
  obtain ⟨⟨⟨x₁, x₂⟩, h⟩, rfl⟩ := (pullbackEquiv f₁ f₂).symm.surjective x
  exact ⟨x₁, x₂, h, rfl⟩

@[simp]
lemma pullbackMk_fst (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂) :
    pullback.fst f₁ f₂ (pullbackMk f₁ f₂ x₁ x₂ h) = x₁ :=
  (congr_fun (PreservesPullback.iso_inv_fst (forget C) f₁ f₂) _).trans
    (congr_fun (Types.pullbackIsoPullback_inv_fst ⇑(ConcreteCategory.hom f₁)
      ⇑(ConcreteCategory.hom f₂)) _)

@[simp]
lemma pullbackMk_snd (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂) :
    pullback.snd f₁ f₂ (pullbackMk f₁ f₂ x₁ x₂ h) = x₂ :=
  (congr_fun (PreservesPullback.iso_inv_snd (forget C) f₁ f₂) _).trans
    (congr_fun (Types.pullbackIsoPullback_inv_snd ⇑(ConcreteCategory.hom f₁)
      ⇑(ConcreteCategory.hom f₂)) _)

end Pullbacks

section WidePullback

variable {FC : C → C → Type*} {CC : C → Type (max v w)} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{max v w} C FC]

open WidePullback

open WidePullbackShape

theorem widePullback_ext {B : C} {ι : Type w} {X : ι → C} (f : ∀ j : ι, X j ⟶ B)
    [HasWidePullback B X f] [PreservesLimit (wideCospan B X f) (forget C)]
    (x y : ToType (widePullback B X f)) (h₀ : base f x = base f y) (h : ∀ j, π f j x = π f j y) :
    x = y := by
  apply Concrete.limit_ext
  rintro (_ | j)
  · exact h₀
  · apply h

theorem widePullback_ext' {B : C} {ι : Type w} [Nonempty ι] {X : ι → C}
    (f : ∀ j : ι, X j ⟶ B) [HasWidePullback.{w} B X f]
    [PreservesLimit (wideCospan B X f) (forget C)] (x y : ToType (widePullback B X f))
    (h : ∀ j, π f j x = π f j y) : x = y := by
  apply Concrete.widePullback_ext _ _ _ _ h
  inhabit ι
  simp only [← π_arrow f default, ConcreteCategory.comp_apply, h]

end WidePullback

section Multiequalizer

variable {FC : C → C → Type*} {CC : C → Type s} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{s} C FC]

theorem multiequalizer_ext {J : MulticospanShape.{w, w'}}
    {I : MulticospanIndex J C} [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] (x y : ToType (multiequalizer I))
    (h : ∀ t : J.L, Multiequalizer.ι I t x = Multiequalizer.ι I t y) : x = y := by
  apply Concrete.limit_ext
  rintro (a | b)
  · apply h
  · rw [← limit.w I.multicospan (WalkingMulticospan.Hom.fst b), ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply]
    simp [h]

/-- An auxiliary equivalence to be used in `multiequalizerEquiv` below. -/
def multiequalizerEquivAux {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C) :
    (I.multicospan ⋙ forget C).sections ≃
    { x : ∀ i : J.L, ToType (I.left i) // ∀ i : J.R, I.fst i (x _) = I.snd i (x _) } where
  toFun x :=
    ⟨fun _ => x.1 (WalkingMulticospan.left _), fun i => by
      have a := x.2 (WalkingMulticospan.Hom.fst i)
      have b := x.2 (WalkingMulticospan.Hom.snd i)
      rw [← b] at a
      exact a⟩
  invFun x :=
    { val := fun j =>
        match j with
        | WalkingMulticospan.left _ => x.1 _
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

/-- The equivalence between the noncomputable multiequalizer and
the concrete multiequalizer. -/
noncomputable def multiequalizerEquiv {J : MulticospanShape.{w, w'}}
    (I : MulticospanIndex J C) [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] :
    ToType (multiequalizer I) ≃
      { x : ∀ i : J.L, ToType (I.left i) // ∀ i : J.R, I.fst i (x _) = I.snd i (x _) } :=
  letI h1 := limit.isLimit I.multicospan
  letI h2 := isLimitOfPreserves (forget C) h1
  (Types.isLimitEquivSections h2).trans (Concrete.multiequalizerEquivAux I)

@[simp]
theorem multiequalizerEquiv_apply {J : MulticospanShape.{w, w'}}
    (I : MulticospanIndex J C) [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] (x : ToType (multiequalizer I)) (i : J.L) :
    ((Concrete.multiequalizerEquiv I) x : ∀ i : J.L, ToType (I.left i)) i =
      Multiequalizer.ι I i x :=
  rfl

end Multiequalizer

section WidePushout

open WidePushout

open WidePushoutShape

variable {FC : C → C → Type*} {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{v} C FC]

theorem widePushout_exists_rep {B : C} {α : Type _} {X : α → C} (f : ∀ j : α, B ⟶ X j)
    [HasWidePushout.{v} B X f] [PreservesColimit (wideSpan B X f) (forget C)]
    (x : ToType (widePushout B X f)) :
    (∃ y : ToType B, head f y = x) ∨ ∃ (i : α) (y : ToType (X i)), ι f i y = x := by
  obtain ⟨_ | j, y, rfl⟩ := Concrete.colimit_exists_rep _ x
  · left
    use y
    rfl
  · right
    use j, y
    rfl

theorem widePushout_exists_rep' {B : C} {α : Type _} [Nonempty α] {X : α → C}
    (f : ∀ j : α, B ⟶ X j) [HasWidePushout.{v} B X f] [PreservesColimit (wideSpan B X f) (forget C)]
    (x : ToType (widePushout B X f)) : ∃ (i : α) (y : ToType (X i)), ι f i y = x := by
  rcases Concrete.widePushout_exists_rep f x with (⟨y, rfl⟩ | ⟨i, y, rfl⟩)
  · inhabit α
    use default, f _ y
    simp only [← arrow_ι _ default, ConcreteCategory.comp_apply]
  · use i, y

end WidePushout

attribute [local ext] ConcreteCategory.hom_ext in
-- We don't mark this as an `@[ext]` lemma as we don't always want to work elementwise.
theorem cokernel_funext {C : Type*} [Category C] [HasZeroMorphisms C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {M N K : C} {f : M ⟶ N} [HasCokernel f] {g h : cokernel f ⟶ K}
    (w : ∀ n : ToType N, g (cokernel.π f n) = h (cokernel.π f n)) : g = h := by
  ext x
  simpa using w x

-- TODO: Add analogous lemmas about coproducts and coequalizers.

end CategoryTheory.Limits.Concrete
