/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Adam Topaz
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Images
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Facts about (co)limits of functors into concrete categories
-/


universe s t w v u r

open CategoryTheory

namespace CategoryTheory.Types

open Limits

/-! The forgetful functor on `Type u` is the identity; copy the instances on `𝟭 (Type u)`
over to `forget (Type u)`.

We currently have two instances for `HasForget (Type u)`:

* A global `HasForget` instance where `forget (Type u)` reduces to `𝟭 Type`
* A locally enabled `ConcreteCategory` where `forget (Type u)` is only reducible-with-instances
  equal to `𝟭 Type`.

Since instance synthesis only looks through reducible definitions, we need to help it out by copying
over the instances that wouldn't be found otherwise.
-/

attribute [local instance] Types.instFunLike Types.instConcreteCategory

instance : (@forget (Type u) _ ConcreteCategory.toHasForget).Full :=
  Functor.Full.id

instance : PreservesLimitsOfSize (@forget (Type u) _ ConcreteCategory.toHasForget) :=
  id_preservesLimitsOfSize
instance : PreservesColimitsOfSize (@forget (Type u) _ ConcreteCategory.toHasForget) :=
  id_preservesColimitsOfSize

instance : ReflectsLimitsOfSize (@forget (Type u) _ ConcreteCategory.toHasForget) :=
  id_reflectsLimits
instance : ReflectsColimitsOfSize (@forget (Type u) _ ConcreteCategory.toHasForget) :=
  id_reflectsColimits

instance : (@forget (Type u) _ ConcreteCategory.toHasForget).IsEquivalence :=
  Functor.isEquivalence_refl

instance : (@forget (Type u) _ ConcreteCategory.toHasForget).IsCorepresentable :=
  instIsCorepresentableIdType

end CategoryTheory.Types

namespace CategoryTheory.Limits.Concrete

section Limits

/-- If a functor `G : J ⥤ C` to a concrete category has a limit and that `forget C`
is corepresentable, then `(G ⋙ forget C).sections` is small. -/
lemma small_sections_of_hasLimit
    {C : Type u} [Category.{v} C] [HasForget.{v} C]
    [(forget C).IsCorepresentable] {J : Type w} [Category.{t} J] (G : J ⥤ C) [HasLimit G] :
    Small.{v} (G ⋙ forget C).sections := by
  rw [← Types.hasLimit_iff_small_sections]
  infer_instance

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type r}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{r} C FC]
variable {J : Type w} [Category.{t} J] (F : J ⥤ C) [PreservesLimit F (forget C)]

theorem to_product_injective_of_isLimit
    {D : Cone F} (hD : IsLimit D) :
    Function.Injective fun (x : ToType D.pt) (j : J) => D.π.app j x := by
  let E := (forget C).mapCone D
  intro (x : E.pt) y H
  apply (Types.isLimitEquivSections (isLimitOfPreserves _ hD)).injective
  ext j
  exact funext_iff.mp H j

theorem isLimit_ext {D : Cone F} (hD : IsLimit D) (x y : ToType D.pt) :
    (∀ j, D.π.app j x = D.π.app j y) → x = y := fun h =>
  Concrete.to_product_injective_of_isLimit _ hD (funext h)

theorem limit_ext [HasLimit F] (x y : ToType (limit F)) :
    (∀ j, limit.π F j x = limit.π F j y) → x = y :=
  Concrete.isLimit_ext F (limit.isLimit _) _ _

section Surjective

/--
Given surjections `⋯ ⟶ Xₙ₊₁ ⟶ Xₙ ⟶ ⋯ ⟶ X₀` in a concrete category whose forgetful functor
preserves sequential limits, the projection map `lim Xₙ ⟶ X₀` is surjective.
-/
lemma surjective_π_app_zero_of_surjective_map {C : Type u} [Category.{v} C] {FC : C → C → Type*}
    {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
    [PreservesLimitsOfShape ℕᵒᵖ (forget C)] {F : ℕᵒᵖ ⥤ C} {c : Cone F}
    (hc : IsLimit c) (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) :
    Function.Surjective (c.π.app ⟨0⟩) :=
  Types.surjective_π_app_zero_of_surjective_map (isLimitOfPreserves (forget C) hc) hF

end Surjective

end Limits

section Colimits

section

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type t}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{t} C FC]
variable {J : Type w} [Category.{r} J] (F : J ⥤ C)

section
variable [PreservesColimit F (forget C)]

theorem from_union_surjective_of_isColimit {D : Cocone F} (hD : IsColimit D) :
    let ff : (Σ j : J, ToType (F.obj j)) → ToType D.pt := fun a => D.ι.app a.1 a.2
    Function.Surjective ff := by
  intro ff x
  let E : Cocone (F ⋙ forget C) := (forget C).mapCocone D
  let hE : IsColimit E := isColimitOfPreserves (forget C) hD
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hE x
  exact ⟨⟨j, y⟩, hy⟩

theorem isColimit_exists_rep {D : Cocone F} (hD : IsColimit D) (x : ToType D.pt) :
    ∃ (j : J) (y : ToType (F.obj j)), D.ι.app j y = x := by
  obtain ⟨a, rfl⟩ := Concrete.from_union_surjective_of_isColimit F hD x
  exact ⟨a.1, a.2, rfl⟩

theorem colimit_exists_rep [HasColimit F] (x : ToType (colimit F)) :
    ∃ (j : J) (y : ToType (F.obj j)), colimit.ι F j y = x :=
  Concrete.isColimit_exists_rep F (colimit.isColimit _) x

end

theorem isColimit_rep_eq_of_exists {D : Cocone F} {i j : J} (x : ToType (F.obj i))
    (y : ToType (F.obj j))
    (h : ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y) :
    D.ι.app i x = D.ι.app j y := by
  let E := (forget C).mapCocone D
  obtain ⟨k, f, g, (hfg : (F ⋙ forget C).map f x = F.map g y)⟩ := h
  let h1 : (F ⋙ forget C).map f ≫ E.ι.app k = E.ι.app i := E.ι.naturality f
  let h2 : (F ⋙ forget C).map g ≫ E.ι.app k = E.ι.app j := E.ι.naturality g
  change E.ι.app i x = E.ι.app j y
  rw [← h1, types_comp_apply, hfg]
  exact congrFun h2 y

theorem colimit_rep_eq_of_exists [HasColimit F] {i j : J} (x : ToType (F.obj i))
    (y : ToType (F.obj j))
    (h : ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y) :
    colimit.ι F i x = colimit.ι F j y :=
  Concrete.isColimit_rep_eq_of_exists F x y h

end

section FilteredColimits

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type s}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable {J : Type w} [Category.{r} J] (F : J ⥤ C) [PreservesColimit F (forget C)] [IsFiltered J]

theorem isColimit_exists_of_rep_eq {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : ToType (F.obj i)) (y : ToType (F.obj j)) (h : D.ι.app _ x = D.ι.app _ y) :
    ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y := by
  let E := (forget C).mapCocone D
  let hE : IsColimit E := isColimitOfPreserves _ hD
  exact (Types.FilteredColimit.isColimit_eq_iff (F ⋙ forget C) hE).mp h

theorem isColimit_rep_eq_iff_exists {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : ToType (F.obj i)) (y : ToType (F.obj j)) :
    D.ι.app i x = D.ι.app j y ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  ⟨Concrete.isColimit_exists_of_rep_eq.{s} _ hD _ _,
   Concrete.isColimit_rep_eq_of_exists _ _ _⟩

theorem colimit_exists_of_rep_eq [HasColimit F] {i j : J} (x : ToType (F.obj i))
    (y : ToType (F.obj j)) (h : colimit.ι F _ x = colimit.ι F _ y) :
    ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  Concrete.isColimit_exists_of_rep_eq.{s} F (colimit.isColimit _) x y h

theorem colimit_rep_eq_iff_exists [HasColimit F] {i j : J} (x : ToType (F.obj i))
    (y : ToType (F.obj j)) :
    colimit.ι F i x = colimit.ι F j y ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  ⟨Concrete.colimit_exists_of_rep_eq.{s} _ _ _, Concrete.colimit_rep_eq_of_exists _ _ _⟩

end FilteredColimits

end Colimits

end CategoryTheory.Limits.Concrete
