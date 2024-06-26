/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

#align_import category_theory.limits.constructions.over.products from "leanprover-community/mathlib"@"ac3ae212f394f508df43e37aa093722fa9b65d31"

/-!
# Products in the over category

Shows that products in the over category can be derived from wide pullbacks in the base category.
The main result is `over_product_of_widePullback`, which says that if `C` has `J`-indexed wide
pullbacks, then `Over B` has `J`-indexed products.
-/


universe w v u -- morphism levels before object levels. See note [category_theory universes].

open CategoryTheory CategoryTheory.Limits

variable {J : Type w}
variable {C : Type u} [Category.{v} C]
variable {X : C}

namespace CategoryTheory.Over

namespace ConstructProducts

/-- (Implementation)
Given a product diagram in `C/B`, construct the corresponding wide pullback diagram
in `C`.
-/
abbrev widePullbackDiagramOfDiagramOver (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    WidePullbackShape J ⥤ C :=
  WidePullbackShape.wideCospan B (fun j => (F.obj ⟨j⟩).left) fun j => (F.obj ⟨j⟩).hom
#align category_theory.over.construct_products.wide_pullback_diagram_of_diagram_over CategoryTheory.Over.ConstructProducts.widePullbackDiagramOfDiagramOver

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def conesEquivInverseObj (B : C) {J : Type w} (F : Discrete J ⥤ Over B) (c : Cone F) :
    Cone (widePullbackDiagramOfDiagramOver B F) where
  pt := c.pt.left
  π :=
    { app := fun X => Option.casesOn X c.pt.hom fun j : J => (c.π.app ⟨j⟩).left
      -- `tidy` can do this using `case_bash`, but let's try to be a good `-T50000` citizen:
      naturality := fun X Y f => by
        dsimp; cases X <;> cases Y <;> cases f
        · rw [Category.id_comp, Category.comp_id]
        · rw [Over.w, Category.id_comp]
        · rw [Category.id_comp, Category.comp_id] }
#align category_theory.over.construct_products.cones_equiv_inverse_obj CategoryTheory.Over.ConstructProducts.conesEquivInverseObj

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def conesEquivInverse (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    Cone F ⥤ Cone (widePullbackDiagramOfDiagramOver B F) where
  obj := conesEquivInverseObj B F
  map f :=
    { hom := f.hom.left
      w := fun j => by
        cases' j with j
        · simp
        · dsimp
          rw [← f.w ⟨j⟩]
          rfl }
#align category_theory.over.construct_products.cones_equiv_inverse CategoryTheory.Over.ConstructProducts.conesEquivInverse

-- Porting note: this should help with the additional `naturality` proof we now have to give in
-- `conesEquivFunctor`, but doesn't.
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Discrete

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def conesEquivFunctor (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    Cone (widePullbackDiagramOfDiagramOver B F) ⥤ Cone F where
  obj c :=
    { pt := Over.mk (c.π.app none)
      π :=
        { app := fun ⟨j⟩ => Over.homMk (c.π.app (some j)) (c.w (WidePullbackShape.Hom.term j))
          -- Porting note (#10888): added proof for `naturality`
          naturality := fun ⟨X⟩ ⟨Y⟩ ⟨⟨f⟩⟩ => by dsimp at f ⊢; aesop_cat } }
  map f := { hom := Over.homMk f.hom }
#align category_theory.over.construct_products.cones_equiv_functor CategoryTheory.Over.ConstructProducts.conesEquivFunctor

-- Porting note: unfortunately `aesop` can't cope with a `cases` rule here for the type synonym
-- `WidePullbackShape`.
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WidePullbackShape
-- If this worked we could avoid the `rintro` in `conesEquivUnitIso`.

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simp]
def conesEquivUnitIso (B : C) (F : Discrete J ⥤ Over B) :
    𝟭 (Cone (widePullbackDiagramOfDiagramOver B F)) ≅
      conesEquivFunctor B F ⋙ conesEquivInverse B F :=
  NatIso.ofComponents fun _ => Cones.ext
    { hom := 𝟙 _
      inv := 𝟙 _ }
    (by rintro (j | j) <;> aesop_cat)
#align category_theory.over.construct_products.cones_equiv_unit_iso CategoryTheory.Over.ConstructProducts.conesEquivUnitIso

-- TODO: Can we add `:= by aesop` to the second arguments of `NatIso.ofComponents` and
--       `Cones.ext`?
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simp]
def conesEquivCounitIso (B : C) (F : Discrete J ⥤ Over B) :
    conesEquivInverse B F ⋙ conesEquivFunctor B F ≅ 𝟭 (Cone F) :=
  NatIso.ofComponents fun _ => Cones.ext
    { hom := Over.homMk (𝟙 _)
      inv := Over.homMk (𝟙 _) }
#align category_theory.over.construct_products.cones_equiv_counit_iso CategoryTheory.Over.ConstructProducts.conesEquivCounitIso

/-- (Impl) Establish an equivalence between the category of cones for `F` and for the "grown" `F`.
-/
@[simps]
def conesEquiv (B : C) (F : Discrete J ⥤ Over B) :
    Cone (widePullbackDiagramOfDiagramOver B F) ≌ Cone F where
  functor := conesEquivFunctor B F
  inverse := conesEquivInverse B F
  unitIso := conesEquivUnitIso B F
  counitIso := conesEquivCounitIso B F
#align category_theory.over.construct_products.cones_equiv CategoryTheory.Over.ConstructProducts.conesEquiv

/-- Use the above equivalence to prove we have a limit. -/
theorem has_over_limit_discrete_of_widePullback_limit {B : C} (F : Discrete J ⥤ Over B)
    [HasLimit (widePullbackDiagramOfDiagramOver B F)] : HasLimit F :=
  HasLimit.mk
    { cone := _
      isLimit := IsLimit.ofRightAdjoint (conesEquiv B F).symm.toAdjunction
        (limit.isLimit (widePullbackDiagramOfDiagramOver B F)) }
#align category_theory.over.construct_products.has_over_limit_discrete_of_wide_pullback_limit CategoryTheory.Over.ConstructProducts.has_over_limit_discrete_of_widePullback_limit

/-- Given a wide pullback in `C`, construct a product in `C/B`. -/
theorem over_product_of_widePullback [HasLimitsOfShape (WidePullbackShape J) C] {B : C} :
    HasLimitsOfShape (Discrete J) (Over B) :=
  { has_limit := fun F => has_over_limit_discrete_of_widePullback_limit F }
#align category_theory.over.construct_products.over_product_of_wide_pullback CategoryTheory.Over.ConstructProducts.over_product_of_widePullback

/-- Given a pullback in `C`, construct a binary product in `C/B`. -/
theorem over_binaryProduct_of_pullback [HasPullbacks C] {B : C} : HasBinaryProducts (Over B) :=
  over_product_of_widePullback
#align category_theory.over.construct_products.over_binary_product_of_pullback CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback

/-- Given all wide pullbacks in `C`, construct products in `C/B`. -/
theorem over_products_of_widePullbacks [HasWidePullbacks.{w} C] {B : C} :
    HasProducts.{w} (Over B) :=
  fun _ => over_product_of_widePullback
#align category_theory.over.construct_products.over_products_of_wide_pullbacks CategoryTheory.Over.ConstructProducts.over_products_of_widePullbacks

/-- Given all finite wide pullbacks in `C`, construct finite products in `C/B`. -/
theorem over_finiteProducts_of_finiteWidePullbacks [HasFiniteWidePullbacks C] {B : C} :
    HasFiniteProducts (Over B) :=
  ⟨fun _ => over_product_of_widePullback⟩
#align category_theory.over.construct_products.over_finite_products_of_finite_wide_pullbacks CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

end ConstructProducts

/-- Construct terminal object in the over category. This isn't an instance as it's not typically the
way we want to define terminal objects.
(For instance, this gives a terminal object which is different from the generic one given by
`over_product_of_widePullback` above.)
-/
theorem over_hasTerminal (B : C) : HasTerminal (Over B) where
  has_limit F := HasLimit.mk
    { cone :=
        { pt := Over.mk (𝟙 _)
          π :=
            { app := fun p => p.as.elim } }
      isLimit :=
        { lift := fun s => Over.homMk _
          fac := fun _ j => j.as.elim
          uniq := fun s m _ => by
            simp only
            ext
            rw [Over.homMk_left _]
            have := m.w
            dsimp at this
            rwa [Category.comp_id, Category.comp_id] at this } }
#align category_theory.over.over_has_terminal CategoryTheory.Over.over_hasTerminal

end CategoryTheory.Over
