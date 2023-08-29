/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.HasLimits

#align_import category_theory.limits.shapes.equalizers from "leanprover-community/mathlib"@"4698e35ca56a0d4fa53aa5639c3364e0a77f4eba"

/-!
# Equalizers and coequalizers

This file defines (co)equalizers as special cases of (co)limits.

An equalizer is the categorical generalization of the subobject {a ∈ A | f(a) = g(a)} known
from abelian groups or modules. It is a limit cone over the diagram formed by `f` and `g`.

A coequalizer is the dual concept.

## Main definitions

* `WalkingParallelPair` is the indexing category used for (co)equalizer_diagrams
* `parallelPair` is a functor from `WalkingParallelPair` to our category `C`.
* a `fork` is a cone over a parallel pair.
  * there is really only one interesting morphism in a fork: the arrow from the vertex of the fork
    to the domain of f and g. It is called `fork.ι`.
* an `equalizer` is now just a `limit (parallelPair f g)`

Each of these has a dual.

## Main statements

* `equalizer.ι_mono` states that every equalizer map is a monomorphism
* `isIso_limit_cone_parallelPair_of_self` states that the identity on the domain of `f` is an
  equalizer of `f` and `f`.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

/- Porting note: removed global noncomputable since there are things that might be
computable value like WalkingPair -/
section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

-- attribute [local tidy] tactic.case_bash -- Porting note: no tidy nor cases_bash

universe v v₂ u u₂

/-- The type of objects for the diagram indexing a (co)equalizer. -/
inductive WalkingParallelPair : Type
  | zero
  | one
  deriving DecidableEq, Inhabited
#align category_theory.limits.walking_parallel_pair CategoryTheory.Limits.WalkingParallelPair

open WalkingParallelPair

/-- The type family of morphisms for the diagram indexing a (co)equalizer. -/
inductive WalkingParallelPairHom : WalkingParallelPair → WalkingParallelPair → Type
  | left : WalkingParallelPairHom zero one
  | right : WalkingParallelPairHom zero one
  | id (X : WalkingParallelPair) : WalkingParallelPairHom X X
  deriving DecidableEq
#align category_theory.limits.walking_parallel_pair_hom CategoryTheory.Limits.WalkingParallelPairHom

/- Porting note: this simplifies using walkingParallelPairHom_id; replacement is below;
simpNF still complains of striking this from the simp list -/
attribute [-simp, nolint simpNF] WalkingParallelPairHom.id.sizeOf_spec

/-- Satisfying the inhabited linter -/
instance : Inhabited (WalkingParallelPairHom zero one) where default := WalkingParallelPairHom.left

open WalkingParallelPairHom

/-- Composition of morphisms in the indexing diagram for (co)equalizers. -/
def WalkingParallelPairHom.comp :
  -- Porting note: changed X Y Z to implicit to match comp fields in precategory
    ∀ { X Y Z : WalkingParallelPair } (_ : WalkingParallelPairHom X Y)
      (_ : WalkingParallelPairHom Y Z), WalkingParallelPairHom X Z
  | _, _, _, id _, h => h
  | _, _, _, left, id one => left
  | _, _, _, right, id one => right
#align category_theory.limits.walking_parallel_pair_hom.comp CategoryTheory.Limits.WalkingParallelPairHom.comp

-- Porting note: adding these since they are simple and aesop couldn't directly prove them
theorem WalkingParallelPairHom.id_comp
    {X Y : WalkingParallelPair} (g : WalkingParallelPairHom X Y) : comp (id X) g = g :=
  rfl

theorem WalkingParallelPairHom.comp_id
    {X Y : WalkingParallelPair} (f : WalkingParallelPairHom X Y) : comp f (id Y) = f := by
  cases f <;> rfl
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals

theorem WalkingParallelPairHom.assoc {X Y Z W : WalkingParallelPair}
    (f : WalkingParallelPairHom X Y) (g: WalkingParallelPairHom Y Z)
    (h : WalkingParallelPairHom Z W) : comp (comp f g) h = comp f (comp g h) := by
  cases f <;> cases g <;> cases h <;> rfl
              -- ⊢ comp (comp left (id one)) h = comp left (comp (id one) h)
              -- ⊢ comp (comp right (id one)) h = comp right (comp (id one) h)
                          -- ⊢ comp (comp left (id one)) (id one) = comp left (comp (id one) (id one))
                          -- ⊢ comp (comp right (id one)) (id one) = comp right (comp (id one) (id one))
                          -- ⊢ comp (comp (id zero) left) (id one) = comp (id zero) (comp left (id one))
                          -- ⊢ comp (comp (id zero) right) (id one) = comp (id zero) (comp right (id one))
                                      -- 🎉 no goals
                                      -- 🎉 no goals
                                      -- 🎉 no goals
                                      -- 🎉 no goals
                                      -- 🎉 no goals
                                      -- 🎉 no goals
                                      -- 🎉 no goals

instance walkingParallelPairHomCategory : SmallCategory WalkingParallelPair where
  Hom := WalkingParallelPairHom
  id := id
  comp := comp
  comp_id := comp_id
  id_comp := id_comp
  assoc := assoc
#align category_theory.limits.walking_parallel_pair_hom_category CategoryTheory.Limits.walkingParallelPairHomCategory

@[simp]
theorem walkingParallelPairHom_id (X : WalkingParallelPair) : WalkingParallelPairHom.id X = 𝟙 X :=
  rfl
#align category_theory.limits.walking_parallel_pair_hom_id CategoryTheory.Limits.walkingParallelPairHom_id

-- Porting note: simpNF asked me to do this because the LHS of the non-primed version reduced
@[simp]
theorem WalkingParallelPairHom.id.sizeOf_spec' (X : WalkingParallelPair) :
    (WalkingParallelPairHom._sizeOf_inst X X).sizeOf (𝟙 X) = 1 + sizeOf X := by cases X <;> rfl
                                                                                -- ⊢ sizeOf (𝟙 zero) = 1 + sizeOf zero
                                                                                            -- 🎉 no goals
                                                                                            -- 🎉 no goals

/-- The functor `WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ` sending left to left and right to
right.
-/
def walkingParallelPairOp : WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ where
  obj x := op <| by cases x; exacts [one, zero]
                    -- ⊢ WalkingParallelPair
                             -- 🎉 no goals
  map f := by
    cases f <;> apply Quiver.Hom.op
                -- ⊢ WalkingParallelPair.casesOn (motive := fun t => one = t → WalkingParallelPai …
                -- ⊢ WalkingParallelPair.casesOn (motive := fun t => one = t → WalkingParallelPai …
                -- ⊢ WalkingParallelPair.casesOn (motive := fun t => X✝ = t → WalkingParallelPair …
    exacts [left, right, WalkingParallelPairHom.id _]
    -- 🎉 no goals
  map_comp := by rintro _ _ _ (_|_|_) g <;> cases g <;> rfl
                                            -- ⊢ { obj := fun x => op (WalkingParallelPair.casesOn (motive := fun t => x = t  …
                                            -- ⊢ { obj := fun x => op (WalkingParallelPair.casesOn (motive := fun t => x = t  …
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
#align category_theory.limits.walking_parallel_pair_op CategoryTheory.Limits.walkingParallelPairOp

@[simp]
theorem walkingParallelPairOp_zero : walkingParallelPairOp.obj zero = op one := rfl
#align category_theory.limits.walking_parallel_pair_op_zero CategoryTheory.Limits.walkingParallelPairOp_zero

@[simp]
theorem walkingParallelPairOp_one : walkingParallelPairOp.obj one = op zero := rfl
#align category_theory.limits.walking_parallel_pair_op_one CategoryTheory.Limits.walkingParallelPairOp_one

@[simp]
theorem walkingParallelPairOp_left :
    walkingParallelPairOp.map left = @Quiver.Hom.op _ _ zero one left := rfl
#align category_theory.limits.walking_parallel_pair_op_left CategoryTheory.Limits.walkingParallelPairOp_left

@[simp]
theorem walkingParallelPairOp_right :
    walkingParallelPairOp.map right = @Quiver.Hom.op _ _ zero one right := rfl
#align category_theory.limits.walking_parallel_pair_op_right CategoryTheory.Limits.walkingParallelPairOp_right

/--
The equivalence `WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ` sending left to left and right to
right.
-/
@[simps functor inverse]
def walkingParallelPairOpEquiv : WalkingParallelPair ≌ WalkingParallelPairᵒᵖ where
  functor := walkingParallelPairOp
  inverse := walkingParallelPairOp.leftOp
  unitIso :=
    NatIso.ofComponents (fun j => eqToIso (by cases j <;> rfl))
                                              -- ⊢ (𝟭 WalkingParallelPair).obj zero = (walkingParallelPairOp ⋙ walkingParallelP …
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
      (by rintro _ _ (_ | _ | _) <;> simp)
                                     -- 🎉 no goals
                                     -- 🎉 no goals
                                     -- 🎉 no goals
  counitIso :=
    NatIso.ofComponents (fun j => eqToIso (by
            induction' j with X
            -- ⊢ (walkingParallelPairOp.leftOp ⋙ walkingParallelPairOp).obj (op X) = (𝟭 Walki …
            cases X <;> rfl ))
            -- ⊢ (walkingParallelPairOp.leftOp ⋙ walkingParallelPairOp).obj (op zero) = (𝟭 Wa …
                        -- 🎉 no goals
                        -- 🎉 no goals
      (fun {i} {j} f => by
      induction' i with i
      -- ⊢ (walkingParallelPairOp.leftOp ⋙ walkingParallelPairOp).map f ≫ ((fun j => eq …
      induction' j with j
      -- ⊢ (walkingParallelPairOp.leftOp ⋙ walkingParallelPairOp).map f ≫ ((fun j => eq …
      let g := f.unop
      -- ⊢ (walkingParallelPairOp.leftOp ⋙ walkingParallelPairOp).map f ≫ ((fun j => eq …
      have : f = g.op := rfl
      -- ⊢ (walkingParallelPairOp.leftOp ⋙ walkingParallelPairOp).map f ≫ ((fun j => eq …
      rw [this]
      -- ⊢ (walkingParallelPairOp.leftOp ⋙ walkingParallelPairOp).map g.op ≫ ((fun j => …
      cases i <;> cases j <;> cases g <;> rfl)
      -- ⊢ (walkingParallelPairOp.leftOp ⋙ walkingParallelPairOp).map g.op ≫ ((fun j => …
                  -- ⊢ (walkingParallelPairOp.leftOp ⋙ walkingParallelPairOp).map g.op ≫ ((fun j => …
                  -- ⊢ (walkingParallelPairOp.leftOp ⋙ walkingParallelPairOp).map g.op ≫ ((fun j => …
                              -- ⊢ (walkingParallelPairOp.leftOp ⋙ walkingParallelPairOp).map (WalkingParallelP …
                              -- 🎉 no goals
                              -- ⊢ (walkingParallelPairOp.leftOp ⋙ walkingParallelPairOp).map left.op ≫ ((fun j …
                              -- ⊢ (walkingParallelPairOp.leftOp ⋙ walkingParallelPairOp).map (WalkingParallelP …
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- 🎉 no goals
  functor_unitIso_comp := fun j => by cases j <;> rfl
                                      -- ⊢ walkingParallelPairOp.map (NatTrans.app (NatIso.ofComponents fun j => eqToIs …
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
#align category_theory.limits.walking_parallel_pair_op_equiv CategoryTheory.Limits.walkingParallelPairOpEquiv

@[simp]
theorem walkingParallelPairOpEquiv_unitIso_zero :
    walkingParallelPairOpEquiv.unitIso.app zero = Iso.refl zero := rfl
#align category_theory.limits.walking_parallel_pair_op_equiv_unit_iso_zero CategoryTheory.Limits.walkingParallelPairOpEquiv_unitIso_zero

@[simp]
theorem walkingParallelPairOpEquiv_unitIso_one :
    walkingParallelPairOpEquiv.unitIso.app one = Iso.refl one := rfl
#align category_theory.limits.walking_parallel_pair_op_equiv_unit_iso_one CategoryTheory.Limits.walkingParallelPairOpEquiv_unitIso_one

@[simp]
theorem walkingParallelPairOpEquiv_counitIso_zero :
    walkingParallelPairOpEquiv.counitIso.app (op zero) = Iso.refl (op zero) := rfl
#align category_theory.limits.walking_parallel_pair_op_equiv_counit_iso_zero CategoryTheory.Limits.walkingParallelPairOpEquiv_counitIso_zero

@[simp]
theorem walkingParallelPairOpEquiv_counitIso_one :
    walkingParallelPairOpEquiv.counitIso.app (op one) = Iso.refl (op one) :=
  rfl
#align category_theory.limits.walking_parallel_pair_op_equiv_counit_iso_one CategoryTheory.Limits.walkingParallelPairOpEquiv_counitIso_one

variable {C : Type u} [Category.{v} C]

variable {X Y : C}

/-- `parallelPair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with
    common domain and codomain. -/
def parallelPair (f g : X ⟶ Y) : WalkingParallelPair ⥤ C where
  obj x :=
    match x with
    | zero => X
    | one => Y
  map h :=
    match h with
    | WalkingParallelPairHom.id _ => 𝟙 _
    | left => f
    | right => g
  -- `sorry` can cope with this, but it's too slow:
  map_comp := by
    rintro _ _ _ ⟨⟩ g <;> cases g <;> {dsimp; simp}
                          -- ⊢ {
                          -- ⊢ {
                                      -- 🎉 no goals
                                      -- 🎉 no goals
                                      -- 🎉 no goals
                                      -- 🎉 no goals
                                      -- 🎉 no goals
#align category_theory.limits.parallel_pair CategoryTheory.Limits.parallelPair

@[simp]
theorem parallelPair_obj_zero (f g : X ⟶ Y) : (parallelPair f g).obj zero = X := rfl
#align category_theory.limits.parallel_pair_obj_zero CategoryTheory.Limits.parallelPair_obj_zero

@[simp]
theorem parallelPair_obj_one (f g : X ⟶ Y) : (parallelPair f g).obj one = Y := rfl
#align category_theory.limits.parallel_pair_obj_one CategoryTheory.Limits.parallelPair_obj_one

@[simp]
theorem parallelPair_map_left (f g : X ⟶ Y) : (parallelPair f g).map left = f := rfl
#align category_theory.limits.parallel_pair_map_left CategoryTheory.Limits.parallelPair_map_left

@[simp]
theorem parallelPair_map_right (f g : X ⟶ Y) : (parallelPair f g).map right = g := rfl
#align category_theory.limits.parallel_pair_map_right CategoryTheory.Limits.parallelPair_map_right

@[simp]
theorem parallelPair_functor_obj {F : WalkingParallelPair ⥤ C} (j : WalkingParallelPair) :
    (parallelPair (F.map left) (F.map right)).obj j = F.obj j := by cases j <;> rfl
                                                                    -- ⊢ (parallelPair (F.map left) (F.map right)).obj zero = F.obj zero
                                                                                -- 🎉 no goals
                                                                                -- 🎉 no goals
#align category_theory.limits.parallel_pair_functor_obj CategoryTheory.Limits.parallelPair_functor_obj

/-- Every functor indexing a (co)equalizer is naturally isomorphic (actually, equal) to a
    `parallelPair` -/
@[simps!]
def diagramIsoParallelPair (F : WalkingParallelPair ⥤ C) :
    F ≅ parallelPair (F.map left) (F.map right) :=
  NatIso.ofComponents (fun j => eqToIso <| by cases j <;> rfl) (by rintro _ _ (_|_|_) <;> simp)
                                              -- ⊢ F.obj zero = (parallelPair (F.map left) (F.map right)).obj zero
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                                                          -- 🎉 no goals
                                                                                          -- 🎉 no goals
                                                                                          -- 🎉 no goals
#align category_theory.limits.diagram_iso_parallel_pair CategoryTheory.Limits.diagramIsoParallelPair

/-- Construct a morphism between parallel pairs. -/
def parallelPairHom {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y')
    (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') : parallelPair f g ⟶ parallelPair f' g'
    where
  app j :=
    match j with
    | zero => p
    | one => q
  naturality := by
    rintro _ _ ⟨⟩ <;> {dsimp; simp [wf,wg]}
                      -- 🎉 no goals
                      -- 🎉 no goals
                      -- 🎉 no goals
#align category_theory.limits.parallel_pair_hom CategoryTheory.Limits.parallelPairHom

@[simp]
theorem parallelPairHom_app_zero {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X')
    (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') :
    (parallelPairHom f g f' g' p q wf wg).app zero = p :=
  rfl
#align category_theory.limits.parallel_pair_hom_app_zero CategoryTheory.Limits.parallelPairHom_app_zero

@[simp]
theorem parallelPairHom_app_one {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X')
    (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') :
    (parallelPairHom f g f' g' p q wf wg).app one = q :=
  rfl
#align category_theory.limits.parallel_pair_hom_app_one CategoryTheory.Limits.parallelPairHom_app_one

/-- Construct a natural isomorphism between functors out of the walking parallel pair from
its components. -/
@[simps!]
def parallelPair.ext {F G : WalkingParallelPair ⥤ C} (zero : F.obj zero ≅ G.obj zero)
    (one : F.obj one ≅ G.obj one) (left : F.map left ≫ one.hom = zero.hom ≫ G.map left)
    (right : F.map right ≫ one.hom = zero.hom ≫ G.map right) : F ≅ G :=
  NatIso.ofComponents
    (by
      rintro ⟨j⟩
      -- ⊢ F.obj CategoryTheory.Limits.WalkingParallelPair.zero ≅ G.obj CategoryTheory. …
      exacts [zero, one])
      -- 🎉 no goals
    (by rintro _ _ ⟨_⟩ <;> simp [left, right])
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
#align category_theory.limits.parallel_pair.ext CategoryTheory.Limits.parallelPair.ext

/-- Construct a natural isomorphism between `parallelPair f g` and `parallelPair f' g'` given
equalities `f = f'` and `g = g'`. -/
@[simps!]
def parallelPair.eqOfHomEq {f g f' g' : X ⟶ Y} (hf : f = f') (hg : g = g') :
    parallelPair f g ≅ parallelPair f' g' :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [hf]) (by simp [hg])
                                                 -- 🎉 no goals
                                                                -- 🎉 no goals
#align category_theory.limits.parallel_pair.eq_of_hom_eq CategoryTheory.Limits.parallelPair.eqOfHomEq

/-- A fork on `f` and `g` is just a `Cone (parallelPair f g)`. -/
abbrev Fork (f g : X ⟶ Y) :=
  Cone (parallelPair f g)
#align category_theory.limits.fork CategoryTheory.Limits.Fork

/-- A cofork on `f` and `g` is just a `Cocone (parallelPair f g)`. -/
abbrev Cofork (f g : X ⟶ Y) :=
  Cocone (parallelPair f g)
#align category_theory.limits.cofork CategoryTheory.Limits.Cofork

variable {f g : X ⟶ Y}

/-- A fork `t` on the parallel pair `f g : X ⟶ Y` consists of two morphisms
    `t.π.app zero : t.pt ⟶ X`
    and `t.π.app one : t.pt ⟶ Y`. Of these, only the first one is interesting, and we give it the
    shorter name `Fork.ι t`. -/
def Fork.ι (t : Fork f g) :=
  t.π.app zero
#align category_theory.limits.fork.ι CategoryTheory.Limits.Fork.ι

@[simp]
theorem Fork.app_zero_eq_ι (t : Fork f g) : t.π.app zero = t.ι :=
  rfl
#align category_theory.limits.fork.app_zero_eq_ι CategoryTheory.Limits.Fork.app_zero_eq_ι

/-- A cofork `t` on the parallelPair `f g : X ⟶ Y` consists of two morphisms
    `t.ι.app zero : X ⟶ t.pt` and `t.ι.app one : Y ⟶ t.pt`. Of these, only the second one is
    interesting, and we give it the shorter name `Cofork.π t`. -/
def Cofork.π (t : Cofork f g) :=
  t.ι.app one
#align category_theory.limits.cofork.π CategoryTheory.Limits.Cofork.π

@[simp]
theorem Cofork.app_one_eq_π (t : Cofork f g) : t.ι.app one = t.π :=
  rfl
#align category_theory.limits.cofork.app_one_eq_π CategoryTheory.Limits.Cofork.app_one_eq_π

@[simp]
theorem Fork.app_one_eq_ι_comp_left (s : Fork f g) : s.π.app one = s.ι ≫ f := by
  rw [← s.app_zero_eq_ι, ← s.w left, parallelPair_map_left]
  -- 🎉 no goals
#align category_theory.limits.fork.app_one_eq_ι_comp_left CategoryTheory.Limits.Fork.app_one_eq_ι_comp_left

@[reassoc]
theorem Fork.app_one_eq_ι_comp_right (s : Fork f g) : s.π.app one = s.ι ≫ g := by
  rw [← s.app_zero_eq_ι, ← s.w right, parallelPair_map_right]
  -- 🎉 no goals
#align category_theory.limits.fork.app_one_eq_ι_comp_right CategoryTheory.Limits.Fork.app_one_eq_ι_comp_right

@[simp]
theorem Cofork.app_zero_eq_comp_π_left (s : Cofork f g) : s.ι.app zero = f ≫ s.π := by
  rw [← s.app_one_eq_π, ← s.w left, parallelPair_map_left]
  -- 🎉 no goals
#align category_theory.limits.cofork.app_zero_eq_comp_π_left CategoryTheory.Limits.Cofork.app_zero_eq_comp_π_left

@[reassoc]
theorem Cofork.app_zero_eq_comp_π_right (s : Cofork f g) : s.ι.app zero = g ≫ s.π := by
  rw [← s.app_one_eq_π, ← s.w right, parallelPair_map_right]
  -- 🎉 no goals
#align category_theory.limits.cofork.app_zero_eq_comp_π_right CategoryTheory.Limits.Cofork.app_zero_eq_comp_π_right

/-- A fork on `f g : X ⟶ Y` is determined by the morphism `ι : P ⟶ X` satisfying `ι ≫ f = ι ≫ g`.
-/
@[simps]
def Fork.ofι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : Fork f g where
  pt := P
  π :=
    { app := fun X => by cases X; exact ι; exact ι ≫ f
                         -- ⊢ ((Functor.const WalkingParallelPair).obj P).obj zero ⟶ (parallelPair f g).ob …
                                  -- ⊢ ((Functor.const WalkingParallelPair).obj P).obj one ⟶ (parallelPair f g).obj …
                                           -- 🎉 no goals
      naturality := fun {X} {Y} f =>
        by cases X <;> cases Y <;> cases f <;> dsimp <;> simp; assumption }
           -- ⊢ ((Functor.const WalkingParallelPair).obj P).map f ≫ (fun X_1 => WalkingParal …
                       -- ⊢ ((Functor.const WalkingParallelPair).obj P).map f ≫ (fun X_1 => WalkingParal …
                       -- ⊢ ((Functor.const WalkingParallelPair).obj P).map f ≫ (fun X_1 => WalkingParal …
                                   -- ⊢ ((Functor.const WalkingParallelPair).obj P).map (WalkingParallelPairHom.id z …
                                   -- ⊢ ((Functor.const WalkingParallelPair).obj P).map left ≫ (fun X_1 => WalkingPa …
                                   -- 🎉 no goals
                                   -- ⊢ ((Functor.const WalkingParallelPair).obj P).map (WalkingParallelPairHom.id o …
                                               -- ⊢ 𝟙 P ≫ ι = ι ≫ (parallelPair f g).map (𝟙 zero)
                                               -- ⊢ 𝟙 P ≫ ι ≫ f = ι ≫ f
                                               -- ⊢ 𝟙 P ≫ ι ≫ f = ι ≫ g
                                               -- ⊢ 𝟙 P ≫ ι ≫ f = (ι ≫ f) ≫ (parallelPair f g).map (𝟙 one)
                                                         -- 🎉 no goals
                                                         -- 🎉 no goals
                                                         -- ⊢ ι ≫ f = ι ≫ g
                                                         -- 🎉 no goals
                                                               -- 🎉 no goals
#align category_theory.limits.fork.of_ι CategoryTheory.Limits.Fork.ofι

/-- A cofork on `f g : X ⟶ Y` is determined by the morphism `π : Y ⟶ P` satisfying
    `f ≫ π = g ≫ π`. -/
@[simps]
def Cofork.ofπ {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : Cofork f g where
  pt := P
  ι :=
    { app := fun X => WalkingParallelPair.casesOn X (f ≫ π) π
      naturality := fun i j f => by cases f <;> dsimp <;> simp [w] }
                                                -- ⊢ f ≫ π = (f ≫ π) ≫ 𝟙 P
                                                -- ⊢ g ≫ π = (f ≫ π) ≫ 𝟙 P
                                                -- ⊢ (parallelPair f g).map (𝟙 i) ≫ WalkingParallelPair.rec (f ≫ π) π i = Walking …
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
#align category_theory.limits.cofork.of_π CategoryTheory.Limits.Cofork.ofπ

-- See note [dsimp, simp]
@[simp]
theorem Fork.ι_ofι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : (Fork.ofι ι w).ι = ι :=
  rfl
#align category_theory.limits.fork.ι_of_ι CategoryTheory.Limits.Fork.ι_ofι

@[simp]
theorem Cofork.π_ofπ {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : (Cofork.ofπ π w).π = π :=
  rfl
#align category_theory.limits.cofork.π_of_π CategoryTheory.Limits.Cofork.π_ofπ

@[reassoc (attr := simp)]
theorem Fork.condition (t : Fork f g) : t.ι ≫ f = t.ι ≫ g := by
  rw [← t.app_one_eq_ι_comp_left, ← t.app_one_eq_ι_comp_right]
  -- 🎉 no goals
#align category_theory.limits.fork.condition CategoryTheory.Limits.Fork.condition

@[reassoc (attr := simp)]
theorem Cofork.condition (t : Cofork f g) : f ≫ t.π = g ≫ t.π := by
  rw [← t.app_zero_eq_comp_π_left, ← t.app_zero_eq_comp_π_right]
  -- 🎉 no goals
#align category_theory.limits.cofork.condition CategoryTheory.Limits.Cofork.condition

/-- To check whether two maps are equalized by both maps of a fork, it suffices to check it for the
    first map -/
theorem Fork.equalizer_ext (s : Fork f g) {W : C} {k l : W ⟶ s.pt} (h : k ≫ s.ι = l ≫ s.ι) :
    ∀ j : WalkingParallelPair, k ≫ s.π.app j = l ≫ s.π.app j
  | zero => h
  | one => by
    have : k ≫ ι s ≫ f = l ≫ ι s ≫ f := by
      simp only [← Category.assoc]; exact congrArg (· ≫ f) h
    rw [s.app_one_eq_ι_comp_left, this]
    -- 🎉 no goals
#align category_theory.limits.fork.equalizer_ext CategoryTheory.Limits.Fork.equalizer_ext

/-- To check whether two maps are coequalized by both maps of a cofork, it suffices to check it for
    the second map -/
theorem Cofork.coequalizer_ext (s : Cofork f g) {W : C} {k l : s.pt ⟶ W}
    (h : Cofork.π s ≫ k = Cofork.π s ≫ l) : ∀ j : WalkingParallelPair, s.ι.app j ≫ k = s.ι.app j ≫ l
  | zero => by simp only [s.app_zero_eq_comp_π_left, Category.assoc, h]
               -- 🎉 no goals
  | one => h
#align category_theory.limits.cofork.coequalizer_ext CategoryTheory.Limits.Cofork.coequalizer_ext

theorem Fork.IsLimit.hom_ext {s : Fork f g} (hs : IsLimit s) {W : C} {k l : W ⟶ s.pt}
    (h : k ≫ Fork.ι s = l ≫ Fork.ι s) : k = l :=
  hs.hom_ext <| Fork.equalizer_ext _ h
#align category_theory.limits.fork.is_limit.hom_ext CategoryTheory.Limits.Fork.IsLimit.hom_ext

theorem Cofork.IsColimit.hom_ext {s : Cofork f g} (hs : IsColimit s) {W : C} {k l : s.pt ⟶ W}
    (h : Cofork.π s ≫ k = Cofork.π s ≫ l) : k = l :=
  hs.hom_ext <| Cofork.coequalizer_ext _ h
#align category_theory.limits.cofork.is_colimit.hom_ext CategoryTheory.Limits.Cofork.IsColimit.hom_ext

@[reassoc (attr := simp)]
theorem Fork.IsLimit.lift_ι {s t : Fork f g} (hs : IsLimit s) : hs.lift t ≫ s.ι = t.ι :=
  hs.fac _ _
#align category_theory.limits.fork.is_limit.lift_ι CategoryTheory.Limits.Fork.IsLimit.lift_ι

@[reassoc (attr := simp)]
theorem Cofork.IsColimit.π_desc {s t : Cofork f g} (hs : IsColimit s) : s.π ≫ hs.desc t = t.π :=
  hs.fac _ _
#align category_theory.limits.cofork.is_colimit.π_desc CategoryTheory.Limits.Cofork.IsColimit.π_desc

-- porting note: `Fork.IsLimit.lift` was added in order to ease the port
/-- If `s` is a limit fork over `f` and `g`, then a morphism `k : W ⟶ X` satisfying
    `k ≫ f = k ≫ g` induces a morphism `l : W ⟶ s.pt` such that `l ≫ fork.ι s = k`. -/
def Fork.IsLimit.lift {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    W ⟶ s.pt :=
  hs.lift (Fork.ofι _ h)

@[reassoc (attr := simp)]
lemma Fork.IsLimit.lift_ι' {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    Fork.IsLimit.lift hs k h ≫ Fork.ι s = k :=
    hs.fac _ _

/-- If `s` is a limit fork over `f` and `g`, then a morphism `k : W ⟶ X` satisfying
    `k ≫ f = k ≫ g` induces a morphism `l : W ⟶ s.pt` such that `l ≫ fork.ι s = k`. -/
def Fork.IsLimit.lift' {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    { l : W ⟶ s.pt // l ≫ Fork.ι s = k } :=
  ⟨Fork.IsLimit.lift hs k h, by simp⟩
                                -- 🎉 no goals
#align category_theory.limits.fork.is_limit.lift' CategoryTheory.Limits.Fork.IsLimit.lift'

-- porting note: `Cofork.IsColimit.desc` was added in order to ease the port
/-- If `s` is a colimit cofork over `f` and `g`, then a morphism `k : Y ⟶ W` satisfying
    `f ≫ k = g ≫ k` induces a morphism `l : s.pt ⟶ W` such that `cofork.π s ≫ l = k`. -/
def Cofork.IsColimit.desc {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = g ≫ k) : s.pt ⟶ W :=
  hs.desc (Cofork.ofπ _ h)

@[reassoc (attr := simp)]
lemma Cofork.IsColimit.π_desc' {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = g ≫ k) : Cofork.π s ≫ Cofork.IsColimit.desc hs k h = k :=
  hs.fac _ _

/-- If `s` is a colimit cofork over `f` and `g`, then a morphism `k : Y ⟶ W` satisfying
    `f ≫ k = g ≫ k` induces a morphism `l : s.pt ⟶ W` such that `cofork.π s ≫ l = k`. -/
def Cofork.IsColimit.desc' {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = g ≫ k) : { l : s.pt ⟶ W // Cofork.π s ≫ l = k } :=
  ⟨Cofork.IsColimit.desc hs k h, by simp⟩
                                    -- 🎉 no goals
#align category_theory.limits.cofork.is_colimit.desc' CategoryTheory.Limits.Cofork.IsColimit.desc'

theorem Fork.IsLimit.existsUnique {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X)
    (h : k ≫ f = k ≫ g) : ∃! l : W ⟶ s.pt, l ≫ Fork.ι s = k :=
  ⟨hs.lift <| Fork.ofι _ h, hs.fac _ _, fun _ hm =>
    Fork.IsLimit.hom_ext hs <| hm.symm ▸ (hs.fac (Fork.ofι _ h) WalkingParallelPair.zero).symm⟩
#align category_theory.limits.fork.is_limit.exists_unique CategoryTheory.Limits.Fork.IsLimit.existsUnique

theorem Cofork.IsColimit.existsUnique {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = g ≫ k) : ∃! d : s.pt ⟶ W, Cofork.π s ≫ d = k :=
  ⟨hs.desc <| Cofork.ofπ _ h, hs.fac _ _, fun _ hm =>
    Cofork.IsColimit.hom_ext hs <| hm.symm ▸ (hs.fac (Cofork.ofπ _ h) WalkingParallelPair.one).symm⟩
#align category_theory.limits.cofork.is_colimit.exists_unique CategoryTheory.Limits.Cofork.IsColimit.existsUnique

/-- This is a slightly more convenient method to verify that a fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
@[simps]
def Fork.IsLimit.mk (t : Fork f g) (lift : ∀ s : Fork f g, s.pt ⟶ t.pt)
    (fac : ∀ s : Fork f g, lift s ≫ Fork.ι t = Fork.ι s)
    (uniq : ∀ (s : Fork f g) (m : s.pt ⟶ t.pt) (_ : m ≫ t.ι = s.ι), m = lift s) : IsLimit t :=
  { lift
    fac := fun s j =>
      WalkingParallelPair.casesOn j (fac s) <| by
        erw [← s.w left, ← t.w left, ← Category.assoc, fac]; rfl
        -- ⊢ ι s ≫ (parallelPair f g).map left = NatTrans.app s.π zero ≫ (parallelPair f  …
                                                             -- 🎉 no goals
    uniq := fun s m j => by aesop}
                            -- 🎉 no goals
#align category_theory.limits.fork.is_limit.mk CategoryTheory.Limits.Fork.IsLimit.mk

/-- This is another convenient method to verify that a fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def Fork.IsLimit.mk' {X Y : C} {f g : X ⟶ Y} (t : Fork f g)
    (create : ∀ s : Fork f g, { l // l ≫ t.ι = s.ι ∧ ∀ {m}, m ≫ t.ι = s.ι → m = l }) : IsLimit t :=
  Fork.IsLimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w => (create s).2.2 w
#align category_theory.limits.fork.is_limit.mk' CategoryTheory.Limits.Fork.IsLimit.mk'

/-- This is a slightly more convenient method to verify that a cofork is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content -/
def Cofork.IsColimit.mk (t : Cofork f g) (desc : ∀ s : Cofork f g, t.pt ⟶ s.pt)
    (fac : ∀ s : Cofork f g, Cofork.π t ≫ desc s = Cofork.π s)
    (uniq : ∀ (s : Cofork f g) (m : t.pt ⟶ s.pt) (_ : t.π ≫ m = s.π), m = desc s) : IsColimit t :=
  { desc
    fac := fun s j =>
      WalkingParallelPair.casesOn j (by erw [← s.w left, ← t.w left, Category.assoc, fac]; rfl)
                                        -- ⊢ (parallelPair f g).map left ≫ π s = (parallelPair f g).map left ≫ NatTrans.a …
                                                                                           -- 🎉 no goals
        (fac s)
    uniq := by aesop }
               -- 🎉 no goals
#align category_theory.limits.cofork.is_colimit.mk CategoryTheory.Limits.Cofork.IsColimit.mk

/-- This is another convenient method to verify that a fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def Cofork.IsColimit.mk' {X Y : C} {f g : X ⟶ Y} (t : Cofork f g)
    (create : ∀ s : Cofork f g, { l : t.pt ⟶ s.pt // t.π ≫ l = s.π ∧ ∀ {m}, t.π ≫ m = s.π → m = l })
    : IsColimit t :=
  Cofork.IsColimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w =>
    (create s).2.2 w
#align category_theory.limits.cofork.is_colimit.mk' CategoryTheory.Limits.Cofork.IsColimit.mk'

/-- Noncomputably make a limit cone from the existence of unique factorizations. -/
noncomputable def Fork.IsLimit.ofExistsUnique {t : Fork f g}
    (hs : ∀ s : Fork f g, ∃! l : s.pt ⟶ t.pt, l ≫ Fork.ι t = Fork.ι s) : IsLimit t := by
  choose d hd hd' using hs
  -- ⊢ IsLimit t
  exact Fork.IsLimit.mk _ d hd fun s m hm => hd' _ _ hm
  -- 🎉 no goals
#align category_theory.limits.fork.is_limit.of_exists_unique CategoryTheory.Limits.Fork.IsLimit.ofExistsUnique

/-- Noncomputably make a colimit cocone from the existence of unique factorizations. -/
noncomputable def Cofork.IsColimit.ofExistsUnique {t : Cofork f g}
    (hs : ∀ s : Cofork f g, ∃! d : t.pt ⟶ s.pt, Cofork.π t ≫ d = Cofork.π s) : IsColimit t := by
  choose d hd hd' using hs
  -- ⊢ IsColimit t
  exact Cofork.IsColimit.mk _ d hd fun s m hm => hd' _ _ hm
  -- 🎉 no goals
#align category_theory.limits.cofork.is_colimit.of_exists_unique CategoryTheory.Limits.Cofork.IsColimit.ofExistsUnique

/--
Given a limit cone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from `Z` to its point are in
bijection with morphisms `h : Z ⟶ X` such that `h ≫ f = h ≫ g`.
Further, this bijection is natural in `Z`: see `Fork.IsLimit.homIso_natural`.
This is a special case of `IsLimit.homIso'`, often useful to construct adjunctions.
-/
@[simps]
def Fork.IsLimit.homIso {X Y : C} {f g : X ⟶ Y} {t : Fork f g} (ht : IsLimit t) (Z : C) :
    (Z ⟶ t.pt) ≃ { h : Z ⟶ X // h ≫ f = h ≫ g } where
  toFun k := ⟨k ≫ t.ι, by simp only [Category.assoc, t.condition]⟩
                          -- 🎉 no goals
  invFun h := (Fork.IsLimit.lift' ht _ h.prop).1
  left_inv k := Fork.IsLimit.hom_ext ht (Fork.IsLimit.lift' _ _ _).prop
  right_inv h := Subtype.ext (Fork.IsLimit.lift' ht _ _).prop
#align category_theory.limits.fork.is_limit.hom_iso CategoryTheory.Limits.Fork.IsLimit.homIso

/-- The bijection of `Fork.IsLimit.homIso` is natural in `Z`. -/
theorem Fork.IsLimit.homIso_natural {X Y : C} {f g : X ⟶ Y} {t : Fork f g} (ht : IsLimit t)
    {Z Z' : C} (q : Z' ⟶ Z) (k : Z ⟶ t.pt) :
    (Fork.IsLimit.homIso ht _ (q ≫ k) : Z' ⟶ X) = q ≫ (Fork.IsLimit.homIso ht _ k : Z ⟶ X) :=
  Category.assoc _ _ _
#align category_theory.limits.fork.is_limit.hom_iso_natural CategoryTheory.Limits.Fork.IsLimit.homIso_natural

/-- Given a colimit cocone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from the cocone point
to `Z` are in bijection with morphisms `h : Y ⟶ Z` such that `f ≫ h = g ≫ h`.
Further, this bijection is natural in `Z`: see `Cofork.IsColimit.homIso_natural`.
This is a special case of `IsColimit.homIso'`, often useful to construct adjunctions.
-/
@[simps]
def Cofork.IsColimit.homIso {X Y : C} {f g : X ⟶ Y} {t : Cofork f g} (ht : IsColimit t) (Z : C) :
    (t.pt ⟶ Z) ≃ { h : Y ⟶ Z // f ≫ h = g ≫ h } where
  toFun k := ⟨t.π ≫ k, by simp only [← Category.assoc, t.condition]⟩
                          -- 🎉 no goals
  invFun h := (Cofork.IsColimit.desc' ht _ h.prop).1
  left_inv k := Cofork.IsColimit.hom_ext ht (Cofork.IsColimit.desc' _ _ _).prop
  right_inv h := Subtype.ext (Cofork.IsColimit.desc' ht _ _).prop
#align category_theory.limits.cofork.is_colimit.hom_iso CategoryTheory.Limits.Cofork.IsColimit.homIso

/-- The bijection of `Cofork.IsColimit.homIso` is natural in `Z`. -/
theorem Cofork.IsColimit.homIso_natural {X Y : C} {f g : X ⟶ Y} {t : Cofork f g} {Z Z' : C}
    (q : Z ⟶ Z') (ht : IsColimit t) (k : t.pt ⟶ Z) :
    (Cofork.IsColimit.homIso ht _ (k ≫ q) : Y ⟶ Z') =
      (Cofork.IsColimit.homIso ht _ k : Y ⟶ Z) ≫ q :=
  (Category.assoc _ _ _).symm
#align category_theory.limits.cofork.is_colimit.hom_iso_natural CategoryTheory.Limits.Cofork.IsColimit.homIso_natural

/-- This is a helper construction that can be useful when verifying that a category has all
    equalizers. Given `F : WalkingParallelPair ⥤ C`, which is really the same as
    `parallelPair (F.map left) (F.map right)`, and a fork on `F.map left` and `F.map right`,
    we get a cone on `F`.

    If you're thinking about using this, have a look at `hasEqualizers_of_hasLimit_parallelPair`,
    which you may find to be an easier way of achieving your goal. -/
def Cone.ofFork {F : WalkingParallelPair ⥤ C} (t : Fork (F.map left) (F.map right)) : Cone F
    where
  pt := t.pt
  π :=
    { app := fun X => t.π.app X ≫ eqToHom (by aesop)
                                              -- 🎉 no goals
      naturality := by rintro _ _ (_|_|_) <;> {dsimp; simp [t.condition]}}
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
#align category_theory.limits.cone.of_fork CategoryTheory.Limits.Cone.ofFork

/-- This is a helper construction that can be useful when verifying that a category has all
    coequalizers. Given `F : WalkingParallelPair ⥤ C`, which is really the same as
    `parallelPair (F.map left) (F.map right)`, and a cofork on `F.map left` and `F.map right`,
    we get a cocone on `F`.

    If you're thinking about using this, have a look at
    `hasCoequalizers_of_hasColimit_parallelPair`, which you may find to be an easier way of
    achieving your goal. -/
def Cocone.ofCofork {F : WalkingParallelPair ⥤ C} (t : Cofork (F.map left) (F.map right)) : Cocone F
    where
  pt := t.pt
  ι :=
    { app := fun X => eqToHom (by aesop) ≫ t.ι.app X
                                  -- 🎉 no goals
      naturality := by rintro _ _ (_|_|_) <;> {dsimp; simp [t.condition]}}
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
#align category_theory.limits.cocone.of_cofork CategoryTheory.Limits.Cocone.ofCofork

@[simp]
theorem Cone.ofFork_π {F : WalkingParallelPair ⥤ C} (t : Fork (F.map left) (F.map right)) (j) :
    (Cone.ofFork t).π.app j = t.π.app j ≫ eqToHom (by aesop) := rfl
                                                      -- 🎉 no goals
#align category_theory.limits.cone.of_fork_π CategoryTheory.Limits.Cone.ofFork_π

@[simp]
theorem Cocone.ofCofork_ι {F : WalkingParallelPair ⥤ C} (t : Cofork (F.map left) (F.map right))
    (j) : (Cocone.ofCofork t).ι.app j = eqToHom (by aesop) ≫ t.ι.app j := rfl
                                                    -- 🎉 no goals
#align category_theory.limits.cocone.of_cofork_ι CategoryTheory.Limits.Cocone.ofCofork_ι

/-- Given `F : WalkingParallelPair ⥤ C`, which is really the same as
    `parallelPair (F.map left) (F.map right)` and a cone on `F`, we get a fork on
    `F.map left` and `F.map right`. -/
def Fork.ofCone {F : WalkingParallelPair ⥤ C} (t : Cone F) : Fork (F.map left) (F.map right)
    where
  pt := t.pt
  π := { app := fun X => t.π.app X ≫ eqToHom (by aesop)
                                                 -- 🎉 no goals
         naturality := by rintro _ _ (_|_|_) <;> {dsimp; simp}}
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
#align category_theory.limits.fork.of_cone CategoryTheory.Limits.Fork.ofCone

/-- Given `F : WalkingParallelPair ⥤ C`, which is really the same as
    `parallelPair (F.map left) (F.map right)` and a cocone on `F`, we get a cofork on
    `F.map left` and `F.map right`. -/
def Cofork.ofCocone {F : WalkingParallelPair ⥤ C} (t : Cocone F) : Cofork (F.map left) (F.map right)
    where
  pt := t.pt
  ι := { app := fun X => eqToHom (by aesop) ≫ t.ι.app X
                                     -- 🎉 no goals
         naturality := by rintro _ _ (_|_|_) <;> {dsimp; simp}}
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
#align category_theory.limits.cofork.of_cocone CategoryTheory.Limits.Cofork.ofCocone

@[simp]
theorem Fork.ofCone_π {F : WalkingParallelPair ⥤ C} (t : Cone F) (j) :
    (Fork.ofCone t).π.app j = t.π.app j ≫ eqToHom (by aesop) := rfl
                                                      -- 🎉 no goals
#align category_theory.limits.fork.of_cone_π CategoryTheory.Limits.Fork.ofCone_π

@[simp]
theorem Cofork.ofCocone_ι {F : WalkingParallelPair ⥤ C} (t : Cocone F) (j) :
    (Cofork.ofCocone t).ι.app j = eqToHom (by aesop) ≫ t.ι.app j := rfl
                                              -- 🎉 no goals
#align category_theory.limits.cofork.of_cocone_ι CategoryTheory.Limits.Cofork.ofCocone_ι

@[simp]
theorem Fork.ι_postcompose {f' g' : X ⟶ Y} {α : parallelPair f g ⟶ parallelPair f' g'}
    {c : Fork f g} : Fork.ι ((Cones.postcompose α).obj c) = c.ι ≫ α.app _ :=
  rfl
#align category_theory.limits.fork.ι_postcompose CategoryTheory.Limits.Fork.ι_postcompose

@[simp]
theorem Cofork.π_precompose {f' g' : X ⟶ Y} {α : parallelPair f g ⟶ parallelPair f' g'}
    {c : Cofork f' g'} : Cofork.π ((Cocones.precompose α).obj c) = α.app _ ≫ c.π :=
  rfl
#align category_theory.limits.cofork.π_precompose CategoryTheory.Limits.Cofork.π_precompose

/-- Helper function for constructing morphisms between equalizer forks.
-/
@[simps]
def Fork.mkHom {s t : Fork f g} (k : s.pt ⟶ t.pt) (w : k ≫ t.ι = s.ι) : s ⟶ t where
  Hom := k
  w := by
    rintro ⟨_ | _⟩
    -- ⊢ k ≫ NatTrans.app t.π zero = NatTrans.app s.π zero
    · exact w
      -- 🎉 no goals
    · simp only [Fork.app_one_eq_ι_comp_left,← Category.assoc]
      -- ⊢ (k ≫ ι t) ≫ f = ι s ≫ f
      congr
      -- 🎉 no goals
#align category_theory.limits.fork.mk_hom CategoryTheory.Limits.Fork.mkHom

/-- To construct an isomorphism between forks,
it suffices to give an isomorphism between the cone points
and check that it commutes with the `ι` morphisms.
-/
@[simps]
def Fork.ext {s t : Fork f g} (i : s.pt ≅ t.pt) (w : i.hom ≫ t.ι = s.ι := by aesop_cat) :
    s ≅ t where
  hom := Fork.mkHom i.hom w
  inv := Fork.mkHom i.inv (by rw [← w, Iso.inv_hom_id_assoc])
                              -- 🎉 no goals
#align category_theory.limits.fork.ext CategoryTheory.Limits.Fork.ext

/-- Every fork is isomorphic to one of the form `Fork.of_ι _ _`. -/
def Fork.isoForkOfι (c : Fork f g) : c ≅ Fork.ofι c.ι c.condition :=
  Fork.ext (by simp only [Fork.ofι_pt, Functor.const_obj_obj]; rfl) (by simp)
               -- ⊢ c.pt ≅ c.pt
                                                               -- 🎉 no goals
                                                                        -- 🎉 no goals
#align category_theory.limits.fork.iso_fork_of_ι CategoryTheory.Limits.Fork.isoForkOfι

/-- Helper function for constructing morphisms between coequalizer coforks.
-/
@[simps]
def Cofork.mkHom {s t : Cofork f g} (k : s.pt ⟶ t.pt) (w : s.π ≫ k = t.π) : s ⟶ t where
  Hom := k
  w := by
    rintro ⟨_ | _⟩
    -- ⊢ NatTrans.app s.ι zero ≫ k = NatTrans.app t.ι zero
    · simp [Cofork.app_zero_eq_comp_π_left, w]
      -- 🎉 no goals
    · exact w
      -- 🎉 no goals
#align category_theory.limits.cofork.mk_hom CategoryTheory.Limits.Cofork.mkHom

@[reassoc (attr := simp)]
theorem Fork.hom_comp_ι {s t : Fork f g} (f : s ⟶ t) : f.Hom ≫ t.ι = s.ι := by
  cases s; cases t; cases f; aesop
  -- ⊢ f.Hom ≫ ι t = ι { pt := pt✝, π := π✝ }
           -- ⊢ f.Hom ≫ ι { pt := pt✝, π := π✝ } = ι { pt := pt✝¹, π := π✝¹ }
                    -- ⊢ (ConeMorphism.mk Hom✝).Hom ≫ ι { pt := pt✝, π := π✝ } = ι { pt := pt✝¹, π := …
                             -- 🎉 no goals
#align category_theory.limits.fork.hom_comp_ι CategoryTheory.Limits.Fork.hom_comp_ι

@[reassoc (attr := simp)]
theorem Fork.π_comp_hom {s t : Cofork f g} (f : s ⟶ t) : s.π ≫ f.Hom = t.π := by
  cases s; cases t; cases f; aesop
  -- ⊢ Cofork.π { pt := pt✝, ι := ι✝ } ≫ f.Hom = Cofork.π t
           -- ⊢ Cofork.π { pt := pt✝¹, ι := ι✝¹ } ≫ f.Hom = Cofork.π { pt := pt✝, ι := ι✝ }
                    -- ⊢ Cofork.π { pt := pt✝¹, ι := ι✝¹ } ≫ (CoconeMorphism.mk Hom✝).Hom = Cofork.π  …
                             -- 🎉 no goals
#align category_theory.limits.fork.π_comp_hom CategoryTheory.Limits.Fork.π_comp_hom

/-- To construct an isomorphism between coforks,
it suffices to give an isomorphism between the cocone points
and check that it commutes with the `π` morphisms.
-/
@[simps]
def Cofork.ext {s t : Cofork f g} (i : s.pt ≅ t.pt) (w : s.π ≫ i.hom = t.π := by aesop_cat) :
    s ≅ t where
  hom := Cofork.mkHom i.hom w
  inv := Cofork.mkHom i.inv (by rw [Iso.comp_inv_eq, w])
                                -- 🎉 no goals
#align category_theory.limits.cofork.ext CategoryTheory.Limits.Cofork.ext

/-- Every cofork is isomorphic to one of the form `Cofork.ofπ _ _`. -/
def Cofork.isoCoforkOfπ (c : Cofork f g) : c ≅ Cofork.ofπ c.π c.condition :=
  Cofork.ext (by simp only [Cofork.ofπ_pt, Functor.const_obj_obj]; rfl) (by dsimp; simp)
                 -- ⊢ c.pt ≅ c.pt
                                                                   -- 🎉 no goals
                                                                            -- ⊢ π c ≫ 𝟙 c.pt = π c
                                                                                   -- 🎉 no goals
#align category_theory.limits.cofork.iso_cofork_of_π CategoryTheory.Limits.Cofork.isoCoforkOfπ

variable (f g)

section

/-- `HasEqualizer f g` represents a particular choice of limiting cone
for the parallel pair of morphisms `f` and `g`.
-/
abbrev HasEqualizer :=
  HasLimit (parallelPair f g)
#align category_theory.limits.has_equalizer CategoryTheory.Limits.HasEqualizer

variable [HasEqualizer f g]

/-- If an equalizer of `f` and `g` exists, we can access an arbitrary choice of such by
    saying `equalizer f g`. -/
noncomputable abbrev equalizer : C :=
  limit (parallelPair f g)
#align category_theory.limits.equalizer CategoryTheory.Limits.equalizer

/-- If an equalizer of `f` and `g` exists, we can access the inclusion
    `equalizer f g ⟶ X` by saying `equalizer.ι f g`. -/
noncomputable abbrev equalizer.ι : equalizer f g ⟶ X :=
  limit.π (parallelPair f g) zero
#align category_theory.limits.equalizer.ι CategoryTheory.Limits.equalizer.ι

/-- An equalizer cone for a parallel pair `f` and `g` -/
noncomputable abbrev equalizer.fork : Fork f g :=
  limit.cone (parallelPair f g)
#align category_theory.limits.equalizer.fork CategoryTheory.Limits.equalizer.fork

@[simp]
theorem equalizer.fork_ι : (equalizer.fork f g).ι = equalizer.ι f g :=
  rfl
#align category_theory.limits.equalizer.fork_ι CategoryTheory.Limits.equalizer.fork_ι

@[simp]
theorem equalizer.fork_π_app_zero : (equalizer.fork f g).π.app zero = equalizer.ι f g :=
  rfl
#align category_theory.limits.equalizer.fork_π_app_zero CategoryTheory.Limits.equalizer.fork_π_app_zero

@[reassoc]
theorem equalizer.condition : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g :=
  Fork.condition <| limit.cone <| parallelPair f g
#align category_theory.limits.equalizer.condition CategoryTheory.Limits.equalizer.condition

/-- The equalizer built from `equalizer.ι f g` is limiting. -/
noncomputable def equalizerIsEqualizer : IsLimit (Fork.ofι (equalizer.ι f g)
    (equalizer.condition f g)) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Fork.ext (Iso.refl _) (by aesop))
                                                                  -- 🎉 no goals
#align category_theory.limits.equalizer_is_equalizer CategoryTheory.Limits.equalizerIsEqualizer

variable {f g}

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` factors through the equalizer of `f` and `g`
    via `equalizer.lift : W ⟶ equalizer f g`. -/
noncomputable abbrev equalizer.lift {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) : W ⟶ equalizer f g :=
  limit.lift (parallelPair f g) (Fork.ofι k h)
#align category_theory.limits.equalizer.lift CategoryTheory.Limits.equalizer.lift

-- Porting note: removed simp since simp can prove this and the reassoc version
@[reassoc]
theorem equalizer.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    equalizer.lift k h ≫ equalizer.ι f g = k :=
  limit.lift_π _ _
#align category_theory.limits.equalizer.lift_ι CategoryTheory.Limits.equalizer.lift_ι

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` induces a morphism `l : W ⟶ equalizer f g`
    satisfying `l ≫ equalizer.ι f g = k`. -/
noncomputable def equalizer.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    { l : W ⟶ equalizer f g // l ≫ equalizer.ι f g = k } :=
  ⟨equalizer.lift k h, equalizer.lift_ι _ _⟩
#align category_theory.limits.equalizer.lift' CategoryTheory.Limits.equalizer.lift'

/-- Two maps into an equalizer are equal if they are equal when composed with the equalizer map. -/
@[ext]
theorem equalizer.hom_ext {W : C} {k l : W ⟶ equalizer f g}
    (h : k ≫ equalizer.ι f g = l ≫ equalizer.ι f g) : k = l :=
  Fork.IsLimit.hom_ext (limit.isLimit _) h
#align category_theory.limits.equalizer.hom_ext CategoryTheory.Limits.equalizer.hom_ext

theorem equalizer.existsUnique {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    ∃! l : W ⟶ equalizer f g, l ≫ equalizer.ι f g = k :=
  Fork.IsLimit.existsUnique (limit.isLimit _) _ h
#align category_theory.limits.equalizer.exists_unique CategoryTheory.Limits.equalizer.existsUnique

/-- An equalizer morphism is a monomorphism -/
instance equalizer.ι_mono : Mono (equalizer.ι f g) where
  right_cancellation _ _ w := equalizer.hom_ext w
#align category_theory.limits.equalizer.ι_mono CategoryTheory.Limits.equalizer.ι_mono

end

section

variable {f g}

/-- The equalizer morphism in any limit cone is a monomorphism. -/
theorem mono_of_isLimit_fork {c : Fork f g} (i : IsLimit c) : Mono (Fork.ι c) :=
  { right_cancellation := fun _ _ w => Fork.IsLimit.hom_ext i w }
#align category_theory.limits.mono_of_is_limit_fork CategoryTheory.Limits.mono_of_isLimit_fork

end

section

variable {f g}

/-- The identity determines a cone on the equalizer diagram of `f` and `g` if `f = g`. -/
def idFork (h : f = g) : Fork f g :=
  Fork.ofι (𝟙 X) <| h ▸ rfl
#align category_theory.limits.id_fork CategoryTheory.Limits.idFork

/-- The identity on `X` is an equalizer of `(f, g)`, if `f = g`. -/
def isLimitIdFork (h : f = g) : IsLimit (idFork h) :=
  Fork.IsLimit.mk _ (fun s => Fork.ι s) (fun s => Category.comp_id _) fun s m h => by
    convert h
    -- ⊢ m = m ≫ Fork.ι (idFork h✝)
    exact (Category.comp_id _).symm
    -- 🎉 no goals
#align category_theory.limits.is_limit_id_fork CategoryTheory.Limits.isLimitIdFork

/-- Every equalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
theorem isIso_limit_cone_parallelPair_of_eq (h₀ : f = g) {c : Fork f g} (h : IsLimit c) :
    IsIso c.ι :=
  IsIso.of_iso <| IsLimit.conePointUniqueUpToIso h <| isLimitIdFork h₀
#align category_theory.limits.is_iso_limit_cone_parallel_pair_of_eq CategoryTheory.Limits.isIso_limit_cone_parallelPair_of_eq

/-- The equalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
theorem equalizer.ι_of_eq [HasEqualizer f g] (h : f = g) : IsIso (equalizer.ι f g) :=
  isIso_limit_cone_parallelPair_of_eq h <| limit.isLimit _
#align category_theory.limits.equalizer.ι_of_eq CategoryTheory.Limits.equalizer.ι_of_eq

/-- Every equalizer of `(f, f)` is an isomorphism. -/
theorem isIso_limit_cone_parallelPair_of_self {c : Fork f f} (h : IsLimit c) : IsIso c.ι :=
  isIso_limit_cone_parallelPair_of_eq rfl h
#align category_theory.limits.is_iso_limit_cone_parallel_pair_of_self CategoryTheory.Limits.isIso_limit_cone_parallelPair_of_self

/-- An equalizer that is an epimorphism is an isomorphism. -/
theorem isIso_limit_cone_parallelPair_of_epi {c : Fork f g} (h : IsLimit c) [Epi c.ι] : IsIso c.ι :=
  isIso_limit_cone_parallelPair_of_eq ((cancel_epi _).1 (Fork.condition c)) h
#align category_theory.limits.is_iso_limit_cone_parallel_pair_of_epi CategoryTheory.Limits.isIso_limit_cone_parallelPair_of_epi

/-- Two morphisms are equal if there is a fork whose inclusion is epi. -/
theorem eq_of_epi_fork_ι (t : Fork f g) [Epi (Fork.ι t)] : f = g :=
  (cancel_epi (Fork.ι t)).1 <| Fork.condition t
#align category_theory.limits.eq_of_epi_fork_ι CategoryTheory.Limits.eq_of_epi_fork_ι

/-- If the equalizer of two morphisms is an epimorphism, then the two morphisms are equal. -/
theorem eq_of_epi_equalizer [HasEqualizer f g] [Epi (equalizer.ι f g)] : f = g :=
  (cancel_epi (equalizer.ι f g)).1 <| equalizer.condition _ _
#align category_theory.limits.eq_of_epi_equalizer CategoryTheory.Limits.eq_of_epi_equalizer

end

instance hasEqualizer_of_self : HasEqualizer f f :=
  HasLimit.mk
    { cone := idFork rfl
      isLimit := isLimitIdFork rfl }
#align category_theory.limits.has_equalizer_of_self CategoryTheory.Limits.hasEqualizer_of_self

/-- The equalizer inclusion for `(f, f)` is an isomorphism. -/
instance equalizer.ι_of_self : IsIso (equalizer.ι f f) :=
  equalizer.ι_of_eq rfl
#align category_theory.limits.equalizer.ι_of_self CategoryTheory.Limits.equalizer.ι_of_self

/-- The equalizer of a morphism with itself is isomorphic to the source. -/
noncomputable def equalizer.isoSourceOfSelf : equalizer f f ≅ X :=
  asIso (equalizer.ι f f)
#align category_theory.limits.equalizer.iso_source_of_self CategoryTheory.Limits.equalizer.isoSourceOfSelf

@[simp]
theorem equalizer.isoSourceOfSelf_hom : (equalizer.isoSourceOfSelf f).hom = equalizer.ι f f :=
  rfl
#align category_theory.limits.equalizer.iso_source_of_self_hom CategoryTheory.Limits.equalizer.isoSourceOfSelf_hom

@[simp]
theorem equalizer.isoSourceOfSelf_inv :
    (equalizer.isoSourceOfSelf f).inv = equalizer.lift (𝟙 X) (by simp) := by
                                                                 -- 🎉 no goals
  ext
  -- ⊢ (isoSourceOfSelf f).inv ≫ ι f f = lift (𝟙 X) (_ : 𝟙 X ≫ f = 𝟙 X ≫ f) ≫ ι f f
  simp [equalizer.isoSourceOfSelf]
  -- 🎉 no goals
#align category_theory.limits.equalizer.iso_source_of_self_inv CategoryTheory.Limits.equalizer.isoSourceOfSelf_inv

section

/-- `HasCoequalizer f g` represents a particular choice of colimiting cocone
for the parallel pair of morphisms `f` and `g`.
-/
abbrev HasCoequalizer :=
  HasColimit (parallelPair f g)
#align category_theory.limits.has_coequalizer CategoryTheory.Limits.HasCoequalizer

variable [HasCoequalizer f g]

/-- If a coequalizer of `f` and `g` exists, we can access an arbitrary choice of such by
    saying `coequalizer f g`. -/
noncomputable abbrev coequalizer : C :=
  colimit (parallelPair f g)
#align category_theory.limits.coequalizer CategoryTheory.Limits.coequalizer

/-- If a coequalizer of `f` and `g` exists, we can access the corresponding projection by
    saying `coequalizer.π f g`. -/
noncomputable abbrev coequalizer.π : Y ⟶ coequalizer f g :=
  colimit.ι (parallelPair f g) one
#align category_theory.limits.coequalizer.π CategoryTheory.Limits.coequalizer.π

/-- An arbitrary choice of coequalizer cocone for a parallel pair `f` and `g`.
-/
noncomputable abbrev coequalizer.cofork : Cofork f g :=
  colimit.cocone (parallelPair f g)
#align category_theory.limits.coequalizer.cofork CategoryTheory.Limits.coequalizer.cofork

@[simp]
theorem coequalizer.cofork_π : (coequalizer.cofork f g).π = coequalizer.π f g :=
  rfl
#align category_theory.limits.coequalizer.cofork_π CategoryTheory.Limits.coequalizer.cofork_π

-- Porting note: simp can prove this, simp removed
theorem coequalizer.cofork_ι_app_one : (coequalizer.cofork f g).ι.app one = coequalizer.π f g :=
  rfl
#align category_theory.limits.coequalizer.cofork_ι_app_one CategoryTheory.Limits.coequalizer.cofork_ι_app_one

@[reassoc]
theorem coequalizer.condition : f ≫ coequalizer.π f g = g ≫ coequalizer.π f g :=
  Cofork.condition <| colimit.cocone <| parallelPair f g
#align category_theory.limits.coequalizer.condition CategoryTheory.Limits.coequalizer.condition

/-- The cofork built from `coequalizer.π f g` is colimiting. -/
noncomputable def coequalizerIsCoequalizer :
    IsColimit (Cofork.ofπ (coequalizer.π f g) (coequalizer.condition f g)) :=
  IsColimit.ofIsoColimit (colimit.isColimit _) (Cofork.ext (Iso.refl _) (by aesop))
                                                                            -- 🎉 no goals
#align category_theory.limits.coequalizer_is_coequalizer CategoryTheory.Limits.coequalizerIsCoequalizer

variable {f g}

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = g ≫ k` factors through the coequalizer of `f`
    and `g` via `coequalizer.desc : coequalizer f g ⟶ W`. -/
noncomputable abbrev coequalizer.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
    coequalizer f g ⟶ W :=
  colimit.desc (parallelPair f g) (Cofork.ofπ k h)
#align category_theory.limits.coequalizer.desc CategoryTheory.Limits.coequalizer.desc

-- Porting note: removing simp since simp can prove this and reassoc version
@[reassoc]
theorem coequalizer.π_desc {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
    coequalizer.π f g ≫ coequalizer.desc k h = k :=
  colimit.ι_desc _ _
#align category_theory.limits.coequalizer.π_desc CategoryTheory.Limits.coequalizer.π_desc

theorem coequalizer.π_colimMap_desc {X' Y' Z : C} (f' g' : X' ⟶ Y') [HasCoequalizer f' g']
    (p : X ⟶ X') (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') (h : Y' ⟶ Z)
    (wh : f' ≫ h = g' ≫ h) :
    coequalizer.π f g ≫ colimMap (parallelPairHom f g f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h :=
  by rw [ι_colimMap_assoc, parallelPairHom_app_one, coequalizer.π_desc]
     -- 🎉 no goals
#align category_theory.limits.coequalizer.π_colim_map_desc CategoryTheory.Limits.coequalizer.π_colimMap_desc

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = g ≫ k` induces a morphism
    `l : coequalizer f g ⟶ W` satisfying `coequalizer.π ≫ g = l`. -/
noncomputable def coequalizer.desc' {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
    { l : coequalizer f g ⟶ W // coequalizer.π f g ≫ l = k } :=
  ⟨coequalizer.desc k h, coequalizer.π_desc _ _⟩
#align category_theory.limits.coequalizer.desc' CategoryTheory.Limits.coequalizer.desc'

/-- Two maps from a coequalizer are equal if they are equal when composed with the coequalizer
    map -/
@[ext]
theorem coequalizer.hom_ext {W : C} {k l : coequalizer f g ⟶ W}
    (h : coequalizer.π f g ≫ k = coequalizer.π f g ≫ l) : k = l :=
  Cofork.IsColimit.hom_ext (colimit.isColimit _) h
#align category_theory.limits.coequalizer.hom_ext CategoryTheory.Limits.coequalizer.hom_ext

theorem coequalizer.existsUnique {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
    ∃! d : coequalizer f g ⟶ W, coequalizer.π f g ≫ d = k :=
  Cofork.IsColimit.existsUnique (colimit.isColimit _) _ h
#align category_theory.limits.coequalizer.exists_unique CategoryTheory.Limits.coequalizer.existsUnique

/-- A coequalizer morphism is an epimorphism -/
instance coequalizer.π_epi : Epi (coequalizer.π f g) where
  left_cancellation _ _ w := coequalizer.hom_ext w
#align category_theory.limits.coequalizer.π_epi CategoryTheory.Limits.coequalizer.π_epi

end

section

variable {f g}

/-- The coequalizer morphism in any colimit cocone is an epimorphism. -/
theorem epi_of_isColimit_cofork {c : Cofork f g} (i : IsColimit c) : Epi c.π :=
  { left_cancellation := fun _ _ w => Cofork.IsColimit.hom_ext i w }
#align category_theory.limits.epi_of_is_colimit_cofork CategoryTheory.Limits.epi_of_isColimit_cofork

end

section

variable {f g}

/-- The identity determines a cocone on the coequalizer diagram of `f` and `g`, if `f = g`. -/
def idCofork (h : f = g) : Cofork f g :=
  Cofork.ofπ (𝟙 Y) <| h ▸ rfl
#align category_theory.limits.id_cofork CategoryTheory.Limits.idCofork

/-- The identity on `Y` is a coequalizer of `(f, g)`, where `f = g`.  -/
def isColimitIdCofork (h : f = g) : IsColimit (idCofork h) :=
  Cofork.IsColimit.mk _ (fun s => Cofork.π s) (fun s => Category.id_comp _) fun s m h => by
    convert h
    -- ⊢ m = Cofork.π (idCofork h✝) ≫ m
    exact (Category.id_comp _).symm
    -- 🎉 no goals
#align category_theory.limits.is_colimit_id_cofork CategoryTheory.Limits.isColimitIdCofork

/-- Every coequalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
theorem isIso_colimit_cocone_parallelPair_of_eq (h₀ : f = g) {c : Cofork f g} (h : IsColimit c) :
    IsIso c.π :=
  IsIso.of_iso <| IsColimit.coconePointUniqueUpToIso (isColimitIdCofork h₀) h
#align category_theory.limits.is_iso_colimit_cocone_parallel_pair_of_eq CategoryTheory.Limits.isIso_colimit_cocone_parallelPair_of_eq

/-- The coequalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
theorem coequalizer.π_of_eq [HasCoequalizer f g] (h : f = g) : IsIso (coequalizer.π f g) :=
  isIso_colimit_cocone_parallelPair_of_eq h <| colimit.isColimit _
#align category_theory.limits.coequalizer.π_of_eq CategoryTheory.Limits.coequalizer.π_of_eq

/-- Every coequalizer of `(f, f)` is an isomorphism. -/
theorem isIso_colimit_cocone_parallelPair_of_self {c : Cofork f f} (h : IsColimit c) : IsIso c.π :=
  isIso_colimit_cocone_parallelPair_of_eq rfl h
#align category_theory.limits.is_iso_colimit_cocone_parallel_pair_of_self CategoryTheory.Limits.isIso_colimit_cocone_parallelPair_of_self

/-- A coequalizer that is a monomorphism is an isomorphism. -/
theorem isIso_limit_cocone_parallelPair_of_epi {c : Cofork f g} (h : IsColimit c) [Mono c.π] :
    IsIso c.π :=
  isIso_colimit_cocone_parallelPair_of_eq ((cancel_mono _).1 (Cofork.condition c)) h
#align category_theory.limits.is_iso_limit_cocone_parallel_pair_of_epi CategoryTheory.Limits.isIso_limit_cocone_parallelPair_of_epi

/-- Two morphisms are equal if there is a cofork whose projection is mono. -/
theorem eq_of_mono_cofork_π (t : Cofork f g) [Mono (Cofork.π t)] : f = g :=
  (cancel_mono (Cofork.π t)).1 <| Cofork.condition t
#align category_theory.limits.eq_of_mono_cofork_π CategoryTheory.Limits.eq_of_mono_cofork_π

/-- If the coequalizer of two morphisms is a monomorphism, then the two morphisms are equal. -/
theorem eq_of_mono_coequalizer [HasCoequalizer f g] [Mono (coequalizer.π f g)] : f = g :=
  (cancel_mono (coequalizer.π f g)).1 <| coequalizer.condition _ _
#align category_theory.limits.eq_of_mono_coequalizer CategoryTheory.Limits.eq_of_mono_coequalizer

end

instance hasCoequalizer_of_self : HasCoequalizer f f :=
  HasColimit.mk
    { cocone := idCofork rfl
      isColimit := isColimitIdCofork rfl }
#align category_theory.limits.has_coequalizer_of_self CategoryTheory.Limits.hasCoequalizer_of_self

/-- The coequalizer projection for `(f, f)` is an isomorphism. -/
instance coequalizer.π_of_self : IsIso (coequalizer.π f f) :=
  coequalizer.π_of_eq rfl
#align category_theory.limits.coequalizer.π_of_self CategoryTheory.Limits.coequalizer.π_of_self

/-- The coequalizer of a morphism with itself is isomorphic to the target. -/
noncomputable def coequalizer.isoTargetOfSelf : coequalizer f f ≅ Y :=
  (asIso (coequalizer.π f f)).symm
#align category_theory.limits.coequalizer.iso_target_of_self CategoryTheory.Limits.coequalizer.isoTargetOfSelf

@[simp]
theorem coequalizer.isoTargetOfSelf_hom :
    (coequalizer.isoTargetOfSelf f).hom = coequalizer.desc (𝟙 Y) (by simp) := by
                                                                     -- 🎉 no goals
  ext
  -- ⊢ π f f ≫ (isoTargetOfSelf f).hom = π f f ≫ desc (𝟙 Y) (_ : f ≫ 𝟙 Y = f ≫ 𝟙 Y)
  simp [coequalizer.isoTargetOfSelf]
  -- 🎉 no goals
#align category_theory.limits.coequalizer.iso_target_of_self_hom CategoryTheory.Limits.coequalizer.isoTargetOfSelf_hom

@[simp]
theorem coequalizer.isoTargetOfSelf_inv : (coequalizer.isoTargetOfSelf f).inv = coequalizer.π f f :=
  rfl
#align category_theory.limits.coequalizer.iso_target_of_self_inv CategoryTheory.Limits.coequalizer.isoTargetOfSelf_inv

section Comparison

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

/-- The comparison morphism for the equalizer of `f,g`.
This is an isomorphism iff `G` preserves the equalizer of `f,g`; see
`CategoryTheory/Limits/Preserves/Shapes/Equalizers.lean`
-/
noncomputable def equalizerComparison [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] :
    G.obj (equalizer f g) ⟶ equalizer (G.map f) (G.map g) :=
  equalizer.lift (G.map (equalizer.ι _ _))
    (by simp only [← G.map_comp]; rw[equalizer.condition])
        -- ⊢ G.map (equalizer.ι f g ≫ f) = G.map (equalizer.ι f g ≫ g)
                                  -- 🎉 no goals
#align category_theory.limits.equalizer_comparison CategoryTheory.Limits.equalizerComparison

@[reassoc (attr := simp)]
theorem equalizerComparison_comp_π [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] :
    equalizerComparison f g G ≫ equalizer.ι (G.map f) (G.map g) = G.map (equalizer.ι f g) :=
  equalizer.lift_ι _ _
#align category_theory.limits.equalizer_comparison_comp_π CategoryTheory.Limits.equalizerComparison_comp_π

@[reassoc (attr := simp)]
theorem map_lift_equalizerComparison [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] {Z : C}
    {h : Z ⟶ X} (w : h ≫ f = h ≫ g) :
    G.map (equalizer.lift h w) ≫ equalizerComparison f g G =
      equalizer.lift (G.map h) (by simp only [← G.map_comp, w]) := by
                                   -- 🎉 no goals
  apply equalizer.hom_ext
  -- ⊢ (G.map (equalizer.lift h w) ≫ equalizerComparison f g G) ≫ equalizer.ι (G.ma …
  simp [← G.map_comp]
  -- 🎉 no goals
#align category_theory.limits.map_lift_equalizer_comparison CategoryTheory.Limits.map_lift_equalizerComparison

/-- The comparison morphism for the coequalizer of `f,g`. -/
noncomputable def coequalizerComparison [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.map g)] :
    coequalizer (G.map f) (G.map g) ⟶ G.obj (coequalizer f g) :=
  coequalizer.desc (G.map (coequalizer.π _ _))
    (by simp only [← G.map_comp]; rw [coequalizer.condition])
        -- ⊢ G.map (f ≫ coequalizer.π f g) = G.map (g ≫ coequalizer.π f g)
                                  -- 🎉 no goals
#align category_theory.limits.coequalizer_comparison CategoryTheory.Limits.coequalizerComparison

@[reassoc (attr := simp)]
theorem ι_comp_coequalizerComparison [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.map g)] :
    coequalizer.π _ _ ≫ coequalizerComparison f g G = G.map (coequalizer.π _ _) :=
  coequalizer.π_desc _ _
#align category_theory.limits.ι_comp_coequalizer_comparison CategoryTheory.Limits.ι_comp_coequalizerComparison

@[reassoc (attr := simp)]
theorem coequalizerComparison_map_desc [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.map g)]
    {Z : C} {h : Y ⟶ Z} (w : f ≫ h = g ≫ h) :
    coequalizerComparison f g G ≫ G.map (coequalizer.desc h w) =
      coequalizer.desc (G.map h) (by simp only [← G.map_comp, w]) := by
                                     -- 🎉 no goals
  apply coequalizer.hom_ext
  -- ⊢ coequalizer.π (G.map f) (G.map g) ≫ coequalizerComparison f g G ≫ G.map (coe …
  simp [← G.map_comp]
  -- 🎉 no goals
#align category_theory.limits.coequalizer_comparison_map_desc CategoryTheory.Limits.coequalizerComparison_map_desc

end Comparison

variable (C)

/-- `HasEqualizers` represents a choice of equalizer for every pair of morphisms -/
abbrev HasEqualizers :=
  HasLimitsOfShape WalkingParallelPair C
#align category_theory.limits.has_equalizers CategoryTheory.Limits.HasEqualizers

/-- `HasCoequalizers` represents a choice of coequalizer for every pair of morphisms -/
abbrev HasCoequalizers :=
  HasColimitsOfShape WalkingParallelPair C
#align category_theory.limits.has_coequalizers CategoryTheory.Limits.HasCoequalizers

/-- If `C` has all limits of diagrams `parallelPair f g`, then it has all equalizers -/
theorem hasEqualizers_of_hasLimit_parallelPair
    [∀ {X Y : C} {f g : X ⟶ Y}, HasLimit (parallelPair f g)] : HasEqualizers C :=
  { has_limit := fun F => hasLimitOfIso (diagramIsoParallelPair F).symm }
#align category_theory.limits.has_equalizers_of_has_limit_parallel_pair CategoryTheory.Limits.hasEqualizers_of_hasLimit_parallelPair

/-- If `C` has all colimits of diagrams `parallelPair f g`, then it has all coequalizers -/
theorem hasCoequalizers_of_hasColimit_parallelPair
    [∀ {X Y : C} {f g : X ⟶ Y}, HasColimit (parallelPair f g)] : HasCoequalizers C :=
  { has_colimit := fun F => hasColimitOfIso (diagramIsoParallelPair F) }
#align category_theory.limits.has_coequalizers_of_has_colimit_parallel_pair CategoryTheory.Limits.hasCoequalizers_of_hasColimit_parallelPair

section

-- In this section we show that a split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
variable {C} [IsSplitMono f]

/-- A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
Here we build the cone, and show in `isSplitMonoEqualizes` that it is a limit cone.
-/
-- @[simps (config := { rhsMd := semireducible })] Porting note: no semireducible
@[simps!]
noncomputable def coneOfIsSplitMono : Fork (𝟙 Y) (retraction f ≫ f) :=
  Fork.ofι f (by simp)
                 -- 🎉 no goals
#align category_theory.limits.cone_of_is_split_mono CategoryTheory.Limits.coneOfIsSplitMono

@[simp]
theorem coneOfIsSplitMono_ι : (coneOfIsSplitMono f).ι = f :=
  rfl
#align category_theory.limits.cone_of_is_split_mono_ι CategoryTheory.Limits.coneOfIsSplitMono_ι

/-- A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
-/
noncomputable def isSplitMonoEqualizes {X Y : C} (f : X ⟶ Y) [IsSplitMono f] :
    IsLimit (coneOfIsSplitMono f) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ retraction f, by
      dsimp
      -- ⊢ (Fork.ι s ≫ retraction f) ≫ f = Fork.ι s
      rw [Category.assoc, ← s.condition]
      -- ⊢ Fork.ι s ≫ 𝟙 Y = Fork.ι s
      apply Category.comp_id, fun hm => by simp [← hm]⟩
      -- 🎉 no goals
                                           -- 🎉 no goals
#align category_theory.limits.is_split_mono_equalizes CategoryTheory.Limits.isSplitMonoEqualizes

end

/-- We show that the converse to `isSplitMonoEqualizes` is true:
Whenever `f` equalizes `(r ≫ f)` and `(𝟙 Y)`, then `r` is a retraction of `f`. -/
def splitMonoOfEqualizer {X Y : C} {f : X ⟶ Y} {r : Y ⟶ X} (hr : f ≫ r ≫ f = f)
    (h : IsLimit (Fork.ofι f (hr.trans (Category.comp_id _).symm : f ≫ r ≫ f = f ≫ 𝟙 Y))) :
    SplitMono f where
  retraction := r
  id := Fork.IsLimit.hom_ext h ((Category.assoc _ _ _).trans <| hr.trans (Category.id_comp _).symm)
#align category_theory.limits.split_mono_of_equalizer CategoryTheory.Limits.splitMonoOfEqualizer

variable {C f g}

/-- The fork obtained by postcomposing an equalizer fork with a monomorphism is an equalizer. -/
def isEqualizerCompMono {c : Fork f g} (i : IsLimit c) {Z : C} (h : Y ⟶ Z) [hm : Mono h] :
    have : Fork.ι c ≫ f ≫ h = Fork.ι c ≫ g ≫ h := by
      simp only [←Category.assoc]
      -- ⊢ (Fork.ι c ≫ f) ≫ h = (Fork.ι c ≫ g) ≫ h
      exact congrArg (· ≫ h) c.condition;
      -- 🎉 no goals
    IsLimit (Fork.ofι c.ι (by simp [this]) : Fork (f ≫ h) (g ≫ h)) :=
                              -- 🎉 no goals
  Fork.IsLimit.mk' _ fun s =>
    let s' : Fork f g := Fork.ofι s.ι (by apply hm.right_cancellation; simp [s.condition])
                                          -- ⊢ (Fork.ι s ≫ f) ≫ h = (Fork.ι s ≫ g) ≫ h
                                                                       -- 🎉 no goals
    let l := Fork.IsLimit.lift' i s'.ι s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Fork.IsLimit.hom_ext i; rw [Fork.ι_ofι] at hm; rw [hm]; exact l.2.symm⟩
      -- ⊢ m✝ ≫ Fork.ι c = ↑l ≫ Fork.ι c
                                    -- ⊢ m✝ ≫ Fork.ι c = ↑l ≫ Fork.ι c
                                                           -- ⊢ Fork.ι s = ↑l ≫ Fork.ι c
                                                                    -- 🎉 no goals
#align category_theory.limits.is_equalizer_comp_mono CategoryTheory.Limits.isEqualizerCompMono

variable (C f g)

@[instance]
theorem hasEqualizer_comp_mono [HasEqualizer f g] {Z : C} (h : Y ⟶ Z) [Mono h] :
    HasEqualizer (f ≫ h) (g ≫ h) :=
  ⟨⟨{   cone := _
        isLimit := isEqualizerCompMono (limit.isLimit _) h }⟩⟩
#align category_theory.limits.has_equalizer_comp_mono CategoryTheory.Limits.hasEqualizer_comp_mono

/-- An equalizer of an idempotent morphism and the identity is split mono. -/
@[simps]
def splitMonoOfIdempotentOfIsLimitFork {X : C} {f : X ⟶ X} (hf : f ≫ f = f) {c : Fork (𝟙 X) f}
    (i : IsLimit c) : SplitMono c.ι where
  retraction := i.lift (Fork.ofι f (by simp [hf]))
                                       -- 🎉 no goals
  id := by
    letI := mono_of_isLimit_fork i
    -- ⊢ Fork.ι c ≫ IsLimit.lift i (Fork.ofι f (_ : f ≫ 𝟙 X = f ≫ f)) = 𝟙 (((Functor. …
    rw [← cancel_mono_id c.ι, Category.assoc, Fork.IsLimit.lift_ι, Fork.ι_ofι, ← c.condition]
    -- ⊢ Fork.ι c ≫ 𝟙 X = Fork.ι c
    exact Category.comp_id c.ι
    -- 🎉 no goals
#align category_theory.limits.split_mono_of_idempotent_of_is_limit_fork CategoryTheory.Limits.splitMonoOfIdempotentOfIsLimitFork

/-- The equalizer of an idempotent morphism and the identity is split mono. -/
noncomputable def splitMonoOfIdempotentEqualizer {X : C} {f : X ⟶ X} (hf : f ≫ f = f)
    [HasEqualizer (𝟙 X) f] : SplitMono (equalizer.ι (𝟙 X) f) :=
  splitMonoOfIdempotentOfIsLimitFork _ hf (limit.isLimit _)
#align category_theory.limits.split_mono_of_idempotent_equalizer CategoryTheory.Limits.splitMonoOfIdempotentEqualizer

section

-- In this section we show that a split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
variable {C} [IsSplitEpi f]

/-- A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
Here we build the cocone, and show in `isSplitEpiCoequalizes` that it is a colimit cocone.
-/
-- @[simps (config := { rhsMd := semireducible })] Porting note: no semireducible
@[simps!]
noncomputable def coconeOfIsSplitEpi : Cofork (𝟙 X) (f ≫ section_ f) :=
  Cofork.ofπ f (by simp)
                   -- 🎉 no goals
#align category_theory.limits.cocone_of_is_split_epi CategoryTheory.Limits.coconeOfIsSplitEpi

@[simp]
theorem coconeOfIsSplitEpi_π : (coconeOfIsSplitEpi f).π = f :=
  rfl
#align category_theory.limits.cocone_of_is_split_epi_π CategoryTheory.Limits.coconeOfIsSplitEpi_π

/-- A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
-/
noncomputable def isSplitEpiCoequalizes {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] :
    IsColimit (coconeOfIsSplitEpi f) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨section_ f ≫ s.π, by
      dsimp
      -- ⊢ f ≫ section_ f ≫ Cofork.π s = Cofork.π s
      rw [← Category.assoc, ← s.condition, Category.id_comp], fun hm => by simp [← hm]⟩
      -- 🎉 no goals
                                                                           -- 🎉 no goals
#align category_theory.limits.is_split_epi_coequalizes CategoryTheory.Limits.isSplitEpiCoequalizes

end

/-- We show that the converse to `isSplitEpiEqualizes` is true:
Whenever `f` coequalizes `(f ≫ s)` and `(𝟙 X)`, then `s` is a section of `f`. -/
def splitEpiOfCoequalizer {X Y : C} {f : X ⟶ Y} {s : Y ⟶ X} (hs : f ≫ s ≫ f = f)
    (h :
      IsColimit
        (Cofork.ofπ f
          ((Category.assoc _ _ _).trans <| hs.trans (Category.id_comp f).symm :
            (f ≫ s) ≫ f = 𝟙 X ≫ f))) :
    SplitEpi f where
  section_ := s
  id := Cofork.IsColimit.hom_ext h (hs.trans (Category.comp_id _).symm)
#align category_theory.limits.split_epi_of_coequalizer CategoryTheory.Limits.splitEpiOfCoequalizer

variable {C f g}

/-- The cofork obtained by precomposing a coequalizer cofork with an epimorphism is
a coequalizer. -/
def isCoequalizerEpiComp {c : Cofork f g} (i : IsColimit c) {W : C} (h : W ⟶ X) [hm : Epi h] :
    have : (h ≫ f) ≫ Cofork.π c = (h ≫ g) ≫ Cofork.π c := by
      simp only [Category.assoc]
      -- ⊢ h ≫ f ≫ Cofork.π c = h ≫ g ≫ Cofork.π c
      exact congrArg (h ≫ ·) c.condition
      -- 🎉 no goals
    IsColimit (Cofork.ofπ c.π (this) : Cofork (h ≫ f) (h ≫ g)) :=
  Cofork.IsColimit.mk' _ fun s =>
    let s' : Cofork f g :=
      Cofork.ofπ s.π (by apply hm.left_cancellation; simp_rw [← Category.assoc, s.condition])
                         -- ⊢ h ≫ f ≫ Cofork.π s = h ≫ g ≫ Cofork.π s
                                                     -- 🎉 no goals
    let l := Cofork.IsColimit.desc' i s'.π s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Cofork.IsColimit.hom_ext i; rw [Cofork.π_ofπ] at hm; rw [hm]; exact l.2.symm⟩
      -- ⊢ Cofork.π c ≫ m✝ = Cofork.π c ≫ ↑l
                                        -- ⊢ Cofork.π c ≫ m✝ = Cofork.π c ≫ ↑l
                                                                 -- ⊢ Cofork.π s = Cofork.π c ≫ ↑l
                                                                          -- 🎉 no goals
#align category_theory.limits.is_coequalizer_epi_comp CategoryTheory.Limits.isCoequalizerEpiComp

theorem hasCoequalizer_epi_comp [HasCoequalizer f g] {W : C} (h : W ⟶ X) [Epi h] :
    HasCoequalizer (h ≫ f) (h ≫ g) :=
  ⟨⟨{   cocone := _
        isColimit := isCoequalizerEpiComp (colimit.isColimit _) h }⟩⟩
#align category_theory.limits.has_coequalizer_epi_comp CategoryTheory.Limits.hasCoequalizer_epi_comp

variable (C f g)

/-- A coequalizer of an idempotent morphism and the identity is split epi. -/
@[simps]
def splitEpiOfIdempotentOfIsColimitCofork {X : C} {f : X ⟶ X} (hf : f ≫ f = f) {c : Cofork (𝟙 X) f}
    (i : IsColimit c) : SplitEpi c.π where
  section_ := i.desc (Cofork.ofπ f (by simp [hf]))
                                       -- 🎉 no goals
  id := by
    letI := epi_of_isColimit_cofork i
    -- ⊢ IsColimit.desc i (Cofork.ofπ f (_ : 𝟙 X ≫ f = f ≫ f)) ≫ Cofork.π c = 𝟙 (((Fu …
    rw [← cancel_epi_id c.π, ← Category.assoc, Cofork.IsColimit.π_desc, Cofork.π_ofπ, ←
      c.condition]
    exact Category.id_comp _
    -- 🎉 no goals
#align category_theory.limits.split_epi_of_idempotent_of_is_colimit_cofork CategoryTheory.Limits.splitEpiOfIdempotentOfIsColimitCofork

/-- The coequalizer of an idempotent morphism and the identity is split epi. -/
noncomputable def splitEpiOfIdempotentCoequalizer {X : C} {f : X ⟶ X} (hf : f ≫ f = f)
    [HasCoequalizer (𝟙 X) f] : SplitEpi (coequalizer.π (𝟙 X) f) :=
  splitEpiOfIdempotentOfIsColimitCofork _ hf (colimit.isColimit _)
#align category_theory.limits.split_epi_of_idempotent_coequalizer CategoryTheory.Limits.splitEpiOfIdempotentCoequalizer

end CategoryTheory.Limits
