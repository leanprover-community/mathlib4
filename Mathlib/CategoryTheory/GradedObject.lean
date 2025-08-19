/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.Data.Set.Subsingleton
import Mathlib.Algebra.Group.Int.Defs

/-!
# The category of graded objects

For any type `β`, a `β`-graded object over some category `C` is just
a function `β → C` into the objects of `C`.
We put the "pointwise" category structure on these, as the non-dependent specialization of
`CategoryTheory.Pi`.

We describe the `comap` functors obtained by precomposing with functions `β → γ`.

As a consequence a fixed element (e.g. `1`) in an additive group `β` provides a shift
functor on `β`-graded objects

When `C` has coproducts we construct the `total` functor `GradedObject β C ⥤ C`,
show that it is faithful, and deduce that when `C` is concrete so is `GradedObject β C`.

A covariant functoriality of `GradedObject β C` with respect to the index set `β` is also
introduced: if `p : I → J` is a map such that `C` has coproducts indexed by `p ⁻¹' {j}`, we
have a functor `map : GradedObject I C ⥤ GradedObject J C`.

-/

namespace CategoryTheory

open Category Limits

universe w v u

/-- A type synonym for `β → C`, used for `β`-graded objects in a category `C`. -/
def GradedObject (β : Type w) (C : Type u) : Type max w u :=
  β → C

-- Satisfying the inhabited linter...
instance inhabitedGradedObject (β : Type w) (C : Type u) [Inhabited C] :
    Inhabited (GradedObject β C) :=
  ⟨fun _ ↦ Inhabited.default⟩

-- `s` is here to distinguish type synonyms asking for different shifts
/-- A type synonym for `β → C`, used for `β`-graded objects in a category `C`
with a shift functor given by translation by `s`.
-/
@[nolint unusedArguments]
abbrev GradedObjectWithShift {β : Type w} [AddCommGroup β] (_ : β) (C : Type u) : Type max w u :=
  GradedObject β C

namespace GradedObject

variable {C : Type u} [Category.{v} C]

@[simps!]
instance categoryOfGradedObjects (β : Type w) : Category.{max w v} (GradedObject β C) :=
  CategoryTheory.pi fun _ ↦ C

@[ext]
lemma hom_ext {β : Type*} {X Y : GradedObject β C} (f g : X ⟶ Y) (h : ∀ x, f x = g x) : f = g := by
  funext
  apply h

/-- The projection of a graded object to its `i`-th component. -/
@[simps]
def eval {β : Type w} (b : β) : GradedObject β C ⥤ C where
  obj X := X b
  map f := f b

section

variable {β : Type*} (X Y : GradedObject β C)

/-- Constructor for isomorphisms in `GradedObject` -/
@[simps]
def isoMk (e : ∀ i, X i ≅ Y i) : X ≅ Y where
  hom i := (e i).hom
  inv i := (e i).inv

variable {X Y}

-- this lemma is not an instance as it may create a loop with `isIso_apply_of_isIso`
lemma isIso_of_isIso_apply (f : X ⟶ Y) [hf : ∀ i, IsIso (f i)] :
    IsIso f := by
  change IsIso (isoMk X Y (fun i ↦ asIso (f i))).hom
  infer_instance

instance isIso_apply_of_isIso (f : X ⟶ Y) [IsIso f] (i : β) : IsIso (f i) := by
  change IsIso ((eval i).map f)
  infer_instance

end

end GradedObject

namespace Iso

variable {C D E J : Type*} [Category C] [Category D] [Category E]
  {X Y : GradedObject J C}

@[reassoc (attr := simp)]
lemma hom_inv_id_eval (e : X ≅ Y) (j : J) :
    e.hom j ≫ e.inv j = 𝟙 _ := by
  rw [← GradedObject.categoryOfGradedObjects_comp, e.hom_inv_id,
    GradedObject.categoryOfGradedObjects_id]

@[reassoc (attr := simp)]
lemma inv_hom_id_eval (e : X ≅ Y) (j : J) :
    e.inv j ≫ e.hom j = 𝟙 _ := by
  rw [← GradedObject.categoryOfGradedObjects_comp, e.inv_hom_id,
    GradedObject.categoryOfGradedObjects_id]

@[reassoc (attr := simp)]
lemma map_hom_inv_id_eval (e : X ≅ Y) (F : C ⥤ D) (j : J) :
    F.map (e.hom j) ≫ F.map (e.inv j) = 𝟙 _ := by
  rw [← F.map_comp, ← GradedObject.categoryOfGradedObjects_comp, e.hom_inv_id,
    GradedObject.categoryOfGradedObjects_id, Functor.map_id]

@[reassoc (attr := simp)]
lemma map_inv_hom_id_eval (e : X ≅ Y) (F : C ⥤ D) (j : J) :
    F.map (e.inv j) ≫ F.map (e.hom j) = 𝟙 _ := by
  rw [← F.map_comp, ← GradedObject.categoryOfGradedObjects_comp, e.inv_hom_id,
    GradedObject.categoryOfGradedObjects_id, Functor.map_id]

@[reassoc (attr := simp)]
lemma map_hom_inv_id_eval_app (e : X ≅ Y) (F : C ⥤ D ⥤ E) (j : J) (Y : D) :
    (F.map (e.hom j)).app Y ≫ (F.map (e.inv j)).app Y = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← F.map_comp, hom_inv_id_eval,
    Functor.map_id, NatTrans.id_app]

@[reassoc (attr := simp)]
lemma map_inv_hom_id_eval_app (e : X ≅ Y) (F : C ⥤ D ⥤ E) (j : J) (Y : D) :
    (F.map (e.inv j)).app Y ≫ (F.map (e.hom j)).app Y = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← F.map_comp, inv_hom_id_eval,
    Functor.map_id, NatTrans.id_app]

end Iso

namespace GradedObject

variable {C : Type u} [Category.{v} C]

section

variable (C)

/-- Pull back an `I`-graded object in `C` to a `J`-graded object along a function `J → I`. -/
abbrev comap {I J : Type*} (h : J → I) : GradedObject I C ⥤ GradedObject J C :=
  Pi.comap (fun _ ↦ C) h

@[simp]
theorem eqToHom_proj {I : Type*} {x x' : GradedObject I C} (h : x = x') (i : I) :
    (eqToHom h : x ⟶ x') i = eqToHom (funext_iff.mp h i) := by
  subst h
  rfl

/-- The natural isomorphism comparing between
pulling back along two propositionally equal functions.
-/
@[simps]
def comapEq {β γ : Type w} {f g : β → γ} (h : f = g) : comap C f ≅ comap C g where
  hom := { app := fun X b ↦ eqToHom (by dsimp; simp only [h]) }
  inv := { app := fun X b ↦ eqToHom (by dsimp; simp only [h]) }

theorem comapEq_symm {β γ : Type w} {f g : β → γ} (h : f = g) :
    comapEq C h.symm = (comapEq C h).symm := by cat_disch

theorem comapEq_trans {β γ : Type w} {f g h : β → γ} (k : f = g) (l : g = h) :
    comapEq C (k.trans l) = comapEq C k ≪≫ comapEq C l := by cat_disch

theorem eqToHom_apply {β : Type w} {X Y : β → C} (h : X = Y) (b : β) :
    (eqToHom h : X ⟶ Y) b = eqToHom (by rw [h]) := by
  subst h
  rfl

/-- The equivalence between β-graded objects and γ-graded objects,
given an equivalence between β and γ.
-/
@[simps]
def comapEquiv {β γ : Type w} (e : β ≃ γ) : GradedObject β C ≌ GradedObject γ C where
  functor := comap C (e.symm : γ → β)
  inverse := comap C (e : β → γ)
  counitIso :=
    (Pi.comapComp (fun _ ↦ C) _ _).trans (comapEq C (by ext; simp))
  unitIso :=
    (comapEq C (by ext; simp)).trans (Pi.comapComp _ _ _).symm

end

instance hasShift {β : Type*} [AddCommGroup β] (s : β) : HasShift (GradedObjectWithShift s C) ℤ :=
  hasShiftMk _ _
    { F := fun n ↦ comap C fun b : β ↦ b + n • s
      zero := comapEq C (by cat_disch) ≪≫ Pi.comapId β fun _ ↦ C
      add := fun m n ↦ comapEq C (by ext; dsimp; rw [add_comm m n, add_zsmul, add_assoc]) ≪≫
          (Pi.comapComp _ _ _).symm }

@[simp]
theorem shiftFunctor_obj_apply {β : Type*} [AddCommGroup β] (s : β) (X : β → C) (t : β) (n : ℤ) :
    (shiftFunctor (GradedObjectWithShift s C) n).obj X t = X (t + n • s) :=
  rfl

@[simp]
theorem shiftFunctor_map_apply {β : Type*} [AddCommGroup β] (s : β)
    {X Y : GradedObjectWithShift s C} (f : X ⟶ Y) (t : β) (n : ℤ) :
    (shiftFunctor (GradedObjectWithShift s C) n).map f t = f (t + n • s) :=
  rfl

instance [HasZeroMorphisms C] (β : Type w) (X Y : GradedObject β C) : Zero (X ⟶ Y) :=
  ⟨fun _ ↦ 0⟩

@[simp]
theorem zero_apply [HasZeroMorphisms C] (β : Type w) (X Y : GradedObject β C) (b : β) :
    (0 : X ⟶ Y) b = 0 :=
  rfl

instance hasZeroMorphisms [HasZeroMorphisms C] (β : Type w) :
    HasZeroMorphisms.{max w v} (GradedObject β C) where

section

open ZeroObject

instance hasZeroObject [HasZeroObject C] [HasZeroMorphisms C] (β : Type w) :
    HasZeroObject.{max w v} (GradedObject β C) := by
  refine ⟨⟨fun _ ↦ 0, fun X ↦ ⟨⟨⟨fun b ↦ 0⟩, fun f ↦ ?_⟩⟩, fun X ↦
    ⟨⟨⟨fun b ↦ 0⟩, fun f ↦ ?_⟩⟩⟩⟩ <;> cat_disch

end

end GradedObject

namespace GradedObject

-- The universes get a little hairy here, so we restrict the universe level for the grading to 0.
-- Since we're typically interested in grading by ℤ or a finite group, this should be okay.
-- If you're grading by things in higher universes, have fun!
variable (β : Type)
variable (C : Type u) [Category.{v} C]
variable [HasCoproducts.{0} C]

section

/-- The total object of a graded object is the coproduct of the graded components.
-/
noncomputable def total : GradedObject β C ⥤ C where
  obj X := ∐ fun i : β ↦ X i
  map f := Limits.Sigma.map fun i ↦ f i

end

variable [HasZeroMorphisms C]

/--
The `total` functor taking a graded object to the coproduct of its graded components is faithful.
To prove this, we need to know that the coprojections into the coproduct are monomorphisms,
which follows from the fact we have zero morphisms and decidable equality for the grading.
-/
instance : (total β C).Faithful where
  map_injective {X Y} f g w := by
    ext i
    replace w := Sigma.ι (fun i : β ↦ X i) i ≫= w
    erw [colimit.ι_map, colimit.ι_map] at w
    simp? at * says simp only [Discrete.functor_obj_eq_as, Discrete.natTrans_app] at *
    exact Mono.right_cancellation _ _ w

end GradedObject

namespace GradedObject

noncomputable section

variable (β : Type)
variable (C : Type (u + 1)) [LargeCategory C] [HasForget C] [HasCoproducts.{0} C]
  [HasZeroMorphisms C]

instance : HasForget (GradedObject β C) where forget := total β C ⋙ forget C

instance : HasForget₂ (GradedObject β C) C where forget₂ := total β C

end

end GradedObject

namespace GradedObject

variable {I J K : Type*} {C : Type*} [Category C]
  (X Y Z : GradedObject I C) (φ : X ⟶ Y) (e : X ≅ Y) (ψ : Y ⟶ Z) (p : I → J)

/-- If `X : GradedObject I C` and `p : I → J`, `X.mapObjFun p j` is the family of objects `X i`
for `i : I` such that `p i = j`. -/
abbrev mapObjFun (j : J) (i : p ⁻¹' {j}) : C := X i

variable (j : J)

/-- Given `X : GradedObject I C` and `p : I → J`, `X.HasMap p` is the condition that
for all `j : J`, the coproduct of all `X i` such `p i = j` exists. -/
abbrev HasMap : Prop := ∀ (j : J), HasCoproduct (X.mapObjFun p j)

variable {X Y} in
lemma hasMap_of_iso (e : X ≅ Y) (p : I → J) [HasMap X p] : HasMap Y p := fun j ↦ by
  have α : Discrete.functor (X.mapObjFun p j) ≅ Discrete.functor (Y.mapObjFun p j) :=
    Discrete.natIso (fun ⟨i, _⟩ ↦ (GradedObject.eval i).mapIso e)
  exact hasColimit_of_iso α.symm

section
variable [X.HasMap p] [Y.HasMap p]

/-- Given `X : GradedObject I C` and `p : I → J`, `X.mapObj p` is the graded object by `J`
which in degree `j` consists of the coproduct of the `X i` such that `p i = j`. -/
noncomputable def mapObj : GradedObject J C := fun j ↦ ∐ (X.mapObjFun p j)

/-- The canonical inclusion `X i ⟶ X.mapObj p j` when `i : I` and `j : J` are such
that `p i = j`. -/
noncomputable def ιMapObj (i : I) (j : J) (hij : p i = j) : X i ⟶ X.mapObj p j :=
  Sigma.ι (X.mapObjFun p j) ⟨i, hij⟩

/-- Given `X : GradedObject I C`, `p : I → J` and `j : J`,
`CofanMapObjFun X p j` is the type `Cofan (X.mapObjFun p j)`. The point object of
such colimits cofans are isomorphic to `X.mapObj p j`, see `CofanMapObjFun.iso`. -/
abbrev CofanMapObjFun (j : J) : Type _ := Cofan (X.mapObjFun p j)

-- in order to use the cofan API, some definitions below
-- have a `simp` attribute rather than `simps`
/-- Constructor for `CofanMapObjFun X p j`. -/
@[simp]
def CofanMapObjFun.mk (j : J) (pt : C) (ι' : ∀ (i : I) (_ : p i = j), X i ⟶ pt) :
    CofanMapObjFun X p j :=
  Cofan.mk pt (fun ⟨i, hi⟩ ↦ ι' i hi)

/-- The tautological cofan corresponding to the coproduct decomposition of `X.mapObj p j`. -/
@[simp]
noncomputable def cofanMapObj (j : J) : CofanMapObjFun X p j :=
  CofanMapObjFun.mk X p j (X.mapObj p j) (fun i hi ↦ X.ιMapObj p i j hi)

/-- Given `X : GradedObject I C`, `p : I → J` and `j : J`, `X.mapObj p j` satisfies
the universal property of the coproduct of those `X i` such that `p i = j`. -/
noncomputable def isColimitCofanMapObj (j : J) : IsColimit (X.cofanMapObj p j) :=
  colimit.isColimit _

@[ext]
lemma mapObj_ext {A : C} {j : J} (f g : X.mapObj p j ⟶ A)
    (hfg : ∀ (i : I) (hij : p i = j), X.ιMapObj p i j hij ≫ f = X.ιMapObj p i j hij ≫ g) :
    f = g :=
  Cofan.IsColimit.hom_ext (X.isColimitCofanMapObj p j) _ _ (fun ⟨i, hij⟩ ↦ hfg i hij)

/-- This is the morphism `X.mapObj p j ⟶ A` constructed from a family of
morphisms `X i ⟶ A` for all `i : I` such that `p i = j`. -/
noncomputable def descMapObj {A : C} {j : J} (φ : ∀ (i : I) (_ : p i = j), X i ⟶ A) :
    X.mapObj p j ⟶ A :=
  Cofan.IsColimit.desc (X.isColimitCofanMapObj p j) (fun ⟨i, hi⟩ ↦ φ i hi)

@[reassoc (attr := simp)]
lemma ι_descMapObj {A : C} {j : J}
    (φ : ∀ (i : I) (_ : p i = j), X i ⟶ A) (i : I) (hi : p i = j) :
    X.ιMapObj p i j hi ≫ X.descMapObj p φ = φ i hi := by
  apply Cofan.IsColimit.fac

end
namespace CofanMapObjFun

lemma hasMap (c : ∀ j, CofanMapObjFun X p j) (hc : ∀ j, IsColimit (c j)) :
    X.HasMap p := fun j ↦ ⟨_, hc j⟩

variable {j X p}
variable [X.HasMap p]
variable {c : CofanMapObjFun X p j} (hc : IsColimit c)

/-- If `c : CofanMapObjFun X p j` is a colimit cofan, this is the induced
isomorphism `c.pt ≅ X.mapObj p j`. -/
noncomputable def iso : c.pt ≅ X.mapObj p j :=
  IsColimit.coconePointUniqueUpToIso hc (X.isColimitCofanMapObj p j)

@[reassoc (attr := simp)]
lemma inj_iso_hom (i : I) (hi : p i = j) :
    c.inj ⟨i, hi⟩ ≫ (c.iso hc).hom = X.ιMapObj p i j hi := by
  apply IsColimit.comp_coconePointUniqueUpToIso_hom

@[reassoc (attr := simp)]
lemma ιMapObj_iso_inv (i : I) (hi : p i = j) :
    X.ιMapObj p i j hi ≫ (c.iso hc).inv = c.inj ⟨i, hi⟩ := by
  apply IsColimit.comp_coconePointUniqueUpToIso_inv

end CofanMapObjFun

variable {X Y}
variable [X.HasMap p] [Y.HasMap p]

/-- The canonical morphism of `J`-graded objects `X.mapObj p ⟶ Y.mapObj p` induced by
a morphism `X ⟶ Y` of `I`-graded objects and a map `p : I → J`. -/
noncomputable def mapMap : X.mapObj p ⟶ Y.mapObj p := fun j ↦
  X.descMapObj p (fun i hi ↦ φ i ≫ Y.ιMapObj p i j hi)

@[reassoc (attr := simp)]
lemma ι_mapMap (i : I) (j : J) (hij : p i = j) :
    X.ιMapObj p i j hij ≫ mapMap φ p j = φ i ≫ Y.ιMapObj p i j hij := by
  simp only [mapMap, ι_descMapObj]

lemma congr_mapMap (φ₁ φ₂ : X ⟶ Y) (h : φ₁ = φ₂) : mapMap φ₁ p = mapMap φ₂ p := by
  subst h
  rfl

variable (X)

@[simp]
lemma mapMap_id : mapMap (𝟙 X) p = 𝟙 _ := by cat_disch

variable {X Z}

@[simp, reassoc]
lemma mapMap_comp [Z.HasMap p] : mapMap (φ ≫ ψ) p = mapMap φ p ≫ mapMap ψ p := by cat_disch

/-- The isomorphism of `J`-graded objects `X.mapObj p ≅ Y.mapObj p` induced by an
isomorphism `X ≅ Y` of graded objects and a map `p : I → J`. -/
@[simps]
noncomputable def mapIso : X.mapObj p ≅ Y.mapObj p where
  hom := mapMap e.hom p
  inv := mapMap e.inv p

variable (C)

/-- Given a map `p : I → J`, this is the functor `GradedObject I C ⥤ GradedObject J C` which
sends an `I`-object `X` to the graded object `X.mapObj p` which in degree `j : J` is given
by the coproduct of those `X i` such that `p i = j`. -/
@[simps]
noncomputable def map [∀ (j : J), HasColimitsOfShape (Discrete (p ⁻¹' {j})) C] :
    GradedObject I C ⥤ GradedObject J C where
  obj X := X.mapObj p
  map φ := mapMap φ p

variable {C} (X Y)
variable (q : J → K) (r : I → K) (hpqr : ∀ i, q (p i) = r i)

section

variable (k : K) (c : ∀ (j : J), q j = k → X.CofanMapObjFun p j)
  (hc : ∀ j hj, IsColimit (c j hj))
  (c' : Cofan (fun (j : q ⁻¹' {k}) ↦ (c j.1 j.2).pt)) (hc' : IsColimit c')

/-- Given maps `p : I → J`, `q : J → K` and `r : I → K` such that `q.comp p = r`,
`X : GradedObject I C`, `k : K`, the datum of cofans `X.CofanMapObjFun p j` for all
`j : J` and of a cofan for all the points of these cofans, this is a cofan of
type `X.CofanMapObjFun r k`, which is a colimit (see `isColimitCofanMapObjComp`) if the
given cofans are. -/
@[simp]
def cofanMapObjComp : X.CofanMapObjFun r k :=
  CofanMapObjFun.mk _ _ _ c'.pt (fun i hi ↦
    (c (p i) (by rw [hpqr, hi])).inj ⟨i, rfl⟩ ≫ c'.inj (⟨p i, by
      rw [Set.mem_preimage, Set.mem_singleton_iff, hpqr, hi]⟩))

/-- Given maps `p : I → J`, `q : J → K` and `r : I → K` such that `q.comp p = r`,
`X : GradedObject I C`, `k : K`, the cofan constructed by `cofanMapObjComp` is a colimit.
In other words, if we have, for all `j : J` such that `hj : q j = k`,
a colimit cofan `c j hj` which computes the coproduct of the `X i` such that `p i = j`,
and also a colimit cofan which computes the coproduct of the points of these `c j hj`, then
the point of this latter cofan computes the coproduct of the `X i` such that `r i = k`. -/
@[simp]
def isColimitCofanMapObjComp :
    IsColimit (cofanMapObjComp X p q r hpqr k c c') :=
  mkCofanColimit _
    (fun s ↦ Cofan.IsColimit.desc hc'
      (fun ⟨j, (hj : q j = k)⟩ ↦ Cofan.IsColimit.desc (hc j hj)
        (fun ⟨i, (hi : p i = j)⟩ ↦ s.inj ⟨i, by
          simp only [Set.mem_preimage, Set.mem_singleton_iff, ← hpqr, hi, hj]⟩)))
    (fun s ⟨i, (hi : r i = k)⟩ ↦ by simp)
    (fun s m hm ↦ by
      apply Cofan.IsColimit.hom_ext hc'
      rintro ⟨j, rfl : q j = k⟩
      apply Cofan.IsColimit.hom_ext (hc j rfl)
      rintro ⟨i, rfl : p i = j⟩
      dsimp
      rw [Cofan.IsColimit.fac, Cofan.IsColimit.fac, ← hm]
      dsimp
      rw [assoc])

include hpqr in
lemma hasMap_comp [(X.mapObj p).HasMap q] : X.HasMap r :=
  fun k ↦ ⟨_, isColimitCofanMapObjComp X p q r hpqr k _
    (fun j _ ↦ X.isColimitCofanMapObj p j) _ ((X.mapObj p).isColimitCofanMapObj q k)⟩

end

variable [HasZeroMorphisms C] [DecidableEq J] (i : I) (j : J)

/-- The canonical inclusion `X i ⟶ X.mapObj p j` when `p i = j`, the zero morphism otherwise. -/
noncomputable def ιMapObjOrZero : X i ⟶ X.mapObj p j :=
  if h : p i = j
    then X.ιMapObj p i j h
    else 0

lemma ιMapObjOrZero_eq (h : p i = j) : X.ιMapObjOrZero p i j = X.ιMapObj p i j h := dif_pos h

lemma ιMapObjOrZero_eq_zero (h : p i ≠ j) : X.ιMapObjOrZero p i j = 0 := dif_neg h

variable {X Y} in
@[reassoc (attr := simp)]
lemma ιMapObjOrZero_mapMap :
    X.ιMapObjOrZero p i j ≫ mapMap φ p j = φ i ≫ Y.ιMapObjOrZero p i j := by
  by_cases h : p i = j
  · simp only [ιMapObjOrZero_eq _ _ _ _ h, ι_mapMap]
  · simp only [ιMapObjOrZero_eq_zero _ _ _ _ h, zero_comp, comp_zero]

end GradedObject

end CategoryTheory
