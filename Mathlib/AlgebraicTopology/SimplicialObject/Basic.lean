/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.Util.Superscript

/-!
# Simplicial objects in a category.

A simplicial object in a category `C` is a `C`-valued presheaf on `SimplexCategory`.
(Similarly, a cosimplicial object is a functor `SimplexCategory ⥤ C`.)

## Notation

The following notations can be enabled via `open Simplicial`.

- `X _⦋n⦌` denotes the `n`-th term of a simplicial object `X`, where `n : ℕ`.
- `X ^⦋n⦌` denotes the `n`-th term of a cosimplicial object `X`, where `n : ℕ`.

The following notations can be enabled via
`open CategoryTheory.SimplicialObject.Truncated`.

- `X _⦋m⦌ₙ` denotes the `m`-th term of an `n`-truncated simplicial object `X`.
- `X ^⦋m⦌ₙ` denotes the `m`-th term of an `n`-truncated cosimplicial object `X`.
-/

open Opposite

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor

universe v u v' u'

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- The category of simplicial objects valued in a category `C`.
This is the category of contravariant functors from `SimplexCategory` to `C`. -/
def SimplicialObject :=
  SimplexCategoryᵒᵖ ⥤ C

@[simps!]
instance : Category (SimplicialObject C) := by
  dsimp only [SimplicialObject]
  infer_instance

namespace SimplicialObject

set_option quotPrecheck false in
/-- `X _⦋n⦌` denotes the `n`th-term of the simplicial object X -/
scoped[Simplicial]
  notation3:1000 X " _⦋" n "⦌" =>
      (X : CategoryTheory.SimplicialObject _).obj (Opposite.op (SimplexCategory.mk n))

open Simplicial

instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (SimplicialObject C) := by
  dsimp [SimplicialObject]
  infer_instance

instance [HasLimits C] : HasLimits (SimplicialObject C) :=
  ⟨inferInstance⟩

instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (SimplicialObject C) := by
  dsimp [SimplicialObject]
  infer_instance

instance [HasColimits C] : HasColimits (SimplicialObject C) :=
  ⟨inferInstance⟩

variable {C}

@[ext]
lemma hom_ext {X Y : SimplicialObject C} (f g : X ⟶ Y)
    (h : ∀ (n : SimplexCategoryᵒᵖ), f.app n = g.app n) : f = g :=
  NatTrans.ext (by ext; apply h)

variable (X : SimplicialObject C)

/-- Face maps for a simplicial object. -/
def δ {n} (i : Fin (n + 2)) : X _⦋n + 1⦌ ⟶ X _⦋n⦌ :=
  X.map (SimplexCategory.δ i).op

/-- Degeneracy maps for a simplicial object. -/
def σ {n} (i : Fin (n + 1)) : X _⦋n⦌ ⟶ X _⦋n + 1⦌ :=
  X.map (SimplexCategory.σ i).op

/-- The diagonal of a simplex is the long edge of the simplex. -/
def diagonal {n : ℕ} : X _⦋n⦌ ⟶ X _⦋1⦌ := X.map ((SimplexCategory.diag n).op)

/-- Isomorphisms from identities in ℕ. -/
def eqToIso {n m : ℕ} (h : n = m) : X _⦋n⦌ ≅ X _⦋m⦌ :=
  X.mapIso (CategoryTheory.eqToIso (by congr))

@[simp]
theorem eqToIso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by
  simp [eqToIso]

/-- The generic case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ j.succ ≫ X.δ i = X.δ (Fin.castSucc i) ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ H]

@[reassoc]
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    X.δ j ≫ X.δ i =
      X.δ (Fin.castSucc i) ≫
        X.δ (j.pred fun (hj : j = 0) => by simp [hj, Fin.not_lt_zero] at H) := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ' H]
@[reassoc]
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    X.δ j.succ ≫ X.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) =
      X.δ i ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ'' H]

/-- The special case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} :
    X.δ (Fin.castSucc i) ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ_self]

@[reassoc]
theorem δ_comp_δ_self' {n} {j : Fin (n + 3)} {i : Fin (n + 2)} (H : j = Fin.castSucc i) :
    X.δ j ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  subst H
  rw [δ_comp_δ_self]

/-- The second simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    X.σ j.succ ≫ X.δ (Fin.castSucc i) = X.δ i ≫ X.σ j := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_le H]

/-- The first part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ (Fin.castSucc i) = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_self, op_id, X.map_id]

@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    X.σ i ≫ X.δ j = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_self]

/-- The second part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ i.succ = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_succ, op_id, X.map_id]

@[reassoc]
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.σ i ≫ X.δ j = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_succ]

/-- The fourth simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    X.σ (Fin.castSucc j) ≫ X.δ i.succ = X.δ i ≫ X.σ j := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt H]

@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.σ j ≫ X.δ i =
      X.δ (i.pred fun (hi : i = 0) => by simp only [Fin.not_lt_zero, hi] at H) ≫
        X.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt' H]

/-- The fifth simplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    X.σ j ≫ X.σ (Fin.castSucc i) = X.σ i ≫ X.σ j.succ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.σ_comp_σ H]

open Simplicial

@[reassoc (attr := simp)]
theorem δ_naturality {X' X : SimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 2)) :
    X.δ i ≫ f.app (op ⦋n⦌) = f.app (op ⦋n + 1⦌) ≫ X'.δ i :=
  f.naturality _

@[reassoc (attr := simp)]
theorem σ_naturality {X' X : SimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ f.app (op ⦋n + 1⦌) = f.app (op ⦋n⦌) ≫ X'.σ i :=
  f.naturality _

variable (C)

/-- Functor composition induces a functor on simplicial objects. -/
@[simps!]
def whiskering (D : Type*) [Category D] : (C ⥤ D) ⥤ SimplicialObject C ⥤ SimplicialObject D :=
  whiskeringRight _ _ _

/-- Truncated simplicial objects. -/
def Truncated (n : ℕ) :=
  (SimplexCategory.Truncated n)ᵒᵖ ⥤ C

instance {n : ℕ} : Category (Truncated C n) := by
  dsimp [Truncated]
  infer_instance

variable {C}

namespace Truncated

instance {n} {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (SimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance

instance {n} [HasLimits C] : HasLimits (SimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

instance {n} {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (SimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance

instance {n} [HasColimits C] : HasColimits (SimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

variable (C) in
/-- Functor composition induces a functor on truncated simplicial objects. -/
@[simps!]
def whiskering {n} (D : Type*) [Category D] : (C ⥤ D) ⥤ Truncated C n ⥤ Truncated D n :=
  whiskeringRight _ _ _

open Mathlib.Tactic (subscriptTerm) in
/-- For `X : Truncated C n` and `m ≤ n`, `X _⦋m⦌ₙ` is the `m`-th term of X. The
proof `p : m ≤ n` can also be provided using the syntax `X _⦋m, p⦌ₙ`. -/
scoped syntax:max (name := mkNotation)
  term " _⦋" term ("," term)? "⦌" noWs subscriptTerm : term

open scoped SimplexCategory.Truncated in
scoped macro_rules
  | `($X:term _⦋$m:term⦌$n:subscript) =>
    `(($X : CategoryTheory.SimplicialObject.Truncated _ $n).obj
      (Opposite.op ⟨SimplexCategory.mk $m, by first | get_elem_tactic |
      fail "Failed to prove truncation property. Try writing `X _⦋m, by ...⦌ₙ`."⟩))
  | `($X:term _⦋$m:term, $p:term⦌$n:subscript) =>
    `(($X : CategoryTheory.SimplicialObject.Truncated _ $n).obj
      (Opposite.op ⟨SimplexCategory.mk $m, $p⟩))

variable (C) in
/-- Further truncation of truncated simplicial objects. -/
@[simps!]
def trunc (n m : ℕ) (h : m ≤ n := by omega) : Truncated C n ⥤ Truncated C m :=
  (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.incl m n).op

end Truncated

section Truncation

/-- The truncation functor from simplicial objects to truncated simplicial objects. -/
def truncation (n : ℕ) : SimplicialObject C ⥤ SimplicialObject.Truncated C n :=
  (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.inclusion n).op

/-- For all `m ≤ n`, `truncation m` factors through `Truncated n`. -/
def truncationCompTrunc {n m : ℕ} (h : m ≤ n) :
    truncation n ⋙ Truncated.trunc C n m ≅ truncation m :=
  Iso.refl _

end Truncation


noncomputable section

/-- The n-skeleton as a functor `SimplicialObject.Truncated C n ⥤ SimplicialObject C`. -/
protected abbrev Truncated.sk (n : ℕ) [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasLeftKanExtension F] :
    SimplicialObject.Truncated C n ⥤ SimplicialObject C :=
  lan (SimplexCategory.Truncated.inclusion n).op

/-- The n-coskeleton as a functor `SimplicialObject.Truncated C n ⥤ SimplicialObject C`. -/
protected abbrev Truncated.cosk (n : ℕ) [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    SimplicialObject.Truncated C n ⥤ SimplicialObject C :=
  ran (SimplexCategory.Truncated.inclusion n).op

/-- The n-skeleton as an endofunctor on `SimplicialObject C`. -/
abbrev sk (n : ℕ) [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasLeftKanExtension F] :
    SimplicialObject C ⥤ SimplicialObject C := truncation n ⋙ Truncated.sk n

/-- The n-coskeleton as an endofunctor on `SimplicialObject C`. -/
abbrev cosk (n : ℕ) [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    SimplicialObject C ⥤ SimplicialObject C := truncation n ⋙ Truncated.cosk n

end

section adjunctions
/- When the left and right Kan extensions exist, `Truncated.sk n` and `Truncated.cosk n`
respectively define left and right adjoints to `truncation n`. -/


variable (n : ℕ)
variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]
variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasLeftKanExtension F]

/-- The adjunction between the n-skeleton and n-truncation. -/
noncomputable def skAdj : Truncated.sk (C := C) n ⊣ truncation n :=
  lanAdjunction _ _

/-- The adjunction between n-truncation and the n-coskeleton. -/
noncomputable def coskAdj : truncation (C := C) n ⊣ Truncated.cosk n :=
  ranAdjunction _ _

instance : ((sk n).obj X).IsLeftKanExtension ((skAdj n).unit.app _) := by
  dsimp [sk, skAdj]
  rw [lanAdjunction_unit]
  infer_instance

instance : ((cosk n).obj X).IsRightKanExtension ((coskAdj n).counit.app _) := by
  dsimp [cosk, coskAdj]
  rw [ranAdjunction_counit]
  infer_instance

namespace Truncated
/- When the left and right Kan extensions exist and are pointwise Kan extensions,
`skAdj n` and `coskAdj n` are respectively coreflective and reflective. -/

variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseLeftKanExtension F]

instance cosk_reflective : IsIso (coskAdj (C := C) n).counit :=
  reflective' (SimplexCategory.Truncated.inclusion n).op

instance sk_coreflective : IsIso (skAdj (C := C) n).unit :=
  coreflective' (SimplexCategory.Truncated.inclusion n).op

/-- Since `Truncated.inclusion` is fully faithful, so is right Kan extension along it. -/
noncomputable def cosk.fullyFaithful :
    (Truncated.cosk (C := C) n).FullyFaithful := by
  apply Adjunction.fullyFaithfulROfIsIsoCounit (coskAdj n)

instance cosk.full : (Truncated.cosk (C := C) n).Full := FullyFaithful.full (cosk.fullyFaithful _)

instance cosk.faithful : (Truncated.cosk (C := C) n).Faithful :=
  FullyFaithful.faithful (cosk.fullyFaithful _)

noncomputable instance coskAdj.reflective : Reflective (Truncated.cosk (C := C) n) :=
  Reflective.mk (truncation _) (coskAdj _)

/-- Since `Truncated.inclusion` is fully faithful, so is left Kan extension along it. -/
noncomputable def sk.fullyFaithful : (Truncated.sk (C := C) n).FullyFaithful :=
  Adjunction.fullyFaithfulLOfIsIsoUnit (skAdj n)

instance sk.full : (Truncated.sk (C := C) n).Full := FullyFaithful.full (sk.fullyFaithful _)

instance sk.faithful : (Truncated.sk (C := C) n).Faithful :=
  FullyFaithful.faithful (sk.fullyFaithful _)

noncomputable instance skAdj.coreflective : Coreflective (Truncated.sk (C := C) n) :=
  Coreflective.mk (truncation _) (skAdj _)

end Truncated

end adjunctions

variable (C)

/-- The constant simplicial object is the constant functor. -/
abbrev const : C ⥤ SimplicialObject C :=
  CategoryTheory.Functor.const _

/-- The category of augmented simplicial objects, defined as a comma category. -/
def Augmented :=
  Comma (𝟭 (SimplicialObject C)) (const C)

@[simps!]
instance : Category (Augmented C) := by
  dsimp only [Augmented]
  infer_instance

variable {C}

namespace Augmented

@[ext]
lemma hom_ext {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) :
    f = g :=
  Comma.hom_ext _ _ h₁ h₂

/-- Drop the augmentation. -/
@[simps!]
def drop : Augmented C ⥤ SimplicialObject C :=
  Comma.fst _ _

/-- The point of the augmentation. -/
@[simps!]
def point : Augmented C ⥤ C :=
  Comma.snd _ _

/-- The functor from augmented objects to arrows. -/
@[simps]
def toArrow : Augmented C ⥤ Arrow C where
  obj X :=
    { left := drop.obj X _⦋0⦌
      right := point.obj X
      hom := X.hom.app _ }
  map η :=
    { left := (drop.map η).app _
      right := point.map η
      w := by
        dsimp
        rw [← NatTrans.comp_app]
        erw [η.w]
        rfl }

/-- The compatibility of a morphism with the augmentation, on 0-simplices -/
@[reassoc]
theorem w₀ {X Y : Augmented C} (f : X ⟶ Y) :
    (Augmented.drop.map f).app (op ⦋0⦌) ≫ Y.hom.app (op ⦋0⦌) =
      X.hom.app (op ⦋0⦌) ≫ Augmented.point.map f := by
  convert congr_app f.w (op ⦋0⦌)

variable (C)

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simp]
def whiskeringObj (D : Type*) [Category D] (F : C ⥤ D) : Augmented C ⥤ Augmented D where
  obj X :=
    { left := ((whiskering _ _).obj F).obj (drop.obj X)
      right := F.obj (point.obj X)
      hom := whiskerRight X.hom F ≫ (Functor.constComp _ _ _).hom }
  map η :=
    { left := whiskerRight η.left _
      right := F.map η.right
      w := by
        ext
        dsimp [whiskerRight]
        simp only [Category.comp_id, ← F.map_comp, ← NatTrans.comp_app]
        erw [η.w]
        rfl }

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simps]
def whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augmented D where
  obj := whiskeringObj _ _
  map η :=
    { app := fun A =>
        { left := whiskerLeft _ η
          right := η.app _
          w := by
            ext n
            dsimp
            rw [Category.comp_id, Category.comp_id, η.naturality] } }
  map_comp := fun _ _ => by ext <;> rfl

variable {C}

/-- The constant augmented simplicial object functor. -/
@[simps]
def const : C ⥤ Augmented C where
  obj X :=
    { left := (SimplicialObject.const C).obj X
      right := X
      hom := 𝟙 _ }
  map f :=
    { left := (SimplicialObject.const C).map f
      right := f }

end Augmented

/-- Augment a simplicial object with an object. -/
@[simps]
def augment (X : SimplicialObject C) (X₀ : C) (f : X _⦋0⦌ ⟶ X₀)
    (w : ∀ (i : SimplexCategory) (g₁ g₂ : ⦋0⦌ ⟶ i),
      X.map g₁.op ≫ f = X.map g₂.op ≫ f) :
    SimplicialObject.Augmented C where
  left := X
  right := X₀
  hom :=
    { app := fun _ => X.map (SimplexCategory.const _ _ 0).op ≫ f
      naturality := by
        intro i j g
        dsimp
        rw [← g.op_unop]
        simpa only [← X.map_comp, ← Category.assoc, Category.comp_id, ← op_comp] using w _ _ _ }

-- Not `@[simp]` since `simp` can prove this.
theorem augment_hom_zero (X : SimplicialObject C) (X₀ : C) (f : X _⦋0⦌ ⟶ X₀) (w) :
    (X.augment X₀ f w).hom.app (op ⦋0⦌) = f := by simp

end SimplicialObject

/-- Cosimplicial objects. -/
def CosimplicialObject :=
  SimplexCategory ⥤ C

namespace CosimplicialObject

@[simps!]
instance : Category (CosimplicialObject C) := by
  dsimp only [CosimplicialObject]
  infer_instance

/-- `X ^⦋n⦌` denotes the `n`th-term of the cosimplicial object X -/
scoped[Simplicial]
  notation3:1000 X " ^⦋" n "⦌" =>
    (X : CategoryTheory.CosimplicialObject _).obj (SimplexCategory.mk n)

instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CosimplicialObject C) := by
  dsimp [CosimplicialObject]
  infer_instance

instance [HasLimits C] : HasLimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CosimplicialObject C) := by
  dsimp [CosimplicialObject]
  infer_instance

instance [HasColimits C] : HasColimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

variable {C}

@[ext]
lemma hom_ext {X Y : CosimplicialObject C} (f g : X ⟶ Y)
    (h : ∀ (n : SimplexCategory), f.app n = g.app n) : f = g :=
  NatTrans.ext (by ext; apply h)

variable (X : CosimplicialObject C)

open Simplicial

/-- Coface maps for a cosimplicial object. -/
def δ {n} (i : Fin (n + 2)) : X ^⦋n⦌ ⟶ X ^⦋n + 1⦌ :=
  X.map (SimplexCategory.δ i)

/-- Codegeneracy maps for a cosimplicial object. -/
def σ {n} (i : Fin (n + 1)) : X ^⦋n + 1⦌ ⟶ X ^⦋n⦌ :=
  X.map (SimplexCategory.σ i)

/-- Isomorphisms from identities in ℕ. -/
def eqToIso {n m : ℕ} (h : n = m) : X ^⦋n⦌ ≅ X ^⦋m⦌ :=
  X.mapIso (CategoryTheory.eqToIso (by rw [h]))

@[simp]
theorem eqToIso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by
  simp [eqToIso]

/-- The generic case of the first cosimplicial identity -/
@[reassoc]
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ i ≫ X.δ j.succ = X.δ j ≫ X.δ (Fin.castSucc i) := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ H]

@[reassoc]
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    X.δ i ≫ X.δ j =
      X.δ (j.pred fun (hj : j = 0) => by simp only [hj, Fin.not_lt_zero] at H) ≫
        X.δ (Fin.castSucc i) := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ' H]

@[reassoc]
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    X.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ X.δ j.succ =
      X.δ j ≫ X.δ i := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ'' H]

/-- The special case of the first cosimplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} :
    X.δ i ≫ X.δ (Fin.castSucc i) = X.δ i ≫ X.δ i.succ := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ_self]

@[reassoc]
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i) :
    X.δ i ≫ X.δ j = X.δ i ≫ X.δ i.succ := by
  subst H
  rw [δ_comp_δ_self]

/-- The second cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    X.δ (Fin.castSucc i) ≫ X.σ j.succ = X.σ j ≫ X.δ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_le H]

/-- The first part of the third cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.δ (Fin.castSucc i) ≫ X.σ i = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_self, X.map_id]

@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    X.δ j ≫ X.σ i = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_self]

/-- The second part of the third cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.δ i.succ ≫ X.σ i = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_succ, X.map_id]

@[reassoc]
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.δ j ≫ X.σ i = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_succ]

/-- The fourth cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    X.δ i.succ ≫ X.σ (Fin.castSucc j) = X.σ j ≫ X.δ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt H]

@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.δ i ≫ X.σ j =
      X.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) ≫
        X.δ (i.pred <|
          fun (hi : i = 0) => by simp only [Fin.not_lt_zero, hi] at H) := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt' H]

/-- The fifth cosimplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    X.σ (Fin.castSucc i) ≫ X.σ j = X.σ j.succ ≫ X.σ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.σ_comp_σ H]

@[reassoc (attr := simp)]
theorem δ_naturality {X' X : CosimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 2)) :
    X.δ i ≫ f.app ⦋n + 1⦌ = f.app ⦋n⦌ ≫ X'.δ i :=
  f.naturality _

@[reassoc (attr := simp)]
theorem σ_naturality {X' X : CosimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ f.app ⦋n⦌ = f.app ⦋n + 1⦌ ≫ X'.σ i :=
  f.naturality _

variable (C)

/-- Functor composition induces a functor on cosimplicial objects. -/
@[simps!]
def whiskering (D : Type*) [Category D] : (C ⥤ D) ⥤ CosimplicialObject C ⥤ CosimplicialObject D :=
  whiskeringRight _ _ _

/-- Truncated cosimplicial objects. -/
def Truncated (n : ℕ) :=
  SimplexCategory.Truncated n ⥤ C

instance {n : ℕ} : Category (Truncated C n) := by
  dsimp [Truncated]
  infer_instance

variable {C}

namespace Truncated

instance {n} {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CosimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance

instance {n} [HasLimits C] : HasLimits (CosimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

instance {n} {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CosimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance

instance {n} [HasColimits C] : HasColimits (CosimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

variable (C) in
/-- Functor composition induces a functor on truncated cosimplicial objects. -/
@[simps!]
def whiskering {n} (D : Type*) [Category D] : (C ⥤ D) ⥤ Truncated C n ⥤ Truncated D n :=
  whiskeringRight _ _ _

open Mathlib.Tactic (subscriptTerm) in
/-- For `X : Truncated C n` and `m ≤ n`, `X ^⦋m⦌ₙ` is the `m`-th term of X. The
proof `p : m ≤ n` can also be provided using the syntax `X ^⦋m, p⦌ₙ`. -/
scoped syntax:max (name := mkNotation)
  term " ^⦋" term ("," term)? "⦌" noWs subscriptTerm : term

open scoped SimplexCategory.Truncated in
scoped macro_rules
  | `($X:term ^⦋$m:term⦌$n:subscript) =>
    `(($X : CategoryTheory.CosimplicialObject.Truncated _ $n).obj
      ⟨SimplexCategory.mk $m, by first | get_elem_tactic |
      fail "Failed to prove truncation property. Try writing `X ^⦋m, by ...⦌ₙ`."⟩)
  | `($X:term ^⦋$m:term, $p:term⦌$n:subscript) =>
    `(($X : CategoryTheory.CosimplicialObject.Truncated _ $n).obj
      ⟨SimplexCategory.mk $m, $p⟩)

variable (C) in
/-- Further truncation of truncated cosimplicial objects. -/
def trunc (n m : ℕ) (h : m ≤ n := by omega) : Truncated C n ⥤ Truncated C m :=
  (whiskeringLeft _ _ _).obj <| SimplexCategory.Truncated.incl m n

end Truncated

section Truncation

/-- The truncation functor from cosimplicial objects to truncated cosimplicial objects. -/
def truncation (n : ℕ) : CosimplicialObject C ⥤ CosimplicialObject.Truncated C n :=
  (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.inclusion n)

/-- For all `m ≤ n`, `truncation m` factors through `Truncated n`. -/
def truncationCompTrunc {n m : ℕ} (h : m ≤ n) :
    truncation n ⋙ Truncated.trunc C n m ≅ truncation m :=
  Iso.refl _

end Truncation

variable (C)

/-- The constant cosimplicial object. -/
abbrev const : C ⥤ CosimplicialObject C :=
  CategoryTheory.Functor.const _

/-- Augmented cosimplicial objects. -/
def Augmented :=
  Comma (const C) (𝟭 (CosimplicialObject C))

@[simps!]
instance : Category (Augmented C) := by
  dsimp only [Augmented]
  infer_instance

variable {C}

namespace Augmented

@[ext]
lemma hom_ext {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) :
    f = g :=
  Comma.hom_ext _ _ h₁ h₂

/-- Drop the augmentation. -/
@[simps!]
def drop : Augmented C ⥤ CosimplicialObject C :=
  Comma.snd _ _

/-- The point of the augmentation. -/
@[simps!]
def point : Augmented C ⥤ C :=
  Comma.fst _ _

/-- The functor from augmented objects to arrows. -/
@[simps!]
def toArrow : Augmented C ⥤ Arrow C where
  obj X :=
    { left := point.obj X
      right := (drop.obj X) ^⦋0⦌
      hom := X.hom.app _ }
  map η :=
    { left := point.map η
      right := (drop.map η).app _
      w := by
        dsimp
        rw [← NatTrans.comp_app]
        erw [← η.w]
        rfl }

variable (C)

/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simp]
def whiskeringObj (D : Type*) [Category D] (F : C ⥤ D) : Augmented C ⥤ Augmented D where
  obj X :=
    { left := F.obj (point.obj X)
      right := ((whiskering _ _).obj F).obj (drop.obj X)
      hom := (Functor.constComp _ _ _).inv ≫ whiskerRight X.hom F }
  map η :=
    { left := F.map η.left
      right := whiskerRight η.right _
      w := by
        ext
        dsimp
        rw [Category.id_comp, Category.id_comp, ← F.map_comp, ← F.map_comp, ← NatTrans.comp_app]
        erw [← η.w]
        rfl }

/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simps]
def whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augmented D where
  obj := whiskeringObj _ _
  map η :=
    { app := fun A =>
        { left := η.app _
          right := whiskerLeft _ η
          w := by
            ext n
            dsimp
            rw [Category.id_comp, Category.id_comp, η.naturality] }
      naturality := fun _ _ f => by ext <;> simp }

variable {C}

/-- The constant augmented cosimplicial object functor. -/
@[simps]
def const : C ⥤ Augmented C where
  obj X :=
    { left := X
      right := (CosimplicialObject.const C).obj X
      hom := 𝟙 _ }
  map f :=
    { left := f
      right := (CosimplicialObject.const C).map f }

end Augmented

open Simplicial

/-- Augment a cosimplicial object with an object. -/
@[simps]
def augment (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj ⦋0⦌)
    (w : ∀ (i : SimplexCategory) (g₁ g₂ : ⦋0⦌ ⟶ i),
      f ≫ X.map g₁ = f ≫ X.map g₂) : CosimplicialObject.Augmented C where
  left := X₀
  right := X
  hom :=
    { app := fun _ => f ≫ X.map (SimplexCategory.const _ _ 0)
      naturality := by
        intro i j g
        dsimp
        rw [Category.id_comp, Category.assoc, ← X.map_comp, w] }

-- Not `@[simp]` since `simp` can prove this.
theorem augment_hom_zero (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj ⦋0⦌) (w) :
    (X.augment X₀ f w).hom.app ⦋0⦌ = f := by simp

end CosimplicialObject

/-- The anti-equivalence between simplicial objects and cosimplicial objects. -/
@[simps!]
def simplicialCosimplicialEquiv : (SimplicialObject C)ᵒᵖ ≌ CosimplicialObject Cᵒᵖ :=
  Functor.leftOpRightOpEquiv _ _

/-- The anti-equivalence between cosimplicial objects and simplicial objects. -/
@[simps!]
def cosimplicialSimplicialEquiv : (CosimplicialObject C)ᵒᵖ ≌ SimplicialObject Cᵒᵖ :=
  Functor.opUnopEquiv _ _

variable {C}

/-- Construct an augmented cosimplicial object in the opposite
category from an augmented simplicial object. -/
@[simps!]
def SimplicialObject.Augmented.rightOp (X : SimplicialObject.Augmented C) :
    CosimplicialObject.Augmented Cᵒᵖ where
  left := Opposite.op X.right
  right := X.left.rightOp
  hom := NatTrans.rightOp X.hom

/-- Construct an augmented simplicial object from an augmented cosimplicial
object in the opposite category. -/
@[simps!]
def CosimplicialObject.Augmented.leftOp (X : CosimplicialObject.Augmented Cᵒᵖ) :
    SimplicialObject.Augmented C where
  left := X.right.leftOp
  right := X.left.unop
  hom := NatTrans.leftOp X.hom

/-- Converting an augmented simplicial object to an augmented cosimplicial
object and back is isomorphic to the given object. -/
@[simps!]
def SimplicialObject.Augmented.rightOpLeftOpIso (X : SimplicialObject.Augmented C) :
    X.rightOp.leftOp ≅ X :=
  Comma.isoMk X.left.rightOpLeftOpIso (CategoryTheory.eqToIso <| by simp)

/-- Converting an augmented cosimplicial object to an augmented simplicial
object and back is isomorphic to the given object. -/
@[simps!]
def CosimplicialObject.Augmented.leftOpRightOpIso (X : CosimplicialObject.Augmented Cᵒᵖ) :
    X.leftOp.rightOp ≅ X :=
  Comma.isoMk (CategoryTheory.eqToIso <| by simp) X.right.leftOpRightOpIso

variable (C)

/-- A functorial version of `SimplicialObject.Augmented.rightOp`. -/
@[simps]
def simplicialToCosimplicialAugmented :
    (SimplicialObject.Augmented C)ᵒᵖ ⥤ CosimplicialObject.Augmented Cᵒᵖ where
  obj X := X.unop.rightOp
  map f :=
    { left := f.unop.right.op
      right := NatTrans.rightOp f.unop.left
      w := by
        ext x
        dsimp
        simp_rw [← op_comp]
        congr 1
        exact (congr_app f.unop.w (op x)).symm }

/-- A functorial version of `Cosimplicial_object.Augmented.leftOp`. -/
@[simps]
def cosimplicialToSimplicialAugmented :
    CosimplicialObject.Augmented Cᵒᵖ ⥤ (SimplicialObject.Augmented C)ᵒᵖ where
  obj X := Opposite.op X.leftOp
  map f :=
    Quiver.Hom.op <|
      { left := NatTrans.leftOp f.right
        right := f.left.unop
        w := by
          ext x
          dsimp
          simp_rw [← unop_comp]
          congr 1
          exact (congr_app f.w (unop x)).symm }

/-- The contravariant categorical equivalence between augmented simplicial
objects and augmented cosimplicial objects in the opposite category. -/
@[simps! functor inverse]
def simplicialCosimplicialAugmentedEquiv :
    (SimplicialObject.Augmented C)ᵒᵖ ≌ CosimplicialObject.Augmented Cᵒᵖ where
  functor := simplicialToCosimplicialAugmented _
  inverse := cosimplicialToSimplicialAugmented _
  unitIso := NatIso.ofComponents (fun X => X.unop.rightOpLeftOpIso.op) fun f => by
      dsimp
      rw [← f.op_unop]
      simp_rw [← op_comp]
      congr 1
      cat_disch
  counitIso := NatIso.ofComponents fun X => X.leftOpRightOpIso

end CategoryTheory
