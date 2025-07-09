/-
Copyright (c) 2025 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Whiskering

/-!
# Inserting associators and unitors


## TODO

- Inserting isomorphisms (not just morphisms). To obtain "simplified" expressions, we need to
  collect simp lemmas for isomorphisms (e.g., pentagon identities in terms of `Iso` terms).

-/

open Lean Meta Elab Qq

namespace Mathlib.Tactic

namespace Associators

open CategoryTheory

structure CategoryExpr where
  /-- The category type. -/
  type : Expr
  /-- The category structure. -/
  inst : Expr
  objLevel : Level
  morLevel : Level
  deriving Inhabited

/-- The domain of a morphism. -/
def srcExpr (η : Expr) : MetaM CategoryExpr := do
  let η ← whnfR (← inferType η)
  match η.getAppFn with
  | .const ``CategoryTheory.Functor [v₁, _, u₁, _] => do
    match η.getAppFnArgs with
    | (``CategoryTheory.Functor, #[C, inst, _, _]) =>
      return ⟨C, inst, u₁, v₁⟩
    | _ => throwError m!"{η} is not a functor type"
  | _ => throwError m!"{η} is not a functor type"

/-- The codomain of a morphism. -/
def tgtExpr (η : Expr) : MetaM CategoryExpr := do
  let η ← whnfR (← inferType η)
  match η.getAppFn with
  | .const ``CategoryTheory.Functor [_, v₂, _, u₂] => do
    match η.getAppFnArgs with
    | (``CategoryTheory.Functor, #[_, _, D, inst]) =>
      return ⟨D, inst, u₂, v₂⟩
    | _ => throwError m!"{η} is not a functor type"
  | _ => throwError m!"{η} is not a functor type"

def isComp? (f : Expr) : MetaM (Option (Expr × Expr)) := do
  match (← whnfR f).getAppFnArgs with
  | (``Functor.comp, #[_, _, _, _, _, _, f, g]) => return some (f, g)
  | _ => return none

def whiskerLeft? (fg fh : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  match (← isComp? fg, ← isComp? fh) with
  | (some (f, g), some (f', h)) =>
    match ← withReducible <| isDefEq f f' with
    | true => return some (f, g, h)
    | false => return none
  | _ => return none

def whiskerRight? (fh gh : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  match (← isComp? fh, ← isComp? gh) with
  | (some (f, h), some (g, h')) =>
    match ← withReducible <| isDefEq h h' with
    | true => return some (f, g, h)
    | false => return none
  | _ => return none

def refl? (f g : Expr) : MetaM (Option Expr) := do
  match ← withReducible <| isDefEq f g with
  | true => return some f
  | false => return none

def postCompTgt? (f fg : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← isComp? fg with
  | some (f', g) =>
    match ← withReducible <| isDefEq f f' with
    | true => return (f, g)
    | _ => return none
  | none => return none

def postCompSrc? (fg g : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← isComp? fg with
  | some (f, g') =>
    match ← withReducible <| isDefEq g g' with
    | true => return (f, g)
    | false => return none
  | none => return none

def leftUnitor? (id_f g : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← isComp? id_f with
  | some (_id, f) =>
    let _A ← srcExpr f
    have u₁ := _A.objLevel
    have v₁ := _A.morLevel
    have A : Q(Type u₁) := _A.type
    have _instA : Q(Category.{v₁} $A) := _A.inst
    match ← withReducible <| isDefEq _id q(𝟭 $A) with
    | true => return some (f, g)
    | false => return none
  | none => return none

def leftUnitorInv? (f id_g : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← isComp? id_g with
  | some (_id, g) =>
    let _A ← srcExpr g
    have u₁ := _A.objLevel
    have v₁ := _A.morLevel
    have A : Q(Type u₁) := _A.type
    have _instA : Q(Category.{v₁} $A) := _A.inst
    match ← withReducible <| isDefEq _id q(𝟭 $A) with
    | true => return some (f, g)
    | false => return none
  | none => return none

def rightUnitor? (f_id g : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← isComp? f_id with
  | some (f, _id) =>
    let _B ← tgtExpr f
    have u₁ := _B.objLevel
    have v₁ := _B.morLevel
    have B : Q(Type u₁) := _B.type
    have _instB : Q(Category.{v₁} $B) := _B.inst
    match ← withReducible <| isDefEq _id q(𝟭 $B) with
    | true => return some (f, g)
    | false => return none
  | none => return none

def rightUnitorInv? (f g_id : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← isComp? g_id with
  | some (g, _id) =>
    let _B ← tgtExpr g
    have u₁ := _B.objLevel
    have v₁ := _B.morLevel
    have B : Q(Type u₁) := _B.type
    have _instB : Q(Category.{v₁} $B) := _B.inst
    match ← withReducible <| isDefEq _id q(𝟭 $B) with
    | true => return some (f, g)
    | false => return none
  | none => return none

def assoc? (fgh i : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  match ← isComp? fgh with
  | some (fg, h) =>
    match ← isComp? fg with
    | some (f, g) => return some (f, g, h, i)
    | none => return none
  | none => return none

def assocInv? (i fgh : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  match ← isComp? fgh with
  | some (fg, h) =>
    match ← isComp? fg with
    | some (f, g) => return some (f, g, h, i)
    | none => return none
  | none => return none

partial def associators (f g : Expr) : MetaM Expr := do
  withIncRecDepth do
    match ← refl? f g with
    | some f => do
      let _A ← srcExpr f
      let _B ← tgtExpr f
      let u₁ := _A.objLevel
      let v₁ := _A.morLevel
      let u₂ := _B.objLevel
      let v₂ := _B.morLevel
      have A : Q(Type u₁) := _A.type
      have B : Q(Type u₂) := _B.type
      have _instA : Q(Category.{v₁} $A) := _A.inst
      have _instB : Q(Category.{v₂} $B) := _B.inst
      have f : Q($A ⥤ $B) := f
      return q(Iso.refl $f)
    | _ => do
    match ← leftUnitor? f g with
    | some (f, g) => do
      let _A ← srcExpr f
      let _B ← tgtExpr f
      have u₁ := _A.objLevel
      have v₁ := _A.morLevel
      have u₂ := _B.objLevel
      have v₂ := _B.morLevel
      have A : Q(Type u₁) := _A.type
      have B : Q(Type u₂) := _B.type
      have _instA : Q(Category.{v₁} $A) := _A.inst
      have _instB : Q(Category.{v₂} $B) := _B.inst
      have f : Q($A ⥤ $B) := f
      have g : Q($A ⥤ $B) := g
      let assoc ← associators f g
      have assoc : Q($f ≅ $g) := assoc
      return q(Functor.leftUnitor $f ≪≫ $assoc)
    | _ => do
    match ← leftUnitorInv? f g with
    | some (f, g) => do
      let _A ← srcExpr f
      let _B ← tgtExpr f
      have u₁ := _A.objLevel
      have v₁ := _A.morLevel
      have u₂ := _B.objLevel
      have v₂ := _B.morLevel
      have A : Q(Type u₁) := _A.type
      have B : Q(Type u₂) := _B.type
      have _instA : Q(Category.{v₁} $A) := _A.inst
      have _instB : Q(Category.{v₂} $B) := _B.inst
      have f : Q($A ⥤ $B) := f
      have g : Q($A ⥤ $B) := g
      let assoc ← associators f g
      have assoc : Q($f ≅ $g) := assoc
      return q($assoc ≪≫ (Functor.leftUnitor $g).symm)
    | _ => do
    match ← rightUnitor? f g with
    | some (f, g) => do
      let _A ← srcExpr f
      let _B ← tgtExpr f
      have u₁ := _A.objLevel
      have v₁ := _A.morLevel
      have u₂ := _B.objLevel
      have v₂ := _B.morLevel
      have A : Q(Type u₁) := _A.type
      have B : Q(Type u₂) := _B.type
      have _instA : Q(Category.{v₁} $A) := _A.inst
      have _instB : Q(Category.{v₂} $B) := _B.inst
      have f : Q($A ⥤ $B) := f
      have g : Q($A ⥤ $B) := g
      let assoc ← associators f g
      have assoc : Q($f ≅ $g) := assoc
      return q(Functor.rightUnitor $f ≪≫ $assoc)
    | _ => do
    match ← rightUnitorInv? f g with
    | some (f, g) => do
      let _A ← srcExpr f
      let _B ← tgtExpr f
      have u₁ := _A.objLevel
      have v₁ := _A.morLevel
      have u₂ := _B.objLevel
      have v₂ := _B.morLevel
      have A : Q(Type u₁) := _A.type
      have B : Q(Type u₂) := _B.type
      have _instA : Q(Category.{v₁} $A) := _A.inst
      have _instB : Q(Category.{v₂} $B) := _B.inst
      have f : Q($A ⥤ $B) := f
      have g : Q($A ⥤ $B) := g
      let assoc ← associators f g
      have assoc : Q($f ≅ $g) := assoc
      return q($assoc ≪≫ (Functor.rightUnitor $g).symm)

    | _ => do
    match ← whiskerLeft? f g with
    | some (f, g, h) => do
      let _A ← srcExpr f
      let _B ← tgtExpr f
      let _C ← tgtExpr g
      let u₁ := _A.objLevel
      let v₁ := _A.morLevel
      let u₂ := _B.objLevel
      let v₂ := _B.morLevel
      let u₃ := _C.objLevel
      let v₃ := _C.morLevel
      have A : Q(Type u₁) := _A.type
      have B : Q(Type u₂) := _B.type
      have C : Q(Type u₃) := _C.type
      have _instA : Q(Category.{v₁} $A) := _A.inst
      have _instB : Q(Category.{v₂} $B) := _B.inst
      have _instC : Q(Category.{v₃} $C) := _C.inst
      have f : Q($A ⥤ $B) := f
      have g : Q($B ⥤ $C) := g
      have h : Q($B ⥤ $C) := h
      let assoc ← associators g h
      have assoc : Q($g ≅ $h) := assoc
      return q(Functor.isoWhiskerLeft $f $assoc)
    | _ => do
    match ← whiskerRight? f g with
    | some (f, g, h) => do
      let _A ← srcExpr f
      let _B ← tgtExpr f
      let _C ← tgtExpr h
      let u₁ := _A.objLevel
      let v₁ := _A.morLevel
      let u₂ := _B.objLevel
      let v₂ := _B.morLevel
      let u₃ := _C.objLevel
      let v₃ := _C.morLevel
      have A : Q(Type u₁) := _A.type
      have B : Q(Type u₂) := _B.type
      have C : Q(Type u₃) := _C.type
      have _instA : Q(Category.{v₁} $A) := _A.inst
      have _instB : Q(Category.{v₂} $B) := _B.inst
      have _instC : Q(Category.{v₃} $C) := _C.inst
      have f : Q($A ⥤ $B) := f
      have g : Q($A ⥤ $B) := g
      have h : Q($B ⥤ $C) := h
      let assoc ← associators f g
      have assoc : Q($f ≅ $g) := assoc
      return q(Functor.isoWhiskerRight $assoc $h)
    | _ => do
    match ← postCompTgt? f g with
    | some (f, g) => do
      let _A ← srcExpr f
      let _B ← tgtExpr f
      let u₁ := _A.objLevel
      let v₁ := _A.morLevel
      let u₂ := _B.objLevel
      let v₂ := _B.morLevel
      have A : Q(Type u₁) := _A.type
      have B : Q(Type u₂) := _B.type
      have _instA : Q(Category.{v₁} $A) := _A.inst
      have _instB : Q(Category.{v₂} $B) := _B.inst
      have f : Q($A ⥤ $B) := f
      have g : Q($B ⥤ $B) := g
      let assoc ← associators q(𝟭 $B) g
      have assoc : Q(𝟭 $B ≅ $g) := assoc
      return q((Functor.rightUnitor $f).symm ≪≫ (Functor.isoWhiskerLeft $f $assoc))
    | _ => do
    match ← postCompSrc? f g with
    | some (f, g) => do
      let _A ← srcExpr f
      let _B ← tgtExpr f
      let u₁ := _A.objLevel
      let v₁ := _A.morLevel
      let u₂ := _B.objLevel
      let v₂ := _B.morLevel
      have A : Q(Type u₁) := _A.type
      have B : Q(Type u₂) := _B.type
      have _instA : Q(Category.{v₁} $A) := _A.inst
      have _instB : Q(Category.{v₂} $B) := _B.inst
      have f : Q($A ⥤ $B) := f
      have g : Q($B ⥤ $B) := g
      let assoc ← associators g q(𝟭 $B)
      have assoc : Q($g ≅ 𝟭 $B) := assoc
      return q(Functor.isoWhiskerLeft $f $assoc ≪≫ Functor.rightUnitor $f)
    | _ => do
    match ← assoc? f g with
    | some (f, g, h, i) => do
      let _A ← srcExpr f
      let _B ← tgtExpr f
      let _C ← tgtExpr g
      let _D ← tgtExpr h
      have u₁ := _A.objLevel
      have v₁ := _A.morLevel
      have u₂ := _B.objLevel
      have v₂ := _B.morLevel
      have u₃ := _C.objLevel
      have v₃ := _C.morLevel
      have u₄ := _D.objLevel
      have v₄ := _D.morLevel
      have A : Q(Type u₁) := _A.type
      have B : Q(Type u₂) := _B.type
      have C : Q(Type u₃) := _C.type
      have D : Q(Type u₄) := _D.type
      have _instA : Q(Category.{v₁} $A) := _A.inst
      have _instB : Q(Category.{v₂} $B) := _B.inst
      have _instC : Q(Category.{v₃} $C) := _C.inst
      have _instD : Q(Category.{v₄} $D) := _D.inst
      have f : Q($A ⥤ $B) := f
      have g : Q($B ⥤ $C) := g
      have h : Q($C ⥤ $D) := h
      have i : Q($A ⥤ $D) := i
      let assoc ← associators q($f ⋙ $g ⋙ $h) i
      have assoc : Q($f ⋙ $g ⋙ $h ≅ $i) := assoc
      return q(Functor.associator $f $g $h ≪≫ $assoc)
    | _ => do
    match ← assocInv? f g with
    | some (f, g, h, i) => do
      let _A ← srcExpr f
      let _B ← tgtExpr f
      let _C ← tgtExpr g
      let _D ← tgtExpr i
      have u₁ := _A.objLevel
      have v₁ := _A.morLevel
      have u₂ := _B.objLevel
      have v₂ := _B.morLevel
      have u₃ := _C.objLevel
      have v₃ := _C.morLevel
      have u₄ := _D.objLevel
      have v₄ := _D.morLevel
      have A : Q(Type u₁) := _A.type
      have B : Q(Type u₂) := _B.type
      have C : Q(Type u₃) := _C.type
      have D : Q(Type u₄) := _D.type
      have _instA : Q(Category.{v₁} $A) := _A.inst
      have _instB : Q(Category.{v₂} $B) := _B.inst
      have _instC : Q(Category.{v₃} $C) := _C.inst
      have _instD : Q(Category.{v₄} $D) := _D.inst
      have f : Q($A ⥤ $B) := f
      have g : Q($B ⥤ $C) := g
      have h : Q($C ⥤ $D) := h
      have i : Q($A ⥤ $D) := i
      let assoc ← associators i q($f ⋙ $g ⋙ $h)
      have assoc : Q($i ≅ $f ⋙ $g ⋙ $h) := assoc
      return q($assoc ≪≫ (Functor.associator $f $g $h).symm)
    | _ => do
      throwError
        m!"Failed to insert associators between {f} and {g}."

def associatorsHom (f g : Expr) : MetaM Expr := do
  let _A ← srcExpr f
  let _B ← tgtExpr f
  have u₁ := _A.objLevel
  have v₁ := _A.morLevel
  have u₂ := _B.objLevel
  have v₂ := _B.morLevel
  have A : Q(Type u₁) := _A.type
  have B : Q(Type u₂) := _B.type
  have _instA : Q(Category.{v₁} $A) := _A.inst
  have _instB : Q(Category.{v₂} $B) := _B.inst
  have f : Q($A ⥤ $B) := f
  have g : Q($A ⥤ $B) := g
  let assoc ← associators f g
  have assoc : Q($f ≅ $g) := assoc
  return q(Iso.hom $assoc)

/-- The domain and the codomain of a morphism. -/
def FunctorExpr (η : Expr) : MetaM (Expr × Expr) := do
  let η ← whnfR η
  match η.getAppFnArgs with
  | (``Quiver.Hom, #[_, _, F, G]) =>
    return ⟨F, G⟩
  | _ => throwError m!"{η} is not a natural transformation type"

section SimpTheorems

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅
variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
variable {E : Type u₅} [Category.{v₅} E]

open Functor

theorem id_whiskerLeft {F G : A ⥤ B} (η : F ⟶ G) :
    whiskerLeft (𝟭 A) η = (leftUnitor F).hom ≫ η ≫ (leftUnitor G).inv := by
  aesop_cat

theorem comp_whiskerLeft (F : A ⥤ B) (G : B ⥤ C) {H H' : C ⥤ D} (η : H ⟶ H') :
    whiskerLeft (F ⋙ G) η =
      (associator _ _ _).hom ≫ (whiskerLeft F (whiskerLeft G η)) ≫ (associator _ _ _).inv := by
  aesop_cat

theorem whiskerRight_id {F G : A ⥤ B} (η : F ⟶ G) :
    whiskerRight η (𝟭 B) = (rightUnitor F).hom ≫ η ≫ (rightUnitor G).inv := by
  aesop_cat

theorem whiskerRight_comp {F F' : A ⥤ B} (η : F ⟶ F') (G : B ⥤ C) (H : C ⥤ D) :
    whiskerRight η (G ⋙ H) =
      (associator _ _ _).inv ≫ whiskerRight (whiskerRight η G) H ≫ (associator _ _ _).hom := by
  aesop_cat

theorem whisker_assoc (F : A ⥤ B) {G G' : B ⥤ C} (η : G ⟶ G') (H : C ⥤ D) :
    whiskerRight (whiskerLeft F η) H =
      (associator _ _ _).hom ≫ whiskerLeft F (whiskerRight η H) ≫ (associator _ _ _).inv := by
  aesop_cat

local infixr:81 " ◁ " => Functor.whiskerLeft
local infixl:81 " ▷ " => Functor.whiskerRight
local notation "α_" => Functor.associator
local notation "λ_" => Functor.leftUnitor
local notation "ρ_" => Functor.rightUnitor

attribute [reassoc] Functor.pentagon

@[reassoc]
theorem pentagon_inv (f : A ⥤ B) (g : B ⥤ C) (h : C ⥤ D) (i : D ⥤ E) :
    f ◁ (α_ g h i).inv ≫ (α_ f (g ⋙ h) i).inv ≫ (α_ f g h).inv ▷ i =
      (α_ f g (h ⋙ i)).inv ≫ (α_ (f ⋙ g) h i).inv := by
  aesop_cat

@[reassoc]
theorem pentagon_inv_inv_hom_hom_inv (f : A ⥤ B) (g : B ⥤ C) (h : C ⥤ D) (i : D ⥤ E) :
    (α_ f (g ⋙ h) i).inv ≫ (α_ f g h).inv ▷ i ≫ (α_ (f ⋙ g) h i).hom =
    f ◁ (α_ g h i).hom ≫ (α_ f g (h ⋙ i)).inv := by
  aesop_cat

@[reassoc]
theorem pentagon_inv_hom_hom_hom_inv (f : A ⥤ B) (g : B ⥤ C) (h : C ⥤ D) (i : D ⥤ E) :
    (α_ (f ⋙ g) h i).inv ≫ (α_ f g h).hom ▷ i ≫ (α_ f (g ⋙ h) i).hom =
      (α_ f g (h ⋙ i)).hom ≫ f ◁ (α_ g h i).inv := by
  aesop_cat

@[reassoc]
theorem pentagon_hom_inv_inv_inv_inv (f : A ⥤ B) (g : B ⥤ C) (h : C ⥤ D) (i : D ⥤ E) :
    f ◁ (α_ g h i).hom ≫ (α_ f g (h ⋙ i)).inv ≫ (α_ (f ⋙ g) h i).inv =
      (α_ f (g ⋙ h) i).inv ≫ (α_ f g h).inv ▷ i := by
  aesop_cat

@[reassoc]
theorem pentagon_hom_hom_inv_hom_hom (f : A ⥤ B) (g : B ⥤ C) (h : C ⥤ D) (i : D ⥤ E) :
    (α_ (f ⋙ g) h i).hom ≫ (α_ f g (h ⋙ i)).hom ≫ f ◁ (α_ g h i).inv =
      (α_ f g h).hom ▷ i ≫ (α_ f (g ⋙ h) i).hom := by
  aesop_cat

@[reassoc]
theorem pentagon_hom_inv_inv_inv_hom (f : A ⥤ B) (g : B ⥤ C) (h : C ⥤ D) (i : D ⥤ E) :
    (α_ f g (h ⋙ i)).hom ≫ f ◁ (α_ g h i).inv ≫ (α_ f (g ⋙ h) i).inv =
    (α_ (f ⋙ g) h i).inv ≫ (α_ f g h).hom ▷ i := by
  aesop_cat

@[reassoc]
theorem pentagon_hom_hom_inv_inv_hom (f : A ⥤ B) (g : B ⥤ C) (h : C ⥤ D) (i : D ⥤ E) :
    (α_ f (g ⋙ h) i).hom ≫ f ◁ (α_ g h i).hom ≫ (α_ f g (h ⋙ i)).inv =
      (α_ f g h).inv ▷ i ≫ (α_ (f ⋙ g) h i).hom := by
  aesop_cat

@[reassoc]
theorem pentagon_inv_hom_hom_hom_hom (f : A ⥤ B) (g : B ⥤ C) (h : C ⥤ D) (i : D ⥤ E) :
    (α_ f g h).inv ▷ i ≫ (α_ (f ⋙ g) h i).hom ≫ (α_ f g (h ⋙ i)).hom =
      (α_ f (g ⋙ h) i).hom ≫ f ◁ (α_ g h i).hom := by
  aesop_cat

@[reassoc]
theorem pentagon_inv_inv_hom_inv_inv (f : A ⥤ B) (g : B ⥤ C) (h : C ⥤ D) (i : D ⥤ E) :
    (α_ f g (h ⋙ i)).inv ≫ (α_ (f ⋙ g) h i).inv ≫ (α_ f g h).hom ▷ i =
      f ◁ (α_ g h i).inv ≫ (α_ f (g ⋙ h) i).inv := by
  aesop_cat

attribute [reassoc] Functor.triangle

@[reassoc]
theorem triangle_assoc_comp_right (f : A ⥤ B) (g : B ⥤ C) :
    (α_ f (𝟭 B) g).inv ≫ (ρ_ f).hom ▷ g = f ◁ (λ_ g).hom := by
  aesop_cat

@[reassoc]
theorem triangle_assoc_comp_right_inv (f : A ⥤ B) (g : B ⥤ C) :
    (ρ_ f).inv ▷ g ≫ (α_ f (𝟭 B) g).hom = f ◁ (λ_ g).inv := by
  aesop_cat

@[reassoc]
theorem triangle_assoc_comp_left_inv (f : A ⥤ B) (g : B ⥤ C) :
    f ◁ (λ_ g).inv ≫ (α_ f (𝟭 B) g).inv = (ρ_ f).inv ▷ g := by
  aesop_cat

theorem leftUnitor_whiskerRight (F : A ⥤ B) (G : B ⥤ C) :
    (λ_ F).hom ▷ G = (α_ (𝟭 A) F G).hom ≫ (λ_ (F ⋙ G)).hom := by
  aesop_cat

theorem leftUnitor_inv_whiskerRight (F : A ⥤ B) (G : B ⥤ C) :
    (λ_ F).inv ▷ G = (λ_ (F ⋙ G)).inv ≫ (α_ (𝟭 A) F G).inv := by
  aesop_cat

theorem whiskerLeft_rightUnitor (F : A ⥤ B) (G : B ⥤ C) :
    F ◁ (ρ_ G).hom = (α_ F G (𝟭 C)).inv ≫ (ρ_ (F ⋙ G)).hom := by
  aesop_cat

theorem whiskerLeft_rightUnitor_inv (F : A ⥤ B) (G : B ⥤ C) :
    F ◁ (ρ_ G).inv = (ρ_ (F ⋙ G)).inv ≫ (α_ F G (𝟭 C)).hom := by
  aesop_cat

def simpTheoremNames : Array Name :=
  #[``Category.id_comp, ``Category.comp_id, ``Category.assoc,
    ``Iso.hom_inv_id, ``Iso.hom_inv_id_assoc,
    ``Iso.inv_hom_id, ``Iso.inv_hom_id_assoc,
    ``Functor.whiskerLeft_id', ``Functor.whiskerRight_id',
    ``Functor.whiskerLeft_comp, ``Functor.whiskerRight_comp,
    ``Associators.id_whiskerLeft, ``Associators.comp_whiskerLeft,
    ``Associators.whiskerRight_id, ``Associators.whiskerRight_comp,
    ``Associators.whisker_assoc,
    ``Functor.pentagon, ``Functor.pentagon_assoc,
    ``Associators.pentagon_inv, ``Associators.pentagon_inv_assoc,
    ``Associators.pentagon_inv_inv_hom_hom_inv, ``Associators.pentagon_inv_inv_hom_hom_inv_assoc,
    ``Associators.pentagon_inv_hom_hom_hom_inv, ``Associators.pentagon_inv_hom_hom_hom_inv_assoc,
    ``Associators.pentagon_hom_inv_inv_inv_inv, ``Associators.pentagon_hom_inv_inv_inv_inv_assoc,
    ``Associators.pentagon_hom_hom_inv_hom_hom, ``Associators.pentagon_hom_hom_inv_hom_hom_assoc,
    ``Associators.pentagon_hom_inv_inv_inv_hom, ``Associators.pentagon_hom_inv_inv_inv_hom_assoc,
    ``Associators.pentagon_hom_hom_inv_inv_hom, ``Associators.pentagon_hom_hom_inv_inv_hom_assoc,
    ``Associators.pentagon_inv_hom_hom_hom_hom, ``Associators.pentagon_inv_hom_hom_hom_hom_assoc,
    ``Associators.pentagon_inv_inv_hom_inv_inv, ``Associators.pentagon_inv_inv_hom_inv_inv_assoc,
    ``Functor.triangle, ``Functor.triangle_assoc,
    ``Associators.triangle_assoc_comp_right, ``Associators.triangle_assoc_comp_right_assoc,
    ``Associators.triangle_assoc_comp_right_inv, ``Associators.triangle_assoc_comp_right_inv_assoc,
    ``Associators.triangle_assoc_comp_left_inv, ``Associators.triangle_assoc_comp_left_inv_assoc,
    ``Associators.leftUnitor_whiskerRight,
    ``Associators.leftUnitor_inv_whiskerRight,
    ``Associators.whiskerLeft_rightUnitor,
    ``Associators.whiskerLeft_rightUnitor_inv,
    ``Iso.refl_hom, ``Iso.refl_inv, ``Iso.trans_hom, ``Iso.trans_inv,
    ``Iso.symm_hom, ``Iso.symm_inv,
    ``Functor.isoWhiskerLeft_hom, ``Functor.isoWhiskerLeft_inv,
    ``Functor.isoWhiskerRight_hom, ``Functor.isoWhiskerRight_inv,
    ``Functor.isoWhiskerLeft_trans, ``Functor.isoWhiskerRight_trans]

end SimpTheorems

syntax (name := assoc) "assoc%" : term

@[term_elab assoc]
def elabAssociators : Term.TermElab := fun _ expectedType? => do
  match expectedType? with
  | none => throwError "expected type not provided for `assoc%`"
  | some e =>
    let ⟨F, G⟩ ← FunctorExpr e
    let α ← associatorsHom F G
    let thms := (← simpTheoremNames.mapM (fun n => mkSimpTheoremFromConst n)).flatten
    let thms : SimpTheorems := (thms.foldl (·.addSimpTheorem ·)) {}
    let (α', _) ← simp α (← Simp.mkContext (simpTheorems := #[thms]))
    Tactic.TryThis.addTermSuggestion (← getRef) α'.expr
    return α'.expr

end Associators

end Mathlib.Tactic
