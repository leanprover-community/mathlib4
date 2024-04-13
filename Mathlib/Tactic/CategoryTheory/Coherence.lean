/-
Copyright (c) 2022. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yuma Mizuno, Oleksandr Manzyuk
-/
import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Mathlib.Lean.Meta
import Mathlib.Tactic.CategoryTheory.BicategoryCoherence
import Mathlib.Tactic.CategoryTheory.MonoidalComp

#align_import category_theory.monoidal.coherence from "leanprover-community/mathlib"@"f187f1074fa1857c94589cc653c786cadc4c35ff"

/-!
# A `coherence` tactic for monoidal categories

We provide a `coherence` tactic,
which proves equations where the two sides differ by replacing
strings of monoidal structural morphisms with other such strings.
(The replacements are always equalities by the monoidal coherence theorem.)

A simpler version of this tactic is `pure_coherence`,
which proves that any two morphisms (with the same source and target)
in a monoidal category which are built out of associators and unitors
are equal.

-/

set_option autoImplicit true

-- Porting note: restore when ported
-- import Mathlib.CategoryTheory.Bicategory.CoherenceTactic

universe v u

open CategoryTheory FreeMonoidalCategory

-- As the lemmas and typeclasses in this file are not intended for use outside of the tactic,
-- we put everything inside a namespace.
namespace Mathlib.Tactic.Coherence

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
open scoped MonoidalCategory

noncomputable section lifting

/-- A typeclass carrying a choice of lift of an object from `C` to `FreeMonoidalCategory C`.
It must be the case that `projectObj id (LiftObj.lift x) = x` by defeq. -/
class LiftObj (X : C) where
  protected lift : C
  protected free_lift : FreeMonoidalCategory C

instance LiftObj_unit : LiftObj (𝟙_ C) := ⟨𝟙_ C, unit⟩

instance LiftObj_tensor (X Y : C) [LiftObj X] [LiftObj Y] : LiftObj (X ⊗ Y) where
  lift := LiftObj.lift X ⊗ LiftObj.lift Y
  free_lift := LiftObj.free_lift X ⊗ LiftObj.free_lift Y

instance (priority := 100) LiftObj_of (X : C) : LiftObj X := ⟨X, of X⟩

/-- A typeclass carrying a choice of lift of a morphism from `C` to `FreeMonoidalCategory C`.
It must be the case that `projectMap id _ _ (LiftHom.lift f) = f` by defeq. -/
class LiftHom {X Y : C} [LiftObj X] [LiftObj Y] (f : X ⟶ Y) where
  protected lift : LiftObj.lift X ⟶ LiftObj.lift Y
  protected free_lift : LiftObj.free_lift X ⟶ LiftObj.free_lift Y

instance LiftHom_id (X : C) [LiftObj X] : LiftHom (𝟙 X) := ⟨𝟙 _, 𝟙 _⟩

instance LiftHom_left_unitor_hom (X : C) [LiftObj X] : LiftHom (λ_ X).hom where
  lift := (λ_ (LiftObj.lift X)).hom
  free_lift := (λ_ (LiftObj.free_lift X)).hom

instance LiftHom_left_unitor_inv (X : C) [LiftObj X] : LiftHom (λ_ X).inv where
  lift := (λ_ (LiftObj.lift X)).inv
  free_lift := (λ_ (LiftObj.free_lift X)).inv

instance LiftHom_right_unitor_hom (X : C) [LiftObj X] : LiftHom (ρ_ X).hom where
  lift := (ρ_ (LiftObj.lift X)).hom
  free_lift := (ρ_ (LiftObj.free_lift X)).hom

instance LiftHom_right_unitor_inv (X : C) [LiftObj X] : LiftHom (ρ_ X).inv where
  lift := (ρ_ (LiftObj.lift X)).inv
  free_lift := (ρ_ (LiftObj.free_lift X)).inv

instance LiftHom_associator_hom (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] :
    LiftHom (α_ X Y Z).hom where
  lift := (α_ (LiftObj.lift X) (LiftObj.lift Y) (LiftObj.lift Z)).hom
  free_lift := (α_ (LiftObj.free_lift X) (LiftObj.free_lift Y) (LiftObj.free_lift Z)).hom

instance LiftHom_associator_inv (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] :
    LiftHom (α_ X Y Z).inv where
  lift := (α_ (LiftObj.lift X) (LiftObj.lift Y) (LiftObj.lift Z)).inv
  free_lift := (α_ (LiftObj.free_lift X) (LiftObj.free_lift Y) (LiftObj.free_lift Z)).inv

instance LiftHom_comp {X Y Z : C} [LiftObj X] [LiftObj Y] [LiftObj Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    [LiftHom f] [LiftHom g] : LiftHom (f ≫ g) where
  lift := LiftHom.lift f ≫ LiftHom.lift g
  free_lift := LiftHom.free_lift f ≫ LiftHom.free_lift g

instance liftHom_WhiskerLeft (X : C) [LiftObj X] {Y Z : C} [LiftObj Y] [LiftObj Z]
    (f : Y ⟶ Z) [LiftHom f] : LiftHom (X ◁ f) where
  lift := LiftObj.lift X ◁ LiftHom.lift f

instance liftHom_WhiskerRight {X Y : C} (f : X ⟶ Y) [LiftObj X] [LiftObj Y] [LiftHom f]
    {Z : C} [LiftObj Z] : LiftHom (f ▷ Z) where
  lift := LiftHom.lift f ▷ LiftObj.lift Z

instance LiftHom_tensor {W X Y Z : C} [LiftObj W] [LiftObj X] [LiftObj Y] [LiftObj Z]
    (f : W ⟶ X) (g : Y ⟶ Z) [LiftHom f] [LiftHom g] : LiftHom (f ⊗ g) where
  lift := LiftHom.lift f ⊗ LiftHom.lift g
  free_lift := LiftHom.free_lift f ⊗ LiftHom.free_lift g

end lifting

open Lean Meta Elab Tactic

/-- Helper function for throwing exceptions. -/
def exception (g : MVarId) (msg : MessageData) : MetaM α := throwTacticEx `monoidal_coherence g msg

/-- Helper function for throwing exceptions with respect to the main goal. -/
def exception' (msg : MessageData) : TacticM Unit := do
  try
    liftMetaTactic (exception (msg := msg))
  catch _ =>
    -- There might not be any goals
    throwError msg

/-- Auxiliary definition for `monoidal_coherence`. -/
-- We could construct this expression directly without using `elabTerm`,
-- but it would require preparing many implicit arguments by hand.
def mkProjectMapExpr (e : Expr) : TermElabM Expr := do
  Term.elabTerm
    (← ``(FreeMonoidalCategory.projectMap _root_.id _ _ (LiftHom.free_lift $(← Term.exprToSyntax e))))
    none

/-- Coherence tactic for monoidal categories. -/
def monoidal_coherence (g : MVarId) : TermElabM Unit := g.withContext do
  withOptions (fun opts => synthInstance.maxSize.set opts
    (max 512 (synthInstance.maxSize.get opts))) do
  -- TODO: is this `dsimp only` step necessary? It doesn't appear to be in the tests below.
  let (ty, _) ← dsimp (← g.getType) (← Simp.Context.ofNames [] true)
  let some (_, lhs, rhs) := (← whnfR ty).eq? | exception g "Not an equation of morphisms."
  let projectMap_lhs ← mkProjectMapExpr lhs
  let projectMap_rhs ← mkProjectMapExpr rhs
  -- This new equation is defeq to the original by assumption
  -- on the `LiftObj` and `LiftHom` instances.
  let g₁ ← g.change (← mkEq projectMap_lhs projectMap_rhs)
  let [g₂] ← g₁.applyConst ``congrArg
    | exception g "congrArg failed in coherence"
  let [] ← g₂.applyConst ``Subsingleton.elim
    | exception g "This shouldn't happen; Subsingleton.elim does not create goals."

/-- Coherence tactic for monoidal categories.
Use `pure_coherence` instead, which is a frontend to this one. -/
elab "monoidal_coherence" : tactic => do monoidal_coherence (← getMainGoal)

open Mathlib.Tactic.BicategoryCoherence

/--
`pure_coherence` uses the coherence theorem for monoidal categories to prove the goal.
It can prove any equality made up only of associators, unitors, and identities.
```lean
example {C : Type} [Category C] [MonoidalCategory C] :
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
by pure_coherence
```

Users will typically just use the `coherence` tactic,
which can also cope with identities of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `pure_coherence`
-/
elab (name := pure_coherence) "pure_coherence" : tactic => do
  let g ← getMainGoal
  monoidal_coherence g <|> bicategory_coherence g

/--
Auxiliary simp lemma for the `coherence` tactic:
this moves brackets to the left in order to expose a maximal prefix
built out of unitors and associators.
-/
-- We have unused typeclass arguments here.
-- They are intentional, to ensure that `simp only [assoc_LiftHom]` only left associates
-- monoidal structural morphisms.
@[nolint unusedArguments]
lemma assoc_liftHom {W X Y Z : C} [LiftObj W] [LiftObj X] [LiftObj Y]
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) [LiftHom f] [LiftHom g] :
    f ≫ (g ≫ h) = (f ≫ g) ≫ h :=
  (Category.assoc _ _ _).symm

section
open Lean Meta Elab
open CategoryTheory

structure Context where
  C : Expr
  -- instC : Expr
  -- instMC : Expr
  proof : Bool

/-- Populate a `context` object for evaluating `e`. -/
def mkContext (e : Expr) (proof := false) : MetaM Context := do
  match (← inferType e).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) =>
    let C ← inferType f
    let v ← mkFreshLevelMVar
    let u ← mkFreshLevelMVar
    let instC ← synthInstance (mkAppN (.const ``Category [v, u]) #[C])
    let instMC ← synthInstance (mkAppN (.const ``MonoidalCategory [v, u]) #[C, instC])
    let lctx ← Lean.MonadLCtx.getLCtx
    for decl in lctx do
      println! "{← ppExpr decl.toExpr} : {← ppExpr decl.type}"
    println! "instC: {instC}"
    return ⟨C, proof⟩
  | _ => throwError "not a morphism"

/-- The monad for `Abel` contains, in addition to the `AtomM` state,
some information about the current type we are working over, so that we can consistently
use group lemmas or monoid lemmas as appropriate. -/
abbrev M := ReaderT Context MetaM

/-- Expressions for atomic 1-morphisms. -/
structure Atom₁ : Type where
  /-- Extract a Lean expression from an `Atom₁` expression. -/
  e : Expr

/-- Expressions for 1-morphisms. -/
inductive Mor₁ : Type
  /-- `id C` is the expression for `𝟙_ C`. -/
  | id : Mor₁
  /-- `comp X Y` is the expression for `X ⊗ Y` -/
  | comp : Mor₁ → Mor₁ → Mor₁
  /-- Construct the expression for an atomic 1-morphism. -/
  | of : Atom₁ → Mor₁
  deriving Inhabited

/-- Extract a Lean expression from a `Mor₁` expression. -/
def Mor₁.e : Mor₁ → M Expr
  | .id => do
    mkAppOptM ``MonoidalCategoryStruct.tensorUnit #[(← read).C, none, none]
  | .comp f g => do
    mkAppM ``MonoidalCategoryStruct.tensorObj #[← Mor₁.e f, ← Mor₁.e g]
  | .of f => return f.e

/-- Converts a 1-morphism into a list of its underlying expressions. -/
def Mor₁.toList : Mor₁ → List Expr
  | .id => []
  | .comp f g => f.toList ++ g.toList
  | .of f => [f.e]

/-- Construct a `Mor₁` expression from a Lean expression. -/
partial def toMor₁ (e : Expr) : Mor₁ :=
  match e.getAppFnArgs with
  | (``MonoidalCategoryStruct.tensorUnit, #[C, _, _]) => Mor₁.id
  | (``MonoidalCategoryStruct.tensorObj, #[_, _, _, f, g]) => (toMor₁ f).comp (toMor₁ g)
  | _ => Mor₁.of ⟨e⟩

/-- Expressions for atomic structural 2-morphisms. -/
inductive StructuralAtom : Type
  /-- The expression for the associator `(α_ f g h).hom`. -/
  | associator (f g h : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the associator `(α_ f g h).inv`. -/
  | associatorInv (f g h : Mor₁) : StructuralAtom
  /-- The expression for the left unitor `(λ_ f).hom`. -/
  | leftUnitor (f : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the left unitor `(λ_ f).inv`. -/
  | leftUnitorInv (f : Mor₁) : StructuralAtom
  /-- The expression for the right unitor `(ρ_ f).hom`. -/
  | rightUnitor (f : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the right unitor `(ρ_ f).inv`. -/
  | rightUnitorInv (f : Mor₁) : StructuralAtom
  deriving Inhabited

/-- Extract a Lean expression from a `StructuralAtom` expression. -/
def StructuralAtom.e : StructuralAtom → M Expr
  | .associator f g h => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.associator #[← f.e, ← g.e, ← h.e]]
  | .associatorInv f g h => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.associator #[← f.e, ← g.e, ← h.e]]
  | .leftUnitor f => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.leftUnitor #[← f.e]]
  | .leftUnitorInv f => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.leftUnitor #[← f.e]]
  | .rightUnitor f => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.rightUnitor #[← f.e]]
  | .rightUnitorInv f => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.rightUnitor #[← f.e]]

/-- Construct a `StructuralAtom` expression from a Lean expression. -/
def structuralAtom? (e : Expr) : Option StructuralAtom := do
  match e.getAppFnArgs with
  | (``Iso.hom, #[_, _, _, _, η]) =>
    match η.getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      return .associator (toMor₁ f) (toMor₁ g) (toMor₁ h)
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) => return .leftUnitor (toMor₁ f)
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) => return .rightUnitor (toMor₁ f)
    | _ => none
  | (``Iso.inv, #[_, _, _, _, η]) =>
    match η.getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      return .associatorInv (toMor₁ f) (toMor₁ g) (toMor₁ h)
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) => return .leftUnitorInv (toMor₁ f)
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) => return .rightUnitorInv (toMor₁ f)
    | _ => none
  | _ => none

/-- Expressions for atomic (non-structural) 2-morphisms. -/
structure Atom where
  /-- Extract a Lean expression from an `Atom` expression. -/
  e : Expr
  deriving Inhabited

/-- Expressions for atomic 2-Morphisms. -/
inductive Core : Type
  -- /-- Construct the expression for a structural 2-morphism. -/
  -- | ofStructural : StructuralAtom → Core
  /-- Construct the expression for an atomic 2-morphism. -/
  | of : Atom → Core
  deriving Inhabited

/-- Extract a Lean expression from a `Core` expression. -/
def Core.e : Core → M Expr
  -- | .ofStructural η => η.e
  | .of a => return a.e

/-- Expressions of the form `η ▷ f₁ ▷ ... ▷ fₙ`. -/
inductive WhiskerRightExpr : Type
  /-- Construct the expression for a core 2-morphism. -/
  | of (η : Core) : WhiskerRightExpr
  /-- Construct the expression for `η ▷ f`. -/
  | whisker (η : WhiskerRightExpr) (f : Atom₁) : WhiskerRightExpr
  deriving Inhabited

/-- Expressions of the form `f₁ ◁ ... ◁ fₙ ◁ η`. -/
inductive WhiskerLeftExpr : Type
  /-- Construct the expression for a right-whiskered 2-morphism. -/
  | of (η : WhiskerRightExpr) : WhiskerLeftExpr
  /-- Construct the expression for `f ◁ η`. -/
  | whisker (f : Atom₁) (η : WhiskerLeftExpr) : WhiskerLeftExpr
  deriving Inhabited

inductive Structural : Type
  | atom (η : StructuralAtom) : Structural
  | id (f : Mor₁) : Structural
  | comp (α β : Structural) : Structural
  | whiskerLeft (f : Mor₁) (η : Structural) : Structural
  | whiskerRight (η : Structural) (f : Mor₁) : Structural
  | monoidalCoherence (f g : Mor₁) (e : Expr) : Structural
  deriving Inhabited

/-- Normalized expressions for 2-morphisms. -/
inductive NormalExpr : Type
  /-- Construct the expression for `𝟙 f`. -/
  | nil (src tar : Mor₁) (η : Structural) : NormalExpr
  /-- Construct the normalized expression of 2-morphisms recursively. -/
  | cons (head_structural : Structural) (head : WhiskerLeftExpr) (tail : NormalExpr) : NormalExpr
  deriving Inhabited

/-- The domain of a morphism. -/
def src (η : Expr) : MetaM Mor₁ := do
  match (← inferType η).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) => return toMor₁ f
  | _ => throwError "{η} is not a morphism"

/-- The codomain of a morphism. -/
def tar (η : Expr) : MetaM Mor₁ := do
  match (← inferType η).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, _, g]) => return toMor₁ g
  | _ => throwError "{η} is not a morphism"

/-- The domain of a 2-morphism. -/
def Core.src (η : Core) : M Mor₁ := do Coherence.src (← η.e)
/-- The codomain of a 2-morphism. -/
def Core.tar (η : Core) : M Mor₁ := do Coherence.tar (← η.e)

-- /-- Construct a normalized expression from an atomic 2-morphism. -/
-- def NormalExpr.mk (η : Core) : MetaM NormalExpr := do
--   return .cons (.of (.of η)) (.id (← η.tar))

/-- The domain of a 2-morphism. -/
def WhiskerRightExpr.src : WhiskerRightExpr → M Mor₁
  | WhiskerRightExpr.of η => η.src
  | WhiskerRightExpr.whisker η f => return (← WhiskerRightExpr.src η).comp (Mor₁.of f)

/-- The codomain of a 2-morphism. -/
def WhiskerRightExpr.tar : WhiskerRightExpr → M Mor₁
  | WhiskerRightExpr.of η => η.tar
  | WhiskerRightExpr.whisker η f => return (← WhiskerRightExpr.tar η).comp (Mor₁.of f)

/-- The domain of a 2-morphism. -/
def WhiskerLeftExpr.src : WhiskerLeftExpr → M Mor₁
  | WhiskerLeftExpr.of η => WhiskerRightExpr.src η
  | WhiskerLeftExpr.whisker f η => return (Mor₁.of f).comp (← WhiskerLeftExpr.src η)

/-- The codomain of a 2-morphism. -/
def WhiskerLeftExpr.tar : WhiskerLeftExpr → M Mor₁
  | WhiskerLeftExpr.of η => WhiskerRightExpr.tar η
  | WhiskerLeftExpr.whisker f η => return (Mor₁.of f).comp (← WhiskerLeftExpr.tar η)

/-- Extract a Lean expression from a `WhiskerRightExpr` expression. -/
def WhiskerRightExpr.e : WhiskerRightExpr → M Expr
  | WhiskerRightExpr.of η => η.e
  | WhiskerRightExpr.whisker η f => do
    mkAppM ``MonoidalCategoryStruct.whiskerRight #[← η.e, f.e]

/-- Extract a Lean expression from a `WhiskerLeftExpr` expression. -/
def WhiskerLeftExpr.e : WhiskerLeftExpr → M Expr
  | WhiskerLeftExpr.of η => η.e
  | WhiskerLeftExpr.whisker f η => do
    mkAppM ``MonoidalCategoryStruct.whiskerLeft #[f.e, ← η.e]

partial def Structural.e : Structural → M Expr
  | .atom η => η.e
  | .id f => do
    mkAppM ``CategoryStruct.id #[← f.e]
  | .comp α β => do
    match α, β with
    -- | _, .id _ => α.e
    -- | .id _ , _ => β.e
    | _, _ => mkAppM ``CategoryStruct.comp #[← α.e, ← β.e]
  | .whiskerLeft f η => do
    match η with
    -- | .id g => mkAppM ``CategoryStruct.id #[← (f.comp g).e]
    -- | .comp η₁ η₂ => mkAppM ``MonoidalCategoryStruct.whiskerLeft #[← f.e, ← mkAppM ``CategoryStruct.comp #[← η₁.e, ← η₂.e]]
    | _ => mkAppM ``MonoidalCategoryStruct.whiskerLeft #[← f.e, ← η.e]
  | .whiskerRight η f => do
    match η with
    -- | .id g => mkAppM ``CategoryStruct.id #[← (g.comp f).e]
    | _ => mkAppM ``MonoidalCategoryStruct.whiskerRight #[← η.e, ← f.e]
  | .monoidalCoherence _ _ e => do
    mkAppOptM ``MonoidalCoherence.hom #[none, none, none, none, e]
    -- return e

def StructuralAtom.src : StructuralAtom → Mor₁
  | .associator f g h => (f.comp g).comp h
  | .associatorInv f g h => f.comp (g.comp h)
  | .leftUnitor f => (Mor₁.id).comp f
  | .leftUnitorInv f => f
  | .rightUnitor f => f.comp (Mor₁.id)
  | .rightUnitorInv f => f

def StructuralAtom.tar : StructuralAtom → Mor₁
  | .associator f g h => f.comp (g.comp h)
  | .associatorInv f g h => (f.comp g).comp h
  | .leftUnitor f => f
  | .leftUnitorInv f => (Mor₁.id).comp f
  | .rightUnitor f => f
  | .rightUnitorInv f => f.comp (Mor₁.id)

def Structural.src : Structural → Mor₁
  | .atom η => η.src
  | .id f => f
  | .comp α β => α.src
  | .whiskerLeft f η => f.comp (η.src)
  | .whiskerRight η f => (η.src).comp f
  | .monoidalCoherence f g _ => f

def Structural.tar : Structural → Mor₁
  | .atom η => η.tar
  | .id f => f
  | .comp α β => β.tar
  | .whiskerLeft f η => f.comp (η.tar)
  | .whiskerRight η f => (η.tar).comp f
  | .monoidalCoherence f g _ => g

/-- Extract a Lean expression from a `NormalExpr` expression. -/
def NormalExpr.e : NormalExpr → M Expr
  | NormalExpr.nil _ _ α => α.e
  -- | NormalExpr.cons (.id _) η (NormalExpr.nil _ _ (.id _)) => η.e
  | NormalExpr.cons α η θ => do
    mkAppM ``CategoryStruct.comp #[← α.e, ← mkAppM ``CategoryStruct.comp #[← η.e, ← θ.e]]

/-- The domain of a 2-morphism. -/
def NormalExpr.src : NormalExpr → M Mor₁
  | NormalExpr.nil src tar f => return src
  | NormalExpr.cons α η ηs => do Coherence.src (← α.e)

/-- The codomain of a 2-morphism. -/
def NormalExpr.tar : NormalExpr → MetaM Mor₁
  | NormalExpr.nil src tar f => return tar
  | NormalExpr.cons α η ηs => ηs.tar

/-- The associator as a term of `normalExpr`. -/
def NormalExpr.associator (f g h : Mor₁) : NormalExpr :=
  .nil (f.comp (g.comp h)) (f.comp (g.comp h)) (.atom <| .associator f g h)

/-- The inverse of the associator as a term of `normalExpr`. -/
def NormalExpr.associatorInv (f g h : Mor₁) : NormalExpr :=
  .nil ((f.comp g).comp h) (f.comp (g.comp h)) (.atom <| .associatorInv f g h)

/-- The left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitor (f : Mor₁) : NormalExpr :=
  .nil ((Mor₁.id).comp f) f (.atom <| .leftUnitor f)

/-- The inverse of the left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitorInv (f : Mor₁) : NormalExpr :=
  .nil f ((Mor₁.id).comp f) (.atom <| .leftUnitorInv f)

/-- The right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitor (f : Mor₁) : NormalExpr :=
  .nil (f.comp (Mor₁.id)) f (.atom <| .rightUnitor f)

/-- The inverse of the right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitorInv (f : Mor₁) : NormalExpr :=
  .nil f (f.comp (Mor₁.id)) (.atom <| .rightUnitorInv f)

/-- Return `η` for `η ▷ g₁ ▷ ... ▷ gₙ`. -/
def WhiskerRightExpr.core : WhiskerRightExpr → Core
  | WhiskerRightExpr.of η => η
  | WhiskerRightExpr.whisker η _ => η.core

/-- Return `η` for `f₁ ◁ ... ◁ fₙ ◁ η ▷ g₁ ▷ ... ▷ gₙ`. -/
def WhiskerLeftExpr.core : WhiskerLeftExpr → Core
  | WhiskerLeftExpr.of η => η.core
  | WhiskerLeftExpr.whisker _ η => η.core

-- /-- Return `ture` if `η` is a structural 2-morphism. -/
-- def WhiskerLeftExpr.isStructural (η : WhiskerLeftExpr) : Bool :=
--   match η.core with
--   | .of _ => false
--   | .ofStructural _ => true

-- /-- Interpret an `Expr` term as a `Core` term. -/
-- def toCore (e : Expr) : Core :=
--   match structuralAtom? e with
--   | some η => Core.ofStructural η
--   | none => Core.of ⟨e⟩

partial def structural? (e : Expr) : M Structural := do
  -- let _ ← dsimp e {}
  -- if let some η ← isDefEq e e then
  --   sorry
  match (← whnfR e).getAppFnArgs with
  | (``CategoryStruct.comp, #[_, _, _, α, β]) =>
    return .comp (← structural? α) (← structural? β)
  | (``CategoryStruct.id, #[_, f]) => return .id (toMor₁ f)
  | (``MonoidalCategoryStruct.whiskerLeft, #[f, η]) => return .whiskerLeft (toMor₁ f) (← structural? η)
  | (``MonoidalCategoryStruct.whiskerRight, #[η, f]) => return .whiskerRight (← structural? η) (toMor₁ f)
  | (``MonoidalCoherence.hom, #[_, _, f, g, inst]) =>
    return .monoidalCoherence (toMor₁ f) (toMor₁ g) inst
    -- match structuralAtom? η with
    -- | some η => return .atom η
    -- | none => throwError "not a structural 2-morphism : {← ppExpr (← whnfR e)}"
  | _ => match structuralAtom? e with
    | some η => return .atom η
    | none => throwError "not a structural 2-morphism : {← ppExpr (← whnfR e)}"

def toCore (e : Expr) : Core :=
  Core.of ⟨e⟩

/-- Construct a `NormalExpr` expression from a Lean expression for a core 2-morphism. -/
def NormalExpr.of (η : Expr) : MetaM NormalExpr := do
  return .cons (.id (← Coherence.src η)) (.of (.of (toCore η))) (.nil (← Coherence.tar η) (← Coherence.tar η) (.id (← Coherence.tar η)))

section
open scoped MonoidalCategory
-- universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
-- (instC : Category.{v} C) (instMC : MonoidalCategory C)
variable {f f' g g' h i j : C}

theorem evalComp_nil_cons {f g h i j : C} (α : f ⟶ g) (β : g ⟶ h) (η : h ⟶ i) (ηs : i ⟶ j) :
    α ≫ (β ≫ η ≫ ηs) = (α ≫ β) ≫ η ≫ ηs := by
  simp

theorem evalComp_nil_nil {f g h : C} (α : f ⟶ g) (β : g ⟶ h) :
    α ≫ β = α ≫ β := by
  simp

theorem evalComp_cons {f g h i j : C} (α : f ⟶ g) (η : g ⟶ h) (ηs : h ⟶ i) (θ : i ⟶ j) (ι : h ⟶ j) (pf_ι : ηs ≫ θ = ι)  :
    (α ≫ η ≫ ηs) ≫ θ = α ≫ η ≫ ι := by
  simp [pf_ι]

theorem evalWhiskerLeft_nil (f : C) (α : g ⟶ h) :
    f ◁ α = f ◁ α := by
  simp

theorem evalWhiskerLeft_of_cons {f g h i j : C} (α : g ⟶ h) (η : h ⟶ i) (ηs : i ⟶ j) (θ : f ⊗ i ⟶ f ⊗ j) (pf_θ : f ◁ ηs = θ) :
    f ◁ (α ≫ η ≫ ηs) = f ◁ α ≫ f ◁ η ≫ θ := by
  simp [pf_θ]

theorem evalWhiskerLeft_comp {f g h i : C} (η : h ⟶ i) (θ : g ⊗ h ⟶ g ⊗ i) (ι : f ⊗ g ⊗ h ⟶ f ⊗ g ⊗ i)
    (ι' : f ⊗ g ⊗ h ⟶ (f ⊗ g) ⊗ i) (ι'' : (f ⊗ g) ⊗ h ⟶ (f ⊗ g) ⊗ i)
    (pf_θ : g ◁ η = θ) (pf_ι : f ◁ θ = ι) (pf_ι' : ι ≫ (α_ _ _ _).inv = ι') (pf_ι'' : (α_ _ _ _).hom ≫ ι' = ι'') :
    (f ⊗ g) ◁ η = ι'' := by
  simp [pf_θ, pf_ι, pf_ι', pf_ι'']

theorem evalWhiskerLeft_id {f g : C} (η : f ⟶ g) (η' : f ⟶ 𝟙_ C ⊗ g) (η'' : 𝟙_ C ⊗ f ⟶ 𝟙_ C ⊗ g)
    (pf_η' : η ≫ (λ_ _).inv = η') (pf_η'' : (λ_ _).hom ≫ η' = η'') :
    𝟙_ C ◁ η = η'' := by
  simp [pf_η', pf_η'']

theorem eval_comp (η η' : f ⟶ g) (θ θ' : g ⟶ h) (ι : f ⟶ h) (pf_η : η = η') (pf_θ : θ = θ') (pf_ηθ : η' ≫ θ' = ι) :
    η ≫ θ = ι := by simp [pf_η, pf_θ, pf_ηθ]

theorem eval_whiskerLeft (f : C) (η η' : g ⟶ h) (θ : f ⊗ g ⟶ f ⊗ h) (pf_η : η = η') (pf_θ : f ◁ η' = θ) :
    f ◁ η = θ := by
  simp [pf_η, pf_θ]

theorem eval_whiskerRight (η η' : f ⟶ g) (h : C) (θ : f ⊗ h ⟶ g ⊗ h) (pf_η : η = η') (pf_θ : η' ▷ h = θ) :
    η ▷ h = θ := by
  simp [pf_η, pf_θ]

theorem eval_of (η : f ⟶ g) :
    η = 𝟙 _ ≫ η ≫ 𝟙 _ := by
  simp

theorem evalWhiskerRight_nil (α : f ⟶ g) (h : C) :
    α ▷ h = α ▷ h := by
  simp

theorem evalWhiskerRight_cons_of_of (α : f ⟶ g) (η : g ⟶ h) (ηs : h ⟶ i) (j : C) (θ : h ⊗ j ⟶ i ⊗ j)
    (pf_θ : ηs ▷ j = θ) :
    (α ≫ η ≫ ηs) ▷ j = α ▷ j ≫ η ▷ j ≫ θ := by
  simp [pf_θ]

theorem evalWhiskerRight_cons_whisker (f : C) (α : g ⟶ f ⊗ h) (η : h ⟶ i) (ηs : f ⊗ i ⟶ j) (k : C)
    (η₁ : h ⊗ k ⟶ i ⊗ k) (η₂ : f ⊗ (h ⊗ k) ⟶ f ⊗ (i ⊗ k)) (ηs₁ : (f ⊗ i) ⊗ k ⟶ j ⊗ k)
    (ηs₂ : f ⊗ (i ⊗ k) ⟶ j ⊗ k) (η₃ : f ⊗ (h ⊗ k) ⟶ j ⊗ k) (η₄ : (f ⊗ h) ⊗ k ⟶ j ⊗ k)
    (η₅ : g ⊗ k ⟶ j ⊗ k)
    (pf_η₁ : (𝟙 _ ≫ η ≫ 𝟙 _ ) ▷ k = η₁) (pf_η₂ : f ◁ η₁ = η₂) (pf_ηs₁ : ηs ▷ k = ηs₁) (pf_ηs₂ : (α_ _ _ _).inv ≫ ηs₁ = ηs₂)
    (pf_η₃ : η₂ ≫ ηs₂ = η₃) (pf_η₄ : (α_ _ _ _).hom ≫ η₃ = η₄) (pf_η₅ : α ▷ k ≫ η₄ = η₅) :
    (α ≫ (f ◁ η) ≫ ηs) ▷ k = η₅ := by
  simp at pf_η₁
  simp [pf_η₁, pf_η₂, pf_ηs₁, pf_ηs₂, pf_η₃, pf_η₄, pf_η₅]

theorem evalWhiskerRight_comp (η : f ⟶ f') (g h : C) (η₁ : f ⊗ g ⟶ f' ⊗ g) (η₂ : (f ⊗ g) ⊗ h ⟶ (f' ⊗ g) ⊗ h)
    (η₃ : (f ⊗ g) ⊗ h ⟶ f' ⊗ (g ⊗ h)) (η₄ : f ⊗ (g ⊗ h) ⟶ f' ⊗ (g ⊗ h))
    (pf_η₁ : η ▷ g = η₁) (pf_η₂ : η₁ ▷ h = η₂) (pf_η₃ : η₂ ≫ (α_ _ _ _).hom = η₃) (pf_η₄ : (α_ _ _ _).inv ≫ η₃ = η₄) :
    η ▷ (g ⊗ h) = η₄ := by
  simp [pf_η₁, pf_η₂, pf_η₃, pf_η₄]

theorem evalWhiskerRight_id (η : f ⟶ g) (η₁ : f ⟶ g ⊗ 𝟙_ C) (η₂ : f ⊗ 𝟙_ C ⟶ g ⊗ 𝟙_ C)
    (pf_η₁ : η ≫ (ρ_ _).inv = η₁) (pf_η₂ : (ρ_ _).hom ≫ η₁ = η₂) :
    η ▷ 𝟙_ C = η₂ := by
  simp [pf_η₁, pf_η₂]

theorem eval_monoidalComp (η η' : f ⟶ g) (α : g ⟶ h) (θ θ' : h ⟶ i)
    (αθ : g ⟶ i) (ηαθ : f ⟶ i)
    (pf_η : η = η') (pf_θ : θ = θ') (pf_αθ : α ≫ θ' = αθ) (pf_ηαθ : η' ≫ αθ = ηαθ) :
    η ≫ α ≫ θ = ηαθ := by
  simp [pf_η, pf_θ, pf_αθ, pf_ηαθ]

end

/-- Evaluate the expression `η ≫ θ` into a normalized form. -/
partial def evalComp : NormalExpr → NormalExpr → M (NormalExpr × Expr)
  | .nil f g α, .cons β η ηs => do
    return (.cons (α.comp β) η ηs, ← mkAppM ``evalComp_nil_cons #[← α.e, ← β.e, ← η.e, ← ηs.e])
  | .nil f g α, .nil f' g' α' => do
    return (.nil f g' (α.comp α'), ← mkAppM ``evalComp_nil_nil #[← α.e, ← α'.e])
  -- | e, .nil _ _ (.id _) => do return (e, _)
  | .cons α η ηs, θ => do
    let (ι, pf_ι) ← evalComp ηs θ
    return (.cons α η ι, ← mkAppM ``evalComp_cons #[← α.e, ← η.e, ← ηs.e, ← θ.e, ← ι.e, pf_ι])

/-- Evaluate the expression `f ◁ η` into a normalized form. -/
partial def evalWhiskerLeftExpr : Mor₁ → NormalExpr → M (NormalExpr × Expr)
  | f, .nil g h α => do
    return (.nil (f.comp g) (f.comp h) (.whiskerLeft f α), ← mkAppM ``evalWhiskerLeft_nil #[← f.e, ← α.e])
  | .of f, .cons α η ηs => do
    let η' := WhiskerLeftExpr.whisker f η
    let (θ, pf_θ) ← evalWhiskerLeftExpr (.of f) ηs
    return (.cons (.whiskerLeft (.of f) α) η' θ, ← mkAppM ``evalWhiskerLeft_of_cons #[← α.e, ← η.e, ← ηs.e, ← θ.e, pf_θ])
  | .comp f g, η => do
    let (θ, pf_θ) ← evalWhiskerLeftExpr g η
    let (ι, pf_ι) ← evalWhiskerLeftExpr f θ
    let h ← η.src
    let h' ← η.tar
    let (ι', pf_ι') ← evalComp ι (NormalExpr.associatorInv f g h')
    let (ι'', pf_ι'') ← evalComp (NormalExpr.associator f g h) ι'
    return (ι'', ← mkAppM ``evalWhiskerLeft_comp #[← η.e, ← θ.e, ← ι.e, ← ι'.e, ← ι''.e, pf_θ, pf_ι, pf_ι', pf_ι''])
  | .id, η => do
    let f ← η.src
    let g ← η.tar
    let (η', pf_η') ← evalComp η (NormalExpr.leftUnitorInv g)
    let (η'', pf_η'') ← evalComp (NormalExpr.leftUnitor f) η'
    return (η'', ← mkAppM ``evalWhiskerLeft_id #[← η.e, ← η'.e, ← η''.e, pf_η', pf_η''])

/-- Evaluate the expression `η ▷ f` into a normalized form. -/
partial def evalWhiskerRightExpr : NormalExpr → Mor₁ → M (NormalExpr × Expr)
  | .nil f g α, h => do
    return (.nil (f.comp h) (g.comp h) (.whiskerRight α h), ← mkAppM ``evalWhiskerRight_nil #[← α.e, ← h.e])
    -- match α with
    -- | .id _ => return .nil (f.comp (.of h)) (g.comp (.of h)) (.whiskerRight α (.of h))
    -- | _ => return .nil (f.comp (.of h)) (g.comp (.of h)) (.whiskerRight α (.of h))
  | .cons α (.of η) ηs, .of f => do
    let (θ, pf_θ) ← evalWhiskerRightExpr ηs (.of f)
    return (.cons (.whiskerRight α (.of f)) (.of (.whisker η f)) θ,
      ← mkAppM ``evalWhiskerRight_cons_of_of #[← α.e, ← η.e, ← ηs.e, f.e, ← θ.e, pf_θ])
  | .cons α (.whisker f η) ηs, h => do
    let g ← η.src
    let g' ← η.tar
    let (η₁, pf_η₁) ← evalWhiskerRightExpr (.cons (.id g) η (.nil g' g' (.id g'))) h
    let (η₂, pf_η₂) ← evalWhiskerLeftExpr (.of f) η₁
    let (ηs₁, pf_ηs₁) ← evalWhiskerRightExpr ηs h
    let α' := .whiskerRight α h
    let (ηs₂, pf_ηs₂) ← evalComp (.associatorInv (.of f) g' h) ηs₁
    let (η₃, pf_η₃) ← evalComp η₂ ηs₂
    let (η₄, pf_η₄) ← evalComp (.associator (.of f) g h) η₃
    let (η₅, pf_η₅) ← evalComp (.nil α'.src α'.tar α') η₄
    return (η₅, ← mkAppM ``evalWhiskerRight_cons_whisker
      #[f.e, ← α.e, ← η.e, ← ηs.e, ← h.e, ← η₁.e, ← η₂.e, ← ηs₁.e, ← ηs₂.e, ← η₃.e, ← η₄.e, ← η₅.e,
        pf_η₁, pf_η₂, pf_ηs₁, pf_ηs₂, pf_η₃, pf_η₄, pf_η₅])
  | η, .comp g h => do
    let (η₁, pf_η₁) ← evalWhiskerRightExpr η g
    let (η₂, pf_η₂) ← evalWhiskerRightExpr η₁ h
    let f ← η.src
    let f' ← η.tar
    let (η₃, pf_η₃) ← evalComp η₂ (.associator f' g h)
    let (η₄, pf_η₄) ← evalComp (.associatorInv f g h) η₃
    return (η₄, ← mkAppM ``evalWhiskerRight_comp #[← η.e, ← g.e, ← h.e, ← η₁.e, ← η₂.e, ← η₃.e, ← η₄.e, pf_η₁, pf_η₂, pf_η₃, pf_η₄])
  | η, .id => do
    let f ← η.src
    let g ← η.tar
    let (η₁, pf_η₁) ← evalComp η (.rightUnitorInv g)
    let (η₂, pf_η₂) ← evalComp (.rightUnitor f) η₁
    return (η₂, ← mkAppM ``evalWhiskerRight_id #[← η.e, ← η₁.e, ← η₂.e, pf_η₁, pf_η₂])

/-- Evaluate the expression of a 2-morphism into a normalized form. -/
partial def eval (e : Expr) : M (NormalExpr × Expr) := do
  match e.getAppFnArgs with
  | (``CategoryStruct.id, #[_, _, f]) =>
    return (NormalExpr.nil (toMor₁ f) (toMor₁ f) (.id (toMor₁ f)), ← mkEqRefl (← mkAppM ``CategoryStruct.id #[f]))
  | (``CategoryStruct.comp, #[_, _, _, _, _, η, θ]) => do
    let (η_e, pf_η) ← eval η
    let (θ_e, pf_θ) ← eval θ
    let (ηθ, pf) ← evalComp η_e θ_e
    return (ηθ, ← mkAppM ``eval_comp #[η, ← η_e.e, θ, ← θ_e.e, ← ηθ.e, pf_η, pf_θ, pf])
  | (``Iso.hom, #[_, _, _, _, η]) => do
    match η.getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) => do
      let src := ((toMor₁ f).comp (toMor₁ g)).comp (toMor₁ h)
      let tar := (toMor₁ f).comp ((toMor₁ g).comp (toMor₁ h))
      let α := (.nil src tar (.atom <| .associator (toMor₁ f) (toMor₁ g) (toMor₁ h)))
      return (α , ← mkEqRefl (← α.e))
    | (``MonoidalCategoryStruct.leftUnitor, #[C, _, _, f]) => do
      let src := (Mor₁.id).comp (toMor₁ f)
      let tar := toMor₁ f
      let α := (.nil src tar (.atom <| .leftUnitor (toMor₁ f)))
      return (α, ← mkEqRefl (← α.e))
    | (``MonoidalCategoryStruct.rightUnitor, #[C, _, _, f]) => do
      let src := (toMor₁ f).comp (Mor₁.id)
      let tar := toMor₁ f
      let α := (.nil src tar (.atom <| .rightUnitor (toMor₁ f)))
      return (α, ← mkEqRefl (← α.e))
    | _ => return (← NormalExpr.of e, ← mkAppM ``eval_of #[e])
  | (``Iso.inv, #[_, _, _, _, η]) => do
    match η.getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) => do
      let src := (toMor₁ f).comp ((toMor₁ g).comp (toMor₁ h))
      let tar := ((toMor₁ f).comp (toMor₁ g)).comp (toMor₁ h)
      let α := (.nil src tar (.atom <| .associatorInv (toMor₁ f) (toMor₁ g) (toMor₁ h)))
      return (α, ← mkEqRefl (← α.e))
    | (``MonoidalCategoryStruct.leftUnitor, #[C, _, _, f]) => do
      let src := toMor₁ f
      let tar := (Mor₁.id).comp (toMor₁ f)
      let α := (.nil src tar (.atom <| .leftUnitorInv (toMor₁ f)))
      return (α, ← mkEqRefl (← α.e))
    | (``MonoidalCategoryStruct.rightUnitor, #[C, _, _, f]) => do
      let src := toMor₁ f
      let tar := (toMor₁ f).comp (Mor₁.id)
      let α := (.nil src tar (.atom <| .rightUnitorInv (toMor₁ f)))
      return (α, ← mkEqRefl (← α.e))
    | _ => return (← NormalExpr.of e, ← mkAppM ``eval_of #[e])
  | (``MonoidalCategoryStruct.whiskerLeft, #[_, _, _, f, _, _, η]) =>
    let (η_e, pf_η) ← eval η
    let (θ, pf_θ) ← evalWhiskerLeftExpr (toMor₁ f) η_e
    return (θ, ← mkAppM ``eval_whiskerLeft #[f, η, ← η_e.e, ← θ.e, pf_η, pf_θ])
  | (``MonoidalCategoryStruct.whiskerRight, #[_, _, _, _, _, η, h]) =>
    let (η_e, pf_η) ← eval η
    let (θ, pf_θ) ← evalWhiskerRightExpr η_e (toMor₁ h)
    return (θ, ← mkAppM ``eval_whiskerRight #[η, ← η_e.e, h, ← θ.e, pf_η, pf_θ])
  | (``monoidalComp, #[_, _, _, _, _, _, mα, η, θ]) => do
    let α₀ ← mkAppOptM ``MonoidalCoherence.hom #[none, none, none, none, mα]
    let (η_e, pf_η) ← eval η
    let α₀' ← structural? α₀
    -- | throwError "expected a structural 2-morphism, but got {← ppExpr α₀}"
    let α := NormalExpr.nil α₀'.src α₀'.tar α₀'
    -- let (α_e, pf_α) ← eval α
    let (θ_e, pf_θ) ← eval θ
    let (αθ, pf_θα) ← evalComp α θ_e
    let (ηαθ, pf_ηαθ) ← evalComp η_e αθ
    -- IO.println (← ppExpr <| ← ηαθ.e)
    return (ηαθ, ← mkAppM ``eval_monoidalComp
      #[η, ← η_e.e, ← α.e, θ, ← θ_e.e, ← αθ.e, ← ηαθ.e, pf_η, pf_θ, pf_θα, pf_ηαθ])
  | _ => return (← NormalExpr.of e, ← mkAppM ``eval_of #[e])

section

/-- Run a computation in the `AtomM` monad. -/
abbrev M.run {α : Type} (c : Context) (m : M α) : MetaM α :=
  ReaderT.run m c

open CategoryTheory
open scoped MonoidalCategory

elab "normalize% " t:term:51 : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  M.run (← mkContext e) do
    (← Mathlib.Tactic.Coherence.eval e).1.e

-- universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

example : normalize% (𝟙 (X ⊗ Y)) = 𝟙 (X ⊗ Y) := by
  sorry

example : normalize% (α_ X Y Z).hom = (α_ X Y Z).hom := by
  sorry

example : normalize% X ◁ (f ≫ g) = X ◁ f ≫ X ◁ g := by
  simp

example : normalize% X ◁ (f ≫ g) = normalize% X ◁ f ≫ X ◁ g := by
  congr
  simp

example : normalize% (X ⊗ Y) ◁ f = normalize% (α_ _ _ _).hom ≫ X ◁ Y ◁ f ≫ (α_ _ _ _).inv := by

  simp

example : normalize% f = f := by
  simp

example : (normalize% f ▷ (X ⊗ Y)) = (α_ _ _ _).inv ≫ f ▷ X ▷ Y ≫ (α_ _ _ _).hom := by
  simp

example : normalize% (X ◁ f) ▷ Y = normalize% (α_ _ _ _).hom ≫ X ◁ f ▷ Y ≫ (α_ _ _ _).inv := by
  congr 1 <;> simp

example : normalize% (X ◁ f) = X ◁ f := by
  simp

example : normalize% (X ◁ f) = X ◁ f := by
  simp

example : (((X ◁ f) ▷ Y) ▷ Z) = (α_ _ _ _).hom ≫ normalize% ((X ◁ f) ▷ (Y ⊗ Z)) ≫ (α_ _ _ _).inv := by
  sorry

example : normalize% (((X ◁ f) ▷ Y) ▷ Z) = (α_ _ _ _).hom ≫ normalize% ((X ◁ f) ▷ (Y ⊗ Z)) ≫ (α_ _ _ _).inv := by
  sorry

example : normalize% X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by simp
example : normalize% 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by simp
example : normalize% X ◁ (f ≫ g) = X ◁ f ≫ X ◁ g := by simp
example : normalize% (f ≫ g) ▷ Y = f ▷ Y ≫ g ▷ Y := by simp
example : normalize% 𝟙_ C ◁ f = (λ_ _).hom ≫ f ≫ (λ_ _).inv := by simp
example : normalize% (X ⊗ Y) ◁ f = (α_ _ _ _).hom ≫ X ◁ Y ◁ f ≫ (α_ _ _ _).inv := by simp
example : normalize% f ▷ 𝟙_ C = (ρ_ _).hom ≫ f ≫ (ρ_ _).inv := by simp
example : normalize% f ▷ (X ⊗ Y) = (α_ _ _ _).inv ≫ f ▷ X ▷ Y ≫ (α_ _ _ _).hom := by simp
example : normalize% (X ◁ f) ▷ Y = (α_ _ _ _).hom ≫ X ◁ f ▷ Y ≫ (α_ _ _ _).inv := by simp
example : normalize% (λ_ X).hom = (λ_ X).hom := by simp
example : normalize% (λ_ X).inv = (λ_ X).inv := by simp
example : normalize% (ρ_ X).hom = (ρ_ X).hom := by simp
example : normalize% (ρ_ X).inv = (ρ_ X).inv := by simp
example : normalize% (α_ X Y Z).hom = (α_ _ _ _).hom := by simp
example : normalize% (α_ X Y Z).inv = (α_ _ _ _).inv := by simp
example : normalize% 𝟙 (X ⊗ Y) = 𝟙 (X ⊗ Y) := by simp

-- #guard_expr (normalize% 𝟙 X ▷ Y) = 𝟙 (X ⊗ Y)
-- #guard_expr (normalize% (X ◁ (f ≫ g))) = X ◁ f ≫ X ◁ g
-- #guard_expr (normalize% ((f ≫ g) ▷ Y)) = f ▷ Y ≫ g ▷ Y
-- #guard_expr (normalize% 𝟙_ C ◁ f) = (λ_ _).hom ≫ f ≫ (λ_ _).inv
-- #guard_expr (normalize% (X ⊗ Y) ◁ f) = (α_ _ _ _).hom ≫ X ◁ Y ◁ f ≫ (α_ _ _ _).inv
-- #guard_expr (normalize% (f ▷ 𝟙_ C)) = (ρ_ _).hom ≫ f ≫ (ρ_ _).inv
-- #guard_expr (normalize% f ▷ (X ⊗ Y)) = (α_ _ _ _).inv ≫ f ▷ X ▷ Y ≫ (α_ _ _ _).hom
-- #guard_expr (normalize% ((X ◁ f) ▷ Y)) = (α_ _ _ _).hom ≫ X ◁ f ▷ Y ≫ (α_ _ _ _).inv
-- #guard_expr (normalize% (λ_ X).hom) = (λ_ X).hom
-- #guard_expr (normalize% (λ_ X).inv) = (λ_ X).inv
-- #guard_expr (normalize% (ρ_ X).hom) = (ρ_ X).hom
-- #guard_expr (normalize% (ρ_ X).inv) = (ρ_ X).inv
-- #guard_expr (normalize% (α_ X Y Z).hom) = (α_ _ _ _).hom
-- #guard_expr (normalize% (α_ X Y Z).inv) = (α_ _ _ _).inv
-- #guard_expr (normalize% (𝟙 (X ⊗ Y))) = 𝟙 (X ⊗ Y)

open MonoidalCategory

example (X X₁ X₂ : C) (η : X ⟶ X₁ ⊗ X₂) :
  normalize%
  η ⊗≫
    (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫
    𝟙_ C ◁ ((α_ (𝟙_ C) X₁ X₂).inv ≫
      ((λ_ X₁).hom ≫ (ρ_ X₁).inv) ▷ X₂ ≫
        (α_ X₁ (𝟙_ C) X₂).hom) ≫
          (α_ (𝟙_ C) X₁ (𝟙_ C ⊗ X₂)).inv ≫
            ((λ_ X₁).hom ≫ (ρ_ X₁).inv) ▷ (𝟙_ C ⊗ X₂) ≫
              (α_ X₁ (𝟙_ C) (𝟙_ C ⊗ X₂)).hom ≫
                X₁ ◁ 𝟙_ C ◁ ((λ_ X₂).hom ≫ (ρ_ X₂).inv) ≫
                  X₁ ◁ (α_ (𝟙_ C) X₂ (𝟙_ C)).inv ≫
                    X₁ ◁ ((λ_ X₂).hom ≫ (ρ_ X₂).inv) ▷ 𝟙_ C ≫
                      X₁ ◁ (α_ X₂ (𝟙_ C) (𝟙_ C)).hom ≫ (α_ X₁ X₂ (𝟙_ C ⊗ 𝟙_ C)).inv  =
  normalize%
    η ⊗≫ 𝟙 ((X₁ ⊗ X₂) ⊗ 𝟙_ C ⊗ 𝟙_ C) := by
  sorry
  -- coherence

end

syntax (name := monoidal) "monoidal" : tactic

initialize registerTraceClass `monoidal

theorem mk_eq {α : Type _} (a b a' b' : α) (ha : a = a') (hb : b = b') (h : a' = b') : a = b := by
  simp [h, ha, hb]

open Lean Elab Meta Tactic in

def mkEq (e : Expr) : MetaM Expr := do
  let some (_, e₁, e₂) := (← whnfR <| e).eq?
    | throwError "monoidal requires an equality goal"
  M.run (← mkContext e₁) do
    let (e₁', p₁) ← eval e₁
    trace[monoidal] "found `{p₁}`, a proof that `{e₁} = {← e₁'.e}`"
    let (e₂', p₂) ← eval e₂
    trace[monoidal] "found `{p₂}`, a proof that `{e₂} = {← e₂'.e}`"
    mkAppM ``mk_eq #[e₁, e₂, ← e₁'.e, ← e₂'.e, p₁, p₂]

open Lean Elab Meta Tactic in

elab_rules : tactic | `(tactic| monoidal) => withMainContext do
  let t ← getMainTarget
  let mvarIds ← (← getMainGoal).apply (← mkEq t)
  replaceMainGoal (mvarIds)

end

/--
Internal tactic used in `coherence`.

Rewrites an equation `f = g` as `f₀ ≫ f₁ = g₀ ≫ g₁`,
where `f₀` and `g₀` are maximal prefixes of `f` and `g` (possibly after reassociating)
which are "liftable" (i.e. expressible as compositions of unitors and associators).
-/
elab (name := liftable_prefixes) "liftable_prefixes" : tactic => do
  withMainContext do
    let t ← getMainTarget
    let mvarIds ← (← getMainGoal).apply (← mkEq t)
    replaceMainGoal (mvarIds)
  -- withOptions (fun opts => synthInstance.maxSize.set opts
  --   (max 256 (synthInstance.maxSize.get opts))) do
  -- evalTactic (← `(tactic|
  --   (simp (config := {failIfUnchanged := false}) only
  --     [monoidalComp, Category.assoc, MonoidalCoherence.hom]) <;>
  --   (apply (cancel_epi (𝟙 _)).1 <;> try infer_instance) <;>
  --   (simp (config := {failIfUnchanged := false}) only
  --     [assoc_liftHom, Mathlib.Tactic.BicategoryCoherence.assoc_liftHom₂])))

lemma insert_id_lhs {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y) (w : f ≫ 𝟙 _ = g) :
    f = g := by
  simpa using w

lemma insert_id_rhs {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y) (w : f = g ≫ 𝟙 _) :
    f = g := by
  simpa using w

/-- If either the lhs or rhs is not a composition, compose it on the right with an identity. -/
def insertTrailingIds (g : MVarId) : MetaM MVarId := do
  let some (_, lhs, rhs) := (← withReducible g.getType').eq? | exception g "Not an equality."
  let mut g := g
  if !(lhs.isAppOf ``CategoryStruct.comp) then
    let [g'] ← g.applyConst ``insert_id_lhs | exception g "failed to apply insert_id_lhs"
    g := g'
  if !(rhs.isAppOf ``CategoryStruct.comp) then
    let [g'] ← g.applyConst ``insert_id_rhs | exception g "failed to apply insert_id_rhs"
    g := g'
  return g

/-- The main part of `coherence` tactic. -/
-- Porting note: this is an ugly port, using too many `evalTactic`s.
-- We can refactor later into either a `macro` (but the flow control is awkward)
-- or a `MetaM` tactic.
def coherence_loop (maxSteps := 37) : TacticM Unit :=
  match maxSteps with
  | 0 => exception' "`coherence` tactic reached iteration limit"
  | maxSteps' + 1 => do
    -- To prove an equality `f = g` in a monoidal category,
    -- first try the `pure_coherence` tactic on the entire equation:
    evalTactic (← `(tactic| pure_coherence)) <|> do
    -- Otherwise, rearrange so we have a maximal prefix of each side
    -- that is built out of unitors and associators:
    evalTactic (← `(tactic| liftable_prefixes)) <|>
      exception' "Something went wrong in the `coherence` tactic: \
        is the target an equation in a monoidal category?"
    -- The goal should now look like `f₀ ≫ f₁ = g₀ ≫ g₁`,
    liftMetaTactic MVarId.congrCore
    -- and now we have two goals `f₀ = g₀` and `f₁ = g₁`.
    -- Discharge the first using `coherence`,
    evalTactic (← `(tactic| { pure_coherence })) <|>
      exception' "`coherence` tactic failed, subgoal not true in the free monoidal category"
    -- Then check that either `g₀` is identically `g₁`,
    evalTactic (← `(tactic| rfl)) <|> do
      -- or that both are compositions,
      liftMetaTactic' insertTrailingIds
      liftMetaTactic MVarId.congrCore
      -- with identical first terms,
      evalTactic (← `(tactic| rfl)) <|>
        exception' "`coherence` tactic failed, non-structural morphisms don't match"
      -- and whose second terms can be identified by recursively called `coherence`.
      coherence_loop maxSteps'

open Lean.Parser.Tactic

/--
Simp lemmas for rewriting a hom in monoical categories into a normal form.
-/
syntax (name := monoidal_simps) "monoidal_simps" (config)? : tactic

@[inherit_doc monoidal_simps]
elab_rules : tactic
| `(tactic| monoidal_simps $[$cfg]?) => do
  evalTactic (← `(tactic|
    simp $[$cfg]? only [
      Category.assoc, MonoidalCategory.tensor_whiskerLeft, MonoidalCategory.id_whiskerLeft,
      MonoidalCategory.whiskerRight_tensor, MonoidalCategory.whiskerRight_id,
      MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_id,
      MonoidalCategory.comp_whiskerRight, MonoidalCategory.id_whiskerRight,
      MonoidalCategory.whisker_assoc,
      MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id];
    -- I'm not sure if `tensorHom` should be expanded.
    try simp only [MonoidalCategory.tensorHom_def]
    ))

/--
Use the coherence theorem for monoidal categories to solve equations in a monoidal equation,
where the two sides only differ by replacing strings of monoidal structural morphisms
(that is, associators, unitors, and identities)
with different strings of structural morphisms with the same source and target.

That is, `coherence` can handle goals of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `pure_coherence`.

(If you have very large equations on which `coherence` is unexpectedly failing,
you may need to increase the typeclass search depth,
using e.g. `set_option synthInstance.maxSize 500`.)
-/
syntax (name := coherence) "coherence" : tactic

@[inherit_doc coherence]
elab_rules : tactic
| `(tactic| coherence) => do
  evalTactic (← `(tactic|
    (simp (config := {failIfUnchanged := false}) only [bicategoricalComp,
      Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom,
      Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom',
      monoidalComp]);
    whisker_simps (config := {failIfUnchanged := false});
    monoidal_simps (config := {failIfUnchanged := false})))
  coherence_loop

example {U V W X Y : C} (f : U ⟶ V ⊗ (W ⊗ X)) (g : (V ⊗ W) ⊗ X ⟶ Y) :
    f ⊗≫ g = f ≫ (α_ _ _ _).inv ≫ g := by
  -- dsimp only [monoidalComp]
  -- dsimp only [MonoidalCoherence.assoc'_hom, MonoidalCoherence.whiskerRight_hom,
  --   MonoidalCoherence.refl_hom]
  liftable_prefixes
  apply
    congrArg₂ (· ≫ ·) (by sorry) <| congrArg₂ (· ≫ ·) rfl <|
    congrArg₂ (· ≫ ·) (by sorry) <| congrArg₂ (· ≫ ·) rfl
    (by sorry)


variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)

example : normalize% (X ⊗ Y) ◁ f = sorry := by
  sorry

#check normalize% (f ≫ g) ▷ Y

#check normalize% (f ≫ g)

#check normalize% f ⊗ g

#guard_expr normalize% X ◁ 𝟙 Y = X ◁ 𝟙 Y
#guard_expr normalize% 𝟙 X ▷ Y = 𝟙 X ▷ Y
#guard_expr normalize% X ◁ (f ≫ g) = _ ≫ X ◁ f ≫ _ ≫ X ◁ g ≫ _
#guard_expr normalize% (f ≫ g) ▷ Y = _ ≫ f ▷ Y ≫ _ ≫ g ▷ Y ≫ _
#guard_expr normalize% 𝟙_ C ◁ f = _ ≫ f ≫ _
#guard_expr normalize% (X ⊗ Y) ◁ f = _ ≫ X ◁ Y ◁ f ≫ _
#guard_expr normalize% f ▷ 𝟙_ C = _ ≫ f ≫ _
#guard_expr normalize% f ▷ (X ⊗ Y) = _ ≫ f ▷ X ▷ Y ≫ _
#guard_expr normalize% (X ◁ f) ▷ Y = _ ≫ X ◁ f ▷ Y ≫ _
#guard_expr normalize% (λ_ X).hom = (λ_ X).hom
#guard_expr normalize% (λ_ X).inv = (λ_ X).inv
#guard_expr normalize% (ρ_ X).hom = (ρ_ X).hom
#guard_expr normalize% (ρ_ X).inv = (ρ_ X).inv
#guard_expr normalize% (α_ X Y Z).hom = (α_ _ _ _).hom
#guard_expr normalize% (α_ X Y Z).inv = (α_ _ _ _).inv
#guard_expr normalize% 𝟙 (X ⊗ Y) = 𝟙 (X ⊗ Y)
#guard_expr normalize% f ⊗ g = _ ≫ (f ⊗ g) ≫ _
variable {V₁ V₂ V₃ : C} (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁) in
#guard_expr normalize% R V₁ V₂ ▷ V₃ ⊗≫ V₂ ◁ R V₁ V₃ = _ ≫ R V₁ V₂ ▷ V₃ ≫ _ ≫ V₂ ◁ R V₁ V₃ ≫ _
