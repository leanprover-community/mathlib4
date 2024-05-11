/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Free

#align_import category_theory.bicategory.coherence_tactic from "leanprover-community/mathlib"@"3d7987cda72abc473c7cdbbb075170e9ac620042"

/-!
# A `coherence` tactic for bicategories, and `⊗≫` (composition up to associators)

We provide a `bicategory_coherence` tactic,
which proves that any two 2-morphisms (with the same source and target)
in a bicategory which are built out of associators and unitors
are equal.

We also provide `f ⊗≫ g`, the `bicategoricalComp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.

This file mainly deals with the type class setup for the coherence tactic. The actual front end
tactic is given in `Mathlib.Tactic.CategoryTheory.Coherence` at the same time as the coherence
tactic for monoidal categories.
-/

set_option autoImplicit true


noncomputable section

universe w v u

open CategoryTheory CategoryTheory.FreeBicategory

open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B] {a b c d e : B}

namespace Mathlib.Tactic.BicategoryCoherence

/-- A typeclass carrying a choice of lift of a 1-morphism from `B` to `FreeBicategory B`. -/
class LiftHom {a b : B} (f : a ⟶ b) where
  /-- A lift of a morphism to the free bicategory.
  This should only exist for "structural" morphisms. -/
  lift : of.obj a ⟶ of.obj b
#align category_theory.bicategory.lift_hom Mathlib.Tactic.BicategoryCoherence.LiftHom

instance liftHomId : LiftHom (𝟙 a) where lift := 𝟙 (of.obj a)
#align category_theory.bicategory.lift_hom_id Mathlib.Tactic.BicategoryCoherence.liftHomId

instance liftHomComp (f : a ⟶ b) (g : b ⟶ c) [LiftHom f] [LiftHom g] : LiftHom (f ≫ g) where
  lift := LiftHom.lift f ≫ LiftHom.lift g
#align category_theory.bicategory.lift_hom_comp Mathlib.Tactic.BicategoryCoherence.liftHomComp

instance (priority := 100) liftHomOf (f : a ⟶ b) : LiftHom f where lift := of.map f
#align category_theory.bicategory.lift_hom_of Mathlib.Tactic.BicategoryCoherence.liftHomOf

/-- A typeclass carrying a choice of lift of a 2-morphism from `B` to `FreeBicategory B`. -/
class LiftHom₂ {f g : a ⟶ b} [LiftHom f] [LiftHom g] (η : f ⟶ g) where
  /-- A lift of a 2-morphism to the free bicategory.
  This should only exist for "structural" 2-morphisms. -/
  lift : LiftHom.lift f ⟶ LiftHom.lift g
#align category_theory.bicategory.lift_hom₂ Mathlib.Tactic.BicategoryCoherence.LiftHom₂

instance liftHom₂Id (f : a ⟶ b) [LiftHom f] : LiftHom₂ (𝟙 f) where
  lift := 𝟙 _
#align category_theory.bicategory.lift_hom₂_id Mathlib.Tactic.BicategoryCoherence.liftHom₂Id

instance liftHom₂LeftUnitorHom (f : a ⟶ b) [LiftHom f] : LiftHom₂ (λ_ f).hom where
  lift := (λ_ (LiftHom.lift f)).hom
#align category_theory.bicategory.lift_hom₂_left_unitor_hom Mathlib.Tactic.BicategoryCoherence.liftHom₂LeftUnitorHom

instance liftHom₂LeftUnitorInv (f : a ⟶ b) [LiftHom f] : LiftHom₂ (λ_ f).inv where
  lift := (λ_ (LiftHom.lift f)).inv
#align category_theory.bicategory.lift_hom₂_left_unitor_inv Mathlib.Tactic.BicategoryCoherence.liftHom₂LeftUnitorInv

instance liftHom₂RightUnitorHom (f : a ⟶ b) [LiftHom f] : LiftHom₂ (ρ_ f).hom where
  lift := (ρ_ (LiftHom.lift f)).hom
#align category_theory.bicategory.lift_hom₂_right_unitor_hom Mathlib.Tactic.BicategoryCoherence.liftHom₂RightUnitorHom

instance liftHom₂RightUnitorInv (f : a ⟶ b) [LiftHom f] : LiftHom₂ (ρ_ f).inv where
  lift := (ρ_ (LiftHom.lift f)).inv
#align category_theory.bicategory.lift_hom₂_right_unitor_inv Mathlib.Tactic.BicategoryCoherence.liftHom₂RightUnitorInv

instance liftHom₂AssociatorHom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) [LiftHom f] [LiftHom g]
    [LiftHom h] : LiftHom₂ (α_ f g h).hom where
  lift := (α_ (LiftHom.lift f) (LiftHom.lift g) (LiftHom.lift h)).hom
#align category_theory.bicategory.lift_hom₂_associator_hom Mathlib.Tactic.BicategoryCoherence.liftHom₂AssociatorHom

instance liftHom₂AssociatorInv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) [LiftHom f] [LiftHom g]
    [LiftHom h] : LiftHom₂ (α_ f g h).inv where
  lift := (α_ (LiftHom.lift f) (LiftHom.lift g) (LiftHom.lift h)).inv
#align category_theory.bicategory.lift_hom₂_associator_inv Mathlib.Tactic.BicategoryCoherence.liftHom₂AssociatorInv

instance liftHom₂Comp {f g h : a ⟶ b} [LiftHom f] [LiftHom g] [LiftHom h] (η : f ⟶ g) (θ : g ⟶ h)
    [LiftHom₂ η] [LiftHom₂ θ] : LiftHom₂ (η ≫ θ) where
  lift := LiftHom₂.lift η ≫ LiftHom₂.lift θ
#align category_theory.bicategory.lift_hom₂_comp Mathlib.Tactic.BicategoryCoherence.liftHom₂Comp

instance liftHom₂WhiskerLeft (f : a ⟶ b) [LiftHom f] {g h : b ⟶ c} (η : g ⟶ h) [LiftHom g]
    [LiftHom h] [LiftHom₂ η] : LiftHom₂ (f ◁ η) where
  lift := LiftHom.lift f ◁ LiftHom₂.lift η
#align category_theory.bicategory.lift_hom₂_whisker_left Mathlib.Tactic.BicategoryCoherence.liftHom₂WhiskerLeft

instance liftHom₂WhiskerRight {f g : a ⟶ b} (η : f ⟶ g) [LiftHom f] [LiftHom g] [LiftHom₂ η]
    {h : b ⟶ c} [LiftHom h] : LiftHom₂ (η ▷ h) where
  lift := LiftHom₂.lift η ▷ LiftHom.lift h
#align category_theory.bicategory.lift_hom₂_whisker_right Mathlib.Tactic.BicategoryCoherence.liftHom₂WhiskerRight

/-- A typeclass carrying a choice of bicategorical structural isomorphism between two objects.
Used by the `⊗≫` bicategorical composition operator, and the `coherence` tactic.
-/
class BicategoricalCoherence (f g : a ⟶ b) [LiftHom f] [LiftHom g] where
  /-- The chosen structural isomorphism between to 1-morphisms. -/
  hom' : f ⟶ g
  [isIso : IsIso hom']
#align category_theory.bicategory.bicategorical_coherence Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence


namespace BicategoricalCoherence

attribute [instance] isIso

-- Porting note: the field `BicategoricalCoherence.hom'` was named `hom` in mathlib3, but in Lean4
-- `f` and `g` are not explicit parameters, so that we have to redefine `hom` as follows
/-- The chosen structural isomorphism between to 1-morphisms. -/
abbrev hom (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] : f ⟶ g := hom'

attribute [simp] hom hom'

@[simps]
instance refl (f : a ⟶ b) [LiftHom f] : BicategoricalCoherence f f :=
  ⟨𝟙 _⟩
#align category_theory.bicategory.bicategorical_coherence.refl Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.refl

@[simps]
instance whiskerLeft (f : a ⟶ b) (g h : b ⟶ c) [LiftHom f] [LiftHom g] [LiftHom h]
    [BicategoricalCoherence g h] : BicategoricalCoherence (f ≫ g) (f ≫ h) :=
  ⟨f ◁ BicategoricalCoherence.hom g h⟩
#align category_theory.bicategory.bicategorical_coherence.whisker_left Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.whiskerLeft

@[simps]
instance whiskerRight (f g : a ⟶ b) (h : b ⟶ c) [LiftHom f] [LiftHom g] [LiftHom h]
    [BicategoricalCoherence f g] : BicategoricalCoherence (f ≫ h) (g ≫ h) :=
  ⟨BicategoricalCoherence.hom f g ▷ h⟩
#align category_theory.bicategory.bicategorical_coherence.whisker_right Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.whiskerRight

@[simps]
instance tensorRight (f : a ⟶ b) (g : b ⟶ b) [LiftHom f] [LiftHom g]
    [BicategoricalCoherence (𝟙 b) g] : BicategoricalCoherence f (f ≫ g) :=
  ⟨(ρ_ f).inv ≫ f ◁ BicategoricalCoherence.hom (𝟙 b) g⟩
#align category_theory.bicategory.bicategorical_coherence.tensor_right Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.tensorRight

@[simps]
instance tensorRight' (f : a ⟶ b) (g : b ⟶ b) [LiftHom f] [LiftHom g]
    [BicategoricalCoherence g (𝟙 b)] : BicategoricalCoherence (f ≫ g) f :=
  ⟨f ◁ BicategoricalCoherence.hom g (𝟙 b) ≫ (ρ_ f).hom⟩
#align category_theory.bicategory.bicategorical_coherence.tensor_right' Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.tensorRight'

@[simps]
instance left (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] :
    BicategoricalCoherence (𝟙 a ≫ f) g :=
  ⟨(λ_ f).hom ≫ BicategoricalCoherence.hom f g⟩
#align category_theory.bicategory.bicategorical_coherence.left Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.left

@[simps]
instance left' (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] :
    BicategoricalCoherence f (𝟙 a ≫ g) :=
  ⟨BicategoricalCoherence.hom f g ≫ (λ_ g).inv⟩
#align category_theory.bicategory.bicategorical_coherence.left' Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.left'

@[simps]
instance right (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] :
    BicategoricalCoherence (f ≫ 𝟙 b) g :=
  ⟨(ρ_ f).hom ≫ BicategoricalCoherence.hom f g⟩
#align category_theory.bicategory.bicategorical_coherence.right Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.right

@[simps]
instance right' (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] :
    BicategoricalCoherence f (g ≫ 𝟙 b) :=
  ⟨BicategoricalCoherence.hom f g ≫ (ρ_ g).inv⟩
#align category_theory.bicategory.bicategorical_coherence.right' Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.right'

@[simps]
instance assoc (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d) [LiftHom f] [LiftHom g] [LiftHom h]
    [LiftHom i] [BicategoricalCoherence (f ≫ g ≫ h) i] :
    BicategoricalCoherence ((f ≫ g) ≫ h) i :=
  ⟨(α_ f g h).hom ≫ BicategoricalCoherence.hom (f ≫ g ≫ h) i⟩
#align category_theory.bicategory.bicategorical_coherence.assoc Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.assoc

@[simps]
instance assoc' (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d) [LiftHom f] [LiftHom g] [LiftHom h]
    [LiftHom i] [BicategoricalCoherence i (f ≫ g ≫ h)] :
    BicategoricalCoherence i ((f ≫ g) ≫ h) :=
  ⟨BicategoricalCoherence.hom i (f ≫ g ≫ h) ≫ (α_ f g h).inv⟩
#align category_theory.bicategory.bicategorical_coherence.assoc' Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.assoc'

end BicategoricalCoherence

/-- Construct an isomorphism between two objects in a bicategorical category
out of unitors and associators. -/
def bicategoricalIso (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] : f ≅ g :=
  asIso (BicategoricalCoherence.hom f g)
#align category_theory.bicategory.bicategorical_iso Mathlib.Tactic.BicategoryCoherence.bicategoricalIso

/-- Compose two morphisms in a bicategorical category,
inserting unitors and associators between as necessary. -/
def bicategoricalComp {f g h i : a ⟶ b} [LiftHom g] [LiftHom h] [BicategoricalCoherence g h]
    (η : f ⟶ g) (θ : h ⟶ i) : f ⟶ i :=
  η ≫ BicategoricalCoherence.hom g h ≫ θ
#align category_theory.bicategory.bicategorical_comp Mathlib.Tactic.BicategoryCoherence.bicategoricalComp

-- type as \ot \gg
@[inherit_doc Mathlib.Tactic.BicategoryCoherence.bicategoricalComp]
scoped[CategoryTheory.Bicategory] infixr:80 " ⊗≫ " =>
  Mathlib.Tactic.BicategoryCoherence.bicategoricalComp

/-- Compose two isomorphisms in a bicategorical category,
inserting unitors and associators between as necessary. -/
def bicategoricalIsoComp {f g h i : a ⟶ b} [LiftHom g] [LiftHom h] [BicategoricalCoherence g h]
    (η : f ≅ g) (θ : h ≅ i) : f ≅ i :=
  η ≪≫ asIso (BicategoricalCoherence.hom g h) ≪≫ θ
#align category_theory.bicategory.bicategorical_iso_comp Mathlib.Tactic.BicategoryCoherence.bicategoricalIsoComp

-- type as \ll \ot \gg
@[inherit_doc Mathlib.Tactic.BicategoryCoherence.bicategoricalIsoComp]
scoped[CategoryTheory.Bicategory] infixr:80 " ≪⊗≫ " =>
  Mathlib.Tactic.BicategoryCoherence.bicategoricalIsoComp

example {f' : a ⟶ d} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {h' : a ⟶ d} (η : f' ⟶ f ≫ g ≫ h)
    (θ : (f ≫ g) ≫ h ⟶ h') : f' ⟶ h' :=
    η ⊗≫ θ

-- To automatically insert unitors/associators at the beginning or end,
-- you can use `η ⊗≫ 𝟙 _`
example {f' : a ⟶ d} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} (η : f' ⟶ (f ≫ g) ≫ h) :
    f' ⟶ f ≫ g ≫ h :=
  η ⊗≫ 𝟙 _

@[simp]
theorem bicategoricalComp_refl {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) : η ⊗≫ θ = η ≫ θ := by
  dsimp [bicategoricalComp]; simp
#align category_theory.bicategory.bicategorical_comp_refl Mathlib.Tactic.BicategoryCoherence.bicategoricalComp_refl

open Lean Elab Tactic Meta

/-- Helper function for throwing exceptions. -/
def exception (g : MVarId) (msg : MessageData) : MetaM α :=
  throwTacticEx `bicategorical_coherence g msg

/-- Helper function for throwing exceptions with respect to the main goal. -/
def exception' (msg : MessageData) : TacticM Unit := do
  try
    liftMetaTactic (exception (msg := msg))
  catch _ =>
    -- There might not be any goals
    throwError msg

set_option quotPrecheck false in
/-- Auxiliary definition for `bicategorical_coherence`. -/
-- We could construct this expression directly without using `elabTerm`,
-- but it would require preparing many implicit arguments by hand.
def mkLiftMap₂LiftExpr (e : Expr) : TermElabM Expr := do
  Term.elabTerm
    (← ``((FreeBicategory.lift (Prefunctor.id _)).map₂ (LiftHom₂.lift $(← Term.exprToSyntax e))))
    none

/-- Coherence tactic for bicategories. -/
def bicategory_coherence (g : MVarId) : TermElabM Unit := g.withContext do
  withOptions (fun opts => synthInstance.maxSize.set opts
    (max 256 (synthInstance.maxSize.get opts))) do
  -- TODO: is this `dsimp only` step necessary? It doesn't appear to be in the tests below.
  let (ty, _) ← dsimp (← g.getType) (← Simp.Context.ofNames [] true)
  let some (_, lhs, rhs) := (← whnfR ty).eq? | exception g "Not an equation of morphisms."
  let lift_lhs ← mkLiftMap₂LiftExpr lhs
  let lift_rhs ← mkLiftMap₂LiftExpr rhs
  -- This new equation is defeq to the original by assumption
  -- on the `LiftHom` instances.
  let g₁ ← g.change (← mkEq lift_lhs lift_rhs)
  let [g₂] ← g₁.applyConst ``congrArg
    | exception g "congrArg failed in coherence"
  let [] ← g₂.applyConst ``Subsingleton.elim
    | exception g "This shouldn't happen; Subsingleton.elim does not create goals."

/-- Coherence tactic for bicategories.
Use `pure_coherence` instead, which is a frontend to this one. -/
elab "bicategory_coherence" : tactic => do bicategory_coherence (← getMainGoal)

open Lean.Parser.Tactic

/--
Simp lemmas for rewriting a 2-morphism into a normal form.
-/
syntax (name := whisker_simps) "whisker_simps" (config)? : tactic

@[inherit_doc whisker_simps]
elab_rules : tactic
| `(tactic| whisker_simps $[$cfg]?) => do
  evalTactic (← `(tactic|
    simp $[$cfg]? only [Category.assoc,
      Bicategory.comp_whiskerLeft, Bicategory.id_whiskerLeft,
      Bicategory.whiskerRight_comp, Bicategory.whiskerRight_id,
      Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_id,
      Bicategory.comp_whiskerRight, Bicategory.id_whiskerRight, Bicategory.whisker_assoc]
    ))

-- We have unused typeclass arguments here.
-- They are intentional, to ensure that `simp only [assoc_liftHom₂]` only left associates
-- bicategorical structural morphisms.
/-- Auxiliary simp lemma for the `coherence` tactic:
this move brackets to the left in order to expose a maximal prefix
built out of unitors and associators.
-/
@[nolint unusedArguments]
theorem assoc_liftHom₂ {f g h i : a ⟶ b} [LiftHom f] [LiftHom g] [LiftHom h]
    (η : f ⟶ g) (θ : g ⟶ h) (ι : h ⟶ i) [LiftHom₂ η] [LiftHom₂ θ] : η ≫ θ ≫ ι = (η ≫ θ) ≫ ι :=
  (Category.assoc _ _ _).symm
#align tactic.bicategory.coherence.assoc_lift_hom₂ Mathlib.Tactic.BicategoryCoherence.assoc_liftHom₂
