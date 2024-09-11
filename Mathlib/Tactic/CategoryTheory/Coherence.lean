/-
Copyright (c) 2022. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yuma Mizuno, Oleksandr Manzyuk
-/
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Lean.Meta
import Mathlib.Tactic.CategoryTheory.BicategoryCoherence
import Mathlib.Tactic.CategoryTheory.MonoidalComp

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

universe v u

open CategoryTheory FreeMonoidalCategory

-- As the lemmas and typeclasses in this file are not intended for use outside of the tactic,
-- we put everything inside a namespace.
namespace Mathlib.Tactic.Coherence

variable {C : Type u} [Category.{v} C]
open scoped MonoidalCategory

noncomputable section lifting

variable [MonoidalCategory C]

/-- A typeclass carrying a choice of lift of an object from `C` to `FreeMonoidalCategory C`.
It must be the case that `projectObj id (LiftObj.lift x) = x` by defeq. -/
class LiftObj (X : C) where
  protected lift : FreeMonoidalCategory C

instance LiftObj_unit : LiftObj (𝟙_ C) := ⟨unit⟩

instance LiftObj_tensor (X Y : C) [LiftObj X] [LiftObj Y] : LiftObj (X ⊗ Y) where
  lift := LiftObj.lift X ⊗ LiftObj.lift Y

instance (priority := 100) LiftObj_of (X : C) : LiftObj X := ⟨of X⟩

/-- A typeclass carrying a choice of lift of a morphism from `C` to `FreeMonoidalCategory C`.
It must be the case that `projectMap id _ _ (LiftHom.lift f) = f` by defeq. -/
class LiftHom {X Y : C} [LiftObj X] [LiftObj Y] (f : X ⟶ Y) where
  protected lift : LiftObj.lift X ⟶ LiftObj.lift Y

instance LiftHom_id (X : C) [LiftObj X] : LiftHom (𝟙 X) := ⟨𝟙 _⟩

instance LiftHom_left_unitor_hom (X : C) [LiftObj X] : LiftHom (λ_ X).hom where
  lift := (λ_ (LiftObj.lift X)).hom

instance LiftHom_left_unitor_inv (X : C) [LiftObj X] : LiftHom (λ_ X).inv where
  lift := (λ_ (LiftObj.lift X)).inv

instance LiftHom_right_unitor_hom (X : C) [LiftObj X] : LiftHom (ρ_ X).hom where
  lift := (ρ_ (LiftObj.lift X)).hom

instance LiftHom_right_unitor_inv (X : C) [LiftObj X] : LiftHom (ρ_ X).inv where
  lift := (ρ_ (LiftObj.lift X)).inv

instance LiftHom_associator_hom (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] :
    LiftHom (α_ X Y Z).hom where
  lift := (α_ (LiftObj.lift X) (LiftObj.lift Y) (LiftObj.lift Z)).hom

instance LiftHom_associator_inv (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] :
    LiftHom (α_ X Y Z).inv where
  lift := (α_ (LiftObj.lift X) (LiftObj.lift Y) (LiftObj.lift Z)).inv

instance LiftHom_comp {X Y Z : C} [LiftObj X] [LiftObj Y] [LiftObj Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    [LiftHom f] [LiftHom g] : LiftHom (f ≫ g) where
  lift := LiftHom.lift f ≫ LiftHom.lift g

instance liftHom_WhiskerLeft (X : C) [LiftObj X] {Y Z : C} [LiftObj Y] [LiftObj Z]
    (f : Y ⟶ Z) [LiftHom f] : LiftHom (X ◁ f) where
  lift := LiftObj.lift X ◁ LiftHom.lift f

instance liftHom_WhiskerRight {X Y : C} (f : X ⟶ Y) [LiftObj X] [LiftObj Y] [LiftHom f]
    {Z : C} [LiftObj Z] : LiftHom (f ▷ Z) where
  lift := LiftHom.lift f ▷ LiftObj.lift Z

instance LiftHom_tensor {W X Y Z : C} [LiftObj W] [LiftObj X] [LiftObj Y] [LiftObj Z]
    (f : W ⟶ X) (g : Y ⟶ Z) [LiftHom f] [LiftHom g] : LiftHom (f ⊗ g) where
  lift := LiftHom.lift f ⊗ LiftHom.lift g

end lifting

open Lean Meta Elab Tactic

/-- Helper function for throwing exceptions. -/
def exception {α : Type} (g : MVarId) (msg : MessageData) : MetaM α :=
  throwTacticEx `monoidal_coherence g msg

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
    (← ``(FreeMonoidalCategory.projectMap _root_.id _ _ (LiftHom.lift $(← Term.exprToSyntax e))))
    none

/-- Coherence tactic for monoidal categories. -/
def monoidal_coherence (g : MVarId) : TermElabM Unit := g.withContext do
  withOptions (fun opts => synthInstance.maxSize.set opts
    (max 512 (synthInstance.maxSize.get opts))) do
  let (ty, _) ← dsimp (← g.getType)
    { simpTheorems := #[.addDeclToUnfoldCore {} ``MonoidalCoherence.hom] }
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
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
  pure_coherence
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

/--
Internal tactic used in `coherence`.

Rewrites an equation `f = g` as `f₀ ≫ f₁ = g₀ ≫ g₁`,
where `f₀` and `g₀` are maximal prefixes of `f` and `g` (possibly after reassociating)
which are "liftable" (i.e. expressible as compositions of unitors and associators).
-/
elab (name := liftable_prefixes) "liftable_prefixes" : tactic => do
  withOptions (fun opts => synthInstance.maxSize.set opts
    (max 256 (synthInstance.maxSize.get opts))) do
  evalTactic (← `(tactic|
    (simp (config := {failIfUnchanged := false}) only
      [monoidalComp, Category.assoc, MonoidalCoherence.hom, BicategoricalCoherence.hom]) <;>
    (apply (cancel_epi (𝟙 _)).1 <;> try infer_instance) <;>
    (simp (config := {failIfUnchanged := false}) only
      [assoc_liftHom, Mathlib.Tactic.BicategoryCoherence.assoc_liftHom₂])))

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
    (simp (config := {failIfUnchanged := false}) only [bicategoricalComp, monoidalComp]);
    whisker_simps (config := {failIfUnchanged := false});
    monoidal_simps (config := {failIfUnchanged := false})))
  coherence_loop

end Coherence

end Mathlib.Tactic
