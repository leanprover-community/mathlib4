/-
Copyright (c) 2022. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yuma Mizuno, Oleksandr Manzyuk

! This file was ported from Lean 3 source module category_theory.monoidal.coherence
! leanprover-community/mathlib commit f187f1074fa1857c94589cc653c786cadc4c35ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
-- Porting note: restore when ported
-- import Mathlib.CategoryTheory.Bicategory.CoherenceTactic

/-!
# A `coherence` tactic for monoidal categories, and `⊗≫` (composition up to associators)

We provide a `coherence` tactic,
which proves equations where the two sides differ by replacing
strings of monoidal structural morphisms with other such strings.
(The replacements are always equalities by the monoidal coherence theorem.)

A simpler version of this tactic is `pure_coherence`,
which proves that any two morphisms (with the same source and target)
in a monoidal category which are built out of associators and unitors
are equal.

We also provide `f ⊗≫ g`, the `monoidal_comp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.
-/

noncomputable section

universe v u

open CategoryTheory
open CategoryTheory.FreeMonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace CategoryTheory.MonoidalCategory

/-- A typeclass carrying a choice of lift of an object from `C` to `FreeMonoidalCategory C`. -/
class LiftObj (X : C) :=
(lift : FreeMonoidalCategory C)

instance LiftObj_unit : LiftObj (𝟙_ C) := { lift := Unit, }
instance LiftObj_tensor (X Y : C) [LiftObj X] [LiftObj Y] : LiftObj (X ⊗ Y) :=
{ lift := LiftObj.lift X ⊗ LiftObj.lift Y, }
instance (priority := 100) LiftObj_of (X : C) : LiftObj X := { lift := of X, }

/-- A typeclass carrying a choice of lift of a morphism from `C` to `FreeMonoidalCategory C`. -/
class LiftHom {X Y : C} [LiftObj X] [LiftObj Y] (f : X ⟶ Y) :=
(lift : LiftObj.lift X ⟶ LiftObj.lift Y)

instance LiftHom_id (X : C) [LiftObj X] : LiftHom (𝟙 X) :=
{ lift := 𝟙 _, }
instance LiftHom_left_unitor_hom (X : C) [LiftObj X] : LiftHom (λ_ X).hom :=
{ lift := (λ_ (LiftObj.lift X)).hom, }
instance LiftHom_left_unitor_inv (X : C) [LiftObj X] : LiftHom (λ_ X).inv :=
{ lift := (λ_ (LiftObj.lift X)).inv, }
instance LiftHom_right_unitor_hom (X : C) [LiftObj X] : LiftHom (ρ_ X).hom :=
{ lift := (ρ_ (LiftObj.lift X)).hom, }
instance LiftHom_right_unitor_inv (X : C) [LiftObj X] : LiftHom (ρ_ X).inv :=
{ lift := (ρ_ (LiftObj.lift X)).inv, }
instance LiftHom_associator_hom (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] :
  LiftHom (α_ X Y Z).hom :=
{ lift := (α_ (LiftObj.lift X) (LiftObj.lift Y) (LiftObj.lift Z)).hom, }
instance LiftHom_associator_inv (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] :
  LiftHom (α_ X Y Z).inv :=
{ lift := (α_ (LiftObj.lift X) (LiftObj.lift Y) (LiftObj.lift Z)).inv, }
instance LiftHom_comp {X Y Z : C} [LiftObj X] [LiftObj Y] [LiftObj Z] (f : X ⟶ Y) (g : Y ⟶ Z)
  [LiftHom f] [LiftHom g] : LiftHom (f ≫ g) :=
{ lift := LiftHom.lift f ≫ LiftHom.lift g }
instance LiftHom_tensor {W X Y Z : C} [LiftObj W] [LiftObj X] [LiftObj Y] [LiftObj Z]
  (f : W ⟶ X) (g : Y ⟶ Z) [LiftHom f] [LiftHom g] : LiftHom (f ⊗ g) :=
{ lift := LiftHom.lift f ⊗ LiftHom.lift g }

/--
A typeclass carrying a choice of monoidal structural isomorphism between two objects.
Used by the `⊗≫` monoidal composition operator, and the `coherence` tactic.
-/
-- We could likely turn this into a `Prop` valued existential if that proves useful.
class MonoidalCoherence (X Y : C) [LiftObj X] [LiftObj Y] :=
(hom : X ⟶ Y)
[isIso : IsIso hom]

attribute [instance] MonoidalCoherence.isIso

namespace MonoidalCoherence

@[simps]
instance refl (X : C) [LiftObj X] : MonoidalCoherence X X := ⟨𝟙 _⟩

@[simps]
instance tensor (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] [MonoidalCoherence Y Z] :
  MonoidalCoherence (X ⊗ Y) (X ⊗ Z) :=
⟨𝟙 X ⊗ MonoidalCoherence.hom⟩

@[simps]
instance tensor_right (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence (𝟙_ C) Y] :
  MonoidalCoherence X (X ⊗ Y) :=
⟨(ρ_ X).inv ≫ (𝟙 X ⊗ MonoidalCoherence.hom)⟩

@[simps]
instance tensor_right' (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence Y (𝟙_ C)] :
  MonoidalCoherence (X ⊗ Y) X :=
⟨(𝟙 X ⊗ MonoidalCoherence.hom) ≫ (ρ_ X).hom⟩

@[simps]
instance left (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] :
  MonoidalCoherence (𝟙_ C ⊗ X) Y :=
⟨(λ_ X).hom ≫ MonoidalCoherence.hom⟩

@[simps]
instance left' (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] :
  MonoidalCoherence X (𝟙_ C ⊗ Y) :=
⟨MonoidalCoherence.hom ≫ (λ_ Y).inv⟩

@[simps]
instance right (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] :
  MonoidalCoherence (X ⊗ 𝟙_ C) Y :=
⟨(ρ_ X).hom ≫ MonoidalCoherence.hom⟩

@[simps]
instance right' (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] :
  MonoidalCoherence X (Y ⊗ 𝟙_ C) :=
⟨MonoidalCoherence.hom ≫ (ρ_ Y).inv⟩

@[simps]
instance assoc (X Y Z W : C) [LiftObj W] [LiftObj X] [LiftObj Y] [LiftObj Z]
  [MonoidalCoherence (X ⊗ (Y ⊗ Z)) W] : MonoidalCoherence ((X ⊗ Y) ⊗ Z) W :=
⟨(α_ X Y Z).hom ≫ MonoidalCoherence.hom⟩

@[simps]
instance assoc' (W X Y Z : C) [LiftObj W] [LiftObj X] [LiftObj Y] [LiftObj Z]
  [MonoidalCoherence W (X ⊗ (Y ⊗ Z))] : MonoidalCoherence W ((X ⊗ Y) ⊗ Z) :=
⟨MonoidalCoherence.hom ≫ (α_ X Y Z).inv⟩

end MonoidalCoherence

/-- Construct an isomorphism between two objects in a monoidal category
out of unitors and associators. -/
def monoidalIso (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] : X ≅ Y :=
asIso MonoidalCoherence.hom

example (X : C) : X ≅ (X ⊗ (𝟙_ C ⊗ 𝟙_ C)) := monoidalIso _ _

example (X1 X2 X3 X4 X5 X6 X7 X8 X9 : C) :
  (𝟙_ C ⊗ (X1 ⊗ X2 ⊗ ((X3 ⊗ X4) ⊗ X5)) ⊗ X6 ⊗ (X7 ⊗ X8 ⊗ X9)) ≅
  (X1 ⊗ (X2 ⊗ X3) ⊗ X4 ⊗ (X5 ⊗ (𝟙_ C ⊗ X6) ⊗ X7) ⊗ X8 ⊗ X9) :=
monoidalIso _ _

/-- Compose two morphisms in a monoidal category,
inserting unitors and associators between as necessary. -/
def monoidalComp {W X Y Z : C} [LiftObj X] [LiftObj Y]
  [MonoidalCoherence X Y] (f : W ⟶ X) (g : Y ⟶ Z) : W ⟶ Z :=
f ≫ MonoidalCoherence.hom ≫ g

@[inherit_doc monoidalComp]
infixr:80 " ⊗≫ " => monoidalComp -- type as \ot \gg

/-- Compose two isomorphisms in a monoidal category,
inserting unitors and associators between as necessary. -/
def monoidalIsoComp {W X Y Z : C} [LiftObj X] [LiftObj Y]
  [MonoidalCoherence X Y] (f : W ≅ X) (g : Y ≅ Z) : W ≅ Z :=
f ≪≫ asIso MonoidalCoherence.hom ≪≫ g

@[inherit_doc monoidalIsoComp]
infixr:80 " ≪⊗≫ " => monoidalIsoComp -- type as \ot \gg

example {U V W X Y : C} (f : U ⟶ V ⊗ (W ⊗ X)) (g : (V ⊗ W) ⊗ X ⟶ Y) : U ⟶ Y := f ⊗≫ g

-- To automatically insert unitors/associators at the beginning or end,
-- you can use `f ⊗≫ 𝟙 _`
example {W X Y Z : C} (f : W ⟶ (X ⊗ Y) ⊗ Z) : W ⟶ X ⊗ (Y ⊗ Z) := f ⊗≫ 𝟙 _

@[simp] lemma monoidalComp_refl {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ⊗≫ g = f ≫ g := by
  simp [monoidalComp]

example {U V W X Y : C} (f : U ⟶ V ⊗ (W ⊗ X)) (g : (V ⊗ W) ⊗ X ⟶ Y) :
    f ⊗≫ g = f ≫ (α_ _ _ _).inv ≫ g := by
  simp [monoidalComp]

end CategoryTheory.MonoidalCategory

open CategoryTheory.MonoidalCategory

namespace Mathlib.Tactic.Coherence

open Lean Meta Elab Tactic

/--
Auxilliary definition of `monoidal_coherence`,
being careful with namespaces to avoid shadowing.
-/
-- We could construct this expression directly without using `elabTerm`,
-- but it would require preparing many implicit arguments by hand.
def mkProjectMapExpr (e : Expr) : TermElabM Expr := do
  Term.elabTerm (← `(CategoryTheory.FreeMonoidalCategory.projectMap _root_.id _ _
    (CategoryTheory.MonoidalCategory.LiftHom.lift $(← Term.exprToSyntax e)))) none

/-- Coherence tactic for monoidal categories. -/
def monoidal_coherence (g : MVarId) : TermElabM Unit := do
  withOptions (fun opts => opts.setNat `synthInstance.maxSize
    (max 256 (opts.getNat `synthInstance.maxSize))) do
  -- TODO: is this `dsimp only` step necessary? It doesn't appear to be in the tests below.
  let (ty, _) ← dsimp (← g.getType) (← Simp.Context.ofNames [] true)
  let some (_, lhs, rhs) := ty.eq? | throwError "Not an equation of morphisms."
  let projectMap_lhs ← mkProjectMapExpr lhs
  let projectMap_rhs ← mkProjectMapExpr rhs
  let g₁ ← g.change (← mkEq projectMap_lhs projectMap_rhs)
  let [g₂] ← g₁.apply (← mkConstWithFreshMVarLevels `congrArg)
    | throwError "congrArg failed in coherence"
  _ ← g₂.apply (← mkConstWithFreshMVarLevels `Subsingleton.elim)

/-- Coherence tactic for monoidal categories. -/
syntax (name := monoidal_coherence_stx) "monoidal_coherence" : tactic

elab_rules : tactic | `(tactic| monoidal_coherence) => withMainContext do
    monoidal_coherence (← getMainGoal)

/--
`pure_coherence` uses the coherence theorem for monoidal categories to prove the goal.
It can prove any equality made up only of associators, unitors, and identities.
```lean
example {C : Type} [Category C] [MonoidalCategory C] :
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
by pure_coherence
```

Users will typically just use the `coherence` tactic, which can also cope with identities of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `pure_coherence`
-/
macro (name := pure_coherence) "pure_coherence" : tactic =>
  `(tactic| monoidal_coherence)

-- Porting note: restore this when `category_theory.bicategory.coherence` is ported.
-- macro (name := pure_coherence') "pure_coherence" : tactic =>
--   `(tactic| bicategory_coherence)

example (X₁ X₂ : C) :
    ((λ_ (𝟙_ C)).inv ⊗ 𝟙 (X₁ ⊗ X₂)) ≫ (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫
      (𝟙 (𝟙_ C) ⊗ (α_ (𝟙_ C) X₁ X₂).inv) =
    𝟙 (𝟙_ C) ⊗ ((λ_ X₁).inv ⊗ 𝟙 X₂) := by
  pure_coherence
  -- This is just running:
  -- change projectMap id _ _ (LiftHom.lift (((λ_ (𝟙_ C)).inv ⊗ 𝟙 (X₁ ⊗ X₂)) ≫
  --     (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫ (𝟙 (𝟙_ C) ⊗ (α_ (𝟙_ C) X₁ X₂).inv))) =
  --   projectMap id _ _ (LiftHom.lift (𝟙 (𝟙_ C) ⊗ ((λ_ X₁).inv ⊗ 𝟙 X₂)))
  -- exact congrArg _ (Subsingleton.elim _ _)

namespace coherence

/--
Auxiliary simp lemma for the `coherence` tactic:
this moves brackets to the left in order to expose a maximal prefix
built out of unitors and associators.
-/
-- We have unused typeclass arguments here.
-- They are intentional, to ensure that `simp only [assoc_LiftHom]` only left associates
-- monoidal structural morphisms.
@[nolint unusedArguments]
lemma assoc_LiftHom {W X Y Z : C} [LiftObj W] [LiftObj X] [LiftObj Y]
  (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) [LiftHom f] [LiftHom g] :
  f ≫ (g ≫ h) = (f ≫ g) ≫ h :=
(Category.assoc _ _ _).symm

/--
Internal tactic used in `coherence`.

Rewrites an equation `f = g` as `f₀ ≫ f₁ = g₀ ≫ g₁`,
where `f₀` and `g₀` are maximal prefixes of `f` and `g` (possibly after reassociating)
which are "liftable" (i.e. expressible as compositions of unitors and associators).
-/
macro (name := liftable_prefixes) "liftable_prefixes" : tactic => do
  -- TODO we used to set the max instance search depth higher. Is this still needed?
  `(tactic| (
    simp only [monoidalComp, Category.assoc, MonoidalCoherence.hom] <;>
    (apply (cancel_epi (𝟙 _)).1 <;> try infer_instance) <;>
    -- TODO add `Bicategory.Coherence.assoc_LiftHom₂` when
    -- `category_theory.bicategory.coherence` is ported.
    simp only [assoc_LiftHom]))

example {Y Z : C} (f : Y ⟶ Z) (g) (w : false) : (λ_ _).hom ≫ f = g := by
  liftable_prefixes
  guard_target = (𝟙 _ ≫ (λ_ _).hom) ≫ f = (𝟙 _) ≫ g
  cases w

lemma insert_id_lhs {C : Type _} [Category C] {X Y : C} (f g : X ⟶ Y) (w : f ≫ 𝟙 _ = g) : f = g :=
by simpa using w
lemma insert_id_rhs {C : Type _} [Category C] {X Y : C} (f g : X ⟶ Y) (w : f = g ≫ 𝟙 _) : f = g :=
by simpa using w

end coherence

open coherence

/-- If either the lhs or rhs is not a composition, compose it on the right with an identity. -/
def insertTrailingIds : TacticM Unit := do
  let some (_, lhs, rhs) := (← getMainTarget).eq? | throwError "Not an equality."
  match lhs.getAppFnArgs with
  | (``CategoryStruct.comp, _) => pure ()
  | _ => evalTactic (← `(tactic| apply insert_id_lhs))
  match rhs.getAppFnArgs with
  | (``CategoryStruct.comp, _) => pure ()
  | _ => evalTactic (← `(tactic| apply insert_id_rhs))

/-- The main part of `coherence` tactic. -/
-- Porting note: this is an ugly port, using too many `evalTactic`s.
-- We can refactor later into either a `macro` (but the flow control is awkward)
-- or a `MetaM` tactic.
partial def coherence_loop : TacticM Unit :=
do
  -- To prove an equality `f = g` in a monoidal category,
  -- first try the `pure_coherence` tactic on the entire equation:
  evalTactic (← `(tactic| pure_coherence)) <|> do
  -- Otherwise, rearrange so we have a maximal prefix of each side
  -- that is built out of unitors and associators:
  evalTactic (← `(tactic| liftable_prefixes)) <|>
    throwError ("Something went wrong in the `coherence` tactic: " ++
      "is the target an equation in a monoidal category?")
  -- The goal should now look like `f₀ ≫ f₁ = g₀ ≫ g₁`,
  liftMetaTactic (MVarId.congrN (depth := 1) (closePre := false) (closePost := false))
  -- and now we have two goals `f₀ = g₀` and `f₁ = g₁`.
  -- Discharge the first using `coherence`,
  evalTactic (← `(tactic| { pure_coherence })) <|> (do
    throwError ("`coherence` tactic failed, " ++
      s!"subgoal {← ppExpr (← getMainTarget)} not true in the free monoidal_category"))
  -- Then check that either `g₀` is identically `g₁`,
  evalTactic (← `(tactic| rfl)) <|> (do
    -- or that both are compositions,
    insertTrailingIds
    liftMetaTactic (MVarId.congrN (depth := 1) (closePre := false) (closePost := false))
    -- with identical first terms,
    evalTactic (← `(tactic| rfl)) <|>
      throwError ("`coherence` tactic failed, non-structural morphisms don't match: " ++
        s!"{← ppExpr (← getMainTarget)}")
    -- and whose second terms can be identified by recursively called `coherence`.
    coherence_loop)

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
  evalTactic (← `(tactic| (
    -- Porting note: restore this when `category_theory.bicategory.coherence` is ported.
    -- simp only [bicategorical_comp];
    simp only [monoidalComp];
    -- Porting note: restore this when `category_theory.bicategory.coherence` is ported.
    -- try bicategory.whisker_simps
    )))
  coherence_loop

example (f : 𝟙_ C ⟶ _) : f ≫ (λ_ (𝟙_ C)).hom = f ≫ (ρ_ (𝟙_ C)).hom :=
by coherence

example (f) : (λ_ (𝟙_ C)).hom ≫ f ≫ (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ f ≫ (ρ_ (𝟙_ C)).hom :=
by coherence

example {U : C} (f : U ⟶ 𝟙_ C) : f ≫ (ρ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom = f :=
by coherence

example (W X Y Z : C) (f) :
  ((α_ W X Y).hom ⊗ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).hom ≫ (𝟙 W ⊗ (α_ X Y Z).hom) ≫ f ≫
    (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom =
  (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom ≫ f ≫
    ((α_ W X Y).hom ⊗ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).hom ≫ (𝟙 W ⊗ (α_ X Y Z).hom) :=
by coherence

example {U V W X Y : C} (f : U ⟶ V ⊗ (W ⊗ X)) (g : (V ⊗ W) ⊗ X ⟶ Y) :
    f ⊗≫ g = f ≫ (α_ _ _ _).inv ≫ g := by
  coherence
