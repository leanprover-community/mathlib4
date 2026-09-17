import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Products.Associator

/-!
# Testing the `@[defeq]` attribute on some important equalities in category theory

Category theory in mathlib relies heavily on the `dsimp` tactic to simplify terms
in dependent position. The `dsimp` tactic makes use of the `@[defeq]` attribute.
In lean v4.31.0, automatic tagging for this attribute was restricted to theorems that are type-correct
at `implicit_reducible` transparency.
An attribute `@[backward_defeq]` was added for theorems that are definitional equalities
but that do not type-check at `implicit_reducible` transparency.

In practice, this means that many lemma generated `@[simps]` on semi-reducible `def`s
are not seen by `dsimp`, unless the option `set_option backward.defeqAttrib.useBackward`
is set to true. This is usually an indicator that the definition needs to be implicit-reducible.

This test file ensures that some of the important "dsimplification" equalities in category
theory are tagged with `@[defeq]`.

You should feel free to add more here when tagging definitions with `@[implicit_reducible]`.
-/

/-- Throwaway command for this test: `#ensure_defeq foo` returns an error if
the declaration `foo` does not have the `@[defeq]` tag (e.g., if it has
the `@[backward_defeq]` tag instead). -/
syntax (name := ensureDefeqCmd) "#ensure_defeq " ident : command

open Lean in
elab_rules : command
  | `(command| #ensure_defeq $ident:ident) => do
    let name := ident.getId
    let env ← getEnv
    match env.find? name with
    | ConstantInfo.thmInfo _ =>
      if defeqAttr.hasTag env name then
        logInfo m!"`{.ofConstName name}` is tagged with @[defeq]"
        return ()
      else if backwardDefeqAttr.hasTag env name then
        throwError "`{.ofConstName name}` is tagged with @[backward_defeq] instead of @[defeq]!"
      else
        throwError "`{.ofConstName name}` is not tagged @[defeq] nor @[backward_defeq]!"
    | none => throwError "Unknown identifier `{.ofConstName name}`"
    | _ => throwError "#ensure_defeq can only be run on equality theorems."

-- intentional error to test the command
/-- error: `CategoryTheory.Category.assoc` is not tagged @[defeq] nor @[backward_defeq]! -/
#guard_msgs (error) in
#ensure_defeq CategoryTheory.Category.assoc

/-- info: `CategoryTheory.NatIso.ofComponents_hom_app` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.NatIso.ofComponents_hom_app

/-- info: `CategoryTheory.Iso.trans_hom` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Iso.trans_hom

/-- info: `CategoryTheory.Functor.comp_map` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Functor.comp_map

/-- info: `CategoryTheory.Functor.comp_obj` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Functor.comp_obj

/-- info: `CategoryTheory.Functor.curry_obj_obj_obj` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Functor.curry_obj_obj_obj

/-- info: `CategoryTheory.Functor.uncurry_obj_obj` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Functor.uncurry_obj_obj

/-- info: `CategoryTheory.Functor.associator_hom_app` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Functor.associator_hom_app

/-- info: `CategoryTheory.Functor.leftUnitor_hom_app` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Functor.leftUnitor_hom_app

/-- info: `CategoryTheory.Functor.rightUnitor_hom_app` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Functor.rightUnitor_hom_app

/-- info: `SSet.mapFundamentalGroupoid_obj_mk` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq SSet.mapFundamentalGroupoid_obj_mk

-- Equivalence and product constructions should compute in dependent positions.

/-- info: `CategoryTheory.Equivalence.mkIso_hom` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Equivalence.mkIso_hom

/-- info: `CategoryTheory.Equivalence.functorFunctor_map` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Equivalence.functorFunctor_map

/-- info: `CategoryTheory.Equivalence.refl_functor` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Equivalence.refl_functor

/-- info: `CategoryTheory.Equivalence.refl_unitIso` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Equivalence.refl_unitIso

/-- info: `CategoryTheory.Equivalence.trans_functor` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Equivalence.trans_functor

/-- info: `CategoryTheory.Equivalence.congrLeft_functor` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Equivalence.congrLeft_functor

/-- info: `CategoryTheory.Equivalence.congrRight_functor` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Equivalence.congrRight_functor

/-- info: `CategoryTheory.Equivalence.congrRightFunctor_map` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Equivalence.congrRightFunctor_map

/-- info: `CategoryTheory.Functor.asEquivalence_functor` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Functor.asEquivalence_functor

/-- info: `CategoryTheory.Functor.asEquivalence_counitIso_hom_app` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.Functor.asEquivalence_counitIso_hom_app

/-- info: `CategoryTheory.ObjectProperty.fullSubcategoryCongr_functor` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.ObjectProperty.fullSubcategoryCongr_functor

/-- info: `CategoryTheory.prod.associator_map` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.prod.associator_map

/-- info: `CategoryTheory.prod.inverseAssociator_obj` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.prod.inverseAssociator_obj

/-- info: `CategoryTheory.prod.inverseAssociator_map` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.prod.inverseAssociator_map

/-- info: `CategoryTheory.prod.associativity_unitIso` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.prod.associativity_unitIso

/-- info: `CategoryTheory.prod.prodFunctorToFunctorProdAssociator_hom_app_app` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.prod.prodFunctorToFunctorProdAssociator_hom_app_app

/-- info: `CategoryTheory.prod.functorProdToProdFunctorAssociator_hom_app` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.prod.functorProdToProdFunctorAssociator_hom_app

/-- info: `CategoryTheory.prod.prodμ_functor_map` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.prod.prodμ_functor_map

/-- info: `CategoryTheory.prod.prodμ_inverse_map` is tagged with @[defeq] -/
#guard_msgs in
#ensure_defeq CategoryTheory.prod.prodμ_inverse_map
