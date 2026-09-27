module

public import Mathlib.Tactic.CategoryTheory.CatLemmas
public import Mathlib.Tactic.CategoryTheory.IsoReassoc

open CategoryTheory Lean Meta Elab Command

namespace Tests.TheoremTransformCompatibility

variable {C : Type*} [Category* C]

/-- Documentation retained by generated declarations. -/
@[map]
protected lemma protectedSource {X Y : C} (f g : X ⟶ Y) (h : f = g) : f = g := h

run_cmd liftTermElabM do
  let src := ``protectedSource
  let tgt := src.appendAfter "_map"
  let env ← getEnv
  guard <| isProtected env tgt
  guard <| (← findDocString? env src) == (← findDocString? env tgt)
  guard <| (← findDeclarationRanges? tgt).isSome

def wrap {X Y : C} (f : X ⟶ Y) := f

@[simp, map, op]
lemma onlySource {X Y : C} (f : X ⟶ Y) : wrap f = f := rfl

@[op (attr := map (attr := reassoc (attr := simp)))]
lemma allBranches {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    wrap f ≫ wrap g = f ≫ g := rfl

run_cmd liftTermElabM do
  let simps ← getSimpTheorems
  guard <| simps.isLemma (.decl ``onlySource)
  guard <| !simps.isLemma (.decl ``onlySource_map)
  guard <| !simps.isLemma (.decl ``onlySource_op)
  for suffix in ["", "_op", "_map", "_op_map", "_assoc", "_op_assoc",
      "_map_assoc", "_op_map_assoc"] do
    guard <| simps.isLemma (.decl ((``allBranches).appendAfter suffix))

@[to_dual (attr := op) dualOp]
lemma sourceOp {X Y : C} (f g : X ⟶ Y) (h : f = g) : f = g := h

@[to_dual (attr := cat_lemmas) dualBundle]
lemma sourceBundle {X Y : C} (f g : X ⟶ Y) (h : f = g) : f = g := h

run_cmd liftTermElabM do
  let env ← getEnv
  for (src, tgt) in [(``sourceOp_op, ``dualOp_op),
      (``sourceBundle_map, ``dualBundle_map), (``sourceBundle_op, ``dualBundle_op),
      (``sourceBundle_op_map, ``dualBundle_op_map)] do
    guard <| (Mathlib.Tactic.Translate.findTranslationName? env Mathlib.Tactic.ToDual.data src) == some tgt

-- Keep reassociation's isomorphism handler intact.
@[reassoc]
lemma iso {X Y : C} (f g : X ≅ Y) (h : f = g) : f = g := h

example {X Y Z : C} (f g : X ≅ Y) (h : f = g) (e : Y ≅ Z) : f ≪≫ e = g ≪≫ e :=
  iso_assoc f g h e

-- The explicit duality option still marks the generated reassociation lemma.
@[to_dual homDual]
lemma hom {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    f ≫ g = h := w

attribute [reassoc +to_dual] hom

run_cmd liftTermElabM do
  guard <| (Mathlib.Tactic.Translate.findTranslation? (← getEnv)
    Mathlib.Tactic.ToDual.data ``hom_assoc).isSome

-- Reassociation after mapping accepts an arbitrary target-category postcomposition.
attribute [reassoc] sourceBundle_op_map

example {X Y : C} (f g : X ⟶ Y) (h : f = g) {D : Type*} [Category* D]
    (F : Cᵒᵖ ⥤ D) {Z : D} (k : F.obj (Opposite.op X) ⟶ Z) :
    F.map f.op ≫ k = F.map g.op ≫ k := sourceBundle_op_map_assoc f g h F k

end Tests.TheoremTransformCompatibility
