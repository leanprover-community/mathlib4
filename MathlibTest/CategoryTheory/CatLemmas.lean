module

public import Mathlib.Tactic.CategoryTheory.CatLemmas
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Monoidal.Category
public import MathlibTest.CategoryTheory.TheoremTransformRegistration

open CategoryTheory Lean Meta Elab Command

namespace Tests.CatLemmas

universe v u vD uD

variable {C : Type u} [Category.{v} C]

@[cat_lemmas]
lemma family {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    f ≫ g = h := w

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
    {D : Type uD} [Category.{vD} D] (F : Cᵒᵖ ⥤ D) :
    F.map g.op ≫ F.map f.op = F.map h.op := family_op_map.{v, vD, u, uD} f g h w F

-- Opposing a mapped equality instead has a functor out of C, not out of Cᵒᵖ.
attribute [op] family_map

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
    {D : Type uD} [Category.{vD} D] (F : C ⥤ D) :
    (F.map g).op ≫ (F.map f).op = (F.map h).op := family_map_op f g h w F

run_cmd liftTermElabM do
  let src := ``family
  for suffix in ["", "_op", "_map", "_op_map", "_map_op"] do
    guard <| (← getEnv).contains (src.appendAfter suffix)
    guard <| !(← getSimpTheorems).isLemma (.decl (src.appendAfter suffix))
  for suffix in ["_op_op", "_map_map", "_op_map_op", "_assoc"] do
    guard <| !(← getEnv).contains (src.appendAfter suffix)

-- The diagnostic reports the actual family in stage order, without generating twice.
/--
info: Lemma family (attributes applied by cat_lemmas):
diagnostic
diagnostic_op
diagnostic_map
diagnostic_op_map
-/
#guard_msgs in
@[cat_lemmas?]
lemma diagnostic {X Y : C} (f g : X ⟶ Y) (w : f = g) : f = g := w

@[cat_lemmas (skip := [op])]
lemma skipOp {X Y : C} (f g : X ⟶ Y) (w : f = g) : f = g := w

run_cmd liftTermElabM do
  guard <| (← getEnv).contains ``skipOp_map
  guard <| !(← getEnv).contains ((``skipOp).appendAfter "_op")
  guard <| !(← getEnv).contains ((``skipOp).appendAfter "_op_map")

def wrap {X Y : C} (f : X ⟶ Y) := f

/--
info: Lemma family (attributes applied by cat_lemmas):
diagnosticSimp [simp]
diagnosticSimp_op
diagnosticSimp_map [simp]
diagnosticSimp_op_map
-/
#guard_msgs in
@[cat_lemmas? (simp) (noSimp := [op])]
lemma diagnosticSimp {X Y : C} (f : X ⟶ Y) : wrap f = f := rfl

@[simp, cat_lemmas]
lemma sourceSimp {X Y : C} (f : X ⟶ Y) : wrap f = f := rfl

@[cat_lemmas (simp) (noSimp := [op])]
lemma selective {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    wrap f ≫ wrap g = f ≫ g := rfl

run_cmd liftTermElabM do
  let simps ← getSimpTheorems
  guard <| simps.isLemma (.decl ``sourceSimp)
  for n in [``sourceSimp_op, ``sourceSimp_map, ``sourceSimp_op_map] do
    guard <| !simps.isLemma (.decl n)
  for n in [``selective, ``selective_map] do guard <| simps.isLemma (.decl n)
  for n in [``selective_op, ``selective_op_map] do guard <| !simps.isLemma (.decl n)

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) {D : Type*} [Category* D] (F : C ⥤ D) :
    F.map (wrap f) ≫ F.map (wrap g) = F.map f ≫ F.map g := by simp

-- Existing simp membership is preserved even without bundle simp registration.
attribute [simp, cat_lemmas (skip := [map])] Category.id_comp

def identityTemplate (C : Type u) [Category.{v} C] : C ⥤ C := 𝟭 C

@[cat_lemmas (skip := [map]) (specialize := [same := identityTemplate, same := identityTemplate])]
lemma specialized {X Y : C} (f g : X ⟶ Y) (w : f = g) : f = g := w

example {X Y : C} (f g : X ⟶ Y) (w : f = g) : f = g := specialized_same f g w

run_cmd liftTermElabM do
  guard <| (← getEnv).contains ``specialized_same
  guard <| (← getEnv).contains ``specialized_op_same
  guard <| !(← getEnv).contains ((``specialized).appendAfter "_map")
  guard <| !(← getEnv).contains ((``specialized).appendAfter "_same_same")

-- Equal resulting propositions do not make differently named requests identical.
@[cat_lemmas (skip := [op, map]) (simp) (noSimp := [first])
  (specialize := [first := identityTemplate, second := identityTemplate (suffix := "_secondId")])]
lemma siblings {X Y : C} (f : X ⟶ Y) : wrap f = f := rfl

run_cmd liftTermElabM do
  guard <| !(← getSimpTheorems).isLemma (.decl ``siblings_first)
  guard <| (← getSimpTheorems).isLemma (.decl ``siblings_secondId)

def whiskeringTemplate {B C D : Type*} [Category* B] [Category* C] [Category* D]
    (F : D ⥤ B) : (B ⥤ C) ⥤ D ⥤ C := (Functor.whiskeringLeft D B C).obj F

-- This explicit template applies to the original functor category, but not its opposite.
@[cat_lemmas (skip := [map]) (specialize := [whisker := whiskeringTemplate])]
lemma whiskered {B : Type*} [Category* B] {F G : B ⥤ C} (α β : F ⟶ G) (w : α = β) :
    α = β := w

run_cmd liftTermElabM do
  guard <| (← getEnv).contains ``whiskered_whisker
  guard <| !(← getEnv).contains ((``whiskered).appendAfter "_op_whisker")

@[cat_lemmas (skip := [op, map])
  (specialize := [left := MonoidalCategory.tensorLeft, right := MonoidalCategory.tensorRight])]
lemma tensorSiblings {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    f ≫ g = h := w

open MonoidalCategory in
example [MonoidalCategory C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : f ≫ g = h) (T : C) : T ◁ f ≫ T ◁ g = T ◁ h := tensorSiblings_left f g h w T

open MonoidalCategory in
example [MonoidalCategory C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : f ≫ g = h) (T : C) : f ▷ T ≫ g ▷ T = h ▷ T := tensorSiblings_right f g h w T

-- No category match: retain the source, without running every imported registration.
@[cat_lemmas]
lemma numeric (n : Nat) : n = n := rfl

run_cmd liftTermElabM do
  for suffix in ["_op", "_map", "_zeroAdd"] do
    guard <| !(← getEnv).contains ((``numeric).appendAfter suffix)

-- Specialization is also available through the common term driver.
example {X Y : C} (f g : X ⟶ Y) (w : f = g) : f = g :=
  transform_lemma% specialize_map[identityTemplate] w

end Tests.CatLemmas
