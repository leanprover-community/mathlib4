/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Opposites
public import Mathlib.Tactic.CategoryTheory.HomTransform

/-!
# The `op` attribute

Adding `@[op]` to a lemma named `H` of shape `∀ .., f = g`, where `f` and `g` are morphisms
in some category `C`, creates a new lemma named `H_op` by applying `Quiver.Hom.op` to both sides
and then simplifying with `simp only [op_comp, op_id]`.

There is also a term elaborator `op_of% t` for use within proofs.
-/

public meta section

open Lean Meta Elab Tactic Qq
open CategoryTheory

namespace Mathlib.Tactic.CategoryTheory.Op

open TheoremTransform

/-- `simp only` with `op_comp` and `op_id` on a single expression (used on each side via
`simpEq`). -/
def opSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``op_comp, ``op_id] e (config := { decide := false })

/-- Apply `Quiver.Hom.op` and normalize with `op_comp` and `op_id`, retaining the normalized
type even when simplification changes only the displayed statement. -/
def opHomProof (p : Proof) : Term.TermElabM (Except MessageData Proof) := do
  match ← matchHomEquality p `op with
  | .error reason => return .error reason
  | .ok ⟨u, v, _C, instC, _X, _Y, f, g⟩ => do
    let e : Q($f = $g) := p.value
    let type : Q(Prop) := q(Quiver.Hom.op $f = Quiver.Hom.op $g)
    let value : Q($type) := q(congrArg Quiver.Hom.op $e)
    return .ok (← normalizeHomProof instC ⟨type, value⟩ opSimp)

/-- Build the opposite equality without emitting a declaration. -/
def opExprHom (type : Q(Prop)) (e : Q($type)) : Term.TermElabM Expr := do
  match ← opHomProof ⟨type, e⟩ with
  | .ok p => p.toExpr
  | .error reason => throwError reason

initialize TheoremTransform.register `op {
  suffix := "_op"
  apply := fun request p => do
    unless request.args.isEmpty do throwError "`op` takes no transformation arguments"
    underForall p opHomProof }

/-- Apply the opposite transformation beneath forall binders. -/
def opExpr (pf : Expr) : Term.TermElabM Expr := do
  (← TheoremTransform.apply { transformation := `op } (← Proof.ofExpr pf)).toExpr

/--
Adding `@[op]` to a lemma named `H` of shape `∀ .., f = g`, where `f` and `g` are morphisms in
some category `C`, creates a new lemma named `H_op` by applying `Quiver.Hom.op` to both sides and
then simplifying with `simp only [op_comp, op_id]`.

Use `@[op (attr := map)]` to mark both the original lemma and `H_op` with `map`, and similarly
for `reassoc` and other attributes.
-/
syntax (name := opStx) "op" optAttrArg : attr

private def opImpl (src : Name) (ref : Syntax) (kind : AttributeKind) : AttrM Name :=
  match ref with
  | `(attr| op $optAttr) => MetaM.run' do
    unless kind == .global do throwError "`op` can only be used as a global attribute"
    TheoremTransform.addDecl { transformation := `op } src ref optAttr
  | _ => throwUnsupportedSyntax

initialize
  registerGeneratingAttr `opStx ((#[·]) <$> opImpl · · ·)
  registerBuiltinAttribute {
    name := `opStx
    descr := ""
    applicationTime := .afterCompilation
    add := fun src ref kind => discard <| opImpl src ref kind }

/--
`op_of% t`, where `t` is an equality `f = g` between morphisms (possibly under `∀` binders),
produces the corresponding statement with `Quiver.Hom.op` applied to both sides and
`simp only [op_comp, op_id]` on each side.
-/
elab "op_of% " t:term : term => do
  TheoremTransform.elabTerm { transformation := `op } t

end Mathlib.Tactic.CategoryTheory.Op
