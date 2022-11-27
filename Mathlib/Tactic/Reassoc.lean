import Mathlib.CategoryTheory.Category.Basic
import Lean
import Qq

open Qq

set_option warningAsError false

open Lean
namespace Lean.Meta

/--
Given a monadic function `deduce` that takes a type and a term of that type and produces a new term,
lifts this to the monadic function that opens a `∀` telescope, applies `deduce` to the body,
and then builds the lambda telescope term for the new term.
-/
def mapForallTelescope' (deduce : Expr → Expr → MetaM Expr) (forallTerm : Expr) : MetaM Expr := do
  forallTelescope (← Meta.inferType forallTerm) fun xs ty => do
    Meta.mkLambdaFVars xs (← deduce ty (mkAppN forallTerm xs))

#eval do
  let r ← mapForallTelescope' (fun ty e => pure e) q(fun {n : Nat} (m : Nat) => n + m)
  dbg_trace r

/--
Given a monadic function `deduce` that takes a term and produces a new term,
lifts this to the monadic function that opens a `∀` telescope, applies `deduce` to the body,
and then builds the lambda telescope term for the new term.
-/
def mapForallTelescope (deduce : Expr → MetaM Expr) (forallTerm : Expr) : MetaM Expr := do
  mapForallTelescope' (fun _ e => deduce e) forallTerm

end Lean.Meta

open CategoryTheory

axiom C : Type 3
@[instance] axiom 𝒞 : Category.{7} C
axiom X : C
axiom Y : C
axiom Z : C
axiom f : X ⟶ Y
axiom g : Y ⟶ Z
axiom h : X ⟶ Z
axiom w : f ≫ g = h

instance : Repr Q(Type u) := instReprExpr


structure HomExpr (v : Level) {u : Level} (α : Q(Type u)) where
  inst : Q(Category.{v} $α)
  src : Q($α)
  tgt : Q($α)
  hom : Q($src ⟶ $tgt)

instance : Repr (HomExpr v α) where
  reprPrec e n := reprPrec ([e.inst, e.src, e.tgt, e.hom] : List Expr) n

def HomExpr.id? (f : HomExpr v α) : MetaM Bool :=
  match f.hom.getAppFnArgs with
  | (`CategoryStruct.id, _) => pure true
  | _ => pure false

def HomExpr.comp? (f : HomExpr v α) : MetaM (HomExpr v α × HomExpr v α) :=
  match f.hom with
  | ~q(@CategoryStruct.comp _ _ _ $y _ $g $h) => pure ⟨⟨f.inst, f.src, y, g⟩, ⟨f.inst, y, f.tgt, h⟩⟩
  | _ => throwError "{f.hom} is not a composition"

def HomExpr' {v : Level} {u : Level} (α : Q(Type u)) (_ : Q(Category.{v} $α)) (src tgt : Q($α)) :=
  Q($src ⟶ $tgt)

def HomExpr'.comp? (f : HomExpr' α i x z) : MetaM ((y : Q($α)) × HomExpr' α i x y × HomExpr' α i y z) := do
  let (g, h) ← HomExpr.comp? ⟨i, x, z, f⟩
  pure ⟨g.tgt, g.hom, h.hom⟩

namespace Lean.Expr

/-- Infer the type of an expression,
identifying it as a morphism in a category,
or fail. -/
def inferHomExpr (e : Expr) : MetaM ((v u : Level) × (α : Q(Type u)) × HomExpr v α) := do
  let ⟨.succ v, h, e⟩ ← inferTypeQ e | throwError "{e} : Prop, so can not be a morphism"
  match h with
  | ~q(@Quiver.Hom.{v+1} $α $i $x $y) => do
    let ⟨.succ u, α, _⟩ ← inferTypeQ x | failure
    match i with
    | ~q(@CategoryStruct.toQuiver.{v} _ (@Category.toCategoryStruct.{v} _ $i)) => do
      pure ⟨v, u, α, ⟨i, x, y, e⟩⟩
  | _ => throwError "{e} does not match @Quiver.Hom _ _ _ _"


def objectType (e : Expr) : MetaM Q(Type u) := do
  let ⟨_, _, α, _⟩ ← inferHomExpr e
  pure α

def categoryInst (e : Expr) : MetaM Expr := do
  let ⟨_, _, _, ⟨inst, _, _, _⟩⟩ ← inferHomExpr e
  pure inst

def morphismSource (e : Expr) : MetaM Expr := do
  let ⟨_, _, _, ⟨_, src, _, _⟩⟩ ← inferHomExpr e
  pure src

def morphismTarget (e : Expr) : MetaM Expr := do
  let ⟨_, _, _, ⟨_, _, tgt, _⟩⟩ ← inferHomExpr e
  pure tgt

def morphismIdentity? (e : Expr) : MetaM Bool := do
  let ⟨_, _, _, h⟩ ← inferHomExpr e
  h.id?

def morphismComposition? (e : Expr) : MetaM (Expr × Expr) := do
  let ⟨_, _, _, h⟩ ← inferHomExpr e
  let (f, g) ← h.comp?
  pure ⟨f.hom, g.hom⟩


#eval inferHomExpr q(f)
#eval (show MetaM (Expr × Expr) from do
  let ⟨v, u, α, h⟩ ← inferHomExpr q(f ≫ g)
  let ⟨g, h⟩ ← h.comp?
  pure (g.hom, h.hom))

-- #eval inferHomExpr q(7)
-- #eval (show MetaM Expr from do
--   let ⟨v, u, α, h⟩ ← inferHomExpr q(f)
--   let ⟨g, h⟩ ← h.comp?
--   pure g.hom)


end Lean.Expr

variable {C : Type _} [Category C]

/-- A variant of `eq_whisker` with a more convenient argument order for use in tactics.  -/
theorem eq_whisker' {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) :
    f ≫ h = g ≫ h := by rw [w]

open Meta
open Lean.Meta
open Lean.Elab.Tactic

def simpTheoremsOfNames (lemmas : List Name) : MetaM SimpTheorems := do
  lemmas.foldlM (·.addConst ·) (← simpOnlyBuiltins.foldlM (·.addConst ·) {})

def simpOnlyNames (lemmas : List Name) (e : Expr) : MetaM Simp.Result := do
  (·.1) <$> simp e { simpTheorems := #[← simpTheoremsOfNames lemmas], congrTheorems := ← getSimpCongrTheorems }

def categorySimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``Category.comp_id, ``Category.id_comp, ``Category.assoc] e

def deriveType (derive : Expr → MetaM Simp.Result) (e : Expr) : MetaM Expr := do
  match (← derive (← inferType e)) with
  | ⟨ty', none, _⟩ => mkExpectedTypeHint e ty'
  -- We use `mkExpectedTypeHint` in this branch as well, in order to preserve the binder types.
  | ⟨ty', some prf, _⟩ => mkExpectedTypeHint (← mkEqMP prf e) ty'

/--
Given an equation `f = g` between morphisms `X ⟶ Y` in a category (possibly afer a forall binder),
produce the equation `∀ {Z} (h : Y ⟶ Z), f ≫ h = g ≫ h`,
but with compositions fully right associated and identities removed.
-/
def reassoc (e : Expr) : MetaM Expr := do
  mapForallTelescope (fun e => do deriveType categorySimp (← mkAppM `eq_whisker' #[e])) e

open Lean.Elab

initialize registerBuiltinAttribute {
  name := `reassoc
  descr := ""
  add := fun src ref _ => MetaM.run' do
    let tgt := match src with
      | Name.str n s => Name.mkStr n $ s ++ "_assoc"
      | x => x
    addDeclarationRanges tgt {
      range := ← getDeclarationRange (← getRef)
      selectionRange := ← getDeclarationRange ref
    }
    let info ← getConstInfo src
    let newValue ← reassoc info.value!
    let newType ← inferType newValue
    match info with
    | ConstantInfo.thmInfo info =>
      addAndCompile <| .thmDecl { info with type := newType, name := tgt, value := newValue }
    | ConstantInfo.defnInfo info =>
      addAndCompile <| .defnDecl { info with type := newType, name := tgt, value := newValue }
    | _ => throwError "Constant {src} is not a theorem or definition."
    if isProtected (← getEnv) src then
      setEnv $ addProtected (← getEnv) tgt
    ToAdditive.copyAttributes src tgt }
