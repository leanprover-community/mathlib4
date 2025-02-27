/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
import Mathlib.CategoryTheory.Opposites
import Mathlib.Order.Fin.Basic
import Mathlib.Util.Superscript

/-! # The simplex category

We construct a skeletal model of the simplex category, with objects `ℕ` and the
morphisms `n ⟶ m` being the monotone maps from `Fin (n + 1)` to `Fin (m + 1)`.

In `Mathlib.AlgebraicTopology.SimplexCategory.Basic`, we show that this category
is equivalent to `NonemptyFinLinOrd`.

## Remarks

The definitions `SimplexCategory` and `SimplexCategory.Hom` are marked as irreducible.

We provide the following functions to work with these objects:
1. `SimplexCategory.mk` creates an object of `SimplexCategory` out of a natural number.
  Use the notation `⦋n⦌` in the `Simplicial` locale.
2. `SimplexCategory.len` gives the "length" of an object of `SimplexCategory`, as a natural.
3. `SimplexCategory.Hom.mk` makes a morphism out of a monotone map between `Fin`'s.
4. `SimplexCategory.Hom.toOrderHom` gives the underlying monotone map associated to a
  term of `SimplexCategory.Hom`.

## Notations

* `⦋n⦌` denotes the `n`-dimensional simplex. This notation is available with
  `open Simplicial`.
* `⦋m⦌ₙ` denotes the `m`-dimensional simplex in the `n`-truncated simplex category.
  The truncation proof `p : m ≤ n` can also be provided using the syntax `⦋m, p⦌ₙ`.
  This notation is available with `open SimplexCategory.Truncated`.
-/

universe v

open CategoryTheory

/-- The simplex category:
* objects are natural numbers `n : ℕ`
* morphisms from `n` to `m` are monotone functions `Fin (n+1) → Fin (m+1)`
-/
def SimplexCategory :=
  ℕ

namespace SimplexCategory

-- Porting note: the definition of `SimplexCategory` is made irreducible below
/-- Interpret a natural number as an object of the simplex category. -/
def mk (n : ℕ) : SimplexCategory :=
  n

/-- the `n`-dimensional simplex can be denoted `⦋n⦌` -/
scoped[Simplicial] notation "⦋" n "⦌" => SimplexCategory.mk n

-- TODO: Make `len` irreducible.
/-- The length of an object of `SimplexCategory`. -/
def len (n : SimplexCategory) : ℕ :=
  n

@[ext]
theorem ext (a b : SimplexCategory) : a.len = b.len → a = b :=
  id

attribute [irreducible] SimplexCategory

open Simplicial

@[simp]
theorem len_mk (n : ℕ) : ⦋n⦌.len = n :=
  rfl

@[simp]
theorem mk_len (n : SimplexCategory) : ⦋n.len⦌ = n :=
  rfl

/-- A recursor for `SimplexCategory`. Use it as `induction Δ using SimplexCategory.rec`. -/
protected def rec {F : SimplexCategory → Sort*} (h : ∀ n : ℕ, F ⦋n⦌) : ∀ X, F X := fun n =>
  h n.len

/-- Morphisms in the `SimplexCategory`. -/
protected def Hom (a b : SimplexCategory) :=
  Fin (a.len + 1) →o Fin (b.len + 1)

namespace Hom

/-- Make a morphism in `SimplexCategory` from a monotone map of `Fin`'s. -/
def mk {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1)) : SimplexCategory.Hom a b :=
  f

/-- Recover the monotone map from a morphism in the simplex category. -/
def toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) :
    Fin (a.len + 1) →o Fin (b.len + 1) :=
  f

theorem ext' {a b : SimplexCategory} (f g : SimplexCategory.Hom a b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  id

attribute [irreducible] SimplexCategory.Hom

@[simp]
theorem mk_toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) : mk f.toOrderHom = f :=
  rfl

@[simp]
theorem toOrderHom_mk {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1)) :
    (mk f).toOrderHom = f :=
  rfl

theorem mk_toOrderHom_apply {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1))
    (i : Fin (a.len + 1)) : (mk f).toOrderHom i = f i :=
  rfl

/-- Identity morphisms of `SimplexCategory`. -/
@[simp]
def id (a : SimplexCategory) : SimplexCategory.Hom a a :=
  mk OrderHom.id

/-- Composition of morphisms of `SimplexCategory`. -/
@[simp]
def comp {a b c : SimplexCategory} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b) :
    SimplexCategory.Hom a c :=
  mk <| f.toOrderHom.comp g.toOrderHom

end Hom

instance smallCategory : SmallCategory.{0} SimplexCategory where
  Hom n m := SimplexCategory.Hom n m
  id _ := SimplexCategory.Hom.id _
  comp f g := SimplexCategory.Hom.comp g f

@[simp]
lemma id_toOrderHom (a : SimplexCategory) :
    Hom.toOrderHom (𝟙 a) = OrderHom.id := rfl

@[simp]
lemma comp_toOrderHom {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).toOrderHom = g.toOrderHom.comp f.toOrderHom := rfl

@[ext]
theorem Hom.ext {a b : SimplexCategory} (f g : a ⟶ b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  Hom.ext' _ _

/-- The truncated simplex category. -/
def Truncated (n : ℕ) :=
  FullSubcategory fun a : SimplexCategory => a.len ≤ n

instance (n : ℕ) : SmallCategory.{0} (Truncated n) :=
  FullSubcategory.category _

namespace Truncated

instance {n} : Inhabited (Truncated n) :=
  ⟨⟨⦋0⦌, by simp⟩⟩

/-- The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
def inclusion (n : ℕ) : SimplexCategory.Truncated n ⥤ SimplexCategory :=
  fullSubcategoryInclusion _

instance (n : ℕ) : (inclusion n : Truncated n ⥤ _).Full := FullSubcategory.full _
instance (n : ℕ) : (inclusion n : Truncated n ⥤ _).Faithful := FullSubcategory.faithful _

/-- A proof that the full subcategory inclusion is fully faithful -/
noncomputable def inclusion.fullyFaithful (n : ℕ) :
    (inclusion n : Truncated n ⥤ _).op.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _

@[ext]
theorem Hom.ext {n} {a b : Truncated n} (f g : a ⟶ b) :
    f.toOrderHom = g.toOrderHom → f = g := SimplexCategory.Hom.ext _ _

section Meta

open Mathlib.Tactic (subscriptTerm) in
/-- For `m ≤ n`, `⦋m⦌ₙ` is the `m`-dimensional simplex in `Truncated n`. The
proof `p : m ≤ n` can also be provided using the syntax `⦋m, p⦌ₙ`. -/
scoped syntax:max (name := mkNotation)
  "⦋" term ("," term)? "⦌" noWs subscriptTerm : term
scoped macro_rules
  | `(⦋$m:term⦌$n:subscript) =>
    `((⟨SimplexCategory.mk $m, by first | get_elem_tactic |
      fail "Failed to prove truncation property. Try writing `⦋m, by ...⦌ₙ`."⟩ :
      SimplexCategory.Truncated $n))
  | `(⦋$m:term, $p:term⦌$n:subscript) =>
    `((⟨SimplexCategory.mk $m, $p⟩ : SimplexCategory.Truncated $n))

section Delab
open Lean PrettyPrinter.Delaborator SubExpr
open Mathlib.Tactic.Superscript (Mapping)

/-- Checks that the provided expression can be subscripted. -/
private partial def subscriptable (e : Expr) : DelabM Unit := do
  -- Any number or free variable with a subscriptable name is subscriptable.
  if (← name e).any isSubscriptable || (← delab) matches `($_:num) then return
  -- Addition and subtraction are subscriptable if their operands are.
  guard <| e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6
  let #[_, _, _, _, x, y] := e.getAppArgs | failure
  let _ ← withNaryArg 4 <| subscriptable x
  let _ ← withAppArg <| subscriptable y
where
  -- Return the user-facing name of any constant or free variable.
  name : Expr → MetaM (Option Name)
    | Expr.const name _ => pure name
    | Expr.fvar name => name.getUserName
    | _ => pure none
  -- Return `true` if every character in `s` can be subscripted.
  isSubscriptable (s : Name) : Bool :=
    s.toString.toList.all Mapping.subscript.toSpecial.contains

/-- Checks that the provided expression can be subscripted before delaborating. -/
def Meta.subscript (e : Expr) : Delab := subscriptable e >>= fun () ↦ delab

/-- Delaborator for the notation `⦋m⦌ₙ`. -/
@[app_delab FullSubcategory.mk]
def delabMkNotation : Delab :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 4 do
    let #[cat, .lam x _ body _, simplex, _] := (← getExpr).getAppArgs | failure
    -- check that this is a `FullSubcategory` of `SimplexCategory`
    guard <| cat.isConstOf ``SimplexCategory
    guard <| simplex.isAppOfArity ``SimplexCategory.mk 1
    -- check that the predicate matches `fun x ↦ x.len ≤ n`
    let_expr LE.le _ _ lhs rhs := body | failure
    let_expr SimplexCategory.len simplex := lhs | failure
    guard <| simplex == .bvar 0
    -- if `pp.proofs` is set to `true`, include the proof `p : m ≤ n`
    let n ← withNaryArg 1 <| withBindingBody x <| withAppArg <| Meta.subscript rhs
    let m ← withNaryArg 2 <| withAppArg delab
    if (← getPPOption getPPProofs) then
      let p ← withAppArg delab
      `(⦋$m, $p⦌$n)
    else `(⦋$m⦌$n)

end Delab
end Meta

end Truncated

end SimplexCategory
