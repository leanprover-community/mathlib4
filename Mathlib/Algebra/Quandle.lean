/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller

! This file was ported from Lean 3 source module algebra.quandle
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Algebra.Hom.Aut
import Mathbin.Data.Zmod.Defs
import Mathbin.Tactic.Group

/-!
# Racks and Quandles

This file defines racks and quandles, algebraic structures for sets
that bijectively act on themselves with a self-distributivity
property.  If `R` is a rack and `act : R → (R ≃ R)` is the self-action,
then the self-distributivity is, equivalently, that
```
act (act x y) = act x * act y * (act x)⁻¹
```
where multiplication is composition in `R ≃ R` as a group.
Quandles are racks such that `act x x = x` for all `x`.

One example of a quandle (not yet in mathlib) is the action of a Lie
algebra on itself, defined by `act x y = Ad (exp x) y`.

Quandles and racks were independently developed by multiple
mathematicians.  David Joyce introduced quandles in his thesis
[Joyce1982] to define an algebraic invariant of knot and link
complements that is analogous to the fundamental group of the
exterior, and he showed that the quandle associated to an oriented
knot is invariant up to orientation-reversed mirror image.  Racks were
used by Fenn and Rourke for framed codimension-2 knots and
links.[FennRourke1992]

The name "rack" came from wordplay by Conway and Wraith for the "wrack
and ruin" of forgetting everything but the conjugation operation for a
group.

## Main definitions

* `shelf` is a type with a self-distributive action
* `rack` is a shelf whose action for each element is invertible
* `quandle` is a rack whose action for an element fixes that element
* `quandle.conj` defines a quandle of a group acting on itself by conjugation.
* `shelf_hom` is homomorphisms of shelves, racks, and quandles.
* `rack.envel_group` gives the universal group the rack maps to as a conjugation quandle.
* `rack.opp` gives the rack with the action replaced by its inverse.

## Main statements
* `rack.envel_group` is left adjoint to `quandle.conj` (`to_envel_group.map`).
  The universality statements are `to_envel_group.univ` and `to_envel_group.univ_uniq`.

## Notation

The following notation is localized in `quandles`:

* `x ◃ y` is `shelf.act x y`
* `x ◃⁻¹ y` is `rack.inv_act x y`
* `S →◃ S'` is `shelf_hom S S'`

Use `open_locale quandles` to use these.

## Todo

* If `g` is the Lie algebra of a Lie group `G`, then `(x ◃ y) = Ad (exp x) x` forms a quandle.
* If `X` is a symmetric space, then each point has a corresponding involution that acts on `X`,
  forming a quandle.
* Alexander quandle with `a ◃ b = t * b + (1 - t) * b`, with `a` and `b` elements
  of a module over `Z[t,t⁻¹]`.
* If `G` is a group, `H` a subgroup, and `z` in `H`, then there is a quandle `(G/H;z)` defined by
  `yH ◃ xH = yzy⁻¹xH`.  Every homogeneous quandle (i.e., a quandle `Q` whose automorphism group acts
  transitively on `Q` as a set) is isomorphic to such a quandle.
  There is a generalization to this arbitrary quandles in [Joyce's paper (Theorem 7.2)][Joyce1982].

## Tags

rack, quandle
-/


open MulOpposite

universe u v

/-- A *shelf* is a structure with a self-distributive binary operation.
The binary operation is regarded as a left action of the type on itself.
-/
class Shelf (α : Type u) where
  act : α → α → α
  self_distrib : ∀ {x y z : α}, act x (act y z) = act (act x y) (act x z)
#align shelf Shelf

/-- The type of homomorphisms between shelves.
This is also the notion of rack and quandle homomorphisms.
-/
@[ext]
structure ShelfHom (S₁ : Type _) (S₂ : Type _) [Shelf S₁] [Shelf S₂] where
  toFun : S₁ → S₂
  map_act' : ∀ {x y : S₁}, to_fun (Shelf.act x y) = Shelf.act (to_fun x) (to_fun y)
#align shelf_hom ShelfHom

/-- A *rack* is an automorphic set (a set with an action on itself by
bijections) that is self-distributive.  It is a shelf such that each
element's action is invertible.

The notations `x ◃ y` and `x ◃⁻¹ y` denote the action and the
inverse action, respectively, and they are right associative.
-/
class Rack (α : Type u) extends Shelf α where
  invAct : α → α → α
  left_inv : ∀ x, Function.LeftInverse (inv_act x) (act x)
  right_inv : ∀ x, Function.RightInverse (inv_act x) (act x)
#align rack Rack

-- mathport name: shelf.act
scoped[Quandles] infixr:65 " ◃ " => Shelf.act

-- mathport name: rack.inv_act
scoped[Quandles] infixr:65 " ◃⁻¹ " => Rack.invAct

-- mathport name: shelf_hom
scoped[Quandles] infixr:25 " →◃ " => ShelfHom

open Quandles

namespace Rack

variable {R : Type _} [Rack R]

theorem self_distrib {x y z : R} : x ◃ y ◃ z = (x ◃ y) ◃ x ◃ z :=
  Shelf.self_distrib
#align rack.self_distrib Rack.self_distrib

/-- A rack acts on itself by equivalences.
-/
def act (x : R) : R ≃ R where
  toFun := Shelf.act x
  invFun := invAct x
  left_inv := left_inv x
  right_inv := right_inv x
#align rack.act Rack.act

@[simp]
theorem act_apply (x y : R) : act x y = x ◃ y :=
  rfl
#align rack.act_apply Rack.act_apply

@[simp]
theorem act_symm_apply (x y : R) : (act x).symm y = x ◃⁻¹ y :=
  rfl
#align rack.act_symm_apply Rack.act_symm_apply

@[simp]
theorem invAct_apply (x y : R) : (act x)⁻¹ y = x ◃⁻¹ y :=
  rfl
#align rack.inv_act_apply Rack.invAct_apply

@[simp]
theorem invAct_act_eq (x y : R) : x ◃⁻¹ x ◃ y = y :=
  left_inv x y
#align rack.inv_act_act_eq Rack.invAct_act_eq

@[simp]
theorem act_invAct_eq (x y : R) : x ◃ x ◃⁻¹ y = y :=
  right_inv x y
#align rack.act_inv_act_eq Rack.act_invAct_eq

theorem left_cancel (x : R) {y y' : R} : x ◃ y = x ◃ y' ↔ y = y' :=
  by
  constructor
  apply (act x).Injective
  rintro rfl
  rfl
#align rack.left_cancel Rack.left_cancel

theorem left_cancel_inv (x : R) {y y' : R} : x ◃⁻¹ y = x ◃⁻¹ y' ↔ y = y' :=
  by
  constructor
  apply (act x).symm.Injective
  rintro rfl
  rfl
#align rack.left_cancel_inv Rack.left_cancel_inv

theorem self_distrib_inv {x y z : R} : x ◃⁻¹ y ◃⁻¹ z = (x ◃⁻¹ y) ◃⁻¹ x ◃⁻¹ z :=
  by
  rw [← left_cancel (x ◃⁻¹ y), right_inv, ← left_cancel x, right_inv, self_distrib]
  repeat' rw [right_inv]
#align rack.self_distrib_inv Rack.self_distrib_inv

/-- The *adjoint action* of a rack on itself is `op'`, and the adjoint
action of `x ◃ y` is the conjugate of the action of `y` by the action
of `x`. It is another way to understand the self-distributivity axiom.

This is used in the natural rack homomorphism `to_conj` from `R` to
`conj (R ≃ R)` defined by `op'`.
-/
theorem ad_conj {R : Type _} [Rack R] (x y : R) : act (x ◃ y) = act x * act y * (act x)⁻¹ :=
  by
  rw [eq_mul_inv_iff_mul_eq]; ext z
  apply self_distrib.symm
#align rack.ad_conj Rack.ad_conj

/-- The opposite rack, swapping the roles of `◃` and `◃⁻¹`.
-/
instance oppositeRack : Rack Rᵐᵒᵖ
    where
  act x y := op (invAct (unop x) (unop y))
  self_distrib :=
    MulOpposite.rec' fun x =>
      MulOpposite.rec' fun y =>
        MulOpposite.rec' fun z => by
          simp only [unop_op, op_inj]
          exact self_distrib_inv
  invAct x y := op (Shelf.act (unop x) (unop y))
  left_inv := MulOpposite.rec' fun x => MulOpposite.rec' fun y => by simp
  right_inv := MulOpposite.rec' fun x => MulOpposite.rec' fun y => by simp
#align rack.opposite_rack Rack.oppositeRack

@[simp]
theorem op_act_op_eq {x y : R} : op x ◃ op y = op (x ◃⁻¹ y) :=
  rfl
#align rack.op_act_op_eq Rack.op_act_op_eq

@[simp]
theorem op_invAct_op_eq {x y : R} : op x ◃⁻¹ op y = op (x ◃ y) :=
  rfl
#align rack.op_inv_act_op_eq Rack.op_invAct_op_eq

@[simp]
theorem self_act_act_eq {x y : R} : (x ◃ x) ◃ y = x ◃ y := by rw [← right_inv x y, ← self_distrib]
#align rack.self_act_act_eq Rack.self_act_act_eq

@[simp]
theorem self_invAct_invAct_eq {x y : R} : (x ◃⁻¹ x) ◃⁻¹ y = x ◃⁻¹ y :=
  by
  have h := @self_act_act_eq _ _ (op x) (op y)
  simpa using h
#align rack.self_inv_act_inv_act_eq Rack.self_invAct_invAct_eq

@[simp]
theorem self_act_invAct_eq {x y : R} : (x ◃ x) ◃⁻¹ y = x ◃⁻¹ y :=
  by
  rw [← left_cancel (x ◃ x)]
  rw [right_inv]
  rw [self_act_act_eq]
  rw [right_inv]
#align rack.self_act_inv_act_eq Rack.self_act_invAct_eq

@[simp]
theorem self_invAct_act_eq {x y : R} : (x ◃⁻¹ x) ◃ y = x ◃ y :=
  by
  have h := @self_act_inv_act_eq _ _ (op x) (op y)
  simpa using h
#align rack.self_inv_act_act_eq Rack.self_invAct_act_eq

theorem self_act_eq_iff_eq {x y : R} : x ◃ x = y ◃ y ↔ x = y :=
  by
  constructor; swap; rintro rfl; rfl
  intro h
  trans (x ◃ x) ◃⁻¹ x ◃ x
  rw [← left_cancel (x ◃ x), right_inv, self_act_act_eq]
  rw [h, ← left_cancel (y ◃ y), right_inv, self_act_act_eq]
#align rack.self_act_eq_iff_eq Rack.self_act_eq_iff_eq

theorem self_invAct_eq_iff_eq {x y : R} : x ◃⁻¹ x = y ◃⁻¹ y ↔ x = y :=
  by
  have h := @self_act_eq_iff_eq _ _ (op x) (op y)
  simpa using h
#align rack.self_inv_act_eq_iff_eq Rack.self_invAct_eq_iff_eq

/-- The map `x ↦ x ◃ x` is a bijection.  (This has applications for the
regular isotopy version of the Reidemeister I move for knot diagrams.)
-/
def selfApplyEquiv (R : Type _) [Rack R] : R ≃ R
    where
  toFun x := x ◃ x
  invFun x := x ◃⁻¹ x
  left_inv x := by simp
  right_inv x := by simp
#align rack.self_apply_equiv Rack.selfApplyEquiv

/-- An involutory rack is one for which `rack.op R x` is an involution for every x.
-/
def IsInvolutory (R : Type _) [Rack R] : Prop :=
  ∀ x : R, Function.Involutive (Shelf.act x)
#align rack.is_involutory Rack.IsInvolutory

theorem involutory_invAct_eq_act {R : Type _} [Rack R] (h : IsInvolutory R) (x y : R) :
    x ◃⁻¹ y = x ◃ y := by
  rw [← left_cancel x, right_inv]
  exact ((h x).LeftInverse y).symm
#align rack.involutory_inv_act_eq_act Rack.involutory_invAct_eq_act

/-- An abelian rack is one for which the mediality axiom holds.
-/
def IsAbelian (R : Type _) [Rack R] : Prop :=
  ∀ x y z w : R, (x ◃ y) ◃ z ◃ w = (x ◃ z) ◃ y ◃ w
#align rack.is_abelian Rack.IsAbelian

/-- Associative racks are uninteresting.
-/
theorem assoc_iff_id {R : Type _} [Rack R] {x y z : R} : x ◃ y ◃ z = (x ◃ y) ◃ z ↔ x ◃ z = z :=
  by
  rw [self_distrib]
  rw [left_cancel]
#align rack.assoc_iff_id Rack.assoc_iff_id

end Rack

namespace ShelfHom

variable {S₁ : Type _} {S₂ : Type _} {S₃ : Type _} [Shelf S₁] [Shelf S₂] [Shelf S₃]

instance : CoeFun (S₁ →◃ S₂) fun _ => S₁ → S₂ :=
  ⟨ShelfHom.toFun⟩

@[simp]
theorem toFun_eq_coe (f : S₁ →◃ S₂) : f.toFun = f :=
  rfl
#align shelf_hom.to_fun_eq_coe ShelfHom.toFun_eq_coe

@[simp]
theorem map_act (f : S₁ →◃ S₂) {x y : S₁} : f (x ◃ y) = f x ◃ f y :=
  map_act' f
#align shelf_hom.map_act ShelfHom.map_act

/-- The identity homomorphism -/
def id (S : Type _) [Shelf S] : S →◃ S where
  toFun := id
  map_act' := by simp
#align shelf_hom.id ShelfHom.id

instance inhabited (S : Type _) [Shelf S] : Inhabited (S →◃ S) :=
  ⟨id S⟩
#align shelf_hom.inhabited ShelfHom.inhabited

/-- The composition of shelf homomorphisms -/
def comp (g : S₂ →◃ S₃) (f : S₁ →◃ S₂) : S₁ →◃ S₃
    where
  toFun := g.toFun ∘ f.toFun
  map_act' := by simp
#align shelf_hom.comp ShelfHom.comp

@[simp]
theorem comp_apply (g : S₂ →◃ S₃) (f : S₁ →◃ S₂) (x : S₁) : (g.comp f) x = g (f x) :=
  rfl
#align shelf_hom.comp_apply ShelfHom.comp_apply

end ShelfHom

/-- A quandle is a rack such that each automorphism fixes its corresponding element.
-/
class Quandle (α : Type _) extends Rack α where
  fix : ∀ {x : α}, act x x = x
#align quandle Quandle

namespace Quandle

open Rack

variable {Q : Type _} [Quandle Q]

attribute [simp] fix

@[simp]
theorem fix_inv {x : Q} : x ◃⁻¹ x = x :=
  by
  rw [← left_cancel x]
  simp
#align quandle.fix_inv Quandle.fix_inv

instance oppositeQuandle : Quandle Qᵐᵒᵖ
    where fix x := by
    induction x using MulOpposite.rec'
    simp
#align quandle.opposite_quandle Quandle.oppositeQuandle

/-- The conjugation quandle of a group.  Each element of the group acts by
the corresponding inner automorphism.
-/
@[nolint has_nonempty_instance]
def Conj (G : Type _) :=
  G
#align quandle.conj Quandle.Conj

instance Conj.quandle (G : Type _) [Group G] : Quandle (Conj G)
    where
  act x := @MulAut.conj G _ x
  self_distrib x y z := by
    dsimp only [[anonymous], MulAut.conj_apply, conj]
    group
  invAct x := (@MulAut.conj G _ x).symm
  left_inv x y := by
    dsimp [act, conj]
    group
  right_inv x y := by
    dsimp [act, conj]
    group
  fix x := by simp
#align quandle.conj.quandle Quandle.Conj.quandle

@[simp]
theorem conj_act_eq_conj {G : Type _} [Group G] (x y : Conj G) :
    x ◃ y = ((x : G) * (y : G) * (x : G)⁻¹ : G) :=
  rfl
#align quandle.conj_act_eq_conj Quandle.conj_act_eq_conj

theorem conj_swap {G : Type _} [Group G] (x y : Conj G) : x ◃ y = y ↔ y ◃ x = x :=
  by
  dsimp [conj] at *; constructor
  repeat' intro h; conv_rhs => rw [eq_mul_inv_of_mul_eq (eq_mul_inv_of_mul_eq h)]; simp
#align quandle.conj_swap Quandle.conj_swap

/-- `conj` is functorial
-/
def Conj.map {G : Type _} {H : Type _} [Group G] [Group H] (f : G →* H) : Conj G →◃ Conj H
    where
  toFun := f
  map_act' := by simp
#align quandle.conj.map Quandle.Conj.map

instance {G : Type _} {H : Type _} [Group G] [Group H] : HasLift (G →* H) (Conj G →◃ Conj H)
    where lift := Conj.map

/-- The dihedral quandle. This is the conjugation quandle of the dihedral group restrict to flips.

Used for Fox n-colorings of knots.
-/
@[nolint has_nonempty_instance]
def Dihedral (n : ℕ) :=
  ZMod n
#align quandle.dihedral Quandle.Dihedral

/-- The operation for the dihedral quandle.  It does not need to be an equivalence
because it is an involution (see `dihedral_act.inv`).
-/
def dihedralAct (n : ℕ) (a : ZMod n) : ZMod n → ZMod n := fun b => 2 * a - b
#align quandle.dihedral_act Quandle.dihedralAct

theorem dihedralAct.inv (n : ℕ) (a : ZMod n) : Function.Involutive (dihedralAct n a) :=
  by
  intro b
  dsimp [dihedral_act]
  ring
#align quandle.dihedral_act.inv Quandle.dihedralAct.inv

instance (n : ℕ) : Quandle (Dihedral n)
    where
  act := dihedralAct n
  self_distrib x y z := by dsimp [dihedral_act]; ring
  invAct := dihedralAct n
  left_inv x := (dihedralAct.inv n x).LeftInverse
  right_inv x := (dihedralAct.inv n x).RightInverse
  fix x := by dsimp [dihedral_act]; ring

end Quandle

namespace Rack

/-- This is the natural rack homomorphism to the conjugation quandle of the group `R ≃ R`
that acts on the rack.
-/
def toConj (R : Type _) [Rack R] : R →◃ Quandle.Conj (R ≃ R)
    where
  toFun := act
  map_act' := ad_conj
#align rack.to_conj Rack.toConj

section EnvelGroup

/-!
### Universal enveloping group of a rack

The universal enveloping group `envel_group R` of a rack `R` is the
universal group such that every rack homomorphism `R →◃ conj G` is
induced by a unique group homomorphism `envel_group R →* G`.
For quandles, Joyce called this group `AdConj R`.

The `envel_group` functor is left adjoint to the `conj` forgetful
functor, and the way we construct the enveloping group is via a
technique that should work for left adjoints of forgetful functors in
general.  It involves thinking a little about 2-categories, but the
payoff is that the map `envel_group R →* G` has a nice description.

Let's think of a group as being a one-object category.  The first step
is to define `pre_envel_group`, which gives formal expressions for all
the 1-morphisms and includes the unit element, elements of `R`,
multiplication, and inverses.  To introduce relations, the second step
is to define `pre_envel_group_rel'`, which gives formal expressions
for all 2-morphisms between the 1-morphisms.  The 2-morphisms include
associativity, multiplication by the unit, multiplication by inverses,
compatibility with multiplication and inverses (`congr_mul` and
`congr_inv`), the axioms for an equivalence relation, and,
importantly, the relationship between conjugation and the rack action
(see `rack.ad_conj`).

None of this forms a 2-category yet, for example due to lack of
associativity of `trans`.  The `pre_envel_group_rel` relation is a
`Prop`-valued version of `pre_envel_group_rel'`, and making it
`Prop`-valued essentially introduces enough 3-isomorphisms so that
every pair of compatible 2-morphisms is isomorphic.  Now, while
composition in `pre_envel_group` does not strictly satisfy the category
axioms, `pre_envel_group` and `pre_envel_group_rel'` do form a weak
2-category.

Since we just want a 1-category, the last step is to quotient
`pre_envel_group` by `pre_envel_group_rel'`, and the result is the
group `envel_group`.

For a homomorphism `f : R →◃ conj G`, how does
`envel_group.map f : envel_group R →* G` work?  Let's think of `G` as
being a 2-category with one object, a 1-morphism per element of `G`,
and a single 2-morphism called `eq.refl` for each 1-morphism.  We
define the map using a "higher `quotient.lift`" -- not only do we
evaluate elements of `pre_envel_group` as expressions in `G` (this is
`to_envel_group.map_aux`), but we evaluate elements of
`pre_envel_group'` as expressions of 2-morphisms of `G` (this is
`to_envel_group.map_aux.well_def`).  That is to say,
`to_envel_group.map_aux.well_def` recursively evaluates formal
expressions of 2-morphisms as equality proofs in `G`.  Now that all
morphisms are accounted for, the map descends to a homomorphism
`envel_group R →* G`.

Note: `Type`-valued relations are not common.  The fact it is
`Type`-valued is what makes `to_envel_group.map_aux.well_def` have
well-founded recursion.
-/


/-- Free generators of the enveloping group.
-/
inductive PreEnvelGroup (R : Type u) : Type u
  | Unit : pre_envel_group
  | incl (x : R) : pre_envel_group
  | mul (a b : pre_envel_group) : pre_envel_group
  | inv (a : pre_envel_group) : pre_envel_group
#align rack.pre_envel_group Rack.PreEnvelGroup

instance PreEnvelGroup.inhabited (R : Type u) : Inhabited (PreEnvelGroup R) :=
  ⟨PreEnvelGroup.unit⟩
#align rack.pre_envel_group.inhabited Rack.PreEnvelGroup.inhabited

open PreEnvelGroup

/-- Relations for the enveloping group. This is a type-valued relation because
`to_envel_group.map_aux.well_def` inducts on it to show `to_envel_group.map`
is well-defined.  The relation `pre_envel_group_rel` is the `Prop`-valued version,
which is used to define `envel_group` itself.
-/
inductive PreEnvelGroupRel' (R : Type u) [Rack R] : PreEnvelGroup R → PreEnvelGroup R → Type u
  | refl {a : PreEnvelGroup R} : pre_envel_group_rel' a a
  | symm {a b : PreEnvelGroup R} (hab : pre_envel_group_rel' a b) : pre_envel_group_rel' b a
  |
  trans {a b c : PreEnvelGroup R} (hab : pre_envel_group_rel' a b)
    (hbc : pre_envel_group_rel' b c) : pre_envel_group_rel' a c
  |
  congr_mul {a b a' b' : PreEnvelGroup R} (ha : pre_envel_group_rel' a a')
    (hb : pre_envel_group_rel' b b') : pre_envel_group_rel' (mul a b) (mul a' b')
  |
  congr_inv {a a' : PreEnvelGroup R} (ha : pre_envel_group_rel' a a') :
    pre_envel_group_rel' (inv a) (inv a')
  | assoc (a b c : PreEnvelGroup R) : pre_envel_group_rel' (mul (mul a b) c) (mul a (mul b c))
  | one_mul (a : PreEnvelGroup R) : pre_envel_group_rel' (mul Unit a) a
  | mul_one (a : PreEnvelGroup R) : pre_envel_group_rel' (mul a Unit) a
  | mul_left_inv (a : PreEnvelGroup R) : pre_envel_group_rel' (mul (inv a) a) Unit
  |
  act_incl (x y : R) :
    pre_envel_group_rel' (mul (mul (incl x) (incl y)) (inv (incl x))) (incl (x ◃ y))
#align rack.pre_envel_group_rel' Rack.PreEnvelGroupRel'

instance PreEnvelGroupRel'.inhabited (R : Type u) [Rack R] :
    Inhabited (PreEnvelGroupRel' R Unit Unit) :=
  ⟨PreEnvelGroupRel'.refl⟩
#align rack.pre_envel_group_rel'.inhabited Rack.PreEnvelGroupRel'.inhabited

/--
The `pre_envel_group_rel` relation as a `Prop`.  Used as the relation for `pre_envel_group.setoid`.
-/
inductive PreEnvelGroupRel (R : Type u) [Rack R] : PreEnvelGroup R → PreEnvelGroup R → Prop
  | Rel {a b : PreEnvelGroup R} (r : PreEnvelGroupRel' R a b) : pre_envel_group_rel a b
#align rack.pre_envel_group_rel Rack.PreEnvelGroupRel

/-- A quick way to convert a `pre_envel_group_rel'` to a `pre_envel_group_rel`.
-/
theorem PreEnvelGroupRel'.rel {R : Type u} [Rack R] {a b : PreEnvelGroup R} :
    PreEnvelGroupRel' R a b → PreEnvelGroupRel R a b :=
  pre_envel_group_rel.rel
#align rack.pre_envel_group_rel'.rel Rack.PreEnvelGroupRel'.rel

@[refl]
theorem PreEnvelGroupRel.refl {R : Type u} [Rack R] {a : PreEnvelGroup R} :
    PreEnvelGroupRel R a a :=
  PreEnvelGroupRel.rel PreEnvelGroupRel'.refl
#align rack.pre_envel_group_rel.refl Rack.PreEnvelGroupRel.refl

@[symm]
theorem PreEnvelGroupRel.symm {R : Type u} [Rack R] {a b : PreEnvelGroup R} :
    PreEnvelGroupRel R a b → PreEnvelGroupRel R b a
  | ⟨r⟩ => r.symm.Rel
#align rack.pre_envel_group_rel.symm Rack.PreEnvelGroupRel.symm

@[trans]
theorem PreEnvelGroupRel.trans {R : Type u} [Rack R] {a b c : PreEnvelGroup R} :
    PreEnvelGroupRel R a b → PreEnvelGroupRel R b c → PreEnvelGroupRel R a c
  | ⟨rab⟩, ⟨rbc⟩ => (rab.trans rbc).Rel
#align rack.pre_envel_group_rel.trans Rack.PreEnvelGroupRel.trans

instance PreEnvelGroup.setoid (R : Type _) [Rack R] : Setoid (PreEnvelGroup R)
    where
  R := PreEnvelGroupRel R
  iseqv := by
    constructor; apply pre_envel_group_rel.refl
    constructor; apply pre_envel_group_rel.symm
    apply pre_envel_group_rel.trans
#align rack.pre_envel_group.setoid Rack.PreEnvelGroup.setoid

/-- The universal enveloping group for the rack R.
-/
def EnvelGroup (R : Type _) [Rack R] :=
  Quotient (PreEnvelGroup.setoid R)
#align rack.envel_group Rack.EnvelGroup

-- Define the `group` instances in two steps so `inv` can be inferred correctly.
-- TODO: is there a non-invasive way of defining the instance directly?
instance (R : Type _) [Rack R] : DivInvMonoid (EnvelGroup R)
    where
  mul a b :=
    Quotient.liftOn₂ a b (fun a b => ⟦PreEnvelGroup.mul a b⟧) fun a b a' b' ⟨ha⟩ ⟨hb⟩ =>
      Quotient.sound (PreEnvelGroupRel'.congr_mul ha hb).Rel
  one := ⟦Unit⟧
  inv a :=
    Quotient.liftOn a (fun a => ⟦PreEnvelGroup.inv a⟧) fun a a' ⟨ha⟩ =>
      Quotient.sound (PreEnvelGroupRel'.congr_inv ha).Rel
  mul_assoc a b c :=
    Quotient.induction_on₃ a b c fun a b c => Quotient.sound (PreEnvelGroupRel'.assoc a b c).Rel
  one_mul a := Quotient.inductionOn a fun a => Quotient.sound (PreEnvelGroupRel'.one_mul a).Rel
  mul_one a := Quotient.inductionOn a fun a => Quotient.sound (PreEnvelGroupRel'.mul_one a).Rel

instance (R : Type _) [Rack R] : Group (EnvelGroup R) :=
  { EnvelGroup.divInvMonoid _ with
    mul_left_inv := fun a =>
      Quotient.inductionOn a fun a => Quotient.sound (PreEnvelGroupRel'.mul_left_inv a).Rel }

instance EnvelGroup.inhabited (R : Type _) [Rack R] : Inhabited (EnvelGroup R) :=
  ⟨1⟩
#align rack.envel_group.inhabited Rack.EnvelGroup.inhabited

/-- The canonical homomorphism from a rack to its enveloping group.
Satisfies universal properties given by `to_envel_group.map` and `to_envel_group.univ`.
-/
def toEnvelGroup (R : Type _) [Rack R] : R →◃ Quandle.Conj (EnvelGroup R)
    where
  toFun x := ⟦incl x⟧
  map_act' x y := Quotient.sound (PreEnvelGroupRel'.act_incl x y).symm.Rel
#align rack.to_envel_group Rack.toEnvelGroup

/-- The preliminary definition of the induced map from the enveloping group.
See `to_envel_group.map`.
-/
def toEnvelGroup.mapAux {R : Type _} [Rack R] {G : Type _} [Group G] (f : R →◃ Quandle.Conj G) :
    PreEnvelGroup R → G
  | Unit => 1
  | incl x => f x
  | mul a b => to_envel_group.map_aux a * to_envel_group.map_aux b
  | inv a => (to_envel_group.map_aux a)⁻¹
#align rack.to_envel_group.map_aux Rack.toEnvelGroup.mapAux

namespace ToEnvelGroup.MapAux

open PreEnvelGroupRel'

/-- Show that `to_envel_group.map_aux` sends equivalent expressions to equal terms.
-/
theorem well_def {R : Type _} [Rack R] {G : Type _} [Group G] (f : R →◃ Quandle.Conj G) :
    ∀ {a b : PreEnvelGroup R},
      PreEnvelGroupRel' R a b → toEnvelGroup.mapAux f a = toEnvelGroup.mapAux f b
  | a, b, refl => rfl
  | a, b, symm h => (well_def h).symm
  | a, b, trans hac hcb => Eq.trans (well_def hac) (well_def hcb)
  | _, _, congr_mul ha hb => by simp [to_envel_group.map_aux, well_def ha, well_def hb]
  | _, _, congr_inv ha => by simp [to_envel_group.map_aux, well_def ha]
  | _, _, assoc a b c => by apply mul_assoc
  | _, _, one_mul a => by simp [to_envel_group.map_aux]
  | _, _, mul_one a => by simp [to_envel_group.map_aux]
  | _, _, mul_left_inv a => by simp [to_envel_group.map_aux]
  | _, _, act_incl x y => by simp [to_envel_group.map_aux]
#align rack.to_envel_group.map_aux.well_def Rack.toEnvelGroup.mapAux.well_def

end ToEnvelGroup.MapAux

/-- Given a map from a rack to a group, lift it to being a map from the enveloping group.
More precisely, the `envel_group` functor is left adjoint to `quandle.conj`.
-/
def toEnvelGroup.map {R : Type _} [Rack R] {G : Type _} [Group G] :
    (R →◃ Quandle.Conj G) ≃ (EnvelGroup R →* G)
    where
  toFun f :=
    { toFun := fun x =>
        Quotient.liftOn x (toEnvelGroup.mapAux f) fun a b ⟨hab⟩ =>
          toEnvelGroup.mapAux.well_def f hab
      map_one' :=
        by
        change Quotient.liftOn ⟦Rack.PreEnvelGroup.unit⟧ (to_envel_group.map_aux f) _ = 1
        simp [to_envel_group.map_aux]
      map_mul' := fun x y =>
        Quotient.induction_on₂ x y fun x y =>
          by
          change Quotient.liftOn ⟦mul x y⟧ (to_envel_group.map_aux f) _ = _
          simp [to_envel_group.map_aux] }
  invFun F := (Quandle.Conj.map F).comp (toEnvelGroup R)
  left_inv f := by
    ext
    rfl
  right_inv F :=
    MonoidHom.ext fun x =>
      Quotient.inductionOn x fun x => by
        induction x
        · exact F.map_one.symm
        · rfl
        · have hm : ⟦x_a.mul x_b⟧ = @Mul.mul (envel_group R) _ ⟦x_a⟧ ⟦x_b⟧ := rfl
          rw [hm, F.map_mul, MonoidHom.map_mul, ← x_ih_a, ← x_ih_b]
        · have hm : ⟦x_a.inv⟧ = @Inv.inv (envel_group R) _ ⟦x_a⟧ := rfl
          rw [hm, F.map_inv, MonoidHom.map_inv, x_ih]
#align rack.to_envel_group.map Rack.toEnvelGroup.map

/-- Given a homomorphism from a rack to a group, it factors through the enveloping group.
-/
theorem toEnvelGroup.univ (R : Type _) [Rack R] (G : Type _) [Group G] (f : R →◃ Quandle.Conj G) :
    (Quandle.Conj.map (toEnvelGroup.map f)).comp (toEnvelGroup R) = f :=
  toEnvelGroup.map.symm_apply_apply f
#align rack.to_envel_group.univ Rack.toEnvelGroup.univ

/-- The homomorphism `to_envel_group.map f` is the unique map that fits into the commutative
triangle in `to_envel_group.univ`.
-/
theorem toEnvelGroup.univ_uniq (R : Type _) [Rack R] (G : Type _) [Group G]
    (f : R →◃ Quandle.Conj G) (g : EnvelGroup R →* G)
    (h : f = (Quandle.Conj.map g).comp (toEnvelGroup R)) : g = toEnvelGroup.map f :=
  h.symm ▸ (toEnvelGroup.map.apply_symm_apply g).symm
#align rack.to_envel_group.univ_uniq Rack.toEnvelGroup.univ_uniq

/-- The induced group homomorphism from the enveloping group into bijections of the rack,
using `rack.to_conj`. Satisfies the property `envel_action_prop`.

This gives the rack `R` the structure of an augmented rack over `envel_group R`.
-/
def envelAction {R : Type _} [Rack R] : EnvelGroup R →* R ≃ R :=
  toEnvelGroup.map (toConj R)
#align rack.envel_action Rack.envelAction

@[simp]
theorem envelAction_prop {R : Type _} [Rack R] (x y : R) :
    envelAction (toEnvelGroup R x) y = x ◃ y :=
  rfl
#align rack.envel_action_prop Rack.envelAction_prop

end EnvelGroup

end Rack

