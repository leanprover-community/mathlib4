/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Algebra.Group.End
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

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
links in [FennRourke1992]. Unital shelves are discussed in [crans2017].

The name "rack" came from wordplay by Conway and Wraith for the "wrack
and ruin" of forgetting everything but the conjugation operation for a
group.

## Main definitions

* `Shelf` is a type with a self-distributive action
* `UnitalShelf` is a shelf with a left and right unit
* `Rack` is a shelf whose action for each element is invertible
* `Quandle` is a rack whose action for an element fixes that element
* `Quandle.conj` defines a quandle of a group acting on itself by conjugation.
* `ShelfHom` is homomorphisms of shelves, racks, and quandles.
* `Rack.EnvelGroup` gives the universal group the rack maps to as a conjugation quandle.
* `Rack.oppositeRack` gives the rack with the action replaced by its inverse.

## Main statements
* `Rack.EnvelGroup` is left adjoint to `Quandle.Conj` (`toEnvelGroup.map`).
  The universality statements are `toEnvelGroup.univ` and `toEnvelGroup.univ_uniq`.

## Implementation notes
"Unital racks" are uninteresting (see `Rack.assoc_iff_id`, `UnitalShelf.assoc`), so we do not
define them.

## Notation

The following notation is localized in `quandles`:

* `x ◃ y` is `Shelf.act x y`
* `x ◃⁻¹ y` is `Rack.inv_act x y`
* `S →◃ S'` is `ShelfHom S S'`

Use `open quandles` to use these.

## TODO

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

/-- A *Shelf* is a structure with a self-distributive binary operation.
The binary operation is regarded as a left action of the type on itself.
-/
class Shelf (α : Type u) where
  /-- The action of the `Shelf` over `α` -/
  act : α → α → α
  /-- A verification that `act` is self-distributive -/
  self_distrib : ∀ {x y z : α}, act x (act y z) = act (act x y) (act x z)

/--
A *unital shelf* is a shelf equipped with an element `1` such that, for all elements `x`,
we have both `x ◃ 1` and `1 ◃ x` equal `x`.
-/
class UnitalShelf (α : Type u) extends Shelf α, One α where
  one_act : ∀ a : α, act 1 a = a
  act_one : ∀ a : α, act a 1 = a

/-- The type of homomorphisms between shelves.
This is also the notion of rack and quandle homomorphisms.
-/
@[ext]
structure ShelfHom (S₁ : Type*) (S₂ : Type*) [Shelf S₁] [Shelf S₂] where
  /-- The function under the Shelf Homomorphism -/
  toFun : S₁ → S₂
  /-- The homomorphism property of a Shelf Homomorphism -/
  map_act' : ∀ {x y : S₁}, toFun (Shelf.act x y) = Shelf.act (toFun x) (toFun y)

/-- A *rack* is an automorphic set (a set with an action on itself by
bijections) that is self-distributive.  It is a shelf such that each
element's action is invertible.

The notations `x ◃ y` and `x ◃⁻¹ y` denote the action and the
inverse action, respectively, and they are right associative..............................................
-/
class Rack (α : Type u) extends Shelf α where
  /-- The inverse actions of the elements -/
  invAct : α → α → α
  /-- Proof of left inverse -/
  left_inv : ∀ x, Function.LeftInverse (invAct x) (act x)
  /-- Proof of right inverse -/
  right_inv : ∀ x, Function.RightInverse (invAct x) (act x)

/-- Action of a Shelf -/
scoped[Quandles] infixr:65 " ◃ " => Shelf.act

/-- Inverse Action of a Rack -/
scoped[Quandles] infixr:65 " ◃⁻¹ " => Rack.invAct

/-- Shelf Homomorphism -/
scoped[Quandles] infixr:25 " →◃ " => ShelfHom

open Quandles

namespace UnitalShelf
open Shelf

variable {S : Type*} [UnitalShelf S]

/--
A monoid is *graphic* if, for all `x` and `y`, the *graphic identity*
`(x * y) * x = x * y` holds.  For a unital shelf, this graphic
identity holds.
-/
lemma act_act_self_eq (x y : S) : (x ◃ y) ◃ x = x ◃ y := by
  have h : (x ◃ y) ◃ x = (x ◃ y) ◃ (x ◃ 1) := by rw [act_one]
  rw [h, ← Shelf.self_distrib, act_one]

lemma act_idem (x : S) : (x ◃ x) = x := by rw [← act_one x, ← Shelf.self_distrib, act_one]

lemma act_self_act_eq (x y : S) : x ◃ (x ◃ y) = x ◃ y := by
  have h : x ◃ (x ◃ y) = (x ◃ 1) ◃ (x ◃ y) := by rw [act_one]
  rw [h, ← Shelf.self_distrib, one_act]

/--
The associativity of a unital shelf comes for free.
-/
lemma assoc (x y z : S) : (x ◃ y) ◃ z = x ◃ y ◃ z := by
  rw [self_distrib, self_distrib, act_act_self_eq, act_self_act_eq]

end UnitalShelf

namespace Rack

variable {R : Type*} [Rack R]

export Shelf (self_distrib)

/-- A rack acts on itself by equivalences. -/
def act' (x : R) : R ≃ R where
  toFun := Shelf.act x
  invFun := invAct x
  left_inv := left_inv x
  right_inv := right_inv x

@[simp]
theorem act'_apply (x y : R) : act' x y = x ◃ y :=
  rfl

@[simp]
theorem act'_symm_apply (x y : R) : (act' x).symm y = x ◃⁻¹ y :=
  rfl

@[simp]
theorem invAct_apply (x y : R) : (act' x)⁻¹ y = x ◃⁻¹ y :=
  rfl

@[simp]
theorem invAct_act_eq (x y : R) : x ◃⁻¹ x ◃ y = y :=
  left_inv x y

@[simp]
theorem act_invAct_eq (x y : R) : x ◃ x ◃⁻¹ y = y :=
  right_inv x y

theorem left_cancel (x : R) {y y' : R} : x ◃ y = x ◃ y' ↔ y = y' := by
  constructor
  · apply (act' x).injective
  rintro rfl
  rfl

theorem left_cancel_inv (x : R) {y y' : R} : x ◃⁻¹ y = x ◃⁻¹ y' ↔ y = y' := by
  constructor
  · apply (act' x).symm.injective
  rintro rfl
  rfl

theorem self_distrib_inv {x y z : R} : x ◃⁻¹ y ◃⁻¹ z = (x ◃⁻¹ y) ◃⁻¹ x ◃⁻¹ z := by
  rw [← left_cancel (x ◃⁻¹ y), right_inv, ← left_cancel x, right_inv, self_distrib]
  repeat' rw [right_inv]

/-- The *adjoint action* of a rack on itself is `op'`, and the adjoint
action of `x ◃ y` is the conjugate of the action of `y` by the action
of `x`. It is another way to understand the self-distributivity axiom.

This is used in the natural rack homomorphism `toConj` from `R` to
`Conj (R ≃ R)` defined by `op'`.
-/
theorem ad_conj {R : Type*} [Rack R] (x y : R) : act' (x ◃ y) = act' x * act' y * (act' x)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]; ext z
  apply self_distrib.symm

/-- The opposite rack, swapping the roles of `◃` and `◃⁻¹`.
-/
instance oppositeRack : Rack Rᵐᵒᵖ where
  act x y := op (invAct (unop x) (unop y))
  self_distrib := by
    intro x y z
    induction x
    induction y
    induction z
    simp only [op_inj, unop_op]
    rw [self_distrib_inv]
  invAct x y := op (Shelf.act (unop x) (unop y))
  left_inv := MulOpposite.rec' fun x => MulOpposite.rec' fun y => by simp
  right_inv := MulOpposite.rec' fun x => MulOpposite.rec' fun y => by simp

@[simp]
theorem op_act_op_eq {x y : R} : op x ◃ op y = op (x ◃⁻¹ y) :=
  rfl

@[simp]
theorem op_invAct_op_eq {x y : R} : op x ◃⁻¹ op y = op (x ◃ y) :=
  rfl

@[simp]
theorem self_act_act_eq {x y : R} : (x ◃ x) ◃ y = x ◃ y := by rw [← right_inv x y, ← self_distrib]

@[simp]
theorem self_invAct_invAct_eq {x y : R} : (x ◃⁻¹ x) ◃⁻¹ y = x ◃⁻¹ y := by
  have h := @self_act_act_eq _ _ (op x) (op y)
  simpa using h

@[simp]
theorem self_act_invAct_eq {x y : R} : (x ◃ x) ◃⁻¹ y = x ◃⁻¹ y := by
  rw [← left_cancel (x ◃ x)]
  rw [right_inv]
  rw [self_act_act_eq]
  rw [right_inv]

@[simp]
theorem self_invAct_act_eq {x y : R} : (x ◃⁻¹ x) ◃ y = x ◃ y := by
  have h := @self_act_invAct_eq _ _ (op x) (op y)
  simpa using h

theorem self_act_eq_iff_eq {x y : R} : x ◃ x = y ◃ y ↔ x = y := by
  constructor; swap
  · rintro rfl; rfl
  intro h
  trans (x ◃ x) ◃⁻¹ x ◃ x
  · rw [← left_cancel (x ◃ x), right_inv, self_act_act_eq]
  · rw [h, ← left_cancel (y ◃ y), right_inv, self_act_act_eq]

theorem self_invAct_eq_iff_eq {x y : R} : x ◃⁻¹ x = y ◃⁻¹ y ↔ x = y := by
  have h := @self_act_eq_iff_eq _ _ (op x) (op y)
  simpa using h

/-- The map `x ↦ x ◃ x` is a bijection.  (This has applications for the
regular isotopy version of the Reidemeister I move for knot diagrams.)
-/
def selfApplyEquiv (R : Type*) [Rack R] : R ≃ R where
  toFun x := x ◃ x
  invFun x := x ◃⁻¹ x
  left_inv x := by simp
  right_inv x := by simp

/-- An involutory rack is one for which `Rack.oppositeRack R x` is an involution for every x.
-/
def IsInvolutory (R : Type*) [Rack R] : Prop :=
  ∀ x : R, Function.Involutive (Shelf.act x)

theorem involutory_invAct_eq_act {R : Type*} [Rack R] (h : IsInvolutory R) (x y : R) :
    x ◃⁻¹ y = x ◃ y := by
  rw [← left_cancel x, right_inv, h x]

/-- An abelian rack is one for which the mediality axiom holds.
-/
def IsAbelian (R : Type*) [Rack R] : Prop :=
  ∀ x y z w : R, (x ◃ y) ◃ z ◃ w = (x ◃ z) ◃ y ◃ w

/-- Associative racks are uninteresting.
-/
theorem assoc_iff_id {R : Type*} [Rack R] {x y z : R} : x ◃ y ◃ z = (x ◃ y) ◃ z ↔ x ◃ z = z := by
  rw [self_distrib]
  rw [left_cancel]

end Rack

namespace ShelfHom

variable {S₁ : Type*} {S₂ : Type*} {S₃ : Type*} [Shelf S₁] [Shelf S₂] [Shelf S₃]

instance : FunLike (S₁ →◃ S₂) S₁ S₂ where
  coe := toFun
  coe_injective' | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[simp] theorem toFun_eq_coe (f : S₁ →◃ S₂) : f.toFun = f := rfl

@[simp]
theorem map_act (f : S₁ →◃ S₂) {x y : S₁} : f (x ◃ y) = f x ◃ f y :=
  map_act' f

/-- The identity homomorphism -/
def id (S : Type*) [Shelf S] : S →◃ S where
  toFun := fun x => x
  map_act' := by simp

instance inhabited (S : Type*) [Shelf S] : Inhabited (S →◃ S) :=
  ⟨id S⟩

/-- The composition of shelf homomorphisms -/
def comp (g : S₂ →◃ S₃) (f : S₁ →◃ S₂) : S₁ →◃ S₃ where
  toFun := g.toFun ∘ f.toFun
  map_act' := by simp

@[simp]
theorem comp_apply (g : S₂ →◃ S₃) (f : S₁ →◃ S₂) (x : S₁) : (g.comp f) x = g (f x) :=
  rfl

end ShelfHom

/-- A quandle is a rack such that each automorphism fixes its corresponding element.
-/
class Quandle (α : Type*) extends Rack α where
  /-- The fixing property of a Quandle -/
  fix : ∀ {x : α}, act x x = x

namespace Quandle

open Rack

variable {Q : Type*} [Quandle Q]

attribute [simp] fix

@[simp]
theorem fix_inv {x : Q} : x ◃⁻¹ x = x := by
  rw [← left_cancel x]
  simp

instance oppositeQuandle : Quandle Qᵐᵒᵖ where
  fix := by
    intro x
    induction x
    simp

/-- The conjugation quandle of a group.  Each element of the group acts by
the corresponding inner automorphism. -/
abbrev Conj (G : Type*) := G

instance Conj.quandle (G : Type*) [Group G] : Quandle (Conj G) where
  act x := @MulAut.conj G _ x
  self_distrib := by
    intro x y z
    dsimp only [MulAut.conj_apply]
    simp [mul_assoc]
  invAct x := (@MulAut.conj G _ x).symm
  left_inv x y := by
    simp [mul_assoc]
  right_inv x y := by
    simp [mul_assoc]
  fix := by simp

@[simp]
theorem conj_act_eq_conj {G : Type*} [Group G] (x y : Conj G) :
    x ◃ y = ((x : G) * (y : G) * (x : G)⁻¹ : G) :=
  rfl

theorem conj_swap {G : Type*} [Group G] (x y : Conj G) : x ◃ y = y ↔ y ◃ x = x := by
  dsimp [Conj] at *; constructor
  repeat' intro h; conv_rhs => rw [eq_mul_inv_of_mul_eq (eq_mul_inv_of_mul_eq h)]; simp

/-- `Conj` is functorial
-/
def Conj.map {G : Type*} {H : Type*} [Group G] [Group H] (f : G →* H) : Conj G →◃ Conj H where
  toFun := f
  map_act' := by simp

/-- The dihedral quandle. This is the conjugation quandle of the dihedral group restricted to flips.

Used for Fox n-colorings of knots. -/
def Dihedral (n : ℕ) :=
  ZMod n

/-- The operation for the dihedral quandle.  It does not need to be an equivalence
because it is an involution (see `dihedralAct.inv`). -/
def dihedralAct (n : ℕ) (a : ZMod n) : ZMod n → ZMod n := fun b => 2 * a - b

theorem dihedralAct.inv (n : ℕ) (a : ZMod n) : Function.Involutive (dihedralAct n a) := by
  intro b
  dsimp only [dihedralAct]
  simp

instance (n : ℕ) : Quandle (Dihedral n) where
  act := dihedralAct n
  self_distrib := by
    intro x y z
    simp only [dihedralAct]
    ring_nf
  invAct := dihedralAct n
  left_inv x := (dihedralAct.inv n x).leftInverse
  right_inv x := (dihedralAct.inv n x).rightInverse
  fix := by
    intro x
    simp only [dihedralAct]
    ring_nf

end Quandle

namespace Rack

/-- This is the natural rack homomorphism to the conjugation quandle of the group `R ≃ R`
that acts on the rack. -/
def toConj (R : Type*) [Rack R] : R →◃ Quandle.Conj (R ≃ R) where
  toFun := act'
  map_act' := by
    intro x y
    exact ad_conj x y

section EnvelGroup

/-!
### Universal enveloping group of a rack

The universal enveloping group `EnvelGroup R` of a rack `R` is the
universal group such that every rack homomorphism `R →◃ conj G` is
induced by a unique group homomorphism `EnvelGroup R →* G`.
For quandles, Joyce called this group `AdConj R`.

The `EnvelGroup` functor is left adjoint to the `Conj` forgetful
functor, and the way we construct the enveloping group is via a
technique that should work for left adjoints of forgetful functors in
general.  It involves thinking a little about 2-categories, but the
payoff is that the map `EnvelGroup R →* G` has a nice description.

Let's think of a group as being a one-object category.  The first step
is to define `PreEnvelGroup`, which gives formal expressions for all
the 1-morphisms and includes the unit element, elements of `R`,
multiplication, and inverses.  To introduce relations, the second step
is to define `PreEnvelGroupRel'`, which gives formal expressions
for all 2-morphisms between the 1-morphisms.  The 2-morphisms include
associativity, multiplication by the unit, multiplication by inverses,
compatibility with multiplication and inverses (`congr_mul` and
`congr_inv`), the axioms for an equivalence relation, and,
importantly, the relationship between conjugation and the rack action
(see `Rack.ad_conj`).

None of this forms a 2-category yet, for example due to lack of
associativity of `trans`.  The `PreEnvelGroupRel` relation is a
`Prop`-valued version of `PreEnvelGroupRel'`, and making it
`Prop`-valued essentially introduces enough 3-isomorphisms so that
every pair of compatible 2-morphisms is isomorphic.  Now, while
composition in `PreEnvelGroup` does not strictly satisfy the category
axioms, `PreEnvelGroup` and `PreEnvelGroupRel'` do form a weak
2-category.

Since we just want a 1-category, the last step is to quotient
`PreEnvelGroup` by `PreEnvelGroupRel'`, and the result is the
group `EnvelGroup`.

For a homomorphism `f : R →◃ Conj G`, how does
`EnvelGroup.map f : EnvelGroup R →* G` work?  Let's think of `G` as
being a 2-category with one object, a 1-morphism per element of `G`,
and a single 2-morphism called `Eq.refl` for each 1-morphism.  We
define the map using a "higher `Quotient.lift`" -- not only do we
evaluate elements of `PreEnvelGroup` as expressions in `G` (this is
`toEnvelGroup.mapAux`), but we evaluate elements of
`PreEnvelGroup'` as expressions of 2-morphisms of `G` (this is
`toEnvelGroup.mapAux.well_def`).  That is to say,
`toEnvelGroup.mapAux.well_def` recursively evaluates formal
expressions of 2-morphisms as equality proofs in `G`.  Now that all
morphisms are accounted for, the map descends to a homomorphism
`EnvelGroup R →* G`.

Note: `Type`-valued relations are not common.  The fact it is
`Type`-valued is what makes `toEnvelGroup.mapAux.well_def` have
well-founded recursion.
-/


/-- Free generators of the enveloping group.
-/
inductive PreEnvelGroup (R : Type u) : Type u
  | unit : PreEnvelGroup R
  | incl (x : R) : PreEnvelGroup R
  | mul (a b : PreEnvelGroup R) : PreEnvelGroup R
  | inv (a : PreEnvelGroup R) : PreEnvelGroup R

instance PreEnvelGroup.inhabited (R : Type u) : Inhabited (PreEnvelGroup R) :=
  ⟨PreEnvelGroup.unit⟩

open PreEnvelGroup

/-- Relations for the enveloping group. This is a type-valued relation because
`toEnvelGroup.mapAux.well_def` inducts on it to show `toEnvelGroup.map`
is well-defined.  The relation `PreEnvelGroupRel` is the `Prop`-valued version,
which is used to define `EnvelGroup` itself.
-/
inductive PreEnvelGroupRel' (R : Type u) [Rack R] : PreEnvelGroup R → PreEnvelGroup R → Type u
  | refl {a : PreEnvelGroup R} : PreEnvelGroupRel' R a a
  | symm {a b : PreEnvelGroup R} (hab : PreEnvelGroupRel' R a b) : PreEnvelGroupRel' R b a
  | trans {a b c : PreEnvelGroup R} (hab : PreEnvelGroupRel' R a b)
    (hbc : PreEnvelGroupRel' R b c) : PreEnvelGroupRel' R a c
  | congr_mul {a b a' b' : PreEnvelGroup R} (ha : PreEnvelGroupRel' R a a')
    (hb : PreEnvelGroupRel' R b b') : PreEnvelGroupRel' R (mul a b) (mul a' b')
  | congr_inv {a a' : PreEnvelGroup R} (ha : PreEnvelGroupRel' R a a') :
    PreEnvelGroupRel' R (inv a) (inv a')
  | assoc (a b c : PreEnvelGroup R) : PreEnvelGroupRel' R (mul (mul a b) c) (mul a (mul b c))
  | one_mul (a : PreEnvelGroup R) : PreEnvelGroupRel' R (mul unit a) a
  | mul_one (a : PreEnvelGroup R) : PreEnvelGroupRel' R (mul a unit) a
  | inv_mul_cancel (a : PreEnvelGroup R) : PreEnvelGroupRel' R (mul (inv a) a) unit
  | act_incl (x y : R) :
    PreEnvelGroupRel' R (mul (mul (incl x) (incl y)) (inv (incl x))) (incl (x ◃ y))

instance PreEnvelGroupRel'.inhabited (R : Type u) [Rack R] :
    Inhabited (PreEnvelGroupRel' R unit unit) :=
  ⟨PreEnvelGroupRel'.refl⟩

/--
The `PreEnvelGroupRel` relation as a `Prop`.  Used as the relation for `PreEnvelGroup.setoid`.
-/
inductive PreEnvelGroupRel (R : Type u) [Rack R] : PreEnvelGroup R → PreEnvelGroup R → Prop
  | rel {a b : PreEnvelGroup R} (r : PreEnvelGroupRel' R a b) : PreEnvelGroupRel R a b

/-- A quick way to convert a `PreEnvelGroupRel'` to a `PreEnvelGroupRel`.
-/
theorem PreEnvelGroupRel'.rel {R : Type u} [Rack R] {a b : PreEnvelGroup R} :
    PreEnvelGroupRel' R a b → PreEnvelGroupRel R a b := PreEnvelGroupRel.rel

@[refl]
theorem PreEnvelGroupRel.refl {R : Type u} [Rack R] {a : PreEnvelGroup R} :
    PreEnvelGroupRel R a a :=
  PreEnvelGroupRel.rel PreEnvelGroupRel'.refl

@[symm]
theorem PreEnvelGroupRel.symm {R : Type u} [Rack R] {a b : PreEnvelGroup R} :
    PreEnvelGroupRel R a b → PreEnvelGroupRel R b a
  | ⟨r⟩ => r.symm.rel

@[trans]
theorem PreEnvelGroupRel.trans {R : Type u} [Rack R] {a b c : PreEnvelGroup R} :
    PreEnvelGroupRel R a b → PreEnvelGroupRel R b c → PreEnvelGroupRel R a c
  | ⟨rab⟩, ⟨rbc⟩ => (rab.trans rbc).rel

instance PreEnvelGroup.setoid (R : Type*) [Rack R] : Setoid (PreEnvelGroup R) where
  r := PreEnvelGroupRel R
  iseqv := by
    constructor
    · apply PreEnvelGroupRel.refl
    · apply PreEnvelGroupRel.symm
    · apply PreEnvelGroupRel.trans
/-- The universal enveloping group for the rack R.
-/
def EnvelGroup (R : Type*) [Rack R] :=
  Quotient (PreEnvelGroup.setoid R)

-- Define the `Group` instances in two steps so `inv` can be inferred correctly.
-- TODO: is there a non-invasive way of defining the instance directly?
instance (R : Type*) [Rack R] : DivInvMonoid (EnvelGroup R) where
  mul a b :=
    Quotient.liftOn₂ a b (fun a b => ⟦PreEnvelGroup.mul a b⟧) fun _ _ _ _ ⟨ha⟩ ⟨hb⟩ =>
      Quotient.sound (PreEnvelGroupRel'.congr_mul ha hb).rel
  one := ⟦unit⟧
  inv a :=
    Quotient.liftOn a (fun a => ⟦PreEnvelGroup.inv a⟧) fun _ _ ⟨ha⟩ =>
      Quotient.sound (PreEnvelGroupRel'.congr_inv ha).rel
  mul_assoc a b c :=
    Quotient.inductionOn₃ a b c fun a b c => Quotient.sound (PreEnvelGroupRel'.assoc a b c).rel
  one_mul a := Quotient.inductionOn a fun a => Quotient.sound (PreEnvelGroupRel'.one_mul a).rel
  mul_one a := Quotient.inductionOn a fun a => Quotient.sound (PreEnvelGroupRel'.mul_one a).rel

instance (R : Type*) [Rack R] : Group (EnvelGroup R) :=
  { inv_mul_cancel := fun a =>
      Quotient.inductionOn a fun a => Quotient.sound (PreEnvelGroupRel'.inv_mul_cancel a).rel }

instance EnvelGroup.inhabited (R : Type*) [Rack R] : Inhabited (EnvelGroup R) :=
  ⟨1⟩

/-- The canonical homomorphism from a rack to its enveloping group.
Satisfies universal properties given by `toEnvelGroup.map` and `toEnvelGroup.univ`.
-/
def toEnvelGroup (R : Type*) [Rack R] : R →◃ Quandle.Conj (EnvelGroup R) where
  toFun x := ⟦incl x⟧
  map_act' := @fun x y => Quotient.sound (PreEnvelGroupRel'.act_incl x y).symm.rel

/-- The preliminary definition of the induced map from the enveloping group.
See `toEnvelGroup.map`.
-/
def toEnvelGroup.mapAux {R : Type*} [Rack R] {G : Type*} [Group G] (f : R →◃ Quandle.Conj G) :
    PreEnvelGroup R → G
  | .unit => 1
  | .incl x => f x
  | .mul a b => toEnvelGroup.mapAux f a * toEnvelGroup.mapAux f b
  | .inv a => (toEnvelGroup.mapAux f a)⁻¹

namespace toEnvelGroup.mapAux

open PreEnvelGroupRel'

/-- Show that `toEnvelGroup.mapAux` sends equivalent expressions to equal terms.
-/
theorem well_def {R : Type*} [Rack R] {G : Type*} [Group G] (f : R →◃ Quandle.Conj G) :
    ∀ {a b : PreEnvelGroup R},
      PreEnvelGroupRel' R a b → toEnvelGroup.mapAux f a = toEnvelGroup.mapAux f b
  | _, _, PreEnvelGroupRel'.refl => rfl
  | _, _, PreEnvelGroupRel'.symm h => (well_def f h).symm
  | _, _, PreEnvelGroupRel'.trans hac hcb => Eq.trans (well_def f hac) (well_def f hcb)
  | _, _, PreEnvelGroupRel'.congr_mul ha hb => by
    simp [toEnvelGroup.mapAux, well_def f ha, well_def f hb]
  | _, _, congr_inv ha => by simp [toEnvelGroup.mapAux, well_def f ha]
  | _, _, assoc a b c => by apply mul_assoc
  | _, _, PreEnvelGroupRel'.one_mul a => by simp [toEnvelGroup.mapAux]
  | _, _, PreEnvelGroupRel'.mul_one a => by simp [toEnvelGroup.mapAux]
  | _, _, PreEnvelGroupRel'.inv_mul_cancel a => by simp [toEnvelGroup.mapAux]
  | _, _, act_incl x y => by simp [toEnvelGroup.mapAux]

end toEnvelGroup.mapAux

/-- Given a map from a rack to a group, lift it to being a map from the enveloping group.
More precisely, the `EnvelGroup` functor is left adjoint to `Quandle.Conj`.
-/
def toEnvelGroup.map {R : Type*} [Rack R] {G : Type*} [Group G] :
    (R →◃ Quandle.Conj G) ≃ (EnvelGroup R →* G) where
  toFun f :=
    { toFun := fun x =>
        Quotient.liftOn x (toEnvelGroup.mapAux f) fun _ _ ⟨hab⟩ =>
          toEnvelGroup.mapAux.well_def f hab
      map_one' := by
        change Quotient.liftOn ⟦Rack.PreEnvelGroup.unit⟧ (toEnvelGroup.mapAux f) _ = 1
        simp only [Quotient.lift_mk, mapAux]
      map_mul' := fun x y =>
        Quotient.inductionOn₂ x y fun x y => by
          change Quotient.liftOn ⟦mul x y⟧ (toEnvelGroup.mapAux f) _ = _
          simp [toEnvelGroup.mapAux] }
  invFun F := (Quandle.Conj.map F).comp (toEnvelGroup R)
  right_inv F :=
    MonoidHom.ext fun x =>
      Quotient.inductionOn x fun x => by
        induction x with
        | unit => exact F.map_one.symm
        | incl => rfl
        | mul x y ih_x ih_y =>
          have hm : ⟦x.mul y⟧ = @Mul.mul (EnvelGroup R) _ ⟦x⟧ ⟦y⟧ := rfl
          simp only [MonoidHom.coe_mk, OneHom.coe_mk, Quotient.lift_mk]
          suffices ∀ x y, F (Mul.mul x y) = F (x) * F (y) by
            simp_all only [MonoidHom.coe_mk, OneHom.coe_mk, Quotient.lift_mk]
            rw [← ih_x, ← ih_y, mapAux]
          exact F.map_mul
        | inv x ih_x =>
          have hm : ⟦x.inv⟧ = @Inv.inv (EnvelGroup R) _ ⟦x⟧ := rfl
          rw [hm, F.map_inv, MonoidHom.map_inv, ih_x]

/-- Given a homomorphism from a rack to a group, it factors through the enveloping group.
-/
theorem toEnvelGroup.univ (R : Type*) [Rack R] (G : Type*) [Group G] (f : R →◃ Quandle.Conj G) :
    (Quandle.Conj.map (toEnvelGroup.map f)).comp (toEnvelGroup R) = f :=
  toEnvelGroup.map.symm_apply_apply f

/-- The homomorphism `toEnvelGroup.map f` is the unique map that fits into the commutative
triangle in `toEnvelGroup.univ`.
-/
theorem toEnvelGroup.univ_uniq (R : Type*) [Rack R] (G : Type*) [Group G]
    (f : R →◃ Quandle.Conj G) (g : EnvelGroup R →* G)
    (h : f = (Quandle.Conj.map g).comp (toEnvelGroup R)) : g = toEnvelGroup.map f :=
  h.symm ▸ (toEnvelGroup.map.apply_symm_apply g).symm

/-- The induced group homomorphism from the enveloping group into bijections of the rack,
using `Rack.toConj`. Satisfies the property `envelAction_prop`.

This gives the rack `R` the structure of an augmented rack over `EnvelGroup R`.
-/
def envelAction {R : Type*} [Rack R] : EnvelGroup R →* R ≃ R :=
  toEnvelGroup.map (toConj R)

@[simp]
theorem envelAction_prop {R : Type*} [Rack R] (x y : R) :
    envelAction (toEnvelGroup R x) y = x ◃ y :=
  rfl

end EnvelGroup

end Rack
