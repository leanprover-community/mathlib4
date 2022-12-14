/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
Ported by: Joël Riou
-/
import Mathlib.Combinatorics.Quiver.Subquiver
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Sum.Basic

/-!
## Weakly connected components

For a quiver `V`, we build a quiver `Symmetrify V` by adding a reversal of every edge.
Informally, a path in `Symmetrify V` corresponds to a 'zigzag' in `V`. This lets us
define the type `WeaklyConnectedComponent V` as the quotient of `V` by the relation which
identifies `a` with `b` if there is a path from `a` to `b` in `Symmetrify V`. (These
zigzags can be seen as a proof-relevant analogue of `EqvGen`.)

Strongly connected components have not yet been defined.
-/

universe v u

namespace Quiver

/-- A type synonym for the symmetrized quiver (with an arrow both ways for each original arrow).
    NB: this does not work for `Prop`-valued quivers. It requires `[Quiver.{v+1} V]`. -/
-- Porting note: no hasNonemptyInstnace linter yet
def Symmetrify (V : Type u) :=
  V

instance symmetrifyQuiver (V : Type u) [Quiver V] : Quiver (Symmetrify V) :=
  ⟨fun a b : V => Sum (a ⟶ b) (b ⟶ a)⟩

variable (V : Type u) [Quiver.{v + 1} V]

/-- A quiver `HasReverse` if we can reverse an arrow `p` from `a` to `b` to get an arrow
    `p.reverse` from `b` to `a`.-/
class HasReverse where
  /-- the map which sends an arrow to its reverse -/
  reverse' : ∀ {a b : V}, (a ⟶ b) → (b ⟶ a)

/-- Reverse the direction of an arrow. -/
def reverse {V} [Quiver.{v + 1} V] [HasReverse V] {a b : V} : (a ⟶ b) → (b ⟶ a) :=
  HasReverse.reverse'

/-- A quiver `HasInvolutiveReverse` if reversing twice is the identity.`-/
class HasInvolutiveReverse extends HasReverse V where
  /-- `reverse` is involutive -/
  inv' : ∀ {a b : V} (f : a ⟶ b), reverse (reverse f) = f

@[simp]
theorem reverse_reverse {V} [Quiver.{v + 1} V] [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) :
    reverse (reverse f) = f := by apply h.inv'

variable {V}

instance : HasReverse (Symmetrify V) :=
  ⟨fun e => e.swap⟩

instance :
    HasInvolutiveReverse
      (Symmetrify V) where
  toHasReverse := ⟨fun e => e.swap⟩
  inv' e := congr_fun Sum.swap_swap_eq e

/-- Reverse the direction of a path. -/
@[simp]
def Path.reverse [HasReverse V] {a : V} : ∀ {b}, Path a b → Path b a
  | _, Path.nil => Path.nil
  | _, Path.cons p e => (Quiver.reverse e).toPath.comp p.reverse

@[simp]
theorem Path.reverse_toPath [HasReverse V] {a b : V} (f : a ⟶ b) :
    f.toPath.reverse = (Quiver.reverse f).toPath :=
  rfl
#align quiver.path.reverse_to_path Quiver.Path.reverse_toPath

@[simp]
theorem Path.reverse_comp [HasReverse V] {a b c : V} (p : Path a b) (q : Path b c) :
    (p.comp q).reverse = q.reverse.comp p.reverse := by
  induction' q with _ _ _ _ h
  · simp
  · simp [h]

@[simp]
theorem Path.reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (p : Path a b) :
    p.reverse.reverse = p := by
  induction' p with _ _ _ _ h
  · simp
  · rw [Path.reverse, Path.reverse_comp, h, Path.reverse_toPath, Quiver.reverse_reverse]
    rfl

/-- The inclusion of a quiver in its symmetrification -/
def Symmetrify.of : Prefunctor V (Symmetrify V) where
  obj := id
  map := Sum.inl

/-- Given a quiver `V'` with reversible arrows, a prefunctor to `V'` can be lifted to one from
    `Symmetrify V` to `V'` -/
def Symmetrify.lift {V' : Type _} [Quiver V'] [HasReverse V'] (φ : Prefunctor V V') :
    Prefunctor (Symmetrify V) V' where
  obj := φ.obj
  map f := match f with
  | Sum.inl g => φ.map g
  | Sum.inr g => reverse (φ.map g)

theorem Symmetrify.lift_spec (V' : Type _) [Quiver V'] [HasReverse V'] (φ : Prefunctor V V') :
    Symmetrify.of.comp (Symmetrify.lift φ) = φ := by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rfl

theorem Symmetrify.lift_reverse (V' : Type _) [Quiver V'] [h : HasInvolutiveReverse V']
    (φ : Prefunctor V V') {X Y : Symmetrify V} (f : X ⟶ Y) :
    (Symmetrify.lift φ).map (Quiver.reverse f) = Quiver.reverse ((Symmetrify.lift φ).map f) := by
  dsimp [Symmetrify.lift]; cases f
  · simp only
    rfl
  · simp only
    rw [h.inv']
    rfl

/-- `lift φ` is the only prefunctor extending `φ` and preserving reverses. -/
theorem Symmetrify.lift_unique (V' : Type _) [Quiver V'] [HasReverse V'] (φ : Prefunctor V V')
    (Φ : Prefunctor (Symmetrify V) V') (hΦ : Symmetrify.of.comp Φ = φ)
    (hΦinv : ∀ {X Y : Symmetrify V} (f : X ⟶ Y),
      Φ.map (Quiver.reverse f) = Quiver.reverse (Φ.map f)) :
    Φ = Symmetrify.lift φ := by
  subst_vars
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    cases f
    · rfl
    · exact hΦinv (Sum.inl _)
#align quiver.symmetrify.lift_unique Quiver.Symmetrify.lift_unique

variable (V)

/-- Two vertices are related in the zigzag setoid if there is a
    zigzag of arrows from one to the other. -/
def zigzagSetoid : Setoid V :=
  ⟨fun a b => Nonempty (@Path (Symmetrify V) _ a b), fun _ => ⟨Path.nil⟩, fun ⟨p⟩ =>
    ⟨p.reverse⟩, fun ⟨p⟩ ⟨q⟩ => ⟨p.comp q⟩⟩

/-- The type of weakly connected components of a directed graph. Two vertices are
    in the same weakly connected component if there is a zigzag of arrows from one
    to the other. -/
def WeaklyConnectedComponent : Type u :=
  Quotient (zigzagSetoid V)

namespace WeaklyConnectedComponent

variable {V}

/-- The weakly connected component corresponding to a vertex. -/
protected def mk : V → WeaklyConnectedComponent V :=
  @Quotient.mk' _ (zigzagSetoid V)

instance : CoeTC V (WeaklyConnectedComponent V) :=
  ⟨WeaklyConnectedComponent.mk⟩

instance [Inhabited V] : Inhabited (WeaklyConnectedComponent V) :=
  ⟨show V from default⟩

protected theorem eq (a b : V) :
    (a : WeaklyConnectedComponent V) = b ↔ Nonempty (@Path (Symmetrify V) _ a b) :=
  Quotient.eq'

end WeaklyConnectedComponent

variable {V}

-- Without the explicit universe level in `Quiver.{v+1}` Lean comes up with
-- `Quiver.{max u_2 u_3 + 1}`. This causes problems elsewhere, so we write `Quiver.{v+1}`.
/-- A wide subquiver `H` of `Symmetrify V` determines a wide subquiver of `V`, containing an
    an arrow `e` if either `e` or its reversal is in `H`. -/
def wideSubquiverSymmetrify (H : WideSubquiver (Symmetrify V)) : WideSubquiver V :=
  fun _ _ => { e | H _ _ (Sum.inl e) ∨ H _ _ (Sum.inr e) }

end Quiver
