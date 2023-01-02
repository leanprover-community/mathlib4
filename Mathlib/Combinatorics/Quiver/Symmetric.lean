/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn

! This file was ported from Lean 3 source module combinatorics.quiver.symmetric
! leanprover-community/mathlib commit 1e05171a5e8cf18d98d9cf7b207540acb044acae
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.Quiver.Basic
import Mathbin.Combinatorics.Quiver.Path
import Mathbin.Combinatorics.Quiver.Push
import Mathbin.Data.Sum.Basic

/-!
## Symmetric quivers and arrow reversal

This file contains constructions related to symmetric quivers:

* `symmetrify V` adds formal inverses to each arrow of `V`.
* `has_reverse` is the class of quivers where each arrow has an assigned formal inverse.
* `has_involutive_reverse` extends `has_reverse` by requiring that the reverse of the reverse
  is equal to the original arrow.
* `prefunctor.preserve_reverse` is the class of prefunctors mapping reverses to reverses.
* `symmetrify.of`, `symmetrify.lift`, and the associated lemmas witness the universal property
  of `symmetrify`.
-/


universe v u w v'

namespace Quiver

#print Quiver.Symmetrify /-
/-- A type synonym for the symmetrized quiver (with an arrow both ways for each original arrow).
    NB: this does not work for `Prop`-valued quivers. It requires `[quiver.{v+1} V]`. -/
@[nolint has_nonempty_instance]
def Symmetrify (V : Type _) :=
  V
#align quiver.symmetrify Quiver.Symmetrify
-/

#print Quiver.symmetrifyQuiver /-
instance symmetrifyQuiver (V : Type u) [Quiver V] : Quiver (Symmetrify V) :=
  ⟨fun a b : V => Sum (a ⟶ b) (b ⟶ a)⟩
#align quiver.symmetrify_quiver Quiver.symmetrifyQuiver
-/

variable (U V W : Type _) [Quiver.{u + 1} U] [Quiver.{v + 1} V] [Quiver.{w + 1} W]

#print Quiver.HasReverse /-
/-- A quiver `has_reverse` if we can reverse an arrow `p` from `a` to `b` to get an arrow
    `p.reverse` from `b` to `a`.-/
class HasReverse where
  reverse' : ∀ {a b : V}, (a ⟶ b) → (b ⟶ a)
#align quiver.has_reverse Quiver.HasReverse
-/

#print Quiver.reverse /-
/-- Reverse the direction of an arrow. -/
def reverse {V} [Quiver.{v + 1} V] [HasReverse V] {a b : V} : (a ⟶ b) → (b ⟶ a) :=
  has_reverse.reverse'
#align quiver.reverse Quiver.reverse
-/

#print Quiver.HasInvolutiveReverse /-
/-- A quiver `has_involutive_reverse` if reversing twice is the identity.`-/
class HasInvolutiveReverse extends HasReverse V where
  inv' : ∀ {a b : V} (f : a ⟶ b), reverse (reverse f) = f
#align quiver.has_involutive_reverse Quiver.HasInvolutiveReverse
-/

variable {U V W}

/- warning: quiver.reverse_reverse -> Quiver.reverse_reverse is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_2 : Quiver.{succ u1, u2} V] [h : Quiver.HasInvolutiveReverse.{u1, u2} V _inst_2] {a : V} {b : V} (f : Quiver.Hom.{succ u1, u2} V _inst_2 a b), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V _inst_2 a b) (Quiver.reverse.{u1, u2} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V _inst_2 h) b a (Quiver.reverse.{u1, u2} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V _inst_2 h) a b f)) f
but is expected to have type
  forall {V : Type.{u1}} [_inst_2 : Quiver.{succ u2, u1} V] [h : Quiver.HasInvolutiveReverse.{u2, u1} V _inst_2] {a : V} {b : V} (f : Quiver.Hom.{succ u2, u1} V _inst_2 a b), Eq.{succ u2} (Quiver.Hom.{succ u2, u1} V _inst_2 a b) (Quiver.reverse.{u2, u1} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u1} V _inst_2 h) b a (Quiver.reverse.{u2, u1} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u1} V _inst_2 h) a b f)) f
Case conversion may be inaccurate. Consider using '#align quiver.reverse_reverse Quiver.reverse_reverseₓ'. -/
@[simp]
theorem reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) :
    reverse (reverse f) = f :=
  h.inv' f
#align quiver.reverse_reverse Quiver.reverse_reverse

/- warning: quiver.reverse_inj -> Quiver.reverse_inj is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_2 : Quiver.{succ u1, u2} V] [_inst_4 : Quiver.HasInvolutiveReverse.{u1, u2} V _inst_2] {a : V} {b : V} (f : Quiver.Hom.{succ u1, u2} V _inst_2 a b) (g : Quiver.Hom.{succ u1, u2} V _inst_2 a b), Iff (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V _inst_2 b a) (Quiver.reverse.{u1, u2} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V _inst_2 _inst_4) a b f) (Quiver.reverse.{u1, u2} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V _inst_2 _inst_4) a b g)) (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V _inst_2 a b) f g)
but is expected to have type
  forall {V : Type.{u1}} [_inst_2 : Quiver.{succ u2, u1} V] [_inst_4 : Quiver.HasInvolutiveReverse.{u2, u1} V _inst_2] {a : V} {b : V} (f : Quiver.Hom.{succ u2, u1} V _inst_2 a b) (g : Quiver.Hom.{succ u2, u1} V _inst_2 a b), Iff (Eq.{succ u2} (Quiver.Hom.{succ u2, u1} V _inst_2 b a) (Quiver.reverse.{u2, u1} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u1} V _inst_2 _inst_4) a b f) (Quiver.reverse.{u2, u1} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u1} V _inst_2 _inst_4) a b g)) (Eq.{succ u2} (Quiver.Hom.{succ u2, u1} V _inst_2 a b) f g)
Case conversion may be inaccurate. Consider using '#align quiver.reverse_inj Quiver.reverse_injₓ'. -/
@[simp]
theorem reverse_inj [HasInvolutiveReverse V] {a b : V} (f g : a ⟶ b) :
    reverse f = reverse g ↔ f = g := by
  constructor
  · rintro h
    simpa using congr_arg Quiver.reverse h
  · rintro h
    congr
    assumption
#align quiver.reverse_inj Quiver.reverse_inj

/- warning: quiver.eq_reverse_iff -> Quiver.eq_reverse_iff is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_2 : Quiver.{succ u1, u2} V] [_inst_4 : Quiver.HasInvolutiveReverse.{u1, u2} V _inst_2] {a : V} {b : V} (f : Quiver.Hom.{succ u1, u2} V _inst_2 a b) (g : Quiver.Hom.{succ u1, u2} V _inst_2 b a), Iff (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V _inst_2 a b) f (Quiver.reverse.{u1, u2} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V _inst_2 _inst_4) b a g)) (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V _inst_2 b a) (Quiver.reverse.{u1, u2} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V _inst_2 _inst_4) a b f) g)
but is expected to have type
  forall {V : Type.{u1}} [_inst_2 : Quiver.{succ u2, u1} V] [_inst_4 : Quiver.HasInvolutiveReverse.{u2, u1} V _inst_2] {a : V} {b : V} (f : Quiver.Hom.{succ u2, u1} V _inst_2 a b) (g : Quiver.Hom.{succ u2, u1} V _inst_2 b a), Iff (Eq.{succ u2} (Quiver.Hom.{succ u2, u1} V _inst_2 a b) f (Quiver.reverse.{u2, u1} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u1} V _inst_2 _inst_4) b a g)) (Eq.{succ u2} (Quiver.Hom.{succ u2, u1} V _inst_2 b a) (Quiver.reverse.{u2, u1} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u1} V _inst_2 _inst_4) a b f) g)
Case conversion may be inaccurate. Consider using '#align quiver.eq_reverse_iff Quiver.eq_reverse_iffₓ'. -/
theorem eq_reverse_iff [HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) (g : b ⟶ a) :
    f = reverse g ↔ reverse f = g := by rw [← reverse_inj, reverse_reverse]
#align quiver.eq_reverse_iff Quiver.eq_reverse_iff

section MapReverse

variable [HasReverse U] [HasReverse V] [HasReverse W]

#print Prefunctor.MapReverse /-
/-- A prefunctor preserving reversal of arrows -/
class Prefunctor.MapReverse (φ : U ⥤q V) where
  map_reverse' : ∀ {u v : U} (e : u ⟶ v), φ.map (reverse e) = reverse (φ.map e)
#align prefunctor.map_reverse Prefunctor.MapReverse
-/

/- warning: prefunctor.map_reverse' -> Prefunctor.map_reverse is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u3}} {V : Type.{u4}} [_inst_1 : Quiver.{succ u2, u3} U] [_inst_2 : Quiver.{succ u1, u4} V] [_inst_4 : Quiver.HasReverse.{u2, u3} U _inst_1] [_inst_5 : Quiver.HasReverse.{u1, u4} V _inst_2] (φ : Prefunctor.{succ u2, succ u1, u3, u4} U _inst_1 V _inst_2) [_inst_7 : Prefunctor.MapReverse.{u1, u2, u3, u4} U V _inst_1 _inst_2 _inst_4 _inst_5 φ] {u : U} {v : U} (e : Quiver.Hom.{succ u2, u3} U _inst_1 u v), Eq.{succ u1} (Quiver.Hom.{succ u1, u4} V _inst_2 (Prefunctor.obj.{succ u2, succ u1, u3, u4} U _inst_1 V _inst_2 φ v) (Prefunctor.obj.{succ u2, succ u1, u3, u4} U _inst_1 V _inst_2 φ u)) (Prefunctor.map.{succ u2, succ u1, u3, u4} U _inst_1 V _inst_2 φ v u (Quiver.reverse.{u2, u3} U _inst_1 _inst_4 u v e)) (Quiver.reverse.{u1, u4} V _inst_2 _inst_5 (Prefunctor.obj.{succ u2, succ u1, u3, u4} U _inst_1 V _inst_2 φ u) (Prefunctor.obj.{succ u2, succ u1, u3, u4} U _inst_1 V _inst_2 φ v) (Prefunctor.map.{succ u2, succ u1, u3, u4} U _inst_1 V _inst_2 φ u v e))
but is expected to have type
  forall {U : Type.{u2}} {V : Type.{u1}} [_inst_1 : Quiver.{succ u4, u2} U] [_inst_2 : Quiver.{succ u3, u1} V] [_inst_4 : Quiver.HasReverse.{u4, u2} U _inst_1] [_inst_5 : Quiver.HasReverse.{u3, u1} V _inst_2] (φ : Prefunctor.{succ u4, succ u3, u2, u1} U _inst_1 V _inst_2) [_inst_7 : Prefunctor.MapReverse.{u3, u4, u2, u1} U V _inst_1 _inst_2 _inst_4 _inst_5 φ] {u : U} {v : U} (e : Quiver.Hom.{succ u4, u2} U _inst_1 u v), Eq.{succ u3} (Quiver.Hom.{succ u3, u1} V _inst_2 (Prefunctor.obj.{succ u4, succ u3, u2, u1} U _inst_1 V _inst_2 φ v) (Prefunctor.obj.{succ u4, succ u3, u2, u1} U _inst_1 V _inst_2 φ u)) (Prefunctor.map.{succ u4, succ u3, u2, u1} U _inst_1 V _inst_2 φ v u (Quiver.reverse.{u4, u2} U _inst_1 _inst_4 u v e)) (Quiver.reverse.{u3, u1} V _inst_2 _inst_5 (Prefunctor.obj.{succ u4, succ u3, u2, u1} U _inst_1 V _inst_2 φ u) (Prefunctor.obj.{succ u4, succ u3, u2, u1} U _inst_1 V _inst_2 φ v) (Prefunctor.map.{succ u4, succ u3, u2, u1} U _inst_1 V _inst_2 φ u v e))
Case conversion may be inaccurate. Consider using '#align prefunctor.map_reverse' Prefunctor.map_reverseₓ'. -/
@[simp]
theorem Prefunctor.map_reverse (φ : U ⥤q V) [φ.MapReverse] {u v : U} (e : u ⟶ v) :
    φ.map (reverse e) = reverse (φ.map e) :=
  Prefunctor.MapReverse.map_reverse' e
#align prefunctor.map_reverse' Prefunctor.map_reverse

#print Prefunctor.mapReverseComp /-
instance Prefunctor.mapReverseComp (φ : U ⥤q V) (ψ : V ⥤q W) [φ.MapReverse] [ψ.MapReverse] :
    (φ ⋙q ψ).MapReverse
    where map_reverse' u v e := by simp only [Prefunctor.comp_map, Prefunctor.map_reverse]
#align prefunctor.map_reverse_comp Prefunctor.mapReverseComp
-/

#print Prefunctor.mapReverseId /-
instance Prefunctor.mapReverseId : (Prefunctor.id U).MapReverse where map_reverse' u v e := rfl
#align prefunctor.map_reverse_id Prefunctor.mapReverseId
-/

end MapReverse

instance : HasReverse (Symmetrify V) :=
  ⟨fun a b e => e.swap⟩

instance : HasInvolutiveReverse (Symmetrify V)
    where
  reverse' _ _ e := e.swap
  inv' _ _ e := congr_fun Sum.swap_swap_eq e

/- warning: quiver.symmetrify_reverse -> Quiver.symmetrify_reverse is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_2 : Quiver.{succ u1, u2} V] {a : Quiver.Symmetrify.{u2} V} {b : Quiver.Symmetrify.{u2} V} (e : Quiver.Hom.{succ u1, u2} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_2) a b), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_2) b a) (Quiver.reverse.{u1, u2} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_2) (Quiver.Symmetrify.hasReverse.{u1, u2} V _inst_2) a b e) (Sum.swap.{u1, u1} (Quiver.Hom.{succ u1, u2} V _inst_2 a b) (Quiver.Hom.{succ u1, u2} V _inst_2 b a) e)
but is expected to have type
  forall {V : Type.{u1}} [_inst_2 : Quiver.{succ u2, u1} V] {a : Quiver.Symmetrify.{u1} V} {b : Quiver.Symmetrify.{u1} V} (e : Quiver.Hom.{succ u2, u1} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u2} V _inst_2) a b), Eq.{succ u2} (Quiver.Hom.{succ u2, u1} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u2} V _inst_2) b a) (Quiver.reverse.{u2, u1} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u2} V _inst_2) (Quiver.instHasReverseSymmetrifySymmetrifyQuiver.{u2, u1} V _inst_2) a b e) (Sum.swap.{u2, u2} (Quiver.Hom.{succ u2, u1} V _inst_2 a b) (Quiver.Hom.{succ u2, u1} V _inst_2 b a) e)
Case conversion may be inaccurate. Consider using '#align quiver.symmetrify_reverse Quiver.symmetrify_reverseₓ'. -/
@[simp]
theorem symmetrify_reverse {a b : Symmetrify V} (e : a ⟶ b) : reverse e = e.swap :=
  rfl
#align quiver.symmetrify_reverse Quiver.symmetrify_reverse

#print Quiver.Hom.toPos /-
/-- Shorthand for the "forward" arrow corresponding to `f` in `symmetrify V` -/
abbrev Hom.toPos {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom X Y :=
  Sum.inl f
#align quiver.hom.to_pos Quiver.Hom.toPos
-/

#print Quiver.Hom.toNeg /-
/-- Shorthand for the "backward" arrow corresponding to `f` in `symmetrify V` -/
abbrev Hom.toNeg {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom Y X :=
  Sum.inr f
#align quiver.hom.to_neg Quiver.Hom.toNeg
-/

#print Quiver.Path.reverse /-
/-- Reverse the direction of a path. -/
@[simp]
def Path.reverse [HasReverse V] {a : V} : ∀ {b}, Path a b → Path b a
  | a, path.nil => Path.nil
  | b, path.cons p e => (reverse e).toPath.comp p.reverse
#align quiver.path.reverse Quiver.Path.reverse
-/

/- warning: quiver.path.reverse_to_path -> Quiver.Path.reverse_toPath is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_2 : Quiver.{succ u1, u2} V] [_inst_4 : Quiver.HasReverse.{u1, u2} V _inst_2] {a : V} {b : V} (f : Quiver.Hom.{succ u1, u2} V _inst_2 a b), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} V _inst_2 b a) (Quiver.Path.reverse.{u1, u2} V _inst_2 _inst_4 a b (Quiver.Hom.toPath.{u2, succ u1} V _inst_2 a b f)) (Quiver.Hom.toPath.{u2, succ u1} V _inst_2 b a (Quiver.reverse.{u1, u2} V _inst_2 _inst_4 a b f))
but is expected to have type
  forall {V : Type.{u1}} [_inst_2 : Quiver.{succ u2, u1} V] [_inst_4 : Quiver.HasReverse.{u2, u1} V _inst_2] {a : V} {b : V} (f : Quiver.Hom.{succ u2, u1} V _inst_2 a b), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} V _inst_2 b a) (Quiver.Path.reverse.{u2, u1} V _inst_2 _inst_4 a b (Quiver.Hom.toPath.{u1, succ u2} V _inst_2 a b f)) (Quiver.Hom.toPath.{u1, succ u2} V _inst_2 b a (Quiver.reverse.{u2, u1} V _inst_2 _inst_4 a b f))
Case conversion may be inaccurate. Consider using '#align quiver.path.reverse_to_path Quiver.Path.reverse_toPathₓ'. -/
@[simp]
theorem Path.reverse_toPath [HasReverse V] {a b : V} (f : a ⟶ b) :
    f.toPath.reverse = (reverse f).toPath :=
  rfl
#align quiver.path.reverse_to_path Quiver.Path.reverse_toPath

/- warning: quiver.path.reverse_comp -> Quiver.Path.reverse_comp is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_2 : Quiver.{succ u1, u2} V] [_inst_4 : Quiver.HasReverse.{u1, u2} V _inst_2] {a : V} {b : V} {c : V} (p : Quiver.Path.{succ u1, u2} V _inst_2 a b) (q : Quiver.Path.{succ u1, u2} V _inst_2 b c), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} V _inst_2 c a) (Quiver.Path.reverse.{u1, u2} V _inst_2 _inst_4 a c (Quiver.Path.comp.{u2, succ u1} V _inst_2 a b c p q)) (Quiver.Path.comp.{u2, succ u1} V _inst_2 c b a (Quiver.Path.reverse.{u1, u2} V _inst_2 _inst_4 b c q) (Quiver.Path.reverse.{u1, u2} V _inst_2 _inst_4 a b p))
but is expected to have type
  forall {V : Type.{u1}} [_inst_2 : Quiver.{succ u2, u1} V] [_inst_4 : Quiver.HasReverse.{u2, u1} V _inst_2] {a : V} {b : V} {c : V} (p : Quiver.Path.{succ u2, u1} V _inst_2 a b) (q : Quiver.Path.{succ u2, u1} V _inst_2 b c), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} V _inst_2 c a) (Quiver.Path.reverse.{u2, u1} V _inst_2 _inst_4 a c (Quiver.Path.comp.{u1, succ u2} V _inst_2 a b c p q)) (Quiver.Path.comp.{u1, succ u2} V _inst_2 c b a (Quiver.Path.reverse.{u2, u1} V _inst_2 _inst_4 b c q) (Quiver.Path.reverse.{u2, u1} V _inst_2 _inst_4 a b p))
Case conversion may be inaccurate. Consider using '#align quiver.path.reverse_comp Quiver.Path.reverse_compₓ'. -/
@[simp]
theorem Path.reverse_comp [HasReverse V] {a b c : V} (p : Path a b) (q : Path b c) :
    (p.comp q).reverse = q.reverse.comp p.reverse :=
  by
  induction q
  · simp
  · simp [q_ih]
#align quiver.path.reverse_comp Quiver.Path.reverse_comp

/- warning: quiver.path.reverse_reverse -> Quiver.Path.reverse_reverse is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_2 : Quiver.{succ u1, u2} V] [_inst_4 : Quiver.HasInvolutiveReverse.{u1, u2} V _inst_2] {a : V} {b : V} (p : Quiver.Path.{succ u1, u2} V _inst_2 a b), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} V _inst_2 a b) (Quiver.Path.reverse.{u1, u2} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V _inst_2 _inst_4) b a (Quiver.Path.reverse.{u1, u2} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V _inst_2 _inst_4) a b p)) p
but is expected to have type
  forall {V : Type.{u1}} [_inst_2 : Quiver.{succ u2, u1} V] [_inst_4 : Quiver.HasInvolutiveReverse.{u2, u1} V _inst_2] {a : V} {b : V} (p : Quiver.Path.{succ u2, u1} V _inst_2 a b), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} V _inst_2 a b) (Quiver.Path.reverse.{u2, u1} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u1} V _inst_2 _inst_4) b a (Quiver.Path.reverse.{u2, u1} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u1} V _inst_2 _inst_4) a b p)) p
Case conversion may be inaccurate. Consider using '#align quiver.path.reverse_reverse Quiver.Path.reverse_reverseₓ'. -/
@[simp]
theorem Path.reverse_reverse [HasInvolutiveReverse V] {a b : V} (p : Path a b) :
    p.reverse.reverse = p := by
  induction p
  · simp
  · simp only [path.reverse, path.reverse_comp, path.reverse_to_path, reverse_reverse, p_ih]
    rfl
#align quiver.path.reverse_reverse Quiver.Path.reverse_reverse

namespace Symmetrify

#print Quiver.Symmetrify.of /-
/-- The inclusion of a quiver in its symmetrification -/
@[simps]
def of : V ⥤q Symmetrify V where
  obj := id
  map X Y f := Sum.inl f
#align quiver.symmetrify.of Quiver.Symmetrify.of
-/

variable {V' : Type _} [Quiver.{v' + 1} V']

#print Quiver.Symmetrify.lift /-
/-- Given a quiver `V'` with reversible arrows, a prefunctor to `V'` can be lifted to one from
    `symmetrify V` to `V'` -/
def lift [HasReverse V'] (φ : V ⥤q V') : Symmetrify V ⥤q V'
    where
  obj := φ.obj
  map X Y f := Sum.rec (fun fwd => φ.map fwd) (fun bwd => reverse (φ.map bwd)) f
#align quiver.symmetrify.lift Quiver.Symmetrify.lift
-/

/- warning: quiver.symmetrify.lift_spec -> Quiver.Symmetrify.lift_spec is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u3}} [_inst_2 : Quiver.{succ u1, u3} V] {V' : Type.{u4}} [_inst_4 : Quiver.{succ u2, u4} V'] [_inst_5 : Quiver.HasReverse.{u2, u4} V' _inst_4] (φ : Prefunctor.{succ u1, succ u2, u3, u4} V _inst_2 V' _inst_4), Eq.{max (max (succ u3) (succ u1) (succ u2)) (succ u3) (succ u4)} (Prefunctor.{succ u1, succ u2, u3, u4} V _inst_2 V' _inst_4) (Prefunctor.comp.{u3, succ u1, u3, succ u1, u4, succ u2} V _inst_2 (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.of.{u1, u3} V _inst_2) (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 _inst_5 φ)) φ
but is expected to have type
  forall {V : Type.{u1}} [_inst_2 : Quiver.{succ u3, u1} V] {V' : Type.{u2}} [_inst_4 : Quiver.{succ u4, u2} V'] [_inst_5 : Quiver.HasReverse.{u4, u2} V' _inst_4] (φ : Prefunctor.{succ u3, succ u4, u1, u2} V _inst_2 V' _inst_4), Eq.{max (max (max (succ u3) (succ u4)) (succ u1)) (succ u2)} (Prefunctor.{succ u3, succ u4, u1, u2} V _inst_2 V' _inst_4) (Prefunctor.comp.{u1, succ u3, u1, succ u3, u2, succ u4} V _inst_2 (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.of.{u3, u1} V _inst_2) (Quiver.Symmetrify.lift.{u3, u4, u1, u2} V _inst_2 V' _inst_4 _inst_5 φ)) φ
Case conversion may be inaccurate. Consider using '#align quiver.symmetrify.lift_spec Quiver.Symmetrify.lift_specₓ'. -/
theorem lift_spec [HasReverse V'] (φ : V ⥤q V') : (of ⋙q lift φ) = φ :=
  by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rfl
#align quiver.symmetrify.lift_spec Quiver.Symmetrify.lift_spec

/- warning: quiver.symmetrify.lift_reverse -> Quiver.Symmetrify.lift_reverse is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u3}} [_inst_2 : Quiver.{succ u1, u3} V] {V' : Type.{u4}} [_inst_4 : Quiver.{succ u2, u4} V'] [h : Quiver.HasInvolutiveReverse.{u2, u4} V' _inst_4] (φ : Prefunctor.{succ u1, succ u2, u3, u4} V _inst_2 V' _inst_4) {X : Quiver.Symmetrify.{u3} V} {Y : Quiver.Symmetrify.{u3} V} (f : Quiver.Hom.{succ u1, u3} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) X Y), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} V' _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u4} V' _inst_4 h) φ) Y) (Prefunctor.obj.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u4} V' _inst_4 h) φ) X)) (Prefunctor.map.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u4} V' _inst_4 h) φ) Y X (Quiver.reverse.{u1, u3} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) (Quiver.Symmetrify.hasReverse.{u1, u3} V _inst_2) X Y f)) (Quiver.reverse.{u2, u4} V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u4} V' _inst_4 h) (Prefunctor.obj.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u4} V' _inst_4 h) φ) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u4} V' _inst_4 h) φ) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u4} V' _inst_4 h) φ) X Y f))
but is expected to have type
  forall {V : Type.{u1}} [_inst_2 : Quiver.{succ u3, u1} V] {V' : Type.{u2}} [_inst_4 : Quiver.{succ u4, u2} V'] [h : Quiver.HasInvolutiveReverse.{u4, u2} V' _inst_4] (φ : Prefunctor.{succ u3, succ u4, u1, u2} V _inst_2 V' _inst_4) {X : Quiver.Symmetrify.{u1} V} {Y : Quiver.Symmetrify.{u1} V} (f : Quiver.Hom.{succ u3, u1} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) X Y), Eq.{succ u4} (Quiver.Hom.{succ u4, u2} V' _inst_4 (Prefunctor.obj.{succ u3, succ u4, u1, u2} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u3, u4, u1, u2} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u4, u2} V' _inst_4 h) φ) Y) (Prefunctor.obj.{succ u3, succ u4, u1, u2} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u3, u4, u1, u2} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u4, u2} V' _inst_4 h) φ) X)) (Prefunctor.map.{succ u3, succ u4, u1, u2} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u3, u4, u1, u2} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u4, u2} V' _inst_4 h) φ) Y X (Quiver.reverse.{u3, u1} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) (Quiver.instHasReverseSymmetrifySymmetrifyQuiver.{u3, u1} V _inst_2) X Y f)) (Quiver.reverse.{u4, u2} V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u4, u2} V' _inst_4 h) (Prefunctor.obj.{succ u3, succ u4, u1, u2} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u3, u4, u1, u2} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u4, u2} V' _inst_4 h) φ) X) (Prefunctor.obj.{succ u3, succ u4, u1, u2} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u3, u4, u1, u2} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u4, u2} V' _inst_4 h) φ) Y) (Prefunctor.map.{succ u3, succ u4, u1, u2} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u3, u4, u1, u2} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u4, u2} V' _inst_4 h) φ) X Y f))
Case conversion may be inaccurate. Consider using '#align quiver.symmetrify.lift_reverse Quiver.Symmetrify.lift_reverseₓ'. -/
theorem lift_reverse [h : HasInvolutiveReverse V'] (φ : V ⥤q V') {X Y : Symmetrify V} (f : X ⟶ Y) :
    (lift φ).map (Quiver.reverse f) = Quiver.reverse ((lift φ).map f) :=
  by
  dsimp [lift]; cases f
  · simp only
    rfl
  · simp only [reverse_reverse]
    rfl
#align quiver.symmetrify.lift_reverse Quiver.Symmetrify.lift_reverse

/- warning: quiver.symmetrify.lift_unique -> Quiver.Symmetrify.lift_unique is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u3}} [_inst_2 : Quiver.{succ u1, u3} V] {V' : Type.{u4}} [_inst_4 : Quiver.{succ u2, u4} V'] [_inst_5 : Quiver.HasReverse.{u2, u4} V' _inst_4] (φ : Prefunctor.{succ u1, succ u2, u3, u4} V _inst_2 V' _inst_4) (Φ : Prefunctor.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4), (Eq.{max (max (succ u3) (succ u1) (succ u2)) (succ u3) (succ u4)} (Prefunctor.{succ u1, succ u2, u3, u4} V _inst_2 V' _inst_4) (Prefunctor.comp.{u3, succ u1, u3, succ u1, u4, succ u2} V _inst_2 (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.of.{u1, u3} V _inst_2) Φ) φ) -> (forall [hΦrev : Prefunctor.MapReverse.{u2, u1, u3, u4} (Quiver.Symmetrify.{u3} V) V' (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) _inst_4 (Quiver.Symmetrify.hasReverse.{u1, u3} V _inst_2) _inst_5 Φ], Eq.{max (max (succ u3) (succ u1) (succ u2)) (succ u3) (succ u4)} (Prefunctor.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4) Φ (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 _inst_5 φ))
but is expected to have type
  forall {V : Type.{u1}} [_inst_2 : Quiver.{succ u3, u1} V] {V' : Type.{u2}} [_inst_4 : Quiver.{succ u4, u2} V'] [_inst_5 : Quiver.HasReverse.{u4, u2} V' _inst_4] (φ : Prefunctor.{succ u3, succ u4, u1, u2} V _inst_2 V' _inst_4) (Φ : Prefunctor.{succ u3, succ u4, u1, u2} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4), (Eq.{max (max (max (succ u3) (succ u4)) (succ u1)) (succ u2)} (Prefunctor.{succ u3, succ u4, u1, u2} V _inst_2 V' _inst_4) (Prefunctor.comp.{u1, succ u3, u1, succ u3, u2, succ u4} V _inst_2 (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.of.{u3, u1} V _inst_2) Φ) φ) -> (forall {X : Quiver.Symmetrify.{u1} V} {Y : Quiver.Symmetrify.{u1} V} (f : Quiver.Hom.{succ u3, u1} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) X Y), Eq.{succ u4} (Quiver.Hom.{succ u4, u2} V' _inst_4 (Prefunctor.obj.{succ u3, succ u4, u1, u2} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4 Φ Y) (Prefunctor.obj.{succ u3, succ u4, u1, u2} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4 Φ X)) (Prefunctor.map.{succ u3, succ u4, u1, u2} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4 Φ Y X (Quiver.reverse.{u3, u1} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) (Quiver.instHasReverseSymmetrifySymmetrifyQuiver.{u3, u1} V _inst_2) X Y f)) (Quiver.reverse.{u4, u2} V' _inst_4 _inst_5 (Prefunctor.obj.{succ u3, succ u4, u1, u2} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4 Φ X) (Prefunctor.obj.{succ u3, succ u4, u1, u2} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4 Φ Y) (Prefunctor.map.{succ u3, succ u4, u1, u2} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4 Φ X Y f))) -> (Eq.{max (max (max (succ u3) (succ u4)) (succ u1)) (succ u2)} (Prefunctor.{succ u3, succ u4, u1, u2} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u3} V _inst_2) V' _inst_4) Φ (Quiver.Symmetrify.lift.{u3, u4, u1, u2} V _inst_2 V' _inst_4 _inst_5 φ))
Case conversion may be inaccurate. Consider using '#align quiver.symmetrify.lift_unique Quiver.Symmetrify.lift_uniqueₓ'. -/
/-- `lift φ` is the only prefunctor extending `φ` and preserving reverses. -/
theorem lift_unique [HasReverse V'] (φ : V ⥤q V') (Φ : Symmetrify V ⥤q V') (hΦ : (of ⋙q Φ) = φ)
    [hΦrev : Φ.MapReverse] : Φ = lift φ := by
  subst_vars
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    cases f
    · rfl
    · dsimp [lift, of]
      simp only [← Prefunctor.map_reverse, symmetrify_reverse, Sum.swap_inl]
#align quiver.symmetrify.lift_unique Quiver.Symmetrify.lift_unique

/-- A prefunctor canonically defines a prefunctor of the symmetrifications. -/
@[simps]
def Prefunctor.symmetrify (φ : U ⥤q V) : Symmetrify U ⥤q Symmetrify V
    where
  obj := φ.obj
  map X Y := Sum.map φ.map φ.map
#align prefunctor.symmetrify Prefunctor.symmetrify

instance Prefunctor.symmetrifyMapReverse (φ : U ⥤q V) : Prefunctor.MapReverse φ.Symmetrify :=
  ⟨fun u v e => by cases e <;> rfl⟩
#align prefunctor.symmetrify_map_reverse Prefunctor.symmetrifyMapReverse

end Symmetrify

namespace Push

variable {V' : Type _} (σ : V → V')

instance [HasReverse V] : HasReverse (Push σ)
    where reverse' a b F := by
    cases F
    constructor
    apply reverse
    exact F_f

instance [HasInvolutiveReverse V] : HasInvolutiveReverse (Push σ)
    where
  reverse' a b F := by
    cases F
    constructor
    apply reverse
    exact F_f
  inv' a b F := by
    cases F
    dsimp [reverse]
    congr
    apply reverse_reverse

/- warning: quiver.push.of_reverse -> Quiver.Push.of_reverse is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_2 : Quiver.{succ u1, u2} V] {V' : Type.{u3}} (σ : V -> V') [h : Quiver.HasInvolutiveReverse.{u1, u2} V _inst_2] (X : V) (Y : V) (f : Quiver.Hom.{succ u1, u2} V _inst_2 X Y), Eq.{succ (max u2 u3 (succ u1))} (Quiver.Hom.{succ (max u2 u3 (succ u1)), u3} (Quiver.Push.{u2, succ u1, u3} V _inst_2 V' σ) (Quiver.Push.quiver.{u2, succ u1, u3} V _inst_2 V' σ) (Prefunctor.obj.{succ u1, succ (max u2 u3 (succ u1)), u2, u3} V _inst_2 (Quiver.Push.{u2, succ u1, u3} V _inst_2 V' σ) (Quiver.Push.quiver.{u2, succ u1, u3} V _inst_2 V' σ) (Quiver.Push.of.{u2, succ u1, u3} V _inst_2 V' σ) Y) (Prefunctor.obj.{succ u1, succ (max u2 u3 (succ u1)), u2, u3} V _inst_2 (Quiver.Push.{u2, succ u1, u3} V _inst_2 V' σ) (Quiver.Push.quiver.{u2, succ u1, u3} V _inst_2 V' σ) (Quiver.Push.of.{u2, succ u1, u3} V _inst_2 V' σ) X)) (Quiver.reverse.{max u2 u3 (succ u1), u3} (Quiver.Push.{u2, succ u1, u3} V _inst_2 V' σ) (Quiver.Push.quiver.{u2, succ u1, u3} V _inst_2 V' σ) (Quiver.Push.quiver.hasReverse.{u1, u2, u3} V _inst_2 V' σ (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V _inst_2 h)) (Prefunctor.obj.{succ u1, succ (max u2 u3 (succ u1)), u2, u3} V _inst_2 (Quiver.Push.{u2, succ u1, u3} V _inst_2 V' σ) (Quiver.Push.quiver.{u2, succ u1, u3} V _inst_2 V' σ) (Quiver.Push.of.{u2, succ u1, u3} V _inst_2 V' σ) X) (Prefunctor.obj.{succ u1, succ (max u2 u3 (succ u1)), u2, u3} V _inst_2 (Quiver.Push.{u2, succ u1, u3} V _inst_2 V' σ) (Quiver.Push.quiver.{u2, succ u1, u3} V _inst_2 V' σ) (Quiver.Push.of.{u2, succ u1, u3} V _inst_2 V' σ) Y) (Prefunctor.map.{succ u1, succ (max u2 u3 (succ u1)), u2, u3} V _inst_2 (Quiver.Push.{u2, succ u1, u3} V _inst_2 V' σ) (Quiver.Push.quiver.{u2, succ u1, u3} V _inst_2 V' σ) (Quiver.Push.of.{u2, succ u1, u3} V _inst_2 V' σ) X Y f)) (Prefunctor.map.{succ u1, succ (max u2 u3 (succ u1)), u2, u3} V _inst_2 (Quiver.Push.{u2, succ u1, u3} V _inst_2 V' σ) (Quiver.Push.quiver.{u2, succ u1, u3} V _inst_2 V' σ) (Quiver.Push.of.{u2, succ u1, u3} V _inst_2 V' σ) Y X (Quiver.reverse.{u1, u2} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V _inst_2 h) X Y f))
but is expected to have type
  forall {V : Type.{u2}} [_inst_2 : Quiver.{succ u3, u2} V] {V' : Type.{u1}} (σ : V -> V') [h : Quiver.HasInvolutiveReverse.{u3, u2} V _inst_2] (X : V) (Y : V) (f : Quiver.Hom.{succ u3, u2} V _inst_2 X Y), Eq.{max (max (succ (succ u3)) (succ u2)) (succ u1)} (Quiver.Hom.{succ (max (max (succ u3) u2) u1), u1} (Quiver.Push.{u2, u1} V V' σ) (Quiver.instQuiverPush.{u2, succ u3, u1} V _inst_2 V' σ) (Prefunctor.obj.{succ u3, max (max (succ (succ u3)) (succ u2)) (succ u1), u2, u1} V _inst_2 (Quiver.Push.{u2, u1} V V' σ) (Quiver.instQuiverPush.{u2, succ u3, u1} V _inst_2 V' σ) (Quiver.Push.of.{u2, succ u3, u1} V _inst_2 V' σ) Y) (Prefunctor.obj.{succ u3, max (max (succ (succ u3)) (succ u2)) (succ u1), u2, u1} V _inst_2 (Quiver.Push.{u2, u1} V V' σ) (Quiver.instQuiverPush.{u2, succ u3, u1} V _inst_2 V' σ) (Quiver.Push.of.{u2, succ u3, u1} V _inst_2 V' σ) X)) (Quiver.reverse.{max (max (succ u3) u2) u1, u1} (Quiver.Push.{u2, u1} V V' σ) (Quiver.instQuiverPush.{u2, succ u3, u1} V _inst_2 V' σ) (Quiver.Push.instHasReversePushInstQuiverPush.{u3, u2, u1} V _inst_2 V' σ (Quiver.HasInvolutiveReverse.toHasReverse.{u3, u2} V _inst_2 h)) (Prefunctor.obj.{succ u3, max (max (succ (succ u3)) (succ u2)) (succ u1), u2, u1} V _inst_2 (Quiver.Push.{u2, u1} V V' σ) (Quiver.instQuiverPush.{u2, succ u3, u1} V _inst_2 V' σ) (Quiver.Push.of.{u2, succ u3, u1} V _inst_2 V' σ) X) (Prefunctor.obj.{succ u3, max (max (succ (succ u3)) (succ u2)) (succ u1), u2, u1} V _inst_2 (Quiver.Push.{u2, u1} V V' σ) (Quiver.instQuiverPush.{u2, succ u3, u1} V _inst_2 V' σ) (Quiver.Push.of.{u2, succ u3, u1} V _inst_2 V' σ) Y) (Prefunctor.map.{succ u3, max (max (succ (succ u3)) (succ u2)) (succ u1), u2, u1} V _inst_2 (Quiver.Push.{u2, u1} V V' σ) (Quiver.instQuiverPush.{u2, succ u3, u1} V _inst_2 V' σ) (Quiver.Push.of.{u2, succ u3, u1} V _inst_2 V' σ) X Y f)) (Prefunctor.map.{succ u3, max (max (succ (succ u3)) (succ u2)) (succ u1), u2, u1} V _inst_2 (Quiver.Push.{u2, u1} V V' σ) (Quiver.instQuiverPush.{u2, succ u3, u1} V _inst_2 V' σ) (Quiver.Push.of.{u2, succ u3, u1} V _inst_2 V' σ) Y X (Quiver.reverse.{u3, u2} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u3, u2} V _inst_2 h) X Y f))
Case conversion may be inaccurate. Consider using '#align quiver.push.of_reverse Quiver.Push.of_reverseₓ'. -/
theorem of_reverse [h : HasInvolutiveReverse V] (X Y : V) (f : X ⟶ Y) :
    (reverse <| (Push.of σ).map f) = (Push.of σ).map (reverse f) :=
  rfl
#align quiver.push.of_reverse Quiver.Push.of_reverse

#print Quiver.Push.ofMapReverse /-
instance ofMapReverse [h : HasInvolutiveReverse V] : (Push.of σ).MapReverse :=
  ⟨by simp [of_reverse]⟩
#align quiver.push.of_map_reverse Quiver.Push.ofMapReverse
-/

end Push

#print Quiver.IsPreconnected /-
/-- A quiver is preconnected iff there exists a path between any pair of
vertices.
Note that if `V` doesn't `has_reverse`, then the definition is stronger than
simply having a preconnected underlying `simple_graph`, since a path in one
direction doesn't induce one in the other.
-/
def IsPreconnected (V) [Quiver.{u + 1} V] :=
  ∀ X Y : V, Nonempty (Path X Y)
#align quiver.is_preconnected Quiver.IsPreconnected
-/

end Quiver

