/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Antoine Labelle, Rémi Bottinelli
Ported by: Joël Riou, Rémi Bottinelli
-/
import Mathlib.Combinatorics.Quiver.Subquiver
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Push
import Mathlib.Data.Sum.Basic

/-!
## Symmetric quivers and arrow reversal

This file contains constructions related to symmetric quivers:

* `Symmetrify V` adds formal inverses to each arrow of `V`.
* `HasReverse` is the class of quivers where each arrow has an assigned formal inverse.
* `HasInvolutiveReverse` extends `HasReverse` by requiring that the reverse of the reverse
  is equal to the original arrow.
* `Prefunctor.PreserveReverse` is the class of prefunctors mapping reverses to reverses.
* `Symmetrify.of`, `Symmetrify.lift`, and the associated lemmas witness the universal property
  of `Symmetrify`.
-/

universe v u w v'

namespace Quiver

/-- A type synonym for the symmetrized quiver (with an arrow both ways for each original arrow).
    NB: this does not work for `Prop`-valued quivers. It requires `[Quiver.{v+1} V]`. -/
-- Porting note: no hasNonemptyInstance linter yet
def Symmetrify (V : Type _) := V

instance symmetrifyQuiver (V : Type _) [Quiver V] : Quiver (Symmetrify V) :=
  ⟨fun a b : V ↦ Sum (a ⟶ b) (b ⟶ a)⟩

variable (U V W : Type) [Quiver.{u + 1} U] [Quiver.{v + 1} V]

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
#align quiver.reverse_reverse Quiver.reverse_reverse

@[simp]
theorem reverse_eq_reverse_iff {V} [Quiver.{v + 1} V] [h : HasInvolutiveReverse V] {a b : V}
    (f g : a ⟶ b) : reverse f = reverse g ↔ f = g := by
  constructor
  · rintro h
    simpa using congr_arg Quiver.reverse h
  · rintro h
    congr
#align quiver.reverse_eq_reverse_iff Quiver.reverse_eq_reverse_iff

theorem eq_reverse_iff {V} [Quiver.{v + 1} V] [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b)
    (g : b ⟶ a) : f = reverse g ↔ reverse f = g := by
  simpa using reverse_eq_reverse_iff (reverse f) g

#align quiver.eq_reverse_iff Quiver.eq_reverse_iff

variable {U V W}

/-- A prefunctor preserving reversal of arrows -/
class _root_.Prefunctor.MapReverse [HasReverse U] [HasReverse V] (φ : U ⥤q V) where
  /-- The image of a reverse is the reverse of the image. -/
  map_reverse' : ∀ {u v : U} (e : u ⟶ v), φ.map (reverse e) = reverse (φ.map e)
#align prefunctor.map_reverse Prefunctor.MapReverse

@[simp]
theorem _root_.Prefunctor.map_reverse [HasReverse U] [HasReverse V] (φ : U ⥤q V) [φ.MapReverse]
    {u v : U} (e : u ⟶ v) : φ.map (reverse e) = reverse (φ.map e) :=
  Prefunctor.MapReverse.map_reverse' e
#align prefunctor.map_reverse' Prefunctor.map_reverse

instance _root_.Prefunctor.mapReverseComp [Quiver.{w + 1} W]
    [HasReverse U] [HasReverse V] [HasReverse W]
    (φ : U ⥤q V) (ψ : V ⥤q W) [φ.MapReverse] [ψ.MapReverse] :
    (φ ⋙q ψ).MapReverse where
  map_reverse' e := by
    simp only [Prefunctor.comp_map, Prefunctor.MapReverse.map_reverse']
#align prefunctor.map_reverse_comp Prefunctor.mapReverseComp

instance _root_.Prefunctor.mapReverseId [HasReverse U] :
    (Prefunctor.id U).MapReverse where
  map_reverse' _ := rfl
#align prefunctor.map_reverse_id Prefunctor.mapReverseId

instance : HasReverse (Symmetrify V) :=
  ⟨fun e => e.swap⟩

instance :
    HasInvolutiveReverse
      (Symmetrify V) where
  toHasReverse := ⟨fun e ↦ e.swap⟩
  inv' e := congr_fun Sum.swap_swap_eq e

@[simp]
theorem symmetrify_reverse {a b : Symmetrify V} (e : a ⟶ b) : reverse e = e.swap :=
  rfl
#align quiver.symmetrify_reverse Quiver.symmetrify_reverse

section Paths

/-- Shorthand for the "forward" arrow corresponding to `f` in `symmetrify V` -/
abbrev Hom.toPos {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom X Y :=
  Sum.inl f
#align quiver.hom.to_pos Quiver.Hom.toPos

/-- Shorthand for the "backward" arrow corresponding to `f` in `symmetrify V` -/
abbrev Hom.toNeg {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom Y X :=
  Sum.inr f
#align quiver.hom.to_neg Quiver.Hom.toNeg

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

end Paths

section Symmetrify

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

end Symmetrify

section Push

variable (σ : V → W)

instance [HasReverse V] : HasReverse (Quiver.Push σ) where
  reverse' := fun
              | PushQuiver.arrow f => PushQuiver.arrow (reverse f)

instance [h : HasInvolutiveReverse V] :
    HasInvolutiveReverse (Push σ) where
  reverse' := fun
  | PushQuiver.arrow f => PushQuiver.arrow (reverse f)
  inv' := fun
  | PushQuiver.arrow f => by dsimp [reverse]; congr; apply h.inv'

theorem Push.of_reverse [HasInvolutiveReverse V] (X Y : V) (f : X ⟶ Y) :
    (reverse <| (Push.of σ).map f) = (Push.of σ).map (reverse f) :=
  rfl
#align quiver.push.of_reverse Quiver.Push.of_reverse

instance Push.ofMapReverse [h : HasInvolutiveReverse V] : (Push.of σ).MapReverse :=
  ⟨by simp [of_reverse]⟩
#align quiver.push.of_map_reverse Quiver.Push.ofMapReverse

end Push

/-- A quiver is preconnected iff there exists a path between any pair of
vertices.
Note that if `V` doesn't `has_reverse`, then the definition is stronger than
simply having a preconnected underlying `simple_graph`, since a path in one
direction doesn't induce one in the other.
-/
def IsPreconnected (V) [Quiver.{u + 1} V] :=
  ∀ X Y : V, Nonempty (Path X Y)
#align quiver.is_preconnected Quiver.IsPreconnected

end Quiver
