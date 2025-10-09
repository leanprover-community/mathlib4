/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Antoine Labelle, Rémi Bottinelli
-/
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Push

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
def Symmetrify (V : Type*) := V

instance symmetrifyQuiver (V : Type u) [Quiver V] : Quiver (Symmetrify V) :=
  ⟨fun a b : V ↦ (a ⟶ b) ⊕ (b ⟶ a)⟩

variable (U V W : Type*) [Quiver.{u + 1} U] [Quiver.{v + 1} V] [Quiver.{w + 1} W]

/-- A quiver `HasReverse` if we can reverse an arrow `p` from `a` to `b` to get an arrow
    `p.reverse` from `b` to `a`. -/
class HasReverse where
  /-- the map which sends an arrow to its reverse -/
  reverse' : ∀ {a b : V}, (a ⟶ b) → (b ⟶ a)

/-- Reverse the direction of an arrow. -/
def reverse {V} [Quiver.{v + 1} V] [HasReverse V] {a b : V} : (a ⟶ b) → (b ⟶ a) :=
  HasReverse.reverse'

/-- A quiver `HasInvolutiveReverse` if reversing twice is the identity. -/
class HasInvolutiveReverse extends HasReverse V where
  /-- `reverse` is involutive -/
  inv' : ∀ {a b : V} (f : a ⟶ b), reverse (reverse f) = f

variable {U V W}

@[simp]
theorem reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) :
    reverse (reverse f) = f := by apply h.inv'

@[simp]
theorem reverse_inj [h : HasInvolutiveReverse V] {a b : V}
    (f g : a ⟶ b) : reverse f = reverse g ↔ f = g := by
  constructor
  · rintro h
    simpa using congr_arg Quiver.reverse h
  · rintro h
    congr

theorem eq_reverse_iff [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b)
    (g : b ⟶ a) : f = reverse g ↔ reverse f = g := by
  rw [← reverse_inj, reverse_reverse]

section MapReverse

variable [HasReverse U] [HasReverse V] [HasReverse W]

/-- A prefunctor preserving reversal of arrows -/
class _root_.Prefunctor.MapReverse (φ : U ⥤q V) : Prop where
  /-- The image of a reverse is the reverse of the image. -/
  map_reverse' : ∀ {u v : U} (e : u ⟶ v), φ.map (reverse e) = reverse (φ.map e)

@[simp]
theorem _root_.Prefunctor.map_reverse (φ : U ⥤q V) [φ.MapReverse]
    {u v : U} (e : u ⟶ v) : φ.map (reverse e) = reverse (φ.map e) :=
  Prefunctor.MapReverse.map_reverse' e

instance _root_.Prefunctor.mapReverseComp
    (φ : U ⥤q V) (ψ : V ⥤q W) [φ.MapReverse] [ψ.MapReverse] :
    (φ ⋙q ψ).MapReverse where
  map_reverse' e := by
    simp only [Prefunctor.comp_map, Prefunctor.MapReverse.map_reverse']

instance _root_.Prefunctor.mapReverseId :
    (Prefunctor.id U).MapReverse where
  map_reverse' _ := rfl

end MapReverse

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

section Paths

/-- Shorthand for the "forward" arrow corresponding to `f` in `symmetrify V` -/
abbrev Hom.toPos {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom X Y :=
  Sum.inl f

/-- Shorthand for the "backward" arrow corresponding to `f` in `symmetrify V` -/
abbrev Hom.toNeg {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom Y X :=
  Sum.inr f

/-- Reverse the direction of a path. -/
@[simp]
def Path.reverse [HasReverse V] {a : V} : ∀ {b}, Path a b → Path b a
  | _, Path.nil => Path.nil
  | _, Path.cons p e => (Quiver.reverse e).toPath.comp p.reverse

@[simp]
theorem Path.reverse_toPath [HasReverse V] {a b : V} (f : a ⟶ b) :
    f.toPath.reverse = (Quiver.reverse f).toPath :=
  rfl

@[simp]
theorem Path.reverse_comp [HasReverse V] {a b c : V} (p : Path a b) (q : Path b c) :
    (p.comp q).reverse = q.reverse.comp p.reverse := by
  induction q with
  | nil => simp
  | cons _ _ h => simp [h]

@[simp]
theorem Path.reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (p : Path a b) :
    p.reverse.reverse = p := by
  induction p with
  | nil => simp
  | cons _ _ h =>
    rw [Path.reverse, Path.reverse_comp, h, Path.reverse_toPath, Quiver.reverse_reverse]
    rfl

end Paths

namespace Symmetrify

/-- The inclusion of a quiver in its symmetrification -/
@[simps]
def of : Prefunctor V (Symmetrify V) where
  obj := id
  map := Sum.inl

variable {V' : Type*} [Quiver.{v' + 1} V']

/-- Given a quiver `V'` with reversible arrows, a prefunctor to `V'` can be lifted to one from
    `Symmetrify V` to `V'` -/
def lift [HasReverse V'] (φ : Prefunctor V V') :
    Prefunctor (Symmetrify V) V' where
  obj := φ.obj
  map
  | Sum.inl g => φ.map g
  | Sum.inr g => reverse (φ.map g)

theorem lift_spec [HasReverse V'] (φ : Prefunctor V V') :
    Symmetrify.of.comp (Symmetrify.lift φ) = φ := by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rfl

theorem lift_reverse [h : HasInvolutiveReverse V']
    (φ : Prefunctor V V') {X Y : Symmetrify V} (f : X ⟶ Y) :
    (Symmetrify.lift φ).map (Quiver.reverse f) = Quiver.reverse ((Symmetrify.lift φ).map f) := by
  dsimp [Symmetrify.lift]; cases f
  · simp only
    rfl
  · simp only [reverse_reverse]
    rfl

/-- `lift φ` is the only prefunctor extending `φ` and preserving reverses. -/
theorem lift_unique [HasReverse V'] (φ : V ⥤q V') (Φ : Symmetrify V ⥤q V') (hΦ : (of ⋙q Φ) = φ)
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

/-- A prefunctor canonically defines a prefunctor of the symmetrifications. -/
@[simps]
def _root_.Prefunctor.symmetrify (φ : U ⥤q V) : Symmetrify U ⥤q Symmetrify V where
  obj := φ.obj
  map := Sum.map φ.map φ.map

instance _root_.Prefunctor.symmetrify_mapReverse (φ : U ⥤q V) :
    Prefunctor.MapReverse φ.symmetrify :=
  ⟨fun e => by cases e <;> rfl⟩

end Symmetrify

namespace Push

variable {V' : Type*} (σ : V → V')

instance [HasReverse V] : HasReverse (Quiver.Push σ) where
  reverse' := fun
              | PushQuiver.arrow f => PushQuiver.arrow (reverse f)

instance [h : HasInvolutiveReverse V] :
    HasInvolutiveReverse (Push σ) where
  reverse' := fun
  | PushQuiver.arrow f => PushQuiver.arrow (reverse f)
  inv' := fun
  | PushQuiver.arrow f => by dsimp [reverse]; congr; apply h.inv'

theorem of_reverse [HasInvolutiveReverse V] (X Y : V) (f : X ⟶ Y) :
    (reverse <| (Push.of σ).map f) = (Push.of σ).map (reverse f) :=
  rfl

instance ofMapReverse [h : HasInvolutiveReverse V] : (Push.of σ).MapReverse :=
  ⟨by simp [of_reverse]⟩

end Push

end Quiver
