/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Antoine Labelle, Rémi Bottinelli
-/
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Push
import Mathlib.Data.Sum.Basic

#align_import combinatorics.quiver.symmetric from "leanprover-community/mathlib"@"706d88f2b8fdfeb0b22796433d7a6c1a010af9f2"

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
def Symmetrify (V : Type*) := V
#align quiver.symmetrify Quiver.Symmetrify

instance symmetrifyQuiver (V : Type u) [Quiver V] : Quiver (Symmetrify V) :=
  ⟨fun a b : V ↦ Sum (a ⟶ b) (b ⟶ a)⟩

variable (U V W : Type*) [Quiver.{u + 1} U] [Quiver.{v + 1} V] [Quiver.{w + 1} W]

/-- A quiver `HasReverse` if we can reverse an arrow `p` from `a` to `b` to get an arrow
    `p.reverse` from `b` to `a`.-/
class HasReverse where
  /-- the map which sends an arrow to its reverse -/
  reverse' : ∀ {a b : V}, (a ⟶ b) → (b ⟶ a)
#align quiver.has_reverse Quiver.HasReverse

/-- Reverse the direction of an arrow. -/
def reverse {V} [Quiver.{v + 1} V] [HasReverse V] {a b : V} : (a ⟶ b) → (b ⟶ a) :=
  HasReverse.reverse'
#align quiver.reverse Quiver.reverse

/-- A quiver `HasInvolutiveReverse` if reversing twice is the identity. -/
class HasInvolutiveReverse extends HasReverse V where
  /-- `reverse` is involutive -/
  inv' : ∀ {a b : V} (f : a ⟶ b), reverse (reverse f) = f
#align quiver.has_involutive_reverse Quiver.HasInvolutiveReverse

variable {U V W}

@[simp]
theorem reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) :
    reverse (reverse f) = f := by apply h.inv'
                                  -- 🎉 no goals
#align quiver.reverse_reverse Quiver.reverse_reverse

@[simp]
theorem reverse_inj [h : HasInvolutiveReverse V] {a b : V}
    (f g : a ⟶ b) : reverse f = reverse g ↔ f = g := by
  constructor
  -- ⊢ reverse f = reverse g → f = g
  · rintro h
    -- ⊢ f = g
    simpa using congr_arg Quiver.reverse h
    -- 🎉 no goals
  · rintro h
    -- ⊢ reverse f = reverse g
    congr
    -- 🎉 no goals
#align quiver.reverse_inj Quiver.reverse_inj

theorem eq_reverse_iff [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b)
    (g : b ⟶ a) : f = reverse g ↔ reverse f = g := by
  rw [←reverse_inj, reverse_reverse]
  -- 🎉 no goals
#align quiver.eq_reverse_iff Quiver.eq_reverse_iff

section MapReverse

variable [HasReverse U] [HasReverse V] [HasReverse W]

/-- A prefunctor preserving reversal of arrows -/
class _root_.Prefunctor.MapReverse (φ : U ⥤q V) : Prop where
  /-- The image of a reverse is the reverse of the image. -/
  map_reverse' : ∀ {u v : U} (e : u ⟶ v), φ.map (reverse e) = reverse (φ.map e)
#align prefunctor.map_reverse Prefunctor.MapReverse

@[simp]
theorem _root_.Prefunctor.map_reverse (φ : U ⥤q V) [φ.MapReverse]
    {u v : U} (e : u ⟶ v) : φ.map (reverse e) = reverse (φ.map e) :=
  Prefunctor.MapReverse.map_reverse' e
#align prefunctor.map_reverse' Prefunctor.map_reverse

instance _root_.Prefunctor.mapReverseComp
    (φ : U ⥤q V) (ψ : V ⥤q W) [φ.MapReverse] [ψ.MapReverse] :
    (φ ⋙q ψ).MapReverse where
  map_reverse' e := by
    simp only [Prefunctor.comp_map, Prefunctor.MapReverse.map_reverse']
    -- 🎉 no goals
#align prefunctor.map_reverse_comp Prefunctor.mapReverseComp

instance _root_.Prefunctor.mapReverseId :
    (Prefunctor.id U).MapReverse where
  map_reverse' _ := rfl
#align prefunctor.map_reverse_id Prefunctor.mapReverseId

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
#align quiver.path.reverse Quiver.Path.reverse

@[simp]
theorem Path.reverse_toPath [HasReverse V] {a b : V} (f : a ⟶ b) :
    f.toPath.reverse = (Quiver.reverse f).toPath :=
  rfl
#align quiver.path.reverse_to_path Quiver.Path.reverse_toPath

@[simp]
theorem Path.reverse_comp [HasReverse V] {a b c : V} (p : Path a b) (q : Path b c) :
    (p.comp q).reverse = q.reverse.comp p.reverse := by
  induction' q with _ _ _ _ h
  -- ⊢ reverse (comp p nil) = comp (reverse nil) (reverse p)
  · simp
    -- 🎉 no goals
  · simp [h]
    -- 🎉 no goals
#align quiver.path.reverse_comp Quiver.Path.reverse_comp

@[simp]
theorem Path.reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (p : Path a b) :
    p.reverse.reverse = p := by
  induction' p with _ _ _ _ h
  -- ⊢ reverse (reverse nil) = nil
  · simp
    -- 🎉 no goals
  · rw [Path.reverse, Path.reverse_comp, h, Path.reverse_toPath, Quiver.reverse_reverse]
    -- ⊢ comp a✝¹ (Hom.toPath a✝) = cons a✝¹ a✝
    rfl
    -- 🎉 no goals
#align quiver.path.reverse_reverse Quiver.Path.reverse_reverse

end Paths

namespace Symmetrify

/-- The inclusion of a quiver in its symmetrification -/
def of : Prefunctor V (Symmetrify V) where
  obj := id
  map := Sum.inl
#align quiver.symmetrify.of Quiver.Symmetrify.of

variable {V' : Type*} [Quiver.{v' + 1} V']

/-- Given a quiver `V'` with reversible arrows, a prefunctor to `V'` can be lifted to one from
    `Symmetrify V` to `V'` -/
def lift [HasReverse V'] (φ : Prefunctor V V') :
    Prefunctor (Symmetrify V) V' where
  obj := φ.obj
  map f := match f with
  | Sum.inl g => φ.map g
  | Sum.inr g => reverse (φ.map g)
#align quiver.symmetrify.lift Quiver.Symmetrify.lift

theorem lift_spec [HasReverse V'] (φ : Prefunctor V V') :
    Symmetrify.of.comp (Symmetrify.lift φ) = φ := by
  fapply Prefunctor.ext
  -- ⊢ ∀ (X : V), (of ⋙q lift φ).obj X = φ.obj X
  · rintro X
    -- ⊢ (of ⋙q lift φ).obj X = φ.obj X
    rfl
    -- 🎉 no goals
  · rintro X Y f
    -- ⊢ (of ⋙q lift φ).map f = Eq.recOn (_ : φ.obj Y = (of ⋙q lift φ).obj Y) (Eq.rec …
    rfl
    -- 🎉 no goals
#align quiver.symmetrify.lift_spec Quiver.Symmetrify.lift_spec

theorem lift_reverse [h : HasInvolutiveReverse V']
    (φ : Prefunctor V V') {X Y : Symmetrify V} (f : X ⟶ Y) :
    (Symmetrify.lift φ).map (Quiver.reverse f) = Quiver.reverse ((Symmetrify.lift φ).map f) := by
  dsimp [Symmetrify.lift]; cases f
  -- ⊢ (match Sum.swap f with
  · simp only
    -- ⊢ (match Sum.swap (Sum.inl val✝) with
    rfl
    -- 🎉 no goals
  · simp only [reverse_reverse]
    -- ⊢ (match Sum.swap (Sum.inr val✝) with
    rfl
    -- 🎉 no goals
#align quiver.symmetrify.lift_reverse Quiver.Symmetrify.lift_reverse

/-- `lift φ` is the only prefunctor extending `φ` and preserving reverses. -/
theorem lift_unique [HasReverse V'] (φ : V ⥤q V') (Φ : Symmetrify V ⥤q V') (hΦ : (of ⋙q Φ) = φ)
    (hΦinv : ∀ {X Y : Symmetrify V} (f : X ⟶ Y),
      Φ.map (Quiver.reverse f) = Quiver.reverse (Φ.map f)) :
    Φ = Symmetrify.lift φ := by
  subst_vars
  -- ⊢ Φ = lift (of ⋙q Φ)
  fapply Prefunctor.ext
  -- ⊢ ∀ (X : Symmetrify V), Φ.obj X = (lift (of ⋙q Φ)).obj X
  · rintro X
    -- ⊢ Φ.obj X = (lift (of ⋙q Φ)).obj X
    rfl
    -- 🎉 no goals
  · rintro X Y f
    -- ⊢ Φ.map f = Eq.recOn (_ : (lift (of ⋙q Φ)).obj Y = Φ.obj Y) (Eq.recOn (_ : (li …
    cases f
    -- ⊢ Φ.map (Sum.inl val✝) = Eq.recOn (_ : (lift (of ⋙q Φ)).obj Y = Φ.obj Y) (Eq.r …
    · rfl
      -- 🎉 no goals
    · exact hΦinv (Sum.inl _)
      -- 🎉 no goals
#align quiver.symmetrify.lift_unique Quiver.Symmetrify.lift_unique

/-- A prefunctor canonically defines a prefunctor of the symmetrifications. -/
@[simps]
def _root_.Prefunctor.symmetrify (φ : U ⥤q V) : Symmetrify U ⥤q Symmetrify V
    where
  obj := φ.obj
  map := Sum.map φ.map φ.map
#align prefunctor.symmetrify Prefunctor.symmetrify

instance _root_.Prefunctor.symmetrify_mapReverse (φ : U ⥤q V) :
    Prefunctor.MapReverse φ.symmetrify :=
  ⟨fun e => by cases e <;> rfl⟩
               -- ⊢ (Prefunctor.symmetrify φ).map (reverse (Sum.inl val✝)) = reverse ((Prefuncto …
                           -- 🎉 no goals
                           -- 🎉 no goals
#align prefunctor.symmetrify_map_reverse Prefunctor.symmetrify_mapReverse

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
                             -- ⊢ PushQuiver.arrow (HasReverse.reverse' (HasReverse.reverse' f)) = PushQuiver. …
                                              -- ⊢ HasReverse.reverse' (HasReverse.reverse' f) = f
                                                     -- 🎉 no goals

theorem of_reverse [HasInvolutiveReverse V] (X Y : V) (f : X ⟶ Y) :
    (reverse <| (Push.of σ).map f) = (Push.of σ).map (reverse f) :=
  rfl
#align quiver.push.of_reverse Quiver.Push.of_reverse

instance ofMapReverse [h : HasInvolutiveReverse V] : (Push.of σ).MapReverse :=
  ⟨by simp [of_reverse]⟩
      -- 🎉 no goals
#align quiver.push.of_map_reverse Quiver.Push.ofMapReverse

end Push

/-- A quiver is preconnected iff there exists a path between any pair of
vertices.
Note that if `V` doesn't `HasReverse`, then the definition is stronger than
simply having a preconnected underlying `SimpleGraph`, since a path in one
direction doesn't induce one in the other.
-/
def IsPreconnected (V) [Quiver.{u + 1} V] :=
  ∀ X Y : V, Nonempty (Path X Y)
#align quiver.is_preconnected Quiver.IsPreconnected

end Quiver
