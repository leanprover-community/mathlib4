/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Util.AssertExists

/-!
# Galois connections, insertions and coinsertions

Galois connections are order theoretic adjoints, i.e. a pair of functions `u` and `l`,
such that `∀ a b, l a ≤ b ↔ a ≤ u b`.

## Main definitions

* `GaloisConnection`: A Galois connection is a pair of functions `l` and `u` satisfying
  `l a ≤ b ↔ a ≤ u b`. They are special cases of adjoint functors in category theory,
  but do not depend on the category theory library in mathlib.
* `GaloisInsertion`: A Galois insertion is a Galois connection where `l ∘ u = id`
* `GaloisCoinsertion`: A Galois coinsertion is a Galois connection where `u ∘ l = id`
-/

assert_not_exists CompleteLattice RelIso

open Function OrderDual Set

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {κ : ι → Sort*} {a₁ a₂ : α}
  {b₁ b₂ : β}

/-- A Galois connection is a pair of functions `l` and `u` satisfying
`l a ≤ b ↔ a ≤ u b`. They are special cases of adjoint functors in category theory,
but do not depend on the category theory library in mathlib. -/
def GaloisConnection [Preorder α] [Preorder β] (l : α → β) (u : β → α) :=
  ∀ a b, l a ≤ b ↔ a ≤ u b

namespace GaloisConnection

section

variable [Preorder α] [Preorder β] {l : α → β} {u : β → α}

theorem monotone_intro (hu : Monotone u) (hl : Monotone l) (hul : ∀ a, a ≤ u (l a))
    (hlu : ∀ a, l (u a) ≤ a) : GaloisConnection l u := fun _ _ =>
  ⟨fun h => (hul _).trans (hu h), fun h => (hl h).trans (hlu _)⟩

protected theorem dual {l : α → β} {u : β → α} (gc : GaloisConnection l u) :
    GaloisConnection (OrderDual.toDual ∘ u ∘ OrderDual.ofDual)
      (OrderDual.toDual ∘ l ∘ OrderDual.ofDual) :=
  fun a b => (gc b a).symm

variable (gc : GaloisConnection l u)
include gc

theorem le_iff_le {a : α} {b : β} : l a ≤ b ↔ a ≤ u b :=
  gc _ _

theorem l_le {a : α} {b : β} : a ≤ u b → l a ≤ b :=
  (gc _ _).mpr

theorem le_u {a : α} {b : β} : l a ≤ b → a ≤ u b :=
  (gc _ _).mp

theorem le_u_l (a) : a ≤ u (l a) :=
  gc.le_u <| le_rfl

theorem l_u_le (a) : l (u a) ≤ a :=
  gc.l_le <| le_rfl

theorem monotone_u : Monotone u := fun a _ H => gc.le_u ((gc.l_u_le a).trans H)

theorem monotone_l : Monotone l :=
  gc.dual.monotone_u.dual

/-- If `(l, u)` is a Galois connection, then the relation `x ≤ u (l y)` is a transitive relation.
If `l` is a closure operator (`Submodule.span`, `Subgroup.closure`, ...) and `u` is the coercion to
`Set`, this reads as "if `U` is in the closure of `V` and `V` is in the closure of `W` then `U` is
in the closure of `W`". -/
theorem le_u_l_trans {x y z : α} (hxy : x ≤ u (l y)) (hyz : y ≤ u (l z)) : x ≤ u (l z) :=
  hxy.trans (gc.monotone_u <| gc.l_le hyz)

theorem l_u_le_trans {x y z : β} (hxy : l (u x) ≤ y) (hyz : l (u y) ≤ z) : l (u x) ≤ z :=
  (gc.monotone_l <| gc.le_u hxy).trans hyz

end

section PartialOrder

variable [PartialOrder α] [Preorder β] {l : α → β} {u : β → α} (gc : GaloisConnection l u)
include gc

theorem u_l_u_eq_u (b : β) : u (l (u b)) = u b :=
  (gc.monotone_u (gc.l_u_le _)).antisymm (gc.le_u_l _)

theorem u_l_u_eq_u' : u ∘ l ∘ u = u :=
  funext gc.u_l_u_eq_u

theorem u_unique {l' : α → β} {u' : β → α} (gc' : GaloisConnection l' u') (hl : ∀ a, l a = l' a)
    {b : β} : u b = u' b :=
  le_antisymm (gc'.le_u <| hl (u b) ▸ gc.l_u_le _) (gc.le_u <| (hl (u' b)).symm ▸ gc'.l_u_le _)

/-- If there exists a `b` such that `a = u a`, then `b = l a` is one such element. -/
theorem exists_eq_u (a : α) : (∃ b : β, a = u b) ↔ a = u (l a) :=
  ⟨fun ⟨_, hS⟩ => hS.symm ▸ (gc.u_l_u_eq_u _).symm, fun HI => ⟨_, HI⟩⟩

theorem u_eq {z : α} {y : β} : u y = z ↔ ∀ x, x ≤ z ↔ l x ≤ y := by
  constructor
  · rintro rfl x
    exact (gc x y).symm
  · intro H
    exact ((H <| u y).mpr (gc.l_u_le y)).antisymm ((gc _ _).mp <| (H z).mp le_rfl)

end PartialOrder

section PartialOrder

variable [Preorder α] [PartialOrder β] {l : α → β} {u : β → α} (gc : GaloisConnection l u)
include gc

theorem l_u_l_eq_l (a : α) : l (u (l a)) = l a := gc.dual.u_l_u_eq_u _

theorem l_u_l_eq_l' : l ∘ u ∘ l = l := funext gc.l_u_l_eq_l

theorem l_unique {l' : α → β} {u' : β → α} (gc' : GaloisConnection l' u') (hu : ∀ b, u b = u' b)
    {a : α} : l a = l' a :=
  gc.dual.u_unique gc'.dual hu

/-- If there exists an `a` such that `b = l a`, then `a = u b` is one such element. -/
theorem exists_eq_l (b : β) : (∃ a : α, b = l a) ↔ b = l (u b) := gc.dual.exists_eq_u _

theorem l_eq {x : α} {z : β} : l x = z ↔ ∀ y, z ≤ y ↔ x ≤ u y := gc.dual.u_eq

end PartialOrder

section OrderTop

variable [PartialOrder α] [Preorder β] [OrderTop α]

theorem u_eq_top {l : α → β} {u : β → α} (gc : GaloisConnection l u) {x} : u x = ⊤ ↔ l ⊤ ≤ x :=
  top_le_iff.symm.trans gc.le_iff_le.symm

theorem u_top [OrderTop β] {l : α → β} {u : β → α} (gc : GaloisConnection l u) : u ⊤ = ⊤ :=
  gc.u_eq_top.2 le_top

theorem u_l_top {l : α → β} {u : β → α} (gc : GaloisConnection l u) : u (l ⊤) = ⊤ :=
  gc.u_eq_top.mpr le_rfl

end OrderTop

section OrderBot

variable [Preorder α] [PartialOrder β] [OrderBot β]

theorem l_eq_bot {l : α → β} {u : β → α} (gc : GaloisConnection l u) {x} : l x = ⊥ ↔ x ≤ u ⊥ :=
  gc.dual.u_eq_top

theorem l_bot [OrderBot α] {l : α → β} {u : β → α} (gc : GaloisConnection l u) : l ⊥ = ⊥ :=
  gc.dual.u_top

theorem l_u_bot {l : α → β} {u : β → α} (gc : GaloisConnection l u) : l (u ⊥) = ⊥ :=
  gc.l_eq_bot.mpr le_rfl

end OrderBot

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {l : α → β} {u : β → α}

theorem lt_iff_lt (gc : GaloisConnection l u) {a : α} {b : β} : b < l a ↔ u b < a :=
  lt_iff_lt_of_le_iff_le (gc a b)

end LinearOrder

-- Constructing Galois connections
section Constructions

protected theorem id [pα : Preorder α] : @GaloisConnection α α pα pα id id := fun _ _ =>
  Iff.intro (fun x => x) fun x => x

protected theorem compose [Preorder α] [Preorder β] [Preorder γ] {l1 : α → β} {u1 : β → α}
    {l2 : β → γ} {u2 : γ → β} (gc1 : GaloisConnection l1 u1) (gc2 : GaloisConnection l2 u2) :
    GaloisConnection (l2 ∘ l1) (u1 ∘ u2) := fun _ _ ↦ (gc2 _ _).trans (gc1 _ _)

protected theorem dfun {ι : Type u} {α : ι → Type v} {β : ι → Type w} [∀ i, Preorder (α i)]
    [∀ i, Preorder (β i)] (l : ∀ i, α i → β i) (u : ∀ i, β i → α i)
    (gc : ∀ i, GaloisConnection (l i) (u i)) :
    GaloisConnection (fun (a : ∀ i, α i) i => l i (a i)) fun b i => u i (b i) := fun a b =>
  forall_congr' fun i => gc i (a i) (b i)

end Constructions

theorem l_comm_of_u_comm {X : Type*} [Preorder X] {Y : Type*} [Preorder Y] {Z : Type*}
    [Preorder Z] {W : Type*} [PartialOrder W] {lYX : X → Y} {uXY : Y → X}
    (hXY : GaloisConnection lYX uXY) {lWZ : Z → W} {uZW : W → Z} (hZW : GaloisConnection lWZ uZW)
    {lWY : Y → W} {uYW : W → Y} (hWY : GaloisConnection lWY uYW) {lZX : X → Z} {uXZ : Z → X}
    (hXZ : GaloisConnection lZX uXZ) (h : ∀ w, uXZ (uZW w) = uXY (uYW w)) {x : X} :
    lWZ (lZX x) = lWY (lYX x) :=
  (hXZ.compose hZW).l_unique (hXY.compose hWY) h

theorem u_comm_of_l_comm {X : Type*} [PartialOrder X] {Y : Type*} [Preorder Y] {Z : Type*}
    [Preorder Z] {W : Type*} [Preorder W] {lYX : X → Y} {uXY : Y → X}
    (hXY : GaloisConnection lYX uXY) {lWZ : Z → W} {uZW : W → Z} (hZW : GaloisConnection lWZ uZW)
    {lWY : Y → W} {uYW : W → Y} (hWY : GaloisConnection lWY uYW) {lZX : X → Z} {uXZ : Z → X}
    (hXZ : GaloisConnection lZX uXZ) (h : ∀ x, lWZ (lZX x) = lWY (lYX x)) {w : W} :
    uXZ (uZW w) = uXY (uYW w) :=
  (hXZ.compose hZW).u_unique (hXY.compose hWY) h

theorem l_comm_iff_u_comm {X : Type*} [PartialOrder X] {Y : Type*} [Preorder Y] {Z : Type*}
    [Preorder Z] {W : Type*} [PartialOrder W] {lYX : X → Y} {uXY : Y → X}
    (hXY : GaloisConnection lYX uXY) {lWZ : Z → W} {uZW : W → Z} (hZW : GaloisConnection lWZ uZW)
    {lWY : Y → W} {uYW : W → Y} (hWY : GaloisConnection lWY uYW) {lZX : X → Z} {uXZ : Z → X}
    (hXZ : GaloisConnection lZX uXZ) :
    (∀ w : W, uXZ (uZW w) = uXY (uYW w)) ↔ ∀ x : X, lWZ (lZX x) = lWY (lYX x) :=
  ⟨hXY.l_comm_of_u_comm hZW hWY hXZ, hXY.u_comm_of_l_comm hZW hWY hXZ⟩

end GaloisConnection

/-- A Galois insertion is a Galois connection where `l ∘ u = id`. It also contains a constructive
choice function, to give better definitional equalities when lifting order structures. Dual
to `GaloisCoinsertion` -/
structure GaloisInsertion {α β : Type*} [Preorder α] [Preorder β] (l : α → β) (u : β → α) where
  /-- A contructive choice function for images of `l`. -/
  choice : ∀ x : α, u (l x) ≤ x → β
  /-- The Galois connection associated to a Galois insertion. -/
  gc : GaloisConnection l u
  /-- Main property of a Galois insertion. -/
  le_l_u : ∀ x, x ≤ l (u x)
  /-- Property of the choice function. -/
  choice_eq : ∀ a h, choice a h = l a

/-- A constructor for a Galois insertion with the trivial `choice` function. -/
def GaloisInsertion.monotoneIntro {α β : Type*} [Preorder α] [Preorder β] {l : α → β} {u : β → α}
    (hu : Monotone u) (hl : Monotone l) (hul : ∀ a, a ≤ u (l a)) (hlu : ∀ b, l (u b) = b) :
    GaloisInsertion l u where
  choice x _ := l x
  gc := GaloisConnection.monotone_intro hu hl hul fun b => le_of_eq (hlu b)
  le_l_u b := le_of_eq <| (hlu b).symm
  choice_eq _ _ := rfl

/-- Make a `GaloisInsertion l u` from a `GaloisConnection l u` such that `∀ b, b ≤ l (u b)` -/
def GaloisConnection.toGaloisInsertion {α β : Type*} [Preorder α] [Preorder β] {l : α → β}
    {u : β → α} (gc : GaloisConnection l u) (h : ∀ b, b ≤ l (u b)) : GaloisInsertion l u :=
  { choice := fun x _ => l x
    gc
    le_l_u := h
    choice_eq := fun _ _ => rfl }

/-- Lift the bottom along a Galois connection -/
def GaloisConnection.liftOrderBot {α β : Type*} [Preorder α] [OrderBot α] [PartialOrder β]
    {l : α → β} {u : β → α} (gc : GaloisConnection l u) :
    OrderBot β where
  bot := l ⊥
  bot_le _ := gc.l_le <| bot_le

namespace GaloisInsertion

variable {l : α → β} {u : β → α}

theorem l_u_eq [Preorder α] [PartialOrder β] (gi : GaloisInsertion l u) (b : β) : l (u b) = b :=
  (gi.gc.l_u_le _).antisymm (gi.le_l_u _)

theorem leftInverse_l_u [Preorder α] [PartialOrder β] (gi : GaloisInsertion l u) :
    LeftInverse l u :=
  gi.l_u_eq

theorem l_top [Preorder α] [PartialOrder β] [OrderTop α] [OrderTop β]
    (gi : GaloisInsertion l u) : l ⊤ = ⊤ :=
  top_unique <| (gi.le_l_u _).trans <| gi.gc.monotone_l le_top

theorem l_surjective [Preorder α] [PartialOrder β] (gi : GaloisInsertion l u) : Surjective l :=
  gi.leftInverse_l_u.surjective

theorem u_injective [Preorder α] [PartialOrder β] (gi : GaloisInsertion l u) : Injective u :=
  gi.leftInverse_l_u.injective

theorem u_le_u_iff [Preorder α] [Preorder β] (gi : GaloisInsertion l u) {a b} : u a ≤ u b ↔ a ≤ b :=
  ⟨fun h => (gi.le_l_u _).trans (gi.gc.l_le h), fun h => gi.gc.monotone_u h⟩

theorem strictMono_u [Preorder α] [Preorder β] (gi : GaloisInsertion l u) : StrictMono u :=
  strictMono_of_le_iff_le fun _ _ => gi.u_le_u_iff.symm

end GaloisInsertion

/-- A Galois coinsertion is a Galois connection where `u ∘ l = id`. It also contains a constructive
choice function, to give better definitional equalities when lifting order structures. Dual to
`GaloisInsertion` -/
structure GaloisCoinsertion [Preorder α] [Preorder β] (l : α → β) (u : β → α) where
  /-- A contructive choice function for images of `u`. -/
  choice : ∀ x : β, x ≤ l (u x) → α
  /-- The Galois connection associated to a Galois coinsertion. -/
  gc : GaloisConnection l u
  /-- Main property of a Galois coinsertion. -/
  u_l_le : ∀ x, u (l x) ≤ x
  /-- Property of the choice function. -/
  choice_eq : ∀ a h, choice a h = u a

/-- Make a `GaloisInsertion` between `αᵒᵈ` and `βᵒᵈ` from a `GaloisCoinsertion` between `α` and
`β`. -/
def GaloisCoinsertion.dual [Preorder α] [Preorder β] {l : α → β} {u : β → α} :
    GaloisCoinsertion l u → GaloisInsertion (toDual ∘ u ∘ ofDual) (toDual ∘ l ∘ ofDual) :=
  fun x => ⟨x.1, x.2.dual, x.3, x.4⟩

/-- Make a `GaloisCoinsertion` between `αᵒᵈ` and `βᵒᵈ` from a `GaloisInsertion` between `α` and
`β`. -/
def GaloisInsertion.dual [Preorder α] [Preorder β] {l : α → β} {u : β → α} :
    GaloisInsertion l u → GaloisCoinsertion (toDual ∘ u ∘ ofDual) (toDual ∘ l ∘ ofDual) :=
  fun x => ⟨x.1, x.2.dual, x.3, x.4⟩

/-- Make a `GaloisInsertion` between `α` and `β` from a `GaloisCoinsertion` between `αᵒᵈ` and
`βᵒᵈ`. -/
def GaloisCoinsertion.ofDual [Preorder α] [Preorder β] {l : αᵒᵈ → βᵒᵈ} {u : βᵒᵈ → αᵒᵈ} :
    GaloisCoinsertion l u → GaloisInsertion (ofDual ∘ u ∘ toDual) (ofDual ∘ l ∘ toDual) :=
  fun x => ⟨x.1, x.2.dual, x.3, x.4⟩

/-- Make a `GaloisCoinsertion` between `α` and `β` from a `GaloisInsertion` between `αᵒᵈ` and
`βᵒᵈ`. -/
def GaloisInsertion.ofDual [Preorder α] [Preorder β] {l : αᵒᵈ → βᵒᵈ} {u : βᵒᵈ → αᵒᵈ} :
    GaloisInsertion l u → GaloisCoinsertion (ofDual ∘ u ∘ toDual) (ofDual ∘ l ∘ toDual) :=
  fun x => ⟨x.1, x.2.dual, x.3, x.4⟩

/-- A constructor for a Galois coinsertion with the trivial `choice` function. -/
def GaloisCoinsertion.monotoneIntro [Preorder α] [Preorder β] {l : α → β} {u : β → α}
    (hu : Monotone u) (hl : Monotone l) (hlu : ∀ b, l (u b) ≤ b) (hul : ∀ a, u (l a) = a) :
    GaloisCoinsertion l u :=
  (GaloisInsertion.monotoneIntro hl.dual hu.dual hlu hul).ofDual

/-- Make a `GaloisCoinsertion l u` from a `GaloisConnection l u` such that `∀ a, u (l a) ≤ a` -/
def GaloisConnection.toGaloisCoinsertion {α β : Type*} [Preorder α] [Preorder β] {l : α → β}
    {u : β → α} (gc : GaloisConnection l u) (h : ∀ a, u (l a) ≤ a) : GaloisCoinsertion l u :=
  { choice := fun x _ => u x
    gc
    u_l_le := h
    choice_eq := fun _ _ => rfl }

/-- Lift the top along a Galois connection -/
def GaloisConnection.liftOrderTop {α β : Type*} [PartialOrder α] [Preorder β] [OrderTop β]
    {l : α → β} {u : β → α} (gc : GaloisConnection l u) :
    OrderTop α where
  top := u ⊤
  le_top _ := gc.le_u <| le_top

namespace GaloisCoinsertion

variable {l : α → β} {u : β → α}

theorem u_l_eq [PartialOrder α] [Preorder β] (gi : GaloisCoinsertion l u) (a : α) : u (l a) = a :=
  gi.dual.l_u_eq a

theorem u_l_leftInverse [PartialOrder α] [Preorder β] (gi : GaloisCoinsertion l u) :
    LeftInverse u l :=
  gi.u_l_eq

theorem u_bot [PartialOrder α] [Preorder β] [OrderBot α] [OrderBot β] (gi : GaloisCoinsertion l u) :
    u ⊥ = ⊥ :=
  gi.dual.l_top

theorem u_surjective [PartialOrder α] [Preorder β] (gi : GaloisCoinsertion l u) : Surjective u :=
  gi.dual.l_surjective

theorem l_injective [PartialOrder α] [Preorder β] (gi : GaloisCoinsertion l u) : Injective l :=
  gi.dual.u_injective

theorem l_le_l_iff [Preorder α] [Preorder β] (gi : GaloisCoinsertion l u) {a b} :
    l a ≤ l b ↔ a ≤ b :=
  gi.dual.u_le_u_iff

theorem strictMono_l [Preorder α] [Preorder β] (gi : GaloisCoinsertion l u) : StrictMono l :=
  fun _ _ h => gi.dual.strictMono_u h

end GaloisCoinsertion
