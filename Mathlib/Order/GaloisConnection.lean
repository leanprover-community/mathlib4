/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Order.CompleteLattice
import Mathlib.Order.Synonym
import Mathlib.Order.Hom.Set
import Mathlib.Order.Bounds.Image

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

## Implementation details

Galois insertions can be used to lift order structures from one type to another.
For example, if `α` is a complete lattice, and `l : α → β` and `u : β → α` form a Galois insertion,
then `β` is also a complete lattice. `l` is the lower adjoint and `u` is the upper adjoint.

An example of a Galois insertion is in group theory. If `G` is a group, then there is a Galois
insertion between the set of subsets of `G`, `Set G`, and the set of subgroups of `G`,
`Subgroup G`. The lower adjoint is `Subgroup.closure`, taking the `Subgroup` generated by a `Set`,
and the upper adjoint is the coercion from `Subgroup G` to `Set G`, taking the underlying set
of a subgroup.

Naively lifting a lattice structure along this Galois insertion would mean that the definition
of `inf` on subgroups would be `Subgroup.closure (↑S ∩ ↑T)`. This is an undesirable definition
because the intersection of subgroups is already a subgroup, so there is no need to take the
closure. For this reason a `choice` function is added as a field to the `GaloisInsertion`
structure. It has type `Π S : Set G, ↑(closure S) ≤ S → Subgroup G`. When `↑(closure S) ≤ S`, then
`S` is already a subgroup, so this function can be defined using `Subgroup.mk` and not `closure`.
This means the infimum of subgroups will be defined to be the intersection of sets, paired
with a proof that intersection of subgroups is a subgroup, rather than the closure of the
intersection.
-/


open Function OrderDual Set

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {κ : ι → Sort*} {a₁ a₂ : α}
  {b₁ b₂ : β}

/-- A Galois connection is a pair of functions `l` and `u` satisfying
`l a ≤ b ↔ a ≤ u b`. They are special cases of adjoint functors in category theory,
but do not depend on the category theory library in mathlib. -/
def GaloisConnection [Preorder α] [Preorder β] (l : α → β) (u : β → α) :=
  ∀ a b, l a ≤ b ↔ a ≤ u b

/-- Makes a Galois connection from an order-preserving bijection. -/
theorem OrderIso.to_galoisConnection [Preorder α] [Preorder β] (oi : α ≃o β) :
    GaloisConnection oi oi.symm := fun _ _ => oi.rel_symm_apply.symm

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

theorem upperBounds_l_image (s : Set α) :
    upperBounds (l '' s) = u ⁻¹' upperBounds s :=
  Set.ext fun b => by simp [upperBounds, gc _ _]

theorem lowerBounds_u_image (s : Set β) :
    lowerBounds (u '' s) = l ⁻¹' lowerBounds s :=
  gc.dual.upperBounds_l_image s

theorem bddAbove_l_image {s : Set α} : BddAbove (l '' s) ↔ BddAbove s :=
  ⟨fun ⟨x, hx⟩ => ⟨u x, by rwa [gc.upperBounds_l_image] at hx⟩, gc.monotone_l.map_bddAbove⟩

theorem bddBelow_u_image {s : Set β} : BddBelow (u '' s) ↔ BddBelow s :=
  gc.dual.bddAbove_l_image

theorem isLUB_l_image {s : Set α} {a : α} (h : IsLUB s a) : IsLUB (l '' s) (l a) :=
  ⟨gc.monotone_l.mem_upperBounds_image h.left, fun b hb =>
    gc.l_le <| h.right <| by rwa [gc.upperBounds_l_image] at hb⟩

theorem isGLB_u_image {s : Set β} {b : β} (h : IsGLB s b) : IsGLB (u '' s) (u b) :=
  gc.dual.isLUB_l_image h

theorem isLeast_l {a : α} : IsLeast { b | a ≤ u b } (l a) :=
  ⟨gc.le_u_l _, fun _ hb => gc.l_le hb⟩

theorem isGreatest_u {b : β} : IsGreatest { a | l a ≤ b } (u b) :=
  gc.dual.isLeast_l

theorem isGLB_l {a : α} : IsGLB { b | a ≤ u b } (l a) :=
  gc.isLeast_l.isGLB

theorem isLUB_u {b : β} : IsLUB { a | l a ≤ b } (u b) :=
  gc.isGreatest_u.isLUB

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

theorem l_u_top {l : α → β} {u : β → α} (gc : GaloisConnection l u) : u (l ⊤) = ⊤ :=
  gc.u_eq_top.mpr le_rfl

end OrderTop

section OrderBot

variable [Preorder α] [PartialOrder β] [OrderBot β]

theorem l_eq_bot {l : α → β} {u : β → α} (gc : GaloisConnection l u) {x} : l x = ⊥ ↔ x ≤ u ⊥ :=
  gc.dual.u_eq_top

theorem l_bot [OrderBot α] {l : α → β} {u : β → α} (gc : GaloisConnection l u) : l ⊥ = ⊥ :=
  gc.dual.u_top

end OrderBot

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β] {l : α → β} {u : β → α}

theorem l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) = l a₁ ⊔ l a₂ :=
  (gc.isLUB_l_image isLUB_pair).unique <| by simp only [image_pair, isLUB_pair]

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α] [SemilatticeInf β] {l : α → β} {u : β → α}

theorem u_inf (gc : GaloisConnection l u) : u (b₁ ⊓ b₂) = u b₁ ⊓ u b₂ := gc.dual.l_sup

end SemilatticeInf

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] {l : α → β} {u : β → α}

theorem l_iSup (gc : GaloisConnection l u) {f : ι → α} : l (iSup f) = ⨆ i, l (f i) :=
  Eq.symm <|
    IsLUB.iSup_eq <|
      show IsLUB (range (l ∘ f)) (l (iSup f)) by
        rw [range_comp, ← sSup_range]; exact gc.isLUB_l_image (isLUB_sSup _)

theorem l_iSup₂ (gc : GaloisConnection l u) {f : ∀ i, κ i → α} :
    l (⨆ (i) (j), f i j) = ⨆ (i) (j), l (f i j) := by
  simp_rw [gc.l_iSup]

variable (gc : GaloisConnection l u)
include gc

theorem u_iInf {f : ι → β} : u (iInf f) = ⨅ i, u (f i) :=
  gc.dual.l_iSup

theorem u_iInf₂ {f : ∀ i, κ i → β} : u (⨅ (i) (j), f i j) = ⨅ (i) (j), u (f i j) :=
  gc.dual.l_iSup₂

theorem l_sSup {s : Set α} : l (sSup s) = ⨆ a ∈ s, l a := by
  simp only [sSup_eq_iSup, gc.l_iSup]

theorem u_sInf {s : Set β} : u (sInf s) = ⨅ a ∈ s, u a :=
  gc.dual.l_sSup

end CompleteLattice

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

protected theorem compl [BooleanAlgebra α] [BooleanAlgebra β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) :
    GaloisConnection (compl ∘ u ∘ compl) (compl ∘ l ∘ compl) := fun a b ↦ by
  dsimp
  rw [le_compl_iff_le_compl, gc, compl_le_iff_compl_le]

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

section

/-- `sSup` and `Iic` form a Galois connection. -/
theorem gc_sSup_Iic [CompleteSemilatticeSup α] :
    GaloisConnection (sSup : Set α → α) (Iic : α → Set α) :=
  fun _ _ ↦ sSup_le_iff

/-- `toDual ∘ Ici` and `sInf ∘ ofDual` form a Galois connection. -/
theorem gc_Ici_sInf [CompleteSemilatticeInf α] :
    GaloisConnection (toDual ∘ Ici : α → (Set α)ᵒᵈ) (sInf ∘ ofDual : (Set α)ᵒᵈ → α) :=
  fun _ _ ↦ le_sInf_iff.symm

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] {s : Set α}
  {t : Set β} {l u : α → β → γ} {l₁ u₁ : β → γ → α} {l₂ u₂ : α → γ → β}

theorem sSup_image2_eq_sSup_sSup (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) : sSup (image2 l s t) = l (sSup s) (sSup t) := by
  simp_rw [sSup_image2, ← (h₂ _).l_sSup, ← (h₁ _).l_sSup]

theorem sSup_image2_eq_sSup_sInf (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    sSup (image2 l s t) = l (sSup s) (sInf t) :=
  sSup_image2_eq_sSup_sSup (β := βᵒᵈ) h₁ h₂

theorem sSup_image2_eq_sInf_sSup (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) : sSup (image2 l s t) = l (sInf s) (sSup t) :=
  sSup_image2_eq_sSup_sSup (α := αᵒᵈ) h₁ h₂

theorem sSup_image2_eq_sInf_sInf (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    sSup (image2 l s t) = l (sInf s) (sInf t) :=
  sSup_image2_eq_sSup_sSup (α := αᵒᵈ) (β := βᵒᵈ) h₁ h₂

theorem sInf_image2_eq_sInf_sInf (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) : sInf (image2 u s t) = u (sInf s) (sInf t) := by
  simp_rw [sInf_image2, ← (h₂ _).u_sInf, ← (h₁ _).u_sInf]

theorem sInf_image2_eq_sInf_sSup (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    sInf (image2 u s t) = u (sInf s) (sSup t) :=
  sInf_image2_eq_sInf_sInf (β := βᵒᵈ) h₁ h₂

theorem sInf_image2_eq_sSup_sInf (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) : sInf (image2 u s t) = u (sSup s) (sInf t) :=
  sInf_image2_eq_sInf_sInf (α := αᵒᵈ) h₁ h₂

theorem sInf_image2_eq_sSup_sSup (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    sInf (image2 u s t) = u (sSup s) (sSup t) :=
  sInf_image2_eq_sInf_sInf (α := αᵒᵈ) (β := βᵒᵈ) h₁ h₂

end

namespace OrderIso

variable [Preorder α] [Preorder β]

@[simp]
theorem bddAbove_image (e : α ≃o β) {s : Set α} : BddAbove (e '' s) ↔ BddAbove s :=
  e.to_galoisConnection.bddAbove_l_image

@[simp]
theorem bddBelow_image (e : α ≃o β) {s : Set α} : BddBelow (e '' s) ↔ BddBelow s :=
  e.dual.bddAbove_image

@[simp]
theorem bddAbove_preimage (e : α ≃o β) {s : Set β} : BddAbove (e ⁻¹' s) ↔ BddAbove s := by
  rw [← e.bddAbove_image, e.image_preimage]

@[simp]
theorem bddBelow_preimage (e : α ≃o β) {s : Set β} : BddBelow (e ⁻¹' s) ↔ BddBelow s := by
  rw [← e.bddBelow_image, e.image_preimage]

end OrderIso

namespace Nat

theorem galoisConnection_mul_div {k : ℕ} (h : 0 < k) :
    GaloisConnection (fun n => n * k) fun n => n / k := fun _ _ => (le_div_iff_mul_le h).symm

end Nat

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/5171): this used to have a `@[nolint has_nonempty_instance]`
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

/-- Makes a Galois insertion from an order-preserving bijection. -/
protected def OrderIso.toGaloisInsertion [Preorder α] [Preorder β] (oi : α ≃o β) :
    GaloisInsertion oi oi.symm where
  choice b _ := oi b
  gc := oi.to_galoisConnection
  le_l_u g := le_of_eq (oi.right_inv g).symm
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

theorem l_sup_u [SemilatticeSup α] [SemilatticeSup β] (gi : GaloisInsertion l u) (a b : β) :
    l (u a ⊔ u b) = a ⊔ b :=
  calc
    l (u a ⊔ u b) = l (u a) ⊔ l (u b) := gi.gc.l_sup
    _ = a ⊔ b := by simp only [gi.l_u_eq]

theorem l_iSup_u [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u) {ι : Sort x}
    (f : ι → β) : l (⨆ i, u (f i)) = ⨆ i, f i :=
  calc
    l (⨆ i : ι, u (f i)) = ⨆ i : ι, l (u (f i)) := gi.gc.l_iSup
    _ = ⨆ i : ι, f i := congr_arg _ <| funext fun i => gi.l_u_eq (f i)

theorem l_biSup_u [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u) {ι : Sort x}
    {p : ι → Prop} (f : ∀ i, p i → β) : l (⨆ (i) (hi), u (f i hi)) = ⨆ (i) (hi), f i hi := by
  simp only [iSup_subtype', gi.l_iSup_u]

theorem l_sSup_u_image [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u)
    (s : Set β) : l (sSup (u '' s)) = sSup s := by rw [sSup_image, gi.l_biSup_u, sSup_eq_iSup]

theorem l_inf_u [SemilatticeInf α] [SemilatticeInf β] (gi : GaloisInsertion l u) (a b : β) :
    l (u a ⊓ u b) = a ⊓ b :=
  calc
    l (u a ⊓ u b) = l (u (a ⊓ b)) := congr_arg l gi.gc.u_inf.symm
    _ = a ⊓ b := by simp only [gi.l_u_eq]

theorem l_iInf_u [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u) {ι : Sort x}
    (f : ι → β) : l (⨅ i, u (f i)) = ⨅ i, f i :=
  calc
    l (⨅ i : ι, u (f i)) = l (u (⨅ i : ι, f i)) := congr_arg l gi.gc.u_iInf.symm
    _ = ⨅ i : ι, f i := gi.l_u_eq _

theorem l_biInf_u [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u) {ι : Sort x}
    {p : ι → Prop} (f : ∀ (i) (_ : p i), β) : l (⨅ (i) (hi), u (f i hi)) = ⨅ (i) (hi), f i hi := by
  simp only [iInf_subtype', gi.l_iInf_u]

theorem l_sInf_u_image [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u)
    (s : Set β) : l (sInf (u '' s)) = sInf s := by rw [sInf_image, gi.l_biInf_u, sInf_eq_iInf]

theorem l_iInf_of_ul_eq_self [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u)
    {ι : Sort x} (f : ι → α) (hf : ∀ i, u (l (f i)) = f i) : l (⨅ i, f i) = ⨅ i, l (f i) :=
  calc
    l (⨅ i, f i) = l (⨅ i : ι, u (l (f i))) := by simp [hf]
    _ = ⨅ i, l (f i) := gi.l_iInf_u _

theorem l_biInf_of_ul_eq_self [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u)
    {ι : Sort x} {p : ι → Prop} (f : ∀ (i) (_ : p i), α) (hf : ∀ i hi, u (l (f i hi)) = f i hi) :
    l (⨅ (i) (hi), f i hi) = ⨅ (i) (hi), l (f i hi) := by
  rw [iInf_subtype', iInf_subtype']
  exact gi.l_iInf_of_ul_eq_self _ fun _ => hf _ _

theorem u_le_u_iff [Preorder α] [Preorder β] (gi : GaloisInsertion l u) {a b} : u a ≤ u b ↔ a ≤ b :=
  ⟨fun h => (gi.le_l_u _).trans (gi.gc.l_le h), fun h => gi.gc.monotone_u h⟩

theorem strictMono_u [Preorder α] [Preorder β] (gi : GaloisInsertion l u) : StrictMono u :=
  strictMono_of_le_iff_le fun _ _ => gi.u_le_u_iff.symm

theorem isLUB_of_u_image [Preorder α] [Preorder β] (gi : GaloisInsertion l u) {s : Set β} {a : α}
    (hs : IsLUB (u '' s) a) : IsLUB s (l a) :=
  ⟨fun x hx => (gi.le_l_u x).trans <| gi.gc.monotone_l <| hs.1 <| mem_image_of_mem _ hx, fun _ hx =>
    gi.gc.l_le <| hs.2 <| gi.gc.monotone_u.mem_upperBounds_image hx⟩

theorem isGLB_of_u_image [Preorder α] [Preorder β] (gi : GaloisInsertion l u) {s : Set β} {a : α}
    (hs : IsGLB (u '' s) a) : IsGLB s (l a) :=
  ⟨fun _ hx => gi.gc.l_le <| hs.1 <| mem_image_of_mem _ hx, fun x hx =>
    (gi.le_l_u x).trans <| gi.gc.monotone_l <| hs.2 <| gi.gc.monotone_u.mem_lowerBounds_image hx⟩

section lift

variable [PartialOrder β]

-- See note [reducible non instances]
/-- Lift the suprema along a Galois insertion -/
abbrev liftSemilatticeSup [SemilatticeSup α] (gi : GaloisInsertion l u) : SemilatticeSup β :=
  { ‹PartialOrder β› with
    sup := fun a b => l (u a ⊔ u b)
    le_sup_left := fun a _ => (gi.le_l_u a).trans <| gi.gc.monotone_l <| le_sup_left
    le_sup_right := fun _ b => (gi.le_l_u b).trans <| gi.gc.monotone_l <| le_sup_right
    sup_le := fun _ _ _ hac hbc =>
      gi.gc.l_le <| sup_le (gi.gc.monotone_u hac) (gi.gc.monotone_u hbc) }

-- See note [reducible non instances]
/-- Lift the infima along a Galois insertion -/
abbrev liftSemilatticeInf [SemilatticeInf α] (gi : GaloisInsertion l u) : SemilatticeInf β :=
  { ‹PartialOrder β› with
    inf := fun a b =>
      gi.choice (u a ⊓ u b) <|
        le_inf (gi.gc.monotone_u <| gi.gc.l_le <| inf_le_left)
          (gi.gc.monotone_u <| gi.gc.l_le <| inf_le_right)
    inf_le_left := by simp only [gi.choice_eq]; exact fun a b => gi.gc.l_le inf_le_left
    inf_le_right := by simp only [gi.choice_eq]; exact fun a b => gi.gc.l_le inf_le_right
    le_inf := by
      simp only [gi.choice_eq]
      exact fun a b c hac hbc =>
        (gi.le_l_u a).trans <|
          gi.gc.monotone_l <| le_inf (gi.gc.monotone_u hac) (gi.gc.monotone_u hbc) }

-- See note [reducible non instances]
/-- Lift the suprema and infima along a Galois insertion -/
abbrev liftLattice [Lattice α] (gi : GaloisInsertion l u) : Lattice β :=
  { gi.liftSemilatticeSup, gi.liftSemilatticeInf with }

-- See note [reducible non instances]
/-- Lift the top along a Galois insertion -/
abbrev liftOrderTop [Preorder α] [OrderTop α] (gi : GaloisInsertion l u) :
    OrderTop β where
  top := gi.choice ⊤ <| le_top
  le_top := by
    simp only [gi.choice_eq]; exact fun b => (gi.le_l_u b).trans (gi.gc.monotone_l le_top)

-- See note [reducible non instances]
/-- Lift the top, bottom, suprema, and infima along a Galois insertion -/
abbrev liftBoundedOrder [Preorder α] [BoundedOrder α] (gi : GaloisInsertion l u) : BoundedOrder β :=
  { gi.liftOrderTop, gi.gc.liftOrderBot with }

-- See note [reducible non instances]
/-- Lift all suprema and infima along a Galois insertion -/
abbrev liftCompleteLattice [CompleteLattice α] (gi : GaloisInsertion l u) : CompleteLattice β :=
  { gi.liftBoundedOrder, gi.liftLattice with
    sSup := fun s => l (sSup (u '' s))
    sSup_le := fun _ => (gi.isLUB_of_u_image (isLUB_sSup _)).2
    le_sSup := fun _ => (gi.isLUB_of_u_image (isLUB_sSup _)).1
    sInf := fun s =>
      gi.choice (sInf (u '' s)) <|
        (isGLB_sInf _).2 <|
          gi.gc.monotone_u.mem_lowerBounds_image (gi.isGLB_of_u_image <| isGLB_sInf _).1
    sInf_le := fun s => by dsimp; rw [gi.choice_eq]; exact (gi.isGLB_of_u_image (isGLB_sInf _)).1
    le_sInf := fun s => by dsimp; rw [gi.choice_eq]; exact (gi.isGLB_of_u_image (isGLB_sInf _)).2 }

end lift

end GaloisInsertion

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/5171): this used to have a `@[nolint has_nonempty_instance]`
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

/-- Makes a Galois coinsertion from an order-preserving bijection. -/
protected def OrderIso.toGaloisCoinsertion [Preorder α] [Preorder β] (oi : α ≃o β) :
    GaloisCoinsertion oi oi.symm where
  choice b _ := oi.symm b
  gc := oi.to_galoisConnection
  u_l_le g := le_of_eq (oi.left_inv g)
  choice_eq _ _ := rfl

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

theorem u_inf_l [SemilatticeInf α] [SemilatticeInf β] (gi : GaloisCoinsertion l u) (a b : α) :
    u (l a ⊓ l b) = a ⊓ b :=
  gi.dual.l_sup_u a b

theorem u_iInf_l [CompleteLattice α] [CompleteLattice β] (gi : GaloisCoinsertion l u) {ι : Sort x}
    (f : ι → α) : u (⨅ i, l (f i)) = ⨅ i, f i :=
  gi.dual.l_iSup_u _

theorem u_sInf_l_image [CompleteLattice α] [CompleteLattice β] (gi : GaloisCoinsertion l u)
    (s : Set α) : u (sInf (l '' s)) = sInf s :=
  gi.dual.l_sSup_u_image _

theorem u_sup_l [SemilatticeSup α] [SemilatticeSup β] (gi : GaloisCoinsertion l u) (a b : α) :
    u (l a ⊔ l b) = a ⊔ b :=
  gi.dual.l_inf_u _ _

theorem u_iSup_l [CompleteLattice α] [CompleteLattice β] (gi : GaloisCoinsertion l u) {ι : Sort x}
    (f : ι → α) : u (⨆ i, l (f i)) = ⨆ i, f i :=
  gi.dual.l_iInf_u _

theorem u_biSup_l [CompleteLattice α] [CompleteLattice β] (gi : GaloisCoinsertion l u) {ι : Sort x}
    {p : ι → Prop} (f : ∀ (i) (_ : p i), α) : u (⨆ (i) (hi), l (f i hi)) = ⨆ (i) (hi), f i hi :=
  gi.dual.l_biInf_u _

theorem u_sSup_l_image [CompleteLattice α] [CompleteLattice β] (gi : GaloisCoinsertion l u)
    (s : Set α) : u (sSup (l '' s)) = sSup s :=
  gi.dual.l_sInf_u_image _

theorem u_iSup_of_lu_eq_self [CompleteLattice α] [CompleteLattice β] (gi : GaloisCoinsertion l u)
    {ι : Sort x} (f : ι → β) (hf : ∀ i, l (u (f i)) = f i) : u (⨆ i, f i) = ⨆ i, u (f i) :=
  gi.dual.l_iInf_of_ul_eq_self _ hf

theorem u_biSup_of_lu_eq_self [CompleteLattice α] [CompleteLattice β] (gi : GaloisCoinsertion l u)
    {ι : Sort x} {p : ι → Prop} (f : ∀ (i) (_ : p i), β) (hf : ∀ i hi, l (u (f i hi)) = f i hi) :
    u (⨆ (i) (hi), f i hi) = ⨆ (i) (hi), u (f i hi) :=
  gi.dual.l_biInf_of_ul_eq_self _ hf

theorem l_le_l_iff [Preorder α] [Preorder β] (gi : GaloisCoinsertion l u) {a b} :
    l a ≤ l b ↔ a ≤ b :=
  gi.dual.u_le_u_iff

theorem strictMono_l [Preorder α] [Preorder β] (gi : GaloisCoinsertion l u) : StrictMono l :=
  fun _ _ h => gi.dual.strictMono_u h

theorem isGLB_of_l_image [Preorder α] [Preorder β] (gi : GaloisCoinsertion l u) {s : Set α} {a : β}
    (hs : IsGLB (l '' s) a) : IsGLB s (u a) :=
  gi.dual.isLUB_of_u_image hs

theorem isLUB_of_l_image [Preorder α] [Preorder β] (gi : GaloisCoinsertion l u) {s : Set α} {a : β}
    (hs : IsLUB (l '' s) a) : IsLUB s (u a) :=
  gi.dual.isGLB_of_u_image hs

section lift

variable [PartialOrder α]

-- Porting note: In `liftSemilatticeInf` and `liftSemilatticeSup` below, the elaborator
-- seems to struggle with αᵒᵈ vs α; the `by exact`s are not present in Lean 3, but without
-- them the declarations compile much more slowly for some reason.
-- Possibly related to the issue discussed at
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Performance.20issue.20with.20.60CompleteBooleanAlgebra.60/near/316760798

-- See note [reducible non instances]
/-- Lift the infima along a Galois coinsertion -/
abbrev liftSemilatticeInf [SemilatticeInf β] (gi : GaloisCoinsertion l u) : SemilatticeInf α :=
  { ‹PartialOrder α› with
    inf_le_left := fun a b => by
      exact (@OrderDual.instSemilatticeInf αᵒᵈ gi.dual.liftSemilatticeSup).inf_le_left a b
    inf_le_right := fun a b => by
      exact (@OrderDual.instSemilatticeInf αᵒᵈ gi.dual.liftSemilatticeSup).inf_le_right a b
    le_inf := fun a b c => by
      exact (@OrderDual.instSemilatticeInf αᵒᵈ gi.dual.liftSemilatticeSup).le_inf a b c
    inf := fun a b => u (l a ⊓ l b) }

-- See note [reducible non instances]
/-- Lift the suprema along a Galois coinsertion -/
abbrev liftSemilatticeSup [SemilatticeSup β] (gi : GaloisCoinsertion l u) : SemilatticeSup α :=
  { ‹PartialOrder α› with
    sup := fun a b =>
      gi.choice (l a ⊔ l b) <|
        sup_le (gi.gc.monotone_l <| gi.gc.le_u <| le_sup_left)
          (gi.gc.monotone_l <| gi.gc.le_u <| le_sup_right)
    le_sup_left := fun a b => by
      exact (@OrderDual.instSemilatticeSup αᵒᵈ gi.dual.liftSemilatticeInf).le_sup_left a b
    le_sup_right := fun a b => by
      exact (@OrderDual.instSemilatticeSup αᵒᵈ gi.dual.liftSemilatticeInf).le_sup_right a b
    sup_le := fun a b c => by
      exact (@OrderDual.instSemilatticeSup αᵒᵈ gi.dual.liftSemilatticeInf).sup_le a b c }

-- See note [reducible non instances]
/-- Lift the suprema and infima along a Galois coinsertion -/
abbrev liftLattice [Lattice β] (gi : GaloisCoinsertion l u) : Lattice α :=
  { gi.liftSemilatticeSup, gi.liftSemilatticeInf with }

-- See note [reducible non instances]
/-- Lift the bot along a Galois coinsertion -/
abbrev liftOrderBot [Preorder β] [OrderBot β] (gi : GaloisCoinsertion l u) : OrderBot α :=
  { @OrderDual.instOrderBot _ _ gi.dual.liftOrderTop with bot := gi.choice ⊥ <| bot_le }

-- See note [reducible non instances]
/-- Lift the top, bottom, suprema, and infima along a Galois coinsertion -/
abbrev liftBoundedOrder
    [Preorder β] [BoundedOrder β] (gi : GaloisCoinsertion l u) : BoundedOrder α :=
  { gi.liftOrderBot, gi.gc.liftOrderTop with }

-- See note [reducible non instances]
/-- Lift all suprema and infima along a Galois coinsertion -/
abbrev liftCompleteLattice [CompleteLattice β] (gi : GaloisCoinsertion l u) : CompleteLattice α :=
  { @OrderDual.instCompleteLattice αᵒᵈ gi.dual.liftCompleteLattice with
    sInf := fun s => u (sInf (l '' s))
    sSup := fun s => gi.choice (sSup (l '' s)) _ }

end lift

end GaloisCoinsertion

/-- `sSup` and `Iic` form a Galois insertion. -/
def gi_sSup_Iic [CompleteSemilatticeSup α] :
    GaloisInsertion (sSup : Set α → α) (Iic : α → Set α) :=
  gc_sSup_Iic.toGaloisInsertion fun _ ↦ le_sSup le_rfl

/-- `toDual ∘ Ici` and `sInf ∘ ofDual` form a Galois coinsertion. -/
def gci_Ici_sInf [CompleteSemilatticeInf α] :
    GaloisCoinsertion (toDual ∘ Ici : α → (Set α)ᵒᵈ) (sInf ∘ ofDual : (Set α)ᵒᵈ → α) :=
  gc_Ici_sInf.toGaloisCoinsertion fun _ ↦ sInf_le le_rfl

/-- If `α` is a partial order with bottom element (e.g., `ℕ`, `ℝ≥0`), then `WithBot.unbot' ⊥` and
coercion form a Galois insertion. -/
def WithBot.giUnbot'Bot [Preorder α] [OrderBot α] :
    GaloisInsertion (WithBot.unbot' ⊥) (some : α → WithBot α) where
  gc _ _ := WithBot.unbot'_le_iff (fun _ ↦ bot_le)
  le_l_u _ := le_rfl
  choice o _ := o.unbot' ⊥
  choice_eq _ _ := rfl
