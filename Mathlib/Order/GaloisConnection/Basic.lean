/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Order.Bounds.Image
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.GaloisConnection.Defs

/-!
# Galois connections, insertions and coinsertions

This file contains basic results on Galois connections, insertions and coinsertions in various
order structures, and provides constructions that lift order structures from one type to another.

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

namespace GaloisConnection

section

variable [Preorder α] [Preorder β] {l : α → β} {u : β → α}

variable (gc : GaloisConnection l u)
include gc

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

end

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

-- Constructing Galois connections
section Constructions

protected theorem compl [BooleanAlgebra α] [BooleanAlgebra β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) :
    GaloisConnection (compl ∘ u ∘ compl) (compl ∘ l ∘ compl) := fun a b ↦ by
  dsimp
  rw [le_compl_iff_le_compl, gc, compl_le_iff_compl_le]

end Constructions

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

/-- Makes a Galois connection from an order-preserving bijection. -/
lemma to_galoisConnection (e : α ≃o β) : GaloisConnection e e.symm :=
  fun _ _ => e.rel_symm_apply.symm

/-- Makes a Galois insertion from an order-preserving bijection. -/
protected def toGaloisInsertion (e : α ≃o β) : GaloisInsertion e e.symm where
  choice b _ := e b
  gc := e.to_galoisConnection
  le_l_u g := le_of_eq (e.right_inv g).symm
  choice_eq _ _ := rfl

/-- Makes a Galois coinsertion from an order-preserving bijection. -/
protected def toGaloisCoinsertion (e : α ≃o β) : GaloisCoinsertion e e.symm where
  choice b _ := e.symm b
  gc := e.to_galoisConnection
  u_l_le g := le_of_eq (e.left_inv g)
  choice_eq _ _ := rfl

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

namespace GaloisInsertion

variable {l : α → β} {u : β → α}

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

namespace GaloisCoinsertion

variable {l : α → β} {u : β → α}

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
def WithBot.giUnbotDBot [Preorder α] [OrderBot α] :
    GaloisInsertion (WithBot.unbotD ⊥) (some : α → WithBot α) where
  gc _ _ := WithBot.unbotD_le_iff (fun _ ↦ bot_le)
  le_l_u _ := le_rfl
  choice o _ := o.unbotD ⊥
  choice_eq _ _ := rfl

@[deprecated (since := "2025-02-06")]
alias WithBot.giUnbot'Bot := WithBot.giUnbotDBot
