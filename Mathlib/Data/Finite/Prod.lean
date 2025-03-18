/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic.ApplyFun
import Mathlib.Data.ULift
import Mathlib.Data.Set.NAry

/-!
# Finiteness of products
-/

assert_not_exists OrderedRing MonoidWithZero

variable {α β : Type*}

namespace Finite

instance [Finite α] [Finite β] : Finite (α × β) := by
  haveI := Fintype.ofFinite α
  haveI := Fintype.ofFinite β
  infer_instance

instance {α β : Sort*} [Finite α] [Finite β] : Finite (PProd α β) :=
  of_equiv _ Equiv.pprodEquivProdPLift.symm

theorem prod_left (β) [Finite (α × β)] [Nonempty β] : Finite α :=
  of_surjective (Prod.fst : α × β → α) Prod.fst_surjective

theorem prod_right (α) [Finite (α × β)] [Nonempty α] : Finite β :=
  of_surjective (Prod.snd : α × β → β) Prod.snd_surjective

end Finite

instance Pi.finite {α : Sort*} {β : α → Sort*} [Finite α] [∀ a, Finite (β a)] :
    Finite (∀ a, β a) := by
  classical
  haveI := Fintype.ofFinite (PLift α)
  haveI := fun a => Fintype.ofFinite (PLift (β a))
  exact
    Finite.of_equiv (∀ a : PLift α, PLift (β (Equiv.plift a)))
      (Equiv.piCongr Equiv.plift fun _ => Equiv.plift)

instance Function.Embedding.finite {α β : Sort*} [Finite β] : Finite (α ↪ β) := by
  rcases isEmpty_or_nonempty (α ↪ β) with _ | h
  · infer_instance
  · refine h.elim fun f => ?_
    haveI : Finite α := Finite.of_injective _ f.injective
    exact Finite.of_injective _ DFunLike.coe_injective

instance Equiv.finite_right {α β : Sort*} [Finite β] : Finite (α ≃ β) :=
  Finite.of_injective Equiv.toEmbedding fun e₁ e₂ h => Equiv.ext <| by
    convert DFunLike.congr_fun h using 0

instance Equiv.finite_left {α β : Sort*} [Finite α] : Finite (α ≃ β) :=
  Finite.of_equiv _ ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩

@[to_additive]
instance MulEquiv.finite_left {α β : Type*} [Mul α] [Mul β] [Finite α] : Finite (α ≃* β) :=
  Finite.of_injective toEquiv toEquiv_injective

@[to_additive]
instance MulEquiv.finite_right {α β : Type*} [Mul α] [Mul β] [Finite β] : Finite (α ≃* β) :=
  Finite.of_injective toEquiv toEquiv_injective

open Set Function

variable {γ : Type*}

namespace Set

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

instance fintypeProd (s : Set α) (t : Set β) [Fintype s] [Fintype t] :
    Fintype (s ×ˢ t : Set (α × β)) :=
  Fintype.ofFinset (s.toFinset ×ˢ t.toFinset) <| by simp

instance fintypeOffDiag [DecidableEq α] (s : Set α) [Fintype s] : Fintype s.offDiag :=
  Fintype.ofFinset s.toFinset.offDiag <| by simp

/-- `image2 f s t` is `Fintype` if `s` and `t` are. -/
instance fintypeImage2 [DecidableEq γ] (f : α → β → γ) (s : Set α) (t : Set β) [hs : Fintype s]
    [ht : Fintype t] : Fintype (image2 f s t : Set γ) := by
  rw [← image_prod]
  apply Set.fintypeImage

end FintypeInstances

end Set

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `Fintype` instances
in `Data.Set.Finite`. While every `Fintype` instance gives a `Finite` instance, those
instances that depend on `Fintype` or `Decidable` instances need an additional `Finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`Subtype.Finite` for subsets of a finite type.
-/


namespace Finite.Set

instance finite_prod (s : Set α) (t : Set β) [Finite s] [Finite t] :
    Finite (s ×ˢ t : Set (α × β)) :=
  Finite.of_equiv _ (Equiv.Set.prod s t).symm

instance finite_image2 (f : α → β → γ) (s : Set α) (t : Set β) [Finite s] [Finite t] :
    Finite (image2 f s t : Set γ) := by
  rw [← image_prod]
  infer_instance

end Finite.Set

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors

section Prod

variable {s : Set α} {t : Set β}

protected theorem Finite.prod (hs : s.Finite) (ht : t.Finite) : (s ×ˢ t : Set (α × β)).Finite := by
  have := hs.to_subtype
  have := ht.to_subtype
  apply toFinite

theorem Finite.of_prod_left (h : (s ×ˢ t : Set (α × β)).Finite) : t.Nonempty → s.Finite :=
  fun ⟨b, hb⟩ => (h.image Prod.fst).subset fun a ha => ⟨(a, b), ⟨ha, hb⟩, rfl⟩

theorem Finite.of_prod_right (h : (s ×ˢ t : Set (α × β)).Finite) : s.Nonempty → t.Finite :=
  fun ⟨a, ha⟩ => (h.image Prod.snd).subset fun b hb => ⟨(a, b), ⟨ha, hb⟩, rfl⟩

protected theorem Infinite.prod_left (hs : s.Infinite) (ht : t.Nonempty) : (s ×ˢ t).Infinite :=
  fun h => hs <| h.of_prod_left ht

protected theorem Infinite.prod_right (ht : t.Infinite) (hs : s.Nonempty) : (s ×ˢ t).Infinite :=
  fun h => ht <| h.of_prod_right hs

protected theorem infinite_prod :
    (s ×ˢ t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty := by
  refine ⟨fun h => ?_, ?_⟩
  · simp_rw [Set.Infinite, @and_comm ¬_, ← Classical.not_imp]
    by_contra!
    exact h ((this.1 h.nonempty.snd).prod <| this.2 h.nonempty.fst)
  · rintro (h | h)
    · exact h.1.prod_left h.2
    · exact h.1.prod_right h.2

theorem finite_prod : (s ×ˢ t).Finite ↔ (s.Finite ∨ t = ∅) ∧ (t.Finite ∨ s = ∅) := by
  simp only [← not_infinite, Set.infinite_prod, not_or, not_and_or, not_nonempty_iff_eq_empty]

protected theorem Finite.offDiag {s : Set α} (hs : s.Finite) : s.offDiag.Finite :=
  (hs.prod hs).subset s.offDiag_subset_prod

protected theorem Finite.image2 (f : α → β → γ) (hs : s.Finite) (ht : t.Finite) :
    (image2 f s t).Finite := by
  have := hs.to_subtype
  have := ht.to_subtype
  apply toFinite

end Prod

end SetFiniteConstructors

/-! ### Properties -/

theorem Finite.toFinset_prod {s : Set α} {t : Set β} (hs : s.Finite) (ht : t.Finite) :
    hs.toFinset ×ˢ ht.toFinset = (hs.prod ht).toFinset :=
  Finset.ext <| by simp

theorem Finite.toFinset_offDiag {s : Set α} [DecidableEq α] (hs : s.Finite) :
    hs.offDiag.toFinset = hs.toFinset.offDiag :=
  Finset.ext <| by simp

theorem finite_image_fst_and_snd_iff {s : Set (α × β)} :
    (Prod.fst '' s).Finite ∧ (Prod.snd '' s).Finite ↔ s.Finite :=
  ⟨fun h => (h.1.prod h.2).subset fun _ h => ⟨mem_image_of_mem _ h, mem_image_of_mem _ h⟩,
    fun h => ⟨h.image _, h.image _⟩⟩

/-! ### Infinite sets -/

variable {s t : Set α}

section Image2

variable {f : α → β → γ} {s : Set α} {t : Set β} {a : α} {b : β}

protected theorem Infinite.image2_left (hs : s.Infinite) (hb : b ∈ t)
    (hf : InjOn (fun a => f a b) s) : (image2 f s t).Infinite :=
  (hs.image hf).mono <| image_subset_image2_left hb

protected theorem Infinite.image2_right (ht : t.Infinite) (ha : a ∈ s) (hf : InjOn (f a) t) :
    (image2 f s t).Infinite :=
  (ht.image hf).mono <| image_subset_image2_right ha

theorem infinite_image2 (hfs : ∀ b ∈ t, InjOn (fun a => f a b) s) (hft : ∀ a ∈ s, InjOn (f a) t) :
    (image2 f s t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty := by
  refine ⟨fun h => Set.infinite_prod.1 ?_, ?_⟩
  · rw [← image_uncurry_prod] at h
    exact h.of_image _
  · rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩)
    · exact hs.image2_left hb (hfs _ hb)
    · exact ht.image2_right ha (hft _ ha)

lemma finite_image2 (hfs : ∀ b ∈ t, InjOn (f · b) s) (hft : ∀ a ∈ s, InjOn (f a) t) :
    (image2 f s t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ := by
  rw [← not_infinite, infinite_image2 hfs hft]
  simp [not_or, -not_and, not_and_or, not_nonempty_iff_eq_empty]
  aesop

end Image2

end Set
