/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.UpperLower.Basic
import Mathlib.Topology.Sets.Closeds

#align_import topology.sets.order from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Clopen upper sets

In this file we define the type of clopen upper sets.
-/


open Set TopologicalSpace

variable {α β : Type*} [TopologicalSpace α] [LE α] [TopologicalSpace β] [LE β]

/-! ### Compact open sets -/


/-- The type of clopen upper sets of a topological space. -/
structure ClopenUpperSet (α : Type*) [TopologicalSpace α] [LE α] extends Clopens α where
  upper' : IsUpperSet carrier
#align clopen_upper_set ClopenUpperSet

namespace ClopenUpperSet

instance : SetLike (ClopenUpperSet α) α where
  coe s := s.carrier
  coe_injective' s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    -- ⊢ { toClopens := { carrier := carrier✝, clopen' := clopen'✝ }, upper' := upper …
    obtain ⟨⟨_, _⟩, _⟩ := t
    -- ⊢ { toClopens := { carrier := carrier✝¹, clopen' := clopen'✝¹ }, upper' := upp …
    congr
    -- 🎉 no goals

/-- See Note [custom simps projection]. -/
def Simps.coe (s : ClopenUpperSet α) : Set α := s

initialize_simps_projections ClopenUpperSet (carrier → coe)

theorem upper (s : ClopenUpperSet α) : IsUpperSet (s : Set α) :=
  s.upper'
#align clopen_upper_set.upper ClopenUpperSet.upper

theorem clopen (s : ClopenUpperSet α) : IsClopen (s : Set α) :=
  s.clopen'
#align clopen_upper_set.clopen ClopenUpperSet.clopen

/-- Reinterpret an upper clopen as an upper set. -/
@[simps]
def toUpperSet (s : ClopenUpperSet α) : UpperSet α :=
  ⟨s, s.upper⟩
#align clopen_upper_set.to_upper_set ClopenUpperSet.toUpperSet

@[ext]
protected theorem ext {s t : ClopenUpperSet α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align clopen_upper_set.ext ClopenUpperSet.ext

@[simp]
theorem coe_mk (s : Clopens α) (h) : (mk s h : Set α) = s :=
  rfl
#align clopen_upper_set.coe_mk ClopenUpperSet.coe_mk

instance : Sup (ClopenUpperSet α) :=
  ⟨fun s t => ⟨s.toClopens ⊔ t.toClopens, s.upper.union t.upper⟩⟩

instance : Inf (ClopenUpperSet α) :=
  ⟨fun s t => ⟨s.toClopens ⊓ t.toClopens, s.upper.inter t.upper⟩⟩

instance : Top (ClopenUpperSet α) :=
  ⟨⟨⊤, isUpperSet_univ⟩⟩

instance : Bot (ClopenUpperSet α) :=
  ⟨⟨⊥, isUpperSet_empty⟩⟩

instance : Lattice (ClopenUpperSet α) :=
  SetLike.coe_injective.lattice _ (fun _ _ => rfl) fun _ _ => rfl

instance : BoundedOrder (ClopenUpperSet α) :=
  BoundedOrder.lift ((↑) : _ → Set α) (fun _ _ => id) rfl rfl

@[simp]
theorem coe_sup (s t : ClopenUpperSet α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t :=
  rfl
#align clopen_upper_set.coe_sup ClopenUpperSet.coe_sup

@[simp]
theorem coe_inf (s t : ClopenUpperSet α) : (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t :=
  rfl
#align clopen_upper_set.coe_inf ClopenUpperSet.coe_inf

@[simp]
theorem coe_top : (↑(⊤ : ClopenUpperSet α) : Set α) = univ :=
  rfl
#align clopen_upper_set.coe_top ClopenUpperSet.coe_top

@[simp]
theorem coe_bot : (↑(⊥ : ClopenUpperSet α) : Set α) = ∅ :=
  rfl
#align clopen_upper_set.coe_bot ClopenUpperSet.coe_bot

instance : Inhabited (ClopenUpperSet α) :=
  ⟨⊥⟩

end ClopenUpperSet
