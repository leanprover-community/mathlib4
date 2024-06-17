/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Shing Tak Lam
-/
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.ProjIcc

#align_import topology.continuous_function.ordered from "leanprover-community/mathlib"@"84dc0bd6619acaea625086d6f53cb35cdd554219"

/-!
# Bundled continuous maps into orders, with order-compatible topology

-/


variable {α : Type*} {β : Type*} {γ : Type*}
variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace ContinuousMap

/-!
We now set up the partial order and lattice structure (given by pointwise min and max)
on continuous functions.
-/

instance partialOrder [PartialOrder β] : PartialOrder C(α, β) :=
  PartialOrder.lift (fun f => f.toFun) (fun f g _ => by cases f; cases g; congr)
  -- Porting note: was `by tidy`, and `by aesop` alone didn't work
#align continuous_map.partial_order ContinuousMap.partialOrder

theorem le_def [PartialOrder β] {f g : C(α, β)} : f ≤ g ↔ ∀ a, f a ≤ g a :=
  Pi.le_def
#align continuous_map.le_def ContinuousMap.le_def

theorem lt_def [PartialOrder β] {f g : C(α, β)} : f < g ↔ (∀ a, f a ≤ g a) ∧ ∃ a, f a < g a :=
  Pi.lt_def
#align continuous_map.lt_def ContinuousMap.lt_def

section SemilatticeSup
variable [SemilatticeSup β] [ContinuousSup β]

instance sup : Sup C(α, β) where sup f g := { toFun := fun a ↦ f a ⊔ g a }
#align continuous_map.has_sup ContinuousMap.sup

@[simp, norm_cast] lemma coe_sup (f g : C(α, β)) : ⇑(f ⊔ g) = ⇑f ⊔ g := rfl
#align continuous_map.sup_coe ContinuousMap.coe_sup

@[simp] lemma sup_apply (f g : C(α, β)) (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl
#align continuous_map.sup_apply ContinuousMap.sup_apply

instance semilatticeSup : SemilatticeSup C(α, β) :=
  DFunLike.coe_injective.semilatticeSup _ fun _ _ ↦ rfl

lemma sup'_apply {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C(α, β)) (a : α) :
    s.sup' H f a = s.sup' H fun i ↦ f i a :=
  Finset.comp_sup'_eq_sup'_comp H (fun g : C(α, β) ↦ g a) fun _ _ ↦ rfl
#align continuous_map.sup'_apply ContinuousMap.sup'_apply

@[simp, norm_cast]
lemma coe_sup' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C(α, β)) :
    ⇑(s.sup' H f) = s.sup' H fun i ↦ ⇑(f i) := by ext; simp [sup'_apply]
#align continuous_map.sup'_coe ContinuousMap.coe_sup'

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf β] [ContinuousInf β]

instance inf : Inf C(α, β) where inf f g := { toFun := fun a ↦ f a ⊓ g a }
#align continuous_map.has_inf ContinuousMap.inf

@[simp, norm_cast] lemma coe_inf (f g : C(α, β)) : ⇑(f ⊓ g) = ⇑f ⊓ g := rfl
#align continuous_map.inf_coe ContinuousMap.coe_inf

@[simp] lemma inf_apply (f g : C(α, β)) (a : α) : (f ⊓ g) a = f a ⊓ g a := rfl
#align continuous_map.inf_apply ContinuousMap.inf_apply

instance semilatticeInf : SemilatticeInf C(α, β) :=
  DFunLike.coe_injective.semilatticeInf _ fun _ _ ↦ rfl

lemma inf'_apply {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C(α, β)) (a : α) :
    s.inf' H f a = s.inf' H fun i ↦ f i a :=
  Finset.comp_inf'_eq_inf'_comp H (fun g : C(α, β) ↦ g a) fun _ _ ↦ rfl
#align continuous_map.inf'_apply ContinuousMap.inf'_apply

@[simp, norm_cast]
lemma coe_inf' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C(α, β)) :
    ⇑(s.inf' H f) = s.inf' H fun i ↦ ⇑(f i) := by ext; simp [inf'_apply]
#align continuous_map.inf'_coe ContinuousMap.coe_inf'

end SemilatticeInf

instance [Lattice β] [TopologicalLattice β] : Lattice C(α, β) :=
  DFunLike.coe_injective.lattice _ (fun _ _ ↦ rfl) fun _ _ ↦ rfl

-- TODO transfer this lattice structure to `BoundedContinuousFunction`

section Extend

variable [LinearOrder α] [OrderTopology α] {a b : α} (h : a ≤ b)

/-- Extend a continuous function `f : C(Set.Icc a b, β)` to a function `f : C(α, β)`.  -/
def IccExtend (f : C(Set.Icc a b, β)) : C(α, β) where
  toFun := Set.IccExtend h f
#align continuous_map.Icc_extend ContinuousMap.IccExtend

@[simp]
theorem coe_IccExtend (f : C(Set.Icc a b, β)) :
    ((IccExtend h f : C(α, β)) : α → β) = Set.IccExtend h f :=
  rfl
#align continuous_map.coe_Icc_extend ContinuousMap.coe_IccExtend

end Extend

end ContinuousMap
