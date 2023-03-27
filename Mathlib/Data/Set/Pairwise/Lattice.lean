/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module data.set.pairwise.lattice
! leanprover-community/mathlib commit c227d107bbada5d0d9d20287e3282c0a7f1651a0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Lattice
import Mathbin.Data.Set.Pairwise.Basic

/-!
# Relations holding pairwise

In this file we prove many facts about `pairwise` and the set lattice.
-/


open Set Function

variable {α β γ ι ι' : Type _} {r p q : α → α → Prop}

section Pairwise

variable {f g : ι → α} {s t u : Set α} {a b : α}

namespace Set

/- warning: set.pairwise_Union -> Set.pairwise_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {r : α -> α -> Prop} {f : ι -> (Set.{u1} α)}, (Directed.{u1, succ u2} (Set.{u1} α) ι (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α)) f) -> (Iff (Set.Pairwise.{u1} α (Set.unionᵢ.{u1, succ u2} α ι (fun (n : ι) => f n)) r) (forall (n : ι), Set.Pairwise.{u1} α (f n) r))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {r : α -> α -> Prop} {f : ι -> (Set.{u2} α)}, (Directed.{u2, succ u1} (Set.{u2} α) ι (fun (x._@.Mathlib.Data.Set.Pairwise._hyg.2714 : Set.{u2} α) (x._@.Mathlib.Data.Set.Pairwise._hyg.2716 : Set.{u2} α) => HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) x._@.Mathlib.Data.Set.Pairwise._hyg.2714 x._@.Mathlib.Data.Set.Pairwise._hyg.2716) f) -> (Iff (Set.Pairwise.{u2} α (Set.unionᵢ.{u2, succ u1} α ι (fun (n : ι) => f n)) r) (forall (n : ι), Set.Pairwise.{u2} α (f n) r))
Case conversion may be inaccurate. Consider using '#align set.pairwise_Union Set.pairwise_unionᵢₓ'. -/
theorem pairwise_unionᵢ {f : ι → Set α} (h : Directed (· ⊆ ·) f) :
    (⋃ n, f n).Pairwise r ↔ ∀ n, (f n).Pairwise r :=
  by
  constructor
  · intro H n
    exact Pairwise.mono (subset_Union _ _) H
  · intro H i hi j hj hij
    rcases mem_Union.1 hi with ⟨m, hm⟩
    rcases mem_Union.1 hj with ⟨n, hn⟩
    rcases h m n with ⟨p, mp, np⟩
    exact H p (mp hm) (np hn) hij
#align set.pairwise_Union Set.pairwise_unionᵢ

#print Set.pairwise_unionₛ /-
theorem pairwise_unionₛ {r : α → α → Prop} {s : Set (Set α)} (h : DirectedOn (· ⊆ ·) s) :
    (⋃₀ s).Pairwise r ↔ ∀ a ∈ s, Set.Pairwise a r :=
  by
  rw [sUnion_eq_Union, pairwise_Union h.directed_coe, SetCoe.forall]
  rfl
#align set.pairwise_sUnion Set.pairwise_unionₛ
-/

end Set

end Pairwise

namespace Set

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {s t : Set ι} {f g : ι → α}

/- warning: set.pairwise_disjoint_Union -> Set.pairwiseDisjoint_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {f : ι -> α} {g : ι' -> (Set.{u2} ι)}, (Directed.{u2, succ u3} (Set.{u2} ι) ι' (HasSubset.Subset.{u2} (Set.{u2} ι) (Set.hasSubset.{u2} ι)) g) -> (Iff (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 (Set.unionᵢ.{u2, succ u3} ι ι' (fun (n : ι') => g n)) f) (forall {{n : ι'}}, Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 (g n) f))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u3}} {ι' : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {f : ι -> α} {g : ι' -> (Set.{u3} ι)}, (Directed.{u3, succ u2} (Set.{u3} ι) ι' (fun (x._@.Mathlib.Data.Set.Pairwise._hyg.4274 : Set.{u3} ι) (x._@.Mathlib.Data.Set.Pairwise._hyg.4276 : Set.{u3} ι) => HasSubset.Subset.{u3} (Set.{u3} ι) (Set.instHasSubsetSet.{u3} ι) x._@.Mathlib.Data.Set.Pairwise._hyg.4274 x._@.Mathlib.Data.Set.Pairwise._hyg.4276) g) -> (Iff (Set.PairwiseDisjoint.{u1, u3} α ι _inst_1 _inst_2 (Set.unionᵢ.{u3, succ u2} ι ι' (fun (n : ι') => g n)) f) (forall {{n : ι'}}, Set.PairwiseDisjoint.{u1, u3} α ι _inst_1 _inst_2 (g n) f))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint_Union Set.pairwiseDisjoint_unionᵢₓ'. -/
theorem pairwiseDisjoint_unionᵢ {g : ι' → Set ι} (h : Directed (· ⊆ ·) g) :
    (⋃ n, g n).PairwiseDisjoint f ↔ ∀ ⦃n⦄, (g n).PairwiseDisjoint f :=
  pairwise_unionᵢ h
#align set.pairwise_disjoint_Union Set.pairwiseDisjoint_unionᵢ

#print Set.pairwiseDisjoint_unionₛ /-
theorem pairwiseDisjoint_unionₛ {s : Set (Set ι)} (h : DirectedOn (· ⊆ ·) s) :
    (⋃₀ s).PairwiseDisjoint f ↔ ∀ ⦃a⦄, a ∈ s → Set.PairwiseDisjoint a f :=
  pairwise_unionₛ h
#align set.pairwise_disjoint_sUnion Set.pairwiseDisjoint_unionₛ
-/

end PartialOrderBot

section CompleteLattice

variable [CompleteLattice α]

/- warning: set.pairwise_disjoint.bUnion -> Set.PairwiseDisjoint.bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u3} ι'} {g : ι' -> (Set.{u2} ι)} {f : ι -> α}, (Set.PairwiseDisjoint.{u1, u3} α ι' (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) s (fun (i' : ι') => supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i (g i')) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i (g i')) => f i)))) -> (forall (i : ι'), (Membership.Mem.{u3, u3} ι' (Set.{u3} ι') (Set.hasMem.{u3} ι') i s) -> (Set.PairwiseDisjoint.{u1, u2} α ι (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (g i) f)) -> (Set.PairwiseDisjoint.{u1, u2} α ι (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (Set.unionᵢ.{u2, succ u3} ι ι' (fun (i : ι') => Set.unionᵢ.{u2, 0} ι (Membership.Mem.{u3, u3} ι' (Set.{u3} ι') (Set.hasMem.{u3} ι') i s) (fun (H : Membership.Mem.{u3, u3} ι' (Set.{u3} ι') (Set.hasMem.{u3} ι') i s) => g i))) f)
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u3} ι'} {g : ι' -> (Set.{u2} ι)} {f : ι -> α}, (Set.PairwiseDisjoint.{u1, u3} α ι' (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) s (fun (i' : ι') => supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i (g i')) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i (g i')) => f i)))) -> (forall (i : ι'), (Membership.mem.{u3, u3} ι' (Set.{u3} ι') (Set.instMembershipSet.{u3} ι') i s) -> (Set.PairwiseDisjoint.{u1, u2} α ι (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (g i) f)) -> (Set.PairwiseDisjoint.{u1, u2} α ι (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (Set.unionᵢ.{u2, succ u3} ι ι' (fun (i : ι') => Set.unionᵢ.{u2, 0} ι (Membership.mem.{u3, u3} ι' (Set.{u3} ι') (Set.instMembershipSet.{u3} ι') i s) (fun (H : Membership.mem.{u3, u3} ι' (Set.{u3} ι') (Set.instMembershipSet.{u3} ι') i s) => g i))) f)
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.bUnion Set.PairwiseDisjoint.bunionᵢₓ'. -/
/-- Bind operation for `set.pairwise_disjoint`. If you want to only consider finsets of indices, you
can use `set.pairwise_disjoint.bUnion_finset`. -/
theorem PairwiseDisjoint.bunionᵢ {s : Set ι'} {g : ι' → Set ι} {f : ι → α}
    (hs : s.PairwiseDisjoint fun i' : ι' => ⨆ i ∈ g i', f i)
    (hg : ∀ i ∈ s, (g i).PairwiseDisjoint f) : (⋃ i ∈ s, g i).PairwiseDisjoint f :=
  by
  rintro a ha b hb hab
  simp_rw [Set.mem_unionᵢ] at ha hb
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨d, hd, hb⟩ := hb
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  · exact hg d hd (hcd.subst ha) hb hab
  · exact (hs hc hd <| ne_of_apply_ne _ hcd).mono (le_supᵢ₂ a ha) (le_supᵢ₂ b hb)
#align set.pairwise_disjoint.bUnion Set.PairwiseDisjoint.bunionᵢ

end CompleteLattice

/- warning: set.bUnion_diff_bUnion_eq -> Set.bunionᵢ_diff_bunionᵢ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι} {t : Set.{u2} ι} {f : ι -> (Set.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Union.union.{u2} (Set.{u2} ι) (Set.hasUnion.{u2} ι) s t) f) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => f i))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) => f i)))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i (SDiff.sdiff.{u2} (Set.{u2} ι) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} ι) (Set.booleanAlgebra.{u2} ι)) s t)) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i (SDiff.sdiff.{u2} (Set.{u2} ι) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} ι) (Set.booleanAlgebra.{u2} ι)) s t)) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι} {t : Set.{u2} ι} {f : ι -> (Set.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Union.union.{u2} (Set.{u2} ι) (Set.instUnionSet.{u2} ι) s t) f) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i t) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i t) => f i)))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i (SDiff.sdiff.{u2} (Set.{u2} ι) (Set.instSDiffSet.{u2} ι) s t)) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i (SDiff.sdiff.{u2} (Set.{u2} ι) (Set.instSDiffSet.{u2} ι) s t)) => f i))))
Case conversion may be inaccurate. Consider using '#align set.bUnion_diff_bUnion_eq Set.bunionᵢ_diff_bunionᵢ_eqₓ'. -/
theorem bunionᵢ_diff_bunionᵢ_eq {s t : Set ι} {f : ι → Set α} (h : (s ∪ t).PairwiseDisjoint f) :
    ((⋃ i ∈ s, f i) \ ⋃ i ∈ t, f i) = ⋃ i ∈ s \ t, f i :=
  by
  refine'
    (bUnion_diff_bUnion_subset f s t).antisymm
      (Union₂_subset fun i hi a ha => (mem_diff _).2 ⟨mem_bUnion hi.1 ha, _⟩)
  rw [mem_Union₂]; rintro ⟨j, hj, haj⟩
  exact (h (Or.inl hi.1) (Or.inr hj) (ne_of_mem_of_not_mem hj hi.2).symm).le_bot ⟨ha, haj⟩
#align set.bUnion_diff_bUnion_eq Set.bunionᵢ_diff_bunionᵢ_eq

/- warning: set.bUnion_eq_sigma_of_disjoint -> Set.bunionᵢEqSigmaOfDisjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> (Set.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s f) -> (Equiv.{succ u1, max (succ u2) (succ u1)} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => f i)))) (Sigma.{u2, u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x s))))) i)))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> (Set.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s f) -> (Equiv.{succ u1, max (succ u1) (succ u2)} (Set.Elem.{u1} α (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i)))) (Sigma.{u2, u1} (Set.Elem.{u2} ι s) (fun (i : Set.Elem.{u2} ι s) => Set.Elem.{u1} α (f (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) x s) i)))))
Case conversion may be inaccurate. Consider using '#align set.bUnion_eq_sigma_of_disjoint Set.bunionᵢEqSigmaOfDisjointₓ'. -/
/-- Equivalence between a disjoint bounded union and a dependent sum. -/
noncomputable def bunionᵢEqSigmaOfDisjoint {s : Set ι} {f : ι → Set α} (h : s.PairwiseDisjoint f) :
    (⋃ i ∈ s, f i) ≃ Σi : s, f i :=
  (Equiv.setCongr (bunionᵢ_eq_unionᵢ _ _)).trans <|
    unionEqSigmaOfDisjoint fun ⟨i, hi⟩ ⟨j, hj⟩ ne => h hi hj fun eq => Ne <| Subtype.eq Eq
#align set.bUnion_eq_sigma_of_disjoint Set.bunionᵢEqSigmaOfDisjoint

end Set

section

variable {f : ι → Set α} {s t : Set ι}

/- warning: set.pairwise_disjoint.subset_of_bUnion_subset_bUnion -> Set.PairwiseDisjoint.subset_of_bunionᵢ_subset_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : ι -> (Set.{u1} α)} {s : Set.{u2} ι} {t : Set.{u2} ι}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Union.union.{u2} (Set.{u2} ι) (Set.hasUnion.{u2} ι) s t) f) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (Set.Nonempty.{u1} α (f i))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => f i))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) => f i)))) -> (HasSubset.Subset.{u2} (Set.{u2} ι) (Set.hasSubset.{u2} ι) s t)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {f : ι -> (Set.{u2} α)} {s : Set.{u1} ι} {t : Set.{u1} ι}, (Set.PairwiseDisjoint.{u2, u1} (Set.{u2} α) ι (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (Union.union.{u1} (Set.{u1} ι) (Set.instUnionSet.{u1} ι) s t) f) -> (forall (i : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) -> (Set.Nonempty.{u2} α (f i))) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) => f i))) (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i t) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i t) => f i)))) -> (HasSubset.Subset.{u1} (Set.{u1} ι) (Set.instHasSubsetSet.{u1} ι) s t)
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.subset_of_bUnion_subset_bUnion Set.PairwiseDisjoint.subset_of_bunionᵢ_subset_bunionᵢₓ'. -/
theorem Set.PairwiseDisjoint.subset_of_bunionᵢ_subset_bunionᵢ (h₀ : (s ∪ t).PairwiseDisjoint f)
    (h₁ : ∀ i ∈ s, (f i).Nonempty) (h : (⋃ i ∈ s, f i) ⊆ ⋃ i ∈ t, f i) : s ⊆ t :=
  by
  rintro i hi
  obtain ⟨a, hai⟩ := h₁ i hi
  obtain ⟨j, hj, haj⟩ := mem_Union₂.1 (h <| mem_Union₂_of_mem hi hai)
  rwa [h₀.eq (subset_union_left _ _ hi) (subset_union_right _ _ hj)
      (not_disjoint_iff.2 ⟨a, hai, haj⟩)]
#align set.pairwise_disjoint.subset_of_bUnion_subset_bUnion Set.PairwiseDisjoint.subset_of_bunionᵢ_subset_bunionᵢ

/- warning: pairwise.subset_of_bUnion_subset_bUnion -> Pairwise.subset_of_bunionᵢ_subset_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : ι -> (Set.{u1} α)} {s : Set.{u2} ι} {t : Set.{u2} ι}, (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) f)) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (Set.Nonempty.{u1} α (f i))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => f i))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) => f i)))) -> (HasSubset.Subset.{u2} (Set.{u2} ι) (Set.hasSubset.{u2} ι) s t)
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : ι -> (Set.{u1} α)} {s : Set.{u2} ι} {t : Set.{u2} ι}, (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) f)) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (Set.Nonempty.{u1} α (f i))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i t) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i t) => f i)))) -> (HasSubset.Subset.{u2} (Set.{u2} ι) (Set.instHasSubsetSet.{u2} ι) s t)
Case conversion may be inaccurate. Consider using '#align pairwise.subset_of_bUnion_subset_bUnion Pairwise.subset_of_bunionᵢ_subset_bunionᵢₓ'. -/
theorem Pairwise.subset_of_bunionᵢ_subset_bunionᵢ (h₀ : Pairwise (Disjoint on f))
    (h₁ : ∀ i ∈ s, (f i).Nonempty) (h : (⋃ i ∈ s, f i) ⊆ ⋃ i ∈ t, f i) : s ⊆ t :=
  Set.PairwiseDisjoint.subset_of_bunionᵢ_subset_bunionᵢ (h₀.set_pairwise _) h₁ h
#align pairwise.subset_of_bUnion_subset_bUnion Pairwise.subset_of_bunionᵢ_subset_bunionᵢ

/- warning: pairwise.bUnion_injective -> Pairwise.bunionᵢ_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : ι -> (Set.{u1} α)}, (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) f)) -> (forall (i : ι), Set.Nonempty.{u1} α (f i)) -> (Function.Injective.{succ u2, succ u1} (Set.{u2} ι) (Set.{u1} α) (fun (s : Set.{u2} ι) => Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : ι -> (Set.{u1} α)}, (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) f)) -> (forall (i : ι), Set.Nonempty.{u1} α (f i)) -> (Function.Injective.{succ u2, succ u1} (Set.{u2} ι) (Set.{u1} α) (fun (s : Set.{u2} ι) => Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i))))
Case conversion may be inaccurate. Consider using '#align pairwise.bUnion_injective Pairwise.bunionᵢ_injectiveₓ'. -/
theorem Pairwise.bunionᵢ_injective (h₀ : Pairwise (Disjoint on f)) (h₁ : ∀ i, (f i).Nonempty) :
    Injective fun s : Set ι => ⋃ i ∈ s, f i := fun s t h =>
  ((h₀.subset_of_bunionᵢ_subset_bunionᵢ fun _ _ => h₁ _) <| h.Subset).antisymm <|
    (h₀.subset_of_bunionᵢ_subset_bunionᵢ fun _ _ => h₁ _) <| h.Superset
#align pairwise.bUnion_injective Pairwise.bunionᵢ_injective

end

