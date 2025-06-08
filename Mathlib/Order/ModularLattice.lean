/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Yaël Dillies
-/
import Mathlib.Data.Set.Monotone
import Mathlib.Order.Cover
import Mathlib.Order.LatticeIntervals
import Mathlib.Order.GaloisConnection.Defs

/-!
# Modular Lattices

This file defines (semi)modular lattices, a kind of lattice useful in algebra.
For examples, look to the subobject lattices of abelian groups, submodules, and ideals, or consider
any distributive lattice.

## Typeclasses

We define (semi)modularity typeclasses as Prop-valued mixins.

* `IsWeakUpperModularLattice`: Weakly upper modular lattices. Lattice where `a ⊔ b` covers `a`
  and `b` if `a` and `b` both cover `a ⊓ b`.
* `IsWeakLowerModularLattice`: Weakly lower modular lattices. Lattice where `a` and `b` cover
  `a ⊓ b` if `a ⊔ b` covers both `a` and `b`
* `IsUpperModularLattice`: Upper modular lattices. Lattices where `a ⊔ b` covers `a` if `b`
  covers `a ⊓ b`.
* `IsLowerModularLattice`: Lower modular lattices. Lattices where `a` covers `a ⊓ b` if `a ⊔ b`
  covers `b`.
- `IsModularLattice`: Modular lattices. Lattices where `a ≤ c → (a ⊔ b) ⊓ c = a ⊔ (b ⊓ c)`. We
  only require an inequality because the other direction holds in all lattices.

## Main Definitions

- `infIccOrderIsoIccSup` gives an order isomorphism between the intervals
  `[a ⊓ b, a]` and `[b, a ⊔ b]`.
  This corresponds to the diamond (or second) isomorphism theorems of algebra.

## Main Results

- `isModularLattice_iff_inf_sup_inf_assoc`:
  Modularity is equivalent to the `inf_sup_inf_assoc`: `(x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z`
- `DistribLattice.isModularLattice`: Distributive lattices are modular.

## References

* [Manfred Stern, *Semimodular lattices. {Theory} and applications*][stern2009]
* [Wikipedia, *Modular Lattice*][https://en.wikipedia.org/wiki/Modular_lattice]

## TODO

- Relate atoms and coatoms in modular lattices
-/


open Set

variable {α : Type*}

/-- A weakly upper modular lattice is a lattice where `a ⊔ b` covers `a` and `b` if `a` and `b` both
cover `a ⊓ b`. -/
class IsWeakUpperModularLattice (α : Type*) [Lattice α] : Prop where
/-- `a ⊔ b` covers `a` and `b` if `a` and `b` both cover `a ⊓ b`. -/
  covBy_sup_of_inf_covBy_covBy {a b : α} : a ⊓ b ⋖ a → a ⊓ b ⋖ b → a ⋖ a ⊔ b

/-- A weakly lower modular lattice is a lattice where `a` and `b` cover `a ⊓ b` if `a ⊔ b` covers
both `a` and `b`. -/
class IsWeakLowerModularLattice (α : Type*) [Lattice α] : Prop where
/-- `a` and `b` cover `a ⊓ b` if `a ⊔ b` covers both `a` and `b` -/
  inf_covBy_of_covBy_covBy_sup {a b : α} : a ⋖ a ⊔ b → b ⋖ a ⊔ b → a ⊓ b ⋖ a

/-- An upper modular lattice, aka semimodular lattice, is a lattice where `a ⊔ b` covers `a` and `b`
if either `a` or `b` covers `a ⊓ b`. -/
class IsUpperModularLattice (α : Type*) [Lattice α] : Prop where
/-- `a ⊔ b` covers `a` and `b` if either `a` or `b` covers `a ⊓ b` -/
  covBy_sup_of_inf_covBy {a b : α} : a ⊓ b ⋖ a → b ⋖ a ⊔ b

/-- A lower modular lattice is a lattice where `a` and `b` both cover `a ⊓ b` if `a ⊔ b` covers
either `a` or `b`. -/
class IsLowerModularLattice (α : Type*) [Lattice α] : Prop where
/-- `a` and `b` both cover `a ⊓ b` if `a ⊔ b` covers either `a` or `b` -/
  inf_covBy_of_covBy_sup {a b : α} : a ⋖ a ⊔ b → a ⊓ b ⋖ b

/-- A modular lattice is one with a limited associativity between `⊓` and `⊔`. -/
class IsModularLattice (α : Type*) [Lattice α] : Prop where
/-- Whenever `x ≤ z`, then for any `y`, `(x ⊔ y) ⊓ z ≤ x ⊔ (y ⊓ z)` -/
  sup_inf_le_assoc_of_le : ∀ {x : α} (y : α) {z : α}, x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ y ⊓ z

section WeakUpperModular

variable [Lattice α] [IsWeakUpperModularLattice α] {a b : α}

theorem covBy_sup_of_inf_covBy_of_inf_covBy_left : a ⊓ b ⋖ a → a ⊓ b ⋖ b → a ⋖ a ⊔ b :=
  IsWeakUpperModularLattice.covBy_sup_of_inf_covBy_covBy

theorem covBy_sup_of_inf_covBy_of_inf_covBy_right : a ⊓ b ⋖ a → a ⊓ b ⋖ b → b ⋖ a ⊔ b := by
  rw [inf_comm, sup_comm]
  exact fun ha hb => covBy_sup_of_inf_covBy_of_inf_covBy_left hb ha

alias CovBy.sup_of_inf_of_inf_left := covBy_sup_of_inf_covBy_of_inf_covBy_left

alias CovBy.sup_of_inf_of_inf_right := covBy_sup_of_inf_covBy_of_inf_covBy_right

instance : IsWeakLowerModularLattice (OrderDual α) :=
  ⟨fun ha hb => (ha.ofDual.sup_of_inf_of_inf_left hb.ofDual).toDual⟩

end WeakUpperModular

section WeakLowerModular

variable [Lattice α] [IsWeakLowerModularLattice α] {a b : α}

theorem inf_covBy_of_covBy_sup_of_covBy_sup_left : a ⋖ a ⊔ b → b ⋖ a ⊔ b → a ⊓ b ⋖ a :=
  IsWeakLowerModularLattice.inf_covBy_of_covBy_covBy_sup

theorem inf_covBy_of_covBy_sup_of_covBy_sup_right : a ⋖ a ⊔ b → b ⋖ a ⊔ b → a ⊓ b ⋖ b := by
  rw [sup_comm, inf_comm]
  exact fun ha hb => inf_covBy_of_covBy_sup_of_covBy_sup_left hb ha

alias CovBy.inf_of_sup_of_sup_left := inf_covBy_of_covBy_sup_of_covBy_sup_left

alias CovBy.inf_of_sup_of_sup_right := inf_covBy_of_covBy_sup_of_covBy_sup_right

instance : IsWeakUpperModularLattice (OrderDual α) :=
  ⟨fun ha hb => (ha.ofDual.inf_of_sup_of_sup_left hb.ofDual).toDual⟩

end WeakLowerModular

section UpperModular

variable [Lattice α] [IsUpperModularLattice α] {a b : α}

theorem covBy_sup_of_inf_covBy_left : a ⊓ b ⋖ a → b ⋖ a ⊔ b :=
  IsUpperModularLattice.covBy_sup_of_inf_covBy

theorem covBy_sup_of_inf_covBy_right : a ⊓ b ⋖ b → a ⋖ a ⊔ b := by
  rw [sup_comm, inf_comm]
  exact covBy_sup_of_inf_covBy_left

alias CovBy.sup_of_inf_left := covBy_sup_of_inf_covBy_left

alias CovBy.sup_of_inf_right := covBy_sup_of_inf_covBy_right

-- See note [lower instance priority]
instance (priority := 100) IsUpperModularLattice.to_isWeakUpperModularLattice :
    IsWeakUpperModularLattice α :=
  ⟨fun _ => CovBy.sup_of_inf_right⟩

instance : IsLowerModularLattice (OrderDual α) :=
  ⟨fun h => h.ofDual.sup_of_inf_left.toDual⟩

end UpperModular

section LowerModular

variable [Lattice α] [IsLowerModularLattice α] {a b : α}

theorem inf_covBy_of_covBy_sup_left : a ⋖ a ⊔ b → a ⊓ b ⋖ b :=
  IsLowerModularLattice.inf_covBy_of_covBy_sup

theorem inf_covBy_of_covBy_sup_right : b ⋖ a ⊔ b → a ⊓ b ⋖ a := by
  rw [inf_comm, sup_comm]
  exact inf_covBy_of_covBy_sup_left

alias CovBy.inf_of_sup_left := inf_covBy_of_covBy_sup_left

alias CovBy.inf_of_sup_right := inf_covBy_of_covBy_sup_right

-- See note [lower instance priority]
instance (priority := 100) IsLowerModularLattice.to_isWeakLowerModularLattice :
    IsWeakLowerModularLattice α :=
  ⟨fun _ => CovBy.inf_of_sup_right⟩

instance : IsUpperModularLattice (OrderDual α) :=
  ⟨fun h => h.ofDual.inf_of_sup_left.toDual⟩

end LowerModular

section IsModularLattice

variable [Lattice α] [IsModularLattice α]

theorem sup_inf_assoc_of_le {x : α} (y : α) {z : α} (h : x ≤ z) : (x ⊔ y) ⊓ z = x ⊔ y ⊓ z :=
  le_antisymm (IsModularLattice.sup_inf_le_assoc_of_le y h)
    (le_inf (sup_le_sup_left inf_le_left _) (sup_le h inf_le_right))

theorem IsModularLattice.inf_sup_inf_assoc {x y z : α} : x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z :=
  (sup_inf_assoc_of_le y inf_le_right).symm

theorem inf_sup_assoc_of_le {x : α} (y : α) {z : α} (h : z ≤ x) : x ⊓ y ⊔ z = x ⊓ (y ⊔ z) := by
  rw [inf_comm, sup_comm, ← sup_inf_assoc_of_le y h, inf_comm, sup_comm]

instance : IsModularLattice αᵒᵈ :=
  ⟨fun y z xz =>
    le_of_eq
      (by
        rw [inf_comm, sup_comm, eq_comm, inf_comm, sup_comm]
        exact @sup_inf_assoc_of_le α _ _ _ y _ xz)⟩

variable {x y z : α}

theorem IsModularLattice.sup_inf_sup_assoc : (x ⊔ z) ⊓ (y ⊔ z) = (x ⊔ z) ⊓ y ⊔ z :=
  @IsModularLattice.inf_sup_inf_assoc αᵒᵈ _ _ _ _ _

theorem eq_of_le_of_inf_le_of_le_sup (hxy : x ≤ y) (hinf : y ⊓ z ≤ x) (hsup : y ≤ x ⊔ z) :
    x = y := by
  refine hxy.antisymm ?_
  rw [← inf_eq_right, sup_inf_assoc_of_le _ hxy] at hsup
  rwa [← hsup, sup_le_iff, and_iff_right rfl.le, inf_comm]

theorem eq_of_le_of_inf_le_of_sup_le (hxy : x ≤ y) (hinf : y ⊓ z ≤ x ⊓ z) (hsup : y ⊔ z ≤ x ⊔ z) :
    x = y :=
  eq_of_le_of_inf_le_of_le_sup hxy (hinf.trans inf_le_left) (le_sup_left.trans hsup)

theorem sup_lt_sup_of_lt_of_inf_le_inf (hxy : x < y) (hinf : y ⊓ z ≤ x ⊓ z) : x ⊔ z < y ⊔ z :=
  lt_of_le_of_ne (sup_le_sup_right (le_of_lt hxy) _) fun hsup =>
    ne_of_lt hxy <| eq_of_le_of_inf_le_of_sup_le (le_of_lt hxy) hinf (le_of_eq hsup.symm)

theorem inf_lt_inf_of_lt_of_sup_le_sup (hxy : x < y) (hinf : y ⊔ z ≤ x ⊔ z) : x ⊓ z < y ⊓ z :=
  sup_lt_sup_of_lt_of_inf_le_inf (α := αᵒᵈ) hxy hinf

theorem strictMono_inf_prod_sup : StrictMono fun x ↦ (x ⊓ z, x ⊔ z) := fun _x _y hxy ↦
  ⟨⟨inf_le_inf_right _ hxy.le, sup_le_sup_right hxy.le _⟩,
    fun ⟨inf_le, sup_le⟩ ↦ (sup_lt_sup_of_lt_of_inf_le_inf hxy inf_le).not_ge sup_le⟩

/-- A generalization of the theorem that if `N` is a submodule of `M` and
  `N` and `M / N` are both Artinian, then `M` is Artinian. -/
theorem wellFounded_lt_exact_sequence {β γ : Type*} [Preorder β] [Preorder γ]
    [h₁ : WellFoundedLT β] [h₂ : WellFoundedLT γ] (K : α)
    (f₁ : β → α) (f₂ : α → β) (g₁ : γ → α) (g₂ : α → γ) (gci : GaloisCoinsertion f₁ f₂)
    (gi : GaloisInsertion g₂ g₁) (hf : ∀ a, f₁ (f₂ a) = a ⊓ K) (hg : ∀ a, g₁ (g₂ a) = a ⊔ K) :
    WellFoundedLT α :=
  StrictMono.wellFoundedLT (f := fun A ↦ (f₂ A, g₂ A)) fun A B hAB ↦ by
    simp only [Prod.le_def, lt_iff_le_not_ge, ← gci.l_le_l_iff, ← gi.u_le_u_iff, hf, hg]
    exact strictMono_inf_prod_sup hAB

/-- A generalization of the theorem that if `N` is a submodule of `M` and
  `N` and `M / N` are both Noetherian, then `M` is Noetherian. -/
theorem wellFounded_gt_exact_sequence {β γ : Type*} [Preorder β] [Preorder γ]
    [WellFoundedGT β] [WellFoundedGT γ] (K : α)
    (f₁ : β → α) (f₂ : α → β) (g₁ : γ → α) (g₂ : α → γ) (gci : GaloisCoinsertion f₁ f₂)
    (gi : GaloisInsertion g₂ g₁) (hf : ∀ a, f₁ (f₂ a) = a ⊓ K) (hg : ∀ a, g₁ (g₂ a) = a ⊔ K) :
    WellFoundedGT α :=
  wellFounded_lt_exact_sequence (α := αᵒᵈ) (β := γᵒᵈ) (γ := βᵒᵈ)
    K g₁ g₂ f₁ f₂ gi.dual gci.dual hg hf

/-- The diamond isomorphism between the intervals `[a ⊓ b, a]` and `[b, a ⊔ b]` -/
@[simps]
def infIccOrderIsoIccSup (a b : α) : Set.Icc (a ⊓ b) a ≃o Set.Icc b (a ⊔ b) where
  toFun x := ⟨x ⊔ b, ⟨le_sup_right, sup_le_sup_right x.prop.2 b⟩⟩
  invFun x := ⟨a ⊓ x, ⟨inf_le_inf_left a x.prop.1, inf_le_left⟩⟩
  left_inv x :=
    Subtype.ext
      (by
        change a ⊓ (↑x ⊔ b) = ↑x
        rw [sup_comm, ← inf_sup_assoc_of_le _ x.prop.2, sup_eq_right.2 x.prop.1])
  right_inv x :=
    Subtype.ext
      (by
        change a ⊓ ↑x ⊔ b = ↑x
        rw [inf_comm, inf_sup_assoc_of_le _ x.prop.1, inf_eq_left.2 x.prop.2])
  map_rel_iff' {x y} := by
    simp only [Subtype.mk_le_mk, Equiv.coe_fn_mk, le_sup_right]
    rw [← Subtype.coe_le_coe]
    refine ⟨fun h => ?_, fun h => sup_le_sup_right h _⟩
    rw [← sup_eq_right.2 x.prop.1, inf_sup_assoc_of_le _ x.prop.2, sup_comm, ←
      sup_eq_right.2 y.prop.1, inf_sup_assoc_of_le _ y.prop.2, sup_comm b]
    exact inf_le_inf_left _ h

theorem inf_strictMonoOn_Icc_sup {a b : α} : StrictMonoOn (fun c => a ⊓ c) (Icc b (a ⊔ b)) :=
  StrictMono.of_restrict (infIccOrderIsoIccSup a b).symm.strictMono

theorem sup_strictMonoOn_Icc_inf {a b : α} : StrictMonoOn (fun c => c ⊔ b) (Icc (a ⊓ b) a) :=
  StrictMono.of_restrict (infIccOrderIsoIccSup a b).strictMono

/-- The diamond isomorphism between the intervals `]a ⊓ b, a[` and `}b, a ⊔ b[`. -/
@[simps]
def infIooOrderIsoIooSup (a b : α) : Ioo (a ⊓ b) a ≃o Ioo b (a ⊔ b) where
  toFun c :=
    ⟨c ⊔ b,
      le_sup_right.trans_lt <|
        sup_strictMonoOn_Icc_inf (left_mem_Icc.2 inf_le_left) (Ioo_subset_Icc_self c.2) c.2.1,
      sup_strictMonoOn_Icc_inf (Ioo_subset_Icc_self c.2) (right_mem_Icc.2 inf_le_left) c.2.2⟩
  invFun c :=
    ⟨a ⊓ c,
      inf_strictMonoOn_Icc_sup (left_mem_Icc.2 le_sup_right) (Ioo_subset_Icc_self c.2) c.2.1,
      inf_le_left.trans_lt' <|
        inf_strictMonoOn_Icc_sup (Ioo_subset_Icc_self c.2) (right_mem_Icc.2 le_sup_right) c.2.2⟩
  left_inv c :=
    Subtype.ext <| by
      dsimp
      rw [sup_comm, ← inf_sup_assoc_of_le _ c.prop.2.le, sup_eq_right.2 c.prop.1.le]
  right_inv c :=
    Subtype.ext <| by
      dsimp
      rw [inf_comm, inf_sup_assoc_of_le _ c.prop.1.le, inf_eq_left.2 c.prop.2.le]
  map_rel_iff' := @fun c d =>
    @OrderIso.le_iff_le _ _ _ _ (infIccOrderIsoIccSup _ _) ⟨c.1, Ioo_subset_Icc_self c.2⟩
      ⟨d.1, Ioo_subset_Icc_self d.2⟩

-- See note [lower instance priority]
instance (priority := 100) IsModularLattice.to_isLowerModularLattice : IsLowerModularLattice α :=
  ⟨fun {a b} => by
    simp_rw [covBy_iff_Ioo_eq, sup_comm a, inf_comm a, ← isEmpty_coe_sort, right_lt_sup,
      inf_lt_left, (infIooOrderIsoIooSup b a).symm.toEquiv.isEmpty_congr]
    exact id⟩

-- See note [lower instance priority]
instance (priority := 100) IsModularLattice.to_isUpperModularLattice : IsUpperModularLattice α :=
  ⟨fun {a b} => by
    simp_rw [covBy_iff_Ioo_eq, ← isEmpty_coe_sort, right_lt_sup, inf_lt_left,
      (infIooOrderIsoIooSup a b).toEquiv.isEmpty_congr]
    exact id⟩

end IsModularLattice

namespace IsCompl

variable [Lattice α] [BoundedOrder α] [IsModularLattice α]

/-- The diamond isomorphism between the intervals `Set.Iic a` and `Set.Ici b`. -/
def IicOrderIsoIci {a b : α} (h : IsCompl a b) : Set.Iic a ≃o Set.Ici b :=
  (OrderIso.setCongr (Set.Iic a) (Set.Icc (a ⊓ b) a)
        (h.inf_eq_bot.symm ▸ Set.Icc_bot.symm)).trans <|
    (infIccOrderIsoIccSup a b).trans
      (OrderIso.setCongr (Set.Icc b (a ⊔ b)) (Set.Ici b) (h.sup_eq_top.symm ▸ Set.Icc_top))

end IsCompl

theorem isModularLattice_iff_inf_sup_inf_assoc [Lattice α] :
    IsModularLattice α ↔ ∀ x y z : α, x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z :=
  ⟨fun h => @IsModularLattice.inf_sup_inf_assoc _ _ h, fun h =>
    ⟨fun y z xz => by rw [← inf_eq_left.2 xz, h]⟩⟩

namespace DistribLattice

instance (priority := 100) [DistribLattice α] : IsModularLattice α :=
  ⟨fun y z xz => by rw [inf_sup_right, inf_eq_left.2 xz]⟩

end DistribLattice

namespace Disjoint

variable {a b c : α}

theorem disjoint_sup_right_of_disjoint_sup_left [Lattice α] [OrderBot α]
    [IsModularLattice α] (h : Disjoint a b) (hsup : Disjoint (a ⊔ b) c) :
    Disjoint a (b ⊔ c) := by
  rw [disjoint_iff_inf_le, ← h.eq_bot, sup_comm]
  apply le_inf inf_le_left
  apply (inf_le_inf_right (c ⊔ b) le_sup_right).trans
  rw [sup_comm, IsModularLattice.sup_inf_sup_assoc, hsup.eq_bot, bot_sup_eq]

theorem disjoint_sup_left_of_disjoint_sup_right [Lattice α] [OrderBot α]
    [IsModularLattice α] (h : Disjoint b c) (hsup : Disjoint a (b ⊔ c)) :
    Disjoint (a ⊔ b) c := by
  rw [disjoint_comm, sup_comm]
  apply Disjoint.disjoint_sup_right_of_disjoint_sup_left h.symm
  rwa [sup_comm, disjoint_comm] at hsup

theorem isCompl_sup_right_of_isCompl_sup_left [Lattice α] [BoundedOrder α] [IsModularLattice α]
    (h : Disjoint a b) (hcomp : IsCompl (a ⊔ b) c) :
    IsCompl a (b ⊔ c) :=
  ⟨h.disjoint_sup_right_of_disjoint_sup_left hcomp.disjoint, codisjoint_assoc.mp hcomp.codisjoint⟩

theorem isCompl_sup_left_of_isCompl_sup_right [Lattice α] [BoundedOrder α] [IsModularLattice α]
    (h : Disjoint b c) (hcomp : IsCompl a (b ⊔ c)) :
    IsCompl (a ⊔ b) c :=
  ⟨h.disjoint_sup_left_of_disjoint_sup_right hcomp.disjoint, codisjoint_assoc.mpr hcomp.codisjoint⟩

end Disjoint

lemma Set.Iic.isCompl_inf_inf_of_isCompl_of_le [Lattice α] [BoundedOrder α] [IsModularLattice α]
    {a b c : α} (h₁ : IsCompl b c) (h₂ : b ≤ a) :
    IsCompl (⟨a ⊓ b, inf_le_left⟩ : Iic a) (⟨a ⊓ c, inf_le_left⟩ : Iic a) := by
  constructor
  · simp [disjoint_iff, Subtype.ext_iff, inf_comm a c, inf_assoc a, ← inf_assoc b, h₁.inf_eq_bot]
  · simp only [Iic.codisjoint_iff, inf_comm a, IsModularLattice.inf_sup_inf_assoc]
    simp [inf_of_le_left h₂, h₁.sup_eq_top]

namespace IsModularLattice

variable [Lattice α] [IsModularLattice α] {a : α}

instance isModularLattice_Iic : IsModularLattice (Set.Iic a) :=
  ⟨@fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z ≤ ↑x ⊔ ↑y ⊓ ↑z)⟩

instance isModularLattice_Ici : IsModularLattice (Set.Ici a) :=
  ⟨@fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z ≤ ↑x ⊔ ↑y ⊓ ↑z)⟩

section ComplementedLattice

variable [BoundedOrder α] [ComplementedLattice α]

instance complementedLattice_Iic : ComplementedLattice (Set.Iic a) :=
  ⟨fun ⟨x, hx⟩ =>
    let ⟨y, hy⟩ := exists_isCompl x
    ⟨⟨y ⊓ a, Set.mem_Iic.2 inf_le_right⟩, by
      constructor
      · rw [disjoint_iff_inf_le]
        change x ⊓ (y ⊓ a) ≤ ⊥
        -- improve lattice subtype API
        rw [← inf_assoc]
        exact le_trans inf_le_left hy.1.le_bot
      · rw [codisjoint_iff_le_sup]
        change a ≤ x ⊔ y ⊓ a
        -- improve lattice subtype API
        rw [← sup_inf_assoc_of_le _ (Set.mem_Iic.1 hx), hy.2.eq_top, top_inf_eq]⟩⟩

instance complementedLattice_Ici : ComplementedLattice (Set.Ici a) :=
  ⟨fun ⟨x, hx⟩ =>
    let ⟨y, hy⟩ := exists_isCompl x
    ⟨⟨y ⊔ a, Set.mem_Ici.2 le_sup_right⟩, by
      constructor
      · rw [disjoint_iff_inf_le]
        change x ⊓ (y ⊔ a) ≤ a
        -- improve lattice subtype API
        rw [← inf_sup_assoc_of_le _ (Set.mem_Ici.1 hx), hy.1.eq_bot, bot_sup_eq]
      · rw [codisjoint_iff_le_sup]
        change ⊤ ≤ x ⊔ (y ⊔ a)
        -- improve lattice subtype API
        rw [← sup_assoc]
        exact le_trans hy.2.top_le le_sup_left⟩⟩

end ComplementedLattice

end IsModularLattice
