/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Yaël Dillies
-/
import Mathlib.Order.Cover
import Mathlib.Order.LatticeIntervals

#align_import order.modular_lattice from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

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
  covby_sup_of_inf_covby_covby {a b : α} : a ⊓ b ⋖ a → a ⊓ b ⋖ b → a ⋖ a ⊔ b
#align is_weak_upper_modular_lattice IsWeakUpperModularLattice

/-- A weakly lower modular lattice is a lattice where `a` and `b` cover `a ⊓ b` if `a ⊔ b` covers
both `a` and `b`. -/
class IsWeakLowerModularLattice (α : Type*) [Lattice α] : Prop where
/-- `a` and `b` cover `a ⊓ b` if `a ⊔ b` covers both `a` and `b` -/
  inf_covby_of_covby_covby_sup {a b : α} : a ⋖ a ⊔ b → b ⋖ a ⊔ b → a ⊓ b ⋖ a
#align is_weak_lower_modular_lattice IsWeakLowerModularLattice

/-- An upper modular lattice, aka semimodular lattice, is a lattice where `a ⊔ b` covers `a` and `b`
if either `a` or `b` covers `a ⊓ b`. -/
class IsUpperModularLattice (α : Type*) [Lattice α] : Prop where
/-- `a ⊔ b` covers `a` and `b` if either `a` or `b` covers `a ⊓ b` -/
  covby_sup_of_inf_covby {a b : α} : a ⊓ b ⋖ a → b ⋖ a ⊔ b
#align is_upper_modular_lattice IsUpperModularLattice

/-- A lower modular lattice is a lattice where `a` and `b` both cover `a ⊓ b` if `a ⊔ b` covers
either `a` or `b`. -/
class IsLowerModularLattice (α : Type*) [Lattice α] : Prop where
/-- `a` and `b` both cover `a ⊓ b` if `a ⊔ b` covers either `a` or `b` -/
  inf_covby_of_covby_sup {a b : α} : a ⋖ a ⊔ b → a ⊓ b ⋖ b
#align is_lower_modular_lattice IsLowerModularLattice

/-- A modular lattice is one with a limited associativity between `⊓` and `⊔`. -/
class IsModularLattice (α : Type*) [Lattice α] : Prop where
/-- Whenever `x ≤ z`, then for any `y`, `(x ⊔ y) ⊓ z ≤ x ⊔ (y ⊓ z)`  -/
  sup_inf_le_assoc_of_le : ∀ {x : α} (y : α) {z : α}, x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ y ⊓ z
#align is_modular_lattice IsModularLattice

section WeakUpperModular

variable [Lattice α] [IsWeakUpperModularLattice α] {a b : α}

theorem covby_sup_of_inf_covby_of_inf_covby_left : a ⊓ b ⋖ a → a ⊓ b ⋖ b → a ⋖ a ⊔ b :=
  IsWeakUpperModularLattice.covby_sup_of_inf_covby_covby
#align covby_sup_of_inf_covby_of_inf_covby_left covby_sup_of_inf_covby_of_inf_covby_left

theorem covby_sup_of_inf_covby_of_inf_covby_right : a ⊓ b ⋖ a → a ⊓ b ⋖ b → b ⋖ a ⊔ b := by
  rw [inf_comm, sup_comm]
  -- ⊢ b ⊓ a ⋖ a → b ⊓ a ⋖ b → b ⋖ b ⊔ a
  exact fun ha hb => covby_sup_of_inf_covby_of_inf_covby_left hb ha
  -- 🎉 no goals
#align covby_sup_of_inf_covby_of_inf_covby_right covby_sup_of_inf_covby_of_inf_covby_right

alias Covby.sup_of_inf_of_inf_left := covby_sup_of_inf_covby_of_inf_covby_left
#align covby.sup_of_inf_of_inf_left Covby.sup_of_inf_of_inf_left

alias Covby.sup_of_inf_of_inf_right := covby_sup_of_inf_covby_of_inf_covby_right
#align covby.sup_of_inf_of_inf_right Covby.sup_of_inf_of_inf_right

instance : IsWeakLowerModularLattice (OrderDual α) :=
  ⟨fun ha hb => (ha.ofDual.sup_of_inf_of_inf_left hb.ofDual).toDual⟩

end WeakUpperModular

section WeakLowerModular

variable [Lattice α] [IsWeakLowerModularLattice α] {a b : α}

theorem inf_covby_of_covby_sup_of_covby_sup_left : a ⋖ a ⊔ b → b ⋖ a ⊔ b → a ⊓ b ⋖ a :=
  IsWeakLowerModularLattice.inf_covby_of_covby_covby_sup
#align inf_covby_of_covby_sup_of_covby_sup_left inf_covby_of_covby_sup_of_covby_sup_left

theorem inf_covby_of_covby_sup_of_covby_sup_right : a ⋖ a ⊔ b → b ⋖ a ⊔ b → a ⊓ b ⋖ b := by
  rw [sup_comm, inf_comm]
  -- ⊢ a ⋖ b ⊔ a → b ⋖ b ⊔ a → b ⊓ a ⋖ b
  exact fun ha hb => inf_covby_of_covby_sup_of_covby_sup_left hb ha
  -- 🎉 no goals
#align inf_covby_of_covby_sup_of_covby_sup_right inf_covby_of_covby_sup_of_covby_sup_right

alias Covby.inf_of_sup_of_sup_left := inf_covby_of_covby_sup_of_covby_sup_left
#align covby.inf_of_sup_of_sup_left Covby.inf_of_sup_of_sup_left

alias Covby.inf_of_sup_of_sup_right := inf_covby_of_covby_sup_of_covby_sup_right
#align covby.inf_of_sup_of_sup_right Covby.inf_of_sup_of_sup_right

instance : IsWeakUpperModularLattice (OrderDual α) :=
  ⟨fun ha hb => (ha.ofDual.inf_of_sup_of_sup_left hb.ofDual).toDual⟩

end WeakLowerModular

section UpperModular

variable [Lattice α] [IsUpperModularLattice α] {a b : α}

theorem covby_sup_of_inf_covby_left : a ⊓ b ⋖ a → b ⋖ a ⊔ b :=
  IsUpperModularLattice.covby_sup_of_inf_covby
#align covby_sup_of_inf_covby_left covby_sup_of_inf_covby_left

theorem covby_sup_of_inf_covby_right : a ⊓ b ⋖ b → a ⋖ a ⊔ b := by
  rw [sup_comm, inf_comm]
  -- ⊢ b ⊓ a ⋖ b → a ⋖ b ⊔ a
  exact covby_sup_of_inf_covby_left
  -- 🎉 no goals
#align covby_sup_of_inf_covby_right covby_sup_of_inf_covby_right

alias Covby.sup_of_inf_left := covby_sup_of_inf_covby_left
#align covby.sup_of_inf_left Covby.sup_of_inf_left

alias Covby.sup_of_inf_right := covby_sup_of_inf_covby_right
#align covby.sup_of_inf_right Covby.sup_of_inf_right

-- See note [lower instance priority]
instance (priority := 100) IsUpperModularLattice.to_isWeakUpperModularLattice :
    IsWeakUpperModularLattice α :=
  ⟨fun _ => Covby.sup_of_inf_right⟩
#align is_upper_modular_lattice.to_is_weak_upper_modular_lattice IsUpperModularLattice.to_isWeakUpperModularLattice

instance : IsLowerModularLattice (OrderDual α) :=
  ⟨fun h => h.ofDual.sup_of_inf_left.toDual⟩

end UpperModular

section LowerModular

variable [Lattice α] [IsLowerModularLattice α] {a b : α}

theorem inf_covby_of_covby_sup_left : a ⋖ a ⊔ b → a ⊓ b ⋖ b :=
  IsLowerModularLattice.inf_covby_of_covby_sup
#align inf_covby_of_covby_sup_left inf_covby_of_covby_sup_left

theorem inf_covby_of_covby_sup_right : b ⋖ a ⊔ b → a ⊓ b ⋖ a := by
  rw [inf_comm, sup_comm]
  -- ⊢ b ⋖ b ⊔ a → b ⊓ a ⋖ a
  exact inf_covby_of_covby_sup_left
  -- 🎉 no goals
#align inf_covby_of_covby_sup_right inf_covby_of_covby_sup_right

alias Covby.inf_of_sup_left := inf_covby_of_covby_sup_left
#align covby.inf_of_sup_left Covby.inf_of_sup_left

alias Covby.inf_of_sup_right := inf_covby_of_covby_sup_right
#align covby.inf_of_sup_right Covby.inf_of_sup_right

-- See note [lower instance priority]
instance (priority := 100) IsLowerModularLattice.to_isWeakLowerModularLattice :
    IsWeakLowerModularLattice α :=
  ⟨fun _ => Covby.inf_of_sup_right⟩
#align is_lower_modular_lattice.to_is_weak_lower_modular_lattice IsLowerModularLattice.to_isWeakLowerModularLattice

instance : IsUpperModularLattice (OrderDual α) :=
  ⟨fun h => h.ofDual.inf_of_sup_left.toDual⟩

end LowerModular

section IsModularLattice

variable [Lattice α] [IsModularLattice α]

theorem sup_inf_assoc_of_le {x : α} (y : α) {z : α} (h : x ≤ z) : (x ⊔ y) ⊓ z = x ⊔ y ⊓ z :=
  le_antisymm (IsModularLattice.sup_inf_le_assoc_of_le y h)
    (le_inf (sup_le_sup_left inf_le_left _) (sup_le h inf_le_right))
#align sup_inf_assoc_of_le sup_inf_assoc_of_le

theorem IsModularLattice.inf_sup_inf_assoc {x y z : α} : x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z :=
  (sup_inf_assoc_of_le y inf_le_right).symm
#align is_modular_lattice.inf_sup_inf_assoc IsModularLattice.inf_sup_inf_assoc

theorem inf_sup_assoc_of_le {x : α} (y : α) {z : α} (h : z ≤ x) : x ⊓ y ⊔ z = x ⊓ (y ⊔ z) := by
  rw [inf_comm, sup_comm, ← sup_inf_assoc_of_le y h, inf_comm, sup_comm]
  -- 🎉 no goals
#align inf_sup_assoc_of_le inf_sup_assoc_of_le

instance : IsModularLattice αᵒᵈ :=
  ⟨fun y z xz =>
    le_of_eq
      (by
        rw [inf_comm, sup_comm, eq_comm, inf_comm, sup_comm]
        -- ⊢ z ⊓ y ⊔ x✝ = z ⊓ (y ⊔ x✝)
        exact @sup_inf_assoc_of_le α _ _ _ y _ xz)⟩
        -- 🎉 no goals

variable {x y z : α}

theorem IsModularLattice.sup_inf_sup_assoc : (x ⊔ z) ⊓ (y ⊔ z) = (x ⊔ z) ⊓ y ⊔ z :=
  @IsModularLattice.inf_sup_inf_assoc αᵒᵈ _ _ _ _ _
#align is_modular_lattice.sup_inf_sup_assoc IsModularLattice.sup_inf_sup_assoc

theorem eq_of_le_of_inf_le_of_sup_le (hxy : x ≤ y) (hinf : y ⊓ z ≤ x ⊓ z) (hsup : y ⊔ z ≤ x ⊔ z) :
    x = y :=
  le_antisymm hxy <|
    have h : y ≤ x ⊔ z :=
      calc
        y ≤ y ⊔ z := le_sup_left
        _ ≤ x ⊔ z := hsup
    calc
      y ≤ (x ⊔ z) ⊓ y := le_inf h le_rfl
      _ = x ⊔ z ⊓ y := sup_inf_assoc_of_le _ hxy
      _ ≤ x ⊔ z ⊓ x := sup_le_sup_left (by rw [inf_comm, @inf_comm _ _ z]; exact hinf) _
                                           -- ⊢ y ⊓ z ≤ x ⊓ z
                                                                           -- 🎉 no goals
      _ ≤ x := sup_le le_rfl inf_le_right
#align eq_of_le_of_inf_le_of_sup_le eq_of_le_of_inf_le_of_sup_le

theorem sup_lt_sup_of_lt_of_inf_le_inf (hxy : x < y) (hinf : y ⊓ z ≤ x ⊓ z) : x ⊔ z < y ⊔ z :=
  lt_of_le_of_ne (sup_le_sup_right (le_of_lt hxy) _) fun hsup =>
    ne_of_lt hxy <| eq_of_le_of_inf_le_of_sup_le (le_of_lt hxy) hinf (le_of_eq hsup.symm)
#align sup_lt_sup_of_lt_of_inf_le_inf sup_lt_sup_of_lt_of_inf_le_inf

theorem inf_lt_inf_of_lt_of_sup_le_sup (hxy : x < y) (hinf : y ⊔ z ≤ x ⊔ z) : x ⊓ z < y ⊓ z :=
  @sup_lt_sup_of_lt_of_inf_le_inf αᵒᵈ _ _ _ _ _ hxy hinf
#align inf_lt_inf_of_lt_of_sup_le_sup inf_lt_inf_of_lt_of_sup_le_sup

/-- A generalization of the theorem that if `N` is a submodule of `M` and
  `N` and `M / N` are both Artinian, then `M` is Artinian. -/
theorem wellFounded_lt_exact_sequence {β γ : Type*} [PartialOrder β] [Preorder γ]
    (h₁ : WellFounded ((· < ·) : β → β → Prop)) (h₂ : WellFounded ((· < ·) : γ → γ → Prop)) (K : α)
    (f₁ : β → α) (f₂ : α → β) (g₁ : γ → α) (g₂ : α → γ) (gci : GaloisCoinsertion f₁ f₂)
    (gi : GaloisInsertion g₂ g₁) (hf : ∀ a, f₁ (f₂ a) = a ⊓ K) (hg : ∀ a, g₁ (g₂ a) = a ⊔ K) :
    WellFounded ((· < ·) : α → α → Prop) :=
  Subrelation.wf
    (@fun A B hAB =>
      show Prod.Lex (· < ·) (· < ·) (f₂ A, g₂ A) (f₂ B, g₂ B) by
        simp only [Prod.lex_def, lt_iff_le_not_le, ← gci.l_le_l_iff, ← gi.u_le_u_iff, hf, hg,
          le_antisymm_iff]
        simp only [gci.l_le_l_iff, gi.u_le_u_iff, ← lt_iff_le_not_le, ← le_antisymm_iff]
        -- ⊢ A ⊓ K < B ⊓ K ∨ A ⊓ K = B ⊓ K ∧ A ⊔ K < B ⊔ K
        cases' lt_or_eq_of_le (inf_le_inf_right K (le_of_lt hAB)) with h h
        -- ⊢ A ⊓ K < B ⊓ K ∨ A ⊓ K = B ⊓ K ∧ A ⊔ K < B ⊔ K
        · exact Or.inl h
          -- 🎉 no goals
        · exact Or.inr ⟨h, sup_lt_sup_of_lt_of_inf_le_inf hAB (le_of_eq h.symm)⟩)
          -- 🎉 no goals
    (InvImage.wf _ (h₁.prod_lex h₂))
#align well_founded_lt_exact_sequence wellFounded_lt_exact_sequence

/-- A generalization of the theorem that if `N` is a submodule of `M` and
  `N` and `M / N` are both Noetherian, then `M` is Noetherian.  -/
theorem wellFounded_gt_exact_sequence {β γ : Type*} [Preorder β] [PartialOrder γ]
    (h₁ : WellFounded ((· > ·) : β → β → Prop)) (h₂ : WellFounded ((· > ·) : γ → γ → Prop)) (K : α)
    (f₁ : β → α) (f₂ : α → β) (g₁ : γ → α) (g₂ : α → γ) (gci : GaloisCoinsertion f₁ f₂)
    (gi : GaloisInsertion g₂ g₁) (hf : ∀ a, f₁ (f₂ a) = a ⊓ K) (hg : ∀ a, g₁ (g₂ a) = a ⊔ K) :
    WellFounded ((· > ·) : α → α → Prop) :=
  @wellFounded_lt_exact_sequence αᵒᵈ _ _ γᵒᵈ βᵒᵈ _ _ h₂ h₁ K g₁ g₂ f₁ f₂ gi.dual gci.dual hg hf
#align well_founded_gt_exact_sequence wellFounded_gt_exact_sequence

/-- The diamond isomorphism between the intervals `[a ⊓ b, a]` and `[b, a ⊔ b]` -/
@[simps]
def infIccOrderIsoIccSup (a b : α) : Set.Icc (a ⊓ b) a ≃o Set.Icc b (a ⊔ b) where
  toFun x := ⟨x ⊔ b, ⟨le_sup_right, sup_le_sup_right x.prop.2 b⟩⟩
  invFun x := ⟨a ⊓ x, ⟨inf_le_inf_left a x.prop.1, inf_le_left⟩⟩
  left_inv x :=
    Subtype.ext
      (by
        change a ⊓ (↑x ⊔ b) = ↑x
        -- ⊢ a ⊓ (↑x ⊔ b) = ↑x
        rw [sup_comm, ← inf_sup_assoc_of_le _ x.prop.2, sup_eq_right.2 x.prop.1])
        -- 🎉 no goals
  right_inv x :=
    Subtype.ext
      (by
        change a ⊓ ↑x ⊔ b = ↑x
        -- ⊢ a ⊓ ↑x ⊔ b = ↑x
        rw [inf_comm, inf_sup_assoc_of_le _ x.prop.1, inf_eq_left.2 x.prop.2])
        -- 🎉 no goals
  map_rel_iff' := @fun x y => by
    simp only [Subtype.mk_le_mk, Equiv.coe_fn_mk, and_true_iff, le_sup_right]
    -- ⊢ ↑x ⊔ b ≤ ↑y ⊔ b ↔ x ≤ y
    rw [← Subtype.coe_le_coe]
    -- ⊢ ↑x ⊔ b ≤ ↑y ⊔ b ↔ ↑x ≤ ↑y
    refine' ⟨fun h => _, fun h => sup_le_sup_right h _⟩
    -- ⊢ ↑x ≤ ↑y
    rw [← sup_eq_right.2 x.prop.1, inf_sup_assoc_of_le _ x.prop.2, sup_comm, ←
      sup_eq_right.2 y.prop.1, inf_sup_assoc_of_le _ y.prop.2, @sup_comm _ _ b]
    exact inf_le_inf_left _ h
    -- 🎉 no goals
#align inf_Icc_order_iso_Icc_sup infIccOrderIsoIccSup
#align inf_Icc_order_iso_Icc_sup_apply_coe infIccOrderIsoIccSup_apply_coe
#align inf_Icc_order_iso_Icc_sup_symm_apply_coe infIccOrderIsoIccSup_symm_apply_coe

theorem inf_strictMonoOn_Icc_sup {a b : α} : StrictMonoOn (fun c => a ⊓ c) (Icc b (a ⊔ b)) :=
  StrictMono.of_restrict (infIccOrderIsoIccSup a b).symm.strictMono
#align inf_strict_mono_on_Icc_sup inf_strictMonoOn_Icc_sup

theorem sup_strictMonoOn_Icc_inf {a b : α} : StrictMonoOn (fun c => c ⊔ b) (Icc (a ⊓ b) a) :=
  StrictMono.of_restrict (infIccOrderIsoIccSup a b).strictMono
#align sup_strict_mono_on_Icc_inf sup_strictMonoOn_Icc_inf

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
      -- ⊢ a ⊓ (↑c ⊔ b) = ↑c
      rw [sup_comm, ← inf_sup_assoc_of_le _ c.prop.2.le, sup_eq_right.2 c.prop.1.le]
      -- 🎉 no goals
  right_inv c :=
    Subtype.ext <| by
      dsimp
      -- ⊢ a ⊓ ↑c ⊔ b = ↑c
      rw [inf_comm, inf_sup_assoc_of_le _ c.prop.1.le, inf_eq_left.2 c.prop.2.le]
      -- 🎉 no goals
  map_rel_iff' := @fun c d =>
    @OrderIso.le_iff_le _ _ _ _ (infIccOrderIsoIccSup _ _) ⟨c.1, Ioo_subset_Icc_self c.2⟩
      ⟨d.1, Ioo_subset_Icc_self d.2⟩
#align inf_Ioo_order_iso_Ioo_sup infIooOrderIsoIooSup
#align inf_Ioo_order_iso_Ioo_sup_apply_coe infIooOrderIsoIooSup_apply_coe
#align inf_Ioo_order_iso_Ioo_sup_symm_apply_coe infIooOrderIsoIooSup_symm_apply_coe

-- See note [lower instance priority]
instance (priority := 100) IsModularLattice.to_isLowerModularLattice : IsLowerModularLattice α :=
  ⟨fun {a b} => by
    simp_rw [covby_iff_Ioo_eq, @sup_comm _ _ a, @inf_comm _ _ a, ← isEmpty_coe_sort, right_lt_sup,
      inf_lt_left, (infIooOrderIsoIooSup b a).symm.toEquiv.isEmpty_congr]
    exact id⟩
    -- 🎉 no goals
#align is_modular_lattice.to_is_lower_modular_lattice IsModularLattice.to_isLowerModularLattice

-- See note [lower instance priority]
instance (priority := 100) IsModularLattice.to_isUpperModularLattice : IsUpperModularLattice α :=
  ⟨fun {a b} => by
    simp_rw [covby_iff_Ioo_eq, ← isEmpty_coe_sort, right_lt_sup, inf_lt_left,
      (infIooOrderIsoIooSup a b).toEquiv.isEmpty_congr]
    exact id⟩
    -- 🎉 no goals
#align is_modular_lattice.to_is_upper_modular_lattice IsModularLattice.to_isUpperModularLattice

end IsModularLattice

namespace IsCompl

variable [Lattice α] [BoundedOrder α] [IsModularLattice α]

/-- The diamond isomorphism between the intervals `Set.Iic a` and `Set.Ici b`. -/
def IicOrderIsoIci {a b : α} (h : IsCompl a b) : Set.Iic a ≃o Set.Ici b :=
  (OrderIso.setCongr (Set.Iic a) (Set.Icc (a ⊓ b) a)
        (h.inf_eq_bot.symm ▸ Set.Icc_bot.symm)).trans <|
    (infIccOrderIsoIccSup a b).trans
      (OrderIso.setCongr (Set.Icc b (a ⊔ b)) (Set.Ici b) (h.sup_eq_top.symm ▸ Set.Icc_top))
#align is_compl.Iic_order_iso_Ici IsCompl.IicOrderIsoIci

end IsCompl

theorem isModularLattice_iff_inf_sup_inf_assoc [Lattice α] :
    IsModularLattice α ↔ ∀ x y z : α, x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z :=
  ⟨fun h => @IsModularLattice.inf_sup_inf_assoc _ _ h, fun h =>
    ⟨fun y z xz => by rw [← inf_eq_left.2 xz, h]⟩⟩
                      -- 🎉 no goals
#align is_modular_lattice_iff_inf_sup_inf_assoc isModularLattice_iff_inf_sup_inf_assoc

namespace DistribLattice

instance (priority := 100) [DistribLattice α] : IsModularLattice α :=
  ⟨fun y z xz => by rw [inf_sup_right, inf_eq_left.2 xz]⟩
                    -- 🎉 no goals

end DistribLattice

theorem Disjoint.disjoint_sup_right_of_disjoint_sup_left [Lattice α] [OrderBot α]
    [IsModularLattice α] {a b c : α} (h : Disjoint a b) (hsup : Disjoint (a ⊔ b) c) :
    Disjoint a (b ⊔ c) := by
  rw [disjoint_iff_inf_le, ← h.eq_bot, sup_comm]
  -- ⊢ a ⊓ (c ⊔ b) ≤ a ⊓ b
  apply le_inf inf_le_left
  -- ⊢ a ⊓ (c ⊔ b) ≤ b
  apply (inf_le_inf_right (c ⊔ b) le_sup_right).trans
  -- ⊢ (?m.28074 ⊔ a) ⊓ (c ⊔ b) ≤ b
  rw [sup_comm, IsModularLattice.sup_inf_sup_assoc, hsup.eq_bot, bot_sup_eq]
  -- 🎉 no goals
#align disjoint.disjoint_sup_right_of_disjoint_sup_left Disjoint.disjoint_sup_right_of_disjoint_sup_left

theorem Disjoint.disjoint_sup_left_of_disjoint_sup_right [Lattice α] [OrderBot α]
    [IsModularLattice α] {a b c : α} (h : Disjoint b c) (hsup : Disjoint a (b ⊔ c)) :
    Disjoint (a ⊔ b) c := by
  rw [disjoint_comm, sup_comm]
  -- ⊢ Disjoint c (b ⊔ a)
  apply Disjoint.disjoint_sup_right_of_disjoint_sup_left h.symm
  -- ⊢ Disjoint (c ⊔ b) a
  rwa [sup_comm, disjoint_comm] at hsup
  -- 🎉 no goals
#align disjoint.disjoint_sup_left_of_disjoint_sup_right Disjoint.disjoint_sup_left_of_disjoint_sup_right

namespace IsModularLattice

variable [Lattice α] [IsModularLattice α] {a : α}

instance isModularLattice_Iic : IsModularLattice (Set.Iic a) :=
  ⟨@fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z ≤ ↑x ⊔ ↑y ⊓ ↑z)⟩
#align is_modular_lattice.is_modular_lattice_Iic IsModularLattice.isModularLattice_Iic

instance isModularLattice_Ici : IsModularLattice (Set.Ici a) :=
  ⟨@fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z ≤ ↑x ⊔ ↑y ⊓ ↑z)⟩
#align is_modular_lattice.is_modular_lattice_Ici IsModularLattice.isModularLattice_Ici

section ComplementedLattice

variable [BoundedOrder α] [ComplementedLattice α]

instance complementedLattice_Iic : ComplementedLattice (Set.Iic a) :=
  ⟨fun ⟨x, hx⟩ =>
    let ⟨y, hy⟩ := exists_isCompl x
    ⟨⟨y ⊓ a, Set.mem_Iic.2 inf_le_right⟩, by
      constructor
      -- ⊢ Disjoint { val := x, property := hx } { val := y ⊓ a, property := (_ : y ⊓ a …
      · rw [disjoint_iff_inf_le]
        -- ⊢ { val := x, property := hx } ⊓ { val := y ⊓ a, property := (_ : y ⊓ a ∈ Iic  …
        change x ⊓ (y ⊓ a) ≤ ⊥
        -- ⊢ x ⊓ (y ⊓ a) ≤ ⊥
        -- improve lattice subtype API
        rw [← inf_assoc]
        -- ⊢ x ⊓ y ⊓ a ≤ ⊥
        exact le_trans inf_le_left hy.1.le_bot
        -- 🎉 no goals
      · rw [codisjoint_iff_le_sup]
        -- ⊢ ⊤ ≤ { val := x, property := hx } ⊔ { val := y ⊓ a, property := (_ : y ⊓ a ∈  …
        change a ≤ x ⊔ y ⊓ a
        -- ⊢ a ≤ x ⊔ y ⊓ a
        -- improve lattice subtype API
        rw [← sup_inf_assoc_of_le _ (Set.mem_Iic.1 hx), hy.2.eq_top, top_inf_eq]⟩⟩
        -- 🎉 no goals
#align is_modular_lattice.complemented_lattice_Iic IsModularLattice.complementedLattice_Iic

instance complementedLattice_Ici : ComplementedLattice (Set.Ici a) :=
  ⟨fun ⟨x, hx⟩ =>
    let ⟨y, hy⟩ := exists_isCompl x
    ⟨⟨y ⊔ a, Set.mem_Ici.2 le_sup_right⟩, by
      constructor
      -- ⊢ Disjoint { val := x, property := hx } { val := y ⊔ a, property := (_ : y ⊔ a …
      · rw [disjoint_iff_inf_le]
        -- ⊢ { val := x, property := hx } ⊓ { val := y ⊔ a, property := (_ : y ⊔ a ∈ Ici  …
        change x ⊓ (y ⊔ a) ≤ a
        -- ⊢ x ⊓ (y ⊔ a) ≤ a
        -- improve lattice subtype API
        rw [← inf_sup_assoc_of_le _ (Set.mem_Ici.1 hx), hy.1.eq_bot, bot_sup_eq]
        -- 🎉 no goals
      · rw [codisjoint_iff_le_sup]
        -- ⊢ ⊤ ≤ { val := x, property := hx } ⊔ { val := y ⊔ a, property := (_ : y ⊔ a ∈  …
        change ⊤ ≤ x ⊔ (y ⊔ a)
        -- ⊢ ⊤ ≤ x ⊔ (y ⊔ a)
        -- improve lattice subtype API
        rw [← sup_assoc]
        -- ⊢ ⊤ ≤ x ⊔ y ⊔ a
        exact le_trans hy.2.top_le le_sup_left⟩⟩
        -- 🎉 no goals
#align is_modular_lattice.complemented_lattice_Ici IsModularLattice.complementedLattice_Ici

end ComplementedLattice

end IsModularLattice
