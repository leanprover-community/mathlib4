/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.PUnitInstances

#align_import algebra.module.submodule.lattice from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# The lattice structure on `Submodule`s

This file defines the lattice structure on submodules, `Submodule.CompleteLattice`, with `⊥`
defined as `{0}` and `⊓` defined as intersection of the underlying carrier.
If `p` and `q` are submodules of a module, `p ≤ q` means that `p ⊆ q`.

Many results about operations on this lattice structure are defined in `LinearAlgebra/Basic.lean`,
most notably those which use `span`.

## Implementation notes

This structure should match the `AddSubmonoid.CompleteLattice` structure, and we should try
to unify the APIs where possible.

-/

set_option autoImplicit true


variable {R S M : Type*}

section AddCommMonoid

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

namespace Submodule

/-- The set `{0}` is the bottom element of the lattice of submodules. -/
instance : Bot (Submodule R M) :=
  ⟨{ (⊥ : AddSubmonoid M) with
      carrier := {0}
      smul_mem' := by simp }⟩
                      -- 🎉 no goals

instance inhabited' : Inhabited (Submodule R M) :=
  ⟨⊥⟩
#align submodule.inhabited' Submodule.inhabited'

@[simp]
theorem bot_coe : ((⊥ : Submodule R M) : Set M) = {0} :=
  rfl
#align submodule.bot_coe Submodule.bot_coe

@[simp]
theorem bot_toAddSubmonoid : (⊥ : Submodule R M).toAddSubmonoid = ⊥ :=
  rfl
#align submodule.bot_to_add_submonoid Submodule.bot_toAddSubmonoid

section

variable (R)

@[simp]
theorem restrictScalars_bot : restrictScalars S (⊥ : Submodule R M) = ⊥ :=
  rfl
#align submodule.restrict_scalars_bot Submodule.restrictScalars_bot

@[simp]
theorem mem_bot {x : M} : x ∈ (⊥ : Submodule R M) ↔ x = 0 :=
  Set.mem_singleton_iff
#align submodule.mem_bot Submodule.mem_bot

end

@[simp]
theorem restrictScalars_eq_bot_iff {p : Submodule R M} : restrictScalars S p = ⊥ ↔ p = ⊥ := by
  simp [SetLike.ext_iff]
  -- 🎉 no goals
#align submodule.restrict_scalars_eq_bot_iff Submodule.restrictScalars_eq_bot_iff

instance uniqueBot : Unique (⊥ : Submodule R M) :=
  ⟨inferInstance, fun x ↦ Subtype.ext <| (mem_bot R).1 x.mem⟩
#align submodule.unique_bot Submodule.uniqueBot

instance : OrderBot (Submodule R M) where
  bot := ⊥
  bot_le p x := by simp (config := { contextual := true }) [zero_mem]
                   -- 🎉 no goals

protected theorem eq_bot_iff (p : Submodule R M) : p = ⊥ ↔ ∀ x ∈ p, x = (0 : M) :=
  ⟨fun h ↦ h.symm ▸ fun _ hx ↦ (mem_bot R).mp hx,
    fun h ↦ eq_bot_iff.mpr fun x hx ↦ (mem_bot R).mpr (h x hx)⟩
#align submodule.eq_bot_iff Submodule.eq_bot_iff

@[ext high]
protected theorem bot_ext (x y : (⊥ : Submodule R M)) : x = y := by
  rcases x with ⟨x, xm⟩; rcases y with ⟨y, ym⟩; congr
  -- ⊢ { val := x, property := xm } = y
                         -- ⊢ { val := x, property := xm } = { val := y, property := ym }
                                                -- ⊢ x = y
  rw [(Submodule.eq_bot_iff _).mp rfl x xm]
  -- ⊢ 0 = y
  rw [(Submodule.eq_bot_iff _).mp rfl y ym]
  -- 🎉 no goals
#align submodule.bot_ext Submodule.bot_ext

protected theorem ne_bot_iff (p : Submodule R M) : p ≠ ⊥ ↔ ∃ x ∈ p, x ≠ (0 : M) := by
  simp only [ne_eq, p.eq_bot_iff, not_forall, exists_prop]
  -- 🎉 no goals
#align submodule.ne_bot_iff Submodule.ne_bot_iff

theorem nonzero_mem_of_bot_lt {p : Submodule R M} (bot_lt : ⊥ < p) : ∃ a : p, a ≠ 0 :=
  let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp bot_lt.ne'
  ⟨⟨b, hb₁⟩, hb₂ ∘ congr_arg Subtype.val⟩
#align submodule.nonzero_mem_of_bot_lt Submodule.nonzero_mem_of_bot_lt

theorem exists_mem_ne_zero_of_ne_bot {p : Submodule R M} (h : p ≠ ⊥) : ∃ b : M, b ∈ p ∧ b ≠ 0 :=
  let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp h
  ⟨b, hb₁, hb₂⟩
#align submodule.exists_mem_ne_zero_of_ne_bot Submodule.exists_mem_ne_zero_of_ne_bot

-- FIXME: we default PUnit to PUnit.{1} here without the explicit universe annotation
/-- The bottom submodule is linearly equivalent to punit as an `R`-module. -/
@[simps]
def botEquivPUnit : (⊥ : Submodule R M) ≃ₗ[R] PUnit.{v+1} where
  toFun _ := PUnit.unit
  invFun _ := 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := rfl
#align submodule.bot_equiv_punit Submodule.botEquivPUnit

theorem eq_bot_of_subsingleton (p : Submodule R M) [Subsingleton p] : p = ⊥ := by
  rw [eq_bot_iff]
  -- ⊢ p ≤ ⊥
  intro v hv
  -- ⊢ v ∈ ⊥
  exact congr_arg Subtype.val (Subsingleton.elim (⟨v, hv⟩ : p) 0)
  -- 🎉 no goals
#align submodule.eq_bot_of_subsingleton Submodule.eq_bot_of_subsingleton

/-- The universal set is the top element of the lattice of submodules. -/
instance : Top (Submodule R M) :=
  ⟨{ (⊤ : AddSubmonoid M) with
      carrier := Set.univ
      smul_mem' := fun _ _ _ ↦ trivial }⟩

@[simp]
theorem top_coe : ((⊤ : Submodule R M) : Set M) = Set.univ :=
  rfl
#align submodule.top_coe Submodule.top_coe

@[simp]
theorem top_toAddSubmonoid : (⊤ : Submodule R M).toAddSubmonoid = ⊤ :=
  rfl
#align submodule.top_to_add_submonoid Submodule.top_toAddSubmonoid

@[simp]
theorem mem_top {x : M} : x ∈ (⊤ : Submodule R M) :=
  trivial
#align submodule.mem_top Submodule.mem_top

section

variable (R)

@[simp]
theorem restrictScalars_top : restrictScalars S (⊤ : Submodule R M) = ⊤ :=
  rfl
#align submodule.restrict_scalars_top Submodule.restrictScalars_top

end

@[simp]
theorem restrictScalars_eq_top_iff {p : Submodule R M} : restrictScalars S p = ⊤ ↔ p = ⊤ := by
  simp [SetLike.ext_iff]
  -- 🎉 no goals
#align submodule.restrict_scalars_eq_top_iff Submodule.restrictScalars_eq_top_iff

instance : OrderTop (Submodule R M) where
  top := ⊤
  le_top _ _ _ := trivial

theorem eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ ∀ x, x ∈ p :=
  eq_top_iff.trans ⟨fun h _ ↦ h trivial, fun h x _ ↦ h x⟩
#align submodule.eq_top_iff' Submodule.eq_top_iff'

/-- The top submodule is linearly equivalent to the module.

This is the module version of `AddSubmonoid.topEquiv`. -/
@[simps]
def topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M where
  toFun x := x
  invFun x := ⟨x, mem_top⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
#align submodule.top_equiv Submodule.topEquiv

instance : InfSet (Submodule R M) :=
  ⟨fun S ↦
    { carrier := ⋂ s ∈ S, (s : Set M)
      zero_mem' := by simp [zero_mem]
                      -- 🎉 no goals
                     -- 🎉 no goals
      add_mem' := by simp (config := { contextual := true }) [add_mem]
      smul_mem' := by simp (config := { contextual := true }) [smul_mem] }⟩
                      -- 🎉 no goals

private theorem sInf_le' {S : Set (Submodule R M)} {p} : p ∈ S → sInf S ≤ p :=
  Set.biInter_subset_of_mem

private theorem le_sInf' {S : Set (Submodule R M)} {p} : (∀ q ∈ S, p ≤ q) → p ≤ sInf S :=
  Set.subset_iInter₂

instance : Inf (Submodule R M) :=
  ⟨fun p q ↦
    { carrier := p ∩ q
      zero_mem' := by simp [zero_mem]
                      -- 🎉 no goals
                     -- 🎉 no goals
      add_mem' := by simp (config := { contextual := true }) [add_mem]
      smul_mem' := by simp (config := { contextual := true }) [smul_mem] }⟩
                      -- 🎉 no goals

instance completeLattice : CompleteLattice (Submodule R M) :=
  { (inferInstance : OrderTop (Submodule R M)),
    (inferInstance : OrderBot (Submodule R M)) with
    sup := fun a b ↦ sInf { x | a ≤ x ∧ b ≤ x }
    le_sup_left := fun _ _ ↦ le_sInf' fun _ ⟨h, _⟩ ↦ h
    le_sup_right := fun _ _ ↦ le_sInf' fun _ ⟨_, h⟩ ↦ h
    sup_le := fun _ _ _ h₁ h₂ ↦ sInf_le' ⟨h₁, h₂⟩
    inf := (· ⊓ ·)
    le_inf := fun _ _ _ ↦ Set.subset_inter
    inf_le_left := fun _ _ ↦ Set.inter_subset_left _ _
    inf_le_right := fun _ _ ↦ Set.inter_subset_right _ _
    le_sSup := fun _ _ hs ↦ le_sInf' fun _ hq ↦ by exact hq _ hs
                                                   -- 🎉 no goals
    sSup_le := fun _ _ hs ↦ sInf_le' hs
    le_sInf := fun _ _ ↦ le_sInf'
    sInf_le := fun _ _ ↦ sInf_le' }
#align submodule.complete_lattice Submodule.completeLattice

@[simp]
theorem inf_coe : ↑(p ⊓ q) = (p ∩ q : Set M) :=
  rfl
#align submodule.inf_coe Submodule.inf_coe

@[simp]
theorem mem_inf {p q : Submodule R M} {x : M} : x ∈ p ⊓ q ↔ x ∈ p ∧ x ∈ q :=
  Iff.rfl
#align submodule.mem_inf Submodule.mem_inf

@[simp]
theorem sInf_coe (P : Set (Submodule R M)) : (↑(sInf P) : Set M) = ⋂ p ∈ P, ↑p :=
  rfl
#align submodule.Inf_coe Submodule.sInf_coe

@[simp]
theorem finset_inf_coe {ι} (s : Finset ι) (p : ι → Submodule R M) :
    (↑(s.inf p) : Set M) = ⋂ i ∈ s, ↑(p i) := by
  letI := Classical.decEq ι
  -- ⊢ ↑(Finset.inf s p) = ⋂ (i : ι) (_ : i ∈ s), ↑(p i)
  refine' s.induction_on _ fun i s _ ih ↦ _
  -- ⊢ ↑(Finset.inf ∅ p) = ⋂ (i : ι) (_ : i ∈ ∅), ↑(p i)
  · simp
    -- 🎉 no goals
  · rw [Finset.inf_insert, inf_coe, ih]
    -- ⊢ ↑(p i) ∩ ⋂ (i : ι) (_ : i ∈ s), ↑(p i) = ⋂ (i_1 : ι) (_ : i_1 ∈ insert i s), …
    simp
    -- 🎉 no goals
#align submodule.finset_inf_coe Submodule.finset_inf_coe

@[simp]
theorem iInf_coe {ι} (p : ι → Submodule R M) : (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i) := by
  rw [iInf, sInf_coe]; simp only [Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq']
  -- ⊢ ⋂ (p_1 : Submodule R M) (_ : p_1 ∈ Set.range fun i => p i), ↑p_1 = ⋂ (i : ι) …
                       -- 🎉 no goals
#align submodule.infi_coe Submodule.iInf_coe

@[simp]
theorem mem_sInf {S : Set (Submodule R M)} {x : M} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂
#align submodule.mem_Inf Submodule.mem_sInf

@[simp]
theorem mem_iInf {ι} (p : ι → Submodule R M) {x} : (x ∈ ⨅ i, p i) ↔ ∀ i, x ∈ p i := by
  rw [← SetLike.mem_coe, iInf_coe, Set.mem_iInter]; rfl
  -- ⊢ (∀ (i : ι), x ∈ ↑(p i)) ↔ ∀ (i : ι), x ∈ p i
                                                    -- 🎉 no goals
#align submodule.mem_infi Submodule.mem_iInf

@[simp]
theorem mem_finset_inf {ι} {s : Finset ι} {p : ι → Submodule R M} {x : M} :
    x ∈ s.inf p ↔ ∀ i ∈ s, x ∈ p i := by
  simp only [← SetLike.mem_coe, finset_inf_coe, Set.mem_iInter]
  -- 🎉 no goals
#align submodule.mem_finset_inf Submodule.mem_finset_inf

theorem mem_sup_left {S T : Submodule R M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T := by
  have : S ≤ S ⊔ T := le_sup_left
  -- ⊢ ∀ {x : M}, x ∈ S → x ∈ S ⊔ T
  rw [LE.le] at this
  -- ⊢ ∀ {x : M}, x ∈ S → x ∈ S ⊔ T
  exact this
  -- 🎉 no goals
#align submodule.mem_sup_left Submodule.mem_sup_left

theorem mem_sup_right {S T : Submodule R M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T := by
  have : T ≤ S ⊔ T := le_sup_right
  -- ⊢ ∀ {x : M}, x ∈ T → x ∈ S ⊔ T
  rw [LE.le] at this
  -- ⊢ ∀ {x : M}, x ∈ T → x ∈ S ⊔ T
  exact this
  -- 🎉 no goals
#align submodule.mem_sup_right Submodule.mem_sup_right

theorem add_mem_sup {S T : Submodule R M} {s t : M} (hs : s ∈ S) (ht : t ∈ T) : s + t ∈ S ⊔ T :=
  add_mem (mem_sup_left hs) (mem_sup_right ht)
#align submodule.add_mem_sup Submodule.add_mem_sup

theorem sub_mem_sup {R' M' : Type*} [Ring R'] [AddCommGroup M'] [Module R' M']
    {S T : Submodule R' M'} {s t : M'} (hs : s ∈ S) (ht : t ∈ T) : s - t ∈ S ⊔ T := by
  rw [sub_eq_add_neg]
  -- ⊢ s + -t ∈ S ⊔ T
  exact add_mem_sup hs (neg_mem ht)
  -- 🎉 no goals
#align submodule.sub_mem_sup Submodule.sub_mem_sup

theorem mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι → Submodule R M} (i : ι) (h : b ∈ p i) :
    b ∈ ⨆ i, p i :=
  (le_iSup p i) h
#align submodule.mem_supr_of_mem Submodule.mem_iSup_of_mem

open BigOperators

theorem sum_mem_iSup {ι : Type*} [Fintype ι] {f : ι → M} {p : ι → Submodule R M}
    (h : ∀ i, f i ∈ p i) : (∑ i, f i) ∈ ⨆ i, p i :=
  sum_mem fun i _ ↦ mem_iSup_of_mem i (h i)
#align submodule.sum_mem_supr Submodule.sum_mem_iSup

theorem sum_mem_biSup {ι : Type*} {s : Finset ι} {f : ι → M} {p : ι → Submodule R M}
    (h : ∀ i ∈ s, f i ∈ p i) : (∑ i in s, f i) ∈ ⨆ i ∈ s, p i :=
  sum_mem fun i hi ↦ mem_iSup_of_mem i <| mem_iSup_of_mem hi (h i hi)
#align submodule.sum_mem_bsupr Submodule.sum_mem_biSup

/-! Note that `Submodule.mem_iSup` is provided in `LinearAlgebra/Span.lean`. -/


theorem mem_sSup_of_mem {S : Set (Submodule R M)} {s : Submodule R M} (hs : s ∈ S) :
    ∀ {x : M}, x ∈ s → x ∈ sSup S := by
  have := le_sSup hs
  -- ⊢ ∀ {x : M}, x ∈ s → x ∈ sSup S
  rw [LE.le] at this
  -- ⊢ ∀ {x : M}, x ∈ s → x ∈ sSup S
  exact this
  -- 🎉 no goals
#align submodule.mem_Sup_of_mem Submodule.mem_sSup_of_mem

theorem disjoint_def {p p' : Submodule R M} : Disjoint p p' ↔ ∀ x ∈ p, x ∈ p' → x = (0 : M) :=
  disjoint_iff_inf_le.trans <| show (∀ x, x ∈ p ∧ x ∈ p' → x ∈ ({0} : Set M)) ↔ _ by simp
                                                                                     -- 🎉 no goals
#align submodule.disjoint_def Submodule.disjoint_def

theorem disjoint_def' {p p' : Submodule R M} :
    Disjoint p p' ↔ ∀ x ∈ p, ∀ y ∈ p', x = y → x = (0 : M) :=
  disjoint_def.trans
    ⟨fun h x hx _ hy hxy ↦ h x hx <| hxy.symm ▸ hy, fun h x hx hx' ↦ h _ hx x hx' rfl⟩
#align submodule.disjoint_def' Submodule.disjoint_def'

theorem eq_zero_of_coe_mem_of_disjoint (hpq : Disjoint p q) {a : p} (ha : (a : M) ∈ q) : a = 0 := by
  exact_mod_cast disjoint_def.mp hpq a (coe_mem a) ha
  -- 🎉 no goals
#align submodule.eq_zero_of_coe_mem_of_disjoint Submodule.eq_zero_of_coe_mem_of_disjoint

end Submodule

section NatSubmodule

-- Porting note: `S.toNatSubmodule` doesn't work. I used `AddSubmonoid.toNatSubmodule S` instead.
/-- An additive submonoid is equivalent to a ℕ-submodule. -/
def AddSubmonoid.toNatSubmodule : AddSubmonoid M ≃o Submodule ℕ M where
  toFun S := { S with smul_mem' := fun r s hs ↦ show r • s ∈ S from nsmul_mem hs _ }
  invFun := Submodule.toAddSubmonoid
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
#align add_submonoid.to_nat_submodule AddSubmonoid.toNatSubmodule

@[simp]
theorem AddSubmonoid.toNatSubmodule_symm :
    ⇑(AddSubmonoid.toNatSubmodule.symm : _ ≃o AddSubmonoid M) = Submodule.toAddSubmonoid :=
  rfl
#align add_submonoid.to_nat_submodule_symm AddSubmonoid.toNatSubmodule_symm

@[simp]
theorem AddSubmonoid.coe_toNatSubmodule (S : AddSubmonoid M) :
    (AddSubmonoid.toNatSubmodule S : Set M) = S :=
  rfl
#align add_submonoid.coe_to_nat_submodule AddSubmonoid.coe_toNatSubmodule

@[simp]
theorem AddSubmonoid.toNatSubmodule_toAddSubmonoid (S : AddSubmonoid M) :
    S.toNatSubmodule.toAddSubmonoid = S :=
  AddSubmonoid.toNatSubmodule.symm_apply_apply S
#align add_submonoid.to_nat_submodule_to_add_submonoid AddSubmonoid.toNatSubmodule_toAddSubmonoid

@[simp]
theorem Submodule.toAddSubmonoid_toNatSubmodule (S : Submodule ℕ M) :
    AddSubmonoid.toNatSubmodule S.toAddSubmonoid = S :=
  AddSubmonoid.toNatSubmodule.apply_symm_apply S
#align submodule.to_add_submonoid_to_nat_submodule Submodule.toAddSubmonoid_toNatSubmodule

end NatSubmodule

end AddCommMonoid

section IntSubmodule

variable [AddCommGroup M]

-- Porting note: `S.toIntSubmodule` doesn't work. I used `AddSubgroup.toIntSubmodule S` instead.
/-- An additive subgroup is equivalent to a ℤ-submodule. -/
def AddSubgroup.toIntSubmodule : AddSubgroup M ≃o Submodule ℤ M where
  toFun S := { S with smul_mem' := fun _ _ hs ↦ S.zsmul_mem hs _ }
  invFun := Submodule.toAddSubgroup
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
#align add_subgroup.to_int_submodule AddSubgroup.toIntSubmodule

@[simp]
theorem AddSubgroup.toIntSubmodule_symm :
    ⇑(AddSubgroup.toIntSubmodule.symm : _ ≃o AddSubgroup M) = Submodule.toAddSubgroup :=
  rfl
#align add_subgroup.to_int_submodule_symm AddSubgroup.toIntSubmodule_symm

@[simp]
theorem AddSubgroup.coe_toIntSubmodule (S : AddSubgroup M) :
    (AddSubgroup.toIntSubmodule S : Set M) = S :=
  rfl
#align add_subgroup.coe_to_int_submodule AddSubgroup.coe_toIntSubmodule

@[simp]
theorem AddSubgroup.toIntSubmodule_toAddSubgroup (S : AddSubgroup M) :
    S.toIntSubmodule.toAddSubgroup = S :=
  AddSubgroup.toIntSubmodule.symm_apply_apply S
#align add_subgroup.to_int_submodule_to_add_subgroup AddSubgroup.toIntSubmodule_toAddSubgroup

@[simp]
theorem Submodule.toAddSubgroup_toIntSubmodule (S : Submodule ℤ M) :
    AddSubgroup.toIntSubmodule S.toAddSubgroup = S :=
  AddSubgroup.toIntSubmodule.apply_symm_apply S
#align submodule.to_add_subgroup_to_int_submodule Submodule.toAddSubgroup_toIntSubmodule

end IntSubmodule
