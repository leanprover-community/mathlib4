/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
import Mathlib.Algebra.Module.Equiv
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.PUnitInstances
import Mathlib.Data.Set.Subsingleton

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

universe v

variable {R S M : Type*}

section AddCommMonoid

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
variable [SMul S R] [IsScalarTower S R M]
variable {p q : Submodule R M}

namespace Submodule

/-!
## Bottom element of a submodule
-/

/-- The set `{0}` is the bottom element of the lattice of submodules. -/
instance : Bot (Submodule R M) :=
  ⟨{ (⊥ : AddSubmonoid M) with
      carrier := {0}
      smul_mem' := by simp }⟩

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

@[simp]
lemma bot_toAddSubgroup {R M} [Ring R] [AddCommGroup M] [Module R M] :
    (⊥ : Submodule R M).toAddSubgroup = ⊥ := rfl

variable (R) in
@[simp]
theorem mem_bot {x : M} : x ∈ (⊥ : Submodule R M) ↔ x = 0 :=
  Set.mem_singleton_iff
#align submodule.mem_bot Submodule.mem_bot

instance uniqueBot : Unique (⊥ : Submodule R M) :=
  ⟨inferInstance, fun x ↦ Subtype.ext <| (mem_bot R).1 x.mem⟩
#align submodule.unique_bot Submodule.uniqueBot

instance : OrderBot (Submodule R M) where
  bot := ⊥
  bot_le p x := by simp (config := { contextual := true }) [zero_mem]

protected theorem eq_bot_iff (p : Submodule R M) : p = ⊥ ↔ ∀ x ∈ p, x = (0 : M) :=
  ⟨fun h ↦ h.symm ▸ fun _ hx ↦ (mem_bot R).mp hx,
    fun h ↦ eq_bot_iff.mpr fun x hx ↦ (mem_bot R).mpr (h x hx)⟩
#align submodule.eq_bot_iff Submodule.eq_bot_iff

@[ext high]
protected theorem bot_ext (x y : (⊥ : Submodule R M)) : x = y := by
  rcases x with ⟨x, xm⟩; rcases y with ⟨y, ym⟩; congr
  rw [(Submodule.eq_bot_iff _).mp rfl x xm]
  rw [(Submodule.eq_bot_iff _).mp rfl y ym]
#align submodule.bot_ext Submodule.bot_ext

protected theorem ne_bot_iff (p : Submodule R M) : p ≠ ⊥ ↔ ∃ x ∈ p, x ≠ (0 : M) := by
  simp only [ne_eq, p.eq_bot_iff, not_forall, exists_prop]
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

theorem subsingleton_iff_eq_bot : Subsingleton p ↔ p = ⊥ := by
  rw [subsingleton_iff, Submodule.eq_bot_iff]
  refine ⟨fun h x hx ↦ by simpa using h ⟨x, hx⟩ ⟨0, p.zero_mem⟩,
    fun h ⟨x, hx⟩ ⟨y, hy⟩ ↦ by simp [h x hx, h y hy]⟩

theorem eq_bot_of_subsingleton [Subsingleton p] : p = ⊥ :=
  subsingleton_iff_eq_bot.mp inferInstance
#align submodule.eq_bot_of_subsingleton Submodule.eq_bot_of_subsingleton

theorem nontrivial_iff_ne_bot : Nontrivial p ↔ p ≠ ⊥ := by
  rw [iff_not_comm, not_nontrivial_iff_subsingleton, subsingleton_iff_eq_bot]

/-!
## Top element of a submodule
-/

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
lemma top_toAddSubgroup {R M} [Ring R] [AddCommGroup M] [Module R M] :
    (⊤ : Submodule R M).toAddSubgroup = ⊤ := rfl

@[simp]
theorem mem_top {x : M} : x ∈ (⊤ : Submodule R M) :=
  trivial
#align submodule.mem_top Submodule.mem_top

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

/-!
## Infima & suprema in a submodule
-/

instance : InfSet (Submodule R M) :=
  ⟨fun S ↦
    { carrier := ⋂ s ∈ S, (s : Set M)
      zero_mem' := by simp [zero_mem]
      add_mem' := by simp (config := { contextual := true }) [add_mem]
      smul_mem' := by simp (config := { contextual := true }) [smul_mem] }⟩

private theorem sInf_le' {S : Set (Submodule R M)} {p} : p ∈ S → sInf S ≤ p :=
  Set.biInter_subset_of_mem

private theorem le_sInf' {S : Set (Submodule R M)} {p} : (∀ q ∈ S, p ≤ q) → p ≤ sInf S :=
  Set.subset_iInter₂

instance : Inf (Submodule R M) :=
  ⟨fun p q ↦
    { carrier := p ∩ q
      zero_mem' := by simp [zero_mem]
      add_mem' := by simp (config := { contextual := true }) [add_mem]
      smul_mem' := by simp (config := { contextual := true }) [smul_mem] }⟩

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
  refine s.induction_on ?_ fun i s _ ih ↦ ?_
  · simp
  · rw [Finset.inf_insert, inf_coe, ih]
    simp
#align submodule.finset_inf_coe Submodule.finset_inf_coe

@[simp]
theorem iInf_coe {ι} (p : ι → Submodule R M) : (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i) := by
  rw [iInf, sInf_coe]; simp only [Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq']
#align submodule.infi_coe Submodule.iInf_coe

@[simp]
theorem mem_sInf {S : Set (Submodule R M)} {x : M} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂
#align submodule.mem_Inf Submodule.mem_sInf

@[simp]
theorem mem_iInf {ι} (p : ι → Submodule R M) {x} : (x ∈ ⨅ i, p i) ↔ ∀ i, x ∈ p i := by
  rw [← SetLike.mem_coe, iInf_coe, Set.mem_iInter]; rfl
#align submodule.mem_infi Submodule.mem_iInf

@[simp]
theorem mem_finset_inf {ι} {s : Finset ι} {p : ι → Submodule R M} {x : M} :
    x ∈ s.inf p ↔ ∀ i ∈ s, x ∈ p i := by
  simp only [← SetLike.mem_coe, finset_inf_coe, Set.mem_iInter]
#align submodule.mem_finset_inf Submodule.mem_finset_inf

theorem mem_sup_left {S T : Submodule R M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T := by
  have : S ≤ S ⊔ T := le_sup_left
  rw [LE.le] at this
  exact this
#align submodule.mem_sup_left Submodule.mem_sup_left

theorem mem_sup_right {S T : Submodule R M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T := by
  have : T ≤ S ⊔ T := le_sup_right
  rw [LE.le] at this
  exact this
#align submodule.mem_sup_right Submodule.mem_sup_right

theorem add_mem_sup {S T : Submodule R M} {s t : M} (hs : s ∈ S) (ht : t ∈ T) : s + t ∈ S ⊔ T :=
  add_mem (mem_sup_left hs) (mem_sup_right ht)
#align submodule.add_mem_sup Submodule.add_mem_sup

theorem sub_mem_sup {R' M' : Type*} [Ring R'] [AddCommGroup M'] [Module R' M']
    {S T : Submodule R' M'} {s t : M'} (hs : s ∈ S) (ht : t ∈ T) : s - t ∈ S ⊔ T := by
  rw [sub_eq_add_neg]
  exact add_mem_sup hs (neg_mem ht)
#align submodule.sub_mem_sup Submodule.sub_mem_sup

theorem mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι → Submodule R M} (i : ι) (h : b ∈ p i) :
    b ∈ ⨆ i, p i :=
  (le_iSup p i) h
#align submodule.mem_supr_of_mem Submodule.mem_iSup_of_mem

theorem sum_mem_iSup {ι : Type*} [Fintype ι] {f : ι → M} {p : ι → Submodule R M}
    (h : ∀ i, f i ∈ p i) : (∑ i, f i) ∈ ⨆ i, p i :=
  sum_mem fun i _ ↦ mem_iSup_of_mem i (h i)
#align submodule.sum_mem_supr Submodule.sum_mem_iSup

theorem sum_mem_biSup {ι : Type*} {s : Finset ι} {f : ι → M} {p : ι → Submodule R M}
    (h : ∀ i ∈ s, f i ∈ p i) : (∑ i ∈ s, f i) ∈ ⨆ i ∈ s, p i :=
  sum_mem fun i hi ↦ mem_iSup_of_mem i <| mem_iSup_of_mem hi (h i hi)
#align submodule.sum_mem_bsupr Submodule.sum_mem_biSup

/-! Note that `Submodule.mem_iSup` is provided in `Mathlib/LinearAlgebra/Span.lean`. -/


theorem mem_sSup_of_mem {S : Set (Submodule R M)} {s : Submodule R M} (hs : s ∈ S) :
    ∀ {x : M}, x ∈ s → x ∈ sSup S := by
  have := le_sSup hs
  rw [LE.le] at this
  exact this
#align submodule.mem_Sup_of_mem Submodule.mem_sSup_of_mem

@[simp]
theorem toAddSubmonoid_sSup (s : Set (Submodule R M)) :
    (sSup s).toAddSubmonoid = sSup (toAddSubmonoid '' s) := by
  let p : Submodule R M :=
    { toAddSubmonoid := sSup (toAddSubmonoid '' s)
      smul_mem' := fun t {m} h ↦ by
        simp_rw [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, sSup_eq_iSup'] at h ⊢
        refine AddSubmonoid.iSup_induction'
          (C := fun x _ ↦ t • x ∈ ⨆ p : toAddSubmonoid '' s, (p : AddSubmonoid M)) ?_ ?_
          (fun x y _ _ ↦ ?_) h
        · rintro ⟨-, ⟨p : Submodule R M, hp : p ∈ s, rfl⟩⟩ x (hx : x ∈ p)
          suffices p.toAddSubmonoid ≤ ⨆ q : toAddSubmonoid '' s, (q : AddSubmonoid M) by
            exact this (smul_mem p t hx)
          apply le_sSup
          rw [Subtype.range_coe_subtype]
          exact ⟨p, hp, rfl⟩
        · simpa only [smul_zero] using zero_mem _
        · simp_rw [smul_add]; exact add_mem }
  refine le_antisymm (?_ : sSup s ≤ p) ?_
  · exact sSup_le fun q hq ↦ le_sSup <| Set.mem_image_of_mem toAddSubmonoid hq
  · exact sSup_le fun _ ⟨q, hq, hq'⟩ ↦ hq'.symm ▸ le_sSup hq

variable (R)

@[simp]
theorem subsingleton_iff : Subsingleton (Submodule R M) ↔ Subsingleton M :=
  have h : Subsingleton (Submodule R M) ↔ Subsingleton (AddSubmonoid M) := by
    rw [← subsingleton_iff_bot_eq_top, ← subsingleton_iff_bot_eq_top, ← toAddSubmonoid_eq,
      bot_toAddSubmonoid, top_toAddSubmonoid]
  h.trans AddSubmonoid.subsingleton_iff
#align submodule.subsingleton_iff Submodule.subsingleton_iff

@[simp]
theorem nontrivial_iff : Nontrivial (Submodule R M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| subsingleton_iff R).trans
      not_nontrivial_iff_subsingleton.symm)
#align submodule.nontrivial_iff Submodule.nontrivial_iff

variable {R}

instance [Subsingleton M] : Unique (Submodule R M) :=
  ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ ((subsingleton_iff R).mpr ‹_›) a _⟩

instance unique' [Subsingleton R] : Unique (Submodule R M) := by
  haveI := Module.subsingleton R M; infer_instance
#align submodule.unique' Submodule.unique'

instance [Nontrivial M] : Nontrivial (Submodule R M) :=
  (nontrivial_iff R).mpr ‹_›

/-!
## Disjointness of submodules
-/

theorem disjoint_def {p p' : Submodule R M} : Disjoint p p' ↔ ∀ x ∈ p, x ∈ p' → x = (0 : M) :=
  disjoint_iff_inf_le.trans <| show (∀ x, x ∈ p ∧ x ∈ p' → x ∈ ({0} : Set M)) ↔ _ by simp
#align submodule.disjoint_def Submodule.disjoint_def

theorem disjoint_def' {p p' : Submodule R M} :
    Disjoint p p' ↔ ∀ x ∈ p, ∀ y ∈ p', x = y → x = (0 : M) :=
  disjoint_def.trans
    ⟨fun h x hx _ hy hxy ↦ h x hx <| hxy.symm ▸ hy, fun h x hx hx' ↦ h _ hx x hx' rfl⟩
#align submodule.disjoint_def' Submodule.disjoint_def'

theorem eq_zero_of_coe_mem_of_disjoint (hpq : Disjoint p q) {a : p} (ha : (a : M) ∈ q) : a = 0 :=
  mod_cast disjoint_def.mp hpq a (coe_mem a) ha
#align submodule.eq_zero_of_coe_mem_of_disjoint Submodule.eq_zero_of_coe_mem_of_disjoint

theorem mem_right_iff_eq_zero_of_disjoint {p p' : Submodule R M} (h : Disjoint p p') {x : p} :
    (x : M) ∈ p' ↔ x = 0 :=
  ⟨fun hx => coe_eq_zero.1 <| disjoint_def.1 h x x.2 hx, fun h => h.symm ▸ p'.zero_mem⟩
#align submodule.mem_right_iff_eq_zero_of_disjoint Submodule.mem_right_iff_eq_zero_of_disjoint

theorem mem_left_iff_eq_zero_of_disjoint {p p' : Submodule R M} (h : Disjoint p p') {x : p'} :
    (x : M) ∈ p ↔ x = 0 :=
  ⟨fun hx => coe_eq_zero.1 <| disjoint_def.1 h x hx x.2, fun h => h.symm ▸ p.zero_mem⟩
#align submodule.mem_left_iff_eq_zero_of_disjoint Submodule.mem_left_iff_eq_zero_of_disjoint

end Submodule

section NatSubmodule

/-!
## ℕ-submodules
-/

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

/-!
## ℤ-submodules
-/

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
