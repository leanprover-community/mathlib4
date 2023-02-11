/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies

! This file was ported from Lean 3 source module topology.sets.closeds
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Sets.Opens

/-!
# Closed sets

We define a few types of closed sets in a topological space.

## Main Definitions

For a topological space `α`,
* `closeds α`: The type of closed sets.
* `clopens α`: The type of clopen sets.
-/


open Order OrderDual Set

variable {ι α β : Type _} [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-! ### Closed sets -/


/-- The type of closed subsets of a topological space. -/
structure Closeds (α : Type _) [TopologicalSpace α] where
  carrier : Set α
  closed' : IsClosed carrier
#align topological_space.closeds TopologicalSpace.Closeds

namespace Closeds

variable {α}

instance : SetLike (Closeds α) α where
  coe := Closeds.carrier
  coe_injective' s t h := by
    cases s
    cases t
    congr

theorem closed (s : Closeds α) : IsClosed (s : Set α) :=
  s.closed'
#align topological_space.closeds.closed TopologicalSpace.Closeds.closed

@[ext]
protected theorem ext {s t : Closeds α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align topological_space.closeds.ext TopologicalSpace.Closeds.ext

@[simp]
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl
#align topological_space.closeds.coe_mk TopologicalSpace.Closeds.coe_mk

/-- The closure of a set, as an element of `closeds`. -/
protected def closure (s : Set α) : Closeds α :=
  ⟨closure s, isClosed_closure⟩
#align topological_space.closeds.closure TopologicalSpace.Closeds.closure

theorem gc : GaloisConnection Closeds.closure (coe : Closeds α → Set α) := fun s U =>
  ⟨subset_closure.trans, fun h => closure_minimal h U.closed⟩
#align topological_space.closeds.gc TopologicalSpace.Closeds.gc

/-- The galois coinsertion between sets and opens. -/
def gi : GaloisInsertion (@Closeds.closure α _) coe
    where
  choice s hs := ⟨s, closure_eq_iff_isClosed.1 <| hs.antisymm subset_closure⟩
  gc := gc
  le_l_u _ := subset_closure
  choice_eq s hs := SetLike.coe_injective <| subset_closure.antisymm hs
#align topological_space.closeds.gi TopologicalSpace.Closeds.gi

instance : CompleteLattice (Closeds α) :=
  CompleteLattice.copy
    (GaloisInsertion.liftCompleteLattice gi)-- le
    _
    rfl-- top
    ⟨univ, isClosed_univ⟩
    rfl-- bot
    ⟨∅, isClosed_empty⟩
    (SetLike.coe_injective closure_empty.symm)
    (-- sup
    fun s t => ⟨s ∪ t, s.2.union t.2⟩)
    (funext fun s => funext fun t => SetLike.coe_injective (s.2.union t.2).closure_eq.symm)
    (-- inf
    fun s t => ⟨s ∩ t, s.2.inter t.2⟩)
    rfl-- Sup
    _
    rfl
    (-- Inf
    fun S => ⟨⋂ s ∈ S, ↑s, isClosed_binterᵢ fun s _ => s.2⟩)
    (funext fun S => SetLike.coe_injective infₛ_image.symm)

/-- The type of closed sets is inhabited, with default element the empty set. -/
instance : Inhabited (Closeds α) :=
  ⟨⊥⟩

@[simp, norm_cast]
theorem coe_sup (s t : Closeds α) : (↑(s ⊔ t) : Set α) = s ∪ t :=
  rfl
#align topological_space.closeds.coe_sup TopologicalSpace.Closeds.coe_sup

@[simp, norm_cast]
theorem coe_inf (s t : Closeds α) : (↑(s ⊓ t) : Set α) = s ∩ t :=
  rfl
#align topological_space.closeds.coe_inf TopologicalSpace.Closeds.coe_inf

@[simp, norm_cast]
theorem coe_top : (↑(⊤ : Closeds α) : Set α) = univ :=
  rfl
#align topological_space.closeds.coe_top TopologicalSpace.Closeds.coe_top

@[simp, norm_cast]
theorem coe_bot : (↑(⊥ : Closeds α) : Set α) = ∅ :=
  rfl
#align topological_space.closeds.coe_bot TopologicalSpace.Closeds.coe_bot

@[simp, norm_cast]
theorem coe_infₛ {S : Set (Closeds α)} : (↑(infₛ S) : Set α) = ⋂ i ∈ S, ↑i :=
  rfl
#align topological_space.closeds.coe_Inf TopologicalSpace.Closeds.coe_infₛ

@[simp, norm_cast]
theorem coe_finset_sup (f : ι → Closeds α) (s : Finset ι) :
    (↑(s.sup f) : Set α) = s.sup (coe ∘ f) :=
  map_finset_sup (⟨⟨coe, coe_sup⟩, coe_bot⟩ : SupBotHom (Closeds α) (Set α)) _ _
#align topological_space.closeds.coe_finset_sup TopologicalSpace.Closeds.coe_finset_sup

@[simp, norm_cast]
theorem coe_finset_inf (f : ι → Closeds α) (s : Finset ι) :
    (↑(s.inf f) : Set α) = s.inf (coe ∘ f) :=
  map_finset_inf (⟨⟨coe, coe_inf⟩, coe_top⟩ : InfTopHom (Closeds α) (Set α)) _ _
#align topological_space.closeds.coe_finset_inf TopologicalSpace.Closeds.coe_finset_inf

theorem infᵢ_def {ι} (s : ι → Closeds α) :
    (⨅ i, s i) = ⟨⋂ i, s i, isClosed_interᵢ fun i => (s i).2⟩ :=
  by
  ext
  simp only [infᵢ, coe_Inf, bInter_range]
  rfl
#align topological_space.closeds.infi_def TopologicalSpace.Closeds.infᵢ_def

@[simp]
theorem infᵢ_mk {ι} (s : ι → Set α) (h : ∀ i, IsClosed (s i)) :
    (⨅ i, ⟨s i, h i⟩ : Closeds α) = ⟨⋂ i, s i, isClosed_interᵢ h⟩ := by simp [infi_def]
#align topological_space.closeds.infi_mk TopologicalSpace.Closeds.infᵢ_mk

@[simp, norm_cast]
theorem coe_infᵢ {ι} (s : ι → Closeds α) : ((⨅ i, s i : Closeds α) : Set α) = ⋂ i, s i := by
  simp [infi_def]
#align topological_space.closeds.coe_infi TopologicalSpace.Closeds.coe_infᵢ

@[simp]
theorem mem_infᵢ {ι} {x : α} {s : ι → Closeds α} : x ∈ infᵢ s ↔ ∀ i, x ∈ s i := by
  simp [← SetLike.mem_coe]
#align topological_space.closeds.mem_infi TopologicalSpace.Closeds.mem_infᵢ

@[simp]
theorem mem_infₛ {S : Set (Closeds α)} {x : α} : x ∈ infₛ S ↔ ∀ s ∈ S, x ∈ s := by
  simp_rw [infₛ_eq_infᵢ, mem_infi]
#align topological_space.closeds.mem_Inf TopologicalSpace.Closeds.mem_infₛ

instance : Coframe (Closeds α) :=
  { Closeds.completeLattice with
    infₛ := infₛ
    infᵢ_sup_le_sup_inf := fun a s =>
      (SetLike.coe_injective <| by simp only [coe_sup, coe_infi, coe_Inf, Set.union_interᵢ₂]).le }

/-- The term of `closeds α` corresponding to a singleton. -/
@[simps]
def singleton [T1Space α] (x : α) : Closeds α :=
  ⟨{x}, isClosed_singleton⟩
#align topological_space.closeds.singleton TopologicalSpace.Closeds.singleton

end Closeds

/-- The complement of a closed set as an open set. -/
@[simps]
def Closeds.compl (s : Closeds α) : Opens α :=
  ⟨sᶜ, s.2.isOpen_compl⟩
#align topological_space.closeds.compl TopologicalSpace.Closeds.compl

/-- The complement of an open set as a closed set. -/
@[simps]
def Opens.compl (s : Opens α) : Closeds α :=
  ⟨sᶜ, s.2.isClosed_compl⟩
#align topological_space.opens.compl TopologicalSpace.Opens.compl

theorem Closeds.compl_compl (s : Closeds α) : s.compl.compl = s :=
  Closeds.ext (compl_compl s)
#align topological_space.closeds.compl_compl TopologicalSpace.Closeds.compl_compl

theorem Opens.compl_compl (s : Opens α) : s.compl.compl = s :=
  Opens.ext (compl_compl s)
#align topological_space.opens.compl_compl TopologicalSpace.Opens.compl_compl

theorem Closeds.compl_bijective : Function.Bijective (@Closeds.compl α _) :=
  Function.bijective_iff_has_inverse.mpr ⟨Opens.compl, Closeds.compl_compl, Opens.compl_compl⟩
#align topological_space.closeds.compl_bijective TopologicalSpace.Closeds.compl_bijective

theorem Opens.compl_bijective : Function.Bijective (@Opens.compl α _) :=
  Function.bijective_iff_has_inverse.mpr ⟨Closeds.compl, Opens.compl_compl, Closeds.compl_compl⟩
#align topological_space.opens.compl_bijective TopologicalSpace.Opens.compl_bijective

variable (α)

/-- `closeds.compl` as an `order_iso` to the order dual of `opens α`. -/
@[simps]
def Closeds.complOrderIso : Closeds α ≃o (Opens α)ᵒᵈ
    where
  toFun := OrderDual.toDual ∘ Closeds.compl
  invFun := Opens.compl ∘ OrderDual.ofDual
  left_inv s := by simp [closeds.compl_compl]
  right_inv s := by simp [opens.compl_compl]
  map_rel_iff' s t := by
    simpa only [Equiv.coe_fn_mk, Function.comp_apply, OrderDual.toDual_le_toDual] using
      compl_subset_compl
#align topological_space.closeds.compl_order_iso TopologicalSpace.Closeds.complOrderIso

/-- `opens.compl` as an `order_iso` to the order dual of `closeds α`. -/
@[simps]
def Opens.complOrderIso : Opens α ≃o (Closeds α)ᵒᵈ
    where
  toFun := OrderDual.toDual ∘ Opens.compl
  invFun := Closeds.compl ∘ OrderDual.ofDual
  left_inv s := by simp [opens.compl_compl]
  right_inv s := by simp [closeds.compl_compl]
  map_rel_iff' s t := by
    simpa only [Equiv.coe_fn_mk, Function.comp_apply, OrderDual.toDual_le_toDual] using
      compl_subset_compl
#align topological_space.opens.compl_order_iso TopologicalSpace.Opens.complOrderIso

variable {α}

/-- in a `t1_space`, atoms of `closeds α` are precisely the `closeds.singleton`s. -/
theorem Closeds.isAtom_iff [T1Space α] {s : Closeds α} : IsAtom s ↔ ∃ x, s = Closeds.singleton x :=
  by
  have : IsAtom (s : Set α) ↔ IsAtom s :=
    by
    refine' closeds.gi.is_atom_iff' rfl (fun t ht => _) s
    obtain ⟨x, rfl⟩ := t.is_atom_iff.mp ht
    exact closure_singleton
  simpa only [← this, (s : Set α).isAtom_iff, SetLike.ext_iff, Set.ext_iff]
#align topological_space.closeds.is_atom_iff TopologicalSpace.Closeds.isAtom_iff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr∃ , »((x), _)]] -/
/-- in a `t1_space`, coatoms of `opens α` are precisely complements of singletons:
`(closeds.singleton x).compl`. -/
theorem Opens.isCoatom_iff [T1Space α] {s : Opens α} :
    IsCoatom s ↔ ∃ x, s = (Closeds.singleton x).compl :=
  by
  rw [← s.compl_compl, ← isAtom_dual_iff_isCoatom]
  change IsAtom (closeds.compl_order_iso α s.compl) ↔ _
  rw [(closeds.compl_order_iso α).isAtom_iff, closeds.is_atom_iff]
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr∃ , »((x), _)]]"
  exact closeds.compl_bijective.injective.eq_iff.symm
#align topological_space.opens.is_coatom_iff TopologicalSpace.Opens.isCoatom_iff

/-! ### Clopen sets -/


/-- The type of clopen sets of a topological space. -/
structure Clopens (α : Type _) [TopologicalSpace α] where
  carrier : Set α
  clopen' : IsClopen carrier
#align topological_space.clopens TopologicalSpace.Clopens

namespace Clopens

instance : SetLike (Clopens α) α where
  coe s := s.carrier
  coe_injective' s t h := by
    cases s
    cases t
    congr

theorem clopen (s : Clopens α) : IsClopen (s : Set α) :=
  s.clopen'
#align topological_space.clopens.clopen TopologicalSpace.Clopens.clopen

/-- Reinterpret a compact open as an open. -/
@[simps]
def toOpens (s : Clopens α) : Opens α :=
  ⟨s, s.clopen.IsOpen⟩
#align topological_space.clopens.to_opens TopologicalSpace.Clopens.toOpens

@[ext]
protected theorem ext {s t : Clopens α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align topological_space.clopens.ext TopologicalSpace.Clopens.ext

@[simp]
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl
#align topological_space.clopens.coe_mk TopologicalSpace.Clopens.coe_mk

instance : HasSup (Clopens α) :=
  ⟨fun s t => ⟨s ∪ t, s.clopen.union t.clopen⟩⟩

instance : HasInf (Clopens α) :=
  ⟨fun s t => ⟨s ∩ t, s.clopen.inter t.clopen⟩⟩

instance : Top (Clopens α) :=
  ⟨⟨⊤, isClopen_univ⟩⟩

instance : Bot (Clopens α) :=
  ⟨⟨⊥, isClopen_empty⟩⟩

instance : SDiff (Clopens α) :=
  ⟨fun s t => ⟨s \ t, s.clopen.diffₓ t.clopen⟩⟩

instance : HasCompl (Clopens α) :=
  ⟨fun s => ⟨sᶜ, s.clopen.compl⟩⟩

instance : BooleanAlgebra (Clopens α) :=
  SetLike.coe_injective.BooleanAlgebra _ (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (fun _ => rfl)
    fun _ _ => rfl

@[simp]
theorem coe_sup (s t : Clopens α) : (↑(s ⊔ t) : Set α) = s ∪ t :=
  rfl
#align topological_space.clopens.coe_sup TopologicalSpace.Clopens.coe_sup

@[simp]
theorem coe_inf (s t : Clopens α) : (↑(s ⊓ t) : Set α) = s ∩ t :=
  rfl
#align topological_space.clopens.coe_inf TopologicalSpace.Clopens.coe_inf

@[simp]
theorem coe_top : (↑(⊤ : Clopens α) : Set α) = univ :=
  rfl
#align topological_space.clopens.coe_top TopologicalSpace.Clopens.coe_top

@[simp]
theorem coe_bot : (↑(⊥ : Clopens α) : Set α) = ∅ :=
  rfl
#align topological_space.clopens.coe_bot TopologicalSpace.Clopens.coe_bot

@[simp]
theorem coe_sdiff (s t : Clopens α) : (↑(s \ t) : Set α) = s \ t :=
  rfl
#align topological_space.clopens.coe_sdiff TopologicalSpace.Clopens.coe_sdiff

@[simp]
theorem coe_compl (s : Clopens α) : (↑(sᶜ) : Set α) = sᶜ :=
  rfl
#align topological_space.clopens.coe_compl TopologicalSpace.Clopens.coe_compl

instance : Inhabited (Clopens α) :=
  ⟨⊥⟩

end Clopens

end TopologicalSpace

