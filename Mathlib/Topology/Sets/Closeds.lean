/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import Mathlib.Topology.Sets.Opens

#align_import topology.sets.closeds from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Closed sets

We define a few types of closed sets in a topological space.

## Main Definitions

For a topological space `α`,
* `TopologicalSpace.Closeds α`: The type of closed sets.
* `TopologicalSpace.Clopens α`: The type of clopen sets.
-/


open Order OrderDual Set

variable {ι α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-! ### Closed sets -/


/-- The type of closed subsets of a topological space. -/
structure Closeds (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  closed' : IsClosed carrier
#align topological_space.closeds TopologicalSpace.Closeds

namespace Closeds

instance : SetLike (Closeds α) α where
  coe := Closeds.carrier
  coe_injective' s t h := by cases s; cases t; congr

instance : CanLift (Set α) (Closeds α) (↑) IsClosed where
  prf s hs := ⟨⟨s, hs⟩, rfl⟩

theorem closed (s : Closeds α) : IsClosed (s : Set α) :=
  s.closed'
#align topological_space.closeds.closed TopologicalSpace.Closeds.closed

/-- See Note [custom simps projection]. -/
def Simps.coe (s : Closeds α) : Set α := s

initialize_simps_projections Closeds (carrier → coe, as_prefix coe)

@[ext]
protected theorem ext {s t : Closeds α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align topological_space.closeds.ext TopologicalSpace.Closeds.ext

@[simp]
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl
#align topological_space.closeds.coe_mk TopologicalSpace.Closeds.coe_mk

/-- The closure of a set, as an element of `TopologicalSpace.Closeds`. -/
@[simps]
protected def closure (s : Set α) : Closeds α :=
  ⟨closure s, isClosed_closure⟩
#align topological_space.closeds.closure TopologicalSpace.Closeds.closure

theorem gc : GaloisConnection Closeds.closure ((↑) : Closeds α → Set α) := fun _ U =>
  ⟨subset_closure.trans, fun h => closure_minimal h U.closed⟩
#align topological_space.closeds.gc TopologicalSpace.Closeds.gc

/-- The galois coinsertion between sets and opens. -/
def gi : GaloisInsertion (@Closeds.closure α _) (↑) where
  choice s hs := ⟨s, closure_eq_iff_isClosed.1 <| hs.antisymm subset_closure⟩
  gc := gc
  le_l_u _ := subset_closure
  choice_eq _s hs := SetLike.coe_injective <| subset_closure.antisymm hs
#align topological_space.closeds.gi TopologicalSpace.Closeds.gi

instance completeLattice : CompleteLattice (Closeds α) :=
  CompleteLattice.copy
    (GaloisInsertion.liftCompleteLattice gi)
    -- le
    _ rfl
    -- top
    ⟨univ, isClosed_univ⟩ rfl
    -- bot
    ⟨∅, isClosed_empty⟩ (SetLike.coe_injective closure_empty.symm)
    -- sup
    (fun s t => ⟨s ∪ t, s.2.union t.2⟩)
    (funext fun s => funext fun t => SetLike.coe_injective (s.2.union t.2).closure_eq.symm)
    -- inf
    (fun s t => ⟨s ∩ t, s.2.inter t.2⟩) rfl
    -- sSup
    _ rfl
    -- sInf
    (fun S => ⟨⋂ s ∈ S, ↑s, isClosed_biInter fun s _ => s.2⟩)
    (funext fun _ => SetLike.coe_injective sInf_image.symm)

/-- The type of closed sets is inhabited, with default element the empty set. -/
instance : Inhabited (Closeds α) :=
  ⟨⊥⟩

@[simp, norm_cast]
theorem coe_sup (s t : Closeds α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t := by
  rfl
#align topological_space.closeds.coe_sup TopologicalSpace.Closeds.coe_sup

@[simp, norm_cast]
theorem coe_inf (s t : Closeds α) : (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t :=
  rfl
#align topological_space.closeds.coe_inf TopologicalSpace.Closeds.coe_inf

@[simp, norm_cast]
theorem coe_top : (↑(⊤ : Closeds α) : Set α) = univ :=
  rfl
#align topological_space.closeds.coe_top TopologicalSpace.Closeds.coe_top

@[simp, norm_cast] -- Porting note (#10756): new theorem
theorem coe_eq_univ {s : Closeds α} : (s : Set α) = univ ↔ s = ⊤ :=
  SetLike.coe_injective.eq_iff' rfl

@[simp, norm_cast]
theorem coe_bot : (↑(⊥ : Closeds α) : Set α) = ∅ :=
  rfl
#align topological_space.closeds.coe_bot TopologicalSpace.Closeds.coe_bot

@[simp, norm_cast] -- Porting note (#10756): new theorem
theorem coe_eq_empty {s : Closeds α} : (s : Set α) = ∅ ↔ s = ⊥ :=
  SetLike.coe_injective.eq_iff' rfl

theorem coe_nonempty {s : Closeds α} : (s : Set α).Nonempty ↔ s ≠ ⊥ :=
  nonempty_iff_ne_empty.trans coe_eq_empty.not

@[simp, norm_cast]
theorem coe_sInf {S : Set (Closeds α)} : (↑(sInf S) : Set α) = ⋂ i ∈ S, ↑i :=
  rfl
#align topological_space.closeds.coe_Inf TopologicalSpace.Closeds.coe_sInf

@[simp]
lemma coe_sSup {S : Set (Closeds α)} : ((sSup S : Closeds α) : Set α) =
    closure (⋃₀ ((↑) '' S)) := by rfl

@[simp, norm_cast]
theorem coe_finset_sup (f : ι → Closeds α) (s : Finset ι) :
    (↑(s.sup f) : Set α) = s.sup ((↑) ∘ f) :=
  map_finset_sup (⟨⟨(↑), coe_sup⟩, coe_bot⟩ : SupBotHom (Closeds α) (Set α)) _ _
#align topological_space.closeds.coe_finset_sup TopologicalSpace.Closeds.coe_finset_sup

@[simp, norm_cast]
theorem coe_finset_inf (f : ι → Closeds α) (s : Finset ι) :
    (↑(s.inf f) : Set α) = s.inf ((↑) ∘ f) :=
  map_finset_inf (⟨⟨(↑), coe_inf⟩, coe_top⟩ : InfTopHom (Closeds α) (Set α)) _ _
#align topological_space.closeds.coe_finset_inf TopologicalSpace.Closeds.coe_finset_inf

-- Porting note: Lean 3 proofs didn't work as expected, so I reordered lemmas to fix&golf the proofs

@[simp]
theorem mem_sInf {S : Set (Closeds α)} {x : α} : x ∈ sInf S ↔ ∀ s ∈ S, x ∈ s := mem_iInter₂
#align topological_space.closeds.mem_Inf TopologicalSpace.Closeds.mem_sInf

@[simp]
theorem mem_iInf {ι} {x : α} {s : ι → Closeds α} : x ∈ iInf s ↔ ∀ i, x ∈ s i := by simp [iInf]
#align topological_space.closeds.mem_infi TopologicalSpace.Closeds.mem_iInf

@[simp, norm_cast]
theorem coe_iInf {ι} (s : ι → Closeds α) : ((⨅ i, s i : Closeds α) : Set α) = ⋂ i, s i := by
  ext; simp
#align topological_space.closeds.coe_infi TopologicalSpace.Closeds.coe_iInf

theorem iInf_def {ι} (s : ι → Closeds α) :
    ⨅ i, s i = ⟨⋂ i, s i, isClosed_iInter fun i => (s i).2⟩ := by ext1; simp
#align topological_space.closeds.infi_def TopologicalSpace.Closeds.iInf_def

@[simp]
theorem iInf_mk {ι} (s : ι → Set α) (h : ∀ i, IsClosed (s i)) :
    (⨅ i, ⟨s i, h i⟩ : Closeds α) = ⟨⋂ i, s i, isClosed_iInter h⟩ :=
  iInf_def _
#align topological_space.closeds.infi_mk TopologicalSpace.Closeds.iInf_mk

instance : Coframe (Closeds α) :=
  { inferInstanceAs (CompleteLattice (Closeds α)) with
    sInf := sInf
    iInf_sup_le_sup_sInf := fun a s =>
      (SetLike.coe_injective <| by simp only [coe_sup, coe_iInf, coe_sInf, Set.union_iInter₂]).le }

/-- The term of `TopologicalSpace.Closeds α` corresponding to a singleton. -/
@[simps]
def singleton [T1Space α] (x : α) : Closeds α :=
  ⟨{x}, isClosed_singleton⟩
#align topological_space.closeds.singleton TopologicalSpace.Closeds.singleton

@[simp] lemma mem_singleton [T1Space α] {a b : α} : a ∈ singleton b ↔ a = b := Iff.rfl

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

nonrec theorem Closeds.compl_compl (s : Closeds α) : s.compl.compl = s :=
  Closeds.ext (compl_compl (s : Set α))
#align topological_space.closeds.compl_compl TopologicalSpace.Closeds.compl_compl

nonrec theorem Opens.compl_compl (s : Opens α) : s.compl.compl = s :=
  Opens.ext (compl_compl (s : Set α))
#align topological_space.opens.compl_compl TopologicalSpace.Opens.compl_compl

theorem Closeds.compl_bijective : Function.Bijective (@Closeds.compl α _) :=
  Function.bijective_iff_has_inverse.mpr ⟨Opens.compl, Closeds.compl_compl, Opens.compl_compl⟩
#align topological_space.closeds.compl_bijective TopologicalSpace.Closeds.compl_bijective

theorem Opens.compl_bijective : Function.Bijective (@Opens.compl α _) :=
  Function.bijective_iff_has_inverse.mpr ⟨Closeds.compl, Opens.compl_compl, Closeds.compl_compl⟩
#align topological_space.opens.compl_bijective TopologicalSpace.Opens.compl_bijective

variable (α)

/-- `TopologicalSpace.Closeds.compl` as an `OrderIso` to the order dual of
`TopologicalSpace.Opens α`. -/
@[simps]
def Closeds.complOrderIso : Closeds α ≃o (Opens α)ᵒᵈ where
  toFun := OrderDual.toDual ∘ Closeds.compl
  invFun := Opens.compl ∘ OrderDual.ofDual
  left_inv s := by simp [Closeds.compl_compl]
  right_inv s := by simp [Opens.compl_compl]
  map_rel_iff' := (@OrderDual.toDual_le_toDual (Opens α)).trans compl_subset_compl
#align topological_space.closeds.compl_order_iso TopologicalSpace.Closeds.complOrderIso

/-- `TopologicalSpace.Opens.compl` as an `OrderIso` to the order dual of
`TopologicalSpace.Closeds α`. -/
@[simps]
def Opens.complOrderIso : Opens α ≃o (Closeds α)ᵒᵈ where
  toFun := OrderDual.toDual ∘ Opens.compl
  invFun := Closeds.compl ∘ OrderDual.ofDual
  left_inv s := by simp [Opens.compl_compl]
  right_inv s := by simp [Closeds.compl_compl]
  map_rel_iff' := (@OrderDual.toDual_le_toDual (Closeds α)).trans compl_subset_compl
#align topological_space.opens.compl_order_iso TopologicalSpace.Opens.complOrderIso

variable {α}

lemma Closeds.coe_eq_singleton_of_isAtom [T0Space α] {s : Closeds α} (hs : IsAtom s) :
    ∃ a, (s : Set α) = {a} := by
  refine minimal_nonempty_closed_eq_singleton s.2 (coe_nonempty.2 hs.1) fun t hts ht ht' ↦ ?_
  lift t to Closeds α using ht'
  exact SetLike.coe_injective.eq_iff.2 <| (hs.le_iff_eq <| coe_nonempty.1 ht).1 hts

@[simp, norm_cast] lemma Closeds.isAtom_coe [T1Space α] {s : Closeds α} :
    IsAtom (s : Set α) ↔ IsAtom s :=
  Closeds.gi.isAtom_iff' rfl
    (fun t ht ↦ by obtain ⟨x, rfl⟩ := Set.isAtom_iff.1 ht; exact closure_singleton) s

/-- in a `T1Space`, atoms of `TopologicalSpace.Closeds α` are precisely the
`TopologicalSpace.Closeds.singleton`s. -/
theorem Closeds.isAtom_iff [T1Space α] {s : Closeds α} :
    IsAtom s ↔ ∃ x, s = Closeds.singleton x := by
  simp [← Closeds.isAtom_coe, Set.isAtom_iff, SetLike.ext_iff, Set.ext_iff]
#align topological_space.closeds.is_atom_iff TopologicalSpace.Closeds.isAtom_iff

/-- in a `T1Space`, coatoms of `TopologicalSpace.Opens α` are precisely complements of singletons:
`(TopologicalSpace.Closeds.singleton x).compl`. -/
theorem Opens.isCoatom_iff [T1Space α] {s : Opens α} :
    IsCoatom s ↔ ∃ x, s = (Closeds.singleton x).compl := by
  rw [← s.compl_compl, ← isAtom_dual_iff_isCoatom]
  change IsAtom (Closeds.complOrderIso α s.compl) ↔ _
  simp only [(Closeds.complOrderIso α).isAtom_iff, Closeds.isAtom_iff,
    Closeds.compl_bijective.injective.eq_iff]
#align topological_space.opens.is_coatom_iff TopologicalSpace.Opens.isCoatom_iff

/-! ### Clopen sets -/


/-- The type of clopen sets of a topological space. -/
structure Clopens (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isClopen' : IsClopen carrier
#align topological_space.clopens TopologicalSpace.Clopens

namespace Clopens

instance : SetLike (Clopens α) α where
  coe s := s.carrier
  coe_injective' s t h := by cases s; cases t; congr

theorem isClopen (s : Clopens α) : IsClopen (s : Set α) :=
  s.isClopen'
#align topological_space.clopens.clopen TopologicalSpace.Clopens.isClopen

/-- See Note [custom simps projection]. -/
def Simps.coe (s : Clopens α) : Set α := s

initialize_simps_projections Clopens (carrier → coe)

/-- Reinterpret a clopen as an open. -/
@[simps]
def toOpens (s : Clopens α) : Opens α :=
  ⟨s, s.isClopen.isOpen⟩
#align topological_space.clopens.to_opens TopologicalSpace.Clopens.toOpens

@[ext]
protected theorem ext {s t : Clopens α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align topological_space.clopens.ext TopologicalSpace.Clopens.ext

@[simp]
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl
#align topological_space.clopens.coe_mk TopologicalSpace.Clopens.coe_mk

@[simp] lemma mem_mk {s : Set α} {x h} : x ∈ mk s h ↔ x ∈ s := .rfl

instance : Sup (Clopens α) := ⟨fun s t => ⟨s ∪ t, s.isClopen.union t.isClopen⟩⟩
instance : Inf (Clopens α) := ⟨fun s t => ⟨s ∩ t, s.isClopen.inter t.isClopen⟩⟩
instance : Top (Clopens α) := ⟨⟨⊤, isClopen_univ⟩⟩
instance : Bot (Clopens α) := ⟨⟨⊥, isClopen_empty⟩⟩
instance : SDiff (Clopens α) := ⟨fun s t => ⟨s \ t, s.isClopen.diff t.isClopen⟩⟩
instance : HasCompl (Clopens α) := ⟨fun s => ⟨sᶜ, s.isClopen.compl⟩⟩

instance : BooleanAlgebra (Clopens α) :=
  SetLike.coe_injective.booleanAlgebra _ (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (fun _ => rfl)
    fun _ _ => rfl

@[simp] theorem coe_sup (s t : Clopens α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t := rfl
#align topological_space.clopens.coe_sup TopologicalSpace.Clopens.coe_sup

@[simp] theorem coe_inf (s t : Clopens α) : (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t := rfl
#align topological_space.clopens.coe_inf TopologicalSpace.Clopens.coe_inf

@[simp] theorem coe_top : (↑(⊤ : Clopens α) : Set α) = univ := rfl
#align topological_space.clopens.coe_top TopologicalSpace.Clopens.coe_top

@[simp] theorem coe_bot : (↑(⊥ : Clopens α) : Set α) = ∅ := rfl
#align topological_space.clopens.coe_bot TopologicalSpace.Clopens.coe_bot

@[simp] theorem coe_sdiff (s t : Clopens α) : (↑(s \ t) : Set α) = ↑s \ ↑t := rfl
#align topological_space.clopens.coe_sdiff TopologicalSpace.Clopens.coe_sdiff

@[simp] theorem coe_compl (s : Clopens α) : (↑sᶜ : Set α) = (↑s)ᶜ := rfl
#align topological_space.clopens.coe_compl TopologicalSpace.Clopens.coe_compl

instance : Inhabited (Clopens α) := ⟨⊥⟩

variable [TopologicalSpace β]

instance : SProd (Clopens α) (Clopens β) (Clopens (α × β)) where
  sprod s t := ⟨s ×ˢ t, s.2.prod t.2⟩

@[simp]
protected lemma mem_prod {s : Clopens α} {t : Clopens β} {x : α × β} :
    x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t := .rfl

end Clopens

end TopologicalSpace
