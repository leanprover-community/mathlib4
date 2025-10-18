/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Clopen

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
  isClosed' : IsClosed carrier

namespace Closeds

instance : SetLike (Closeds α) α where
  coe := Closeds.carrier
  coe_injective' s t h := by cases s; cases t; congr

instance : CanLift (Set α) (Closeds α) (↑) IsClosed where
  prf s hs := ⟨⟨s, hs⟩, rfl⟩

theorem isClosed (s : Closeds α) : IsClosed (s : Set α) :=
  s.isClosed'

@[deprecated (since := "2025-04-20")] alias closed := isClosed

/-- See Note [custom simps projection]. -/
def Simps.coe (s : Closeds α) : Set α := s

initialize_simps_projections Closeds (carrier → coe, as_prefix coe)

@[simp]
lemma carrier_eq_coe (s : Closeds α) : s.carrier = (s : Set α) := rfl

@[ext]
protected theorem ext {s t : Closeds α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl

@[simp]
lemma mem_mk {s : Set α} {hs : IsClosed s} {x : α} : x ∈ (⟨s, hs⟩ : Closeds α) ↔ x ∈ s :=
  .rfl

/-- The closure of a set, as an element of `TopologicalSpace.Closeds`. -/
@[simps]
protected def closure (s : Set α) : Closeds α :=
  ⟨closure s, isClosed_closure⟩

@[simp]
theorem mem_closure {s : Set α} {x : α} : x ∈ Closeds.closure s ↔ x ∈ closure s := .rfl

theorem gc : GaloisConnection Closeds.closure ((↑) : Closeds α → Set α) := fun _ U =>
  ⟨subset_closure.trans, fun h => closure_minimal h U.isClosed⟩

@[simp]
lemma closure_le {s : Set α} {t : Closeds α} : .closure s ≤ t ↔ s ⊆ t :=
  t.isClosed.closure_subset_iff

/-- The Galois insertion between sets and closeds. -/
def gi : GaloisInsertion (@Closeds.closure α _) (↑) where
  choice s hs := ⟨s, closure_eq_iff_isClosed.1 <| hs.antisymm subset_closure⟩
  gc := gc
  le_l_u _ := subset_closure
  choice_eq _s hs := SetLike.coe_injective <| subset_closure.antisymm hs

instance instCompleteLattice : CompleteLattice (Closeds α) :=
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
theorem coe_sup (s t : Closeds α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t := rfl

@[simp, norm_cast]
theorem coe_inf (s t : Closeds α) : (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t :=
  rfl

@[simp, norm_cast]
theorem coe_top : (↑(⊤ : Closeds α) : Set α) = univ :=
  rfl

@[simp, norm_cast]
theorem coe_eq_univ {s : Closeds α} : (s : Set α) = univ ↔ s = ⊤ :=
  SetLike.coe_injective.eq_iff' rfl

@[simp, norm_cast]
theorem coe_bot : (↑(⊥ : Closeds α) : Set α) = ∅ :=
  rfl

@[simp, norm_cast]
theorem coe_eq_empty {s : Closeds α} : (s : Set α) = ∅ ↔ s = ⊥ :=
  SetLike.coe_injective.eq_iff' rfl

theorem coe_nonempty {s : Closeds α} : (s : Set α).Nonempty ↔ s ≠ ⊥ :=
  nonempty_iff_ne_empty.trans coe_eq_empty.not

@[simp, norm_cast]
theorem coe_sInf {S : Set (Closeds α)} : (↑(sInf S) : Set α) = ⋂ i ∈ S, ↑i :=
  rfl

@[simp]
lemma coe_sSup {S : Set (Closeds α)} : ((sSup S : Closeds α) : Set α) =
    closure (⋃₀ ((↑) '' S)) := rfl

@[simp, norm_cast]
theorem coe_finset_sup (f : ι → Closeds α) (s : Finset ι) :
    (↑(s.sup f) : Set α) = s.sup ((↑) ∘ f) :=
  map_finset_sup (⟨⟨(↑), coe_sup⟩, coe_bot⟩ : SupBotHom (Closeds α) (Set α)) _ _

@[simp, norm_cast]
theorem coe_finset_inf (f : ι → Closeds α) (s : Finset ι) :
    (↑(s.inf f) : Set α) = s.inf ((↑) ∘ f) :=
  map_finset_inf (⟨⟨(↑), coe_inf⟩, coe_top⟩ : InfTopHom (Closeds α) (Set α)) _ _

@[simp]
theorem mem_sInf {S : Set (Closeds α)} {x : α} : x ∈ sInf S ↔ ∀ s ∈ S, x ∈ s := mem_iInter₂

@[simp]
theorem mem_iInf {ι} {x : α} {s : ι → Closeds α} : x ∈ iInf s ↔ ∀ i, x ∈ s i := by simp [iInf]

@[simp, norm_cast]
theorem coe_iInf {ι} (s : ι → Closeds α) : ((⨅ i, s i : Closeds α) : Set α) = ⋂ i, s i := by
  ext; simp

theorem iInf_def {ι} (s : ι → Closeds α) :
    ⨅ i, s i = ⟨⋂ i, s i, isClosed_iInter fun i => (s i).2⟩ := by ext1; simp

@[simp]
theorem iInf_mk {ι} (s : ι → Set α) (h : ∀ i, IsClosed (s i)) :
    (⨅ i, ⟨s i, h i⟩ : Closeds α) = ⟨⋂ i, s i, isClosed_iInter h⟩ :=
  iInf_def _

/-- Closed sets in a topological space form a coframe. -/
def coframeMinimalAxioms : Coframe.MinimalAxioms (Closeds α) where
  iInf_sup_le_sup_sInf a s :=
    (SetLike.coe_injective <| by simp only [coe_sup, coe_iInf, coe_sInf, Set.union_iInter₂]).le

instance instCoframe : Coframe (Closeds α) := .ofMinimalAxioms coframeMinimalAxioms

/-- The term of `TopologicalSpace.Closeds α` corresponding to a singleton. -/
@[simps]
def singleton [T1Space α] (x : α) : Closeds α :=
  ⟨{x}, isClosed_singleton⟩

@[simp] lemma mem_singleton [T1Space α] {a b : α} : a ∈ singleton b ↔ a = b := Iff.rfl

/-- The preimage of a closed set under a continuous map. -/
@[simps]
def preimage (s : Closeds β) {f : α → β} (hf : Continuous f) : Closeds α :=
  ⟨f ⁻¹' s, s.isClosed.preimage hf⟩

end Closeds

/-- The complement of a closed set as an open set. -/
@[simps]
def Closeds.compl (s : Closeds α) : Opens α :=
  ⟨sᶜ, s.2.isOpen_compl⟩

/-- The complement of an open set as a closed set. -/
@[simps]
def Opens.compl (s : Opens α) : Closeds α :=
  ⟨sᶜ, s.2.isClosed_compl⟩

nonrec theorem Closeds.compl_compl (s : Closeds α) : s.compl.compl = s :=
  Closeds.ext (compl_compl (s : Set α))

nonrec theorem Opens.compl_compl (s : Opens α) : s.compl.compl = s :=
  Opens.ext (compl_compl (s : Set α))

theorem Closeds.compl_bijective : Function.Bijective (@Closeds.compl α _) :=
  Function.bijective_iff_has_inverse.mpr ⟨Opens.compl, Closeds.compl_compl, Opens.compl_compl⟩

theorem Opens.compl_bijective : Function.Bijective (@Opens.compl α _) :=
  Function.bijective_iff_has_inverse.mpr ⟨Closeds.compl, Opens.compl_compl, Closeds.compl_compl⟩

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

/-- `TopologicalSpace.Opens.compl` as an `OrderIso` to the order dual of
`TopologicalSpace.Closeds α`. -/
@[simps]
def Opens.complOrderIso : Opens α ≃o (Closeds α)ᵒᵈ where
  toFun := OrderDual.toDual ∘ Opens.compl
  invFun := Closeds.compl ∘ OrderDual.ofDual
  left_inv s := by simp [Opens.compl_compl]
  right_inv s := by simp [Closeds.compl_compl]
  map_rel_iff' := (@OrderDual.toDual_le_toDual (Closeds α)).trans compl_subset_compl

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

/-- in a `T1Space`, coatoms of `TopologicalSpace.Opens α` are precisely complements of singletons:
`(TopologicalSpace.Closeds.singleton x).compl`. -/
theorem Opens.isCoatom_iff [T1Space α] {s : Opens α} :
    IsCoatom s ↔ ∃ x, s = (Closeds.singleton x).compl := by
  rw [← s.compl_compl, ← isAtom_dual_iff_isCoatom]
  change IsAtom (Closeds.complOrderIso α s.compl) ↔ _
  simp only [(Closeds.complOrderIso α).isAtom_iff, Closeds.isAtom_iff,
    Closeds.compl_bijective.injective.eq_iff]

/-! ### Clopen sets -/


/-- The type of clopen sets of a topological space. -/
structure Clopens (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isClopen' : IsClopen carrier

namespace Clopens

instance : SetLike (Clopens α) α where
  coe s := s.carrier
  coe_injective' s t h := by cases s; cases t; congr

theorem isClopen (s : Clopens α) : IsClopen (s : Set α) :=
  s.isClopen'

lemma isOpen (s : Clopens α) : IsOpen (s : Set α) := s.isClopen.isOpen

lemma isClosed (s : Clopens α) : IsClosed (s : Set α) := s.isClopen.isClosed

/-- See Note [custom simps projection]. -/
def Simps.coe (s : Clopens α) : Set α := s

initialize_simps_projections Clopens (carrier → coe, as_prefix coe)

/-- Reinterpret a clopen as an open. -/
@[simps] def toOpens (s : Clopens α) : Opens α := ⟨s, s.isOpen⟩

/-- Reinterpret a clopen as a closed. -/
@[simps] def toCloseds (s : Clopens α) : Closeds α := ⟨s, s.isClosed⟩

@[ext]
protected theorem ext {s t : Clopens α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl

@[simp] lemma mem_mk {s : Set α} {x h} : x ∈ mk s h ↔ x ∈ s := .rfl

instance : Max (Clopens α) := ⟨fun s t => ⟨s ∪ t, s.isClopen.union t.isClopen⟩⟩
instance : Min (Clopens α) := ⟨fun s t => ⟨s ∩ t, s.isClopen.inter t.isClopen⟩⟩
instance : Top (Clopens α) := ⟨⟨⊤, isClopen_univ⟩⟩
instance : Bot (Clopens α) := ⟨⟨⊥, isClopen_empty⟩⟩
instance : SDiff (Clopens α) := ⟨fun s t => ⟨s \ t, s.isClopen.diff t.isClopen⟩⟩
instance : HImp (Clopens α) where himp s t := ⟨s ⇨ t, s.isClopen.himp t.isClopen⟩
instance : HasCompl (Clopens α) := ⟨fun s => ⟨sᶜ, s.isClopen.compl⟩⟩

@[simp, norm_cast] lemma coe_sup (s t : Clopens α) : ↑(s ⊔ t) = (s ∪ t : Set α) := rfl
@[simp, norm_cast] lemma coe_inf (s t : Clopens α) : ↑(s ⊓ t) = (s ∩ t : Set α) := rfl
@[simp, norm_cast] lemma coe_top : (↑(⊤ : Clopens α) : Set α) = univ := rfl
@[simp, norm_cast] lemma coe_bot : (↑(⊥ : Clopens α) : Set α) = ∅ := rfl
@[simp, norm_cast] lemma coe_sdiff (s t : Clopens α) : ↑(s \ t) = (s \ t : Set α) := rfl
@[simp, norm_cast] lemma coe_himp (s t : Clopens α) : ↑(s ⇨ t) = (s ⇨ t : Set α) := rfl
@[simp, norm_cast] lemma coe_compl (s : Clopens α) : (↑sᶜ : Set α) = (↑s)ᶜ := rfl

instance : BooleanAlgebra (Clopens α) :=
  SetLike.coe_injective.booleanAlgebra _ coe_sup coe_inf coe_top coe_bot coe_compl coe_sdiff
    coe_himp

instance : Inhabited (Clopens α) := ⟨⊥⟩

instance : SProd (Clopens α) (Clopens β) (Clopens (α × β)) where
  sprod s t := ⟨s ×ˢ t, s.2.prod t.2⟩

@[simp]
protected lemma mem_prod {s : Clopens α} {t : Clopens β} {x : α × β} :
    x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t := .rfl

@[simp]
lemma coe_finset_sup (s : Finset ι) (U : ι → Clopens α) :
    (↑(s.sup U) : Set α) = ⋃ i ∈ s, U i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ _ IH => simp [IH]

@[simp, norm_cast]
lemma coe_disjoint {s t : Clopens α} : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, ← SetLike.coe_set_eq]

end Clopens

/-! ### Irreducible closed sets -/

/-- The type of irreducible closed subsets of a topological space. -/
structure IrreducibleCloseds (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isIrreducible' : IsIrreducible carrier
  isClosed' : IsClosed carrier

namespace IrreducibleCloseds

instance : SetLike (IrreducibleCloseds α) α where
  coe := IrreducibleCloseds.carrier
  coe_injective' s t h := by cases s; cases t; congr

instance : CanLift (Set α) (IrreducibleCloseds α) (↑) (fun s ↦ IsIrreducible s ∧ IsClosed s) where
  prf s hs := ⟨⟨s, hs.1, hs.2⟩, rfl⟩

theorem isIrreducible (s : IrreducibleCloseds α) : IsIrreducible (s : Set α) := s.isIrreducible'

@[deprecated (since := "2025-10-14")] alias is_irreducible' := isIrreducible

theorem isClosed (s : IrreducibleCloseds α) : IsClosed (s : Set α) := s.isClosed'

@[deprecated (since := "2025-10-14")] alias is_closed' := isClosed

/-- See Note [custom simps projection]. -/
def Simps.coe (s : IrreducibleCloseds α) : Set α := s

initialize_simps_projections IrreducibleCloseds (carrier → coe, as_prefix coe)

@[ext]
protected theorem ext {s t : IrreducibleCloseds α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Set α) (h : IsIrreducible s) (h' : IsClosed s) : (mk s h h' : Set α) = s :=
  rfl

/-- The term of `TopologicalSpace.IrreducibleCloseds α` corresponding to a singleton. -/
@[simps]
def singleton [T1Space α] (x : α) : IrreducibleCloseds α :=
  ⟨{x}, isIrreducible_singleton, isClosed_singleton⟩

@[simp] lemma mem_singleton [T1Space α] {a b : α} : a ∈ singleton b ↔ a = b := Iff.rfl

/--
The equivalence between `IrreducibleCloseds α` and `{x : Set α // IsIrreducible x ∧ IsClosed x }`.
-/
@[simps apply symm_apply]
def equivSubtype : IrreducibleCloseds α ≃ { x : Set α // IsIrreducible x ∧ IsClosed x } where
  toFun a   := ⟨a.1, a.2, a.3⟩
  invFun a  := ⟨a.1, a.2.1, a.2.2⟩

/--
The equivalence between `IrreducibleCloseds α` and `{x : Set α // IsClosed x ∧ IsIrreducible x }`.
-/
@[simps apply symm_apply]
def equivSubtype' : IrreducibleCloseds α ≃ { x : Set α // IsClosed x ∧ IsIrreducible x } where
  toFun a   := ⟨a.1, a.3, a.2⟩
  invFun a  := ⟨a.1, a.2.2, a.2.1⟩

variable (α) in
/-- The equivalence `IrreducibleCloseds α ≃ { x : Set α // IsIrreducible x ∧ IsClosed x }` is an
order isomorphism. -/
def orderIsoSubtype : IrreducibleCloseds α ≃o { x : Set α // IsIrreducible x ∧ IsClosed x } :=
  equivSubtype.toOrderIso (fun _ _ h ↦ h) (fun _ _ h ↦ h)

variable (α) in
/-- The equivalence `IrreducibleCloseds α ≃ { x : Set α // IsClosed x ∧ IsIrreducible x }` is an
order isomorphism. -/
def orderIsoSubtype' : IrreducibleCloseds α ≃o { x : Set α // IsClosed x ∧ IsIrreducible x } :=
  equivSubtype'.toOrderIso (fun _ _ h ↦ h) (fun _ _ h ↦ h)

end IrreducibleCloseds

end TopologicalSpace
