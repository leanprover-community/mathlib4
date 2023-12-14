/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Topology.Order.LowerUpperTopology
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.ZMod.Defs

/-!
# Lawson topology

This file introduces the Lawson topology on a preorder.

## Main definitions

- `LawsonTopology'` - the Lawson topology is defined as the meet of the `LowerTopology` and the
  `ScottTopology`.

## Main statements

## Implementation notes

A type synonym `WithLawsonTopology` is introduced and for a preorder `α`, `WithLawsonTopology α`
is made an instance of `topological_space` by the `LawsonTopology'`.

We define a mixin class `LawsonTopology` for the class of types which are both a preorder and a
topology and where the topology is the `LawsonTopology'`.
It is shown that `WithLawsonTopology α` is an instance of `LawsonTopology`.

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]

## Tags
Lawson topology, preorder
-/

open Set


universe u v

variable {α : Type u} [t₁ : TopologicalSpace α] {T₁ : Set (Set α)}
    [t₂ : TopologicalSpace α] {T₂ : Set (Set α)}
    {cond₁ : TopologicalSpace.IsTopologicalBasis T₁} {cond₂ : TopologicalSpace.IsTopologicalBasis T₂}

--variable {α}


open TopologicalSpace

def X : Fin 2 → Type u
  | 1 => α
  | 2 => α

def T : (i : Fin 2) → Set (Set (X (α:=α) i))
  | 1 => T₁
  | 2 => T₂

#check (@X α 1)

#check T (α:=α) 1

def t : ((i : Fin 2) →  TopologicalSpace (X (α:=α) i))
  | 1 => t₁
  | 2 => t₂

#check t 1

def condx : ((i : Fin 2) →  @IsTopologicalBasis _ (t (α:=α) i) (T (T₁ := T₁) (T₂ := T₂) i))
  | 1 => cond₁
  | 2 => cond₂

variable {β : Type*} {g : β → α}

#check (g : (β → (@X α 1)))

def f : ((i : Fin 2) →  β → (X (α:=α) i))
  | 1 => g
  | 2 => g

#check cond

#check f

#check @isTopologicalBasis_iInf β (Fin 2) X t T condx f

#check isTopologicalBasis_iInf f


theorem isTopologicalBasis_iInf' {β : Type*} {X : Fin 2 → Type u}
    [t : ∀ i, TopologicalSpace (X i)] {T : ∀ i, Set (Set (X i))}
    (f : ∀ i, β → X i) :
    @IsTopologicalBasis β (⨅ i, induced (f i) (t i))
      { S | ∃ (U : ∀ i, Set (X i)) (F : Set (Fin 2)),
        (∀ i, i ∈ F → U i ∈ T i) ∧ S = ⋂ (i) (_ : i ∈ F), f i ⁻¹' U i } := by
  apply isTopologicalBasis_iInf (T:=T) --(f (α := α))
  --apply (isTopologicalBasis_iInf (@X:=X))
  apply (@isTopologicalBasis_iInf β (Fin 2) X t T _ f)

  --intro i


variable {α β : Type*}

variable [TopologicalSpace α]

instance : TopologicalSpace (α×α) := by exact instTopologicalSpaceProd


namespace Topology

/-! ### Lawson topology -/

section Lawson
section Preorder

variable [Preorder α]

/--
The Lawson topology is defined as the meet of the `LowerTopology` and the `ScottTopology`.
-/
def lawson : TopologicalSpace α := lower α ⊓ scott

variable (α) [TopologicalSpace α]

/-- Predicate for an ordered topological space to be equipped with its Lawson topology.

The Lawson topology is defined as the meet of the `LowerTopology` and the `ScottTopology`.
-/
class IsLawson : Prop where
  topology_eq_lawson : ‹TopologicalSpace α› = lawson

end Preorder

namespace IsLawson
section Preorder
variable (α) [Preorder α] [TopologicalSpace α] -- [IsLawson α]



lemma topology_eq : ‹_› = lawson := topology_eq_lawson

/-- The complements of the upper closures of finite sets intersected with Scott open sets form
a basis for the lawson topology. -/
def lawsonBasis (α : Type*) [Preorder α] :=
  { s : Set α | ∃ u : Set α, IsOpen[scott] u ∧ ∃ t : Set α, t.Finite ∧
    u ∩ (upperClosure t : Set α)ᶜ = s }

#check iInf
#check instTopologicalSpaceProd
#check isTopologicalBasis_iInf
#check TopologicalSpace.IsTopologicalBasis.prod

#check isTopologicalBasis_pi


open TopologicalSpace





variable {X : Type u}
    [t₁ : TopologicalSpace X] {T₁ : Set (Set X)}
    [t₂ : TopologicalSpace X] {T₂ : Set (Set X)}
    (cond₁ : TopologicalSpace.IsTopologicalBasis T₁) (cond₂ : TopologicalSpace.IsTopologicalBasis T₂)

#check Inducing

#check (TopologicalSpace.IsTopologicalBasis.prod cond₁ cond₂).inducing induced_inf
-- (fun p : Set X × Set X => p.1 ∩ p.2)

theorem isTopologicalBasis_inf {β : Type*} {ι : Type*} {X : Type*}
    [t₁ : TopologicalSpace X] {T₁ : Set (Set X)}
    [t₂ : TopologicalSpace X] {T₂ : Set (Set X)}
    (cond₁ : TopologicalSpace.IsTopologicalBasis T₁) (cond₂ : TopologicalSpace.IsTopologicalBasis T₂) :
    @TopologicalSpace.IsTopologicalBasis X (t₁ ⊓ t₂)
      { S | ∃ U₁ ∈ T₁, ∃ U₂ ∈ T₂, S = U₁ ∩ U₂ } := by
  letI := t₁ ⊓ t₂
  convert (TopologicalSpace.IsTopologicalBasis.prod cond₁ cond₂).inducing
  sorry

#check inducing_inf_to_pi

#check induced_inf

#check inducing_iInf_to_pi

#check Singleton

#check ℤ₂

def f : Fin 2 → Prop
  | 1 => TopologicalSpace.IsTopologicalBasis T₁
  | 2 => TopologicalSpace.IsTopologicalBasis T₂

variable (X)

def g : Fin 2 → Set (Set X)
  | 1 => T₁
  | 2 => T₂


#check (g X (1 : Fin 2))

variable (i : Fin 2)

#check g X i

#check ∀ (i : Fin 2), TopologicalSpace.IsTopologicalBasis (g X i)





lemma test : ∀ (i : Fin 2), TopologicalSpace.IsTopologicalBasis (g X i) := by sorry

#check isTopologicalBasis_iInf (f)

/-
theorem isTopologicalBasis_iInf {β : Type*} {ι : Type*} {X : ι → Type*}
    [t : ∀ i, TopologicalSpace (X i)] {T : ∀ i, Set (Set (X i))}
    (cond : ∀ i, IsTopologicalBasis (T i)) (f : ∀ i, β → X i) :
    @IsTopologicalBasis β (⨅ i, induced (f i) (t i))
      { S | ∃ (U : ∀ i, Set (X i)) (F : Finset ι),
        (∀ i, i ∈ F → U i ∈ T i) ∧ S = ⋂ (i) (_ : i ∈ F), f i ⁻¹' U i } := by
  letI := ⨅ i, induced (f i) (t i)
  convert (isTopologicalBasis_pi cond).inducing (inducing_iInf_to_pi f)
  ext V
  constructor
  · rintro ⟨U, F, h1, rfl⟩
    refine' ⟨(F : Set ι).pi U, ⟨U, F, h1, rfl⟩, _⟩
    simp_rw [pi_def, Set.preimage_iInter]
    rfl
  · rintro ⟨U, ⟨U, F, h1, rfl⟩, rfl⟩
    refine' ⟨U, F, h1, _⟩
    simp_rw [pi_def, Set.preimage_iInter]
    rfl
-/


protected theorem isTopologicalBasis : TopologicalSpace.IsTopologicalBasis (lawsonBasis α) := by
  rw [lawsonBasis]
  apply isTopologicalBasis_iInf
  sorry

variable (s : Set α) (h: IsUpperSet s) (hs: IsOpen[Topology.scottHausdorff] s)



#check IsScottHausdorff.isOpen_of_isLowerSet (IsLower.isLowerSet_of_isOpen _)






-- Have the lower open sets are SH by
-- IsScottHausdorff.isOpen_of_isLowerSet (IsLower.isLowerSet_of_isOpen _)
-- Have the Scott open sets are SH by scottHausdorff_le_scott I think)
-- Together these are a subbasis
lemma isOpen_implies_scottHausdorff_open {s : Set α} : IsOpen s → IsOpen[scottHausdorff] s := by
  erw [topology_eq α];
  intro hs
  sorry

#check ⟨h, hs⟩

#check IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open.mpr ⟨h, hs⟩

#check scott

-- Get the statement deliberately wrong for now
lemma LawsonOpen_iff_ScottOpen (s : Set α) (h : IsUpperSet s) :
  IsOpen s ↔ IsOpen[Topology.scottHausdorff] s := by
  constructor
  · intro hs
    rw [IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open.mpr ⟨h, hs⟩]
    convert IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open.mpr _
    --rw [IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open]
    rw [@IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open _ _ _ _ s]
    constructor
    · exact h
    · exact fun d d₁ d₂ d₃ => (@LawsonOpen_implies_ScottHausdorffOpen' _ _ l S _ _ _ _ s)
        hs d d₁ d₂ d₃
  · apply TopologicalSpace.le_def.mp (Scott_le_Lawson _ _)

end Preorder
end IsLawson

/--
Type synonym for a preorder equipped with the Lawson topology
-/
def WithLawson (α : Type*) := α

namespace WithLawson

/-- `toLawson` is the identity function to the `WithLawson` of a type.  -/
@[match_pattern] def toLawson : α ≃ WithLawson α := Equiv.refl _

/-- `ofLawson` is the identity function from the `WithLawson` of a type.  -/
@[match_pattern] def ofLawson : WithLawson α ≃ α := Equiv.refl _

@[simp] lemma to_Lawson_symm_eq : (@toLawson α).symm = ofLawson := rfl
@[simp] lemma of_Lawson_symm_eq : (@ofLawson α).symm = toLawson := rfl
@[simp] lemma toLawson_ofLawson (a : WithLawson α) : toLawson (ofLawson a) = a := rfl
@[simp] lemma ofLawson_toLawson (a : α) : ofLawson (toLawson a) = a := rfl

@[simp, nolint simpNF]
lemma toLawson_inj {a b : α} : toLawson a = toLawson b ↔ a = b := Iff.rfl

@[simp, nolint simpNF]
lemma ofLawson_inj {a b : WithLawson α} : ofLawson a = ofLawson b ↔ a = b :=
Iff.rfl

/-- A recursor for `WithLawson`. Use as `induction x using WithLawson.rec`. -/
protected def rec {β : WithLawson α → Sort _}
    (h : ∀ a, β (toLawson a)) : ∀ a, β a := fun a => h (ofLawson a)

instance [Nonempty α] : Nonempty (WithLawson α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithLawson α) := ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithLawson α) := ‹Preorder α›
instance : TopologicalSpace (WithLawson α) := lawson
instance : IsLawson (WithLawson α) := ⟨rfl⟩

/-- If `α` is equipped with the Lawson topology, then it is homeomorphic to `WithLawson α`.
-/
def withLawsonTopologyHomeomorph [TopologicalSpace α] [IsLawson α]  : WithLawson α ≃ₜ α :=
  WithLawson.ofLawson.toHomeomorphOfInducing ⟨by erw [IsLawson.topology_eq α, induced_id]; rfl⟩

/-
theorem isOpen_preimage_ofLawson (S : Set α) :
    IsOpen (WithLawsonTopology.ofLawson ⁻¹' S) ↔
      LawsonTopology'.IsOpen S :=
  Iff.rfl

theorem isOpen_def (T : Set (WithLawsonTopology α)) :
    IsOpen T ↔
      LawsonTopology'.IsOpen (WithLawsonTopology.toLawson ⁻¹' T) :=
  Iff.rfl
-/

end WithLawson
end Lawson

/-

namespace LawsonTopology

section preorder

variable [Preorder α]

variable [TopologicalSpace α] [LawsonTopology α]

variable (α)

lemma topology_eq : ‹_› = LawsonTopology' := topology_eq_LawsonTopology

variable {α}




lemma isOpen_iff_Lower_and_Scott_Open (u : Set α) : LawsonTopology'.IsOpen u
↔ (LowerTopology'.IsOpen u ∧ ScottTopology'.IsOpen u) := by




end preorder

end LawsonTopology

section ts

variable [Preorder α]

lemma Lawson_le_Scott' : @LawsonTopology' α ≤ @ScottTopology' α := inf_le_right

lemma Lawson_le_Lower' : @LawsonTopology' α ≤ @LowerTopology' α := inf_le_left

lemma Scott_Hausdorff_le_Lawson' : @ScottHausdorffTopology α _ ≤ @LawsonTopology' α _ := by
  rw [LawsonTopology', le_inf_iff]
  constructor
  · exact @Scott_Hausdorff_le_Lower' α _
  · exact @Scott_Hausdorff_le_Scott' α _



lemma LawsonOpen_implies_ScottHausdorffOpen''' (s : Set α) :
  IsOpen (WithLawsonTopology.ofLawson ⁻¹' s) → ScottHausdorffTopology.IsOpen s :=
  Scott_Hausdorff_le_Lawson' _

lemma ScottOpen_implies_LawsonOpen (s : Set α) :
  IsOpen (WithScottTopology.ofScott ⁻¹' s) → IsOpen (WithLawsonTopology.ofLawson ⁻¹' s) :=
  Lawson_le_Scott' _ s



lemma LowerOpen_implies_LawsonOpen (s : Set α) :
  IsOpen (WithLowerTopology.ofLower ⁻¹' s) → IsOpen (WithLawsonTopology.ofLawson ⁻¹' s) :=
  Lawson_le_Lower' _ s

end ts

section csh

variable [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
  [ScottTopology α] [LawsonTopology β] (e : OrderIso α β) (s : Set α)


lemma Lawson_le_Scott'' [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
    [ScottTopology α] [LawsonTopology β] (e : OrderIso α β) :
    Equiv.toHomeomorphOfInducing e  ≤ α := inf_le_right

#check image e s

#check e '' s

lemma ScottOpen_implies_LawsonOpen' [Preorder α] [Preorder β] [TopologicalSpace α]
    [TopologicalSpace β][ScottTopology α] [LawsonTopology β] (e : OrderIso α β) (s : Set α) :
    IsOpen s → IsOpen (e '' s) := by
  apply   Lawson_le_Scott'

example [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
  [ScottTopology α] [LawsonTopology β] (e : OrderIso α β) : Continuous e := by
  rw [continuous_def]
  intro s hs
  apply ScottOpen_implies_LawsonOpen'
  --apply ScottOpen_implies_LawsonOpen
  --apply Lawson_le_Scott'


lemma ScottLawsonCont' [Preorder α] :
  Continuous (WithScott.toScott ∘ WithLawson.ofLawson : WithLawson α → _) := by
  rw [continuous_def]
  intro s hs
  apply ScottOpen_implies_LawsonOpen _ hs

lemma LawsonOpen_iff_ScottOpen' [Preorder α] (s : Set α) (h : IsUpperSet s) :
  IsOpen (WithScottTopology.ofScott ⁻¹' s) ↔ IsOpen (WithLawsonTopology.ofLawson ⁻¹' s) := by
  constructor
  · apply ScottOpen_implies_LawsonOpen
  · intro hs
    rw [ScottTopology.isOpen_iff_upper_and_Scott_Hausdorff_Open']
    constructor
    · exact h
    · apply LawsonOpen_implies_ScottHausdorffOpen''' _ hs

variable  (L : TopologicalSpace α) (l : TopologicalSpace α) (S : TopologicalSpace α)

variable [Preorder α]  [@LawsonTopology α L _] [@LowerTopology α l _] [@ScottTopology α S _]

lemma Scott_le_Lawson : L ≤ S := by
  rw [@ScottTopology.topology_eq α _ S _, @LawsonTopology.topology_eq α _ L _,  LawsonTopology']
  apply inf_le_right

lemma Scott_Hausdorff_le_Lawson : (@ScottHausdorffTopology α _) ≤ L := by
  rw [@LawsonTopology.topology_eq α _ L _,  LawsonTopology', le_inf_iff,
    ← @LowerTopology.topology_eq α _ l _, ← @ScottTopology.topology_eq α _ S _]
  constructor
  · exact @Scott_Hausdorff_le_Lower  α _ l _
  · exact Scott_Hausdorff_le_Scott

open Topology

lemma LawsonOpen_implies_ScottHausdorffOpen : IsOpen[L] ≤ IsOpen[ScottHausdorffTopology] := by
  rw [←TopologicalSpace.le_def]
  apply (@Scott_Hausdorff_le_Lawson _ L l _ _ _)


lemma LawsonOpen_implies_ScottHausdorffOpen' (s : Set α) :
IsOpen[L] s → IsOpen[ScottHausdorffTopology] s := by
  apply (@LawsonOpen_implies_ScottHausdorffOpen _ _ l)

end csh

-- Can we say something without CL?
section CompleteLattice

variable [CompleteLattice α]
  (S :TopologicalSpace α) (l : TopologicalSpace α) (L : TopologicalSpace α)
  [@ScottTopology α S _]  [@LawsonTopology α L _] [@LowerTopology α l _]

-- Scott open iff UpperSet and STopology open

open Topology

variable [Preorder α] [TopologicalSpace α] (s : Set α)

#check @Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open _ _ Topology.scott _  s

lemma LawsonOpen_iff_ScottOpen (s : Set α) (h : IsUpperSet s) :
  IsOpen[Topology.lawson] s ↔ IsOpen[Topology.scott] s := by
  constructor
  · intro hs
    rw [@Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open _ _ Topology.scott _ s]
    constructor
    · exact h
    · exact fun d d₁ d₂ d₃ => (@LawsonOpen_implies_ScottHausdorffOpen' _ _ l S _ _ _ _ s)
        hs d d₁ d₂ d₃
  · apply TopologicalSpace.le_def.mp (Scott_le_Lawson _ _)

end CompleteLattice
-/
