/-
Copyright (c) 2024 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Order.Partition.Finpartition

/-!
# Equidecompositions

This file develops the basic theory of equidecompositions.

## Main Definitions

Let `G` be a group acting on a space `X`, and `A B : Set X`.

An *equidecomposition* of `A` and `B` is typically defined as a finite partition of `A` together
with a finite list of elements of `G` of the same size such that applying each element to the
matching piece of the partition yields a partition of `B`.

This yields a bijection `f : A ≃ B` where, given `a : A`, `f a = γ • a` for `γ : G` the group
element for `a`'s piece of the partition. Reversing this is easy, and so we get an equivalent
(up to the choice of group elements) definition: an *Equidecomposition* of `A` and `B` is a
bijection `f : A ≃ B` such that for some `S : Finset G`, `f a ∈ S • a` for all `a`.

We take this as our definition as it is easier to work with. It is implemented as an element
`PartialEquiv X X` with source `A` and target `B`.

## Implementation Notes

* Equidecompositions are implemented as elements of `PartialEquiv X X` together with a
  `Finset` of elements of the acting group and a proof that every point in the source is moved
  by an element in the finset.

* The requirement that `G` be a group is relaxed where possible.

* We introduce a non-standard predicate, `IsDecompOn`, to state that a function satisfies the main
  combinatorial property of equidecompositions, even if it is not injective or surjective.

## TODO

* Prove that if two sets equidecompose into subsets of each other, they are equidecomposable
  (Schroeder-Bernstein type theorem)
* Define equidecomposability into subsets as a preorder on sets and
  prove that its induced equivalence relation is equidecomposability.
* Prove the definition of equidecomposition used here is equivalent to the more familiar one
  using partitions.

-/

variable {X G : Type*} {A B C : Set X}

open Function Set Pointwise PartialEquiv

namespace Equidecomp

section SMul

variable [SMul G X]

/-- Let `G` act on a space `X` and `A : Set X`. We say `f : X → X` is a decomposition on `A`
as witnessed by some `S : Finset G` if for all `a ∈ A`, the value `f a` can be obtained
by applying some element of `S` to `a` instead.

More familiarly, the restriction of `f` to `A` is the result of partitioning `A` into finitely many
pieces, then applying a single element of `G` to each piece. -/
def IsDecompOn (f : X → X) (A : Set X) (S : Finset G) : Prop := ∀

 a ∈ A, ∃ g ∈ S, f a = g • a

variable (X G)

/-- Let `G` act on a space `X`. An `Equidecomposition` with respect to `X` and `G` is a partial
bijection `f : PartialEquiv X X` with the property that for some set `elements : Finset G`,
(which we record), for each `a ∈ f.source`, `f a` can be obtained by applying some `g ∈ elements`
instead. We call `f` an equidecomposition of `f.source` with `f.target`.

More familiarly, `f` is the result of partitioning `f.source` into finitely many pieces,
then applying a single element of `G` to each to get a partition of `f.target`.
-/
structure _root_.Equidecomp extends PartialEquiv X X where
  isDecompOn' : ∃ S : Finset G, IsDecompOn toFun source S

variable {X G}

/-- Note that `Equidecomp X G` is not `FunLike`. -/
instance : CoeFun (Equidecomp X G) fun _ => X → X := ⟨fun f => f.toFun⟩

/-- A finite set of group elements witnessing that `f` is an equidecomposition. -/
noncomputable
def witness (f : Equidecomp X G) : Finset G := f.isDecompOn'.choose

theorem isDecompOn (f : Equidecomp X G) : IsDecompOn f f.source f.witness :=
  f.isDecompOn'.choose_spec

noncomputable def element_witness (f : Equidecomp X G) (a : X) (h : a ∈ f.source) : G :=
    (f.isDecompOn a h).choose

open Classical in noncomputable def minimal_witness (f : Equidecomp X G) : Finset G :=
  {w ∈ f.witness | ∃ a, ∃ h, f.element_witness a h = w}

theorem minimal_witness_subset (f : Equidecomp X G) : f.minimal_witness ⊆ f.witness := by
  simp [witness, minimal_witness]

theorem element_witness_mem_minimal_witness (f : Equidecomp X G) (a : X) (h : a ∈ f.source) :
  f.element_witness a h ∈ f.minimal_witness := by
    simp [minimal_witness]
    apply And.intro
    . simp [witness, element_witness]
      sorry

    . use a
      use h

theorem apply_mem_target {f : Equidecomp X G} {x : X} (h : x ∈ f.source) :
    f x ∈ f.target := by simp [h]

theorem toPartialEquiv_injective : Injective <| toPartialEquiv (X := X) (G := G) := by
  intro ⟨_, _, _⟩ _ _
  congr

theorem IsDecompOn.mono {f f' : X → X} {A A' : Set X} {S : Finset G} (h : IsDecompOn f A S)
    (hA' : A' ⊆ A) (hf' : EqOn f f' A') : IsDecompOn f' A' S := by
  intro a ha
  rw [← hf' ha]
  exact h a (hA' ha)

/-- The restriction of an equidecomposition as an equidecomposition. -/
@[simps!]
def restr (f : Equidecomp X G) (A : Set X) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.restr A
  isDecompOn' := ⟨f.witness,
    f.isDecompOn.mono (source_restr_subset_source _ _) fun _ ↦ congrFun rfl⟩

@[simp]
theorem toPartialEquiv_restr (f : Equidecomp X G) (A : Set X) :
    (f.restr A).toPartialEquiv = f.toPartialEquiv.restr A := rfl

theorem source_restr (f : Equidecomp X G) {A : Set X} (hA : A ⊆ f.source) :
    (f.restr A).source = A := by rw [restr_source, inter_eq_self_of_subset_right hA]

theorem restr_of_source_subset {f : Equidecomp X G} {A : Set X} (hA : f.source ⊆ A) :
    f.restr A = f := by
  apply toPartialEquiv_injective
  rw [toPartialEquiv_restr, PartialEquiv.restr_eq_of_source_subset hA]

@[simp]
theorem restr_univ (f : Equidecomp X G) : f.restr univ = f :=
  restr_of_source_subset <| subset_univ _

end SMul

section Monoid

variable [Monoid G] [MulAction G X]

variable (X G)

/-- The identity function is an equidecomposition of the space with itself. -/
@[simps toPartialEquiv]
def refl : Equidecomp X G where
  toPartialEquiv := .refl _
  isDecompOn' := ⟨{1}, by simp [IsDecompOn]⟩

variable {X} {G}

open scoped Classical in
theorem IsDecompOn.comp' {g f : X → X} {B A : Set X} {T S : Finset G}
    (hg : IsDecompOn g B T) (hf : IsDecompOn f A S) :
    IsDecompOn (g ∘ f) (A ∩ f ⁻¹' B) (T * S)  := by
  intro _ ⟨aA, aB⟩
  rcases hf _ aA with ⟨γ, γ_mem, hγ⟩
  rcases hg _ aB with ⟨δ, δ_mem, hδ⟩
  use δ * γ, Finset.mul_mem_mul δ_mem γ_mem
  rwa [mul_smul, ← hγ]

open scoped Classical in
theorem IsDecompOn.comp {g f : X → X} {B A : Set X} {T S : Finset G}
    (hg : IsDecompOn g B T) (hf : IsDecompOn f A S) (h : MapsTo f A B) :
    IsDecompOn (g ∘ f) A (T * S)  := by
  rw [left_eq_inter.mpr h]
  exact hg.comp' hf

/-- The composition of two equidecompositions as an equidecomposition. -/
@[simps toPartialEquiv, trans]
noncomputable def trans (f g : Equidecomp X G) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.trans g.toPartialEquiv
  isDecompOn' := by classical exact ⟨g.witness * f.witness, g.isDecompOn.comp' f.isDecompOn⟩

end Monoid

section Group

variable [Group G] [MulAction G X]

open scoped Classical in
theorem IsDecompOn.of_leftInvOn {f g : X → X} {A : Set X} {S : Finset G}
    (hf : IsDecompOn f A S) (h : LeftInvOn g f A) : IsDecompOn g (f '' A) S⁻¹ := by
  rintro _ ⟨a, ha, rfl⟩
  rcases hf a ha with ⟨γ, γ_mem, hγ⟩
  use γ⁻¹, Finset.inv_mem_inv γ_mem
  rw [hγ, inv_smul_smul, ← hγ, h ha]

/-- The inverse function of an equidecomposition as an equidecomposition. -/
@[symm, simps toPartialEquiv]
noncomputable def symm (f : Equidecomp X G) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.symm
  isDecompOn' := by classical exact ⟨f.witness⁻¹, by
    convert f.isDecompOn.of_leftInvOn f.leftInvOn
    rw [image_source_eq_target, symm_source]⟩

theorem map_target {f : Equidecomp X G} {x : X} (h : x ∈ f.target) :
    f.symm x ∈ f.source := f.toPartialEquiv.map_target h

theorem left_inv {f : Equidecomp X G} {x : X} (h : x ∈ f.source) :
    f.toPartialEquiv.symm (f x) = x := by simp [h]

theorem right_inv {f : Equidecomp X G} {x : X} (h : x ∈ f.target) :
    f (f.toPartialEquiv.symm x) = x := by simp [h]

@[simp]
theorem symm_symm (f : Equidecomp X G) : f.symm.symm = f := rfl

theorem symm_involutive : Function.Involutive (symm : Equidecomp X G → _) := symm_symm

theorem symm_bijective : Function.Bijective (symm : Equidecomp X G → _) := symm_involutive.bijective

@[simp]
theorem refl_symm : (refl X G).symm = refl X G := rfl

@[simp]
theorem restr_refl_symm (A : Set X) :
    ((Equidecomp.refl X G).restr A).symm = (Equidecomp.refl X G).restr A := rfl

----

variable [Group G] [MulAction G X] [DecidableEq (Set X)]

structure Equipartition (G : Type*) [SMul G X] (A : Set X) where
  parts : Finset (Set X × G × Set X)
  sup_parts : A = (⋃ p ∈ parts, p.1)
  supIndep : Finset.SupIndep (Finset.image (fun p ↦ p.1) parts) id
  bot_notMem : ∀ p ∈ parts, p.1 ≠ ∅
  decomp : ∀ p ∈ parts, (fun x ↦ p.2.1 • x) '' p.1 = p.2.2

def Equipartition.to_finpartition {A : Set X} (P : Equipartition G A) : Finpartition A :=
  { parts := Finset.image (fun p ↦ p.1) P.parts
    sup_parts := by simp [P.sup_parts]
    supIndep := P.supIndep
    bot_notMem := by
      simp only [bot_eq_empty, Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right,
        not_exists]
      refine fun x y ↦ Finset.forall_mem_not_eq'.mp (fun b h ↦ ?_)
      simp [@Prod.eq_iff_fst_eq_snd_eq, P.bot_notMem b h]}

def Equipartition.target (P : Equipartition G A) : Set X := ⋃ p ∈ P.parts, p.2.2

/--
The piece of the partition containing `x`, the group element associated to that piece,
and the image of that piece under the group element.
-/
noncomputable def Equipartition.source_part (P : Equipartition G A) (x : X) (h : x ∈ A) :
       Set X × G × Set X := by
    have h1 : ∃ p ∈ P.parts, x ∈ p.1 := by simp [P.sup_parts, mem_iUnion] at h ⊢; assumption
    exact Classical.choose h1

theorem Equipartition.source_part_spec (P : Equipartition G A) (x : X) (h : x ∈ A) :
    x ∈ (P.source_part x h).1 := by
    simp [Equipartition.source_part]
    have h1 : ∃ p ∈ P.parts, x ∈ p.1 := by simp [P.sup_parts, mem_iUnion] at h ⊢; assumption
    exact (Classical.choose_spec h1).2

theorem Equipartition.source_part_mem_parts (P : Equipartition G A) (x : X) (h : x ∈ A) :
    (P.source_part x h) ∈ P.parts := by
    simp [Equipartition.source_part]
    have h1 : ∃ p ∈ P.parts, x ∈ p.1 := by simp [P.sup_parts, mem_iUnion] at h ⊢; assumption
    exact (Classical.choose_spec h1).1

theorem Equipartition.source_part_decomp (P : Equipartition G A) (x : X) (h : x ∈ A) :
    (P.source_part x h).2.1 • x ∈ (P.source_part x h).2.2 := by
    simp only [← P.decomp (P.source_part x h) (P.source_part_mem_parts x h), image_smul,
      mem_smul_set]
    use x
    simpa using source_part_spec P x h


/--
The piece of the partition whose image contains `x`, the group element associated to that piece,
and the image of that piece under the group element.
-/
noncomputable def Equipartition.target_part (P : Equipartition G A) (x : X) (h : x ∈ P.target) :
       Set X × G × Set X := by
    have h1 : ∃ p ∈ P.parts, x ∈ p.2.2 := by
      simp [Equipartition.target, mem_iUnion] at h ⊢; assumption
    exact (Classical.choose h1)

theorem Equipartition.target_part_spec (P : Equipartition G A) (x : X) (h : x ∈ P.target) :
      x ∈ (P.target_part x h).2.2 := by
    simp [Equipartition.target_part]
    have h1 : ∃ p ∈ P.parts, x ∈ p.2.2 := by
      simp [Equipartition.target, mem_iUnion] at h ⊢; assumption
    exact (Classical.choose_spec h1).2

open scoped Classical in noncomputable def Equipartition.to_equidecomp {A : Set X} (P : Equipartition G A) : Equidecomp X G where
  toFun x := if h : x ∉ A then x else (P.source_part x (not_notMem.mp h)).2.1 • x
  invFun x := if h : x ∉ P.target then x else (P.target_part x (not_notMem.mp h)).2.1⁻¹ • x
  source := A
  target := P.target
  map_source' x hx := by
    simp [hx, Equipartition.target]
    use (P.source_part x hx).1
    use (P.source_part x hx).2.1
    use (P.source_part x hx).2.2
    exact And.intro (P.source_part_mem_parts x hx) (P.source_part_decomp x hx)
  map_target' x hx := by sorry










open scoped Classical in def from_partition (source : Set X)
    (parts : Finpartition source) (witness : parts.parts → G) : Equidecomp X G where
  toFun x := if x ∉ source then x else witness ⟨x, sorry⟩ • x


open scoped Classical in noncomputable def source.to_finpartition {f : Equidecomp X G} :
  Finpartition f.source where
  parts := Finset.image (fun g : f.minimal_witness ↦
              Subtype.val '' {a : f.source | (f.isDecompOn a (Subtype.coe_prop a)).choose = g})
                  f.minimal_witness.attach
  supIndep := by
    rw [Finset.SupIndep]
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, exists_prop, id_eq,
      Finset.sup_set_eq_biUnion, disjoint_iUnion_right, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro t ht a1 ha h1 i hi
    rw [Finset.subset_image_iff] at ht
    rcases ht with ⟨s, ⟨ht1, ht2⟩⟩
    --- h1
    rw [← ht2] at h1

    -- hi
    rw [← ht2] at hi
    simp at hi

    rcases hi with ⟨a, ⟨⟨h3, hi1⟩, hi2⟩⟩

    subst hi2
    simp only [Subtype.val_injective, disjoint_image_iff]
    rw [Set.disjoint_iff]
    simp
    rw [Set.eq_empty_iff_forall_notMem]
    simp only [mem_inter_iff, mem_setOf_eq, not_and, Subtype.forall]

    intro x ha1 h4
    rw [h4]
    simp at h1
    grind
  sup_parts := by
    simp only [Finset.sup_image, id_comp, Finset.sup_set_eq_biUnion, Finset.mem_attach, iUnion_true]
    apply le_antisymm
    . simp only [le_eq_subset, iUnion_subset_iff, image_subset_iff, Subtype.coe_preimage_self,
      subset_univ, implies_true]
    . simp only [le_eq_subset]
      rw [Set.subset_def]
      simp only [mem_iUnion, mem_image, mem_setOf_eq, Subtype.exists, exists_and_right,
        exists_eq_right, exists_prop]
      intro x hx
      use f.element_witness x hx
      apply And.intro
      . exact element_witness_mem_minimal_witness f x hx
      . use hx
        simp_rw [element_witness]


  bot_notMem := by
    --by_cases hC: f.source.Nonempty
    simp only [bot_eq_empty, Finset.mem_image, Finset.mem_attach, image_eq_empty, true_and,
      Subtype.exists, exists_prop, not_exists, not_and]
    intro x hx
    push_neg
    rw [Set.nonempty_def]
    simp only [mem_setOf_eq, Subtype.exists]
    --

    rw [Equidecomp.minimal_witness] at hx
    simp at hx
    rcases hx with ⟨hx, ⟨a, ⟨ha, ha1⟩⟩⟩
    use a
    use ha
    rw [← ha1]
    simp_rw [Equidecomp.element_witness]



end Group


end Equidecomp
