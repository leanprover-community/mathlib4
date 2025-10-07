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
def IsDecompOn (f : X → X) (A : Set X) (S : Finset G) : Prop := ∀ a ∈ A, ∃ g ∈ S, f a = g • a

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

/--
An Equipartition contains a Finset of parts.
Each part has a source, a group element and a target.
The sources and targets of every part are supremum independent (and not empty), which ensures that
they form a `Finpartition` of the source and target of the whole Equipartition.
`decomp` ensures that applying the group element of a part to its source gives the target.
This definition is equivalent to the one given at `Equidecomp`.
It is mainly useful for constructing concrete Equidecompositions.
-/
structure Equipartition (X : Type*) (G : Type*) [SMul G X] where
  parts : Finset (Set X × G × Set X)
  supIndepSource : Finset.SupIndep parts (fun p ↦ p.1)
  supIndepTarget : Finset.SupIndep parts (fun p ↦ p.2.2)
  bot_notMem : ∀ p ∈ parts, p.1 ≠ ∅
  decomp : ∀ p ∈ parts, (fun x ↦ p.2.1 • x) '' p.1 = p.2.2

namespace Equipartition

variable (P : Equipartition X G)

/--
The source of the Equipartition, defined as the union of the source of all parts.
-/
def source := P.parts.sup (fun p ↦ p.1)

/--
The target of the Equipartition, defined as the union of the target of all parts.
-/
def target := P.parts.sup (fun p ↦ p.2.2)

theorem subset_source (p : Set X × G × Set X) (h : p ∈ P.parts) : p.1 ⊆ P.source := by
  simpa [source] using subset_biUnion_of_mem h

theorem subset_target (p : Set X × G × Set X) (h : p ∈ P.parts) : p.2.2 ⊆ P.target := by
  simp only [target, Finset.sup_set_eq_biUnion]
  exact subset_iUnion₂_of_subset p h fun ⦃a⦄ a ↦ a

/--
The sources of each part form a `Finpartition` of `source`.
-/
def source.to_finpartition [DecidableEq (Set X)] (P : Equipartition X G) : Finpartition P.source :=
  { parts := Finset.image (fun p ↦ p.1) P.parts
    sup_parts := by simp [source]
    supIndep := by exact Finset.SupIndep.image P.supIndepSource
    bot_notMem := by
      simp only [bot_eq_empty, Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right,
        not_exists]
      refine fun x y ↦ Finset.forall_mem_not_eq'.mp (fun b h ↦ ?_)
      simp [@Prod.eq_iff_fst_eq_snd_eq, P.bot_notMem b h]}

/--
The targets of each part form a `Finpartition` of `target`.
-/
def target.to_finpartition [DecidableEq (Set X)] (P : Equipartition X G) :
    Finpartition P.target :=
  { parts := Finset.image (fun p ↦ p.2.2) P.parts
    sup_parts := by simp [target]
    supIndep := by exact Finset.SupIndep.image P.supIndepTarget
    bot_notMem := by
      simp only [bot_eq_empty, Finset.mem_image, Prod.exists, exists_eq_right, not_exists]
      refine fun x y ↦ Finset.forall_mem_not_eq'.mp (fun b h ↦ ?_)
      exact ne_of_apply_ne (fun b ↦ b.2.2) (by simp [← P.decomp b h, P.bot_notMem b h])}

theorem parts_eq_iff_1 {p1 p2 : Set X × G × Set X} (h1 : p1 ∈ P.parts) (h2 : p2 ∈ P.parts) :
    p1 = p2 ↔ p1.1 = p2.1 := by
  refine Iff.intro (by simp +contextual) (fun h3 ↦ ?_)
  have h4 := Finset.SupIndep.pairwiseDisjoint P.supIndepSource
  by_contra hC
  simp only [PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, ne_eq, Prod.forall, Prod.mk.injEq,
    not_and] at h4
  have h5 := @h4 p1.1 p1.2.1 p1.2.2 h1 p2.1 p2.2.1 p2.2.2 h2 (by grind)
  simp only [h3, Prod.mk.eta, disjoint_self, bot_eq_empty, P.bot_notMem p2 h2] at h5

theorem parts_eq_iff_2 {p1 p2 : Set X × G × Set X} (h1 : p1 ∈ P.parts) (h2 : p2 ∈ P.parts) :
    p1 = p2 ↔ p1.2.2 = p2.2.2 := by
  refine Iff.intro (by simp +contextual) (fun h3 ↦ ?_)
  have h4 := Finset.SupIndep.pairwiseDisjoint P.supIndepTarget
  by_contra hC
  simp only [PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, ne_eq, Prod.forall, Prod.mk.injEq,
    not_and] at h4
  have h5 := @h4 p1.1 p1.2.1 p1.2.2 h1 p2.1 p2.2.1 p2.2.2 h2 (by grind)
  simp only [h3, ← P.decomp _ h2, image_smul, disjoint_self, bot_eq_empty, smul_set_eq_empty,
    P.bot_notMem p2 h2] at h5

/--
The piece of the partition containing `x`, the group element associated to that piece,
and the image of that piece under the group element.
-/
noncomputable def source_part (x : X) (h : x ∈ P.source) : Set X × G × Set X := by
  have h1 : ∃ p ∈ P.parts, x ∈ p.1 := by simp [source, mem_iUnion] at h ⊢; assumption
  exact Classical.choose h1

theorem source_part_spec (x : X) (h : x ∈ P.source) : x ∈ (P.source_part x h).1 := by
  rw [Equipartition.source_part]
  have h1 : ∃ p ∈ P.parts, x ∈ p.1 := by simp [source, mem_iUnion] at h ⊢; assumption
  exact (Classical.choose_spec h1).2

theorem source_part_mem_parts (x : X) (h : x ∈ P.source) : (P.source_part x h) ∈ P.parts := by
  rw [Equipartition.source_part]
  have h1 : ∃ p ∈ P.parts, x ∈ p.1 := by simp [source, mem_iUnion] at h ⊢; assumption
  exact (Classical.choose_spec h1).1

theorem source_part_decomp (x : X) (h : x ∈ P.source) :
      (P.source_part x h).2.1 • x ∈ (P.source_part x h).2.2 := by
  simp only [← P.decomp (P.source_part x h) (P.source_part_mem_parts x h), image_smul,
    mem_smul_set]
  use x
  simpa using source_part_spec P x h

/--
The piece of the partition whose image contains `x`, the group element associated to that piece,
and the image of that piece under the group element.
-/
noncomputable def target_part (x : X) (h : x ∈ P.target) : Set X × G × Set X := by
  have h1 : ∃ p ∈ P.parts, x ∈ p.2.2 := by
    simp [Equipartition.target, mem_iUnion] at h ⊢; assumption
  exact Classical.choose h1

theorem target_part_spec (x : X) (h : x ∈ P.target) : x ∈ (P.target_part x h).2.2 := by
  rw [Equipartition.target_part]
  have h1 : ∃ p ∈ P.parts, x ∈ p.2.2 := by
    simp [Equipartition.target, mem_iUnion] at h ⊢; assumption
  exact (Classical.choose_spec h1).2

theorem target_part_mem_parts (x : X) (h : x ∈ P.target) : (P.target_part x h) ∈ P.parts := by
  rw [Equipartition.target_part]
  have h1 : ∃ p ∈ P.parts, x ∈ p.2.2 := by
      simp [Equipartition.target, mem_iUnion] at h ⊢; assumption
  exact (Classical.choose_spec h1).1

theorem decomp_inv (x : X) (h : x ∈ P.target) :
    ∃ y ∈ (P.target_part x h).1, (P.target_part x h).2.1 • y = x := by
  let h1 := P.decomp (P.target_part x h) <| Equipartition.target_part_mem_parts P x h
  simp [Set.ext_iff] at h1
  rw [← @mem_smul_set]
  exact (h1 x).mpr <| Equipartition.target_part_spec P x h

theorem target_part_decomp (x : X) (h : x ∈ P.target) :
    (P.target_part x h).2.1⁻¹ • x ∈ (P.target_part x h).1 := by
  rcases P.decomp_inv x h with ⟨y,⟨h1, h2⟩⟩
  have h3 :  (P.target_part x h).2.1⁻¹ • x =
    (P.target_part x h).2.1⁻¹ • (P.target_part x h).2.1 • y := by
    rw [h2]
  simpa [h3] using h1

theorem part_eq_target_part_iff_mem (x : X) (hx : x ∈ P.target) (part : Set X × G × Set X)
    (hp : part ∈ P.parts) : x ∈ part.2.2 ↔ P.target_part x hx = part := by
  constructor
  · intro h
    rw [P.parts_eq_iff_2 (target_part_mem_parts P x hx) hp]
    by_contra h1
    have h2 := Finset.SupIndep.pairwiseDisjoint P.supIndepTarget
    simp [PairwiseDisjoint, Set.Pairwise] at h2
    have h2 := h2 part.1 part.2.1 part.2.2 hp (P.target_part x hx).1 (P.target_part x hx).2.1
            (P.target_part x hx).2.2 (by simpa using target_part_mem_parts P x hx) (by grind)
    simp only [Prod.mk.eta, Disjoint, le_eq_subset, bot_eq_empty, subset_empty_iff] at h2
    have h2 := @h2 {x} (by simp [h]) (by simpa using target_part_spec P x hx)
    simp at h2
  · intro h
    rw [← h]
    exact target_part_spec P x hx

theorem part_eq_source_part_iff_mem (x : X) (hx : x ∈ P.source) (part : Set X × G × Set X)
    (hp : part ∈ P.parts) : x ∈ part.1 ↔ P.source_part x hx = part := by
  constructor
  · intro h
    rw [P.parts_eq_iff_2 (source_part_mem_parts P x hx) hp]
    by_contra h1
    have h2 := Finset.SupIndep.pairwiseDisjoint P.supIndepSource
    simp only [PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, ne_eq, Prod.forall, Prod.mk.injEq,
      not_and] at h2
    have h2 := h2 part.1 part.2.1 part.2.2 hp (P.source_part x hx).1 (P.source_part x hx).2.1
            (P.source_part x hx).2.2 (by simpa using source_part_mem_parts P x hx) (by grind)
    have h2 := @h2 {x} (by simp [h]) (by simpa using source_part_spec P x hx)
    simp at h2
  · intro h
    rw [← h]
    exact source_part_spec P x hx

theorem source_part_eq_target_part (x : X) (h : x ∈ P.source) :
    P.source_part x h = P.target_part ((P.source_part x h).2.1 • x) (mem_of_subset_of_mem
      (P.subset_target (P.source_part x h) (source_part_mem_parts P x h))
          (source_part_decomp P x h)) := by
  let s := P.source_part x h
  have h_target : s.2.1 • x ∈ P.target := by
    apply mem_of_subset_of_mem (P.subset_target s (source_part_mem_parts P x h))
        (source_part_decomp P x h)
  have eq_iff := P.part_eq_target_part_iff_mem _ h_target s (source_part_mem_parts P x h)
  exact (eq_iff.mp (source_part_decomp P x h)).symm

theorem target_part_eq_source_part (x : X) (h : x ∈ P.target) :
    P.target_part x h = P.source_part ((P.target_part x h).2.1⁻¹ • x) (mem_of_subset_of_mem
      (P.subset_source (P.target_part x h) (target_part_mem_parts P x h))
          (target_part_decomp P x h)) := by
  let t := P.target_part x h
  have h_source : t.2.1⁻¹ • x ∈ P.source := by
    apply mem_of_subset_of_mem (P.subset_source t (target_part_mem_parts P x h))
        (target_part_decomp P x h)
  have eq_iff := P.part_eq_source_part_iff_mem _ h_source t (target_part_mem_parts P x h)
  exact (eq_iff.mp (target_part_decomp P x h)).symm

open scoped Classical in noncomputable def to_equidecomp : Equidecomp X G where
  toFun x := if h : x ∉ P.source then x else (P.source_part x (not_notMem.mp h)).2.1 • x
  invFun x := if h : x ∉ P.target then x else (P.target_part x (not_notMem.mp h)).2.1⁻¹ • x
  source := P.source
  target := P.target
  map_source' x hx := by simpa [hx] using (mem_of_subset_of_mem (P.subset_target
    (P.source_part x hx) (source_part_mem_parts P x hx)) (source_part_decomp P x hx))
  map_target' x hx := by
    simpa [hx] using (mem_of_subset_of_mem  (P.subset_source (P.target_part x hx)
       (target_part_mem_parts P x hx)) (target_part_decomp P x hx))
  left_inv' x hx := by
    have h1 : (P.source_part x (not_notMem.mp (of_eq_false (Eq.trans (congrArg Not (eq_true hx))
        not_true_eq_false)) )).2.1 • x ∈ P.target := by
      refine mem_of_subset_of_mem ?_ (P.source_part_decomp x hx)
      exact P.subset_target _ (source_part_mem_parts P x hx)
    simp [hx, h1, ↓reduceDIte, ← P.source_part_eq_target_part x hx, inv_smul_smul]
  right_inv' x hx := by
    have h1 : (P.target_part x (not_notMem.mp (of_eq_false (Eq.trans (congrArg Not (eq_true hx))
        not_true_eq_false)))).2.1⁻¹ • x ∈ P.source := by
      refine mem_of_subset_of_mem ?_ (P.target_part_decomp x hx)
      exact P.subset_source _ (target_part_mem_parts P x hx)
    simp [← P.target_part_eq_source_part x hx, smul_inv_smul, h1, hx]
  isDecompOn' := by
    use Finset.image (fun p ↦ p.2.1) P.parts
    intro x hx
    use (P.source_part x hx).2.1
    constructor
    · simp only [Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right]
      use (P.source_part x hx).1
      use (P.source_part x hx).2.2
      exact source_part_mem_parts P x hx
    · simp [hx]

end Equipartition

end Group

end Equidecomp
