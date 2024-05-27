/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Order.Atoms

#align_import algebra.lie.semisimple from "leanprover-community/mathlib"@"356447fe00e75e54777321045cdff7c9ea212e60"

/-!
# Semisimple Lie algebras

The famous Cartan-Dynkin-Killing classification of semisimple Lie algebras renders them one of the
most important classes of Lie algebras. In this file we define simple and semisimple Lie algebras
and prove some basic related results.

## Main declarations

* `LieModule.IsIrreducible`
* `LieAlgebra.IsSimple`
* `LieAlgebra.HasTrivialRadical`
* `LieAlgebra.SemisimpleGenerators`:
  An abstraction that captures the conditions on a set of ideals
  that ensure that they generate a semisimple Lie algebra.
* `LieAlgebra.IsSemisimple`
* `LieAlgebra.IsSemisimple.instHasTrivialRadical`: A semisimple Lie algebra has trivial radical.
* `LieAlgebra.IsSemisimple.instBooleanAlgebra`:
  The lattice of ideals in a semisimple Lie algebra is a boolean algebra.
  In particular, this implies that the lattice of ideals is atomistic:
  every ideal is a direct sum of atoms (simple ideals) in a unique way.
* `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`
* `LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals`
* `LieAlgebra.abelian_radical_iff_solvable_is_abelian`

## Tags

lie algebra, radical, simple, semisimple
-/


universe u v w w₁ w₂

-- move this to `Mathlib.Order.BooleanAlgebra`
namespace DistribLattice

variable (α : Type*) [DistribLattice α]

/--
An alternative constructor for boolean algebras:
a distributive lattice that is complemented is a boolean algebra.

This is not an instance, because it creates data using choice.
-/
noncomputable
def booleanAlgebra_of_complemented [BoundedOrder α] [ComplementedLattice α] : BooleanAlgebra α where
  __ := (inferInstanceAs (DistribLattice α))
  __ := (inferInstanceAs (BoundedOrder α))
  compl a := Classical.choose <| exists_isCompl a
  inf_compl_le_bot a := (Classical.choose_spec (exists_isCompl a)).disjoint.le_bot
  top_le_sup_compl a := (Classical.choose_spec (exists_isCompl a)).codisjoint.top_le

end DistribLattice

-- move this to `Mathlib.Order.ConditionallyCompleteLattice.Basic`
namespace CompleteDistribLattice

variable (α : Type*) [CompleteDistribLattice α]

/--
An alternative constructor for complete boolean algebras:
a complete distributive lattice that is complemented is a complete boolean algebra.

This is not an instance, because it creates data using choice.
-/
noncomputable
def completeBooleanAlgebra_of_complemented [ComplementedLattice α] :
    CompleteBooleanAlgebra α where
  __ := (inferInstanceAs (CompleteDistribLattice α))
  __ := DistribLattice.booleanAlgebra_of_complemented α

end CompleteDistribLattice


-- move this
namespace IsCompactlyGenerated

open CompleteLattice

variable {α : Type*} [CompleteLattice α] [IsCompactlyGenerated α]

/--
An alternative constructor for boolean algebras.

A set of ideals in a Lie algebra is a set of *boolean generators* if:

* the elements are all atoms,
* the set is independent, and
* the set satisfies an atomicity condition:
  any compact element below the supremum of a subset `s` of generators
  is equal to the supremum of a subset of `s`.

If the supremum of such a collection of boolean generators is the whole lattice,
then the lattice is a boolean algebra (see `BooleanGenerators.booleanAlgebra_of_sSup_eq_top`).
-/
structure BooleanGenerators (S : Set α) : Prop where
  /-- The elements in a collection of boolean generators are all atoms. -/
  isAtom : ∀ I ∈ S, IsAtom I
  /-- The elements in a collection of boolean generators are independent. -/
  setIndependent : CompleteLattice.SetIndependent S
  /-- The elements in a collection of boolean generators satisfy an atomicity condition:
  any compact element below the supremum of a subset `s` of generators
  is equal to the supremum of a subset of `s`. -/
  finitelyAtomistic : ∀ (s : Finset α) (a : α),
      ↑s ⊆ S → IsCompactElement a → a ≤ s.sup id → ∃ t ⊆ s, a = t.sup id

namespace BooleanGenerators

variable {S : Set α} (hS : BooleanGenerators S)

lemma mono {T : Set α} (hTS : T ⊆ S) : BooleanGenerators T where
  isAtom I hI := hS.isAtom I (hTS hI)
  setIndependent := hS.setIndependent.mono hTS
  finitelyAtomistic := fun s a hs ↦ hS.finitelyAtomistic s a (le_trans hs hTS)

lemma atomistic (a : α) (ha : a ≤ sSup S) : ∃ T ⊆ S, a = sSup T := by
  obtain ⟨C, hC, rfl⟩ := IsCompactlyGenerated.exists_sSup_eq a
  have aux : ∀ b : α, IsCompactElement b → b ≤ sSup S → ∃ T ⊆ S, b = sSup T := by
    intro b hb hbS
    obtain ⟨s, hs₁, hs₂⟩ := hb S hbS
    obtain ⟨t, ht, rfl⟩ := hS.finitelyAtomistic s b hs₁ hb hs₂
    refine ⟨t, ?_, Finset.sup_id_eq_sSup t⟩
    refine Set.Subset.trans ?_ hs₁
    simpa only [Finset.coe_subset] using ht
  choose T hT₁ hT₂ using aux
  use sSup {T c h₁ h₂ | (c ∈ C) (h₁ : IsCompactElement c) (h₂ : c ≤ sSup S)}
  constructor
  · apply _root_.sSup_le
    rintro _ ⟨c, -, h₁, h₂, rfl⟩
    apply hT₁
  · apply le_antisymm
    · apply _root_.sSup_le
      intro c hc
      rw [hT₂ c (hC _ hc) ((le_sSup hc).trans ha)]
      apply sSup_le_sSup
      apply _root_.le_sSup
      use c, hc, hC _ hc, (le_sSup hc).trans ha
    · simp only [Set.sSup_eq_sUnion, sSup_le_iff, Set.mem_sUnion, Set.mem_setOf_eq,
        forall_exists_index, and_imp]
      rintro a T b hbC hb hbS rfl haT
      apply (le_sSup haT).trans
      rw [← hT₂]
      exact le_sSup hbC

lemma isAtomistic_of_sSup_eq_top (h : sSup S = ⊤) : IsAtomistic α := by
  refine ⟨fun a ↦ ?_⟩
  obtain ⟨s, hs, hs'⟩ := hS.atomistic a (h ▸ le_top)
  exact ⟨s, hs', fun I hI ↦ hS.isAtom I (hs hI)⟩

lemma mem_of_isAtom_of_le_sSup_atoms (a : α) (ha : IsAtom a) (haS : a ≤ sSup S) :
    a ∈ S := by
  obtain ⟨T, hT, rfl⟩ := hS.atomistic a haS
  obtain rfl | ⟨a, haT⟩ := T.eq_empty_or_nonempty
  · simp only [sSup_empty] at ha
    exact (ha.1 rfl).elim
  suffices sSup T = a from this ▸ hT haT
  have : a ≤ sSup T := le_sSup haT
  rwa [ha.le_iff_eq, eq_comm] at this
  exact (hS.isAtom a (hT haT)).1

lemma sSup_le_sSup_iff_of_atoms (X Y : Set α) (hX : X ⊆ S) (hY : Y ⊆ S) :
    sSup X ≤ sSup Y ↔ X ⊆ Y := by
  refine ⟨?_, sSup_le_sSup⟩
  intro h a ha
  apply (hS.mono hY).mem_of_isAtom_of_le_sSup_atoms _ _ ((le_sSup ha).trans h)
  exact (hS.mono hX).isAtom a ha

lemma complementedLattice_of_sSup_eq_top (h : sSup S = ⊤) : ComplementedLattice α := by
  constructor
  intro a
  obtain ⟨T, hT, rfl⟩ := hS.atomistic a (le_top.trans h.ge)
  use sSup (S \ T)
  constructor
  swap
  · rw [codisjoint_iff, ← sSup_union, Set.union_diff_self, Set.union_eq_right.mpr hT, h]
  intro b hb₁ hb₂
  obtain ⟨X, hX, rfl⟩ := hS.atomistic b (le_top.trans h.ge)
  rw [hS.sSup_le_sSup_iff_of_atoms _ _ hX] at hb₁ hb₂
  · obtain rfl : X = ∅ := by
      have := Set.disjoint_sdiff_right hb₁ hb₂
      rwa [← eq_bot_iff] at this
    simp only [sSup_empty, le_refl]
  · exact Set.diff_subset _ _
  · exact hT

lemma sSup_inter {T₁ T₂ : Set α} (hT₁ : T₁ ⊆ S) (hT₂ : T₂ ⊆ S) :
    sSup (T₁ ∩ T₂) = (sSup T₁) ⊓ (sSup T₂) := by
  apply le_antisymm
  · apply le_inf
    · apply sSup_le_sSup (Set.inter_subset_left T₁ T₂)
    · apply sSup_le_sSup (Set.inter_subset_right T₁ T₂)
  obtain ⟨X, hX, hX'⟩ := hS.atomistic (sSup T₁ ⊓ sSup T₂) (inf_le_left.trans (sSup_le_sSup hT₁))
  rw [hX']
  apply _root_.sSup_le
  intro I hI
  apply _root_.le_sSup
  constructor
  · apply (hS.mono hT₁).mem_of_isAtom_of_le_sSup_atoms _ _ _
    · exact (hS.mono hX).isAtom I hI
    · exact (_root_.le_sSup hI).trans (hX'.ge.trans inf_le_left)
  · apply (hS.mono hT₂).mem_of_isAtom_of_le_sSup_atoms _ _ _
    · exact (hS.mono hX).isAtom I hI
    · exact (_root_.le_sSup hI).trans (hX'.ge.trans inf_le_right)

lemma eq_atoms_of_sSup_eq_top (h : sSup S = ⊤) : S = {a : α | IsAtom a} := by
  apply le_antisymm
  · exact hS.isAtom
  intro a ha
  obtain ⟨T, hT, rfl⟩ := hS.atomistic a (le_top.trans h.ge)
  exact hS.mem_of_isAtom_of_le_sSup_atoms _ ha (sSup_le_sSup hT)

/-- A lattice generated by boolean generators is a distributive lattice. -/
def distribLattice_of_sSup_eq_top (h : sSup S = ⊤) : DistribLattice α where
  le_sup_inf a b c := by
    obtain ⟨Ta, hTa, rfl⟩ := hS.atomistic a (h ▸ le_top)
    obtain ⟨Tb, hTb, rfl⟩ := hS.atomistic b (h ▸ le_top)
    obtain ⟨Tc, hTc, rfl⟩ := hS.atomistic c (h ▸ le_top)
    apply le_of_eq
    rw [← sSup_union, ← sSup_union, ← hS.sSup_inter hTb hTc, ← hS.sSup_inter, ← sSup_union]
    on_goal 1 => congr 1; ext
    all_goals
      simp only [Set.union_subset_iff, Set.mem_inter_iff, Set.mem_union]
      tauto

/-- A lattice generated by boolean generators is a boolean algebra. -/
noncomputable
def booleanAlgebra_of_sSup_eq_top (h : sSup S = ⊤) : BooleanAlgebra α :=
  let _i := hS.distribLattice_of_sSup_eq_top h
  have := hS.complementedLattice_of_sSup_eq_top h
  DistribLattice.booleanAlgebra_of_complemented α

end BooleanGenerators

end IsCompactlyGenerated


section Irreducible

variable (R L M : Type*) [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]

/-- A nontrivial Lie module is *irreducible* if its only Lie submodules are `⊥` and `⊤`. -/
abbrev LieModule.IsIrreducible : Prop :=
  IsSimpleOrder (LieSubmodule R L M)
#align lie_module.is_irreducible LieModule.IsIrreducible

lemma LieModule.nontrivial_of_isIrreducible [LieModule.IsIrreducible R L M] : Nontrivial M where
  exists_pair_ne := by
    have aux : (⊥ : LieSubmodule R L M) ≠ ⊤ := bot_ne_top
    contrapose! aux
    ext m
    simpa using aux m 0

end Irreducible

namespace LieAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/--
A Lie algebra *has trivial radical* if its radical is trivial.
This is equivalent to having no non-trivial solvable ideals,
and further equivalent to having no non-trivial abelian ideals.

In characteristic zero, it is also equivalent to `LieAlgebra.IsSemisimple`.

Note that the label 'semisimple' is apparently not universally agreed
[upon](https://mathoverflow.net/questions/149391/on-radicals-of-a-lie-algebra#comment383669_149391)
for general coefficients.

For example [Seligman, page 15](seligman1967) uses the label for `LieAlgebra.HasTrivialRadical`,
whereas we reserve it for Lie algebras that are a direct sum of simple Lie algebras.
-/
class HasTrivialRadical : Prop where
  radical_eq_bot : radical R L = ⊥
#align lie_algebra.is_semisimple LieAlgebra.HasTrivialRadical

export HasTrivialRadical (radical_eq_bot)
attribute [simp] radical_eq_bot

variable {R L} in
theorem HasTrivialRadical.eq_bot_of_isSolvable [HasTrivialRadical R L]
    (I : LieIdeal R L) [hI : IsSolvable R I] : I = ⊥ :=
  sSup_eq_bot.mp radical_eq_bot _ hI

@[simp]
theorem HasTrivialRadical.center_eq_bot [HasTrivialRadical R L] : center R L = ⊥ :=
  HasTrivialRadical.eq_bot_of_isSolvable _
#align lie_algebra.center_eq_bot_of_semisimple LieAlgebra.HasTrivialRadical.center_eq_bot

variable {R L} in
theorem hasTrivialRadical_of_no_solvable_ideals (h : ∀ I : LieIdeal R L, IsSolvable R I → I = ⊥) :
    HasTrivialRadical R L :=
  ⟨sSup_eq_bot.mpr h⟩

theorem hasTrivialRadical_iff_no_solvable_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsSolvable R I → I = ⊥ :=
  ⟨@HasTrivialRadical.eq_bot_of_isSolvable _ _ _ _ _, hasTrivialRadical_of_no_solvable_ideals⟩
#align lie_algebra.is_semisimple_iff_no_solvable_ideals LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals

theorem hasTrivialRadical_iff_no_abelian_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsLieAbelian I → I = ⊥ := by
  rw [hasTrivialRadical_iff_no_solvable_ideals]
  constructor <;> intro h₁ I h₂
  · exact h₁ _ <| LieAlgebra.ofAbelianIsSolvable R I
  · rw [← abelian_of_solvable_ideal_eq_bot_iff]
    exact h₁ _ <| abelian_derivedAbelianOfIdeal I
#align lie_algebra.is_semisimple_iff_no_abelian_ideals LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals

/-- A Lie algebra is simple if it is irreducible as a Lie module over itself via the adjoint
action, and it is non-Abelian. -/
class IsSimple : Prop where
  eq_bot_or_eq_top : ∀ I : LieIdeal R L, I = ⊥ ∨ I = ⊤
  non_abelian : ¬IsLieAbelian L
#align lie_algebra.is_simple LieAlgebra.IsSimple

namespace IsSimple

variable [IsSimple R L]

instance : LieModule.IsIrreducible R L L := by
  suffices Nontrivial (LieIdeal R L) from ⟨IsSimple.eq_bot_or_eq_top⟩
  rw [LieSubmodule.nontrivial_iff, ← not_subsingleton_iff_nontrivial]
  have _i : ¬ IsLieAbelian L := IsSimple.non_abelian R
  contrapose! _i
  infer_instance

variable {R L} in
lemma eq_top_of_isAtom (I : LieIdeal R L) (hI : IsAtom I) : I = ⊤ :=
  (IsSimple.eq_bot_or_eq_top I).resolve_left hI.1

lemma isAtom_top : IsAtom (⊤ : LieIdeal R L) :=
  ⟨bot_ne_top.symm, fun _ h ↦ IsSimpleOrder.LT.lt.eq_bot h⟩

variable {R L} in
@[simp] lemma isAtom_iff_eq_top (I : LieIdeal R L) : IsAtom I ↔ I = ⊤ :=
  ⟨eq_top_of_isAtom I, fun h ↦ h ▸ isAtom_top R L⟩

instance : HasTrivialRadical R L := by
  rw [hasTrivialRadical_iff_no_abelian_ideals]
  intro I hI
  apply (IsSimple.eq_bot_or_eq_top I).resolve_right
  rintro rfl
  rw [lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv] at hI
  exact IsSimple.non_abelian R (L := L) hI

end IsSimple

variable {R L} in
/--
A set of ideals in a Lie algebra is a set of *semisimple generators* if:

* the ideals are all atoms (in the lattice-theoretic sense),
  so they are nontrivial and do not contain any nontrivial ideals,
* the ideals are all simple, and
* the set is independent in the sense that the intersection of any the ideals
  with the supremum of the others is trivial.

If the supremum of such a collection of semisimple generators
is the whole Lie algebra, then the Lie algebra is semisimple.
See `SemisimpleGenerators.isSemisimple_of_sSup_eq_top`.
-/
structure SemisimpleGenerators (S : Set (LieIdeal R L)) : Prop where
  /-- The ideals in a collection of semisimple generators are all atoms. -/
  isAtom : ∀ I ∈ S, IsAtom I
  /-- The ideals in a collection of semisimple generators are all simple. -/
  isSimple : ∀ I ∈ S, IsSimple R I
  /-- The ideals in a collection of semisimple generators are independent
  (in the lattice-theoretic sense). -/
  setIndependent : CompleteLattice.SetIndependent S

namespace SemisimpleGenerators

open CompleteLattice

variable {R L}
variable {S : Set (LieIdeal R L)} (hS : SemisimpleGenerators S)

lemma mono {T : Set (LieIdeal R L)} (hTS : T ⊆ S) : SemisimpleGenerators T where
  isAtom I hI := hS.isAtom I (hTS hI)
  isSimple I hI := hS.isSimple I (hTS hI)
  setIndependent := hS.setIndependent.mono hTS

/--
In a semisimple Lie algebra,
Lie ideals that are contained in the supremum of a finite collection of atoms
are themselves the supremum of a finite subcollection of those atoms.

By a compactness argument, this statement can be extended to arbitrary sets of atoms.
See `atomistic`.

The proof is by induction on the finite set of atoms.
-/
private
lemma atomistic_of_finset : ∀ s : Finset (LieIdeal R L), ↑s ⊆ S →
    ∀ I : LieIdeal R L, I ≤ s.sup id → ∃ t ⊆ s, I = t.sup id := by
  intro s hs I hI
  obtain rfl | hI := hI.eq_or_lt
  · exact ⟨s, le_rfl, rfl⟩
  -- We assume that `I` is strictly smaller than the supremum of `s`.
  -- Hence there must exist an atom `J` that is not contained in `I`.
  obtain ⟨J, hJs, hJI⟩ : ∃ J ∈ s, ¬ J ≤ I := by
    by_contra! H
    exact hI.ne (le_antisymm hI.le (s.sup_le H))
  classical
  let s' := s.erase J
  have hs' : s' ⊂ s := Finset.erase_ssubset hJs
  have hs'S : ↑s' ⊆ S := Set.Subset.trans (Finset.coe_subset.mpr hs'.subset) hs
  -- If we show that `I` is contained in the supremum `K` of the complement of `J` in `s`,
  -- then we are done by recursion.
  set K := s'.sup id
  suffices I ≤ K by
    obtain ⟨t, hts', htI⟩ := atomistic_of_finset s' hs'S I this
    exact ⟨t, le_trans hts' hs'.subset, htI⟩
  -- Since `I` is contained in the supremum of `J` with the supremum of `s'`,
  -- any element `x` of `I` can be written as `y + z` for some `y ∈ J` and `z ∈ K`.
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ : ∃ y ∈ id J, ∃ z ∈ K, y + z = x := by
    rw [← LieSubmodule.mem_sup, ← Finset.sup_insert, Finset.insert_erase hJs]
    exact hI.le hx
  -- If we show that `y` is contained in the center of `J`,
  -- then we find `x = z`, and hence `x` is contained in the supremum of `s'`.
  -- Since `x` was arbitrary, we have shown that `I` is contained in the supremum of `s'`.
  suffices ⟨y, hy⟩ ∈ LieAlgebra.center R J by
    have _inst := hS.isSimple J (hs hJs)
    rw [HasTrivialRadical.center_eq_bot R J, LieSubmodule.mem_bot] at this
    apply_fun Subtype.val at this
    dsimp at this
    rwa [this, zero_add]
  -- To show that `y` is in the center of `J`,
  -- we show that any `j ∈ J` brackets to `0` with `z` and with `x = y + z`.
  -- By a simple computation, that implies `⁅j, y⁆ = 0`, for all `j`, as desired.
  intro j
  suffices ⁅(j : L), z⁆ = 0 ∧ ⁅(j : L), y + z⁆ = 0 by
    rw [lie_add, this.1, add_zero] at this
    ext
    exact this.2
  rw [← LieSubmodule.mem_bot (R := R) (L := L), ← LieSubmodule.mem_bot (R := R) (L := L)]
  constructor
  -- `j` brackets to `0` with `z`, since `⁅j, z⁆` is contained in `⁅J, K⁆ ≤ J ⊓ K`,
  -- and `J ⊓ K = ⊥` by the independence of the atoms.
  · apply (hS.setIndependent.disjoint_sSup (hs hJs) hs'S (Finset.not_mem_erase _ _)).le_bot
    apply LieSubmodule.lie_le_inf
    apply LieSubmodule.lie_mem_lie _ _ j.2
    simpa only [K, Finset.sup_id_eq_sSup] using hz
  -- By similar reasoning, `j` brackets to `0` with `x = y + z ∈ I`, if we show `J ⊓ I = ⊥`.
  suffices J ⊓ I = ⊥ by
    apply this.le
    apply LieSubmodule.lie_le_inf
    exact LieSubmodule.lie_mem_lie _ _ j.2 hx
  -- Indeed `J ⊓ I = ⊥`, since `J` is an atom that is not contained in `I`.
  apply ((hS.isAtom J (hs hJs)).le_iff.mp _).resolve_right
  · contrapose! hJI
    rw [← hJI]
    exact inf_le_right
  exact inf_le_left
termination_by s => s.card
decreasing_by exact Finset.card_lt_card hs'

lemma bg : IsCompactlyGenerated.BooleanGenerators S where
  isAtom := hS.isAtom
  setIndependent := hS.setIndependent
  finitelyAtomistic s I hs _ := hS.atomistic_of_finset s hs I

end SemisimpleGenerators

/--
A *semisimple* Lie algebra is one that is a direct sum of non-abelian atomic ideals.
These ideals are simple Lie algebras, by `isSimple_of_isAtom`.

Note that the label 'semisimple' is apparently not universally agreed
[upon](https://mathoverflow.net/questions/149391/on-radicals-of-a-lie-algebra#comment383669_149391)
for general coefficients.

For example [Seligman, page 15](seligman1967) uses the label for `LieAlgebra.HasTrivialRadical`,
the weakest of the various properties which are all equivalent over a field of characteristic zero.
-/
class IsSemisimple : Prop where
  /-- In a semisimple Lie algebra, the supremum of the atoms is the whole Lie algebra. -/
  sSup_isAtom_eq_top : sSup {I : LieIdeal R L | IsAtom I} = ⊤
  /-- In a semisimple Lie algebra, the atoms are independent. -/
  setIndependent_isAtom : CompleteLattice.SetIndependent {I : LieIdeal R L | IsAtom I}
  /-- In a semisimple Lie algebra, the atoms are non-abelian. -/
  non_abelian_of_isAtom : ∀ I : LieIdeal R L, IsAtom I → ¬ IsLieAbelian I

variable {R L} in
lemma isSimple_of_isAtom [IsSemisimple R L] (I : LieIdeal R L) (hI : IsAtom I) : IsSimple R I where
  non_abelian := IsSemisimple.non_abelian_of_isAtom I hI
  eq_bot_or_eq_top := by
    -- Suppose that `J` is an ideal of `I`.
    intro J
    -- We first show that `J` is also an ideal of the ambient Lie algebra `L`.
    let J' : LieIdeal R L :=
    { __ := J.toSubmodule.map I.incl.toLinearMap
      lie_mem := by
        rintro x _ ⟨y, hy, rfl⟩
        dsimp
        -- We need to show that `⁅x, y⁆ ∈ J` for any `x ∈ L` and `y ∈ J`.
        -- Since `L` is semisimple, `x` is contained
        -- in the supremum of `I` and the atoms not equal to `I`.
        have hx : x ∈ I ⊔ sSup ({I' : LieIdeal R L | IsAtom I'} \ {I}) := by
          nth_rewrite 1 [← sSup_singleton (a := I)]
          rw [← sSup_union, Set.union_diff_self, Set.union_eq_self_of_subset_left,
            IsSemisimple.sSup_isAtom_eq_top]
          · apply LieSubmodule.mem_top
          · simp only [Set.singleton_subset_iff, Set.mem_setOf_eq, hI]
        -- Hence we can write `x` as `a + b` with `a ∈ I`
        -- and `b` in the supremum of the atoms not equal to `I`.
        rw [LieSubmodule.mem_sup] at hx
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        -- Therefore it suffices to show that `⁅a, y⁆ ∈ J` and `⁅b, y⁆ ∈ J`.
        simp only [add_lie, AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          Submodule.mem_toAddSubmonoid]
        apply add_mem
        -- Now `⁅a, y⁆ ∈ J` since `a ∈ I`, `y ∈ J`, and `J` is an ideal of `I`.
        · simp only [Submodule.mem_map, LieSubmodule.mem_coeSubmodule, Submodule.coeSubtype,
            Subtype.exists, exists_and_right, exists_eq_right, ha, lie_mem_left, exists_true_left]
          exact lie_mem_right R I J ⟨a, ha⟩ y hy
        -- Finally `⁅b, y⁆ = 0`, by the independence of the atoms.
        · suffices ⁅b, y.val⁆ = 0 by simp only [this, zero_mem]
          rw [← LieSubmodule.mem_bot (R := R) (L := L),
              ← (IsSemisimple.setIndependent_isAtom hI).eq_bot]
          exact ⟨lie_mem_right R L I b y y.2, lie_mem_left _ _ _ _ _ hb⟩ }
    -- Now that we know that `J` is an ideal of `L`,
    -- we start with the proof that `I` is a simple Lie algebra.
    -- Assume that `J ≠ ⊤`.
    rw [or_iff_not_imp_right]
    intro hJ
    suffices J' = ⊥ by
      rw [eq_bot_iff] at this ⊢
      intro x hx
      suffices x ∈ J → x = 0 from this hx
      simpa [J'] using @this x.1
    -- We need to show that `J = ⊥`.
    -- Since `J` is an ideal of `L`, and `I` is an atom,
    -- it suffices to show that `J < I`.
    apply hI.2
    rw [lt_iff_le_and_ne]
    constructor
    -- We know that `J ≤ I` since `J` is an ideal of `I`.
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    -- So we need to show `J ≠ I` as ideals of `L`.
    -- This follows from our assumption that `J ≠ ⊤` as ideals of `I`.
    contrapose! hJ
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    rw [← hJ] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hy

variable {R L} in
lemma SemisimpleGenerators.isSemisimple_of_sSup_eq_top
    (S : Set (LieIdeal R L)) (hS : SemisimpleGenerators S) (h : sSup S = ⊤) :
    IsSemisimple R L := by
  obtain rfl := hS.bg.eq_atoms_of_sSup_eq_top h
  constructor
  · exact h
  · exact hS.setIndependent
  · intro I hI
    have := hS.isSimple I hI
    apply IsSimple.non_abelian (R := R)

namespace IsSemisimple

variable [IsSemisimple R L]

lemma semisimpleGenerators_atoms : SemisimpleGenerators {I : LieIdeal R L | IsAtom I} := by
  constructor
  · intro I hI
    exact hI
  · intro I hI
    exact isSimple_of_isAtom I hI
  · apply IsSemisimple.setIndependent_isAtom

variable {R L} in
lemma semisimpleGenerators (S : Set (LieIdeal R L)) (hS : S ⊆ {I : LieIdeal R L | IsAtom I}) :
    SemisimpleGenerators S :=
  (IsSemisimple.semisimpleGenerators_atoms R L).mono hS

instance (priority := 100) instDistribLattice : DistribLattice (LieIdeal R L) :=
  (semisimpleGenerators_atoms R L).bg.distribLattice_of_sSup_eq_top sSup_isAtom_eq_top

noncomputable
instance (priority := 100) instBooleanAlgebra : BooleanAlgebra (LieIdeal R L) :=
  (semisimpleGenerators_atoms R L).bg.booleanAlgebra_of_sSup_eq_top sSup_isAtom_eq_top

/-- A semisimple Lie algebra has trivial radical. -/
instance (priority := 100) instHasTrivialRadical : HasTrivialRadical R L := by
  rw [hasTrivialRadical_iff_no_abelian_ideals]
  intro I hI
  apply (eq_bot_or_exists_atom_le I).resolve_right
  rintro ⟨J, hJ, hJ'⟩
  apply IsSemisimple.non_abelian_of_isAtom J hJ
  constructor
  intro x y
  ext
  simp only [LieIdeal.coe_bracket_of_module, LieSubmodule.coe_bracket, ZeroMemClass.coe_zero]
  have : (⁅(⟨x, hJ' x.2⟩ : I), ⟨y, hJ' y.2⟩⁆ : I) = 0 := trivial_lie_zero _ _ _ _
  apply_fun Subtype.val at this
  exact this

end IsSemisimple

/-- A simple Lie algebra is semisimple. -/
instance (priority := 100) IsSimple.instIsSemisimple [h : IsSimple R L] :
    IsSemisimple R L := by
  constructor
  · simp
  · simpa using CompleteLattice.setIndependent_singleton _
  · intro I hI₁ hI₂
    rw [IsSimple.isAtom_iff_eq_top] at hI₁
    subst I
    obtain @⟨-, h₂⟩ := id h
    rw [lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv] at hI₂
    contradiction

/-- An abelian Lie algebra with trivial radical is trivial. -/
theorem subsingleton_of_hasTrivialRadical_lie_abelian [HasTrivialRadical R L] [h : IsLieAbelian L] :
    Subsingleton L := by
  rw [isLieAbelian_iff_center_eq_top R L, HasTrivialRadical.center_eq_bot] at h
  exact (LieSubmodule.subsingleton_iff R L L).mp (subsingleton_of_bot_eq_top h)
#align lie_algebra.subsingleton_of_semisimple_lie_abelian LieAlgebra.subsingleton_of_hasTrivialRadical_lie_abelian

theorem abelian_radical_of_hasTrivialRadical [HasTrivialRadical R L] :
    IsLieAbelian (radical R L) := by
  rw [HasTrivialRadical.radical_eq_bot]; infer_instance
#align lie_algebra.abelian_radical_of_semisimple LieAlgebra.abelian_radical_of_hasTrivialRadical

/-- The two properties shown to be equivalent here are possible definitions for a Lie algebra
to be reductive.

Note that there is absolutely [no agreement](https://mathoverflow.net/questions/284713/) on what
the label 'reductive' should mean when the coefficients are not a field of characteristic zero. -/
theorem abelian_radical_iff_solvable_is_abelian [IsNoetherian R L] :
    IsLieAbelian (radical R L) ↔ ∀ I : LieIdeal R L, IsSolvable R I → IsLieAbelian I := by
  constructor
  · rintro h₁ I h₂
    rw [LieIdeal.solvable_iff_le_radical] at h₂
    exact (LieIdeal.inclusion_injective h₂).isLieAbelian h₁
  · intro h; apply h; infer_instance
#align lie_algebra.abelian_radical_iff_solvable_is_abelian LieAlgebra.abelian_radical_iff_solvable_is_abelian

theorem ad_ker_eq_bot_of_hasTrivialRadical [HasTrivialRadical R L] : (ad R L).ker = ⊥ := by simp
#align lie_algebra.ad_ker_eq_bot_of_semisimple LieAlgebra.ad_ker_eq_bot_of_hasTrivialRadical

end LieAlgebra
