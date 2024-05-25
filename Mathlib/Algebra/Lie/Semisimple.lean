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

## Main definitions

  * `LieModule.IsIrreducible`
  * `LieAlgebra.IsSimple`
  * `LieAlgebra.HasTrivialRadical`
  * `LieAlgebra.IsSemisimple`
  * `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`
  * `LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals`
  * `LieAlgebra.abelian_radical_iff_solvable_is_abelian`

## Tags

lie algebra, radical, simple, semisimple
-/


universe u v w w₁ w₂

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
  · apply h₁; exact LieAlgebra.ofAbelianIsSolvable R I
  · rw [← abelian_of_solvable_ideal_eq_bot_iff]; apply h₁
    exact abelian_derivedAbelianOfIdeal I
#align lie_algebra.is_semisimple_iff_no_abelian_ideals LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals

@[simp]
theorem HasTrivialRadical.center_eq_bot [HasTrivialRadical R L] : center R L = ⊥ :=
  HasTrivialRadical.eq_bot_of_isSolvable _
#align lie_algebra.center_eq_bot_of_semisimple LieAlgebra.HasTrivialRadical.center_eq_bot

/-- A Lie algebra is simple if it is irreducible as a Lie module over itself via the adjoint
action, and it is non-Abelian. -/
class IsSimple : Prop where
  eq_bot_or_eq_top : ∀ I : LieIdeal R L, I = ⊥ ∨ I = ⊤
  non_abelian : ¬IsLieAbelian L
#align lie_algebra.is_simple LieAlgebra.IsSimple

instance [IsSimple R L] : LieModule.IsIrreducible R L L := by
  have : Nontrivial (LieIdeal R L) := by
    constructor
    by_contra! H
    apply IsSimple.non_abelian R (L := L)
    constructor
    intro x y
    rw [← LieSubmodule.mem_bot (R := R) (L := L), H ⊥ ⊤]
    trivial
  constructor
  apply IsSimple.eq_bot_or_eq_top

variable {R L} in
lemma eq_top_of_isAtom [IsSimple R L] (I : LieIdeal R L) (hI : IsAtom I) : I = ⊤ :=
  (IsSimple.eq_bot_or_eq_top I).resolve_left hI.1

lemma isAtom_top [IsSimple R L] : IsAtom (⊤ : LieIdeal R L) := by
  constructor
  · intro h
    apply IsSimple.non_abelian R (L := L)
    constructor
    intro x y
    rw [← LieSubmodule.mem_bot (R := R) (L := L), ← h]
    trivial
  · intro I hI
    have := IsSimple.eq_bot_or_eq_top I
    contrapose! this
    exact ⟨this, hI.ne⟩

variable {R L} in
lemma isAtom_iff_eq_top [IsSimple R L] (I : LieIdeal R L) : IsAtom I ↔ I = ⊤ :=
  ⟨eq_top_of_isAtom I, fun h ↦ h ▸ isAtom_top R L⟩

instance [IsSimple R L] : HasTrivialRadical R L := by
  rw [hasTrivialRadical_iff_no_abelian_ideals]
  intro I hI
  apply (IsSimple.eq_bot_or_eq_top I).resolve_right
  rintro rfl
  rw [lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv] at hI
  exact IsSimple.non_abelian R (L := L) hI

variable {R L} in
structure SemisimpleGenerators (S : Set (LieIdeal R L)) : Prop where
  isAtom : ∀ I ∈ S, IsAtom I
  isSimple : ∀ I ∈ S, IsSimple R I
  setIndependent : CompleteLattice.SetIndependent S

namespace SemisimpleGenerators

open CompleteLattice

variable {R L}
variable {S : Set (LieIdeal R L)} (hS : SemisimpleGenerators S)

lemma mono {T : Set (LieIdeal R L)} (hTS : T ⊆ S) : SemisimpleGenerators T where
  isAtom I hI := hS.isAtom I (hTS hI)
  isSimple I hI := hS.isSimple I (hTS hI)
  setIndependent := hS.setIndependent.mono hTS

private
lemma compact_step : ∀ s : Finset (LieIdeal R L), ↑s ⊆ S →
    ∀ I : LieIdeal R L, I ≤ s.sup id → ∃ t ⊆ s, I = t.sup id := by
  intro s hs I hI
  obtain rfl | hI := hI.eq_or_lt
  · exact ⟨s, le_rfl, rfl⟩
  obtain ⟨J, hJs, hJI⟩ : ∃ J ∈ s, ¬ J ≤ I := by
    by_contra! H
    exact hI.ne (le_antisymm hI.le (s.sup_le H))
  classical
  let s' := s.erase J
  have hs' : s' ⊂ s := Finset.erase_ssubset hJs
  have hs'S : ↑s' ⊆ S := Set.Subset.trans (Finset.coe_subset.mpr hs'.subset) hs
  suffices I ≤ s'.sup id by
    obtain ⟨t, hts', htI⟩ := compact_step s' hs'S I this
    exact ⟨t, le_trans hts' hs'.subset, htI⟩
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ : ∃ y ∈ id J, ∃ z ∈ s'.sup id, y + z = x := by
    rw [← LieSubmodule.mem_sup, ← Finset.sup_insert, Finset.insert_erase hJs]
    exact hI.le hx
  suffices ⟨y, hy⟩ ∈ LieAlgebra.center R J by
    have _inst := hS.isSimple J (hs hJs)
    rw [HasTrivialRadical.center_eq_bot R J, LieSubmodule.mem_bot] at this
    apply_fun Subtype.val at this
    dsimp at this
    rwa [this, zero_add]
  intro j
  suffices ⁅(j : L), z⁆ = 0 ∧ ⁅(j : L), y + z⁆ = 0 by
    rw [lie_add, this.1, add_zero] at this
    ext
    exact this.2
  rw [← LieSubmodule.mem_bot (R := R) (L := L), ← LieSubmodule.mem_bot (R := R) (L := L)]
  constructor
  · apply (hS.setIndependent.disjoint_sSup (hs hJs) hs'S (Finset.not_mem_erase _ _)).le_bot
    apply LieSubmodule.lie_le_inf
    apply LieSubmodule.lie_mem_lie _ _ j.2
    simpa only [Finset.sup_id_eq_sSup] using hz
  suffices J ⊓ I = ⊥ by
    apply this.le
    apply LieSubmodule.lie_le_inf
    exact LieSubmodule.lie_mem_lie _ _ j.2 hx
  apply ((hS.isAtom J (hs hJs)).le_iff.mp _).resolve_right
  · contrapose! hJI
    rw [← hJI]
    exact inf_le_right
  exact inf_le_left
termination_by s => s.card
decreasing_by
  simp_wf
  exact Finset.card_lt_card hs'

lemma atomistic_helper (J : LieIdeal R L) (hJ : J ≤ sSup S) : ∃ T ⊆ S, J = sSup T := by
  obtain ⟨C, hC, rfl⟩ := IsCompactlyGenerated.exists_sSup_eq J
  suffices ∀ J' : LieIdeal R L, IsCompactElement J' → J' ≤ sSup S → ∃ T ⊆ S, J' = sSup T by
    choose T hT₁ hT₂ using this
    use sSup {T J' h₁ h₂ | (J' ∈ C) (h₁ : IsCompactElement J') (h₂ : J' ≤ sSup S)}
    constructor
    · apply CompleteLattice.sSup_le
      rintro _ ⟨J', -, h₁, h₂, rfl⟩
      apply hT₁
    · apply le_antisymm
      · apply CompleteLattice.sSup_le
        intro J' hJ'
        rw [hT₂ J' (hC _ hJ') ((le_sSup hJ').trans hJ)]
        apply sSup_le_sSup
        apply CompleteLattice.le_sSup
        use J', hJ', hC _ hJ', (le_sSup hJ').trans hJ
      · simp only [Set.sSup_eq_sUnion, sSup_le_iff, Set.mem_sUnion, Set.mem_setOf_eq,
          forall_exists_index, and_imp]
        rintro I T J' hJ'C hJ' hJ'S rfl hIT
        apply (le_sSup hIT).trans
        rw [← hT₂]
        exact le_sSup hJ'C
  clear hJ hC C
  intro J hJ hJS
  obtain ⟨s, hs₁, hs₂⟩ := hJ S hJS
  obtain ⟨t, ht, rfl⟩ := hS.compact_step s hs₁ J hs₂
  refine ⟨t, ?_, Finset.sup_id_eq_sSup t⟩
  refine Set.Subset.trans ?_ hs₁
  simpa only [Finset.coe_subset] using ht

lemma mem_of_isAtom_of_le_sSup_atoms (I : LieIdeal R L) (hI : IsAtom I) (hJ : I ≤ sSup S) :
    I ∈ S := by
  obtain ⟨T, hT, rfl⟩ := hS.atomistic_helper I hJ
  obtain rfl | ⟨I, hIT⟩ := T.eq_empty_or_nonempty
  · simp only [sSup_empty] at hI
    exact (hI.1 rfl).elim
  suffices sSup T = I from this ▸ hT hIT
  have hIJ : I ≤ sSup T := le_sSup hIT
  rwa [hI.le_iff_eq, eq_comm] at hIJ
  exact (hS.isAtom I (hT hIT)).1

lemma sSup_le_sSup_iff_of_atoms (X Y : Set (LieIdeal R L)) (hX : X ⊆ S) (hY : Y ⊆ S) :
    sSup X ≤ sSup Y ↔ X ⊆ Y := by
  refine ⟨?_, sSup_le_sSup⟩
  intro h I hI
  apply (hS.mono hY).mem_of_isAtom_of_le_sSup_atoms _ _ ((le_sSup hI).trans h)
  exact (hS.mono hX).isAtom I hI

lemma eq_atoms_of_sSup_eq_top (h : sSup S = ⊤) : S = {I : LieIdeal R L | IsAtom I} := by
  apply le_antisymm
  · exact hS.isAtom
  intro J hJ
  obtain ⟨T, hT, rfl⟩ := hS.atomistic_helper J (le_top.trans h.ge)
  exact hS.mem_of_isAtom_of_le_sSup_atoms _ hJ (sSup_le_sSup hT)

lemma isAtomistic_of_sSup_eq_top (h : sSup S = ⊤) : IsAtomistic (LieIdeal R L) := by
  constructor
  intro I
  obtain ⟨T, hT, rfl⟩ := hS.atomistic_helper I (le_top.trans h.ge)
  exact ⟨T, rfl, (hS.mono hT).isAtom⟩

lemma complementedLattice_of_sSup_eq_top (h : sSup S = ⊤) : ComplementedLattice (LieIdeal R L) := by
  constructor
  intro I
  obtain ⟨T, hT, rfl⟩ := hS.atomistic_helper I (le_top.trans h.ge)
  use sSup (S \ T)
  constructor
  swap
  · rw [codisjoint_iff, ← sSup_union, Set.union_diff_self, Set.union_eq_right.mpr hT, h]
  intro J hJ₁ hJ₂
  obtain ⟨X, hX, rfl⟩ := hS.atomistic_helper J (le_top.trans h.ge)
  rw [hS.sSup_le_sSup_iff_of_atoms _ _ hX] at hJ₁ hJ₂
  · obtain rfl : X = ∅ := by
      have := Set.disjoint_sdiff_right hJ₁ hJ₂
      rwa [← eq_bot_iff] at this
    simp only [sSup_empty, le_refl]
  · exact Set.diff_subset _ _
  · exact hT

end SemisimpleGenerators

/--
A *semisimple* Lie algebra is one that is a direct sum of simple Lie algebras.

Note that the label 'semisimple' is apparently not universally agreed
[upon](https://mathoverflow.net/questions/149391/on-radicals-of-a-lie-algebra#comment383669_149391)
for general coefficients.

For example [Seligman, page 15](seligman1967) uses the label for `LieAlgebra.HasTrivialRadical`,
the weakest of the various properties which are all equivalent over a field of characteristic zero.
-/
class IsSemisimple : Prop where
  sSup_isAtom_eq_top : sSup {I : LieIdeal R L | IsAtom I} = ⊤
  setIndependent_isAtom : CompleteLattice.SetIndependent {I : LieIdeal R L | IsAtom I}
  non_abelian_of_isAtom : ∀ I : LieIdeal R L, IsAtom I → ¬ IsLieAbelian I

variable {R L} in
lemma isSimple_of_isAtom [IsSemisimple R L] (I : LieIdeal R L) (hI : IsAtom I) : IsSimple R I where
    non_abelian := IsSemisimple.non_abelian_of_isAtom I hI
    eq_bot_or_eq_top := by
      intro J
      let J' : LieIdeal R L :=
      { __ := J.toSubmodule.map I.incl.toLinearMap
        lie_mem := by
          rintro x _ ⟨y, hy, rfl⟩
          dsimp
          have hx : x ∈ I ⊔ sSup ({I' : LieIdeal R L | IsAtom I'} \ {I}) := by
            nth_rewrite 1 [← sSup_singleton (a := I)]
            rw [← sSup_union, Set.union_diff_self, Set.union_eq_self_of_subset_left,
              IsSemisimple.sSup_isAtom_eq_top]
            · apply LieSubmodule.mem_top
            · simp only [Set.singleton_subset_iff, Set.mem_setOf_eq, hI]
          rw [LieSubmodule.mem_sup] at hx
          obtain ⟨a, ha, b, hb, rfl⟩ := hx
          simp only [add_lie, AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
            Submodule.mem_toAddSubmonoid]
          apply add_mem
          · simp only [Submodule.mem_map, LieSubmodule.mem_coeSubmodule, Submodule.coeSubtype,
              Subtype.exists, exists_and_right, exists_eq_right, ha, lie_mem_left, exists_true_left]
            exact lie_mem_right R I J ⟨a, ha⟩ y hy
          · suffices ⁅b, y.val⁆ = 0 by simp only [this, zero_mem]
            rw [← LieSubmodule.mem_bot (R := R) (L := L),
                ← (IsSemisimple.setIndependent_isAtom hI).eq_bot]
            exact ⟨lie_mem_right R L I b y y.2, lie_mem_left _ _ _ _ _ hb⟩ }
      rw [or_iff_not_imp_right]
      intro hJ
      suffices J' = ⊥ by
        have aux : (fun J : LieIdeal R I ↦ J.toSubmodule.map I.incl.toLinearMap).Injective := by
          intro J₁ J₂ h
          ext x
          rw [SetLike.ext_iff] at h
          specialize h x
          simpa only [LieIdeal.incl_coe, LieIdeal.coe_to_lieSubalgebra_to_submodule,
            Submodule.mem_map, LieSubmodule.mem_coeSubmodule, Submodule.coeSubtype,
            SetLike.coe_eq_coe, exists_eq_right] using h
        apply aux
        simpa [J'] using this
      apply hI.2
      rw [lt_iff_le_and_ne]
      constructor
      · rintro _ ⟨x, -, rfl⟩
        exact x.2
      contrapose! hJ
      rw [eq_top_iff]
      rintro ⟨x, hx⟩ -
      rw [← hJ] at hx
      rcases hx with ⟨y, hy, rfl⟩
      exact hy

lemma IsSemisimple.semisimpleGenerators [IsSemisimple R L]
    (S : Set (LieIdeal R L)) (hS : S ⊆ {I : LieIdeal R L | IsAtom I}) :
    SemisimpleGenerators S := by
  apply SemisimpleGenerators.mono _ hS
  constructor
  · intro I hI
    exact hI
  · intro I hI
    exact isSimple_of_isAtom I hI
  · apply IsSemisimple.setIndependent_isAtom

lemma SemisimpleGenerators.isSemisimple_of_sSup_eq_top
    (S : Set (LieIdeal R L)) (hS : SemisimpleGenerators S) (h : sSup S = ⊤) :
    IsSemisimple R L := by
  obtain rfl := hS.eq_atoms_of_sSup_eq_top h
  constructor
  · exact h
  · exact hS.setIndependent
  · intro I hI
    have := hS.isSimple I hI
    apply IsSimple.non_abelian (R := R)

-- move this to `Mathlib.Order.SupIndep`
lemma _root_.CompleteLattice.setIndependent_singleton {α : Type w} [CompleteLattice α] (a : α) :
    CompleteLattice.SetIndependent ({a} : Set α) := by
  intro i hi
  simp_all

/-- A simple Lie algebra is semisimple. -/
instance (priority := 100) isSemisimple_of_isSimple [h : IsSimple R L] :
    IsSemisimple R L := by
  have aux : {I : LieIdeal R L | IsAtom I} = {⊤} := by
    simp only [isAtom_iff_eq_top, Set.setOf_eq_eq_singleton]
  constructor
  · simp [aux]
  · simpa [aux] using _root_.CompleteLattice.setIndependent_singleton _
  · intro I hI₁ hI₂
    rw [isAtom_iff_eq_top] at hI₁
    subst I
    obtain @⟨-, h₂⟩ := id h
    rw [lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv] at hI₂
    contradiction

instance (priority := 100) [IsSemisimple R L] : DistribLattice (LieIdeal R L) where
  __ := (inferInstance : CompleteLattice (LieIdeal R L))
  le_sup_inf I₁ I₂ I₃ := by
    sorry

instance (priority := 100) [IsSemisimple R L] :
    ComplementedLattice (LieIdeal R L) := by
  apply SemisimpleGenerators.complementedLattice_of_sSup_eq_top (S := {I : LieIdeal R L | IsAtom I})
  · exact IsSemisimple.semisimpleGenerators _ _ _ le_rfl
  · exact IsSemisimple.sSup_isAtom_eq_top

/-- A semisimple Lie algebra has trivial radical. -/
instance (priority := 100) hasTrivialRadical_of_isSemisimple [IsSemisimple R L] :
    HasTrivialRadical R L := by
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

/-- A simple Lie algebra has trivial radical. -/
instance (priority := 100) hasTrivialRadical_of_isSimple [IsSimple R L] :
    HasTrivialRadical R L := inferInstance
#align lie_algebra.is_semisimple_of_is_simple LieAlgebra.hasTrivialRadical_of_isSimple

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
