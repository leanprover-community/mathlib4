/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Order.BooleanGenerators

/-!
# Semisimple Lie algebras

The famous Cartan-Dynkin-Killing classification of semisimple Lie algebras renders them one of the
most important classes of Lie algebras. In this file we prove basic results
about simple and semisimple Lie algebras.

## Main declarations

* `LieAlgebra.IsSemisimple.instHasTrivialRadical`: A semisimple Lie algebra has trivial radical.
* `LieAlgebra.IsSemisimple.instBooleanAlgebra`:
  The lattice of ideals in a semisimple Lie algebra is a Boolean algebra.
  In particular, this implies that the lattice of ideals is atomistic:
  every ideal is a direct sum of atoms (simple ideals) in a unique way.
* `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`
* `LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals`
* `LieAlgebra.abelian_radical_iff_solvable_is_abelian`

## Tags

lie algebra, radical, simple, semisimple
-/

section Irreducible

variable (R L M : Type*) [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]

lemma LieModule.nontrivial_of_isIrreducible [LieModule.IsIrreducible R L M] : Nontrivial M where
  exists_pair_ne := by
    have aux : (⊥ : LieSubmodule R L M) ≠ ⊤ := bot_ne_top
    contrapose! aux
    ext m
    simpa using aux m 0

end Irreducible

namespace LieAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {R L} in
theorem HasTrivialRadical.eq_bot_of_isSolvable [HasTrivialRadical R L]
    (I : LieIdeal R L) [hI : IsSolvable I] : I = ⊥ :=
  sSup_eq_bot.mp radical_eq_bot _ hI

instance [HasTrivialRadical R L] : LieModule.IsFaithful R L L := by
  rw [isFaithful_self_iff]
  exact HasTrivialRadical.eq_bot_of_isSolvable _

variable {R L} in
theorem hasTrivialRadical_of_no_solvable_ideals (h : ∀ I : LieIdeal R L, IsSolvable I → I = ⊥) :
    HasTrivialRadical R L :=
  ⟨sSup_eq_bot.mpr h⟩

theorem hasTrivialRadical_iff_no_solvable_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsSolvable I → I = ⊥ :=
  ⟨@HasTrivialRadical.eq_bot_of_isSolvable _ _ _ _ _, hasTrivialRadical_of_no_solvable_ideals⟩

theorem hasTrivialRadical_iff_no_abelian_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsLieAbelian I → I = ⊥ := by
  rw [hasTrivialRadical_iff_no_solvable_ideals]
  constructor <;> intro h₁ I h₂
  · exact h₁ _ <| LieAlgebra.ofAbelianIsSolvable I
  · rw [← abelian_of_solvable_ideal_eq_bot_iff]
    exact h₁ _ <| abelian_derivedAbelianOfIdeal I

namespace IsSimple

variable [IsSimple R L]

instance : LieModule.IsIrreducible R L L := by
  suffices Nontrivial (LieIdeal R L) from ⟨IsSimple.eq_bot_or_eq_top⟩
  rw [LieSubmodule.nontrivial_iff, ← not_subsingleton_iff_nontrivial]
  have _i : ¬ IsLieAbelian L := IsSimple.non_abelian R
  contrapose! _i
  infer_instance

protected lemma isAtom_top : IsAtom (⊤ : LieIdeal R L) := isAtom_top

variable {R L} in
protected lemma isAtom_iff_eq_top (I : LieIdeal R L) : IsAtom I ↔ I = ⊤ := isAtom_iff_eq_top

variable {R L} in
lemma eq_top_of_isAtom (I : LieIdeal R L) (hI : IsAtom I) : I = ⊤ := isAtom_iff_eq_top.mp hI

instance : HasTrivialRadical R L := by
  rw [hasTrivialRadical_iff_no_abelian_ideals]
  intro I hI
  apply (IsSimple.eq_bot_or_eq_top I).resolve_right
  rintro rfl
  rw [lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv] at hI
  exact IsSimple.non_abelian R (L := L) hI

end IsSimple

namespace IsSemisimple

open CompleteLattice IsCompactlyGenerated

variable {R L}
variable [IsSemisimple R L]

lemma isSimple_of_isAtom (I : LieIdeal R L) (hI : IsAtom I) : IsSimple R I where
  non_abelian := IsSemisimple.non_abelian_of_isAtom I hI
  eq_bot_or_eq_top := by
    -- Suppose that `J` is an ideal of `I`.
    intro J
    -- We first show that `J` is also an ideal of the ambient Lie algebra `L`.
    let J' : LieIdeal R L :=
    { __ := J.toSubmodule.map I.incl.toLinearMap
      lie_mem := by
        rintro x _ ⟨y, hy, rfl⟩
        -- We need to show that `⁅x, y⁆ ∈ J` for any `x ∈ L` and `y ∈ J`.
        -- Since `L` is semisimple, `x` is contained
        -- in the supremum of `I` and the atoms not equal to `I`.
        have hx : x ∈ I ⊔ sSup ({I' : LieIdeal R L | IsAtom I'} \ {I}) := by
          nth_rewrite 1 [← sSup_singleton (a := I)]
          rw [← sSup_union, Set.union_diff_self, Set.union_eq_self_of_subset_left,
            IsSemisimple.sSup_atoms_eq_top]
          · apply LieSubmodule.mem_top
          · simp only [Set.singleton_subset_iff, Set.mem_setOf_eq, hI]
        -- Hence we can write `x` as `a + b` with `a ∈ I`
        -- and `b` in the supremum of the atoms not equal to `I`.
        rw [LieSubmodule.mem_sup] at hx
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        -- Therefore it suffices to show that `⁅a, y⁆ ∈ J` and `⁅b, y⁆ ∈ J`.
        simp only [Submodule.carrier_eq_coe, add_lie, SetLike.mem_coe]
        apply add_mem
        -- Now `⁅a, y⁆ ∈ J` since `a ∈ I`, `y ∈ J`, and `J` is an ideal of `I`.
        · simp only [Submodule.mem_map, LieSubmodule.mem_toSubmodule, Subtype.exists]
          erw [Submodule.coe_subtype]
          simp only [exists_and_right, exists_eq_right, ha, lie_mem_left, exists_true_left]
          exact lie_mem_right R I J ⟨a, ha⟩ y hy
        -- Finally `⁅b, y⁆ = 0`, by the independence of the atoms.
        · suffices ⁅b, y.val⁆ = 0 by erw [this]; simp only [zero_mem]
          rw [← LieSubmodule.mem_bot (R := R) (L := L),
              ← (IsSemisimple.sSupIndep_isAtom hI).eq_bot]
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
      have := @this x.1
      simp only [LieIdeal.incl_coe, LieIdeal.toLieSubalgebra_toSubmodule,
        LieSubmodule.mem_mk_iff', Submodule.mem_map, LieSubmodule.mem_toSubmodule, Subtype.exists,
        LieSubmodule.mem_bot, ZeroMemClass.coe_eq_zero, forall_exists_index, and_imp, J'] at this
      exact fun _ ↦ this (↑x) x.property hx rfl
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

/--
In a semisimple Lie algebra,
Lie ideals that are contained in the supremum of a finite collection of atoms
are themselves the supremum of a finite subcollection of those atoms.

By a compactness argument, this statement can be extended to arbitrary sets of atoms.
See `atomistic`.

The proof is by induction on the finite set of atoms.
-/
private
lemma finitelyAtomistic : ∀ s : Finset (LieIdeal R L), ↑s ⊆ {I : LieIdeal R L | IsAtom I} →
    ∀ I : LieIdeal R L, I ≤ s.sup id → ∃ t ⊆ s, I = t.sup id := by
  intro s hs I hI
  let S := {I : LieIdeal R L | IsAtom I}
  obtain rfl | hI := hI.eq_or_lt
  · exact ⟨s, Finset.Subset.rfl, rfl⟩
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
    obtain ⟨t, hts', htI⟩ := finitelyAtomistic s' hs'S I this
    exact ⟨t, hts'.trans hs'.subset, htI⟩
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
    have _inst := isSimple_of_isAtom J (hs hJs)
    simp_all
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
  · apply (sSupIndep_isAtom.disjoint_sSup (hs hJs) hs'S (Finset.notMem_erase _ _)).le_bot
    apply LieSubmodule.lie_le_inf
    apply LieSubmodule.lie_mem_lie j.2
    simpa only [K, Finset.sup_id_eq_sSup] using hz
  -- By similar reasoning, `j` brackets to `0` with `x = y + z ∈ I`, if we show `J ⊓ I = ⊥`.
  suffices J ⊓ I = ⊥ by
    apply this.le
    apply LieSubmodule.lie_le_inf
    exact LieSubmodule.lie_mem_lie j.2 hx
  -- Indeed `J ⊓ I = ⊥`, since `J` is an atom that is not contained in `I`.
  apply ((hs hJs).le_iff.mp _).resolve_right
  · contrapose! hJI
    rw [← hJI]
    exact inf_le_right
  exact inf_le_left
termination_by s => s.card
decreasing_by exact Finset.card_lt_card hs'

variable (R L) in
lemma booleanGenerators : BooleanGenerators {I : LieIdeal R L | IsAtom I} where
  isAtom _ hI := hI
  finitelyAtomistic _ _ hs _ hIs := finitelyAtomistic _ hs _ hIs

instance (priority := 100) instDistribLattice : DistribLattice (LieIdeal R L) :=
  (booleanGenerators R L).distribLattice_of_sSup_eq_top sSup_atoms_eq_top

noncomputable
instance (priority := 100) instBooleanAlgebra : BooleanAlgebra (LieIdeal R L) :=
  (booleanGenerators R L).booleanAlgebra_of_sSup_eq_top sSup_atoms_eq_top

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
instance (priority := 100) IsSimple.instIsSemisimple [IsSimple R L] :
    IsSemisimple R L := by
  constructor
  · simp
  · simpa using sSupIndep_singleton _
  · intro I hI₁ hI₂
    apply IsSimple.non_abelian (R := R) (L := L)
    rw [IsSimple.isAtom_iff_eq_top] at hI₁
    rwa [hI₁, lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv] at hI₂

/-- An abelian Lie algebra with trivial radical is trivial. -/
theorem subsingleton_of_hasTrivialRadical_lie_abelian [HasTrivialRadical R L] [h : IsLieAbelian L] :
    Subsingleton L := by
  rw [isLieAbelian_iff_center_eq_top R L, center_eq_bot] at h
  exact (LieSubmodule.subsingleton_iff R L L).mp (subsingleton_of_bot_eq_top h)

theorem abelian_radical_of_hasTrivialRadical [HasTrivialRadical R L] :
    IsLieAbelian (radical R L) := by
  rw [HasTrivialRadical.radical_eq_bot]; exact LieIdeal.isLieAbelian_of_trivial ..

theorem abelian_radical_iff_solvable_is_abelian [IsNoetherian R L] :
    IsLieAbelian (radical R L) ↔ ∀ I : LieIdeal R L, IsSolvable I → IsLieAbelian I := by
  constructor
  · rintro h₁ I h₂
    rw [LieIdeal.solvable_iff_le_radical] at h₂
    exact (LieIdeal.inclusion_injective h₂).isLieAbelian h₁
  · intro h; apply h; infer_instance

theorem ad_ker_eq_bot_of_hasTrivialRadical [HasTrivialRadical R L] : (ad R L).ker = ⊥ := by simp

end LieAlgebra
