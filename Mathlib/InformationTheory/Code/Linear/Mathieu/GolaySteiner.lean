import Mathlib.InformationTheory.Code.Linear.Mathieu.BGolay
import Mathlib.InformationTheory.SteinerSystem.Basic


namespace golay_code_space'
variable (x:golay_code_space')

#check (x:Set golay_code_index)


lemma min_dist_eq_8 : ∀ x ∈ GolayCode,∀ y ∈ GolayCode, x ≠ y → 8 ≤ addGNorm hdist (x - y) := by
  intro x hx y hy hne
  have hz : x - y ∈ GolayCode := by
    apply sub_mem hx hy
  have hnzero : x - y ≠ 0 := by exact sub_ne_zero.mpr hne


  sorry

-- #synth Fintype HexaCode

/-
consider cosets of GolayCode, i.e. x +ᵥ GolayCode for (x:golay_code_space').
since Fintype.card golay_code_space' = 2 ^ 24 while Fintype.card GolayCode = 2 ^ 12,
we must have 2 ^ (24-12) = 4096 cosets.

then given that w(x) < 4, x is the only element with w(y) ≤ 4 property in x +ᵥ GolayCode.
this is because for y ∈ x +ᵥ GolayCode, x-y ∈ GolayCode (or x + y), and therefore if x ≠ y, w(x-y) ≥ 8.
reverse triangle inequality then says that w(x+y) - w(x) ≤ w(y),meaning w(y) ≥ 5.

there is
- 1 word of weight 0,
- 24 words of weight 1,
- 24\*23/2 = 12 * 23 = 276 words of weight 2, and
- 24\*23\*22/6 = 8 * 23 \* 11 = 11 \* (8 * (25 - 2)) = 11 ⋆ (200 - 16) = 2200 - 176
  = 2024 of weight 3

total: 1 + 24 + 276 + 2024 = 1 + 276 + 2048 = 1 + 2324 = 2325

remaining are:

words of weight 4.
- there are 24⋆ 23 ⋆ 22 ⋆ 21 / (4 * 3 *2 ) = 23 * 22 * 21 = 10626 of these words.
if these words overlap, their difference has a weight of less than 8, therefore
these don't overlap in cosets. therefore, at most 24/4=6 of these words are in one coset.
therefore, there are at least 10626/6=5313/3=1771 cosets containing words of weight 4.

since we know of 2325 cosets already, and there are at least 1771 additional ones, that means
we know of at least 2325 + 1771 = 4096 cosets, which is exactly all of them.
therefore, every coset with words of weight 4 has exactly 6 such words, forming a partition.

we can identify these partitions with their cosets, and look at the action of 2^6:3•S₆ on these cosets.
the first orbit is the coset given by:
!![1,0,0,0,0,0;
  1,0,0,0,0,0;
  1,0,0,0,0,0;
  1,0,0,0,0,0]
the second orbit is given by:
!![1,0,0,0,0,0;
  1,0,0,0,0,0;
  0,1,0,0,0,0;
  0,1,0,0,0,0]

the third orbit is given by:
!![1,0,0,0,0,0;
  1,0,0,0,0,0;
  1,0,0,0,0,0;
  0,1,0,0,0,0]

the fourth orbit is given by:
!![1,1,1,0,0,0;
  1,0,0,0,0,0;
  0,0,0,0,0,0;
  0,0,0,0,0,0]

these orbits fuse with the following permutation:

!![m (0,0), m (1,0), m (2,0), m (3,0), m (5,1), m (4,1);
   m (0,1), m (1,1), m (2,1), m (3,1), m (5,0), m (4,0);
   m (1,ω), m (0,ω), m (3,ω), m (2,ω), m(4,ω⁻¹),m(5,ω⁻¹);
   m(1,ω⁻¹),m(0,ω⁻¹),m(3,ω⁻¹),m(2,ω⁻¹),m (4,ω), m (5,ω)]

you can see this by checking. this permutation also preserves the code

then 2⁶:3⬝S₆, adjoint this new permutation, gives M24.

idea: you can check that two (distjoint) words of weight 4 are in the same coset by
  checking that the union is an octad in the GolayCode.

classification of octads:
- odd parity -> one column with 3, the rest has 1. spreading appropriately to have to_hexacode work.


lemma: 2⁶:3⬝S₆ is the full sextet stabiliser, i.e. given some coset x + GolayCode,
  where w(x)=4, y • (x + GolayCode) = x + GolayCode ↔ y ∈ 2⁶:3⬝S₆. somehow.


-/

-- lemma eq_one_of_ne_zero (x:ZMod 2) : x ≠ 0 ↔ x = 1 := by
--   fin_cases x <;> simp only [Fin.zero_eta, ne_eq, not_true_eq_false, zero_ne_one,
--     IsEmpty.forall_iff,Fin.mk_one, one_ne_zero, not_false_eq_true, forall_true_left]

-- def octads : Steiner 5 8 golay_code_index where
--   carrier := {s | ∃ x ∈ GolayCode, s = x.to_finset ∧ hdist 0 x = 8}
--   blocks_have_size := fun b => by
--     simp only [hammingENatdist_eq_cast_hammingDist, hammingDist_zero_left, Set.mem_setOf_eq,
--       forall_exists_index, and_imp]
--     intro x hx
--     rintro rfl
--     simp_rw [hammingNorm, eq_one_of_ne_zero, to_finset]
--     simp only [Set.mem_setOf_eq]
--     suffices hsuf :
--         Finset.filter (fun x_1 ↦ x x_1 = 1) Finset.univ = Set.toFinset {x_1 | x x_1 = 1} by
--       rw [hsuf]
--       obtain h8 : (8:ℕ∞) = (8 : ℕ) := by rfl
--       rw [h8, Nat.cast_inj]
--       exact id
--     ext a
--     rw [Set.mem_toFinset]
--     simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
--   blocks_are_unique := sorry

end golay_code_space'
