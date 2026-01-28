/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# The field extension obtained by adjoining pth roots to a field of characteristic p

In this file we construct the extension of a field of characteristic `p` obtained by adjoining
the `p`-th roots of a subset.

## Main definitions

- `adjoin_pth_roots`

## Main results

- `adjoin_pth_roots.finite_of_finite`: if `S` is finite, then `(adjoin_pth_roots p S) / k` is a
  finite field extension

- `adjoin_pth_roots.purelyInseparable`: the field extension `(adjoin_pth_roots p S) / k` is purely
  inseparable

- `adjoin_pth_roots.mem_frobenius_img`: every element of `S` is in the image of the frobenius
  morphism on `adjoin_pth_roots p S`.

-/

@[expose] public section

open IntermediateField

noncomputable section

variable {k : Type*} [Field k]
variable (p : ℕ) [ExpChar k p]

instance : ExpChar (AlgebraicClosure k) p := ExpChar.of_injective_algebraMap' k _

/-- Given a field `k` of exponential characteristic `p` and a subset `S` of `k`, the field
`adjoin_pth_roots p S` is obtained by adjoining all `p`-th roots of elements of `S` to `k`. We
construct this as an object of type `IntermediateField k (AlgebraicClosure k)`, which automatically
gives us the structure of a field and of a `k`-algebra. -/
def IntermediateField.adjoinPthRoots (S : Set k) : IntermediateField k (AlgebraicClosure k) :=
  IntermediateField.adjoin k <|
    (frobenius (AlgebraicClosure k) p) ⁻¹' ((algebraMap k (AlgebraicClosure k)) '' S)

lemma adjoinPthRoots_mono {S T : Set k} (hST : S ⊆ T) :
    adjoinPthRoots p S ≤ adjoinPthRoots p T :=
  IntermediateField.adjoin.mono k _ _ <| Set.preimage_mono <| Set.image_mono hST

/-- If the set `S` whose `p`-th roots we adjoin is finite, then the obtained field extension
`(adjoin_pth_roots p S) / k` is finite. -/
lemma adjoinPthRoots_finite_of_finite (S : Set k) [Finite S] :
    FiniteDimensional k (adjoinPthRoots p S) := by
  -- The set of elements to adjoin to `k` is finite:
  have hFin : Finite ((frobenius (AlgebraicClosure k) p) ⁻¹'
      ((algebraMap k (AlgebraicClosure k)) '' S)) := by
    have hFin' : Finite ((algebraMap k (AlgebraicClosure k)) '' S) := by infer_instance
    exact Set.Finite.preimage (Set.injOn_of_injective (frobenius_inj _ _)) (hFin')
  apply IntermediateField.finiteDimensional_adjoin
  -- It remains to show that every element of the set
  -- `` ((frobenius (AlgebraicClosure k) p) ⁻¹' ((algebraMap k (AlgebraicClosure k)) '' S))``
  -- is integral over `k`.
  intro s hs
  apply IsIntegral.of_pow (n := p) (expChar_pos k p)
  have hs_mem : s ^ p ∈ (algebraMap k (AlgebraicClosure k))'' S := by
    simp_all only [Set.mem_preimage, Set.mem_image]
    obtain ⟨w, hw⟩ := hs
    use w
    rw [hw.2]
    exact ⟨hw.1, rfl⟩
  rw [Set.mem_image] at hs_mem
  obtain ⟨y, hy⟩ := hs_mem
  rw [← hy.2]
  exact isIntegral_algebraMap

/-- The field extension `(adjoin_pth_roots p S) / k` is purely inseparable. -/
instance adjoinPthRoots_purelyInseparable (S : Set k) :
    IsPurelyInseparable k (adjoinPthRoots p S) := by
  unfold adjoinPthRoots
  rw [IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem k (AlgebraicClosure k) p]
  intro s hs
  use 1
  simp_all only [Set.mem_preimage, Set.mem_image, pow_one, RingHom.mem_range]
  obtain ⟨w, h1, h2⟩ := hs
  use w
  rw [h2]
  rfl

/-- If `y ∈ S`, then there is an element `x ∈ adjoin_pth_roots p S` with the property that
`y = x ^ p`. -/
lemma adjoinPthRoots_mem_frobenius_img {S : Set k} {y : k} (hy : y ∈ S) :
    algebraMap k (AlgebraicClosure k) y ∈ Subfield.map (frobenius (AlgebraicClosure k) p)
      (adjoinPthRoots p S).toSubfield := by
  use (frobeniusEquiv (AlgebraicClosure k) p).symm (algebraMap k _ y)
  refine ⟨?_, by simp⟩
  apply Subfield.mem_closure_of_mem
  right
  use y
  exact ⟨hy, by simp⟩

-- a relative version of `adjoin_pth_roots.frob_img_mem`, which allows for
-- `adjoin_pth_roots` to be embedded in the algebraic closure of a bigger field.
lemma adjoinPthRoots_mem_frobenius_img' (K : Type*) [Field K] [Algebra k K] {S : Set k} {y : K}
    (hy : y ∈ (algebraMap k K) '' S) :
    haveI : ExpChar (AlgebraicClosure K) p := ExpChar.of_injective_algebraMap' k _
    algebraMap K (AlgebraicClosure K) y ∈ Subfield.map (frobenius (AlgebraicClosure K) p)
      ((adjoinPthRoots p S).map IsAlgClosed.lift).toSubfield := by
  haveI : ExpChar (AlgebraicClosure K) p := ExpChar.of_injective_algebraMap' k _
  unfold adjoinPthRoots
  rw [Subfield.mem_map]
  use (frobeniusEquiv (AlgebraicClosure K) p).symm (algebraMap K _ y)
  refine ⟨?_, by simp⟩
  simp only [toSubfield_map, Subfield.mem_map, RingHom.coe_coe]
  obtain ⟨z, hz⟩ := (Set.mem_image _ _ _).mp hy
  use (frobeniusEquiv (AlgebraicClosure k) p).symm (algebraMap k _ z)
  constructor
  · apply Subfield.mem_closure_of_mem
    simp only [Set.mem_union, Set.mem_range, Set.mem_preimage, frobenius_apply_frobeniusEquiv_symm,
      Set.mem_image, algebraMap.coe_inj, exists_eq_right]
    exact Or.inr hz.left
  · rw [← hz.2, ← RingHom.coe_coe, RingHom.map_frobeniusEquiv_symm, RingHom.coe_coe,
      AlgHom.commutes]
    rfl
