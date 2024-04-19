import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.Ideal.Operations

namespace AlgHom

open BigOperators

universe u u' v w w'

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'} [CommSemiring R] [Semiring A] [Algebra R A]
  [Semiring B] [Algebra R B] [Semiring C] [Algebra R C] (φ : A →ₐ[R] B)

theorem ker_rangeRestrict (f : A →ₐ[R] B) : RingHom.ker f.rangeRestrict = RingHom.ker f :=
  Ideal.ext fun _ ↦ Subtype.ext_iff

end AlgHom

namespace Subalgebra

open BigOperators Algebra

universe u u' v w w'

variable {R : Type u} {A : Type v} {B : Type w} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  (S : Subalgebra R A)

/-- Suppose we are given `∑ i, lᵢ * sᵢ = 1` in `S`, and `S'` a subalgebra of `S` that contains
`lᵢ` and `sᵢ`. To check that an `x : S` falls in `S'`, we only need to show that
`sᵢ ^ n • x ∈ S'` for some `n` for each `sᵢ`. -/
theorem mem_of_finset_sum_eq_one_of_pow_smul_mem {S : Type*} [CommRing S] [Algebra R S]
    (S' : Subalgebra R S) {ι : Type*} (ι' : Finset ι) (s : ι → S) (l : ι → S)
    (e : ∑ i in ι', l i * s i = 1) (hs : ∀ i, s i ∈ S') (hl : ∀ i, l i ∈ S') (x : S)
    (H : ∀ i, ∃ n : ℕ, (s i ^ n : S) • x ∈ S') : x ∈ S' := by
  -- Porting note: needed to add this instance
  let _i : Algebra { x // x ∈ S' } { x // x ∈ S' } := Algebra.id _
  suffices x ∈ Subalgebra.toSubmodule (Algebra.ofId S' S).range by
    obtain ⟨x, rfl⟩ := this
    exact x.2
  choose n hn using H
  let s' : ι → S' := fun x => ⟨s x, hs x⟩
  let l' : ι → S' := fun x => ⟨l x, hl x⟩
  have e' : ∑ i in ι', l' i * s' i = 1 := by
    ext
    show S'.subtype (∑ i in ι', l' i * s' i) = 1
    simpa only [map_sum, map_mul] using e
  have : Ideal.span (s' '' ι') = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← e']
    apply sum_mem
    intros i hi
    exact Ideal.mul_mem_left _ _ <| Ideal.subset_span <| Set.mem_image_of_mem s' hi
  let N := ι'.sup n
  have hN := Ideal.span_pow_eq_top _ this N
  apply (Algebra.ofId S' S).range.toSubmodule.mem_of_span_top_of_smul_mem _ hN
  rintro ⟨_, _, ⟨i, hi, rfl⟩, rfl⟩
  change s' i ^ N • x ∈ _
  rw [← tsub_add_cancel_of_le (show n i ≤ N from Finset.le_sup hi), pow_add, mul_smul]
  refine' Submodule.smul_mem _ (⟨_, pow_mem (hs i) _⟩ : S') _
  exact ⟨⟨_, hn i⟩, rfl⟩
#align subalgebra.mem_of_finset_sum_eq_one_of_pow_smul_mem Subalgebra.mem_of_finset_sum_eq_one_of_pow_smul_mem

theorem mem_of_span_eq_top_of_smul_pow_mem {S : Type*} [CommRing S] [Algebra R S]
    (S' : Subalgebra R S) (s : Set S) (l : s →₀ S) (hs : Finsupp.total s S S (↑) l = 1)
    (hs' : s ⊆ S') (hl : ∀ i, l i ∈ S') (x : S) (H : ∀ r : s, ∃ n : ℕ, (r : S) ^ n • x ∈ S') :
    x ∈ S' :=
  mem_of_finset_sum_eq_one_of_pow_smul_mem S' l.support (↑) l hs (fun x => hs' x.2) hl x H
#align subalgebra.mem_of_span_eq_top_of_smul_pow_mem Subalgebra.mem_of_span_eq_top_of_smul_pow_mem

end Subalgebra
