/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathlib.Topology.StoneCech
import Mathlib.Topology.Algebra.Semigroup
import Mathlib.Data.Stream.Init

#align_import combinatorics.hindman from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Hindman's theorem on finite sums

We prove Hindman's theorem on finite sums, using idempotent ultrafilters.

Given an infinite sequence `a₀, a₁, a₂, …` of positive integers, the set `FS(a₀, …)` is the set
of positive integers that can be expressed as a finite sum of `aᵢ`'s, without repetition. Hindman's
theorem asserts that whenever the positive integers are finitely colored, there exists a sequence
`a₀, a₁, a₂, …` such that `FS(a₀, …)` is monochromatic. There is also a stronger version, saying
that whenever a set of the form `FS(a₀, …)` is finitely colored, there exists a sequence
`b₀, b₁, b₂, …` such that `FS(b₀, …)` is monochromatic and contained in `FS(a₀, …)`. We prove both
these versions for a general semigroup `M` instead of `ℕ+` since it is no harder, although this
special case implies the general case.

The idea of the proof is to extend the addition `(+) : M → M → M` to addition `(+) : βM → βM → βM`
on the space `βM` of ultrafilters on `M`. One can prove that if `U` is an _idempotent_ ultrafilter,
i.e. `U + U = U`, then any `U`-large subset of `M` contains some set `FS(a₀, …)` (see
`exists_FS_of_large`). And with the help of a general topological argument one can show that any set
of the form `FS(a₀, …)` is `U`-large according to some idempotent ultrafilter `U` (see
`exists_idempotent_ultrafilter_le_FS`). This is enough to prove the theorem since in any finite
partition of a `U`-large set, one of the parts is `U`-large.

## Main results

- `FS_partition_regular`: the strong form of Hindman's theorem
- `exists_FS_of_finite_cover`: the weak form of Hindman's theorem

## Tags

Ramsey theory, ultrafilter

-/


open Filter

/-- Multiplication of ultrafilters given by `∀ᶠ m in U*V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m*m')`. -/
@[to_additive
      "Addition of ultrafilters given by `∀ᶠ m in U+V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m+m')`."]
def Ultrafilter.mul {M} [Mul M] : Mul (Ultrafilter M) where mul U V := (· * ·) <$> U <*> V
#align ultrafilter.has_mul Ultrafilter.mul
#align ultrafilter.has_add Ultrafilter.add

attribute [local instance] Ultrafilter.mul Ultrafilter.add

/- We could have taken this as the definition of `U * V`, but then we would have to prove that it
defines an ultrafilter. -/
@[to_additive]
theorem Ultrafilter.eventually_mul {M} [Mul M] (U V : Ultrafilter M) (p : M → Prop) :
    (∀ᶠ m in ↑(U * V), p m) ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m * m') :=
  Iff.rfl
#align ultrafilter.eventually_mul Ultrafilter.eventually_mul
#align ultrafilter.eventually_add Ultrafilter.eventually_add

/-- Semigroup structure on `Ultrafilter M` induced by a semigroup structure on `M`. -/
@[to_additive
      "Additive semigroup structure on `Ultrafilter M` induced by an additive semigroup
      structure on `M`."]
def Ultrafilter.semigroup {M} [Semigroup M] : Semigroup (Ultrafilter M) :=
  { Ultrafilter.mul with
    mul_assoc := fun U V W =>
      Ultrafilter.coe_inj.mp <|
        -- porting note: `simp` was slow to typecheck, replaced by `simp_rw`
        Filter.ext' fun p => by simp_rw [Ultrafilter.eventually_mul, mul_assoc] }
                                -- 🎉 no goals
#align ultrafilter.semigroup Ultrafilter.semigroup
#align ultrafilter.add_semigroup Ultrafilter.addSemigroup

attribute [local instance] Ultrafilter.semigroup Ultrafilter.addSemigroup

-- We don't prove `continuous_mul_right`, because in general it is false!
@[to_additive]
theorem Ultrafilter.continuous_mul_left {M} [Semigroup M] (V : Ultrafilter M) :
    Continuous (· * V) :=
  TopologicalSpace.IsTopologicalBasis.continuous ultrafilterBasis_is_basis _ <|
    Set.forall_range_iff.mpr fun s => ultrafilter_isOpen_basic { m : M | ∀ᶠ m' in V, m * m' ∈ s }
#align ultrafilter.continuous_mul_left Ultrafilter.continuous_mul_left
#align ultrafilter.continuous_add_left Ultrafilter.continuous_add_left

namespace Hindman

-- porting note: mathport wants these names to be `fS`, `fP`, etc, but this does violence to
-- mathematical naming conventions, as does `fs`, `fp`, so we just followed `mathlib` 3 here

/-- `FS a` is the set of finite sums in `a`, i.e. `m ∈ FS a` if `m` is the sum of a nonempty
subsequence of `a`. We give a direct inductive definition instead of talking about subsequences. -/
inductive FS {M} [AddSemigroup M] : Stream' M → Set M
  | head (a : Stream' M) : FS a a.head
  | tail (a : Stream' M) (m : M) (h : FS a.tail m) : FS a m
  | cons (a : Stream' M) (m : M) (h : FS a.tail m) : FS a (a.head + m)
set_option linter.uppercaseLean3 false in
#align hindman.FS Hindman.FS

/-- `FP a` is the set of finite products in `a`, i.e. `m ∈ FP a` if `m` is the product of a nonempty
subsequence of `a`. We give a direct inductive definition instead of talking about subsequences. -/
@[to_additive FS]
inductive FP {M} [Semigroup M] : Stream' M → Set M
  | head (a : Stream' M) : FP a a.head
  | tail (a : Stream' M) (m : M) (h : FP a.tail m) : FP a m
  | cons (a : Stream' M) (m : M) (h : FP a.tail m) : FP a (a.head * m)
set_option linter.uppercaseLean3 false in
#align hindman.FP Hindman.FP

/-- If `m` and `m'` are finite products in `M`, then so is `m * m'`, provided that `m'` is obtained
from a subsequence of `M` starting sufficiently late. -/
@[to_additive
      "If `m` and `m'` are finite sums in `M`, then so is `m + m'`, provided that `m'`
      is obtained from a subsequence of `M` starting sufficiently late."]
theorem FP.mul {M} [Semigroup M] {a : Stream' M} {m : M} (hm : m ∈ FP a) :
    ∃ n, ∀ m' ∈ FP (a.drop n), m * m' ∈ FP a := by
  induction' hm with a a m hm ih a m hm ih
  · exact ⟨1, fun m hm => FP.cons a m hm⟩
    -- 🎉 no goals
  · cases' ih with n hn
    -- ⊢ ∃ n, ∀ (m' : M), m' ∈ FP (Stream'.drop n a) → m * m' ∈ FP a
    use n + 1
    -- ⊢ ∀ (m' : M), m' ∈ FP (Stream'.drop (n + 1) a) → m * m' ∈ FP a
    intro m' hm'
    -- ⊢ m * m' ∈ FP a
    exact FP.tail _ _ (hn _ hm')
    -- 🎉 no goals
  · cases' ih with n hn
    -- ⊢ ∃ n, ∀ (m' : M), m' ∈ FP (Stream'.drop n a) → Stream'.head a * m * m' ∈ FP a
    use n + 1
    -- ⊢ ∀ (m' : M), m' ∈ FP (Stream'.drop (n + 1) a) → Stream'.head a * m * m' ∈ FP a
    intro m' hm'
    -- ⊢ Stream'.head a * m * m' ∈ FP a
    rw [mul_assoc]
    -- ⊢ Stream'.head a * (m * m') ∈ FP a
    exact FP.cons _ _ (hn _ hm')
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align hindman.FP.mul Hindman.FP.mul
set_option linter.uppercaseLean3 false in
#align hindman.FS.add Hindman.FS.add

@[to_additive exists_idempotent_ultrafilter_le_FS]
theorem exists_idempotent_ultrafilter_le_FP {M} [Semigroup M] (a : Stream' M) :
    ∃ U : Ultrafilter M, U * U = U ∧ ∀ᶠ m in U, m ∈ FP a := by
  let S : Set (Ultrafilter M) := ⋂ n, { U | ∀ᶠ m in U, m ∈ FP (a.drop n) }
  -- ⊢ ∃ U, U * U = U ∧ ∀ᶠ (m : M) in ↑U, m ∈ FP a
  have h := exists_idempotent_in_compact_subsemigroup ?_ S ?_ ?_ ?_
  · rcases h with ⟨U, hU, U_idem⟩
    -- ⊢ ∃ U, U * U = U ∧ ∀ᶠ (m : M) in ↑U, m ∈ FP a
    refine' ⟨U, U_idem, _⟩
    -- ⊢ ∀ᶠ (m : M) in ↑U, m ∈ FP a
    convert Set.mem_iInter.mp hU 0
    -- 🎉 no goals
  · exact Ultrafilter.continuous_mul_left
    -- 🎉 no goals
  · apply IsCompact.nonempty_iInter_of_sequence_nonempty_compact_closed
    · intro n U hU
      -- ⊢ U ∈ {U | ∀ᶠ (m : M) in ↑U, m ∈ FP (Stream'.drop n a)}
      apply Eventually.mono hU
      -- ⊢ ∀ (x : M), x ∈ FP (Stream'.drop (n + 1) a) → x ∈ FP (Stream'.drop n a)
      rw [add_comm, ← Stream'.drop_drop, ← Stream'.tail_eq_drop]
      -- ⊢ ∀ (x : M), x ∈ FP (Stream'.tail (Stream'.drop n a)) → x ∈ FP (Stream'.drop n …
      exact FP.tail _
      -- 🎉 no goals
    · intro n
      -- ⊢ Set.Nonempty {U | ∀ᶠ (m : M) in ↑U, m ∈ FP (Stream'.drop n a)}
      exact ⟨pure _, mem_pure.mpr <| FP.head _⟩
      -- 🎉 no goals
    · exact (ultrafilter_isClosed_basic _).isCompact
      -- 🎉 no goals
    · intro n
      -- ⊢ IsClosed {U | ∀ᶠ (m : M) in ↑U, m ∈ FP (Stream'.drop n a)}
      apply ultrafilter_isClosed_basic
      -- 🎉 no goals
  · exact IsClosed.isCompact (isClosed_iInter fun i => ultrafilter_isClosed_basic _)
    -- 🎉 no goals
  · intro U hU V hV
    -- ⊢ U * V ∈ S
    rw [Set.mem_iInter] at *
    -- ⊢ ∀ (i : ℕ), U * V ∈ {U | ∀ᶠ (m : M) in ↑U, m ∈ FP (Stream'.drop i a)}
    intro n
    -- ⊢ U * V ∈ {U | ∀ᶠ (m : M) in ↑U, m ∈ FP (Stream'.drop n a)}
    rw [Set.mem_setOf_eq, Ultrafilter.eventually_mul]
    -- ⊢ ∀ᶠ (m : M) in ↑U, ∀ᶠ (m' : M) in ↑V, m * m' ∈ FP (Stream'.drop n a)
    apply Eventually.mono (hU n)
    -- ⊢ ∀ (x : M), x ∈ FP (Stream'.drop n a) → ∀ᶠ (m' : M) in ↑V, x * m' ∈ FP (Strea …
    intro m hm
    -- ⊢ ∀ᶠ (m' : M) in ↑V, m * m' ∈ FP (Stream'.drop n a)
    obtain ⟨n', hn⟩ := FP.mul hm
    -- ⊢ ∀ᶠ (m' : M) in ↑V, m * m' ∈ FP (Stream'.drop n a)
    apply Eventually.mono (hV (n' + n))
    -- ⊢ ∀ (x : M), x ∈ FP (Stream'.drop (n' + n) a) → m * x ∈ FP (Stream'.drop n a)
    intro m' hm'
    -- ⊢ m * m' ∈ FP (Stream'.drop n a)
    apply hn
    -- ⊢ m' ∈ FP (Stream'.drop n' (Stream'.drop n a))
    simpa only [Stream'.drop_drop] using hm'
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align hindman.exists_idempotent_ultrafilter_le_FP Hindman.exists_idempotent_ultrafilter_le_FP
set_option linter.uppercaseLean3 false in
#align hindman.exists_idempotent_ultrafilter_le_FS Hindman.exists_idempotent_ultrafilter_le_FS

@[to_additive exists_FS_of_large]
theorem exists_FP_of_large {M} [Semigroup M] (U : Ultrafilter M) (U_idem : U * U = U) (s₀ : Set M)
    (sU : s₀ ∈ U) : ∃ a, FP a ⊆ s₀ := by
  /- Informally: given a `U`-large set `s₀`, the set `s₀ ∩ { m | ∀ᶠ m' in U, m * m' ∈ s₀ }` is also
  `U`-large (since `U` is idempotent). Thus in particular there is an `a₀` in this intersection. Now
  let `s₁` be the intersection `s₀ ∩ { m | a₀ * m ∈ s₀ }`. By choice of `a₀`, this is again
  `U`-large, so we can repeat the argument starting from `s₁`, obtaining `a₁`, `s₂`, etc.
  This gives the desired infinite sequence. -/
  have exists_elem : ∀ {s : Set M} (_hs : s ∈ U), (s ∩ { m | ∀ᶠ m' in U, m * m' ∈ s }).Nonempty :=
    fun {s} hs => Ultrafilter.nonempty_of_mem (inter_mem hs <| by rwa [← U_idem] at hs)
  let elem : { s // s ∈ U } → M := fun p => (exists_elem p.property).some
  -- ⊢ ∃ a, FP a ⊆ s₀
  let succ : {s // s ∈ U} → {s // s ∈ U} := fun (p : {s // s ∈ U}) =>
        ⟨p.val ∩ {m : M | elem p * m ∈ p.val},
         inter_mem p.property
           (show (exists_elem p.property).some ∈ {m : M | ∀ᶠ (m' : M) in ↑U, m * m' ∈ p.val} from
              p.val.inter_subset_right {m : M | ∀ᶠ (m' : M) in ↑U, m * m' ∈ p.val}
                (exists_elem p.property).some_mem)⟩
  use Stream'.corec elem succ (Subtype.mk s₀ sU)
  -- ⊢ FP (Stream'.corec elem succ { val := s₀, property := sU }) ⊆ s₀
  suffices ∀ (a : Stream' M), ∀ m ∈ FP a, ∀ p, a = Stream'.corec elem succ p → m ∈ p.val by
    intro m hm
    exact this _ m hm ⟨s₀, sU⟩ rfl
  clear sU s₀
  -- ⊢ ∀ (a : Stream' M) (m : M), m ∈ FP a → ∀ (p : { s // s ∈ U }), a = Stream'.co …
  intro a m h
  -- ⊢ ∀ (p : { s // s ∈ U }), a = Stream'.corec elem succ p → m ∈ ↑p
  induction' h with b b n h ih b n h ih
  · rintro p rfl
    -- ⊢ Stream'.head (Stream'.corec elem succ p) ∈ ↑p
    rw [Stream'.corec_eq, Stream'.head_cons]
    -- ⊢ elem p ∈ ↑p
    exact Set.inter_subset_left _ _ (Set.Nonempty.some_mem _)
    -- 🎉 no goals
  · rintro p rfl
    -- ⊢ n ∈ ↑p
    refine' Set.inter_subset_left _ _ (ih (succ p) _)
    -- ⊢ Stream'.tail (Stream'.corec elem succ p) = Stream'.corec elem succ (succ p)
    rw [Stream'.corec_eq, Stream'.tail_cons]
    -- 🎉 no goals
  · rintro p rfl
    -- ⊢ Stream'.head (Stream'.corec elem succ p) * n ∈ ↑p
    have := Set.inter_subset_right _ _ (ih (succ p) ?_)
    -- ⊢ Stream'.head (Stream'.corec elem succ p) * n ∈ ↑p
    · simpa only using this
      -- 🎉 no goals
    rw [Stream'.corec_eq, Stream'.tail_cons]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align hindman.exists_FP_of_large Hindman.exists_FP_of_large
set_option linter.uppercaseLean3 false in
#align hindman.exists_FS_of_large Hindman.exists_FS_of_large

/-- The strong form of **Hindman's theorem**: in any finite cover of an FP-set, one the parts
contains an FP-set. -/
@[to_additive FS_partition_regular
      "The strong form of **Hindman's theorem**: in any finite cover of
      an FS-set, one the parts contains an FS-set."]
theorem FP_partition_regular {M} [Semigroup M] (a : Stream' M) (s : Set (Set M)) (sfin : s.Finite)
    (scov : FP a ⊆ ⋃₀ s) : ∃ c ∈ s, ∃ b : Stream' M, FP b ⊆ c :=
  let ⟨U, idem, aU⟩ := exists_idempotent_ultrafilter_le_FP a
  let ⟨c, cs, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset aU scov)
  ⟨c, cs, exists_FP_of_large U idem c hc⟩
set_option linter.uppercaseLean3 false in
#align hindman.FP_partition_regular Hindman.FP_partition_regular
set_option linter.uppercaseLean3 false in
#align hindman.FS_partition_regular Hindman.FS_partition_regular

/-- The weak form of **Hindman's theorem**: in any finite cover of a nonempty semigroup, one of the
parts contains an FP-set. -/
@[to_additive exists_FS_of_finite_cover
      "The weak form of **Hindman's theorem**: in any finite cover
      of a nonempty additive semigroup, one of the parts contains an FS-set."]
theorem exists_FP_of_finite_cover {M} [Semigroup M] [Nonempty M] (s : Set (Set M)) (sfin : s.Finite)
    (scov : ⊤ ⊆ ⋃₀ s) : ∃ c ∈ s, ∃ a : Stream' M, FP a ⊆ c :=
  let ⟨U, hU⟩ :=
    exists_idempotent_of_compact_t2_of_continuous_mul_left (@Ultrafilter.continuous_mul_left M _)
  let ⟨c, c_s, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset univ_mem scov)
  ⟨c, c_s, exists_FP_of_large U hU c hc⟩
set_option linter.uppercaseLean3 false in
#align hindman.exists_FP_of_finite_cover Hindman.exists_FP_of_finite_cover
set_option linter.uppercaseLean3 false in
#align hindman.exists_FS_of_finite_cover Hindman.exists_FS_of_finite_cover

@[to_additive FS_iter_tail_sub_FS]
theorem FP_drop_subset_FP {M} [Semigroup M] (a : Stream' M) (n : ℕ) : FP (a.drop n) ⊆ FP a := by
  induction' n with n ih
  -- ⊢ FP (Stream'.drop Nat.zero a) ⊆ FP a
  · rfl
    -- 🎉 no goals
  rw [Nat.succ_eq_one_add, ← Stream'.drop_drop]
  -- ⊢ FP (Stream'.drop 1 (Stream'.drop n a)) ⊆ FP a
  exact _root_.trans (FP.tail _) ih
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align hindman.FP_drop_subset_FP Hindman.FP_drop_subset_FP
set_option linter.uppercaseLean3 false in
#align hindman.FS_iter_tail_sub_FS Hindman.FS_iter_tail_sub_FS

@[to_additive]
theorem FP.singleton {M} [Semigroup M] (a : Stream' M) (i : ℕ) : a.nth i ∈ FP a := by
  induction' i with i ih generalizing a
  -- ⊢ Stream'.nth a Nat.zero ∈ FP a
  · apply FP.head
    -- 🎉 no goals
  · apply FP.tail
    -- ⊢ FP (Stream'.tail a) (Stream'.nth a (Nat.succ i))
    apply ih
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align hindman.FP.singleton Hindman.FP.singleton
set_option linter.uppercaseLean3 false in
#align hindman.FS.singleton Hindman.FS.singleton

@[to_additive]
theorem FP.mul_two {M} [Semigroup M] (a : Stream' M) (i j : ℕ) (ij : i < j) :
    a.nth i * a.nth j ∈ FP a := by
  refine' FP_drop_subset_FP _ i _
  -- ⊢ Stream'.nth a i * Stream'.nth a j ∈ FP (Stream'.drop i a)
  rw [← Stream'.head_drop]
  -- ⊢ Stream'.head (Stream'.drop i a) * Stream'.nth a j ∈ FP (Stream'.drop i a)
  apply FP.cons
  -- ⊢ FP (Stream'.tail (Stream'.drop i a)) (Stream'.nth a j)
  rcases le_iff_exists_add.mp (Nat.succ_le_of_lt ij) with ⟨d, hd⟩
  -- ⊢ FP (Stream'.tail (Stream'.drop i a)) (Stream'.nth a j)
  -- Porting note: need to fix breakage of Set notation
  change _ ∈ FP _
  -- ⊢ Stream'.nth a j ∈ FP (Stream'.tail (Stream'.drop i a))
  have := FP.singleton (a.drop i).tail d
  -- ⊢ Stream'.nth a j ∈ FP (Stream'.tail (Stream'.drop i a))
  rw [Stream'.tail_eq_drop, Stream'.nth_drop, Stream'.nth_drop] at this
  -- ⊢ Stream'.nth a j ∈ FP (Stream'.tail (Stream'.drop i a))
  convert this
  -- ⊢ j = d + 1 + i
  rw [hd, add_comm, Nat.succ_add, Nat.add_succ]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align hindman.FP.mul_two Hindman.FP.mul_two
set_option linter.uppercaseLean3 false in
#align hindman.FS.add_two Hindman.FS.add_two

@[to_additive]
theorem FP.finset_prod {M} [CommMonoid M] (a : Stream' M) (s : Finset ℕ) (hs : s.Nonempty) :
    (s.prod fun i => a.nth i) ∈ FP a := by
  refine' FP_drop_subset_FP _ (s.min' hs) _
  -- ⊢ (Finset.prod s fun i => Stream'.nth a i) ∈ FP (Stream'.drop (Finset.min' s h …
  induction' s using Finset.strongInduction with s ih
  -- ⊢ (Finset.prod s fun i => Stream'.nth a i) ∈ FP (Stream'.drop (Finset.min' s h …
  rw [← Finset.mul_prod_erase _ _ (s.min'_mem hs), ← Stream'.head_drop]
  -- ⊢ (Stream'.head (Stream'.drop (Finset.min' s hs) a) * Finset.prod (Finset.eras …
  cases' (s.erase (s.min' hs)).eq_empty_or_nonempty with h h
  -- ⊢ (Stream'.head (Stream'.drop (Finset.min' s hs) a) * Finset.prod (Finset.eras …
  · rw [h, Finset.prod_empty, mul_one]
    -- ⊢ Stream'.head (Stream'.drop (Finset.min' s hs) a) ∈ FP (Stream'.drop (Finset. …
    exact FP.head _
    -- 🎉 no goals
  · apply FP.cons
    -- ⊢ FP (Stream'.tail (Stream'.drop (Finset.min' s hs) a)) (Finset.prod (Finset.e …
    rw [Stream'.tail_eq_drop, Stream'.drop_drop, add_comm]
    -- ⊢ FP (Stream'.drop (Finset.min' s hs + 1) a) (Finset.prod (Finset.erase s (Fin …
    refine' Set.mem_of_subset_of_mem _ (ih _ (Finset.erase_ssubset <| s.min'_mem hs) h)
    -- ⊢ FP (Stream'.drop (Finset.min' (Finset.erase s (Finset.min' s hs)) h) a) ⊆ FP …
    have : s.min' hs + 1 ≤ (s.erase (s.min' hs)).min' h :=
      Nat.succ_le_of_lt (Finset.min'_lt_of_mem_erase_min' _ _ <| Finset.min'_mem _ _)
    cases' le_iff_exists_add.mp this with d hd
    -- ⊢ FP (Stream'.drop (Finset.min' (Finset.erase s (Finset.min' s hs)) h) a) ⊆ FP …
    rw [hd, add_comm, ← Stream'.drop_drop]
    -- ⊢ FP (Stream'.drop d (Stream'.drop (Finset.min' s hs + 1) a)) ⊆ FP (Stream'.dr …
    apply FP_drop_subset_FP
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align hindman.FP.finset_prod Hindman.FP.finset_prod
set_option linter.uppercaseLean3 false in
#align hindman.FS.finset_sum Hindman.FS.finset_sum

end Hindman
