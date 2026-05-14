/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
module

public import Mathlib.Topology.Compactification.StoneCech
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Stream.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Finset.Max
import Mathlib.Data.Stream.Init
import Mathlib.Init
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Topology.Algebra.Semigroup

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

@[expose] public section


open Filter

/-- Multiplication of ultrafilters given by `∀ᶠ m in U*V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m*m')`. -/
@[to_additive (attr := implicit_reducible)
/-- Addition of ultrafilters given by `∀ᶠ m in U+V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m+m')`. -/]
def Ultrafilter.mul {M} [Mul M] : Mul (Ultrafilter M) where mul U V := (· * ·) <$> U <*> V

attribute [local instance] Ultrafilter.mul Ultrafilter.add

/- We could have taken this as the definition of `U * V`, but then we would have to prove that it
defines an ultrafilter. -/
@[to_additive]
theorem Ultrafilter.eventually_mul {M} [Mul M] (U V : Ultrafilter M) (p : M → Prop) :
    (∀ᶠ m in ↑(U * V), p m) ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m * m') :=
  Iff.rfl

/-- Semigroup structure on `Ultrafilter M` induced by a semigroup structure on `M`. -/
@[to_additive (attr := implicit_reducible)
/-- Additive semigroup structure on `Ultrafilter M` induced by an additive semigroup
structure on `M`. -/]
def Ultrafilter.semigroup {M} [Semigroup M] : Semigroup (Ultrafilter M) :=
  { Ultrafilter.mul with
    mul_assoc := fun U V W =>
      Ultrafilter.coe_inj.mp <|
        Filter.ext' fun p => by simp [Ultrafilter.eventually_mul, mul_assoc] }

attribute [local instance] Ultrafilter.semigroup Ultrafilter.addSemigroup

-- We don't prove `continuous_mul_right`, because in general it is false!
@[to_additive]
theorem Ultrafilter.continuous_mul_left {M} [Mul M] (V : Ultrafilter M) :
    Continuous (· * V) :=
  ultrafilterBasis_is_basis.continuous_iff.2 <| Set.forall_mem_range.mpr fun s ↦
    ultrafilter_isOpen_basic { m : M | ∀ᶠ m' in V, m * m' ∈ s }

namespace Hindman

/-- `FS a` is the set of finite sums in `a`, i.e. `m ∈ FS a` if `m` is the sum of a nonempty
subsequence of `a`. We give a direct inductive definition instead of talking about subsequences. -/
inductive FS {M} [AddSemigroup M] : Stream' M → Set M
  | head' (a : Stream' M) : FS a a.head
  | tail' (a : Stream' M) (m : M) (h : FS a.tail m) : FS a m
  | cons' (a : Stream' M) (m : M) (h : FS a.tail m) : FS a (a.head + m)

/-- `FP a` is the set of finite products in `a`, i.e. `m ∈ FP a` if `m` is the product of a nonempty
subsequence of `a`. We give a direct inductive definition instead of talking about subsequences. -/
@[to_additive FS]
inductive FP {M} [Semigroup M] : Stream' M → Set M
  | head' (a : Stream' M) : FP a a.head
  | tail' (a : Stream' M) (m : M) (h : FP a.tail m) : FP a m
  | cons' (a : Stream' M) (m : M) (h : FP a.tail m) : FP a (a.head * m)

section Aliases

/-! Since the constructors for `FS` and `FP` cheat using the `Set M = M → Prop` defeq,
we provide match patterns that preserve the defeq correctly in their type. -/

variable {M} [Semigroup M] (a : Stream' M) (m : M) (h : FP a.tail m)
/-- Constructor for `FP`. This is the preferred spelling over `FP.head'`. -/
@[to_additive (attr := match_pattern, nolint defLemma)
  /-- Constructor for `FS`. This is the preferred spelling over `FS.head'`. -/]
abbrev FP.head : a.head ∈ FP a := FP.head' a
/-- Constructor for `FP`. This is the preferred spelling over `FP.tail'`. -/
@[to_additive (attr := match_pattern, nolint defLemma)
  /-- Constructor for `FS`. This is the preferred spelling over `FS.tail'`. -/]
abbrev FP.tail : m ∈ FP a := FP.tail' a m h
/-- Constructor for `FP`. This is the preferred spelling over `FP.cons'`. -/
@[to_additive (attr := match_pattern, nolint defLemma)
  /-- Constructor for `FS`. This is the preferred spelling over `FS.cons'`. -/]
abbrev FP.cons : a.head * m ∈ FP a := FP.cons' a m h

end Aliases

/-- If `m` and `m'` are finite products in `M`, then so is `m * m'`, provided that `m'` is obtained
from a subsequence of `M` starting sufficiently late. -/
@[to_additive /-- If `m` and `m'` are finite sums in `M`, then so is `m + m'`, provided that `m'`
is obtained from a subsequence of `M` starting sufficiently late. -/]
theorem FP.mul {M} [Semigroup M] {a : Stream' M} {m : M} (hm : m ∈ FP a) :
    ∃ n, ∀ m' ∈ FP (a.drop n), m * m' ∈ FP a := by
  induction hm with
  | head' a => exact ⟨1, fun m hm => FP.cons a m hm⟩
  | tail' a m _ ih =>
    obtain ⟨n, hn⟩ := ih
    use n + 1
    intro m' hm'
    exact FP.tail _ _ (hn _ hm')
  | cons' a m _ ih =>
    obtain ⟨n, hn⟩ := ih
    use n + 1
    intro m' hm'
    rw [mul_assoc]
    exact FP.cons _ _ (hn _ hm')

@[to_additive exists_idempotent_ultrafilter_le_FS]
theorem exists_idempotent_ultrafilter_le_FP {M} [Semigroup M] (a : Stream' M) :
    ∃ U : Ultrafilter M, U * U = U ∧ ∀ᶠ m in U, m ∈ FP a := by
  let S : Set (Ultrafilter M) := ⋂ n, { U | ∀ᶠ m in U, m ∈ FP (a.drop n) }
  have h := exists_idempotent_in_compact_subsemigroup ?_ S ?_ ?_ ?_
  · rcases h with ⟨U, hU, U_idem⟩
    refine ⟨U, U_idem, ?_⟩
    convert Set.mem_iInter.mp hU 0
  · exact Ultrafilter.continuous_mul_left
  · apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · intro n U hU
      filter_upwards [hU]
      rw [← Stream'.drop_drop, ← Stream'.tail_eq_drop]
      exact FP.tail _
    · intro n
      exact ⟨pure _, mem_pure.mpr <| FP.head _⟩
    · exact (ultrafilter_isClosed_basic _).isCompact
    · intro n
      apply ultrafilter_isClosed_basic
  · exact IsClosed.isCompact (isClosed_iInter fun i => ultrafilter_isClosed_basic _)
  · intro U hU V hV
    rw [Set.mem_iInter] at *
    intro n
    rw [Set.mem_setOf_eq, Ultrafilter.eventually_mul]
    filter_upwards [hU n] with m hm
    obtain ⟨n', hn⟩ := FP.mul hm
    filter_upwards [hV (n' + n)] with m' hm'
    apply hn
    simpa only [Stream'.drop_drop, add_comm] using hm'

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
  let succ : {s // s ∈ U} → {s // s ∈ U} := fun (p : {s // s ∈ U}) =>
        ⟨p.val ∩ {m : M | elem p * m ∈ p.val},
         inter_mem p.property
           (show (exists_elem p.property).some ∈ {m : M | ∀ᶠ (m' : M) in ↑U, m * m' ∈ p.val} from
              p.val.inter_subset_right (exists_elem p.property).some_mem)⟩
  use Stream'.corec elem succ (Subtype.mk s₀ sU)
  suffices ∀ (a : Stream' M), ∀ m ∈ FP a, ∀ p, a = Stream'.corec elem succ p → m ∈ p.val by
    intro m hm
    exact this _ m hm ⟨s₀, sU⟩ rfl
  clear sU s₀
  intro a m h
  induction h with
  | head' b =>
    rintro p rfl
    rw [Stream'.corec_eq, Stream'.head_cons]
    exact Set.inter_subset_left (Set.Nonempty.some_mem _)
  | tail' b n h ih =>
    rintro p rfl
    refine Set.inter_subset_left (ih (succ p) ?_)
    rw [Stream'.corec_eq, Stream'.tail_cons]
  | cons' b n h ih =>
    rintro p rfl
    have := Set.inter_subset_right (ih (succ p) ?_)
    · simpa only using this
    rw [Stream'.corec_eq, Stream'.tail_cons]

/-- The strong form of **Hindman's theorem**: in any finite cover of an FP-set, one the parts
contains an FP-set. -/
@[to_additive FS_partition_regular /-- The strong form of **Hindman's theorem**: in any finite
cover of an FS-set, one the parts contains an FS-set. -/]
theorem FP_partition_regular {M} [Semigroup M] (a : Stream' M) (s : Set (Set M)) (sfin : s.Finite)
    (scov : FP a ⊆ ⋃₀ s) : ∃ c ∈ s, ∃ b : Stream' M, FP b ⊆ c :=
  let ⟨U, idem, aU⟩ := exists_idempotent_ultrafilter_le_FP a
  let ⟨c, cs, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset aU scov)
  ⟨c, cs, exists_FP_of_large U idem c hc⟩

/-- The weak form of **Hindman's theorem**: in any finite cover of a nonempty semigroup, one of the
parts contains an FP-set. -/
@[to_additive exists_FS_of_finite_cover /-- The weak form of **Hindman's theorem**: in any finite
cover of a nonempty additive semigroup, one of the parts contains an FS-set. -/]
theorem exists_FP_of_finite_cover {M} [Semigroup M] [Nonempty M] (s : Set (Set M)) (sfin : s.Finite)
    (scov : ⊤ ⊆ ⋃₀ s) : ∃ c ∈ s, ∃ a : Stream' M, FP a ⊆ c :=
  let ⟨U, hU⟩ :=
    exists_idempotent_of_compact_t2_of_continuous_mul_left (@Ultrafilter.continuous_mul_left M _)
  let ⟨c, c_s, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset univ_mem scov)
  ⟨c, c_s, exists_FP_of_large U hU c hc⟩

@[to_additive FS_iter_tail_sub_FS]
theorem FP_drop_subset_FP {M} [Semigroup M] (a : Stream' M) (n : ℕ) : FP (a.drop n) ⊆ FP a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Stream'.drop_drop]
    exact _root_.trans (FP.tail _) ih

@[to_additive]
theorem FP.singleton {M} [Semigroup M] (a : Stream' M) (i : ℕ) : a.get i ∈ FP a := by
  induction i generalizing a with
  | zero => exact FP.head _
  | succ i ih => exact FP.tail _ _ (ih _)

@[to_additive]
theorem FP.mul_two {M} [Semigroup M] (a : Stream' M) (i j : ℕ) (ij : i < j) :
    a.get i * a.get j ∈ FP a := by
  refine FP_drop_subset_FP _ i ?_
  rw [← Stream'.head_drop]
  apply FP.cons
  rcases Nat.exists_eq_add_of_le (Nat.succ_le_of_lt ij) with ⟨d, hd⟩
  have := FP.singleton (a.drop i).tail d
  rw [Stream'.tail_eq_drop, Stream'.get_drop, Stream'.get_drop] at this
  convert this
  lia

@[to_additive]
theorem FP.finsetProd {M} [CommMonoid M] (a : Stream' M) (s : Finset ℕ) (hs : s.Nonempty) :
    (s.prod fun i => a.get i) ∈ FP a := by
  refine FP_drop_subset_FP _ (s.min' hs) ?_
  induction s using Finset.eraseInduction with | H s ih => _
  rw [← Finset.mul_prod_erase _ _ (s.min'_mem hs), ← Stream'.head_drop]
  rcases (s.erase (s.min' hs)).eq_empty_or_nonempty with h | h
  · rw [h, Finset.prod_empty, mul_one]
    exact FP.head _
  · apply FP.cons
    rw [Stream'.tail_eq_drop, Stream'.drop_drop, add_comm]
    refine Set.mem_of_subset_of_mem ?_ (ih _ (s.min'_mem hs) h)
    have : s.min' hs + 1 ≤ (s.erase (s.min' hs)).min' h :=
      Nat.succ_le_of_lt (Finset.min'_lt_of_mem_erase_min' _ _ <| Finset.min'_mem _ _)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le this
    rw [hd, ← Stream'.drop_drop, add_comm]
    apply FP_drop_subset_FP

@[deprecated (since := "2026-04-08")] alias FS.finset_sum := FS.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias FP.finset_prod := FP.finsetProd

end Hindman
