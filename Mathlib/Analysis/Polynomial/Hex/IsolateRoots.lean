/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Polynomial.Hex.Isolations
public import Mathlib.Analysis.Polynomial.Hex.Basic
public import Mathlib.Analysis.Polynomial.Hex.Sturm
public import Mathlib.Analysis.Polynomial.Hex.Squarefree
public import HexRealRoots.Cert
public import Mathlib.Algebra.Polynomial.Hex.Int

/-!
# The `IsolatedRealRoots` API

The result type and library-side constructors used by the `isolate_roots` term
elaborator provide a complete, certified real-root isolation
of `P : Polynomial R` over `ℝ`. All proof content lives here, so the emitted
term only instantiates these constructors with reified literals and
`decide`-style certificates.

The replay constructor `IsolatedRealRoots.ofCert` is the
certificate shape. Its hypotheses are exactly the cheap kernel checks from
`HexRealRoots.Cert`: a single `SturmChainCert p chain` validity check, a
per-interval sign-variation gap of `1` (`count_one` via `sturmCount_eq_of_cert`,
packaged as `RealRootIsolation.count_one_of_cert`), an `orderedAdjacent` check
(`ordered` via `ordered_of_adjacent`), a `−∞/+∞` sign-variation gap (`complete`
via `rootCount_eq_of_cert`), a `hasSquarefreeSturmChain` check for the squarefree
side, and a size check for nonzeroness. Every hypothesis is a single `decide` on
literals against the reified chain; the kernel never re-runs the search.
-/

public section
set_option backward.proofsInPublic true

open Polynomial

namespace Hex

/-! # The user-facing structure -/

/-- A complete, certified real-root isolation of `P : Polynomial R` over `ℝ`:
`n` rational intervals, each holding exactly one real root, together covering
every real root, sorted and pairwise disjoint. Props are in `aeval` form so the
same structure serves `R = ℤ` (a `Hex.ZPoly` via
`HexPolyZMathlib.toPolynomial`), `R = ℚ`, and `R = ℝ`. -/
structure IsolatedRealRoots {R : Type*} [CommRing R] [Algebra R ℝ]
    (P : Polynomial R) (n : ℕ) where
  /-- The `n` isolating intervals `(lower, upper]`, as pairs of rationals. -/
  intervals : Vector (ℚ × ℚ) n
  /-- Each interval holds exactly one real root of `P`. -/
  unique_root : ∀ i : Fin n, ∃! x : ℝ,
      aeval x P = 0 ∧ (intervals[i].1 : ℝ) < x ∧ x ≤ (intervals[i].2 : ℝ)
  /-- Every real root of `P` lies in one of the intervals. -/
  covers : ∀ x : ℝ, aeval x P = 0 →
      ∃ i : Fin n, (intervals[i].1 : ℝ) < x ∧ x ≤ (intervals[i].2 : ℝ)
  /-- The intervals are sorted and pairwise disjoint: the upper endpoint of each
  is at most the lower endpoint of every later one. With half-open intervals
  this makes `n` exactly the number of distinct real roots. -/
  ordered : ∀ i j : Fin n, i < j → (intervals[i].2 : ℚ) ≤ (intervals[j].1 : ℚ)

/-- Transport an isolation along a pointwise root equivalence. One lemma, used
twice by the elaborator: the squarefree-core step and the user-polynomial
step. Heterogeneous in the coefficient ring, since the structure only sees `P`
through `aeval x P = 0`. -/
@[expose] noncomputable def IsolatedRealRoots.congrRoots {R S : Type*} [CommRing R] [Algebra R ℝ]
    [CommRing S] [Algebra S ℝ] {P : Polynomial R} {Q : Polynomial S} {n : ℕ}
    (h : ∀ x : ℝ, aeval x P = 0 ↔ aeval x Q = 0) :
    IsolatedRealRoots P n → IsolatedRealRoots Q n := fun H =>
  { intervals := H.intervals
    unique_root := fun i => by
      obtain ⟨x, ⟨hx0, hlo, hhi⟩, huniq⟩ := H.unique_root i
      exact ⟨x, ⟨(h x).mp hx0, hlo, hhi⟩,
        fun y hy => huniq y ⟨(h y).mpr hy.1, hy.2.1, hy.2.2⟩⟩
    covers := fun x hx => H.covers x ((h x).mpr hx)
    ordered := H.ordered }

/-- `congrRoots` leaves the intervals untouched, so `simp` reduces a transported
isolation's intervals to the underlying ones. -/
@[simp] theorem IsolatedRealRoots.congrRoots_intervals {R S : Type*} [CommRing R]
    [Algebra R ℝ] [CommRing S] [Algebra S ℝ] {P : Polynomial R} {Q : Polynomial S} {n : ℕ}
    (h : ∀ x : ℝ, aeval x P = 0 ↔ aeval x Q = 0) (H : IsolatedRealRoots P n) :
    (IsolatedRealRoots.congrRoots h H).intervals = H.intervals := rfl

/-- The `n = 0` result for a constant whose real image is nonzero: it has no
real roots, so the empty isolation is complete. Nonzero constants never enter
the isolator (the squarefree Sturm certificate is `false` on constants by
design), so the elaborator dispatches them here. -/
def IsolatedRealRoots.constant {R : Type*} [CommRing R] [Algebra R ℝ] {c : R}
    (hc : algebraMap R ℝ c ≠ 0) : IsolatedRealRoots (Polynomial.C c) 0 where
  intervals := ⟨#[], rfl⟩
  unique_root := fun i => i.elim0
  covers := fun x hx => by
    exact absurd (by rwa [Polynomial.aeval_C] at hx) hc
  ordered := fun i _ _ => i.elim0

/-- The certified isolating intervals count exactly the distinct real roots. -/
theorem IsolatedRealRoots.card_rootSet {R : Type*} [CommRing R] [IsDomain R]
    [Algebra R ℝ] [Module.IsTorsionFree R ℝ] {p : R[X]} {n : ℕ}
    (H : Hex.IsolatedRealRoots p n) (hp : p ≠ 0) :
    Fintype.card (p.rootSet ℝ) = n := by
  classical
  choose r hr hu using H.unique_root
  have hm : StrictMono r := by
    intro i j hij
    have ho : (H.intervals[i].2 : ℝ) ≤ (H.intervals[j].1 : ℝ) := by
      exact_mod_cast H.ordered i j hij
    exact ((hr i).2.2.trans ho).trans_lt (hr j).2.1
  let f : Fin n → p.rootSet ℝ := fun i => ⟨r i, (mem_rootSet_of_ne hp).2 (hr i).1⟩
  have hinj : Function.Injective f := fun _ _ hij => hm.injective (congrArg Subtype.val hij)
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hx0 := (mem_rootSet_of_ne hp).1 hx
    obtain ⟨i, hi⟩ := H.covers x hx0
    exact ⟨i, Subtype.ext (hu i x ⟨hx0, hi⟩).symm⟩
  simpa using (Fintype.card_of_bijective ⟨hinj, hsurj⟩).symm

end Hex

namespace HexRealRootsMathlib

open Hex

/-! # Glue lemmas -/

/-- `aeval` over `ℝ` of an embedded integer polynomial is the degree-indexed sum
of its integer coefficients cast to `ℝ` — the coefficient-sum form of
`eval_toPolyℝ`, reconciled through the existing `aeval_eq_eval_toPolyℝ`. For a
literal `ofCoeffs` this unfolds via `Finset.sum_range_succ` into an explicit
polynomial in `x`. -/
theorem aeval_toPolynomial (p : Hex.ZPoly) (x : ℝ) :
    aeval x (HexPolyZMathlib.toPolynomial p) =
      ∑ i ∈ Finset.range p.size, (p.coeff i : ℝ) * x ^ i := by
  rw [aeval_eq_eval_toPolyℝ, eval_toPolyℝ]

/-- The `aeval`-of-`ofCoeffs` bridge summed over the *raw* coefficient array
length rather than the trimmed `size`: extending the sum only adds the trailing
zeros. Because `coeffs.size` for a literal `#[…]` reduces to a numeral, this is
the shape the `isolate_roots_bridge` tactic unrolls with `Finset.sum_range_succ`
without a `decide` on the trimmed size. -/
theorem aeval_toPolynomial_ofCoeffs (coeffs : Array Int) (x : ℝ) :
    aeval x (HexPolyZMathlib.toPolynomial (Hex.DensePoly.ofCoeffs coeffs)) =
      ∑ i ∈ Finset.range coeffs.size, ((Hex.DensePoly.ofCoeffs coeffs).coeff i : ℝ) * x ^ i := by
  rw [aeval_toPolynomial]
  refine Finset.sum_subset (fun a ha => Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp ha) (Hex.DensePoly.size_ofCoeffs_le coeffs))) ?_
  intro i _ hi
  rw [Finset.mem_range, not_lt] at hi
  rw [Hex.DensePoly.coeff_eq_zero_of_size_le _ hi, show ((Zero.zero : Int) : ℝ) = 0 from by
    norm_num, zero_mul]

/-- `IsRoot` of the real cast is the structure's `aeval = 0` form. -/
theorem isRoot_toPolyℝ_iff (p : Hex.ZPoly) (x : ℝ) :
    (toPolyℝ p).IsRoot x ↔ aeval x (HexPolyZMathlib.toPolynomial p) = 0 := by
  rw [Polynomial.IsRoot, aeval_eq_eval_toPolyℝ]

/-- A `ZPoly` with nonzero stored size is nonzero. Emitted `p ≠ 0` proofs go
through this (a `Nat` `decide` on `p.size`), never through structural
`DensePoly` equality (the core `Array.instDecidableEqImpl` module bug). -/
theorem ne_zero_of_size_ne_zero {p : Hex.ZPoly} (h : p.size ≠ 0) : p ≠ 0 :=
  fun he => h (by rw [he]; exact Hex.DensePoly.size_zero)

/-! # The from-`RealRootIsolations` constructor -/

/-- **`IsolatedRealRoots.of`.** Assemble the user structure from a complete
Sturm-certified run, via `exists_unique_root` + `isolates` + the `aeval` bridge,
including the `ordered` field from the backend's `ordered`. -/
noncomputable def _root_.Hex.IsolatedRealRoots.of (p : Hex.ZPoly) (hp0 : p ≠ 0)
    (hsf : Hex.ZPoly.SquareFreeRat p) (out : Hex.RealRootIsolations p) :
    Hex.IsolatedRealRoots (HexPolyZMathlib.toPolynomial p) out.isolations.size where
  intervals := Vector.ofFn fun i =>
    (out.isolations[i].interval.lower.toRat, out.isolations[i].interval.upper.toRat)
  unique_root := by
    intro i
    have h := (out.isolations[i]).exists_unique_root hsf
    simp only [toReal_eq_cast_toRat] at h
    obtain ⟨r, ⟨hr0, hlo, hhi⟩, huniq⟩ := h
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    refine ⟨r, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact (isRoot_toPolyℝ_iff p r).mp hr0
    · exact hlo
    · exact hhi
    · intro y hy
      exact huniq y ⟨(isRoot_toPolyℝ_iff p y).mpr hy.1, hy.2.1, hy.2.2⟩
  covers := by
    intro x hx
    have hroot : (toPolyℝ p).IsRoot x := (isRoot_toPolyℝ_iff p x).mpr hx
    have hiso := out.isolates hp0 hsf x hroot
    simp only [toReal_eq_cast_toRat] at hiso
    obtain ⟨iso, ⟨hmem, hlo, hhi⟩, _⟩ := hiso
    rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hmem
    obtain ⟨j, hj, hjeq⟩ := hmem
    refine ⟨⟨j, hj⟩, ?_, ?_⟩ <;> simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    · rw [hjeq]; exact hlo
    · rw [hjeq]; exact hhi
  ordered := by
    intro i j hij
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    exact Dyadic.toRat_le_toRat_iff.mpr (out.ordered i j hij)

/-! # The replay constructor -/

/-- A per-interval `count_one` witness from the chain certificate and a single
sign-variation gap `decide`: `sturmCount_eq_of_cert` rewrites the certified count
onto the literal chain, where the emitted `decide` confirms the gap is `1`. -/
theorem RealRootIsolation.count_one_of_cert {p : Hex.ZPoly} {chain : Array Hex.ZPoly}
    (hcert : Hex.SturmChainCert p chain) (I : Hex.DyadicInterval)
    (h : (Hex.sturmVarAt chain I.lower : Int) - Hex.sturmVarAt chain I.upper = 1) :
    Hex.sturmCount p I = 1 :=
  (Hex.ZPoly.sturmCount_eq_of_cert hcert I).trans h

/-- **The replay constructor `IsolatedRealRoots.ofCert`.** The production
certificate shape: from the reified polynomial `p`, a reified Sturm chain
`chain`, and `n` certified isolations `iso` (each carrying its interval and a
cheap `count_one_of_cert` witness), assemble the isolation with every remaining
obligation a single `decide` on literals:

* `hsize : p.size ≠ 0` — nonzeroness by a `Nat` `decide`;
* `hsf : hasSquarefreeSturmChain p` — the squarefree side;
* `hcert : SturmChainCert p chain` — the reified chain is `p`'s Sturm chain,
  validated by coefficient-level checks that kernel-reduce (never a structural
  `Array` equality), used for `complete`;
* `hordered : orderedAdjacent iso.toArray` — the `O(n)` adjacent-pair order
  check, walked to the all-pairs `ordered` field by `ordered_of_adjacent`;
* `hcomplete : sturmVarNegInf chain − sturmVarPosInf chain = n` — the `−∞/+∞`
  sign-variation gap, giving `complete` via `rootCount_eq_of_cert`.

The kernel replays only the exposed count-check closure against the literal
chain; it never rebuilds `sturmChain p` inside a field. -/
noncomputable def _root_.Hex.IsolatedRealRoots.ofCert {p : Hex.ZPoly}
    {chain : Array Hex.ZPoly} {n : ℕ}
    (iso : Vector (Hex.RealRootIsolation p) n) (hsize : p.size ≠ 0)
    (hsf : Hex.ZPoly.hasSquarefreeSturmChain p = true) (hcert : Hex.SturmChainCert p chain)
    (hordered : Hex.orderedAdjacent iso.toArray = true)
    (hcomplete : Hex.sturmVarNegInf chain - Hex.sturmVarPosInf chain = n) :
    Hex.IsolatedRealRoots (HexPolyZMathlib.toPolynomial p) n :=
  iso.size_toArray ▸
    IsolatedRealRoots.of p (ne_zero_of_size_ne_zero hsize)
      (squareFreeRat_of_hasSquarefreeSturmChain p hsf)
      { isolations := iso.toArray
        ordered := Hex.ordered_of_adjacent hordered
        complete := iso.size_toArray.trans
          (hcomplete.symm.trans (Hex.ZPoly.rootCount_eq_of_cert hcert).symm) }

/-! # Pretty interval literals -/

/-- Re-express an isolation over different interval literals: any vector whose
endpoints agree with the originals **as reals** carries the same three
theorems. Stating the agreement over `ℝ` matters: it never normalizes a
rational (no `Rat` gcd anywhere near the kernel), so the elaborator can
discharge it by `norm_num` through the dyadic cast lemmas and present the
intervals as pretty `m / 2^k` literals. With a literal `intervals` field,
user-side extraction is a definitional step:
`show H.intervals = #v[…] from rfl`. -/
@[expose] noncomputable def _root_.Hex.IsolatedRealRoots.withIntervals {R : Type*}
    [CommRing R] [Algebra R ℝ]
    {P : Polynomial R} {n : ℕ} (H : IsolatedRealRoots P n) (w : Vector (ℚ × ℚ) n)
    (hw : ∀ i : Fin n,
      ((w[i].1 : ℚ) : ℝ) = ((H.intervals[i].1 : ℚ) : ℝ) ∧
      ((w[i].2 : ℚ) : ℝ) = ((H.intervals[i].2 : ℚ) : ℝ)) :
    IsolatedRealRoots P n where
  intervals := w
  unique_root i := by
    rw [(hw i).1, (hw i).2]
    exact H.unique_root i
  covers x hx := by
    obtain ⟨i, h1, h2⟩ := H.covers x hx
    exact ⟨i, by rw [(hw i).1]; exact h1, by rw [(hw i).2]; exact h2⟩
  ordered i j hij := by
    have h := H.ordered i j hij
    have hr : ((w[i].2 : ℚ) : ℝ) ≤ ((w[j].1 : ℚ) : ℝ) := by
      rw [(hw i).2, (hw j).1]
      exact_mod_cast h
    exact_mod_cast hr

/-- `withIntervals` sets the intervals to the supplied literal vector, so `simp`
reduces a re-based isolation's intervals to that literal. -/
@[simp] theorem _root_.Hex.IsolatedRealRoots.withIntervals_intervals {R : Type*} [CommRing R]
    [Algebra R ℝ] {P : Polynomial R} {n : ℕ} (H : IsolatedRealRoots P n)
    (w : Vector (ℚ × ℚ) n)
    (hw : ∀ i : Fin n,
      ((w[i].1 : ℚ) : ℝ) = ((H.intervals[i].1 : ℚ) : ℝ) ∧
      ((w[i].2 : ℚ) : ℝ) = ((H.intervals[i].2 : ℚ) : ℝ)) :
    (IsolatedRealRoots.withIntervals H w hw).intervals = w := rfl

/-- The `intervals` of `ofCert` are the `toRat` images of the supplied
isolations' dyadic endpoints. -/
theorem _root_.Hex.IsolatedRealRoots.ofCert_intervals {p : Hex.ZPoly}
    {chain : Array Hex.ZPoly} {n : ℕ}
    (iso : Vector (Hex.RealRootIsolation p) n) (hsize : p.size ≠ 0)
    (hsf : Hex.ZPoly.hasSquarefreeSturmChain p = true) (hcert : Hex.SturmChainCert p chain)
    (hordered : Hex.orderedAdjacent iso.toArray = true)
    (hcomplete : Hex.sturmVarNegInf chain - Hex.sturmVarPosInf chain = n) (i : Fin n) :
    (IsolatedRealRoots.ofCert iso hsize hsf hcert hordered hcomplete).intervals[i] =
      ((iso[i]).interval.lower.toRat, (iso[i]).interval.upper.toRat) := by
  obtain ⟨arr, rfl⟩ := iso
  simp [IsolatedRealRoots.ofCert, IsolatedRealRoots.of]

/-- `ofCert`, re-based on pretty rational interval literals. `w`'s endpoints
are tied to the isolations' dyadics by ℝ-level identities against the literal
`iso` argument — a shape user modules can check without reducing any of this
library's definitions, and with no `Rat` normalization near the kernel. This
is the constructor the `isolate_roots` elaborator emits: with `intervals`
definitionally the literal `w`, user-side extraction is
`show H.intervals = #v[…] from rfl`. -/
@[expose] noncomputable def _root_.Hex.IsolatedRealRoots.ofCertPretty {p : Hex.ZPoly}
    {chain : Array Hex.ZPoly}
    {n : ℕ} (iso : Vector (Hex.RealRootIsolation p) n) (w : Vector (ℚ × ℚ) n)
    (hsize : p.size ≠ 0)
    (hsf : Hex.ZPoly.hasSquarefreeSturmChain p = true) (hcert : Hex.SturmChainCert p chain)
    (hordered : Hex.orderedAdjacent iso.toArray = true)
    (hcomplete : Hex.sturmVarNegInf chain - Hex.sturmVarPosInf chain = n)
    (hw : ∀ i : Fin n,
      ((w[i].1 : ℚ) : ℝ) = Dyadic.toReal (iso[i]).interval.lower ∧
      ((w[i].2 : ℚ) : ℝ) = Dyadic.toReal (iso[i]).interval.upper) :
    Hex.IsolatedRealRoots (HexPolyZMathlib.toPolynomial p) n :=
  IsolatedRealRoots.withIntervals
    (IsolatedRealRoots.ofCert iso hsize hsf hcert hordered hcomplete) w (by
    intro i
    have he := IsolatedRealRoots.ofCert_intervals iso hsize hsf hcert hordered hcomplete i
    constructor
    · rw [(hw i).1, he, toReal_eq_cast_toRat]
    · rw [(hw i).2, he, toReal_eq_cast_toRat])

/-- `ofCertPretty`'s intervals are the supplied literal vector `w`. The
elaborator emits `ofCertPretty` directly, so this `simp` lemma lets a user
`simp`/`simpa`/`grind` compute an isolation's intervals to their literal
endpoints without unfolding the constructor by hand. -/
@[simp] theorem _root_.Hex.IsolatedRealRoots.ofCertPretty_intervals {p : Hex.ZPoly}
    {chain : Array Hex.ZPoly} {n : ℕ} (iso : Vector (Hex.RealRootIsolation p) n)
    (w : Vector (ℚ × ℚ) n) (hsize : p.size ≠ 0)
    (hsf : Hex.ZPoly.hasSquarefreeSturmChain p = true) (hcert : Hex.SturmChainCert p chain)
    (hordered : Hex.orderedAdjacent iso.toArray = true)
    (hcomplete : Hex.sturmVarNegInf chain - Hex.sturmVarPosInf chain = n)
    (hw : ∀ i : Fin n,
      ((w[i].1 : ℚ) : ℝ) = Dyadic.toReal (iso[i]).interval.lower ∧
      ((w[i].2 : ℚ) : ℝ) = Dyadic.toReal (iso[i]).interval.upper) :
    (IsolatedRealRoots.ofCertPretty iso w hsize hsf hcert hordered hcomplete hw).intervals = w :=
  rfl

/-! # The bridge tactic -/

/-- Close `∀ x : ℝ, aeval x (toPolynomial (ofCoeffs #[…])) = 0 ↔ aeval x P = 0`
for a reflected literal `ofCoeffs` polynomial and a user polynomial `P` over
`X`, `C`, numerals, `+`, `-`, `*`, `^`, `neg`. The left side unfolds through
`aeval_toPolynomial_ofCoeffs` (a sum over the raw coefficient-array length, whose
`size` reduces to a numeral) and `Finset.sum_range_succ`; the right side unfolds
through the pointwise `aeval` homomorphism lemmas; `push_cast`/`norm_num`/`ring_nf`
reconcile the two explicit polynomials in `x`.

This is a pointwise evaluation bridge, not a `Polynomial` identity: it works on
closed literal data with integer coefficients and does not attempt to match
`Polynomial` structure. -/
macro (name := isolateRootsBridge) "isolate_roots_bridge" : tactic =>
  `(tactic|
    (intro x
     rw [HexRealRootsMathlib.aeval_toPolynomial_ofCoeffs]
     simp [Finset.sum_range_succ, Finset.sum_range_zero, Hex.DensePoly.coeff_ofCoeffs,
       map_ofNat] <;>
     ring_nf))

end HexRealRootsMathlib
