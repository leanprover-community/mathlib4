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
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Polynomial.Hex.Sturm
public import HexRealRoots.Var
-- `import all` on the executable modules so the non-`@[expose]` bodies of
-- `sturmChain`, `sturmCount`, `sturmVarAt`, and `signVar` unfold here (the
-- degree-positivity derivation reads the empty chain of a degree-`≤ 0` input).
import all Mathlib.Analysis.Polynomial.Hex.Basic
import all HexRealRoots.Basic
import all HexRealRoots.Chain
import all HexRealRoots.Var

/-!
# Isolation semantics

Soundness of a `RealRootIsolation`/`RealRootIsolations` witness, for any
rationally squarefree `p`, no matter which engine produced it:

* `RealRootIsolation.exists_unique_root`: a single certified isolation names
  exactly one real root in its half-open interval.
* `RealRootIsolations.isolates`: a complete run names every real root exactly
  once.

Both consume only the decidable certificate fields (`count_one`, `ordered`,
`complete`) plus the correspondence theorems `sturmCount_eq_card_roots` and
`rootCount_eq_card_roots` from `ChainCorrespond`.

The correspondence theorems carry a `1 ≤ (p.degree?).getD 0` hypothesis
(`SquareFreeRat` alone is insufficient — `SquareFreeRat 0` is vacuous).
`exists_unique_root` does **not** need any extra hypothesis: a
`RealRootIsolation` carries `count_one`, and a Sturm count of `1` forces a
nonempty chain, hence positive degree (`degree_pos_of_count_one`), so the
statement needs no additional hypothesis. `isolates` takes `p ≠ 0` because
the `SquareFreeRat`-only form fails at `p = 0`, where every real is a root but
`complete` forces zero isolations); the nonzero-constant case is vacuous, and
the positive-degree case is the real content.
-/

public section

namespace HexRealRootsMathlib

open Polynomial

noncomputable section

variable {p : Hex.ZPoly}

/-- A polynomial of degree `≤ 0` has the empty Sturm chain. -/
private theorem sturmChain_eq_nil_of_degree_nonpos (h : (p.degree?).getD 0 = 0) :
    Hex.ZPoly.sturmChain p = #[] := by
  have hcase : p.degree? = none ∨ p.degree? = some 0 := by
    rcases hd : p.degree? with _ | n
    · exact Or.inl rfl
    · rcases n with _ | m
      · exact Or.inr rfl
      · rw [hd] at h; simp at h
  rcases hcase with hc | hc <;> simp only [Hex.ZPoly.sturmChain, hc]

/-- A Sturm count of `1` forces positive degree: a degree-`≤ 0` input has the
empty chain, whose count is `0` at every pair of endpoints. -/
theorem degree_pos_of_count_one (iso : Hex.RealRootIsolation p) :
    1 ≤ (p.degree?).getD 0 := by
  by_contra h
  have hz : (p.degree?).getD 0 = 0 := by omega
  have hc := iso.count_one
  unfold Hex.sturmCount at hc
  rw [sturmChain_eq_nil_of_degree_nonpos hz] at hc
  simp only [Hex.sturmVarAt, List.map_nil, Hex.signVar, List.filter_nil,
    Hex.signVar.go, Nat.cast_zero, sub_zero] at hc
  exact absurd hc (by norm_num)

/-- A nonzero executable polynomial has a `some` degree: `degree? = none` means
zero stored size, which pins every coefficient (hence the polynomial) to zero. -/
theorem degree?_ne_none (hp0 : p ≠ 0) : p.degree? ≠ none := by
  intro h
  have hsz : p.size = 0 := (Hex.DensePoly.degree?_eq_none_iff p).mp h
  apply hp0
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.DensePoly.coeff_zero]
  exact Hex.DensePoly.coeff_eq_zero_of_size_le p (by omega)

/-- **Isolation soundness.** A certified isolation of `p` names exactly one real
root of `toPolyℝ p` in its half-open interval `(lower, upper]`. -/
theorem RealRootIsolation.exists_unique_root (hp : Hex.ZPoly.SquareFreeRat p)
    (iso : Hex.RealRootIsolation p) :
    ∃! r : ℝ, (toPolyℝ p).IsRoot r ∧
      Dyadic.toReal iso.interval.lower < r ∧ r ≤ Dyadic.toReal iso.interval.upper := by
  have hdeg : 1 ≤ (p.degree?).getD 0 := degree_pos_of_count_one iso
  have hp0 : p ≠ 0 := by
    intro hh; rw [hh] at hdeg; simp only [Hex.DensePoly.degree?_zero_getD] at hdeg; omega
  have hP0 : toPolyℝ p ≠ 0 := fun h => hp0 (toPolyℝ_eq_zero_iff.mp h)
  -- The filtered root multiset has card `1`.
  have hc := iso.count_one
  rw [sturmCount_eq_card_roots p hdeg hp iso.interval] at hc
  set M := (toPolyℝ p).roots.filter
    (fun r => Dyadic.toReal iso.interval.lower < r ∧ r ≤ Dyadic.toReal iso.interval.upper)
    with hMdef
  have hM : Multiset.card M = 1 := by exact_mod_cast hc
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hM
  have hamem : a ∈ M := by rw [ha]; exact Multiset.mem_singleton_self a
  rw [hMdef, Multiset.mem_filter] at hamem
  obtain ⟨haroots, halo, hahi⟩ := hamem
  have haroot : (toPolyℝ p).IsRoot a := (Polynomial.mem_roots'.mp haroots).2
  refine ⟨a, ⟨haroot, halo, hahi⟩, ?_⟩
  rintro y ⟨hyroot, hylo, hyhi⟩
  have hyM : y ∈ M := by
    rw [hMdef, Multiset.mem_filter]
    exact ⟨Polynomial.mem_roots'.mpr ⟨hP0, hyroot⟩, hylo, hyhi⟩
  rw [ha, Multiset.mem_singleton] at hyM
  exact hyM

/-- The positive-degree core of `RealRootIsolations.isolates`: the injective
root map from isolations hits `rootCount p` distinct roots, which is all of
them. -/
private theorem isolates_of_degree_pos (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) (out : Hex.RealRootIsolations p) :
    ∀ r : ℝ, (toPolyℝ p).IsRoot r →
      ∃! iso ∈ out.isolations.toList,
        Dyadic.toReal iso.interval.lower < r ∧ r ≤ Dyadic.toReal iso.interval.upper := by
  have hp0 : p ≠ 0 := by
    intro hh; rw [hh] at hdeg; simp only [Hex.DensePoly.degree?_zero_getD] at hdeg; omega
  have hP0 : toPolyℝ p ≠ 0 := fun h => hp0 (toPolyℝ_eq_zero_iff.mp h)
  have hsep : (toPolyℝ p).Separable := separable_toPolyℝ p ((squareFreeRat_iff p hp0).mp hp)
  have hnodup : (toPolyℝ p).roots.Nodup := nodup_roots hsep
  -- The unique root of each isolation.
  have H : ∀ i : Fin out.isolations.size, ∃ y : ℝ,
      ((toPolyℝ p).IsRoot y ∧ Dyadic.toReal out.isolations[i].interval.lower < y ∧
          y ≤ Dyadic.toReal out.isolations[i].interval.upper) ∧
        ∀ z, ((toPolyℝ p).IsRoot z ∧ Dyadic.toReal out.isolations[i].interval.lower < z ∧
          z ≤ Dyadic.toReal out.isolations[i].interval.upper) → z = y :=
    fun i => RealRootIsolation.exists_unique_root hp out.isolations[i]
  choose theRoot hroot huniq using H
  -- `theRoot` is strictly increasing along the ordered isolations, hence injective.
  have hmono : ∀ i j : Fin out.isolations.size, (i : ℕ) < (j : ℕ) →
      theRoot i < theRoot j := by
    intro i j hij
    have hord := out.ordered i j hij
    calc theRoot i ≤ Dyadic.toReal out.isolations[i].interval.upper := (hroot i).2.2
      _ ≤ Dyadic.toReal out.isolations[j].interval.lower := toReal_le_toReal hord
      _ < theRoot j := (hroot j).2.1
  have hinj : Function.Injective theRoot := by
    intro i j hij
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
    · exact absurd hij (ne_of_lt (hmono i j h))
    · exact Fin.ext h
    · exact absurd hij.symm (ne_of_lt (hmono j i h))
  -- The isolations' roots exhaust the root finset.
  set S := (toPolyℝ p).roots.toFinset with hSdef
  have hmemS : ∀ i, theRoot i ∈ S := fun i =>
    Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hP0, (hroot i).1⟩)
  have hScard : S.card = out.isolations.size := by
    rw [hSdef, Multiset.toFinset_card_of_nodup hnodup,
      ← rootCount_eq_card_roots p hdeg hp, ← out.complete]
  have himage : Finset.image theRoot Finset.univ = S := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hmemS i
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hScard]
  -- The main statement.
  intro r hr
  have hrS : r ∈ S := Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hP0, hr⟩)
  rw [← himage, Finset.mem_image] at hrS
  obtain ⟨i, -, hi_eq⟩ := hrS
  -- Existence: the `i`-th isolation contains `r`.
  have hmem_i : out.isolations[i] ∈ out.isolations.toList := Array.getElem_mem_toList _
  have hlo_i : Dyadic.toReal out.isolations[i].interval.lower < r := hi_eq ▸ (hroot i).2.1
  have hhi_i : r ≤ Dyadic.toReal out.isolations[i].interval.upper := hi_eq ▸ (hroot i).2.2
  refine ⟨out.isolations[i], ⟨hmem_i, hlo_i, hhi_i⟩, ?_⟩
  -- Uniqueness.
  rintro iso' ⟨hiso'mem, hiso'lo, hiso'hi⟩
  rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hiso'mem
  obtain ⟨j, hj, hjeq⟩ := hiso'mem
  have hjeq' : out.isolations[(⟨j, hj⟩ : Fin out.isolations.size)] = iso' := hjeq
  -- `r` is the unique root of the `j`-th isolation, so `theRoot j = r`.
  have hrj : r = theRoot ⟨j, hj⟩ := by
    refine huniq ⟨j, hj⟩ r ⟨hr, ?_, ?_⟩
    · rw [hjeq']; exact hiso'lo
    · rw [hjeq']; exact hiso'hi
  have hij : (⟨j, hj⟩ : Fin out.isolations.size) = i := by
    apply hinj; rw [← hrj, hi_eq]
  exact hjeq'.symm.trans
    (congrArg (fun k : Fin out.isolations.size => out.isolations[k]) hij)

/-- **Completeness of a run.** A complete isolation run of a nonzero, rationally
squarefree `p` names every real root of `toPolyℝ p` exactly once: each root lies
in exactly one of the emitted half-open intervals.

The `SquareFreeRat p` hypothesis alone is insufficient: for
`p = 0` (which passes `SquareFreeRat`) every real is a root while `complete`
forces zero isolations, so no root is captured. `p ≠ 0` is the honest
hypothesis: a nonzero constant has no roots (vacuous case), and the
positive-degree case is `isolates_of_degree_pos`. -/
theorem RealRootIsolations.isolates (hp0 : p ≠ 0)
    (hp : Hex.ZPoly.SquareFreeRat p) (out : Hex.RealRootIsolations p) :
    ∀ r : ℝ, (toPolyℝ p).IsRoot r →
      ∃! iso ∈ out.isolations.toList,
        Dyadic.toReal iso.interval.lower < r ∧ r ≤ Dyadic.toReal iso.interval.upper := by
  rcases hd : p.degree? with _ | n
  · exact absurd hd (degree?_ne_none hp0)
  · rcases n with _ | n
    · -- A nonzero constant: no roots, so the statement is vacuous.
      intro r hr
      exfalso
      have hP0 : toPolyℝ p ≠ 0 := fun h => hp0 (toPolyℝ_eq_zero_iff.mp h)
      have hnd : (toPolyℝ p).natDegree = 0 := by
        rw [natDegree_toPolyℝ, hd]; rfl
      have hC := Polynomial.eq_C_of_natDegree_eq_zero hnd
      have hc0 : (toPolyℝ p).coeff 0 = 0 := by
        have := hr
        rw [Polynomial.IsRoot, hC, Polynomial.eval_C] at this
        exact this
      exact hP0 (by rw [hC, hc0, Polynomial.C_0])
    · exact isolates_of_degree_pos (by simp [hd]) hp out

/-- Dot-notation alias in the `Hex` namespace for
`HexRealRootsMathlib.RealRootIsolation.exists_unique_root`, so
`iso.exists_unique_root` resolves directly on a `Hex.RealRootIsolation`. -/
theorem _root_.Hex.RealRootIsolation.exists_unique_root
    (hp : Hex.ZPoly.SquareFreeRat p) (iso : Hex.RealRootIsolation p) :
    ∃! r : ℝ, (toPolyℝ p).IsRoot r ∧
      Dyadic.toReal iso.interval.lower < r ∧ r ≤ Dyadic.toReal iso.interval.upper :=
  HexRealRootsMathlib.RealRootIsolation.exists_unique_root hp iso

/-- Dot-notation alias in the `Hex` namespace for
`HexRealRootsMathlib.RealRootIsolations.isolates`, so `out.isolates` resolves
directly on a `Hex.RealRootIsolations`. -/
theorem _root_.Hex.RealRootIsolations.isolates (hp0 : p ≠ 0)
    (hp : Hex.ZPoly.SquareFreeRat p) (out : Hex.RealRootIsolations p) :
    ∀ r : ℝ, (toPolyℝ p).IsRoot r →
      ∃! iso ∈ out.isolations.toList,
        Dyadic.toReal iso.interval.lower < r ∧ r ≤ Dyadic.toReal iso.interval.upper :=
  HexRealRootsMathlib.RealRootIsolations.isolates hp0 hp out

end

end HexRealRootsMathlib
