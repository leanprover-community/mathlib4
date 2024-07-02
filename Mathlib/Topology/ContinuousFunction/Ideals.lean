/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.NormedSpace.Units
import Mathlib.Topology.Algebra.Module.CharacterSpace

#align_import topology.continuous_function.ideals from "leanprover-community/mathlib"@"c2258f7bf086b17eac0929d635403780c39e239f"

/-!
# Ideals of continuous functions

For a topological semiring `R` and a topological space `X` there is a Galois connection between
`Ideal C(X, R)` and `Set X` given by sending each `I : Ideal C(X, R)` to
`{x : X | ∀ f ∈ I, f x = 0}ᶜ` and mapping `s : Set X` to the ideal with carrier
`{f : C(X, R) | ∀ x ∈ sᶜ, f x = 0}`, and we call these maps `ContinuousMap.setOfIdeal` and
`ContinuousMap.idealOfSet`. As long as `R` is Hausdorff, `ContinuousMap.setOfIdeal I` is open,
and if, in addition, `X` is locally compact, then `ContinuousMap.setOfIdeal s` is closed.

When `R = 𝕜` with `RCLike 𝕜` and `X` is compact Hausdorff, then this Galois connection can be
improved to a true Galois correspondence (i.e., order isomorphism) between the type `opens X` and
the subtype of closed ideals of `C(X, 𝕜)`. Because we do not have a bundled type of closed ideals,
we simply register this as a Galois insertion between `Ideal C(X, 𝕜)` and `opens X`, which is
`ContinuousMap.idealOpensGI`. Consequently, the maximal ideals of `C(X, 𝕜)` are precisely those
ideals corresponding to (complements of) singletons in `X`.

In addition, when `X` is locally compact and `𝕜` is a nontrivial topological integral domain, then
there is a natural continuous map from `X` to `WeakDual.characterSpace 𝕜 C(X, 𝕜)` given by point
evaluation, which is herein called `WeakDual.CharacterSpace.continuousMapEval`. Again, when `X` is
compact Hausdorff and `RCLike 𝕜`, more can be obtained. In particular, in that context this map is
bijective, and since the domain is compact and the codomain is Hausdorff, it is a homeomorphism,
herein called `WeakDual.CharacterSpace.homeoEval`.

## Main definitions

* `ContinuousMap.idealOfSet`: ideal of functions which vanish on the complement of a set.
* `ContinuousMap.setOfIdeal`: complement of the set on which all functions in the ideal vanish.
* `ContinuousMap.opensOfIdeal`: `ContinuousMap.setOfIdeal` as a term of `opens X`.
* `ContinuousMap.idealOpensGI`: The Galois insertion `ContinuousMap.opensOfIdeal` and
  `fun s ↦ ContinuousMap.idealOfSet ↑s`.
* `WeakDual.CharacterSpace.continuousMapEval`: the natural continuous map from a locally compact
  topological space `X` to the `WeakDual.characterSpace 𝕜 C(X, 𝕜)` which sends `x : X` to point
  evaluation at `x`, with modest hypothesis on `𝕜`.
* `WeakDual.CharacterSpace.homeoEval`: this is `WeakDual.CharacterSpace.continuousMapEval`
  upgraded to a homeomorphism when `X` is compact Hausdorff and `RCLike 𝕜`.

## Main statements

* `ContinuousMap.idealOfSet_ofIdeal_eq_closure`: when `X` is compact Hausdorff and
  `RCLike 𝕜`, `idealOfSet 𝕜 (setOfIdeal I) = I.closure` for any ideal `I : Ideal C(X, 𝕜)`.
* `ContinuousMap.setOfIdeal_ofSet_eq_interior`: when `X` is compact Hausdorff and `RCLike 𝕜`,
  `setOfIdeal (idealOfSet 𝕜 s) = interior s` for any `s : Set X`.
* `ContinuousMap.ideal_isMaximal_iff`: when `X` is compact Hausdorff and `RCLike 𝕜`, a closed
  ideal of `C(X, 𝕜)` is maximal if and only if it is `idealOfSet 𝕜 {x}ᶜ` for some `x : X`.

## Implementation details

Because there does not currently exist a bundled type of closed ideals, we don't provide the actual
order isomorphism described above, and instead we only consider the Galois insertion
`ContinuousMap.idealOpensGI`.

## Tags

ideal, continuous function, compact, Hausdorff
-/


open scoped NNReal

namespace ContinuousMap

open TopologicalSpace

section TopologicalRing

variable {X R : Type*} [TopologicalSpace X] [Semiring R]
variable [TopologicalSpace R] [TopologicalSemiring R]
variable (R)

/-- Given a topological ring `R` and `s : Set X`, construct the ideal in `C(X, R)` of functions
which vanish on the complement of `s`. -/
def idealOfSet (s : Set X) : Ideal C(X, R) where
  carrier := {f : C(X, R) | ∀ x ∈ sᶜ, f x = 0}
  add_mem' {f g} hf hg x hx := by simp [hf x hx, hg x hx, coe_add, Pi.add_apply, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c f hf x hx := mul_zero (c x) ▸ congr_arg (fun y => c x * y) (hf x hx)
#align continuous_map.ideal_of_set ContinuousMap.idealOfSet

theorem idealOfSet_closed [T2Space R] (s : Set X) :
    IsClosed (idealOfSet R s : Set C(X, R)) := by
  simp only [idealOfSet, Submodule.coe_set_mk, Set.setOf_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_eq (continuous_eval_const x) continuous_const
#align continuous_map.ideal_of_set_closed ContinuousMap.idealOfSet_closed

variable {R}

theorem mem_idealOfSet {s : Set X} {f : C(X, R)} :
    f ∈ idealOfSet R s ↔ ∀ ⦃x : X⦄, x ∈ sᶜ → f x = 0 := by
  convert Iff.rfl
#align continuous_map.mem_ideal_of_set ContinuousMap.mem_idealOfSet

theorem not_mem_idealOfSet {s : Set X} {f : C(X, R)} : f ∉ idealOfSet R s ↔ ∃ x ∈ sᶜ, f x ≠ 0 := by
  simp_rw [mem_idealOfSet]; push_neg; rfl
#align continuous_map.not_mem_ideal_of_set ContinuousMap.not_mem_idealOfSet

/-- Given an ideal `I` of `C(X, R)`, construct the set of points for which every function in the
ideal vanishes on the complement. -/
def setOfIdeal (I : Ideal C(X, R)) : Set X :=
  {x : X | ∀ f ∈ I, (f : C(X, R)) x = 0}ᶜ
#align continuous_map.set_of_ideal ContinuousMap.setOfIdeal

theorem not_mem_setOfIdeal {I : Ideal C(X, R)} {x : X} :
    x ∉ setOfIdeal I ↔ ∀ ⦃f : C(X, R)⦄, f ∈ I → f x = 0 := by
  rw [← Set.mem_compl_iff, setOfIdeal, compl_compl, Set.mem_setOf]
#align continuous_map.not_mem_set_of_ideal ContinuousMap.not_mem_setOfIdeal

theorem mem_setOfIdeal {I : Ideal C(X, R)} {x : X} :
    x ∈ setOfIdeal I ↔ ∃ f ∈ I, (f : C(X, R)) x ≠ 0 := by
  simp_rw [setOfIdeal, Set.mem_compl_iff, Set.mem_setOf]; push_neg; rfl
#align continuous_map.mem_set_of_ideal ContinuousMap.mem_setOfIdeal

theorem setOfIdeal_open [T2Space R] (I : Ideal C(X, R)) : IsOpen (setOfIdeal I) := by
  simp only [setOfIdeal, Set.setOf_forall, isOpen_compl_iff]
  exact
    isClosed_iInter fun f =>
      isClosed_iInter fun _ => isClosed_eq (map_continuous f) continuous_const
#align continuous_map.set_of_ideal_open ContinuousMap.setOfIdeal_open

/-- The open set `ContinuousMap.setOfIdeal I` realized as a term of `opens X`. -/
@[simps]
def opensOfIdeal [T2Space R] (I : Ideal C(X, R)) : Opens X :=
  ⟨setOfIdeal I, setOfIdeal_open I⟩
#align continuous_map.opens_of_ideal ContinuousMap.opensOfIdeal

@[simp]
theorem setOfTop_eq_univ [Nontrivial R] : setOfIdeal (⊤ : Ideal C(X, R)) = Set.univ :=
  Set.univ_subset_iff.mp fun _ _ => mem_setOfIdeal.mpr ⟨1, Submodule.mem_top, one_ne_zero⟩
#align continuous_map.set_of_top_eq_univ ContinuousMap.setOfTop_eq_univ

@[simp]
theorem idealOfEmpty_eq_bot : idealOfSet R (∅ : Set X) = ⊥ :=
  Ideal.ext fun f => by
    simp only [mem_idealOfSet, Set.compl_empty, Set.mem_univ, forall_true_left, Ideal.mem_bot,
      DFunLike.ext_iff, zero_apply]
#align continuous_map.ideal_of_empty_eq_bot ContinuousMap.idealOfEmpty_eq_bot

@[simp]
theorem mem_idealOfSet_compl_singleton (x : X) (f : C(X, R)) :
    f ∈ idealOfSet R ({x}ᶜ : Set X) ↔ f x = 0 := by
  simp only [mem_idealOfSet, compl_compl, Set.mem_singleton_iff, forall_eq]
#align continuous_map.mem_ideal_of_set_compl_singleton ContinuousMap.mem_idealOfSet_compl_singleton

variable (X R)

theorem ideal_gc : GaloisConnection (setOfIdeal : Ideal C(X, R) → Set X) (idealOfSet R) := by
  refine fun I s => ⟨fun h f hf => ?_, fun h x hx => ?_⟩
  · by_contra h'
    rcases not_mem_idealOfSet.mp h' with ⟨x, hx, hfx⟩
    exact hfx (not_mem_setOfIdeal.mp (mt (@h x) hx) hf)
  · obtain ⟨f, hf, hfx⟩ := mem_setOfIdeal.mp hx
    by_contra hx'
    exact not_mem_idealOfSet.mpr ⟨x, hx', hfx⟩ (h hf)
#align continuous_map.ideal_gc ContinuousMap.ideal_gc

end TopologicalRing

section RCLike

open RCLike

variable {X 𝕜 : Type*} [RCLike 𝕜] [TopologicalSpace X]

/-- An auxiliary lemma used in the proof of `ContinuousMap.idealOfSet_ofIdeal_eq_closure` which may
be useful on its own. -/
theorem exists_mul_le_one_eqOn_ge (f : C(X, ℝ≥0)) {c : ℝ≥0} (hc : 0 < c) :
    ∃ g : C(X, ℝ≥0), (∀ x : X, (g * f) x ≤ 1) ∧ {x : X | c ≤ f x}.EqOn (g * f) 1 :=
  ⟨{  toFun := (f ⊔ const X c)⁻¹
      continuous_toFun :=
        ((map_continuous f).sup <| map_continuous _).inv₀ fun _ => (hc.trans_le le_sup_right).ne' },
    fun x =>
    (inv_mul_le_iff (hc.trans_le le_sup_right)).mpr ((mul_one (f x ⊔ c)).symm ▸ le_sup_left),
    fun x hx => by
    simpa only [coe_const, ge_iff_le, mul_apply, coe_mk, Pi.inv_apply, Pi.sup_apply,
      Function.const_apply, sup_eq_left.mpr (Set.mem_setOf.mp hx), ne_eq, Pi.one_apply]
      using inv_mul_cancel (hc.trans_le hx).ne' ⟩
#align continuous_map.exists_mul_le_one_eq_on_ge ContinuousMap.exists_mul_le_one_eqOn_ge

variable [CompactSpace X] [T2Space X]

@[simp]
theorem idealOfSet_ofIdeal_eq_closure (I : Ideal C(X, 𝕜)) :
    idealOfSet 𝕜 (setOfIdeal I) = I.closure := by
  /- Since `idealOfSet 𝕜 (setOfIdeal I)` is closed and contains `I`, it contains `I.closure`.
    For the reverse inclusion, given `f ∈ idealOfSet 𝕜 (setOfIdeal I)` and `(ε : ℝ≥0) > 0` it
    suffices to show that `f` is within `ε` of `I`. -/
  refine le_antisymm ?_
      ((idealOfSet_closed 𝕜 <| setOfIdeal I).closure_subset_iff.mpr fun f hf x hx =>
        not_mem_setOfIdeal.mp hx hf)
  refine (fun f hf => Metric.mem_closure_iff.mpr fun ε hε => ?_)
  lift ε to ℝ≥0 using hε.lt.le
  replace hε := show (0 : ℝ≥0) < ε from hε
  simp_rw [dist_nndist]
  norm_cast
  -- Let `t := {x : X | ε / 2 ≤ ‖f x‖₊}}` which is closed and disjoint from `set_of_ideal I`.
  set t := {x : X | ε / 2 ≤ ‖f x‖₊}
  have ht : IsClosed t := isClosed_le continuous_const (map_continuous f).nnnorm
  have htI : Disjoint t (setOfIdeal I)ᶜ := by
    refine Set.subset_compl_iff_disjoint_left.mp fun x hx => ?_
    simpa only [t, Set.mem_setOf, Set.mem_compl_iff, not_le] using
      (nnnorm_eq_zero.mpr (mem_idealOfSet.mp hf hx)).trans_lt (half_pos hε)
  /- It suffices to produce `g : C(X, ℝ≥0)` which takes values in `[0,1]` and is constantly `1` on
    `t` such that when composed with the natural embedding of `ℝ≥0` into `𝕜` lies in the ideal `I`.
    Indeed, then `‖f - f * ↑g‖ ≤ ‖f * (1 - ↑g)‖ ≤ ⨆ ‖f * (1 - ↑g) x‖`. When `x ∉ t`, `‖f x‖ < ε / 2`
    and `‖(1 - ↑g) x‖ ≤ 1`, and when `x ∈ t`, `(1 - ↑g) x = 0`, and clearly `f * ↑g ∈ I`. -/
  suffices
    ∃ g : C(X, ℝ≥0), (algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g ∈ I ∧ (∀ x, g x ≤ 1) ∧ t.EqOn g 1 by
    obtain ⟨g, hgI, hg, hgt⟩ := this
    refine ⟨f * (algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g, I.mul_mem_left f hgI, ?_⟩
    rw [nndist_eq_nnnorm]
    refine (nnnorm_lt_iff _ hε).2 fun x => ?_
    simp only [coe_sub, coe_mul, Pi.sub_apply, Pi.mul_apply]
    by_cases hx : x ∈ t
    · simpa only [hgt hx, comp_apply, Pi.one_apply, ContinuousMap.coe_coe, algebraMapCLM_apply,
        map_one, mul_one, sub_self, nnnorm_zero] using hε
    · refine lt_of_le_of_lt ?_ (half_lt_self hε)
      have :=
        calc
          ‖((1 - (algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) x : 𝕜)‖₊ =
              ‖1 - algebraMap ℝ≥0 𝕜 (g x)‖₊ := by
            simp only [coe_sub, coe_one, coe_comp, ContinuousMap.coe_coe, Pi.sub_apply,
              Pi.one_apply, Function.comp_apply, algebraMapCLM_apply]
          _ = ‖algebraMap ℝ≥0 𝕜 (1 - g x)‖₊ := by
            simp only [Algebra.algebraMap_eq_smul_one, NNReal.smul_def, ge_iff_le,
              NNReal.coe_sub (hg x), NNReal.coe_one, sub_smul, one_smul]
          _ ≤ 1 := (nnnorm_algebraMap_nnreal 𝕜 (1 - g x)).trans_le tsub_le_self
      calc
        ‖f x - f x * (algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g x‖₊ =
            ‖f x * (1 - (algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) x‖₊ := by
          simp only [mul_sub, coe_sub, coe_one, Pi.sub_apply, Pi.one_apply, mul_one]
        _ ≤ ε / 2 * ‖(1 - (algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) x‖₊ :=
          ((nnnorm_mul_le _ _).trans
            (mul_le_mul_right' (not_le.mp <| show ¬ε / 2 ≤ ‖f x‖₊ from hx).le _))
        _ ≤ ε / 2 := by simpa only [mul_one] using mul_le_mul_left' this _
  /- There is some `g' : C(X, ℝ≥0)` which is strictly positive on `t` such that the composition
    `↑g` with the natural embedding of `ℝ≥0` into `𝕜` lies in `I`. This follows from compactness of
    `t` and that we can do it in any neighborhood of a point `x ∈ t`. Indeed, since `x ∈ t`, then
    `fₓ x ≠ 0` for some `fₓ ∈ I` and so `fun y ↦ ‖(star fₓ * fₓ) y‖₊` is strictly posiive in a
    neighborhood of `y`. Moreover, `(‖(star fₓ * fₓ) y‖₊ : 𝕜) = (star fₓ * fₓ) y`, so composition of
    this map with the natural embedding is just `star fₓ * fₓ ∈ I`. -/
  have : ∃ g' : C(X, ℝ≥0), (algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g' ∈ I ∧ ∀ x ∈ t, 0 < g' x := by
    refine ht.isCompact.induction_on ?_ ?_ ?_ ?_
    · refine ⟨0, ?_, fun x hx => False.elim hx⟩
      convert I.zero_mem
      ext
      simp only [comp_apply, zero_apply, ContinuousMap.coe_coe, map_zero]
    · rintro s₁ s₂ hs ⟨g, hI, hgt⟩; exact ⟨g, hI, fun x hx => hgt x (hs hx)⟩
    · rintro s₁ s₂ ⟨g₁, hI₁, hgt₁⟩ ⟨g₂, hI₂, hgt₂⟩
      refine ⟨g₁ + g₂, ?_, fun x hx => ?_⟩
      · convert I.add_mem hI₁ hI₂
        ext y
        simp only [coe_add, Pi.add_apply, map_add, coe_comp, Function.comp_apply,
          ContinuousMap.coe_coe]
      · rcases hx with (hx | hx)
        · simpa only [zero_add] using add_lt_add_of_lt_of_le (hgt₁ x hx) zero_le'
        · simpa only [zero_add] using add_lt_add_of_le_of_lt zero_le' (hgt₂ x hx)
    · intro x hx
      replace hx := htI.subset_compl_right hx
      rw [compl_compl, mem_setOfIdeal] at hx
      obtain ⟨g, hI, hgx⟩ := hx
      have := (map_continuous g).continuousAt.eventually_ne hgx
      refine
        ⟨{y : X | g y ≠ 0} ∩ t,
          mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨_, this, Set.Subset.rfl⟩,
          ⟨⟨fun x => ‖g x‖₊ ^ 2, (map_continuous g).nnnorm.pow 2⟩, ?_, fun x hx =>
            pow_pos (norm_pos_iff.mpr hx.1) 2⟩⟩
      convert I.mul_mem_left (star g) hI
      ext
      simp only [comp_apply, ContinuousMap.coe_coe, coe_mk, algebraMapCLM_toFun, map_pow,
        mul_apply, star_apply, star_def]
      simp only [normSq_eq_def', RCLike.conj_mul, ofReal_pow]
      rfl
  /- Get the function `g'` which is guaranteed to exist above. By the extreme value theorem and
    compactness of `t`, there is some `0 < c` such that `c ≤ g' x` for all `x ∈ t`. Then by
    `exists_mul_le_one_eqOn_ge` there is some `g` for which `g * g'` is the desired function. -/
  obtain ⟨g', hI', hgt'⟩ := this
  obtain ⟨c, hc, hgc'⟩ : ∃ c > 0, ∀ y : X, y ∈ t → c ≤ g' y :=
    t.eq_empty_or_nonempty.elim
      (fun ht' => ⟨1, zero_lt_one, fun y hy => False.elim (by rwa [ht'] at hy)⟩) fun ht' =>
      let ⟨x, hx, hx'⟩ := ht.isCompact.exists_isMinOn ht' (map_continuous g').continuousOn
      ⟨g' x, hgt' x hx, hx'⟩
  obtain ⟨g, hg, hgc⟩ := exists_mul_le_one_eqOn_ge g' hc
  refine ⟨g * g', ?_, hg, hgc.mono hgc'⟩
  convert I.mul_mem_left ((algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) hI'
  ext
  simp only [algebraMapCLM_coe, comp_apply, mul_apply, ContinuousMap.coe_coe, map_mul]
#align continuous_map.ideal_of_set_of_ideal_eq_closure ContinuousMap.idealOfSet_ofIdeal_eq_closure

theorem idealOfSet_ofIdeal_isClosed {I : Ideal C(X, 𝕜)} (hI : IsClosed (I : Set C(X, 𝕜))) :
    idealOfSet 𝕜 (setOfIdeal I) = I :=
  (idealOfSet_ofIdeal_eq_closure I).trans (Ideal.ext <| Set.ext_iff.mp hI.closure_eq)
#align continuous_map.ideal_of_set_of_ideal_is_closed ContinuousMap.idealOfSet_ofIdeal_isClosed

variable (𝕜)

@[simp]
theorem setOfIdeal_ofSet_eq_interior (s : Set X) : setOfIdeal (idealOfSet 𝕜 s) = interior s := by
  refine
    Set.Subset.antisymm
      ((setOfIdeal_open (idealOfSet 𝕜 s)).subset_interior_iff.mpr fun x hx =>
        let ⟨f, hf, hfx⟩ := mem_setOfIdeal.mp hx
        Set.not_mem_compl_iff.mp (mt (@hf x) hfx))
      fun x hx => ?_
  -- If `x ∉ closure sᶜ`, we must produce `f : C(X, 𝕜)` which is zero on `sᶜ` and `f x ≠ 0`.
  rw [← compl_compl (interior s), ← closure_compl] at hx
  simp_rw [mem_setOfIdeal, mem_idealOfSet]
  /- Apply Urysohn's lemma to get `g : C(X, ℝ)` which is zero on `sᶜ` and `g x ≠ 0`, then compose
    with the natural embedding `ℝ ↪ 𝕜` to produce the desired `f`. -/
  obtain ⟨g, hgs, hgx : Set.EqOn g 1 {x}, -⟩ :=
    exists_continuous_zero_one_of_isClosed isClosed_closure isClosed_singleton
      (Set.disjoint_singleton_right.mpr hx)
  exact
    ⟨⟨fun x => g x, continuous_ofReal.comp (map_continuous g)⟩, by
      simpa only [coe_mk, ofReal_eq_zero] using fun x hx => hgs (subset_closure hx), by
      simpa only [coe_mk, hgx (Set.mem_singleton x), Pi.one_apply, RCLike.ofReal_one] using
        one_ne_zero⟩
#align continuous_map.set_of_ideal_of_set_eq_interior ContinuousMap.setOfIdeal_ofSet_eq_interior

theorem setOfIdeal_ofSet_of_isOpen {s : Set X} (hs : IsOpen s) : setOfIdeal (idealOfSet 𝕜 s) = s :=
  (setOfIdeal_ofSet_eq_interior 𝕜 s).trans hs.interior_eq
#align continuous_map.set_of_ideal_of_set_of_is_open ContinuousMap.setOfIdeal_ofSet_of_isOpen

variable (X)

/-- The Galois insertion `ContinuousMap.opensOfIdeal : Ideal C(X, 𝕜) → Opens X` and
`fun s ↦ ContinuousMap.idealOfSet ↑s`. -/
@[simps]
def idealOpensGI :
    GaloisInsertion (opensOfIdeal : Ideal C(X, 𝕜) → Opens X) fun s => idealOfSet 𝕜 s where
  choice I _ := opensOfIdeal I.closure
  gc I s := ideal_gc X 𝕜 I s
  le_l_u s := (setOfIdeal_ofSet_of_isOpen 𝕜 s.isOpen).ge
  choice_eq I hI :=
    congr_arg _ <|
      Ideal.ext
        (Set.ext_iff.mp
          (isClosed_of_closure_subset <|
              (idealOfSet_ofIdeal_eq_closure I ▸ hI : I.closure ≤ I)).closure_eq)
#align continuous_map.ideal_opens_gi ContinuousMap.idealOpensGI

variable {X}

theorem idealOfSet_isMaximal_iff (s : Opens X) :
    (idealOfSet 𝕜 (s : Set X)).IsMaximal ↔ IsCoatom s := by
  rw [Ideal.isMaximal_def]
  refine (idealOpensGI X 𝕜).isCoatom_iff (fun I hI => ?_) s
  rw [← Ideal.isMaximal_def] at hI
  exact idealOfSet_ofIdeal_isClosed inferInstance
#align continuous_map.ideal_of_set_is_maximal_iff ContinuousMap.idealOfSet_isMaximal_iff

theorem idealOf_compl_singleton_isMaximal (x : X) : (idealOfSet 𝕜 ({x}ᶜ : Set X)).IsMaximal :=
  (idealOfSet_isMaximal_iff 𝕜 (Closeds.singleton x).compl).mpr <| Opens.isCoatom_iff.mpr ⟨x, rfl⟩
#align continuous_map.ideal_of_compl_singleton_is_maximal ContinuousMap.idealOf_compl_singleton_isMaximal

variable {𝕜}

theorem setOfIdeal_eq_compl_singleton (I : Ideal C(X, 𝕜)) [hI : I.IsMaximal] :
    ∃ x : X, setOfIdeal I = {x}ᶜ := by
  have h : (idealOfSet 𝕜 (setOfIdeal I)).IsMaximal :=
    (idealOfSet_ofIdeal_isClosed (inferInstance : IsClosed (I : Set C(X, 𝕜)))).symm ▸ hI
  obtain ⟨x, hx⟩ := Opens.isCoatom_iff.1 ((idealOfSet_isMaximal_iff 𝕜 (opensOfIdeal I)).1 h)
  exact ⟨x, congr_arg (fun (s : Opens X) => (s : Set X)) hx⟩
#align continuous_map.set_of_ideal_eq_compl_singleton ContinuousMap.setOfIdeal_eq_compl_singleton

theorem ideal_isMaximal_iff (I : Ideal C(X, 𝕜)) [hI : IsClosed (I : Set C(X, 𝕜))] :
    I.IsMaximal ↔ ∃ x : X, idealOfSet 𝕜 {x}ᶜ = I := by
  refine
    ⟨?_, fun h =>
      let ⟨x, hx⟩ := h
      hx ▸ idealOf_compl_singleton_isMaximal 𝕜 x⟩
  intro hI'
  obtain ⟨x, hx⟩ := setOfIdeal_eq_compl_singleton I
  exact
    ⟨x, by
      simpa only [idealOfSet_ofIdeal_eq_closure, I.closure_eq_of_isClosed hI] using
        congr_arg (idealOfSet 𝕜) hx.symm⟩
#align continuous_map.ideal_is_maximal_iff ContinuousMap.ideal_isMaximal_iff

end RCLike

end ContinuousMap

namespace WeakDual

namespace CharacterSpace

open Function ContinuousMap

variable (X 𝕜 : Type*) [TopologicalSpace X]

section ContinuousMapEval

variable [LocallyCompactSpace X] [CommRing 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜]
variable [Nontrivial 𝕜] [NoZeroDivisors 𝕜]

/-- The natural continuous map from a locally compact topological space `X` to the
`WeakDual.characterSpace 𝕜 C(X, 𝕜)` which sends `x : X` to point evaluation at `x`. -/
def continuousMapEval : C(X, characterSpace 𝕜 C(X, 𝕜)) where
  toFun x :=
    ⟨{  toFun := fun f => f x
        map_add' := fun f g => rfl
        map_smul' := fun z f => rfl
        cont := continuous_eval_const x }, by
        rw [CharacterSpace.eq_set_map_one_map_mul]; exact ⟨rfl, fun f g => rfl⟩⟩
  continuous_toFun := by
    exact Continuous.subtype_mk (continuous_of_continuous_eval map_continuous) _
#align weak_dual.character_space.continuous_map_eval WeakDual.CharacterSpace.continuousMapEval

@[simp]
theorem continuousMapEval_apply_apply (x : X) (f : C(X, 𝕜)) : continuousMapEval X 𝕜 x f = f x :=
  rfl
#align weak_dual.character_space.continuous_map_eval_apply_apply WeakDual.CharacterSpace.continuousMapEval_apply_apply

end ContinuousMapEval

variable [CompactSpace X] [T2Space X] [RCLike 𝕜]

theorem continuousMapEval_bijective : Bijective (continuousMapEval X 𝕜) := by
  refine ⟨fun x y hxy => ?_, fun φ => ?_⟩
  · contrapose! hxy
    rcases exists_continuous_zero_one_of_isClosed (isClosed_singleton : _root_.IsClosed {x})
        (isClosed_singleton : _root_.IsClosed {y}) (Set.disjoint_singleton.mpr hxy) with
      ⟨f, fx, fy, -⟩
    rw [DFunLike.ne_iff]
    use (⟨fun (x : ℝ) => (x : 𝕜), RCLike.continuous_ofReal⟩ : C(ℝ, 𝕜)).comp f
    simpa only [continuousMapEval_apply_apply, ContinuousMap.comp_apply, coe_mk, Ne,
      RCLike.ofReal_inj] using
      ((fx (Set.mem_singleton x)).symm ▸ (fy (Set.mem_singleton y)).symm ▸ zero_ne_one : f x ≠ f y)
  · obtain ⟨x, hx⟩ := (ideal_isMaximal_iff (RingHom.ker φ)).mp inferInstance
    refine ⟨x, CharacterSpace.ext_ker <| Ideal.ext fun f => ?_⟩
    simpa only [RingHom.mem_ker, continuousMapEval_apply_apply, mem_idealOfSet_compl_singleton,
      RingHom.mem_ker] using SetLike.ext_iff.mp hx f
#align weak_dual.character_space.continuous_map_eval_bijective WeakDual.CharacterSpace.continuousMapEval_bijective

/-- This is the natural homeomorphism between a compact Hausdorff space `X` and the
`WeakDual.characterSpace 𝕜 C(X, 𝕜)`. -/
noncomputable def homeoEval : X ≃ₜ characterSpace 𝕜 C(X, 𝕜) :=
  @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    { Equiv.ofBijective _ (continuousMapEval_bijective X 𝕜) with toFun := continuousMapEval X 𝕜 }
    (map_continuous (continuousMapEval X 𝕜))
#align weak_dual.character_space.homeo_eval WeakDual.CharacterSpace.homeoEval

end CharacterSpace

end WeakDual
