/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.TotallyBounded

/-!
# Absolutely convex sets

A set `s` in an commutative monoid `E` is called absolutely convex or disked if it is convex and
balanced. The importance of absolutely convex sets comes from the fact that every locally convex
topological vector space has a basis consisting of absolutely convex sets.

## Main definitions

* `absConvexHull`: the absolutely convex hull of a set `s` is the smallest absolutely convex set
  containing `s`;
* `closedAbsConvexHull`: the closed absolutely convex hull of a set `s` is the smallest absolutely
  convex set containing `s`;
* `gaugeSeminormFamily`: the seminorm family induced by all open absolutely convex neighborhoods
  of zero.

## Main statements

* `absConvexHull_eq_convexHull_balancedHull`: when the locally convex space is a module, the
  absolutely convex hull of a set `s` equals the convex hull of the balanced hull of `s`;
* `convexHull_union_neg_eq_absConvexHull`: the convex hull of `s ∪ -s` is the absolutely convex hull
  of `s`;
* `closedAbsConvexHull_closure_eq_closedAbsConvexHull` : the closed absolutely convex hull of the
  closure of `s` equals the closed absolutely convex hull of `s`;
* `with_gaugeSeminormFamily`: the topology of a locally convex space is induced by the family
  `gaugeSeminormFamily`.

## Implementation notes

Mathlib's definition of `Convex` requires the scalars to be an `OrderedSemiring` whereas the
definition of `Balanced` requires the scalars to be a `SeminormedRing`. Mathlib doesn't currently
have a concept of a semi-normed ordered ring, so we define a set as `AbsConvex` if it is balanced
over a `SeminormedRing` `𝕜` and convex over `ℝ`, assuming `IsScalarTower ℝ 𝕜 E` and
`SMulCommClass ℝ 𝕜 E` where required.

## Tags

disks, convex, balanced
-/


open NormedField Set

open NNReal Pointwise Topology

variable {𝕜 E : Type*}

section AbsolutelyConvex

variable (𝕜) [SeminormedRing 𝕜] [SMul 𝕜 E] [SMul ℝ E] [AddCommMonoid E]
/-- A set is absolutely convex if it is balanced and convex. Mathlib's definition of `Convex`
requires the scalars to be an `OrderedSemiring` whereas the definition of `Balanced` requires the
scalars to be a `SeminormedRing`. Mathlib doesn't currently have a concept of a semi-normed ordered
ring, so we define a set as `AbsConvex` if it is balanced over a `SeminormedRing` `𝕜` and convex
over `ℝ`. -/
def AbsConvex (s : Set E) : Prop := Balanced 𝕜 s ∧ Convex ℝ s

variable {𝕜}

theorem AbsConvex.empty : AbsConvex 𝕜 (∅ : Set E) := ⟨balanced_empty, convex_empty⟩

theorem AbsConvex.univ : AbsConvex 𝕜 (univ : Set E) := ⟨balanced_univ, convex_univ⟩

theorem AbsConvex.inter {s t : Set E} (hs : AbsConvex 𝕜 s) (ht : AbsConvex 𝕜 t) :
    AbsConvex 𝕜 (s ∩ t) := ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

theorem AbsConvex.sInter {S : Set (Set E)} (h : ∀ s ∈ S, AbsConvex 𝕜 s) : AbsConvex 𝕜 (⋂₀ S) :=
  ⟨.sInter fun s hs => (h s hs).1, convex_sInter fun s hs => (h s hs).2⟩

theorem AbsConvex.iInter {ι : Sort*} {s : ι → Set E} (h : ∀ i, AbsConvex 𝕜 (s i)) :
    AbsConvex 𝕜 (⋂ i, s i) :=
  sInter_range s ▸ AbsConvex.sInter <| forall_mem_range.2 h

variable (𝕜)

/-- The absolute convex hull of a set `s` is the minimal absolute convex set that includes `s`. -/
@[simps! isClosed]
def absConvexHull : ClosureOperator (Set E) :=
  .ofCompletePred (AbsConvex 𝕜) fun _ ↦ .sInter

variable {𝕜} {s : Set E}

theorem subset_absConvexHull : s ⊆ absConvexHull 𝕜 s :=
  (absConvexHull 𝕜).le_closure s

theorem absConvex_absConvexHull : AbsConvex 𝕜 (absConvexHull 𝕜 s) :=
  (absConvexHull 𝕜).isClosed_closure s

theorem balanced_absConvexHull : Balanced 𝕜 (absConvexHull 𝕜 s) :=
  absConvex_absConvexHull.1

theorem convex_absConvexHull : Convex ℝ (absConvexHull 𝕜 s) :=
  absConvex_absConvexHull.2

variable (𝕜 s) in
theorem absConvexHull_eq_iInter :
    absConvexHull 𝕜 s = ⋂ (t : Set E) (_ : s ⊆ t) (_ : AbsConvex 𝕜 t), t := by
  simp [absConvexHull, iInter_subtype, iInter_and]

variable {t : Set E} {x : E}

theorem mem_absConvexHull_iff : x ∈ absConvexHull 𝕜 s ↔ ∀ t, s ⊆ t → AbsConvex 𝕜 t → x ∈ t := by
  simp_rw [absConvexHull_eq_iInter, mem_iInter]

theorem absConvexHull_min : s ⊆ t → AbsConvex 𝕜 t → absConvexHull 𝕜 s ⊆ t :=
  (absConvexHull 𝕜).closure_min

theorem AbsConvex.absConvexHull_subset_iff (ht : AbsConvex 𝕜 t) : absConvexHull 𝕜 s ⊆ t ↔ s ⊆ t :=
  (show (absConvexHull 𝕜).IsClosed t from ht).closure_le_iff

@[mono, gcongr]
theorem absConvexHull_mono (hst : s ⊆ t) : absConvexHull 𝕜 s ⊆ absConvexHull 𝕜 t :=
  (absConvexHull 𝕜).monotone hst

lemma absConvexHull_eq_self : absConvexHull 𝕜 s = s ↔ AbsConvex 𝕜 s :=
  (absConvexHull 𝕜).isClosed_iff.symm

alias ⟨_, AbsConvex.absConvexHull_eq⟩ := absConvexHull_eq_self

@[simp]
theorem absConvexHull_univ : absConvexHull 𝕜 (univ : Set E) = univ :=
  ClosureOperator.closure_top (absConvexHull 𝕜)

@[simp]
theorem absConvexHull_empty : absConvexHull 𝕜 (∅ : Set E) = ∅ :=
  AbsConvex.empty.absConvexHull_eq

@[simp]
theorem absConvexHull_eq_empty : absConvexHull 𝕜 s = ∅ ↔ s = ∅ := by
  constructor
  · intro h
    rw [← Set.subset_empty_iff, ← h]
    exact subset_absConvexHull
  · rintro rfl
    exact absConvexHull_empty

@[simp]
theorem absConvexHull_nonempty : (absConvexHull 𝕜 s).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, nonempty_iff_ne_empty, Ne, Ne]
  exact not_congr absConvexHull_eq_empty

protected alias ⟨_, Set.Nonempty.absConvexHull⟩ := absConvexHull_nonempty

variable [TopologicalSpace E]

theorem absConvex_closed_sInter {S : Set (Set E)} (h : ∀ s ∈ S, AbsConvex 𝕜 s ∧ IsClosed s) :
    AbsConvex 𝕜 (⋂₀ S) ∧ IsClosed (⋂₀ S) :=
  ⟨AbsConvex.sInter (fun s hs => (h s hs).1), isClosed_sInter fun _ hs => (h _ hs).2⟩

variable (𝕜)

/-- The absolutely convex closed hull of a set `s` is the minimal absolutely convex closed set that
includes `s`. -/
@[simps! isClosed]
def closedAbsConvexHull : ClosureOperator (Set E) :=
  .ofCompletePred (fun s => AbsConvex 𝕜 s ∧ IsClosed s) fun _ ↦ absConvex_closed_sInter

variable {𝕜}

theorem absConvex_convexClosedHull {s : Set E} :
    AbsConvex 𝕜 (closedAbsConvexHull 𝕜 s) := ((closedAbsConvexHull 𝕜).isClosed_closure s).1

theorem isClosed_closedAbsConvexHull {s : Set E} :
    IsClosed (closedAbsConvexHull 𝕜 s) := ((closedAbsConvexHull 𝕜).isClosed_closure s).2

theorem subset_closedAbsConvexHull {s : Set E} : s ⊆ closedAbsConvexHull 𝕜 s :=
  (closedAbsConvexHull 𝕜).le_closure s

theorem closure_subset_closedAbsConvexHull {s : Set E} : closure s ⊆ closedAbsConvexHull 𝕜 s :=
  closure_minimal subset_closedAbsConvexHull isClosed_closedAbsConvexHull

theorem closedAbsConvexHull_min {s t : Set E} (hst : s ⊆ t) (h_conv : AbsConvex 𝕜 t)
    (h_closed : IsClosed t) : closedAbsConvexHull 𝕜 s ⊆ t :=
  (closedAbsConvexHull 𝕜).closure_min hst ⟨h_conv, h_closed⟩

theorem absConvexHull_subset_closedAbsConvexHull {s : Set E} :
    (absConvexHull 𝕜) s ⊆ (closedAbsConvexHull 𝕜) s :=
  absConvexHull_min subset_closedAbsConvexHull absConvex_convexClosedHull

@[simp]
theorem closedAbsConvexHull_closure_eq_closedAbsConvexHull {s : Set E} :
    closedAbsConvexHull 𝕜 (closure s) = closedAbsConvexHull 𝕜 s :=
  subset_antisymm (by simpa using ((closedAbsConvexHull 𝕜).monotone
      (closure_subset_closedAbsConvexHull (𝕜 := 𝕜) (E := E))))
    ((closedAbsConvexHull 𝕜).monotone subset_closure)

end AbsolutelyConvex

section NormedField

variable [NormedField 𝕜]
  [AddCommGroup E] [Module ℝ E] [Module 𝕜 E]  [TopologicalSpace E]
  [TopologicalAddGroup E] [ContinuousSMul ℝ E] [ContinuousSMul 𝕜 E]

theorem AbsConvex.closure {s : Set E} (hs : AbsConvex 𝕜 s) : AbsConvex 𝕜 (closure s) :=
  ⟨Balanced.closure hs.1, Convex.closure hs.2⟩

theorem closedAbsConvexHull_eq_closure_absConvexHull {s : Set E} :
    closedAbsConvexHull 𝕜 s = closure (absConvexHull 𝕜 s) := subset_antisymm
  (closedAbsConvexHull_min (subset_trans (subset_absConvexHull) subset_closure)
    (AbsConvex.closure absConvex_absConvexHull) isClosed_closure)
  (closure_minimal absConvexHull_subset_closedAbsConvexHull isClosed_closedAbsConvexHull)

end NormedField

section NontriviallyNormedField

variable (𝕜 E)
variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [Module ℝ E] [SMulCommClass ℝ 𝕜 E]
variable [TopologicalSpace E] [LocallyConvexSpace ℝ E] [ContinuousSMul 𝕜 E]

theorem nhds_hasBasis_absConvex :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ 𝓝 (0 : E) ∧ AbsConvex 𝕜 s) id := by
  refine
    (LocallyConvexSpace.convex_basis_zero ℝ E).to_hasBasis (fun s hs => ?_) fun s hs =>
      ⟨s, ⟨hs.1, hs.2.2⟩, rfl.subset⟩
  refine ⟨convexHull ℝ (balancedCore 𝕜 s), ?_, convexHull_min (balancedCore_subset s) hs.2⟩
  refine ⟨Filter.mem_of_superset (balancedCore_mem_nhds_zero hs.1) (subset_convexHull ℝ _), ?_⟩
  refine ⟨(balancedCore_balanced s).convexHull, ?_⟩
  exact convex_convexHull ℝ (balancedCore 𝕜 s)

variable [ContinuousSMul ℝ E] [TopologicalAddGroup E]

theorem nhds_hasBasis_absConvex_open :
    (𝓝 (0 : E)).HasBasis (fun s => (0 : E) ∈ s ∧ IsOpen s ∧ AbsConvex 𝕜 s) id := by
  refine (nhds_hasBasis_absConvex 𝕜 E).to_hasBasis ?_ ?_
  · rintro s ⟨hs_nhds, hs_balanced, hs_convex⟩
    refine ⟨interior s, ?_, interior_subset⟩
    exact
      ⟨mem_interior_iff_mem_nhds.mpr hs_nhds, isOpen_interior,
        hs_balanced.interior (mem_interior_iff_mem_nhds.mpr hs_nhds), hs_convex.interior⟩
  rintro s ⟨hs_zero, hs_open, hs_balanced, hs_convex⟩
  exact ⟨s, ⟨hs_open.mem_nhds hs_zero, hs_balanced, hs_convex⟩, rfl.subset⟩

end NontriviallyNormedField

section

variable (𝕜) [NontriviallyNormedField 𝕜]
variable [AddCommGroup E] [Module ℝ E] [Module 𝕜 E]

theorem absConvexHull_add_subset {s t : Set E} :
    absConvexHull 𝕜 (s + t) ⊆ absConvexHull 𝕜 s + absConvexHull 𝕜 t :=
  absConvexHull_min (add_subset_add subset_absConvexHull subset_absConvexHull)
    ⟨Balanced.add balanced_absConvexHull balanced_absConvexHull,
      Convex.add convex_absConvexHull convex_absConvexHull⟩

theorem absConvexHull_eq_convexHull_balancedHull [SMulCommClass ℝ 𝕜 E] {s : Set E} :
    absConvexHull 𝕜 s = convexHull ℝ (balancedHull 𝕜 s) := le_antisymm
  (absConvexHull_min
    ((subset_convexHull ℝ s).trans (convexHull_mono (subset_balancedHull 𝕜)))
      ⟨Balanced.convexHull (balancedHull.balanced s), convex_convexHull ..⟩)
  (convexHull_min (balanced_absConvexHull.balancedHull_subset_of_subset subset_absConvexHull)
      convex_absConvexHull)

/-- In general, equality doesn't hold here - e.g. consider `s := {(-1, 1), (1, 1)}` in `ℝ²`. -/
theorem balancedHull_convexHull_subseteq_absConvexHull {s : Set E} :
    balancedHull 𝕜 (convexHull ℝ s) ⊆ absConvexHull 𝕜 s :=
  balanced_absConvexHull.balancedHull_subset_of_subset
    (convexHull_min subset_absConvexHull convex_absConvexHull)

end

section

variable [AddCommGroup E] [Module ℝ E]

lemma balancedHull_subset_convexHull_union_neg {s : Set E} :
    balancedHull ℝ s ⊆ convexHull ℝ (s ∪ -s) := by
  intro a ha
  obtain ⟨r, hr, y, hy, rfl⟩ := mem_balancedHull_iff.1 ha
  apply segment_subset_convexHull (mem_union_left (-s) hy) (mem_union_right _ (neg_mem_neg.mpr hy))
  have : 0 ≤ 1 + r := neg_le_iff_add_nonneg'.mp (neg_le_of_abs_le hr)
  have : 0 ≤ 1 - r := sub_nonneg.2 (le_of_abs_le hr)
  refine ⟨(1 + r)/2, (1 - r)/2, by positivity, by positivity, by ring, ?_⟩
  rw [smul_neg, ← sub_eq_add_neg, ← sub_smul]
  apply congrFun (congrArg HSMul.hSMul _) y
  ring_nf

@[simp]
theorem convexHull_union_neg_eq_absConvexHull {s : Set E} :
    convexHull ℝ (s ∪ -s) = absConvexHull ℝ s := by
  rw [absConvexHull_eq_convexHull_balancedHull]
  exact le_antisymm (convexHull_mono (union_subset (subset_balancedHull ℝ)
    (fun _ _ => by rw [mem_balancedHull_iff]; use -1; aesop)))
    (by
      rw [← Convex.convexHull_eq (convex_convexHull ℝ (s ∪ -s))]
      exact convexHull_mono balancedHull_subset_convexHull_union_neg)

variable (E 𝕜) {s : Set E}
variable [NontriviallyNormedField 𝕜] [Module 𝕜 E] [SMulCommClass ℝ 𝕜 E]
variable [UniformSpace E] [UniformAddGroup E] [lcs : LocallyConvexSpace ℝ E] [ContinuousSMul ℝ E]

-- TVS II.25 Prop3
theorem totallyBounded_absConvexHull (hs : TotallyBounded s) :
    TotallyBounded (absConvexHull ℝ s) := by
  rw [← convexHull_union_neg_eq_absConvexHull]
  apply totallyBounded_convexHull
  rw [totallyBounded_union]
  exact ⟨hs, totallyBounded_neg hs⟩

end

section AbsolutelyConvexSets

variable [TopologicalSpace E] [AddCommMonoid E] [Zero E] [SeminormedRing 𝕜]
variable [SMul 𝕜 E] [SMul ℝ E]
variable (𝕜 E)

/-- The type of absolutely convex open sets. -/
def AbsConvexOpenSets :=
  { s : Set E // (0 : E) ∈ s ∧ IsOpen s ∧ AbsConvex 𝕜 s }

noncomputable instance AbsConvexOpenSets.instCoeTC : CoeTC (AbsConvexOpenSets 𝕜 E) (Set E) :=
  ⟨Subtype.val⟩

namespace AbsConvexOpenSets

variable {𝕜 E}

theorem coe_zero_mem (s : AbsConvexOpenSets 𝕜 E) : (0 : E) ∈ (s : Set E) :=
  s.2.1

theorem coe_isOpen (s : AbsConvexOpenSets 𝕜 E) : IsOpen (s : Set E) :=
  s.2.2.1

theorem coe_nhds (s : AbsConvexOpenSets 𝕜 E) : (s : Set E) ∈ 𝓝 (0 : E) :=
  s.coe_isOpen.mem_nhds s.coe_zero_mem

theorem coe_balanced (s : AbsConvexOpenSets 𝕜 E) : Balanced 𝕜 (s : Set E) :=
  s.2.2.2.1

theorem coe_convex (s : AbsConvexOpenSets 𝕜 E) : Convex ℝ (s : Set E) :=
  s.2.2.2.2

end AbsConvexOpenSets

instance AbsConvexOpenSets.instNonempty : Nonempty (AbsConvexOpenSets 𝕜 E) := by
  rw [← exists_true_iff_nonempty]
  dsimp only [AbsConvexOpenSets]
  rw [Subtype.exists]
  exact ⟨Set.univ, ⟨mem_univ 0, isOpen_univ, balanced_univ, convex_univ⟩, trivial⟩

end AbsolutelyConvexSets

variable [RCLike 𝕜]
variable [AddCommGroup E] [TopologicalSpace E]
variable [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
variable [ContinuousSMul ℝ E]
variable (𝕜 E)

/-- The family of seminorms defined by the gauges of absolute convex open sets. -/
noncomputable def gaugeSeminormFamily : SeminormFamily 𝕜 E (AbsConvexOpenSets 𝕜 E) := fun s =>
  gaugeSeminorm s.coe_balanced s.coe_convex (absorbent_nhds_zero s.coe_nhds)

variable {𝕜 E}

theorem gaugeSeminormFamily_ball (s : AbsConvexOpenSets 𝕜 E) :
    (gaugeSeminormFamily 𝕜 E s).ball 0 1 = (s : Set E) := by
  dsimp only [gaugeSeminormFamily]
  rw [Seminorm.ball_zero_eq]
  simp_rw [gaugeSeminorm_toFun]
  exact gauge_lt_one_eq_self_of_isOpen s.coe_convex s.coe_zero_mem s.coe_isOpen

variable [TopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [SMulCommClass ℝ 𝕜 E] [LocallyConvexSpace ℝ E]

/-- The topology of a locally convex space is induced by the gauge seminorm family. -/
theorem with_gaugeSeminormFamily : WithSeminorms (gaugeSeminormFamily 𝕜 E) := by
  refine SeminormFamily.withSeminorms_of_hasBasis _ ?_
  refine (nhds_hasBasis_absConvex_open 𝕜 E).to_hasBasis (fun s hs => ?_) fun s hs => ?_
  · refine ⟨s, ⟨?_, rfl.subset⟩⟩
    convert (gaugeSeminormFamily _ _).basisSets_singleton_mem ⟨s, hs⟩ one_pos
    rw [gaugeSeminormFamily_ball, Subtype.coe_mk]
  refine ⟨s, ⟨?_, rfl.subset⟩⟩
  rw [SeminormFamily.basisSets_iff] at hs
  rcases hs with ⟨t, r, hr, rfl⟩
  rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]
  -- We have to show that the intersection contains zero, is open, balanced, and convex
  refine
    ⟨mem_iInter₂.mpr fun _ _ => by simp [Seminorm.mem_ball_zero, hr],
      isOpen_biInter_finset fun S _ => ?_,
      balanced_iInter₂ fun _ _ => Seminorm.balanced_ball_zero _ _,
      convex_iInter₂ fun _ _ => Seminorm.convex_ball ..⟩
  -- The only nontrivial part is to show that the ball is open
  have hr' : r = ‖(r : 𝕜)‖ * 1 := by simp [abs_of_pos hr]
  have hr'' : (r : 𝕜) ≠ 0 := by simp [hr.ne']
  rw [hr', ← Seminorm.smul_ball_zero hr'', gaugeSeminormFamily_ball]
  exact S.coe_isOpen.smul₀ hr''
