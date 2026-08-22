/-
Copyright (c) 2026 Michał Pacholski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Pacholski
-/
module

public import Mathlib.Analysis.LocallyConvex.AbsConvex
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Topology.Algebra.FilterBasis


@[expose] public section

open scoped TensorProduct Topology Pointwise
open Function Filter Bornology NormedField

section Semiring

variable {R M N : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable (M N)

variable (R) in
/-- Type synonym for the projective tensor product of topological modules. -/
public def ProjectiveTensorProduct := M ⊗[R] N

@[inherit_doc] scoped[TensorProduct] notation:100 M:100 " ⊗[" R "]π " N:101 =>
  ProjectiveTensorProduct R M N

end Semiring

namespace TensorProduct

section CommSemiring

variable {R M N : Type*}
variable [CommSemiring R] [PartialOrder R] [TopologicalSpace R]
variable [AddCommGroup M] [Module R M] [TopologicalSpace M] [LocallyConvexSpace R M]
variable [AddCommGroup N] [Module R N] [TopologicalSpace N] [LocallyConvexSpace R N]

instance : AddCommGroup (M ⊗[R]π N) := addCommGroup
instance : Module R (M ⊗[R]π  N) := instModule

variable (R) in
def tensorProductTopologies := { t : TopologicalSpace (M ⊗[R] N) |
    letI := t
    IsTopologicalAddGroup (M ⊗[R] N) ∧
    LocallyConvexSpace R (M ⊗[R] N) ∧
    ContinuousSMul R (M ⊗[R] N) ∧
    -- Continuous (fun (p : M × N) ↦ TensorProduct.mk R M N p.1 p.2)
    Continuous (Function.uncurry (tmul R : M → N → M ⊗[R] N))
}

/-- The projective topology on `X ⊗[𝕜]π Y` is defined as the supremum of all topologies
making the space a locally convex topological module such that `tmul` is continuous. -/
instance instTopologicalSpaceProjectiveTensorProduct : TopologicalSpace (M ⊗[R]π N) :=
  sInf (tensorProductTopologies R)

instance : LocallyConvexSpace R (M ⊗[R]π N) := LocallyConvexSpace.sInf fun _ ⟨_, h, _⟩ ↦ h

example {t : TopologicalSpace (M ⊗[R] N)} (ht : t ∈ tensorProductTopologies R) :
  instTopologicalSpaceProjectiveTensorProduct ≤ t := sInf_le ht

example {t : TopologicalSpace (M ⊗[R] N)} (ht : t ∈ tensorProductTopologies R) :
    𝓝 (0 : (M ⊗[R]π N)) ≤ 𝓝 (0 : (M ⊗[R] N)) := nhds_mono (sInf_le ht)

end CommSemiring
section NontriviallyNormedField

variable {𝕜 E F : Type*}
variable [NontriviallyNormedField 𝕜]
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [PartialOrder 𝕜]

local notation:100 A:100 " ⊗ˢ[" 𝕜 "] " B:101 => Set.image2 (tmul 𝕜) A B

omit [TopologicalSpace E] in
/--
this can be moved out to existing file-/
lemma absConvexHull_inter_subset {s t : Set E} :
    absConvexHull 𝕜 (s ∩ t) ⊆ absConvexHull 𝕜 s ∩ absConvexHull 𝕜 t :=
  Set.subset_inter (absConvexHull_mono Set.inter_subset_left)
                   (absConvexHull_mono Set.inter_subset_right)

variable [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]

/-- Every element in a topological vector space over a nontrivially normed field
can be represented as a scaled version of an element in any given neighborhood of zero. -/
lemma exists_smul_of_mem_nhds_zero [ContinuousSMul 𝕜 E]
    {V : Set E} (hV : V ∈ 𝓝 0) (x : E) :
    ∃ (r : 𝕜) (_ : r ≠ 0), ∃ x' ∈ V, x = r • x' := by
  have h_abs := absorbent_nhds_zero (𝕜 := 𝕜) hV x
  have h_abs' : ∀ᶠ (r : 𝕜) in cobounded 𝕜, ∃ x' ∈ V, x = r • x' := by
    filter_upwards [h_abs] with r hr
    have hx : x ∈ r • V := Set.singleton_subset_iff.mp hr
    rcases Set.mem_smul_set.mp hx with ⟨x', hx', rfl⟩
    exact ⟨x', hx', rfl⟩
  have h_abs_ne := h_abs'.and (eventually_ne_cobounded 0)
  rcases h_abs_ne.exists with ⟨r, ⟨x', hx', rfl⟩, hr_ne⟩
  exact ⟨r, hr_ne, x', hx', rfl⟩

abbrev absConvexHulls (𝔘 : Set (Set E)) (𝔙 : Set (Set F)) :=
  { s | ∃ U ∈ 𝔘, ∃ B ∈ 𝔙, s = absConvexHull 𝕜 (U ⊗ˢ[𝕜] B) }

variable {𝔘 : Set (Set E)} {𝔙 : Set (Set F)}
  (h𝔘 : (𝓝 (0 : E)).HasBasis 𝔘 id) (h𝔙 : (𝓝 (0 : F)).HasBasis 𝔙 id)

variable [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F]

def moduleFilterBasis : ModuleFilterBasis 𝕜 (E ⊗[𝕜] F) where
  sets := absConvexHulls 𝔘 𝔙
  nonempty := by
    rcases h𝔘.ex_mem with ⟨U, hU⟩
    rcases h𝔙.ex_mem with ⟨V, hV⟩
    exact ⟨absConvexHull 𝕜 (U ⊗ˢ[𝕜] V), U, hU, V, hV, rfl⟩
  inter_sets := by
    rintro x y ⟨U₁, hU₁, V₁, hV₁, rfl⟩ ⟨U₂, hU₂, V₂, hV₂, rfl⟩
    obtain ⟨U₃, hU₃, hU₃_subset⟩ := h𝔘.mem_iff.mp (inter_mem
      (h𝔘.mem_iff.mpr ⟨U₁, hU₁, subset_rfl⟩)
      (h𝔘.mem_iff.mpr ⟨U₂, hU₂, subset_rfl⟩))
    obtain ⟨V₃, hV₃, hV₃_subset⟩ := h𝔙.mem_iff.mp (inter_mem
      (h𝔙.mem_iff.mpr ⟨V₁, hV₁, subset_rfl⟩)
      (h𝔙.mem_iff.mpr ⟨V₂, hV₂, subset_rfl⟩))
    use absConvexHull 𝕜 (U₃ ⊗ˢ[𝕜] V₃)
    constructor
    · exact ⟨U₃, hU₃, V₃, hV₃, rfl⟩
    · apply (AbsConvex.absConvexHull_subset_iff
        (AbsConvex.inter absConvex_absConvexHull absConvex_absConvexHull)).mpr
      calc
        U₃ ⊗ˢ[𝕜] V₃ ⊆ (U₁ ⊗ˢ[𝕜] V₁) ∩ (U₂ ⊗ˢ[𝕜] V₂) := by
          rintro x ⟨u, hu, v, hv, rfl⟩
          exact ⟨⟨u, Set.mem_of_mem_inter_left (Set.mem_of_subset_of_mem hU₃_subset hu),
            v, Set.mem_of_mem_inter_left (Set.mem_of_subset_of_mem hV₃_subset hv), rfl⟩,
            ⟨u, Set.mem_of_mem_inter_right (Set.mem_of_subset_of_mem hU₃_subset hu),
            v, Set.mem_of_mem_inter_right (Set.mem_of_subset_of_mem hV₃_subset hv), rfl⟩⟩
        _ ⊆ absConvexHull 𝕜 ((U₁ ⊗ˢ[𝕜] V₁) ∩ (U₂ ⊗ˢ[𝕜] V₂)) := subset_absConvexHull
        _ ⊆ (absConvexHull 𝕜) (U₁ ⊗ˢ[𝕜] V₁) ∩ (absConvexHull 𝕜) (U₂ ⊗ˢ[𝕜] V₂) :=
          absConvexHull_inter_subset
  zero' := by
    rintro s ⟨U, hU, V, hV, rfl⟩
    have hU_zero : (0 : E) ∈ U := mem_of_mem_nhds (h𝔘.mem_of_mem hU)
    have hV_zero : (0 : F) ∈ V := mem_of_mem_nhds (h𝔙.mem_of_mem hV)
    have h_zero_tmul : (0 : E) ⊗ₜ[𝕜] (0 : F) ∈ U ⊗ˢ[𝕜] V := Set.mem_image2_of_mem hU_zero hV_zero
    simpa [zero_tmul] using subset_absConvexHull h_zero_tmul
  add' := by

    rintro s ⟨U, hU, V, hV, rfl⟩
    -- -- 1. Find a scalar c with norm < 1/2
    obtain ⟨c, hc, hc_lt⟩ : ∃ (c : 𝕜), 0 < ‖c‖ ∧ ‖c‖ < 1/2 := exists_norm_lt 𝕜 (by norm_num)
    have hc_ne : c ≠ 0 := norm_pos_iff.mp hc

    -- -- 2. Construct the neighborhood preimage for U under c⁻¹ • E
    have h_inv_cont : ContinuousAt (fun x : E ↦ c⁻¹ • x) 0 :=
      (continuous_const_smul c⁻¹).continuousAt
    have hU_nhds : U ∈ 𝓝 (0 : E) := h𝔘.mem_of_mem hU
    have h_preimage : (fun x : E ↦ c⁻¹ • x) ⁻¹' U ∈ 𝓝 (0 : E) := h_inv_cont (by simpa using hU_nhds)
    rcases h𝔘.mem_iff.mp h_preimage with ⟨U', hU', hU'_sub⟩
    have hU'_sub' : ∀ x ∈ U', c⁻¹ • x ∈ U := fun x hx ↦ hU'_sub hx

    -- 3. Show that U' ⊗ˢ[𝕜] B is contained in c • (U ⊗ˢ[𝕜] B)
    have h_sub : U' ⊗ˢ[𝕜] V ⊆ c • (U ⊗ˢ[𝕜] V) := by
      rintro z ⟨x, hx, y, hy, rfl⟩
      use (c⁻¹ • x) ⊗ₜ[𝕜] y
      refine ⟨⟨c⁻¹ • x, hU'_sub' x hx, y, hy, rfl⟩, ?_⟩
      simp only
      rw [smul_tmul, ← tmul_smul, smul_smul, mul_inv_cancel₀ hc_ne, one_smul]

    -- -- 5. Obtain the inclusion of the absolutely convex hulls
    have h_t_sub : absConvexHull 𝕜 (U' ⊗ˢ[𝕜] V) ⊆ c • absConvexHull 𝕜 (U ⊗ˢ[𝕜] V) :=
      absConvexHull_min (h_sub.trans (Set.image_mono subset_absConvexHull))
        ⟨balanced_absConvexHull.smul c, convex_absConvexHull.smul c⟩

    -- 7. Show that c • S + c • S ⊆ S
    have h_add_sub :
        c • absConvexHull 𝕜 (U ⊗ˢ[𝕜] V) + c • absConvexHull 𝕜 (U ⊗ˢ[𝕜] V)
        ⊆ absConvexHull 𝕜 (U ⊗ˢ[𝕜] V) := by
      rintro z ⟨x1, ⟨y1, hy1, rfl⟩, x2, ⟨y2, hy2, rfl⟩, rfl⟩
      have h1 : (1/2 : 𝕜) • y1 + (1/2 : 𝕜) • y2 ∈ absConvexHull 𝕜 (U ⊗ˢ[𝕜] V) := sorry
        -- convex_absConvexHull hy1 hy2 (by norm_num) (by norm_num) (by norm_num)
      have h2 : ‖(2 : 𝕜) * c‖ ≤ 1 := calc
        ‖(2 : 𝕜) * c‖ = ‖(2 : 𝕜)‖ * ‖c‖ := norm_mul (2 : 𝕜) c
        _ = ‖(1 + 1 : 𝕜)‖ * ‖c‖ := sorry -- rfl
        _ ≤ (‖(1 : 𝕜)‖ + ‖(1 : 𝕜)‖) * ‖c‖ := sorry -- mul_le_mul_of_nonneg_right (norm_add _ _) (norm_nonneg _)
        _ = 2 * ‖c‖ := by rw [norm_one]; ring
        _ ≤ 1 := by linarith [hc_lt]
      have h3 : (2 * c) • ((1/2 : 𝕜) • y1 + (1/2 : 𝕜) • y2) ∈ absConvexHull 𝕜 (U ⊗ˢ[𝕜] V) :=
        balanced_absConvexHull (2 * c) h2 ⟨(1/2 : 𝕜) • y1 + (1/2 : 𝕜) • y2, h1, rfl⟩
      have h4 : (2 * c) • ((1/2 : 𝕜) • y1 + (1/2 : 𝕜) • y2) = c • y1 + c • y2 := by
        simp only [smul_add, smul_smul]
        have : (2 : 𝕜) * c * 1/2 = c := by sorry -- ring
        -- rw [this]
        sorry
      rwa [h4] at h3

    -- 8. Wrap up and present the witness
    exact ⟨absConvexHull 𝕜 (U' ⊗ˢ[𝕜] V), ⟨U', hU', V, hV, rfl⟩,
      (Set.add_subset_add h_t_sub h_t_sub).trans h_add_sub⟩
  neg' := by
    intro W hW
    use W
    constructor
    · exact hW
    · obtain ⟨U, _, V, _, rfl⟩  := hW
      have h_balanced : Balanced 𝕜 (absConvexHull 𝕜 (U ⊗ˢ[𝕜] V)) := balanced_absConvexHull
      have h_subset := h_balanced (-1 : 𝕜) (by norm_num)
      rintro x hx
      simpa using h_subset ⟨x, hx, rfl⟩
  conj' := by intro _ U hU; exact ⟨U, hU, by simp⟩
  smul' := by
    intro W hW
    use Metric.closedBall (0 : 𝕜) 1
    constructor
    · exact Metric.closedBall_mem_nhds 0 zero_lt_one
    · use W
      constructor
      · exact hW
      · rintro _ ⟨c, hc, x, hx, rfl⟩
        obtain ⟨U, hU, V, hV, rfl⟩ := hW
        have h_balanced : Balanced 𝕜 (absConvexHull 𝕜 (U ⊗ˢ[𝕜] V)) := balanced_absConvexHull
        have hc_norm : ‖c‖ ≤ 1 := by simpa using hc
        apply h_balanced c hc_norm ⟨x, hx, rfl⟩
  smul_left' := by
    intro c W hW
    obtain ⟨U, hU, V, hV, rfl⟩ := hW
    have hU_nhds : U ∈ 𝓝 0 := h𝔘.mem_iff.mpr ⟨U, hU, subset_rfl⟩
    have hcU_nhds : (fun x ↦ c • x) ⁻¹' U ∈ 𝓝 0 := by
      have h_cont := (continuous_const_smul c).tendsto (0 : E)
      rw [smul_zero] at h_cont
      exact h_cont hU_nhds
    obtain ⟨U', hU', hU_sub⟩ := h𝔘.mem_iff.mp hcU_nhds
    use absConvexHull 𝕜 (U' ⊗ˢ[𝕜] V)
    constructor
    · exact ⟨U', hU', V, hV, rfl⟩
    · have h_abs : AbsConvex 𝕜 ((fun x ↦ c • x) ⁻¹' (absConvexHull 𝕜 (U ⊗ˢ[𝕜] V))) := by
        constructor
        · intro a ha x hx
          rw [Set.mem_smul_set] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          rw [Set.mem_preimage] at hy ⊢
          rw [smul_comm c a y]
          apply Set.smul_mem_smul_set (a := a) at hy
          exact balanced_absConvexHull a ha hy
        · rintro x hx y hy a b ha hb hab
          rw [Set.mem_preimage] at hx hy ⊢
          rw [smul_add, smul_comm c a x, smul_comm c b y]
          exact convex_absConvexHull hx hy ha hb hab
      apply absConvexHull_min _ h_abs
      rintro _ ⟨u, hu, v, hv, rfl⟩
      apply subset_absConvexHull
      exact ⟨c • u, hU_sub hu, v, hv, rfl⟩
  smul_right' := by
    intro c W hW
    obtain ⟨U, hU, V, hV, rfl⟩ := hW
    induction c using TensorProduct.induction_on with
    | zero =>
      filter_upwards with c
      rw [smul_zero]
      apply subset_absConvexHull
      rw [← TensorProduct.tmul_zero F 0]
      have hU_zero : (0 : E) ∈ U := mem_of_mem_nhds (h𝔘.mem_iff.mpr ⟨U, hU, subset_rfl⟩)
      have hV_zero : (0 : F) ∈ V := mem_of_mem_nhds (h𝔙.mem_iff.mpr ⟨V, hV, subset_rfl⟩)
      exact ⟨0, hU_zero, 0, hV_zero, rfl⟩
    | tmul u v =>
      have hU_nhds : U ∈ 𝓝 0 := h𝔘.mem_iff.mpr ⟨U, hU, subset_rfl⟩
      have hV_nhds : V ∈ 𝓝 0 := h𝔙.mem_iff.mpr ⟨V, hV, subset_rfl⟩

    --   -- We need a non-zero scalar c₂ to scale v into V.
    --   -- NontriviallyNormedField guarantees 𝓝[≠] 0 is non-trivial.
    --  haveI : NeBot (𝓝[≠] (0 : 𝕜)) := inferInstance
      have hv : Tendsto (fun x : 𝕜 ↦ x • v) (𝓝 0) (𝓝 0) :=
        (continuous_id.smul continuous_const).tendsto' _ _ (zero_smul _ _)
      have h_ev_v : ∀ᶠ x in 𝓝[≠] (0 : 𝕜), x ≠ 0 ∧ x • v ∈ V :=
        (eventually_nhdsWithin_of_forall fun x a ↦ a).and
          (eventually_nhdsWithin_of_eventually_nhds (hv hV_nhds))

      obtain ⟨c₂, hc₂_ne, hc₂_V⟩ := h_ev_v.exists

    --   -- With c₂ fixed, scale u using the remaining factor (x * c₂⁻¹)
      have hu : Tendsto (fun x : 𝕜 ↦ (x * c₂⁻¹) • u) (𝓝 0) (𝓝 0) := by
        have ht1 : Tendsto (fun x : 𝕜 ↦ x * c₂⁻¹) (𝓝 0) (𝓝 0) :=
          (continuous_mul_const c₂⁻¹).tendsto' _ _ (zero_mul _)
        have ht2 : Tendsto (fun y : 𝕜 ↦ y • u) (𝓝 0) (𝓝 0) :=
          (continuous_id.smul continuous_const).tendsto' _ _ (zero_smul _ _)
        exact ht2.comp ht1

      have h_ev_u : ∀ᶠ x in 𝓝 0, (x * c₂⁻¹) • u ∈ U := hu hU_nhds

      filter_upwards [h_ev_u] with x hx
      have : x • (u ⊗ₜ[𝕜] v) = ((x * c₂⁻¹) • u) ⊗ₜ[𝕜] (c₂ • v) := by
        rw [smul_tmul, tmul_smul, tmul_smul, smul_smul]
        have h_mul : x * c₂⁻¹ * c₂ = x := by
          rw [mul_assoc, inv_mul_cancel₀ hc₂_ne, mul_one]
        rw [h_mul]
      rw [this]
      apply subset_absConvexHull
      exact ⟨_, hx, _, hc₂_V, rfl⟩

    | add x y hx hy =>
      haveI : NeBot (𝓝[≠] (0 : 𝕜)) := inferInstance

      -- Extract non-zero scalars a and b that pull x and y into the absolute convex hull
      have hx_ev : ∀ᶠ c in 𝓝[≠] (0 : 𝕜), c ≠ 0 ∧ c • x ∈ absConvexHull 𝕜 (U ⊗ˢ[𝕜] V) :=
        (eventually_nhdsWithin_of_forall fun x a ↦ a).and
          (eventually_nhdsWithin_of_eventually_nhds hx)
      obtain ⟨a, ha_ne, ha_W⟩ := hx_ev.exists

      have hy_ev : ∀ᶠ c in 𝓝[≠] (0 : 𝕜), c ≠ 0 ∧ c • y ∈ absConvexHull 𝕜 (U ⊗ˢ[𝕜] V) :=
        (eventually_nhdsWithin_of_forall fun x a ↦ a).and
          (eventually_nhdsWithin_of_eventually_nhds hy)
      obtain ⟨b, hb_ne, hb_W⟩ := hy_ev.exists

      -- Prove that ‖c * a⁻¹‖ + ‖c * b⁻¹‖ tends to 0, meaning it will eventually be ≤ 1
      have hc : Tendsto (fun c : 𝕜 ↦ ‖c * a⁻¹‖ + ‖c * b⁻¹‖) (𝓝 0) (𝓝 0) := by
        have ha_lim : Tendsto (fun c : 𝕜 ↦ ‖c * a⁻¹‖) (𝓝 0) (𝓝 0) :=
          (continuous_norm.comp (continuous_id.mul continuous_const)).tendsto' 0 0 (by simp)
        have hb_lim : Tendsto (fun c : 𝕜 ↦ ‖c * b⁻¹‖) (𝓝 0) (𝓝 0) :=
          (continuous_norm.comp (continuous_id.mul continuous_const)).tendsto' 0 0 (by simp)
        -- exact (ha_lim.add hb_lim).tendsto' 0 0 (add_zero _)
        sorry

      have h_le : ∀ᶠ c in 𝓝 0, ‖c * a⁻¹‖ + ‖c * b⁻¹‖ ≤ 1 :=
        hc (Iic_mem_nhds zero_lt_one)

      filter_upwards [h_le] with c hc_le
      have h_eq : c • (x + y) = (c * a⁻¹) • (a • x) + (c * b⁻¹) • (b • y) := by
        rw [smul_add, ← mul_smul, ← mul_smul]
        have ha_mul : c * a⁻¹ * a = c := by rw [mul_assoc, inv_mul_cancel₀ ha_ne, mul_one]
        have hb_mul : c * b⁻¹ * b = c := by rw [mul_assoc, inv_mul_cancel₀ hb_ne, mul_one]
        rw [ha_mul, hb_mul]
      rw [h_eq]

      -- Since the coefficients satisfy the AbsConvex bound (≤ 1), their combination stays inside the hull.
      -- Note: depending on your specific AbsConvex API import, this property might be named
      -- `absConvex_absConvexHull.smul_add_smul_le` or accessed via the underlying structure properties.
      -- exact (absConvex_absConvexHull 𝕜 (U ⊗ˢ[𝕜] V)).smul_add_smul_le ha_W hb_W hc_le
      sorry

lemma locallyConvexSpace_of_basis :
    @LocallyConvexSpace 𝕜 (E ⊗[𝕜] F) _ _ _ _ (moduleFilterBasis h𝔘 h𝔙).topology := by
  letI topology := (moduleFilterBasis h𝔘 h𝔙).topology (R:=𝕜)
  apply LocallyConvexSpace.ofBasisZero 𝕜 (E ⊗[𝕜] F) id _
    (moduleFilterBasis h𝔘 h𝔙).nhds_zero_hasBasis
  rintro s ⟨U, hU, B, hB, rfl⟩
  exact convex_absConvexHull

lemma tendsto_tmul_nhds_zero_of_basis :
    Tendsto (fun p : E × F ↦ p.1 ⊗ₜ[𝕜] p.2) (𝓝 0 ×ˢ 𝓝 0) (moduleFilterBasis h𝔘 h𝔙).filter := by
  rw [(moduleFilterBasis h𝔘 h𝔙).toFilterBasis.hasBasis.tendsto_right_iff]
  rintro s ⟨U, hU, B, hB, rfl⟩
  have hb_nhds : U ∈ 𝓝 (0 : E) := h𝔘.mem_of_mem hU
  have hb'_nhds : B ∈ 𝓝 (0 : F) := h𝔙.mem_of_mem hB
  have h_prod : U ×ˢ B ∈ 𝓝 (0 : E) ×ˢ 𝓝 (0 : F) := prod_mem_prod hb_nhds hb'_nhds
  filter_upwards [h_prod]
  rintro ⟨x, y⟩ ⟨hx : x ∈ U, hy : y ∈ B⟩
  exact subset_absConvexHull (Set.mem_image2_of_mem hx hy)

variable [ContinuousSMul 𝕜 F]

lemma continuousAt_tmul_right_of_basis (y : F) :
    @ContinuousAt E (E ⊗[𝕜] F) _ (moduleFilterBasis h𝔘 h𝔙).topology (fun x ↦ x ⊗ₜ[𝕜] y) 0 := by
  letI topology := (moduleFilterBasis h𝔘 h𝔙).topology (R:=𝕜)
  rw [ContinuousAt, zero_tmul]
  rw [(moduleFilterBasis h𝔘 h𝔙).toAddGroupFilterBasis.nhds_zero_hasBasis.tendsto_right_iff]
  rintro s ⟨U, hU, B, hB, rfl⟩
  have hb'_nhds : B ∈ 𝓝 (0 : F) := h𝔙.mem_of_mem hB
  rcases exists_smul_of_mem_nhds_zero (𝕜 := 𝕜) hb'_nhds y with ⟨r, hr_ne, y', hy', rfl⟩
  have hb_nhds : U ∈ 𝓝 (0 : E) := h𝔘.mem_of_mem hU
  have h_smul : ∀ᶠ x : E in 𝓝 0, r • x ∈ U :=
    (continuous_const_smul r).continuousAt (by simpa using hb_nhds)
  filter_upwards [h_smul] with x hx
  rw [← TensorProduct.smul_tmul]
  exact subset_absConvexHull (Set.mem_image2_of_mem hx hy')

variable [ContinuousSMul 𝕜 E]

lemma continuousAt_mk_apply_of_basis (x : E) :
    @ContinuousAt F (E ⊗[𝕜] F) _ (moduleFilterBasis h𝔘 h𝔙).topology ((mk 𝕜 E F) x) 0 := by
  letI topology := (moduleFilterBasis h𝔘 h𝔙).topology (R:=𝕜)
  rw [ContinuousAt, map_zero]
  rw [(moduleFilterBasis h𝔘 h𝔙).nhds_zero_hasBasis.tendsto_right_iff]
  rintro s ⟨U, hU, B, hB, rfl⟩
  have hb_nhds : U ∈ 𝓝 (0 : E) := h𝔘.mem_of_mem hU
  rcases exists_smul_of_mem_nhds_zero (𝕜 := 𝕜) hb_nhds x with ⟨r, hr_ne, x', hx', rfl⟩
  have hb'_nhds : B ∈ 𝓝 (0 : F) := h𝔙.mem_of_mem hB
  have h_smul : ∀ᶠ y : F in 𝓝 0, r • y ∈ B :=
    (continuous_const_smul r).continuousAt (by simpa using hb'_nhds)
  filter_upwards [h_smul] with y hy
  rw [mk_apply, smul_tmul]
  exact subset_absConvexHull (Set.mem_image2_of_mem hx' hy)

variable [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]

theorem moduleFilterBasis_topology_mem_tensorProductTopologies :
    (moduleFilterBasis h𝔘 h𝔙).topology ∈ tensorProductTopologies 𝕜 := by
  letI topology := (moduleFilterBasis h𝔘 h𝔙).topology (R:=𝕜)
  unfold tensorProductTopologies
  simp only [Set.mem_ofPred_eq]
  refine ⟨(moduleFilterBasis h𝔘 h𝔙).isTopologicalAddGroup, locallyConvexSpace_of_basis h𝔘 h𝔙,
    (moduleFilterBasis h𝔘 h𝔙).continuousSMul, ?_⟩
  apply continuous_of_continuousAt_zero₂
    (LinearMap.toAddMonoidHom'.comp (TensorProduct.mk 𝕜 E F).toAddMonoidHom)
  · rw [ContinuousAt, Prod.mk_zero_zero]
    simp only [AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, comp_apply,
      LinearMap.toAddMonoidHom'_apply, mk_apply, Prod.fst_zero, map_zero, Prod.snd_zero]
    rw [nhds_prod_eq, (moduleFilterBasis h𝔘 h𝔙).toAddGroupFilterBasis.nhds_zero_eq]
    exact tendsto_tmul_nhds_zero_of_basis (𝕜 := 𝕜) h𝔘 h𝔙
  · simp only [AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, comp_apply,
      LinearMap.toAddMonoidHom'_apply]
    exact continuousAt_mk_apply_of_basis h𝔘 h𝔙
  · simp only [AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, comp_apply,
      LinearMap.toAddMonoidHom'_apply, mk_apply]
    exact continuousAt_tmul_right_of_basis h𝔘 h𝔙

/--
This lemma can probably be moved to another file
-/
lemma le_of_nhds_zero_le_nhds_zero {E : Type*} [AddGroup E]
    {t₁ t₂ : TopologicalSpace E}
    [h₁ : @IsTopologicalAddGroup E t₁ _] [h₂ : @IsTopologicalAddGroup E t₂ _]
    (h : @nhds E t₁ 0 ≤ @nhds E t₂ 0) : t₁ ≤ t₂ := by
  rw [← @continuous_id_iff_le E t₁ t₂]
  exact @continuous_of_continuousAt_zero E t₁ _ h₁ E _ _ t₂ _ _ _ (AddMonoidHom.id E) h


theorem topology_eq_projective :
    (moduleFilterBasis h𝔘 h𝔙).topology = (instTopologicalSpaceProjectiveTensorProduct
      (R:=𝕜) (M:=E) (N:=F)) := by
  apply le_antisymm
  · apply le_sInf
    intro t ⟨ht_isTopologicalAddGroup, ht_locallyConvexSpace, ht_continuousSMul , ht_cont_tmul⟩
    letI := t
    let t_hasBasis_absConvex := nhds_hasBasis_absConvex 𝕜 (E ⊗[𝕜] F)
    apply le_of_nhds_zero_le_nhds_zero
    rw [(moduleFilterBasis h𝔘 h𝔙).nhds_zero_hasBasis.le_basis_iff t_hasBasis_absConvex]
    intro W ⟨hW_mem_nhds_zero, hW_absConvex⟩
    let W' := (Function.uncurry (tmul 𝕜)) ⁻¹' W
    have hW_mem_nhds_zero : W' ∈ (𝓝 (0,0)) := by
      apply ContinuousAt.preimage_mem_nhds (Continuous.continuousAt ht_cont_tmul)
      simp only [uncurry_apply_pair, tmul_zero]
      exact hW_mem_nhds_zero
    rw [nhds_prod_eq, (h𝔘.prod h𝔙).mem_iff] at hW_mem_nhds_zero
    obtain ⟨⟨U, V⟩, ⟨⟨hU, hV⟩, hW'⟩⟩ := hW_mem_nhds_zero
    simp only [id_eq] at hU hV hW' ⊢
    have h_tmul_subset_W : U ⊗ˢ[𝕜] V ⊆ W := by
      rw [Set.prod_subset_iff] at hW'
      intro z hz
      rw [Set.mem_image2] at hz
      obtain ⟨x, hx, y, hy, rfl⟩  := hz
      specialize hW' x hx y hy
      apply Set.mem_image_of_mem (Function.uncurry (tmul 𝕜)) at hW'
      dsimp [W'] at hW' W
      apply Set.mem_of_subset_of_mem (Set.image_preimage_subset _ _) at hW'
      exact hW'
    have h_mem_moduleFilterBasis : absConvexHull 𝕜 (U ⊗ˢ[𝕜] V) ∈ (moduleFilterBasis h𝔘 h𝔙) := by
      change _ ∈ (absConvexHulls 𝔘 𝔙)
      rw [Set.mem_ofPred_eq]
      exact ⟨U, hU, V, hV, rfl⟩
    have h_subset_W : absConvexHull 𝕜 (U ⊗ˢ[𝕜] V) ⊆ W := by
      exact (AbsConvex.absConvexHull_subset_iff hW_absConvex).mpr h_tmul_subset_W
    use absConvexHull 𝕜 (U ⊗ˢ[𝕜] V)
    exact ⟨h_mem_moduleFilterBasis, h_subset_W⟩
  · apply sInf_le
    exact moduleFilterBasis_topology_mem_tensorProductTopologies h𝔘 h𝔙

end NontriviallyNormedField

end TensorProduct
