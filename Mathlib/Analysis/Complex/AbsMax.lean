/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.NormedSpace.Completion
import Mathlib.Analysis.NormedSpace.Extr
import Mathlib.Topology.Algebra.Order.ExtrClosure

#align_import analysis.complex.abs_max from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Maximum modulus principle

In this file we prove several versions of the maximum modulus principle. There are several
statements that can be called "the maximum modulus principle" for maps between normed complex
spaces. They differ by assumptions on the domain (any space, a nontrivial space, a finite
dimensional space), assumptions on the codomain (any space, a strictly convex space), and by
conclusion (either equality of norms or of the values of the function).

## Main results

### Theorems for any codomain

Consider a function `f : E → F` that is complex differentiable on a set `s`, is continuous on its
closure, and `‖f x‖` has a maximum on `s` at `c`. We prove the following theorems.

- `Complex.norm_eqOn_closedBall_of_isMaxOn`: if `s = Metric.ball c r`, then `‖f x‖ = ‖f c‖` for
  any `x` from the corresponding closed ball;

- `Complex.norm_eq_norm_of_isMaxOn_of_ball_subset`: if `Metric.ball c (dist w c) ⊆ s`, then
  `‖f w‖ = ‖f c‖`;

- `Complex.norm_eqOn_of_isPreconnected_of_isMaxOn`: if `U` is an open (pre)connected set, `f` is
  complex differentiable on `U`, and `‖f x‖` has a maximum on `U` at `c ∈ U`, then `‖f x‖ = ‖f c‖`
  for all `x ∈ U`;

- `Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn`: if `s` is open and (pre)connected
  and `c ∈ s`, then `‖f x‖ = ‖f c‖` for all `x ∈ closure s`;

- `Complex.norm_eventually_eq_of_isLocalMax`: if `f` is complex differentiable in a neighborhood
  of `c` and `‖f x‖` has a local maximum at `c`, then `‖f x‖` is locally a constant in a
  neighborhood of `c`.

### Theorems for a strictly convex codomain

If the codomain `F` is a strictly convex space, then in the lemmas from the previous section we can
prove `f w = f c` instead of `‖f w‖ = ‖f c‖`, see
`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`,
`Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm`,
`Complex.eq_of_isMaxOn_of_ball_subset`, `Complex.eqOn_closedBall_of_isMaxOn_norm`, and
`Complex.eventually_eq_of_isLocalMax_norm`.

### Values on the frontier

Finally, we prove some corollaries that relate the (norm of the) values of a function on a set to
its values on the frontier of the set. All these lemmas assume that `E` is a nontrivial space.  In
this section `f g : E → F` are functions that are complex differentiable on a bounded set `s` and
are continuous on its closure. We prove the following theorems.

- `Complex.exists_mem_frontier_isMaxOn_norm`: If `E` is a finite dimensional space and `s` is a
  nonempty bounded set, then there exists a point `z ∈ frontier s` such that `(‖f ·‖)` takes it
  maximum value on `closure s` at `z`.

- `Complex.norm_le_of_forall_mem_frontier_norm_le`: if `‖f z‖ ≤ C` for all `z ∈ frontier s`, then
  `‖f z‖ ≤ C` for all `z ∈ s`; note that this theorem does not require `E` to be a finite
  dimensional space.

- `Complex.eqOn_closure_of_eqOn_frontier`: if `f x = g x` on the frontier of `s`, then `f x = g x`
  on `closure s`;

- `Complex.eqOn_of_eqOn_frontier`: if `f x = g x` on the frontier of `s`, then `f x = g x`
  on `s`.

## Tags

maximum modulus principle, complex analysis
-/


open TopologicalSpace Metric Set Filter Asymptotics Function MeasureTheory AffineMap

open scoped Topology Filter NNReal Real

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : Type v} [NormedAddCommGroup F]
  [NormedSpace ℂ F]

local postfix:100 "̂" => UniformSpace.Completion

namespace Complex

/-!
### Auxiliary lemmas

We split the proof into a series of lemmas. First we prove the principle for a function `f : ℂ → F`
with an additional assumption that `F` is a complete space, then drop unneeded assumptions one by
one.

The lemmas with names `*_auxₙ` are considered to be private and should not be used outside of this
file.
-/

theorem norm_max_aux₁ [CompleteSpace F] {f : ℂ → F} {z w : ℂ}
    (hd : DiffContOnCl ℂ f (ball z (dist w z)))
    (hz : IsMaxOn (norm ∘ f) (closedBall z (dist w z)) z) : ‖f w‖ = ‖f z‖ := by
  -- Consider a circle of radius `r = dist w z`.
  set r : ℝ := dist w z
  -- ⊢ ‖f w‖ = ‖f z‖
  have hw : w ∈ closedBall z r := mem_closedBall.2 le_rfl
  -- ⊢ ‖f w‖ = ‖f z‖
  -- Assume the converse. Since `‖f w‖ ≤ ‖f z‖`, we have `‖f w‖ < ‖f z‖`.
  refine' (isMaxOn_iff.1 hz _ hw).antisymm (not_lt.1 _)
  -- ⊢ ¬(norm ∘ f) w < (norm ∘ f) z
  rintro hw_lt : ‖f w‖ < ‖f z‖
  -- ⊢ False
  have hr : 0 < r := dist_pos.2 (ne_of_apply_ne (norm ∘ f) hw_lt.ne)
  -- ⊢ False
  -- Due to Cauchy integral formula, it suffices to prove the following inequality.
  suffices ‖∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ‖ < 2 * π * ‖f z‖ by
    refine' this.ne _
    have A : (∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ) = (2 * π * I : ℂ) • f z :=
      hd.circleIntegral_sub_inv_smul (mem_ball_self hr)
    simp [A, norm_smul, Real.pi_pos.le]
  suffices ‖∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ‖ < 2 * π * r * (‖f z‖ / r) by
    rwa [mul_assoc, mul_div_cancel' _ hr.ne'] at this
  /- This inequality is true because `‖(ζ - z)⁻¹ • f ζ‖ ≤ ‖f z‖ / r` for all `ζ` on the circle and
    this inequality is strict at `ζ = w`. -/
  have hsub : sphere z r ⊆ closedBall z r := sphere_subset_closedBall
  -- ⊢ ‖∮ (ζ : ℂ) in C(z, r), (ζ - z)⁻¹ • f ζ‖ < 2 * π * r * (‖f z‖ / r)
  refine' circleIntegral.norm_integral_lt_of_norm_le_const_of_lt hr _ _ ⟨w, rfl, _⟩
  show ContinuousOn (fun ζ : ℂ => (ζ - z)⁻¹ • f ζ) (sphere z r)
  · refine ((continuousOn_id.sub continuousOn_const).inv₀ ?_).smul (hd.continuousOn_ball.mono hsub)
    -- ⊢ ∀ (x : ℂ), x ∈ sphere z r → _root_.id x - z ≠ 0
    exact fun ζ hζ => sub_ne_zero.2 (ne_of_mem_sphere hζ hr.ne')
    -- 🎉 no goals
  show ∀ ζ ∈ sphere z r, ‖(ζ - z)⁻¹ • f ζ‖ ≤ ‖f z‖ / r
  -- ⊢ ∀ (ζ : ℂ), ζ ∈ sphere z r → ‖(ζ - z)⁻¹ • f ζ‖ ≤ ‖f z‖ / r
  · rintro ζ (hζ : abs (ζ - z) = r)
    -- ⊢ ‖(ζ - z)⁻¹ • f ζ‖ ≤ ‖f z‖ / r
    rw [le_div_iff hr, norm_smul, norm_inv, norm_eq_abs, hζ, mul_comm, mul_inv_cancel_left₀ hr.ne']
    -- ⊢ ‖f ζ‖ ≤ ‖f z‖
    exact hz (hsub hζ)
    -- 🎉 no goals
  show ‖(w - z)⁻¹ • f w‖ < ‖f z‖ / r
  -- ⊢ ‖(w - z)⁻¹ • f w‖ < ‖f z‖ / r
  · rw [norm_smul, norm_inv, norm_eq_abs, ← div_eq_inv_mul]
    -- ⊢ ‖f w‖ / ↑abs (w - z) < ‖f z‖ / r
    exact (div_lt_div_right hr).2 hw_lt
    -- 🎉 no goals
#align complex.norm_max_aux₁ Complex.norm_max_aux₁

/-!
Now we drop the assumption `CompleteSpace F` by embedding `F` into its completion.
-/

theorem norm_max_aux₂ {f : ℂ → F} {z w : ℂ} (hd : DiffContOnCl ℂ f (ball z (dist w z)))
    (hz : IsMaxOn (norm ∘ f) (closedBall z (dist w z)) z) : ‖f w‖ = ‖f z‖ := by
  set e : F →L[ℂ] F̂ := UniformSpace.Completion.toComplL
  -- ⊢ ‖f w‖ = ‖f z‖
  have he : ∀ x, ‖e x‖ = ‖x‖ := UniformSpace.Completion.norm_coe
  -- ⊢ ‖f w‖ = ‖f z‖
  replace hz : IsMaxOn (norm ∘ e ∘ f) (closedBall z (dist w z)) z
  -- ⊢ IsMaxOn (norm ∘ ↑e ∘ f) (closedBall z (dist w z)) z
  · simpa only [IsMaxOn, (· ∘ ·), he] using hz
    -- 🎉 no goals
  simpa only [he, (· ∘ ·)]
    using norm_max_aux₁ (e.differentiable.comp_diffContOnCl hd) hz
#align complex.norm_max_aux₂ Complex.norm_max_aux₂

/-!
Then we replace the assumption `IsMaxOn (norm ∘ f) (Metric.closedBall z r) z` with a seemingly
weaker assumption `IsMaxOn (norm ∘ f) (Metric.ball z r) z`.
-/

theorem norm_max_aux₃ {f : ℂ → F} {z w : ℂ} {r : ℝ} (hr : dist w z = r)
    (hd : DiffContOnCl ℂ f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) : ‖f w‖ = ‖f z‖ := by
  subst r
  -- ⊢ ‖f w‖ = ‖f z‖
  rcases eq_or_ne w z with (rfl | hne); · rfl
  -- ⊢ ‖f w‖ = ‖f w‖
                                          -- 🎉 no goals
  rw [← dist_ne_zero] at hne
  -- ⊢ ‖f w‖ = ‖f z‖
  exact norm_max_aux₂ hd (closure_ball z hne ▸ hz.closure hd.continuousOn.norm)
  -- 🎉 no goals
#align complex.norm_max_aux₃ Complex.norm_max_aux₃

/-!
### Maximum modulus principle for any codomain

If we do not assume that the codomain is a strictly convex space, then we can only claim that the
**norm** `‖f x‖` is locally constant.
-/

/-!
Finally, we generalize the theorem from a disk in `ℂ` to a closed ball in any normed space.
-/

/-- **Maximum modulus principle** on a closed ball: if `f : E → F` is continuous on a closed ball,
is complex differentiable on the corresponding open ball, and the norm `‖f w‖` takes its maximum
value on the open ball at its center, then the norm `‖f w‖` is constant on the closed ball.  -/
theorem norm_eqOn_closedBall_of_isMaxOn {f : E → F} {z : E} {r : ℝ}
    (hd : DiffContOnCl ℂ f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) :
    EqOn (norm ∘ f) (const E ‖f z‖) (closedBall z r) := by
  intro w hw
  -- ⊢ (norm ∘ f) w = Function.const E ‖f z‖ w
  rw [mem_closedBall, dist_comm] at hw
  -- ⊢ (norm ∘ f) w = Function.const E ‖f z‖ w
  rcases eq_or_ne z w with (rfl | hne); · rfl
  -- ⊢ (norm ∘ f) z = Function.const E ‖f z‖ z
                                          -- 🎉 no goals
  set e := (lineMap z w : ℂ → E)
  -- ⊢ (norm ∘ f) w = Function.const E ‖f z‖ w
  have hde : Differentiable ℂ e := (differentiable_id.smul_const (w - z)).add_const z
  -- ⊢ (norm ∘ f) w = Function.const E ‖f z‖ w
  suffices ‖(f ∘ e) (1 : ℂ)‖ = ‖(f ∘ e) (0 : ℂ)‖ by simpa
  -- ⊢ ‖(f ∘ e) 1‖ = ‖(f ∘ e) 0‖
  have hr : dist (1 : ℂ) 0 = 1 := by simp
  -- ⊢ ‖(f ∘ e) 1‖ = ‖(f ∘ e) 0‖
  have hball : MapsTo e (ball 0 1) (ball z r) := by
    refine ((lipschitzWith_lineMap z w).mapsTo_ball (mt nndist_eq_zero.1 hne) 0 1).mono
      Subset.rfl ?_
    simpa only [lineMap_apply_zero, mul_one, coe_nndist] using ball_subset_ball hw
  exact norm_max_aux₃ hr (hd.comp hde.diffContOnCl hball)
      (hz.comp_mapsTo hball (lineMap_apply_zero z w))
#align complex.norm_eq_on_closed_ball_of_is_max_on Complex.norm_eqOn_closedBall_of_isMaxOn

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a set `s`, the norm
of `f` takes it maximum on `s` at `z`, and `w` is a point such that the closed ball with center `z`
and radius `dist w z` is included in `s`, then `‖f w‖ = ‖f z‖`. -/
theorem norm_eq_norm_of_isMaxOn_of_ball_subset {f : E → F} {s : Set E} {z w : E}
    (hd : DiffContOnCl ℂ f s) (hz : IsMaxOn (norm ∘ f) s z) (hsub : ball z (dist w z) ⊆ s) :
    ‖f w‖ = ‖f z‖ :=
  norm_eqOn_closedBall_of_isMaxOn (hd.mono hsub) (hz.on_subset hsub) (mem_closedBall.2 le_rfl)
#align complex.norm_eq_norm_of_is_max_on_of_ball_subset Complex.norm_eq_norm_of_isMaxOn_of_ball_subset

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable in a neighborhood of `c`
and the norm `‖f z‖` has a local maximum at `c`, then `‖f z‖` is locally constant in a neighborhood
of `c`. -/
theorem norm_eventually_eq_of_isLocalMax {f : E → F} {c : E}
    (hd : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z) (hc : IsLocalMax (norm ∘ f) c) :
    ∀ᶠ y in 𝓝 c, ‖f y‖ = ‖f c‖ := by
  rcases nhds_basis_closedBall.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩
  -- ⊢ ∀ᶠ (y : E) in 𝓝 c, ‖f y‖ = ‖f c‖
  exact nhds_basis_closedBall.eventually_iff.2
    ⟨r, hr₀, norm_eqOn_closedBall_of_isMaxOn (DifferentiableOn.diffContOnCl fun x hx =>
        (hr <| closure_ball_subset_closedBall hx).1.differentiableWithinAt) fun x hx =>
      (hr <| ball_subset_closedBall hx).2⟩
#align complex.norm_eventually_eq_of_is_local_max Complex.norm_eventually_eq_of_isLocalMax

theorem isOpen_setOf_mem_nhds_and_isMaxOn_norm {f : E → F} {s : Set E}
    (hd : DifferentiableOn ℂ f s) : IsOpen {z | s ∈ 𝓝 z ∧ IsMaxOn (norm ∘ f) s z} := by
  refine' isOpen_iff_mem_nhds.2 fun z hz => (eventually_eventually_nhds.2 hz.1).and _
  -- ⊢ ∀ᶠ (z : E) in 𝓝 z, IsMaxOn (norm ∘ f) s z
  replace hd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w; exact hd.eventually_differentiableAt hz.1
  -- ⊢ ∀ᶠ (w : E) in 𝓝 z, DifferentiableAt ℂ f w
                                                    -- ⊢ ∀ᶠ (z : E) in 𝓝 z, IsMaxOn (norm ∘ f) s z
  exact (norm_eventually_eq_of_isLocalMax hd <| hz.2.isLocalMax hz.1).mono fun x hx y hy =>
    le_trans (hz.2 hy).out hx.ge
#align complex.is_open_set_of_mem_nhds_and_is_max_on_norm Complex.isOpen_setOf_mem_nhds_and_isMaxOn_norm

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space. Let `f : E → F` be a function that is complex differentiable on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `‖f x‖ = ‖f c‖` for all `x ∈ U`. -/
theorem norm_eqOn_of_isPreconnected_of_isMaxOn {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DifferentiableOn ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const E ‖f c‖) U := by
  set V := U ∩ {z | IsMaxOn (norm ∘ f) U z}
  -- ⊢ EqOn (norm ∘ f) (Function.const E ‖f c‖) U
  have hV : ∀ x ∈ V, ‖f x‖ = ‖f c‖ := fun x hx => le_antisymm (hm hx.1) (hx.2 hcU)
  -- ⊢ EqOn (norm ∘ f) (Function.const E ‖f c‖) U
  suffices : U ⊆ V; exact fun x hx => hV x (this hx)
  -- ⊢ EqOn (norm ∘ f) (Function.const E ‖f c‖) U
                    -- ⊢ U ⊆ V
  have hVo : IsOpen V := by
    simpa only [ho.mem_nhds_iff, setOf_and, setOf_mem_eq]
      using isOpen_setOf_mem_nhds_and_isMaxOn_norm hd
  have hVne : (U ∩ V).Nonempty := ⟨c, hcU, hcU, hm⟩
  -- ⊢ U ⊆ V
  set W := U ∩ {z | ‖f z‖ ≠ ‖f c‖}
  -- ⊢ U ⊆ V
  have hWo : IsOpen W := hd.continuousOn.norm.preimage_open_of_open ho isOpen_ne
  -- ⊢ U ⊆ V
  have hdVW : Disjoint V W := disjoint_left.mpr fun x hxV hxW => hxW.2 (hV x hxV)
  -- ⊢ U ⊆ V
  have hUVW : U ⊆ V ∪ W := fun x hx =>
    (eq_or_ne ‖f x‖ ‖f c‖).imp (fun h => ⟨hx, fun y hy => (hm hy).out.trans_eq h.symm⟩)
      (And.intro hx)
  exact hc.subset_left_of_subset_union hVo hWo hdVW hUVW hVne
  -- 🎉 no goals
#align complex.norm_eq_on_of_is_preconnected_of_is_max_on Complex.norm_eqOn_of_isPreconnected_of_isMaxOn

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U` and is
continuous on its closure. Suppose that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then
`‖f x‖ = ‖f c‖` for all `x ∈ closure U`. -/
theorem norm_eqOn_closure_of_isPreconnected_of_isMaxOn {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DiffContOnCl ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const E ‖f c‖) (closure U) :=
  (norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hd.differentiableOn hcU hm).of_subset_closure
    hd.continuousOn.norm continuousOn_const subset_closure Subset.rfl
#align complex.norm_eq_on_closure_of_is_preconnected_of_is_max_on Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn

section StrictConvex

/-!
### The case of a strictly convex codomain

If the codomain `F` is a strictly convex space, then we can claim equalities like `f w = f z`
instead of `‖f w‖ = ‖f z‖`.

Instead of repeating the proof starting with lemmas about integrals, we apply a corresponding lemma
above twice: for `f` and for `(f · + f c)`.  Then we have `‖f w‖ = ‖f z‖` and
`‖f w + f z‖ = ‖f z + f z‖`, thus `‖f w + f z‖ = ‖f w‖ + ‖f z‖`. This is only possible if
`f w = f z`, see `eq_of_norm_eq_of_norm_add_eq`.
-/

variable [StrictConvexSpace ℝ F]

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `f x = f c` for all `x ∈ U`.

TODO: change assumption from `IsMaxOn` to `IsLocalMax`. -/
theorem eqOn_of_isPreconnected_of_isMaxOn_norm {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DifferentiableOn ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const E (f c)) U := fun x hx =>
  have H₁ : ‖f x‖ = ‖f c‖ := norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hd hcU hm hx
  have H₂ : ‖f x + f c‖ = ‖f c + f c‖ :=
    norm_eqOn_of_isPreconnected_of_isMaxOn hc ho (hd.add_const _) hcU hm.norm_add_self hx
  eq_of_norm_eq_of_norm_add_eq H₁ <| by simp only [H₂, SameRay.rfl.norm_add, H₁, Function.const]
                                        -- 🎉 no goals
#align complex.eq_on_of_is_preconnected_of_is_max_on_norm Complex.eqOn_of_isPreconnected_of_isMaxOn_norm

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U` and is
continuous on its closure. Suppose that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then
`f x = f c` for all `x ∈ closure U`. -/
theorem eqOn_closure_of_isPreconnected_of_isMaxOn_norm {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DiffContOnCl ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const E (f c)) (closure U) :=
  (eqOn_of_isPreconnected_of_isMaxOn_norm hc ho hd.differentiableOn hcU hm).of_subset_closure
    hd.continuousOn continuousOn_const subset_closure Subset.rfl
#align complex.eq_on_closure_of_is_preconnected_of_is_max_on_norm Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm

/-- **Maximum modulus principle**. Let `f : E → F` be a function between complex normed spaces.
Suppose that the codomain `F` is a strictly convex space, `f` is complex differentiable on a set
`s`, `f` is continuous on the closure of `s`, the norm of `f` takes it maximum on `s` at `z`, and
`w` is a point such that the closed ball with center `z` and radius `dist w z` is included in `s`,
then `f w = f z`. -/
theorem eq_of_isMaxOn_of_ball_subset {f : E → F} {s : Set E} {z w : E} (hd : DiffContOnCl ℂ f s)
    (hz : IsMaxOn (norm ∘ f) s z) (hsub : ball z (dist w z) ⊆ s) : f w = f z :=
  have H₁ : ‖f w‖ = ‖f z‖ := norm_eq_norm_of_isMaxOn_of_ball_subset hd hz hsub
  have H₂ : ‖f w + f z‖ = ‖f z + f z‖ :=
    norm_eq_norm_of_isMaxOn_of_ball_subset (hd.add_const _) hz.norm_add_self hsub
  eq_of_norm_eq_of_norm_add_eq H₁ <| by simp only [H₂, SameRay.rfl.norm_add, H₁]
                                        -- 🎉 no goals
#align complex.eq_of_is_max_on_of_ball_subset Complex.eq_of_isMaxOn_of_ball_subset

/-- **Maximum modulus principle** on a closed ball. Suppose that a function `f : E → F` from a
normed complex space to a strictly convex normed complex space has the following properties:

- it is continuous on a closed ball `Metric.closedBall z r`,
- it is complex differentiable on the corresponding open ball;
- the norm `‖f w‖` takes its maximum value on the open ball at its center.

Then `f` is a constant on the closed ball.  -/
theorem eqOn_closedBall_of_isMaxOn_norm {f : E → F} {z : E} {r : ℝ}
    (hd : DiffContOnCl ℂ f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) :
    EqOn f (const E (f z)) (closedBall z r) := fun _x hx =>
  eq_of_isMaxOn_of_ball_subset hd hz <| ball_subset_ball hx
#align complex.eq_on_closed_ball_of_is_max_on_norm Complex.eqOn_closedBall_of_isMaxOn_norm

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable in a neighborhood of `c`
and the norm `‖f z‖` has a local maximum at `c`, then `f` is locally constant in a neighborhood
of `c`. -/
theorem eventually_eq_of_isLocalMax_norm {f : E → F} {c : E}
    (hd : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z) (hc : IsLocalMax (norm ∘ f) c) :
    ∀ᶠ y in 𝓝 c, f y = f c := by
  rcases nhds_basis_closedBall.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩
  -- ⊢ ∀ᶠ (y : E) in 𝓝 c, f y = f c
  exact nhds_basis_closedBall.eventually_iff.2
    ⟨r, hr₀, eqOn_closedBall_of_isMaxOn_norm (DifferentiableOn.diffContOnCl fun x hx =>
        (hr <| closure_ball_subset_closedBall hx).1.differentiableWithinAt) fun x hx =>
      (hr <| ball_subset_closedBall hx).2⟩
#align complex.eventually_eq_of_is_local_max_norm Complex.eventually_eq_of_isLocalMax_norm

theorem eventually_eq_or_eq_zero_of_isLocalMin_norm {f : E → ℂ} {c : E}
    (hf : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z) (hc : IsLocalMin (norm ∘ f) c) :
    (∀ᶠ z in 𝓝 c, f z = f c) ∨ f c = 0 := by
  refine' or_iff_not_imp_right.mpr fun h => _
  -- ⊢ ∀ᶠ (z : E) in 𝓝 c, f z = f c
  have h1 : ∀ᶠ z in 𝓝 c, f z ≠ 0 := hf.self_of_nhds.continuousAt.eventually_ne h
  -- ⊢ ∀ᶠ (z : E) in 𝓝 c, f z = f c
  have h2 : IsLocalMax (norm ∘ f)⁻¹ c := hc.inv (h1.mono fun z => norm_pos_iff.mpr)
  -- ⊢ ∀ᶠ (z : E) in 𝓝 c, f z = f c
  have h3 : IsLocalMax (norm ∘ f⁻¹) c := by refine' h2.congr (eventually_of_forall _); simp
  -- ⊢ ∀ᶠ (z : E) in 𝓝 c, f z = f c
  have h4 : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f⁻¹ z := by filter_upwards [hf, h1] with z h using h.inv
  -- ⊢ ∀ᶠ (z : E) in 𝓝 c, f z = f c
  filter_upwards [eventually_eq_of_isLocalMax_norm h4 h3] with z using inv_inj.mp
  -- 🎉 no goals
#align complex.eventually_eq_or_eq_zero_of_is_local_min_norm Complex.eventually_eq_or_eq_zero_of_isLocalMin_norm

end StrictConvex

/-!
### Maximum on a set vs maximum on its frontier

In this section we prove corollaries of the maximum modulus principle that relate the values of a
function on a set to its values on the frontier of this set.
-/


variable [Nontrivial E]

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a nonempty bounded
set `U` and is continuous on its closure, then there exists a point `z ∈ frontier U` such that
`(‖f ·‖)` takes it maximum value on `closure U` at `z`. -/
theorem exists_mem_frontier_isMaxOn_norm [FiniteDimensional ℂ E] {f : E → F} {U : Set E}
    (hb : Bounded U) (hne : U.Nonempty) (hd : DiffContOnCl ℂ f U) :
    ∃ z ∈ frontier U, IsMaxOn (norm ∘ f) (closure U) z := by
  have hc : IsCompact (closure U) := hb.isCompact_closure
  -- ⊢ ∃ z, z ∈ frontier U ∧ IsMaxOn (norm ∘ f) (closure U) z
  obtain ⟨w, hwU, hle⟩ : ∃ w ∈ closure U, IsMaxOn (norm ∘ f) (closure U) w
  -- ⊢ ∃ w, w ∈ closure U ∧ IsMaxOn (norm ∘ f) (closure U) w
  exact hc.exists_forall_ge hne.closure hd.continuousOn.norm
  -- ⊢ ∃ z, z ∈ frontier U ∧ IsMaxOn (norm ∘ f) (closure U) z
  rw [closure_eq_interior_union_frontier, mem_union] at hwU
  -- ⊢ ∃ z, z ∈ frontier U ∧ IsMaxOn (norm ∘ f) (closure U) z
  cases' hwU with hwU hwU; rotate_left; · exact ⟨w, hwU, hle⟩
  -- ⊢ ∃ z, z ∈ frontier U ∧ IsMaxOn (norm ∘ f) (closure U) z
                           -- ⊢ ∃ z, z ∈ frontier U ∧ IsMaxOn (norm ∘ f) (closure U) z
                                          -- 🎉 no goals
  have : interior U ≠ univ := ne_top_of_le_ne_top hc.ne_univ interior_subset_closure
  -- ⊢ ∃ z, z ∈ frontier U ∧ IsMaxOn (norm ∘ f) (closure U) z
  rcases exists_mem_frontier_infDist_compl_eq_dist hwU this with ⟨z, hzU, hzw⟩
  -- ⊢ ∃ z, z ∈ frontier U ∧ IsMaxOn (norm ∘ f) (closure U) z
  refine' ⟨z, frontier_interior_subset hzU, fun x hx => (hle hx).out.trans_eq _⟩
  -- ⊢ (norm ∘ f) w = (norm ∘ f) z
  refine' (norm_eq_norm_of_isMaxOn_of_ball_subset hd (hle.on_subset subset_closure) _).symm
  -- ⊢ ball w (dist z w) ⊆ U
  rw [dist_comm, ← hzw]
  -- ⊢ ball w (infDist w (interior U)ᶜ) ⊆ U
  exact ball_infDist_compl_subset.trans interior_subset
  -- 🎉 no goals
#align complex.exists_mem_frontier_is_max_on_norm Complex.exists_mem_frontier_isMaxOn_norm

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a bounded set `U` and
`‖f z‖ ≤ C` for any `z ∈ frontier U`, then the same is true for any `z ∈ closure U`. -/
theorem norm_le_of_forall_mem_frontier_norm_le {f : E → F} {U : Set E} (hU : Bounded U)
    (hd : DiffContOnCl ℂ f U) {C : ℝ} (hC : ∀ z ∈ frontier U, ‖f z‖ ≤ C) {z : E}
    (hz : z ∈ closure U) : ‖f z‖ ≤ C := by
  rw [closure_eq_self_union_frontier, union_comm, mem_union] at hz
  -- ⊢ ‖f z‖ ≤ C
  cases' hz with hz hz; · exact hC z hz
  -- ⊢ ‖f z‖ ≤ C
                          -- 🎉 no goals
  /- In case of a finite dimensional domain, one can just apply
    `Complex.exists_mem_frontier_isMaxOn_norm`. To make it work in any Banach space, we restrict
    the function to a line first. -/
  rcases exists_ne z with ⟨w, hne⟩
  -- ⊢ ‖f z‖ ≤ C
  set e := (lineMap z w : ℂ → E)
  -- ⊢ ‖f z‖ ≤ C
  have hde : Differentiable ℂ e := (differentiable_id.smul_const (w - z)).add_const z
  -- ⊢ ‖f z‖ ≤ C
  have hL : AntilipschitzWith (nndist z w)⁻¹ e := antilipschitzWith_lineMap hne.symm
  -- ⊢ ‖f z‖ ≤ C
  replace hd : DiffContOnCl ℂ (f ∘ e) (e ⁻¹' U)
  -- ⊢ DiffContOnCl ℂ (f ∘ e) (e ⁻¹' U)
  exact hd.comp hde.diffContOnCl (mapsTo_preimage _ _)
  -- ⊢ ‖f z‖ ≤ C
  have h₀ : (0 : ℂ) ∈ e ⁻¹' U := by simpa only [mem_preimage, lineMap_apply_zero]
  -- ⊢ ‖f z‖ ≤ C
  rcases exists_mem_frontier_isMaxOn_norm (hL.bounded_preimage hU) ⟨0, h₀⟩ hd with ⟨ζ, hζU, hζ⟩
  -- ⊢ ‖f z‖ ≤ C
  calc
    ‖f z‖ = ‖f (e 0)‖ := by simp only [lineMap_apply_zero]
    _ ≤ ‖f (e ζ)‖ := (hζ (subset_closure h₀))
    _ ≤ C := hC _ (hde.continuous.frontier_preimage_subset _ hζU)
#align complex.norm_le_of_forall_mem_frontier_norm_le Complex.norm_le_of_forall_mem_frontier_norm_le

/-- If two complex differentiable functions `f g : E → F` are equal on the boundary of a bounded set
`U`, then they are equal on `closure U`. -/
theorem eqOn_closure_of_eqOn_frontier {f g : E → F} {U : Set E} (hU : Bounded U)
    (hf : DiffContOnCl ℂ f U) (hg : DiffContOnCl ℂ g U) (hfg : EqOn f g (frontier U)) :
    EqOn f g (closure U) := by
  suffices H : ∀ z ∈ closure U, ‖(f - g) z‖ ≤ 0; · simpa [sub_eq_zero] using H
  -- ⊢ EqOn f g (closure U)
                                                   -- 🎉 no goals
  refine' fun z hz => norm_le_of_forall_mem_frontier_norm_le hU (hf.sub hg) (fun w hw => _) hz
  -- ⊢ ‖(f - g) w‖ ≤ 0
  simp [hfg hw]
  -- 🎉 no goals
#align complex.eq_on_closure_of_eq_on_frontier Complex.eqOn_closure_of_eqOn_frontier

/-- If two complex differentiable functions `f g : E → F` are equal on the boundary of a bounded set
`U`, then they are equal on `U`. -/
theorem eqOn_of_eqOn_frontier {f g : E → F} {U : Set E} (hU : Bounded U) (hf : DiffContOnCl ℂ f U)
    (hg : DiffContOnCl ℂ g U) (hfg : EqOn f g (frontier U)) : EqOn f g U :=
  (eqOn_closure_of_eqOn_frontier hU hf hg hfg).mono subset_closure
#align complex.eq_on_of_eq_on_frontier Complex.eqOn_of_eqOn_frontier

end Complex

