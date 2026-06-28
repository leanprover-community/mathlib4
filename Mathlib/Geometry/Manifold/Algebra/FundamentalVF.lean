/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
# Fundamental vector fields of a Lie group action are Lie algebra (anti-)homomorphisms

For a Lie group `G`, the assignment sending a Lie algebra element `A ∈ 𝔤` to its *fundamental
vector field* (the infinitesimal generator of the corresponding flow) intertwines the Lie algebra
bracket with the Lie bracket of vector fields, up to a sign that depends on the handedness of the
action.

We work with the canonical actions of `G` on itself:

* **Right multiplication** `p ↦ p * g` has, as its fundamental vector fields, the *left-invariant*
  vector fields `mulInvariantVectorField`. For these the assignment is a genuine Lie algebra
  homomorphism:
  `mulInvariantVectorField ⁅A, B⁆ = ⁅mulInvariantVectorField A, mulInvariantVectorField B⁆`
  (`mulInvariantVectorField_bracket`). This is essentially the definition of the Lie bracket on
  `GroupLieAlgebra I G` and is already available in Mathlib via `mulInvariantVector_mlieBracket`.

* **Left multiplication** `p ↦ g * p`, whose fundamental vector field of `A` is
  `funVF A p = D(· * p)₁ A`  (the *right-invariant* vector field, the infinitesimal generator of
  `t ↦ exp (t A) * p`). For these the assignment is a Lie algebra *anti*-homomorphism:
  `⁅funVF A, funVF B⁆ = - funVF ⁅A, B⁆` (`mlieBracket_funVF_eq_neg`).

The minus sign for the left action is the derivative of the inversion map at the identity
(`mfderiv_inv_one`): right-invariant vector fields are the pushforwards of left-invariant ones
under group inversion, which is an anti-automorphism.
-/

open Bundle Filter Function Set VectorField
open scoped Manifold

namespace FundamentalVectorField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness 𝕜 3) G]

/-- The fundamental vector field of the left action of `G` on itself by left multiplication.
At a point `p`, it is the derivative of right multiplication `(· * p)` at the identity, applied to
`A`; equivalently it is the velocity at `t = 0` of the orbit `t ↦ exp (t A) * p`. This is the
right-invariant vector field associated to `A`. -/
noncomputable def funVF (A : GroupLieAlgebra I G) (p : G) : TangentSpace I p :=
  mfderiv I I (· * p) 1 A

/-
The fundamental vector field is linear in `A`: negation.
-/
lemma funVF_neg (A : GroupLieAlgebra I G) : funVF (-A) = - funVF (I := I) (G := G) A := by
  ext p; unfold funVF; simp only [map_neg]
  exact rfl

/-
The derivative of the multiplication map `G × G → G` at the identity `(1, 1)` is the sum of
the two components.
-/
lemma mfderiv_mul_at_one (v : TangentSpace (I.prod I) ((1 : G), (1 : G))) :
    (mfderiv (I.prod I) I (fun p : G × G => p.1 * p.2) ((1 : G), (1 : G)) v : E)
      = (v.1 : E) + (v.2 : E) := by
  rw [ mfderiv_prod_eq_add_apply ];
  · congr! 1;
    · rw [ show ( fun z : G => z * 1 ) = id from funext fun _ => mul_one _ ];
      rw [ mfderiv_id ];
      rfl;
    · rw [ show ( fun z : G => 1 * z ) = id from funext fun _ => one_mul _ ];
      rw [ mfderiv_id ];
      rfl;
  · apply_rules [ ContMDiffAt.mdifferentiableAt ];
    · convert ( ‹LieGroup I ( minSmoothness 𝕜 3 ) G›.contMDiff_mul ) |> ContMDiff.contMDiffAt;
    · simp +decide only [ minSmoothness, ne_eq ];
      split_ifs <;> norm_num

/-- The derivative of `g ↦ (g, g⁻¹)` at the identity. -/
lemma mfderiv_prodMk_inv (A : GroupLieAlgebra I G) :
    mfderiv I (I.prod I) (fun g : G => (g, g⁻¹)) (1 : G) A
      = (A, mfderiv I I (fun g : G => g⁻¹) (1 : G) A) := by
  have hne : (minSmoothness 𝕜 3) ≠ 0 := by
    simp [minSmoothness]; split_ifs <;> norm_num
  have hinv : MDifferentiableAt I I (fun g : G => g⁻¹) (1 : G) :=
    (contMDiff_inv I (minSmoothness 𝕜 3)).mdifferentiableAt hne
  rw [show (fun g : G => (g, g⁻¹)) = (fun g : G => (id g, g⁻¹)) from rfl,
    mfderiv_prodMk mdifferentiableAt_id hinv]
  refine (ContinuousLinearMap.prod_apply
    (mfderiv I I (id : G → G) 1) (mfderiv I I (fun g : G => g⁻¹) 1) A).trans ?_
  rw [mfderiv_id]; rfl

/-
`g ↦ g * g⁻¹` is the constant map `1`, so its derivative vanishes.
-/
lemma mfderiv_mul_inv_self_eq_zero (A : GroupLieAlgebra I G) :
    (mfderiv I I (fun g : G => g * g⁻¹) (1 : G) A : E) = 0 := by
  simp_all +decide [ mfderiv ];
  split_ifs <;> simp_all +decide [ Function.comp_def ];
  rfl

/-- The derivative of the inversion map at the identity of a Lie group is negation.  This is the
source of the sign distinguishing left and right actions. -/
lemma mfderiv_inv_one (A : GroupLieAlgebra I G) :
    (mfderiv I I (fun g : G => g⁻¹) (1 : G) A : E) = -A := by
  have hne : (minSmoothness 𝕜 3) ≠ 0 := by
    simp [minSmoothness]; split_ifs <;> norm_num
  have hf : MDifferentiableAt I (I.prod I) (fun g : G => (g, g⁻¹)) (1 : G) :=
    mdifferentiableAt_id.prodMk
      ((contMDiff_inv I (minSmoothness 𝕜 3)).mdifferentiableAt hne)
  have hg : MDifferentiableAt (I.prod I) I (fun p : G × G => p.1 * p.2) ((1 : G), (1 : G)⁻¹) :=
    (contMDiff_mul I (minSmoothness 𝕜 3)).mdifferentiableAt hne
  have hcomp := mfderiv_comp (I := I) (I' := I.prod I) (I'' := I) (1 : G) hg hf
  have step1 : (mfderiv I I (fun g : G => g * g⁻¹) 1 A : E)
      = mfderiv (I.prod I) I (fun p : G × G => p.1 * p.2) ((1:G), (1:G)⁻¹)
          (mfderiv I (I.prod I) (fun g : G => (g, g⁻¹)) 1 A) :=
    (congrArg (fun L => L A) hcomp).trans
      (by simp only [Function.comp]; exact ContinuousLinearMap.comp_apply _ _ A)
  rw [mfderiv_prodMk_inv] at step1
  rw [show ((1:G), (1:G)⁻¹) = ((1:G),(1:G)) from by rw [inv_one]] at step1
  rw [mfderiv_mul_at_one] at step1
  have h0 := mfderiv_mul_inv_self_eq_zero (I := I) (G := G) A
  rw [step1] at h0
  dsimp only at h0
  exact eq_neg_of_add_eq_zero_right h0

/-
The inverse of the derivative of inversion at `g` is the derivative of inversion at `g⁻¹`
(inversion is an involution).
-/
lemma inverse_mfderiv_inv {g : G} :
    (mfderiv I I (fun b : G => b⁻¹) g).inverse = mfderiv I I (fun b : G => b⁻¹) g⁻¹ := by
  have hne : (minSmoothness 𝕜 3 : WithTop ℕ∞) ≠ 0 := by
    simp [minSmoothness]; split_ifs <;> norm_num
  have hInvDiff : ∀ h : G, MDifferentiableAt I I (fun b : G => b⁻¹) h :=
    fun h => (contMDiff_inv I (minSmoothness 𝕜 3)).mdifferentiableAt hne
  rw [ContinuousLinearMap.inverse_eq]
  · have h_comp : mfderiv I I (fun b : G => (b⁻¹)⁻¹) g⁻¹ =
        mfderiv I I (fun b : G => b⁻¹) g ∘L mfderiv I I (fun b : G => b⁻¹) g⁻¹ := by
      apply HasMFDerivAt.mfderiv
      have h1 := (hInvDiff g⁻¹).hasMFDerivAt
      have h2 : HasMFDerivAt I I (fun b : G => b⁻¹) (g⁻¹⁻¹)
          (mfderiv I I (fun b : G => b⁻¹) g) := by
        rw [inv_inv]; exact (hInvDiff g).hasMFDerivAt
      exact h2.comp g⁻¹ h1
    rw [← h_comp, show (fun b : G => b⁻¹⁻¹) = id from funext fun x => inv_inv x]
    simp [mfderiv_id]
  · have h_comp : mfderiv I I (fun b : G => (b⁻¹)⁻¹) g =
        mfderiv I I (fun b : G => b⁻¹) g⁻¹ ∘L mfderiv I I (fun b : G => b⁻¹) g := by
      have hchain := mfderiv_comp (I := I) (I' := I) (I'' := I)
        g (hInvDiff g⁻¹) (hInvDiff g)
      simp only [Function.comp] at hchain
      exact hchain
    have foo : (mfderiv I I fun b : G ↦ b⁻¹⁻¹) g = (mfderiv I I fun b : G ↦ b) g := by
      congr 1
      ext b
      exact inv_inv b
    have bar : (mfderiv I I fun b : G ↦ b) g = ContinuousLinearMap.id 𝕜 (TangentSpace I g) := by
      have h : (fun b : G ↦ b) = id := rfl
      rw [h]
      exact mfderiv_id
    have := h_comp.symm.trans (foo.trans bar)
    exact this

/-
The fundamental vector field of the left action (right-invariant field) is the pushforward of
the left-invariant vector field of `-A` under group inversion.
-/
lemma funVF_eq_mpullback_inv (A : GroupLieAlgebra I G) :
    funVF A = mpullback I I (fun g : G => g⁻¹) (mulInvariantVectorField (-A)) := by
  apply funext
  intro p
  simp only [funVF, mpullback, mulInvariantVectorField]
  have hne : (minSmoothness 𝕜 3 : WithTop ℕ∞) ≠ 0 := by
    simp [minSmoothness]; split_ifs <;> norm_num
  have hInv : MDifferentiableAt I I (fun x : G => x⁻¹) 1 :=
    (contMDiff_inv I (minSmoothness 𝕜 3)).mdifferentiableAt hne
  have hInv' : ∀ g : G, MDifferentiableAt I I (fun x : G => x⁻¹) g :=
    fun g => (contMDiff_inv I (minSmoothness 𝕜 3)).mdifferentiableAt hne
  have hMulP : MDifferentiableAt I I (fun x : G => x * p) 1 :=
    (contMDiff_mul_right (a := p) (n := minSmoothness 𝕜 3)).mdifferentiableAt hne
  have hMulP' : MDifferentiableAt I I (fun x : G => x * p) (1 : G)⁻¹ := by
    simp only [inv_one]; exact hMulP
  have hMulL : MDifferentiableAt I I (fun x : G => p⁻¹ * x) 1 :=
    (contMDiff_mul_left (a := p⁻¹) (n := minSmoothness 𝕜 3)).mdifferentiableAt hne
  have hInvPinv : MDifferentiableAt I I (fun x : G => x⁻¹) (p⁻¹ * 1) := by
    simp only [mul_one]; exact hInv'  p⁻¹
  have h_chain : mfderiv I I (fun x => x⁻¹ * p) 1 (-A) =
      mfderiv I I (fun x => x * p) 1 (mfderiv I I (fun x => x⁻¹) 1 (-A)) := by
    convert congr_arg (fun f => f (-A))
        (mfderiv_comp (x := 1) hMulP' hInv) using 1
    · rw [inv_one]; exact rfl
  convert h_chain.symm using 1
  · rw [mfderiv_inv_one]; simp +decide
  · have h_chain2 : mfderiv I I (fun x => x⁻¹ * p) 1 (-A) =
        mfderiv I I (fun x => x⁻¹) p⁻¹ (mfderiv I I (fun x => p⁻¹ * x) 1 (-A)) := by
      convert congr_arg (fun f => f (-A))
          (mfderiv_comp 1 hInvPinv hMulL) using 1
      · have : (fun x : G => x⁻¹ * p) = (fun x => x⁻¹) ∘ HMul.hMul p⁻¹ := by
          ext x; simp [mul_inv_rev, inv_inv]
        rw [this]; exact rfl
      · rw [mul_one]; exact rfl
    rw [h_chain2, inverse_mfderiv_inv]
    simp only [map_neg]
    exact rfl

variable [CompleteSpace E]

/-
**Right action ⇒ Lie algebra homomorphism.** The left-invariant vector field assignment
`A ↦ mulInvariantVectorField A` (the fundamental vector field of the right multiplication action)
is a Lie algebra homomorphism: it sends the Lie algebra bracket to the Lie bracket of vector
fields.
-/
theorem mulInvariantVectorField_bracket (A B : GroupLieAlgebra I G) :
    mulInvariantVectorField ⁅A, B⁆ =
      mlieBracket I (mulInvariantVectorField A) (mulInvariantVectorField B) := by
  convert mulInvariantVector_mlieBracket A B

/-
**Left action ⇒ Lie algebra anti-homomorphism (pointwise form).** The Lie bracket of the
fundamental vector fields of the left multiplication action equals the fundamental vector field of
the *negated* Lie algebra bracket.
-/
theorem mlieBracket_funVF (A B : GroupLieAlgebra I G) (g : G) :
    mlieBracket I (funVF A) (funVF B) g = funVF (-⁅A, B⁆) g := by
  rw [ funVF_eq_mpullback_inv, funVF_eq_mpullback_inv, funVF_eq_mpullback_inv ];
  rw [ ← mpullback_mlieBracket ];
  any_goals exact minSmoothness 𝕜 3;
  · rw [ ← mulInvariantVectorField_bracket ];
    simp +decide [ neg_lie ];
  · exact mdifferentiableAt_mulInvariantVectorField _;
  · exact mdifferentiableAt_mulInvariantVectorField _;
  · exact contMDiff_inv I ( minSmoothness 𝕜 3 ) g;
  · exact minSmoothness_monotone ( by norm_num )

/-- **Left action ⇒ Lie algebra anti-homomorphism.** The assignment `A ↦ funVF A` sending a Lie
algebra element to the fundamental vector field of the left multiplication action is a Lie algebra
*anti*-homomorphism: `⁅funVF A, funVF B⁆ = - funVF ⁅A, B⁆`. -/
theorem mlieBracket_funVF_eq_neg (A B : GroupLieAlgebra I G) :
    mlieBracket I (funVF A) (funVF B) = - funVF ⁅A, B⁆ := by
  funext g
  rw [mlieBracket_funVF, funVF_neg]

end FundamentalVectorField
