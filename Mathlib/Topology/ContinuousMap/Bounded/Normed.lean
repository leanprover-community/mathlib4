/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Inheritance of normed algebraic structures by bounded continuous functions

For various types of normed algebraic structures `β`, we show in this file that the space of
bounded continuous functions from `α` to `β` inherits the same normed structure, by using
pointwise operations and checking that they are compatible with the uniform distance.
-/

assert_not_exists CStarRing

noncomputable section

open NNReal Set Function

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace BoundedContinuousFunction

section NormedAddCommGroup

variable [TopologicalSpace α] [SeminormedAddCommGroup β]
variable (f g : α →ᵇ β) {x : α} {C : ℝ}

instance instNorm : Norm (α →ᵇ β) := ⟨(dist · 0)⟩

theorem norm_def : ‖f‖ = dist f 0 := rfl

/-- The norm of a bounded continuous function is the supremum of `‖f x‖`.
We use `sInf` to ensure that the definition works if `α` has no elements. -/
theorem norm_eq (f : α →ᵇ β) : ‖f‖ = sInf { C : ℝ | 0 ≤ C ∧ ∀ x : α, ‖f x‖ ≤ C } := by
  simp [norm_def, BoundedContinuousFunction.dist_eq]

/-- When the domain is non-empty, we do not need the `0 ≤ C` condition in the formula for `‖f‖` as a
`sInf`. -/
theorem norm_eq_of_nonempty [h : Nonempty α] : ‖f‖ = sInf { C : ℝ | ∀ x : α, ‖f x‖ ≤ C } := by
  obtain ⟨a⟩ := h
  rw [norm_eq]
  congr
  ext
  simp only [and_iff_right_iff_imp]
  exact fun h' => le_trans (norm_nonneg (f a)) (h' a)

@[simp]
theorem norm_eq_zero_of_empty [IsEmpty α] : ‖f‖ = 0 :=
  dist_zero_of_empty

theorem norm_coe_le_norm (x : α) : ‖f x‖ ≤ ‖f‖ :=
  calc
    ‖f x‖ = dist (f x) ((0 : α →ᵇ β) x) := by simp [dist_zero_right]
    _ ≤ ‖f‖ := dist_coe_le_dist _

lemma neg_norm_le_apply (f : α →ᵇ ℝ) (x : α) :
    -‖f‖ ≤ f x := (abs_le.mp (norm_coe_le_norm f x)).1

lemma apply_le_norm (f : α →ᵇ ℝ) (x : α) :
    f x ≤ ‖f‖ := (abs_le.mp (norm_coe_le_norm f x)).2

theorem dist_le_two_norm' {f : γ → β} {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x y : γ) :
    dist (f x) (f y) ≤ 2 * C :=
  calc
    dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
    _ ≤ C + C := add_le_add (hC x) (hC y)
    _ = 2 * C := (two_mul _).symm

/-- Distance between the images of any two points is at most twice the norm of the function. -/
theorem dist_le_two_norm (x y : α) : dist (f x) (f y) ≤ 2 * ‖f‖ :=
  dist_le_two_norm' f.norm_coe_le_norm x y

variable {f}

/-- The norm of a function is controlled by the supremum of the pointwise norms. -/
theorem norm_le (C0 : (0 : ℝ) ≤ C) : ‖f‖ ≤ C ↔ ∀ x : α, ‖f x‖ ≤ C := by
  simpa using @dist_le _ _ _ _ f 0 _ C0

theorem norm_le_of_nonempty [Nonempty α] {f : α →ᵇ β} {M : ℝ} : ‖f‖ ≤ M ↔ ∀ x, ‖f x‖ ≤ M := by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_le_iff_of_nonempty

theorem norm_lt_iff_of_compact [CompactSpace α] {f : α →ᵇ β} {M : ℝ} (M0 : 0 < M) :
    ‖f‖ < M ↔ ∀ x, ‖f x‖ < M := by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_lt_iff_of_compact M0

theorem norm_lt_iff_of_nonempty_compact [Nonempty α] [CompactSpace α] {f : α →ᵇ β} {M : ℝ} :
    ‖f‖ < M ↔ ∀ x, ‖f x‖ < M := by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_lt_iff_of_nonempty_compact

variable (f)

/-- Norm of `const α b` is less than or equal to `‖b‖`. If `α` is nonempty,
then it is equal to `‖b‖`. -/
theorem norm_const_le (b : β) : ‖const α b‖ ≤ ‖b‖ :=
  (norm_le (norm_nonneg b)).2 fun _ => le_rfl

@[simp]
theorem norm_const_eq [h : Nonempty α] (b : β) : ‖const α b‖ = ‖b‖ :=
  le_antisymm (norm_const_le b) <| h.elim fun x => (const α b).norm_coe_le_norm x

/-- Constructing a bounded continuous function from a uniformly bounded continuous
function taking values in a normed group. -/
def ofNormedAddCommGroup {α : Type u} {β : Type v} [TopologicalSpace α] [SeminormedAddCommGroup β]
    (f : α → β) (Hf : Continuous f) (C : ℝ) (H : ∀ x, ‖f x‖ ≤ C) : α →ᵇ β :=
  ⟨⟨fun n => f n, Hf⟩, ⟨_, dist_le_two_norm' H⟩⟩

@[simp]
theorem coe_ofNormedAddCommGroup {α : Type u} {β : Type v} [TopologicalSpace α]
    [SeminormedAddCommGroup β] (f : α → β) (Hf : Continuous f) (C : ℝ) (H : ∀ x, ‖f x‖ ≤ C) :
    (ofNormedAddCommGroup f Hf C H : α → β) = f := rfl

theorem norm_ofNormedAddCommGroup_le {f : α → β} (hfc : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hfC : ∀ x, ‖f x‖ ≤ C) : ‖ofNormedAddCommGroup f hfc C hfC‖ ≤ C :=
  (norm_le hC).2 hfC

/-- Constructing a bounded continuous function from a uniformly bounded
function on a discrete space, taking values in a normed group. -/
def ofNormedAddCommGroupDiscrete {α : Type u} {β : Type v} [TopologicalSpace α] [DiscreteTopology α]
    [SeminormedAddCommGroup β] (f : α → β) (C : ℝ) (H : ∀ x, norm (f x) ≤ C) : α →ᵇ β :=
  ofNormedAddCommGroup f continuous_of_discreteTopology C H

@[simp]
theorem coe_ofNormedAddCommGroupDiscrete {α : Type u} {β : Type v} [TopologicalSpace α]
    [DiscreteTopology α] [SeminormedAddCommGroup β] (f : α → β) (C : ℝ) (H : ∀ x, ‖f x‖ ≤ C) :
    (ofNormedAddCommGroupDiscrete f C H : α → β) = f := rfl

/-- Taking the pointwise norm of a bounded continuous function with values in a
`SeminormedAddCommGroup` yields a bounded continuous function with values in ℝ. -/
def normComp : α →ᵇ ℝ :=
  f.comp norm lipschitzWith_one_norm

@[simp]
theorem coe_normComp : (f.normComp : α → ℝ) = norm ∘ f := rfl

@[simp]
theorem norm_normComp : ‖f.normComp‖ = ‖f‖ := by
  simp only [norm_eq, coe_normComp, norm_norm, Function.comp]

theorem bddAbove_range_norm_comp : BddAbove <| Set.range <| norm ∘ f :=
  (@isBounded_range _ _ _ _ f.normComp).bddAbove

theorem norm_eq_iSup_norm : ‖f‖ = ⨆ x : α, ‖f x‖ := by
  simp_rw [norm_def, dist_eq_iSup, coe_zero, Pi.zero_apply, dist_zero_right]

/-- If `‖(1 : β)‖ = 1`, then `‖(1 : α →ᵇ β)‖ = 1` if `α` is nonempty. -/
instance instNormOneClass [Nonempty α] [One β] [NormOneClass β] : NormOneClass (α →ᵇ β) where
  norm_one := by simp only [norm_eq_iSup_norm, coe_one, Pi.one_apply, norm_one, ciSup_const]

/-- The pointwise opposite of a bounded continuous function is again bounded continuous. -/
instance : Neg (α →ᵇ β) :=
  ⟨fun f =>
    ofNormedAddCommGroup (-f) f.continuous.neg ‖f‖ fun x =>
      norm_neg ((⇑f) x) ▸ f.norm_coe_le_norm x⟩

@[simp]
theorem coe_neg : ⇑(-f) = -f := rfl

theorem neg_apply : (-f) x = -f x := rfl

@[simp]
theorem mkOfCompact_neg [CompactSpace α] (f : C(α, β)) : mkOfCompact (-f) = -mkOfCompact f := rfl

@[simp]
theorem mkOfCompact_sub [CompactSpace α] (f g : C(α, β)) :
    mkOfCompact (f - g) = mkOfCompact f - mkOfCompact g := rfl

@[simp]
theorem coe_zsmulRec : ∀ z, ⇑(zsmulRec (· • ·) z f) = z • ⇑f
  | Int.ofNat n => by rw [zsmulRec, Int.ofNat_eq_coe, coe_nsmul, natCast_zsmul]
  | Int.negSucc n => by rw [zsmulRec, negSucc_zsmul, coe_neg, coe_nsmul]

instance instSMulInt : SMul ℤ (α →ᵇ β) where
  smul n f :=
    { toContinuousMap := n • f.toContinuousMap
      map_bounded' := by simpa using (zsmulRec (· • ·) n f).map_bounded' }

@[simp]
theorem coe_zsmul (r : ℤ) (f : α →ᵇ β) : ⇑(r • f) = r • ⇑f := rfl

@[simp]
theorem zsmul_apply (r : ℤ) (f : α →ᵇ β) (v : α) : (r • f) v = r • f v := rfl

instance instAddCommGroup : AddCommGroup (α →ᵇ β) := fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    fun _ _ => coe_zsmul _ _

instance instSeminormedAddCommGroup : SeminormedAddCommGroup (α →ᵇ β) where
  dist_eq f g := by simp only [norm_eq, dist_eq, dist_eq_norm, sub_apply]

instance instNormedAddCommGroup {α β} [TopologicalSpace α] [NormedAddCommGroup β] :
    NormedAddCommGroup (α →ᵇ β) :=
  { instSeminormedAddCommGroup with
    eq_of_dist_eq_zero }

theorem nnnorm_def : ‖f‖₊ = nndist f 0 := rfl

theorem nnnorm_coe_le_nnnorm (x : α) : ‖f x‖₊ ≤ ‖f‖₊ :=
  norm_coe_le_norm _ _

theorem nndist_le_two_nnnorm (x y : α) : nndist (f x) (f y) ≤ 2 * ‖f‖₊ :=
  dist_le_two_norm _ _ _

/-- The `nnnorm` of a function is controlled by the supremum of the pointwise `nnnorm`s. -/
theorem nnnorm_le (C : ℝ≥0) : ‖f‖₊ ≤ C ↔ ∀ x : α, ‖f x‖₊ ≤ C :=
  norm_le C.prop

theorem nnnorm_const_le (b : β) : ‖const α b‖₊ ≤ ‖b‖₊ :=
  norm_const_le _

@[simp]
theorem nnnorm_const_eq [Nonempty α] (b : β) : ‖const α b‖₊ = ‖b‖₊ :=
  Subtype.ext <| norm_const_eq _

theorem nnnorm_eq_iSup_nnnorm : ‖f‖₊ = ⨆ x : α, ‖f x‖₊ :=
  Subtype.ext <| (norm_eq_iSup_norm f).trans <| by simp_rw [val_eq_coe, NNReal.coe_iSup, coe_nnnorm]

theorem enorm_eq_iSup_enorm : ‖f‖ₑ = ⨆ x, ‖f x‖ₑ := by
  simpa only [← edist_zero_eq_enorm] using edist_eq_iSup

theorem abs_diff_coe_le_dist : ‖f x - g x‖ ≤ dist f g := by
  rw [dist_eq_norm]
  exact (f - g).norm_coe_le_norm x

theorem coe_le_coe_add_dist {f g : α →ᵇ ℝ} : f x ≤ g x + dist f g :=
  sub_le_iff_le_add'.1 <| (abs_le.1 <| @dist_coe_le_dist _ _ _ _ f g x).2

theorem norm_compContinuous_le [TopologicalSpace γ] (f : α →ᵇ β) (g : C(γ, α)) :
    ‖f.compContinuous g‖ ≤ ‖f‖ :=
  ((lipschitz_compContinuous g).dist_le_mul f 0).trans <| by
    rw [NNReal.coe_one, one_mul, dist_zero_right]

end NormedAddCommGroup

section NormedSpace

variable {𝕜 : Type*}
variable [TopologicalSpace α] [SeminormedAddCommGroup β]
variable {f g : α →ᵇ β} {x : α} {C : ℝ}

instance instNormedSpace [NormedField 𝕜] [NormedSpace 𝕜 β] : NormedSpace 𝕜 (α →ᵇ β) :=
  ⟨fun c f => by
    refine norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
    exact fun x =>
      norm_smul c (f x) ▸ mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)⟩

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 β]
variable [SeminormedAddCommGroup γ] [NormedSpace 𝕜 γ]
variable (α)

-- TODO does this work in the `IsBoundedSMul` setting, too?
/-- Postcomposition of bounded continuous functions into a normed module by a continuous linear map
is a continuous linear map.
Upgraded version of `ContinuousLinearMap.compLeftContinuous`, similar to `LinearMap.compLeft`. -/
protected def _root_.ContinuousLinearMap.compLeftContinuousBounded (g : β →L[𝕜] γ) :
    (α →ᵇ β) →L[𝕜] α →ᵇ γ :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        ofNormedAddCommGroup (g ∘ f) (g.continuous.comp f.continuous) (‖g‖ * ‖f‖) fun x =>
          g.le_opNorm_of_le (f.norm_coe_le_norm x)
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp } ‖g‖ fun f =>
        norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg g) (norm_nonneg f))
          (fun x => by exact g.le_opNorm_of_le (f.norm_coe_le_norm x))

@[simp]
theorem _root_.ContinuousLinearMap.compLeftContinuousBounded_apply (g : β →L[𝕜] γ) (f : α →ᵇ β)
    (x : α) : (g.compLeftContinuousBounded α f) x = g (f x) := rfl

end NormedSpace

section NormedRing

variable [TopologicalSpace α] {R : Type*}

section NonUnital

section Seminormed

variable [NonUnitalSeminormedRing R]

instance instNonUnitalRing : NonUnitalRing (α →ᵇ R) := fast_instance%
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) fun _ _ => coe_zsmul _ _

instance instNonUnitalSeminormedRing : NonUnitalSeminormedRing (α →ᵇ R) where
  __ := instSeminormedAddCommGroup
  __ := instNonUnitalRing
  norm_mul_le f g := norm_ofNormedAddCommGroup_le _ (by positivity)
    (fun x ↦ (norm_mul_le _ _).trans <| mul_le_mul
      (norm_coe_le_norm f x) (norm_coe_le_norm g x) (norm_nonneg _) (norm_nonneg _))

end Seminormed

instance instNonUnitalSeminormedCommRing [NonUnitalSeminormedCommRing R] :
    NonUnitalSeminormedCommRing (α →ᵇ R) where
  mul_comm _ _ := ext fun _ ↦ mul_comm ..

instance instNonUnitalNormedRing [NonUnitalNormedRing R] : NonUnitalNormedRing (α →ᵇ R) where
  __ := instNonUnitalSeminormedRing
  __ := instNormedAddCommGroup

instance instNonUnitalNormedCommRing [NonUnitalNormedCommRing R] :
    NonUnitalNormedCommRing (α →ᵇ R) where
  mul_comm := mul_comm

end NonUnital

section Seminormed

variable [SeminormedRing R]

@[simp]
theorem coe_npowRec (f : α →ᵇ R) : ∀ n, ⇑(npowRec n f) = (⇑f) ^ n
  | 0 => by rw [npowRec, pow_zero, coe_one]
  | n + 1 => by rw [npowRec, pow_succ, coe_mul, coe_npowRec f n]

instance hasNatPow : Pow (α →ᵇ R) ℕ where
  pow f n :=
    { toContinuousMap := f.toContinuousMap ^ n
      map_bounded' := by simpa [coe_npowRec] using (npowRec n f).map_bounded' }

instance : NatCast (α →ᵇ R) :=
  ⟨fun n => BoundedContinuousFunction.const _ n⟩

@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : ((n : α →ᵇ R) : α → R) = n := rfl

@[simp, norm_cast]
theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : α →ᵇ R) : α → R) = ofNat(n) :=
  rfl

instance : IntCast (α →ᵇ R) :=
  ⟨fun n => BoundedContinuousFunction.const _ n⟩

@[simp, norm_cast]
theorem coe_intCast (n : ℤ) : ((n : α →ᵇ R) : α → R) = n := rfl

instance instRing : Ring (α →ᵇ R) := fast_instance%
  DFunLike.coe_injective.ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) (fun _ _ => coe_zsmul _ _) (fun _ _ => coe_pow _ _) coe_natCast
    coe_intCast

instance instSeminormedRing : SeminormedRing (α →ᵇ R) where
  __ := instRing
  __ := instNonUnitalSeminormedRing

/-- Composition on the left by a (lipschitz-continuous) homomorphism of topological semirings, as a
`RingHom`. Similar to `RingHom.compLeftContinuous`. -/
@[simps!]
protected def _root_.RingHom.compLeftContinuousBounded (α : Type*)
    [TopologicalSpace α] [SeminormedRing β] [SeminormedRing γ]
    (g : β →+* γ) {C : NNReal} (hg : LipschitzWith C g) : (α →ᵇ β) →+* (α →ᵇ γ) :=
  { g.toMonoidHom.compLeftContinuousBounded α hg,
    g.toAddMonoidHom.compLeftContinuousBounded α hg with }

end Seminormed

instance instNormedRing [NormedRing R] : NormedRing (α →ᵇ R) where
  __ := instRing
  __ := instNonUnitalNormedRing

end NormedRing

section NormedCommRing

variable [TopologicalSpace α] {R : Type*}

instance instCommRing [SeminormedCommRing R] : CommRing (α →ᵇ R) where
  mul_comm _ _ := ext fun _ ↦ mul_comm _ _

instance instSeminormedCommRing [SeminormedCommRing R] : SeminormedCommRing (α →ᵇ R) where
  __ := instCommRing
  __ := instNonUnitalSeminormedRing

instance instNormedCommRing [NormedCommRing R] : NormedCommRing (α →ᵇ R) where
  __ := instSeminormedCommRing
  __ := instNormedAddCommGroup

end NormedCommRing

section NonUnitalAlgebra

-- these hypotheses could be generalized if we generalize `IsBoundedSMul` to `Bornology`.
variable {𝕜 : Type*} [PseudoMetricSpace 𝕜] [TopologicalSpace α] [NonUnitalSeminormedRing β]
variable [Zero 𝕜] [SMul 𝕜 β] [IsBoundedSMul 𝕜 β]

instance [IsScalarTower 𝕜 β β] : IsScalarTower 𝕜 (α →ᵇ β) (α →ᵇ β) where
  smul_assoc _ _ _ := ext fun _ ↦ smul_mul_assoc ..

instance [SMulCommClass 𝕜 β β] : SMulCommClass 𝕜 (α →ᵇ β) (α →ᵇ β) where
  smul_comm _ _ _ := ext fun _ ↦ (mul_smul_comm ..).symm

instance [SMulCommClass 𝕜 β β] : SMulCommClass (α →ᵇ β) 𝕜 (α →ᵇ β) where
  smul_comm _ _ _ := ext fun _ ↦ mul_smul_comm ..

end NonUnitalAlgebra

section NormedAlgebra

variable {𝕜 : Type*} [NormedField 𝕜]
variable [TopologicalSpace α] [SeminormedAddCommGroup β] [NormedSpace 𝕜 β]
variable [NormedRing γ] [NormedAlgebra 𝕜 γ]
variable {f g : α →ᵇ γ} {x : α} {c : 𝕜}

/-- `BoundedContinuousFunction.const` as a `RingHom`. -/
def C : 𝕜 →+* α →ᵇ γ where
  toFun := fun c : 𝕜 => const α ((algebraMap 𝕜 γ) c)
  map_one' := ext fun _ => (algebraMap 𝕜 γ).map_one
  map_mul' _ _ := ext fun _ => (algebraMap 𝕜 γ).map_mul _ _
  map_zero' := ext fun _ => (algebraMap 𝕜 γ).map_zero
  map_add' _ _ := ext fun _ => (algebraMap 𝕜 γ).map_add _ _

instance instAlgebra : Algebra 𝕜 (α →ᵇ γ) where
  algebraMap := C
  commutes' _ _ := ext fun _ ↦ Algebra.commutes' _ _
  smul_def' _ _ := ext fun _ ↦ Algebra.smul_def' _ _

@[simp]
theorem algebraMap_apply (k : 𝕜) (a : α) : algebraMap 𝕜 (α →ᵇ γ) k a = k • (1 : γ) := by
  simp only [Algebra.algebraMap_eq_smul_one, coe_smul, coe_one, Pi.one_apply]

instance instNormedAlgebra : NormedAlgebra 𝕜 (α →ᵇ γ) where
  __ := instAlgebra
  __ := instNormedSpace

variable (𝕜)

/-- Composition on the left by a (lipschitz-continuous) homomorphism of topological `R`-algebras,
as an `AlgHom`. Similar to `AlgHom.compLeftContinuous`. -/
@[simps!]
protected def AlgHom.compLeftContinuousBounded
    [NormedRing β] [NormedAlgebra 𝕜 β] [NormedRing γ] [NormedAlgebra 𝕜 γ]
    (g : β →ₐ[𝕜] γ) {C : NNReal} (hg : LipschitzWith C g) : (α →ᵇ β) →ₐ[𝕜] (α →ᵇ γ) :=
  { g.toRingHom.compLeftContinuousBounded α hg with
    commutes' := fun _ => DFunLike.ext _ _ fun _ => g.commutes' _ }

/-- The algebra-homomorphism forgetting that a bounded continuous function is bounded. -/
@[simps]
def toContinuousMapₐ : (α →ᵇ γ) →ₐ[𝕜] C(α, γ) where
  toFun := (↑)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem coe_toContinuousMapₐ (f : α →ᵇ γ) : (f.toContinuousMapₐ 𝕜 : α → γ) = f := rfl

variable {𝕜}

/-! ### Structure as normed module over scalar functions

If `β` is a normed `𝕜`-space, then we show that the space of bounded continuous
functions from `α` to `β` is naturally a module over the algebra of bounded continuous
functions from `α` to `𝕜`. -/

instance instSMul' : SMul (α →ᵇ 𝕜) (α →ᵇ β) where
  smul f g :=
    ofNormedAddCommGroup (fun x => f x • g x) (f.continuous.smul g.continuous) (‖f‖ * ‖g‖) fun x =>
      calc
        ‖f x • g x‖ ≤ ‖f x‖ * ‖g x‖ := norm_smul_le _ _
        _ ≤ ‖f‖ * ‖g‖ :=
          mul_le_mul (f.norm_coe_le_norm _) (g.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)

instance instModule' : Module (α →ᵇ 𝕜) (α →ᵇ β) :=
  Module.ofMinimalAxioms
      (fun c _ _ => ext fun a => smul_add (c a) _ _)
      (fun _ _ _ => ext fun _ => add_smul _ _ _)
      (fun _ _ _ => ext fun _ => mul_smul _ _ _)
      (fun f => ext fun x => one_smul 𝕜 (f x))

/- TODO: When `NormedModule` has been added to `Analysis.Normed.Module.Basic`, this
shows that the space of bounded continuous functions from `α` to `β` is naturally a normed
module over the algebra of bounded continuous functions from `α` to `𝕜`. -/
instance : IsBoundedSMul (α →ᵇ 𝕜) (α →ᵇ β) :=
  IsBoundedSMul.of_norm_smul_le fun _ _ =>
    norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _

end NormedAlgebra

section NormedLatticeOrderedGroup

variable [TopologicalSpace α]
  [NormedAddCommGroup β] [Lattice β] [HasSolidNorm β] [IsOrderedAddMonoid β]

instance instPartialOrder : PartialOrder (α →ᵇ β) :=
  PartialOrder.lift (fun f => f.toFun) (by simp [Injective])

instance instSup : Max (α →ᵇ β) where
  max f g :=
    { toFun := f ⊔ g
      continuous_toFun := f.continuous.sup g.continuous
      map_bounded' := by
        obtain ⟨C₁, hf⟩ := f.bounded
        obtain ⟨C₂, hg⟩ := g.bounded
        refine ⟨C₁ + C₂, fun x y ↦ ?_⟩
        simp_rw [dist_eq_norm_sub] at hf hg ⊢
        exact (norm_sup_sub_sup_le_add_norm _ _ _ _).trans (add_le_add (hf _ _) (hg _ _)) }

instance instInf : Min (α →ᵇ β) where
  min f g :=
    { toFun := f ⊓ g
      continuous_toFun := f.continuous.inf g.continuous
      map_bounded' := by
        obtain ⟨C₁, hf⟩ := f.bounded
        obtain ⟨C₂, hg⟩ := g.bounded
        refine ⟨C₁ + C₂, fun x y ↦ ?_⟩
        simp_rw [dist_eq_norm_sub] at hf hg ⊢
        exact (norm_inf_sub_inf_le_add_norm _ _ _ _).trans (add_le_add (hf _ _) (hg _ _)) }

@[simp, norm_cast] lemma coe_sup (f g : α →ᵇ β) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g := rfl

@[simp, norm_cast] lemma coe_inf (f g : α →ᵇ β) : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g := rfl

instance instSemilatticeSup : SemilatticeSup (α →ᵇ β) := fast_instance%
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

instance instSemilatticeInf : SemilatticeInf (α →ᵇ β) := fast_instance%
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

instance instLattice : Lattice (α →ᵇ β) := fast_instance%
  DFunLike.coe_injective.lattice _ .rfl .rfl coe_sup coe_inf

@[simp, norm_cast] lemma coe_abs (f : α →ᵇ β) : ⇑|f| = |⇑f| := rfl
@[simp, norm_cast] lemma coe_posPart (f : α →ᵇ β) : ⇑f⁺ = (⇑f)⁺ := rfl
@[simp, norm_cast] lemma coe_negPart (f : α →ᵇ β) : ⇑f⁻ = (⇑f)⁻ := rfl

instance instHasSolidNorm : HasSolidNorm (α →ᵇ β) :=
  { solid := by
      intro f g h
      have i1 : ∀ t, ‖f t‖ ≤ ‖g t‖ := fun t => HasSolidNorm.solid (h t)
      rw [norm_le (norm_nonneg _)]
      exact fun t => (i1 t).trans (norm_coe_le_norm g t) }

instance instIsOrderedAddMonoid : IsOrderedAddMonoid (α →ᵇ β) where
  add_le_add_left f g h₁ h t := by simpa using h₁ _

end NormedLatticeOrderedGroup

section NonnegativePart

variable [TopologicalSpace α]

/-- The nonnegative part of a bounded continuous `ℝ`-valued function as a bounded
continuous `ℝ≥0`-valued function. -/
def nnrealPart (f : α →ᵇ ℝ) : α →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.comp _ (show LipschitzWith 1 Real.toNNReal from lipschitzWith_posPart) f

@[simp]
theorem nnrealPart_coeFn_eq (f : α →ᵇ ℝ) : ⇑f.nnrealPart = Real.toNNReal ∘ ⇑f := rfl

/-- The absolute value of a bounded continuous `ℝ`-valued function as a bounded
continuous `ℝ≥0`-valued function. -/
def nnnorm (f : α →ᵇ ℝ) : α →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.comp _
    (show LipschitzWith 1 fun x : ℝ => ‖x‖₊ from lipschitzWith_one_norm) f

@[simp]
theorem nnnorm_coeFn_eq (f : α →ᵇ ℝ) : ⇑f.nnnorm = NNNorm.nnnorm ∘ ⇑f := rfl

-- TODO: Use `posPart` and `negPart` here
/-- Decompose a bounded continuous function to its positive and negative parts. -/
theorem self_eq_nnrealPart_sub_nnrealPart_neg (f : α →ᵇ ℝ) :
    ⇑f = (↑) ∘ f.nnrealPart - (↑) ∘ (-f).nnrealPart := by
  funext x
  dsimp
  simp only [max_zero_sub_max_neg_zero_eq_self]

/-- Express the absolute value of a bounded continuous function in terms of its
positive and negative parts. -/
theorem abs_self_eq_nnrealPart_add_nnrealPart_neg (f : α →ᵇ ℝ) :
    abs ∘ ⇑f = (↑) ∘ f.nnrealPart + (↑) ∘ (-f).nnrealPart := by
  funext x
  dsimp
  simp only [max_zero_add_max_neg_zero_eq_abs_self]

end NonnegativePart

section

variable {α : Type*} [TopologicalSpace α]

-- TODO: `f + const _ ‖f‖` is just `f⁺`
lemma add_norm_nonneg (f : α →ᵇ ℝ) :
    0 ≤ f + const _ ‖f‖ := by
  intro x
  simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, coe_zero, Pi.zero_apply, coe_add,
    const_apply, Pi.add_apply]
  linarith [(abs_le.mp (norm_coe_le_norm f x)).1]

lemma norm_sub_nonneg (f : α →ᵇ ℝ) :
    0 ≤ const _ ‖f‖ - f := by
  intro x
  simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, coe_zero, Pi.zero_apply, coe_sub,
    const_apply, Pi.sub_apply, sub_nonneg]
  linarith [(abs_le.mp (norm_coe_le_norm f x)).2]

end

end BoundedContinuousFunction
