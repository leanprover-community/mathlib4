/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.ContinuousMap.Ideals
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Gelfand Duality

The `gelfandTransform` is an algebra homomorphism from a topological `𝕜`-algebra `A` to
`C(characterSpace 𝕜 A, 𝕜)`. In the case where `A` is a commutative complex Banach algebra, then
the Gelfand transform is actually spectrum-preserving (`spectrum.gelfandTransform_eq`). Moreover,
when `A` is a commutative C⋆-algebra over `ℂ`, then the Gelfand transform is a surjective isometry,
and even an equivalence between C⋆-algebras.

Consider the contravariant functors between compact Hausdorff spaces and commutative unital
C⋆algebras `F : Cpct → CommCStarAlg := X ↦ C(X, ℂ)` and
`G : CommCStarAlg → Cpct := A → characterSpace ℂ A` whose actions on morphisms are given by
`WeakDual.CharacterSpace.compContinuousMap` and `ContinuousMap.compStarAlgHom'`, respectively.

Then `η₁ : id → F ∘ G := gelfandStarTransform` and
`η₂ : id → G ∘ F := WeakDual.CharacterSpace.homeoEval` are the natural isomorphisms implementing
**Gelfand Duality**, i.e., the (contravariant) equivalence of these categories.

## Main definitions

* `Ideal.toCharacterSpace` : constructs an element of the character space from a maximal ideal in
  a commutative complex Banach algebra
* `WeakDual.CharacterSpace.compContinuousMap`: The functorial map taking `ψ : A →⋆ₐ[𝕜] B` to a
  continuous function `characterSpace 𝕜 B → characterSpace 𝕜 A` given by pre-composition with `ψ`.

## Main statements

* `spectrum.gelfandTransform_eq` : the Gelfand transform is spectrum-preserving when the algebra is
  a commutative complex Banach algebra.
* `gelfandTransform_isometry` : the Gelfand transform is an isometry when the algebra is a
  commutative (unital) C⋆-algebra over `ℂ`.
* `gelfandTransform_bijective` : the Gelfand transform is bijective when the algebra is a
  commutative (unital) C⋆-algebra over `ℂ`.
* `gelfandStarTransform_naturality`: The `gelfandStarTransform` is a natural isomorphism
* `WeakDual.CharacterSpace.homeoEval_naturality`: This map implements a natural isomorphism

## TODO

* After defining the category of commutative unital C⋆-algebras, bundle the existing unbundled
  **Gelfand duality** into an actual equivalence (duality) of categories associated to the
  functors `C(·, ℂ)` and `characterSpace ℂ ·` and the natural isomorphisms `gelfandStarTransform`
  and `WeakDual.CharacterSpace.homeoEval`.

## Tags

Gelfand transform, character space, C⋆-algebra
-/

@[expose] public section


open WeakDual

open scoped NNReal

section ComplexBanachAlgebra

open Ideal

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (I : Ideal A)
  [Ideal.IsMaximal I]

/-- Every maximal ideal in a commutative complex Banach algebra gives rise to a character on that
algebra. In particular, the character, which may be identified as an algebra homomorphism due to
`WeakDual.CharacterSpace.equivAlgHom`, is given by the composition of the quotient map and
the Gelfand-Mazur isomorphism `NormedRing.algEquivComplexOfComplete`. -/
noncomputable def Ideal.toCharacterSpace : characterSpace ℂ A :=
  CharacterSpace.equivAlgHom.symm <|
    ((NormedRing.algEquivComplexOfComplete
      (letI := Quotient.field I; isUnit_iff_ne_zero (G₀ := A ⧸ I))).symm : A ⧸ I →ₐ[ℂ] ℂ).comp <|
    Quotient.mkₐ ℂ I

set_option backward.isDefEq.respectTransparency false in
theorem Ideal.toCharacterSpace_apply_eq_zero_of_mem {a : A} (ha : a ∈ I) :
    I.toCharacterSpace a = 0 := by
  unfold Ideal.toCharacterSpace
  simp only [CharacterSpace.equivAlgHom_symm_coe, AlgHom.coe_comp, AlgHom.coe_coe,
    Quotient.mkₐ_eq_mk, Function.comp_apply, NormedRing.algEquivComplexOfComplete_symm_apply]
  simp_rw [Quotient.eq_zero_iff_mem.mpr ha, spectrum.zero_eq]
  exact Set.eq_of_mem_singleton (Set.singleton_nonempty (0 : ℂ)).some_mem

/-- If `a : A` is not a unit, then some character takes the value zero at `a`. This is equivalent
to `gelfandTransform ℂ A a` takes the value zero at some character. -/
theorem WeakDual.CharacterSpace.exists_apply_eq_zero {a : A} (ha : ¬IsUnit a) :
    ∃ f : characterSpace ℂ A, f a = 0 := by
  obtain ⟨M, hM, haM⟩ := (span {a}).exists_le_maximal (span_singleton_ne_top ha)
  exact
    ⟨M.toCharacterSpace,
      M.toCharacterSpace_apply_eq_zero_of_mem
        (haM (mem_span_singleton.mpr ⟨1, (mul_one a).symm⟩))⟩

theorem WeakDual.CharacterSpace.mem_spectrum_iff_exists {a : A} {z : ℂ} :
    z ∈ spectrum ℂ a ↔ ∃ f : characterSpace ℂ A, f a = z := by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨f, hf⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero hz
    simp only [map_sub, sub_eq_zero, AlgHomClass.commutes] at hf
    exact ⟨_, hf.symm⟩
  · rintro ⟨f, rfl⟩
    exact AlgHom.apply_mem_spectrum f a

/-- The Gelfand transform is spectrum-preserving. -/
theorem spectrum.gelfandTransform_eq (a : A) :
    spectrum ℂ (gelfandTransform ℂ A a) = spectrum ℂ a := by
  ext z
  rw [ContinuousMap.spectrum_eq_range, WeakDual.CharacterSpace.mem_spectrum_iff_exists]
  exact Iff.rfl

instance [Nontrivial A] : Nonempty (characterSpace ℂ A) :=
  ⟨Classical.choose <|
      WeakDual.CharacterSpace.exists_apply_eq_zero <| zero_mem_nonunits.2 zero_ne_one⟩

end ComplexBanachAlgebra

section ComplexCStarAlgebra

variable {A : Type*} [CommCStarAlgebra A]

theorem gelfandTransform_map_star (a : A) :
    gelfandTransform ℂ A (star a) = star (gelfandTransform ℂ A a) :=
  ContinuousMap.ext fun φ => map_star φ a

variable (A)

/-- The Gelfand transform is an isometry when the algebra is a C⋆-algebra over `ℂ`. -/
theorem gelfandTransform_isometry : Isometry (gelfandTransform ℂ A) := by
  refine AddMonoidHomClass.isometry_of_norm (gelfandTransform ℂ A) fun a => ?_
  /- By `spectrum.gelfandTransform_eq`, the spectra of `star a * a` and its
    `gelfandTransform` coincide. Therefore, so do their spectral radii, and since they are
    self-adjoint, so also do their norms. Applying the C⋆-property of the norm and taking square
    roots shows that the norm is preserved. -/
  have : spectralRadius ℂ (gelfandTransform ℂ A (star a * a)) = spectralRadius ℂ (star a * a) := by
    unfold spectralRadius; rw [spectrum.gelfandTransform_eq]
  rw [map_mul, (IsSelfAdjoint.star_mul_self a).spectralRadius_eq_nnnorm, gelfandTransform_map_star,
    (IsSelfAdjoint.star_mul_self (gelfandTransform ℂ A a)).spectralRadius_eq_nnnorm] at this
  simp only [ENNReal.coe_inj, CStarRing.nnnorm_star_mul_self, ← sq] at this
  simpa only [Function.comp_apply, NNReal.sqrt_sq] using
    congr_arg (((↑) : ℝ≥0 → ℝ) ∘ ⇑NNReal.sqrt) this

set_option backward.isDefEq.respectTransparency false in
/-- The Gelfand transform is bijective when the algebra is a C⋆-algebra over `ℂ`. -/
theorem gelfandTransform_bijective : Function.Bijective (gelfandTransform ℂ A) := by
  refine ⟨(gelfandTransform_isometry A).injective, ?_⟩
  /- The range of `gelfandTransform ℂ A` is actually a `StarSubalgebra`. The key lemma below may be
    hard to spot; it's `map_star` coming from `WeakDual.Complex.instStarHomClass`, which is a
    nontrivial result. -/
  let rng : StarSubalgebra ℂ C(characterSpace ℂ A, ℂ) :=
    { toSubalgebra := (gelfandTransform ℂ A).range
      star_mem' := by
        rintro - ⟨a, rfl⟩
        use star a
        ext1 φ
        dsimp
        simp only [map_star, RCLike.star_def] }
  suffices rng = ⊤ from
    fun x => show x ∈ rng from this.symm ▸ StarSubalgebra.mem_top
  /- Because the `gelfandTransform ℂ A` is an isometry, it has closed range, and so by the
    Stone-Weierstrass theorem, it suffices to show that the image of the Gelfand transform separates
    points in `C(characterSpace ℂ A, ℂ)` and is closed under `star`. -/
  have h : rng.topologicalClosure = rng := le_antisymm
    (StarSubalgebra.topologicalClosure_minimal le_rfl
      (gelfandTransform_isometry A).isClosedEmbedding.isClosed_range)
    (StarSubalgebra.le_topologicalClosure _)
  refine h ▸ ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    _ (fun _ _ => ?_)
  /- Separating points just means that elements of the `characterSpace` which agree at all points
    of `A` are the same functional, which is just extensionality. -/
  contrapose!
  exact fun h => Subtype.ext (ContinuousLinearMap.ext fun a =>
    h (gelfandTransform ℂ A a) ⟨gelfandTransform ℂ A a, ⟨a, rfl⟩, rfl⟩)

/-- The Gelfand transform as a `StarAlgEquiv` between a commutative unital C⋆-algebra over `ℂ`
and the continuous functions on its `characterSpace`. -/
@[simps!]
noncomputable def gelfandStarTransform : A ≃⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ) :=
  StarAlgEquiv.ofBijective
    (show A →⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ) from
      { gelfandTransform ℂ A with map_star' := fun x => gelfandTransform_map_star x })
    (gelfandTransform_bijective A)

end ComplexCStarAlgebra


section NonUnitalCStarAlgebra

section Functions

variable {X R : Type*} [TopologicalSpace X] [NormedRing R] [IsDomain R]

-- A better way to do this would be to prove that the norm of a bounded
-- continuous function agrees with the norm of the real-valued function where
-- you compose pointwise with the norm. That should simplify the argument a
-- bit I think, at the cost of developing more API (which is probably worthwhile).

open BoundedContinuousFunction in
/-- If the product of bounded continuous functions is zero, then the norm of their sum is the
maximum of their norms. -/
lemma BoundedContinuousFunction.norm_add_eq_max {f g : X →ᵇ R} (h : f * g = 0) :
    ‖f + g‖ = max ‖f‖ ‖g‖ := by
  have hfg : ∀ x, f x = 0 ∨ g x = 0 := by
    simpa [DFunLike.ext_iff, mul_eq_zero] using h
  have hfg' (x : X) : ‖(f + g) x‖ = max ‖f x‖ ‖g x‖ := by
    obtain (h | h) := hfg x <;> simp [h]
  apply le_antisymm
  · rw [norm_le (by positivity)]
    intro x
    rw [hfg']
    apply max_le <;> exact norm_coe_le_norm _ x |>.trans (by simp)
  · apply max_le
    all_goals
      rw [norm_le (by positivity)]
      intro x
      grw [← (f + g).norm_coe_le_norm x, hfg']
      simp

open BoundedContinuousFunction in
lemma ContinuousMap.norm_add_eq_max [CompactSpace X] {f g : C(X, R)} (h : f * g = 0) :
    ‖f + g‖ = max ‖f‖ ‖g‖ := by
  replace h : mkOfCompact f * mkOfCompact g = 0 := by ext x; simpa using congr($h x)
  simpa using BoundedContinuousFunction.norm_add_eq_max h

end Functions

variable {A : Type*} [NonUnitalCommCStarAlgebra A]

open scoped CStarAlgebra in
open Unitization in
lemma CommCStarAlgebra.norm_add_eq {A : Type*} [NonUnitalCommCStarAlgebra A]
    {a b : A} (h : a * b = 0) : ‖a + b‖ = max ‖a‖ ‖b‖ := by
  let f := gelfandStarTransform A⁺¹ ∘ inrNonUnitalStarAlgHom ℂ A
  have hf : Isometry f := gelfandTransform_isometry _ |>.comp isometry_inr
  have h0 : f 0 = 0 := by simp [f]
  simp_rw [← hf.norm_map_of_map_zero h0, show f (a + b) = f a + f b by simp [f]]
  exact ContinuousMap.norm_add_eq_max <| by simpa [f] using congr(f $h)

open NonUnitalStarAlgebra in
lemma IsSelfAdjoint.norm_add_eq {A : Type*} [NonUnitalCStarAlgebra A]
    {a b : A} (hab : a * b = 0) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    ‖a + b‖ = max ‖a‖ ‖b‖ := by
  let S : NonUnitalStarSubalgebra ℂ A := (adjoin ℂ {a, b}).topologicalClosure
  have hS : IsClosed (S : Set A) := (adjoin ℂ {a, b}).isClosed_topologicalClosure
  have hab' : a * b = b * a := by
    rw [hab, eq_comm]; simpa [ha.star_eq, hb.star_eq] using congr(star $hab)
  let _ : NonUnitalCommRing (adjoin ℂ {a, b}) :=
    adjoinNonUnitalCommRingOfComm ℂ (by grind) (by grind [IsSelfAdjoint.star_eq])
  let _ : NonUnitalCommRing S := (adjoin ℂ {a, b}).nonUnitalCommRingTopologicalClosure mul_comm
  let _ : NonUnitalCommCStarAlgebra S := { }
  let c : S := ⟨a, subset_closure <| subset_adjoin _ _ <| by grind⟩
  let d : S := ⟨b, subset_closure <| subset_adjoin _ _ <| by grind⟩
  exact CommCStarAlgebra.norm_add_eq (a := c) (b := d) (h := by ext; simpa)

#check IsMulCommutative

/-- The element of `WeakDual.characterSpace` on `Unitization 𝕜 A` corresponding to the
algebra homomorphism consisting of projection onto the scalar part.

When `A` is a C⋆-algebra composing the inclusion map `A → A⁺¹` with the Gelfand transform
`A⁺¹ → C(characterSpace ℂ A⁺¹, ℂ)`, is an injective non-unital star homomorphism whose range is
precisely kernel of the evaluation map at this point. -/
noncomputable def CharacterSpace.pt {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NonUnitalNormedRing A] [CompleteSpace A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [RegularNormedAlgebra 𝕜 A] :
    characterSpace 𝕜 (Unitization 𝕜 A) :=
  CharacterSpace.equivAlgHom.symm <| Unitization.fstHom 𝕜 A

open CStarAlgebra Unitization in
example {A : Type*} [NonUnitalCommCStarAlgebra A] : False := by
  let g := gelfandStarTransform A⁺¹
  let i := inrNonUnitalStarAlgHom ℂ A


  sorry

end NonUnitalCStarAlgebra

#exit
section Functoriality

namespace WeakDual

namespace CharacterSpace

variable {A B C 𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [StarRing A]
variable [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B] [StarRing B]
variable [NormedRing C] [NormedAlgebra 𝕜 C] [CompleteSpace C] [StarRing C]

/-- The functorial map taking `ψ : A →⋆ₐ[ℂ] B` to a continuous function
`characterSpace ℂ B → characterSpace ℂ A` obtained by pre-composition with `ψ`. -/
@[simps]
noncomputable def compContinuousMap (ψ : A →⋆ₐ[𝕜] B) :
    C(characterSpace 𝕜 B, characterSpace 𝕜 A) where
  toFun φ := equivAlgHom.symm ((equivAlgHom φ).comp ψ.toAlgHom)
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_of_continuous_eval fun a => map_continuous <| gelfandTransform 𝕜 B (ψ a)) _

variable (A) in
/-- `WeakDual.CharacterSpace.compContinuousMap` sends the identity to the identity. -/
@[simp]
theorem compContinuousMap_id :
    compContinuousMap (StarAlgHom.id 𝕜 A) = ContinuousMap.id (characterSpace 𝕜 A) :=
  ContinuousMap.ext fun _a => ext fun _x => rfl

/-- `WeakDual.CharacterSpace.compContinuousMap` is functorial. -/
@[simp]
theorem compContinuousMap_comp (ψ₂ : B →⋆ₐ[𝕜] C) (ψ₁ : A →⋆ₐ[𝕜] B) :
    compContinuousMap (ψ₂.comp ψ₁) = (compContinuousMap ψ₁).comp (compContinuousMap ψ₂) :=
  ContinuousMap.ext fun _a => ext fun _x => rfl

end CharacterSpace

end WeakDual

end Functoriality

open CharacterSpace in
/--
Consider the contravariant functors between compact Hausdorff spaces and commutative unital
C⋆algebras `F : Cpct → CommCStarAlg := X ↦ C(X, ℂ)` and
`G : CommCStarAlg → Cpct := A → characterSpace ℂ A` whose actions on morphisms are given by
`WeakDual.CharacterSpace.compContinuousMap` and `ContinuousMap.compStarAlgHom'`, respectively.

Then `η : id → F ∘ G := gelfandStarTransform` is a natural isomorphism implementing (half of)
the duality between these categories. That is, for commutative unital C⋆-algebras `A` and `B` and
`φ : A →⋆ₐ[ℂ] B` the following diagram commutes:

```
A  --- η A ---> C(characterSpace ℂ A, ℂ)

|                     |

φ                  (F ∘ G) φ

|                     |
V                     V

B  --- η B ---> C(characterSpace ℂ B, ℂ)
```
-/
theorem gelfandStarTransform_naturality {A B : Type*} [CommCStarAlgebra A] [CommCStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) :
    (gelfandStarTransform B : _ →⋆ₐ[ℂ] _).comp φ =
      (compContinuousMap φ |>.compStarAlgHom' ℂ ℂ).comp (gelfandStarTransform A : _ →⋆ₐ[ℂ] _) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Consider the contravariant functors between compact Hausdorff spaces and commutative unital
C⋆algebras `F : Cpct → CommCStarAlg := X ↦ C(X, ℂ)` and
`G : CommCStarAlg → Cpct := A → characterSpace ℂ A` whose actions on morphisms are given by
`WeakDual.CharacterSpace.compContinuousMap` and `ContinuousMap.compStarAlgHom'`, respectively.

Then `η : id → G ∘ F := WeakDual.CharacterSpace.homeoEval` is a natural isomorphism implementing
(half of) the duality between these categories. That is, for compact Hausdorff spaces `X` and `Y`,
`f : C(X, Y)` the following diagram commutes:

```
X  --- η X ---> characterSpace ℂ C(X, ℂ)

|                     |

f                  (G ∘ F) f

|                     |
V                     V

Y  --- η Y ---> characterSpace ℂ C(Y, ℂ)
```
-/
lemma WeakDual.CharacterSpace.homeoEval_naturality {X Y 𝕜 : Type*} [RCLike 𝕜] [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (f : C(X, Y)) :
    (homeoEval Y 𝕜 : C(_, _)).comp f =
      (f.compStarAlgHom' 𝕜 𝕜 |> compContinuousMap).comp (homeoEval X 𝕜 : C(_, _)) :=
  rfl
