/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Dominic Steinitz
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! ## Existence of a Riemannian bundle metric

Using a partition of unity, we prove the existence of a smooth Riemannian metric.

The idea is that there are two equivalent ways of defining a bilinear positive definite form:

  1) pull back the inner product on ℝ^n via the inverse trivialisation
  2) push forward vectors and then apply the inner product on ℝ^n

It turns out that using (1) makes proving smoothness straightforward and
`g_bilin_smooth_on_chart` proves that locally `g_bilini` is smooth (the trick is to make
the set on which this is true small enough hence the intersection:
`((trivializationAt F E i).baseSet ∩ (chartAt HB i).source)`).
This can then be used to prove global smoothness via a partition of unity.

However it is not so clear (to me at any rate) how one uses (1) to prove positive definiteness.
This is where (2) comes in. With this definition, it is straightforward to prove
positivity, definiteness and symmetry.

We then prove that the two definitions are equal which allows me to prove that (1) is symmetric,
positive and definite.

But one is still not done. Mathlib's definition requires von Neumann boundedness
which is true for finite dimensional manifolds.

-/

open Set Bundle ContDiff Manifold Trivialization SmoothPartitionOfUnity

variable {B : Type*}
  {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)]

section tangentSpaceEquiv

variable [∀ x, NormedSpace ℝ (E x)]

/-- `VectorSpaceAux x φ hpos hsymm hdef` is a copy of the fiber `E x` equipped with the norm
induced by the positive definite bilinear form `φ`.

Mathlib's type class system doesn't support having multiple norm structures on the same type.

As the Mathlib documentation states (`Mathlib.Analysis.Normed.Module.FiniteDimension`):
> "The fact that all norms are equivalent is not written explicitly, as it would mean having
> two norms on a single space, which is not the way type classes work. However, if one has a
> finite-dimensional vector space `E` with a norm, and a copy `E'` of this type with another
> norm, then the identities from `E` to `E'` and from `E'` to `E` are continuous thanks to
> `LinearMap.continuous_of_finiteDimensional`. This gives the desired norm equivalence."
> (https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Module/FiniteDimension.html)

It is well known that all norms on a finite-dimensional space are equivalent.
In Mathlib, making this work requires explicit construction and proof. -/
structure VectorSpaceAux
  (x : B) (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) where
  val : E x

lemma VectorSpaceAux.ext_iff {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
    (u v : VectorSpaceAux x φ hpos hsymm hdef) :
  u = v ↔ u.val = (v.val : E x) := by
  cases u; cases v; simp

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Zero (VectorSpaceAux x φ hpos hsymm hdef) where
  zero := ⟨0⟩

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Add (VectorSpaceAux x φ hpos hsymm hdef) where
  add u v := ⟨u.val + v.val⟩

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Neg (VectorSpaceAux x φ hpos hsymm hdef) where
  neg u := ⟨-u.val⟩

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Sub (VectorSpaceAux x φ hpos hsymm hdef) where
  sub u v := ⟨u.val - v.val⟩

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  SMul ℝ (VectorSpaceAux x φ hpos hsymm hdef) where
  smul a u := ⟨a • u.val⟩

noncomputable def seminormOfBilinearForm {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ)
    (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
  Seminorm ℝ (E x) where
  toFun v := Real.sqrt (φ v v)
  map_zero' := by simp
  add_le' r s := by
    rw [Real.sqrt_le_iff]
    · have h0 : ((φ r) s) * ((φ s) r) ≤ ((φ r) r) * ((φ s) s) :=
        LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le φ.toLinearMap₁₂ hpos r s
      have h1 : φ (r + s) (r + s) ≤ (Real.sqrt ((φ r) r) + Real.sqrt ((φ s) s)) ^ 2 := by
        calc φ (r + s) (r + s)
          = (φ r) r + (φ r) s + (φ s) r + (φ s) s := by
              simp only [map_add, ContinuousLinearMap.add_apply]
              ring
        _ = (φ r) r + 2 * (φ r) s + (φ s) s := by
              rw [hsymm r s]
              ring
        _ ≤ (φ r) r + 2 * √((φ r) r * (φ s) s) + (φ s) s := by
              gcongr
              have h2 : ((φ r) s) ^ 2 ≤ ((φ r) r * (φ s) s) := by
                have : ((φ r) s) ^ 2 = (φ r) s * (φ s) r := by rw [sq, hsymm r s]
                linarith [h0]
              exact Real.le_sqrt_of_sq_le h2
        _ = (√((φ r) r) + √((φ s) s)) ^ 2 := by
                rw [add_sq, Real.sq_sqrt (hpos r), Real.sq_sqrt (hpos s),
                    Real.sqrt_mul (hpos r) ((φ s) s)]
                ring
      exact ⟨by positivity, h1⟩
  neg' r := by simp
  smul' a v := by simp [← mul_assoc, ← Real.sqrt_mul_self_eq_abs, Real.sqrt_mul (mul_self_nonneg a)]

noncomputable instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Norm (VectorSpaceAux x φ hpos hsymm hdef) where
  norm v := seminormOfBilinearForm φ hpos hsymm v.val

lemma seminormOfBilinearForm_sub_self {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
    (v : VectorSpaceAux x φ hpos hsymm hdef) :
  seminormOfBilinearForm φ hpos hsymm (v.val - v.val) = 0 := by
  unfold seminormOfBilinearForm
  simp

lemma seminormOfBilinearForm_sub_comm {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
    (u v : VectorSpaceAux x φ hpos hsymm hdef) :
    seminormOfBilinearForm φ hpos hsymm (u.val - v.val) =
    seminormOfBilinearForm φ hpos hsymm (v.val - u.val) := by
  change √((φ (u.val - v.val)) (u.val - v.val)) = √((φ (v.val - u.val)) (v.val - u.val))
  simp only [map_sub, ContinuousLinearMap.coe_sub', Pi.sub_apply]
  ring_nf

lemma my_eq_of_dist_eq_zero {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
    {u v : VectorSpaceAux x φ hpos hsymm hdef} :
    (seminormOfBilinearForm φ hpos hsymm) (u.val - v.val) = 0 → u = v := by
    intro h
    rw [seminormOfBilinearForm] at h
    have h1 : u.val - v.val = 0 := hdef (u.val - v.val)
      ((Real.sqrt_eq_zero (hpos (u.val - v.val))).mp h)
    apply (VectorSpaceAux.ext_iff φ hpos hsymm hdef u v).mpr
    exact sub_eq_zero.mp h1

lemma my_dist_triangle {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  ∀ (x_1 y z : VectorSpaceAux x φ hpos hsymm hdef),
    (seminormOfBilinearForm φ hpos hsymm) (x_1.val - z.val) ≤
      (seminormOfBilinearForm φ hpos hsymm) (x_1.val - y.val) +
      (seminormOfBilinearForm φ hpos hsymm) (y.val - z.val) := by
  intro u v w
  simpa [sub_add_sub_cancel] using
    (seminormOfBilinearForm φ hpos hsymm).add_le' (u.val - v.val) (v.val - w.val)

noncomputable instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  NormedAddCommGroup (VectorSpaceAux x φ hpos hsymm hdef) where
  norm v := seminormOfBilinearForm φ hpos hsymm v.val
  dist_eq := by
    intros x y
    simp only [Neg.neg, Add.add, HAdd.hAdd]
    have : Add.add (-x.val) y.val = y.val - x.val := by
      rw [Add.add_eq_hAdd]
      exact neg_add_eq_sub x.val y.val
    rw [show Add.add (-x.val) y.val = y.val - x.val from this]
    exact seminormOfBilinearForm_sub_comm φ hpos hsymm hdef x y
  add_assoc u v w := VectorSpaceAux.ext_iff _ _ _ _ _ _|>.mpr (add_assoc u.val v.val w.val)
  zero_add u := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (zero_add u.val)
  add_zero u := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (add_zero u.val)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel u := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (neg_add_cancel u.val)
  add_comm u v := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (add_comm u.val v.val)
  sub_eq_add_neg u v := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (sub_eq_add_neg u.val v.val)
  dist_self := seminormOfBilinearForm_sub_self φ hpos hsymm hdef
  dist_comm := seminormOfBilinearForm_sub_comm φ hpos hsymm hdef
  dist_triangle := my_dist_triangle φ hpos hsymm hdef
  eq_of_dist_eq_zero := my_eq_of_dist_eq_zero φ hpos hsymm hdef

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Module ℝ (VectorSpaceAux x φ hpos hsymm hdef) where
  one_smul u := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (one_smul ℝ u.val)
  mul_smul a b u := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (mul_smul a b u.val)
  smul_add a u v := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (smul_add a u.val v.val)
  smul_zero a := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (smul_zero a)
  zero_smul u := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (zero_smul ℝ u.val)
  add_smul a b u := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (add_smul a b u.val)

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  NormedSpace ℝ (VectorSpaceAux x φ hpos hsymm hdef) where
  norm_smul_le := by
    intro a u
    have h1 : (φ (a • u.val)) (a • u.val) = a * (φ u.val) (a • u.val) := by
      rw [φ.map_smul a u.val]
      rfl
    have h2 : (φ u.val) (a • u.val) = a * (φ u.val u.val) :=
      (φ u.val).map_smul a u.val
    have h3 : φ (a • u.val) (a • u.val) = a * a * φ u.val u.val := by grind
    apply le_of_eq
    change Real.sqrt (φ (a • u.val) (a • u.val)) = |a| * Real.sqrt (φ u.val u.val)
    rw [h3, Real.sqrt_mul' (a * a) (hpos u.val), Real.sqrt_mul_self_eq_abs a]

def tangentSpaceEquiv {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  E x ≃ₗ[ℝ] VectorSpaceAux x φ hpos hsymm hdef where
  toFun v := ⟨v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun u := u.val
  left_inv _ := rfl
  right_inv _ := rfl

end tangentSpaceEquiv

variable
  {EB : Type*} [NormedAddCommGroup EB] [InnerProductSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB]
  {F : Type*} [NormedAddCommGroup F] [TopologicalSpace (TotalSpace F E)]

noncomputable section section1

variable
  {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  [TopologicalSpace B] [ChartedSpace HB B]
  [InnerProductSpace ℝ F]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB ω B] [ContMDiffVectorBundle ω F E IB]
  [FiniteDimensional ℝ EB]

def g_bilin (i b : B) :
 (TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
             (fun (x : B) ↦ E x →L[ℝ] E x →L[ℝ] ℝ)) :=
  ⟨b, (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
        (fun (x : B) ↦ E x →L[ℝ] E x →L[ℝ] ℝ) i).symm b (innerSL ℝ)⟩

variable (F) in
def g_bilin_aux (i p : B) : E p →L[ℝ] (E p →L[ℝ] ℝ) :=
  letI χ := trivializationAt F E i
  (innerSL ℝ).comp (χ.continuousLinearMapAt ℝ p) |>.flip.comp (χ.continuousLinearMapAt ℝ p)

lemma g_nonneg {j b : B} (v : E b) :
    0 ≤ ((g_bilin_aux F j b).toFun v).toFun v := by
  unfold g_bilin_aux
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
  · exact inner_self_nonneg (𝕜 := ℝ)

lemma g_pos {i b : B}
    (hb : b ∈ (trivializationAt F E i).baseSet ∩ (chartAt HB i).source)
    (v : E b) (hv : v ≠ 0) :
    0 < ((g_bilin_aux F i b).toFun v).toFun v := by
  unfold g_bilin_aux
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
  letI χ := trivializationAt F E i
  have h1 : (continuousLinearMapAt ℝ χ b) v ≠ 0 := by
    rw [← coe_continuousLinearEquivAt_eq χ hb.1]
    exact AddEquivClass.map_ne_zero_iff.mpr hv
  exact Std.lt_of_le_of_ne (inner_self_nonneg (𝕜 := ℝ))
    (inner_self_ne_zero.mpr h1).symm

theorem g_bilin_symm_aux (i p : B) (v w : E p) :
    ((g_bilin_aux F i p).toFun v).toFun w =
    ((g_bilin_aux F i p).toFun w).toFun v := by
  unfold g_bilin_aux
  simp only [ContinuousLinearMap.coe_comp, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
    ContinuousLinearMap.coe_coe]
  exact real_inner_comm _ _

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
    [FiniteDimensional ℝ (E x)] :
    FiniteDimensional ℝ (VectorSpaceAux x φ hpos hsymm hdef) := by
  exact LinearEquiv.finiteDimensional (tangentSpaceEquiv φ hpos hsymm hdef)

end section1

section section2

variable
  {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedSpace ℝ (E x)]

lemma withSeminormsOfBilinearForm {x : B}
  (φ : E x →L[ℝ] E x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0)
  [FiniteDimensional ℝ (E x)] :
  WithSeminorms (Function.const (Fin 1) (seminormOfBilinearForm φ hpos hsymm)) := by
    apply WithSeminorms.congr (norm_withSeminorms ℝ (E x))
    · have h1 : IsBoundedLinearMap ℝ (tangentSpaceEquiv φ hpos hsymm hdef).toLinearMap := by
        rw [← IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap]
        exact ⟨LinearMap.isLinear _, LinearMap.continuous_of_finiteDimensional _⟩
      obtain ⟨C, hC⟩ := h1.bound
      intro i
      use {0}, ⟨max C 1, by positivity⟩
      intro v
      simp only [Seminorm.comp_id, Fin.isValue, Finset.sup_singleton, Seminorm.smul_apply,
                 coe_normSeminorm]
      calc
        seminormOfBilinearForm φ hpos hsymm v =
        ‖tangentSpaceEquiv φ hpos hsymm hdef v‖ := rfl
        _ ≤ C * ‖v‖ := hC.2 v
        _ ≤ max C 1 * ‖v‖ := by gcongr; exact le_max_left C 1
    · have h1 : IsBoundedLinearMap ℝ (tangentSpaceEquiv φ hpos hsymm hdef).symm.toLinearMap := by
        rw [← IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap]
        exact ⟨LinearMap.isLinear _, LinearMap.continuous_of_finiteDimensional _⟩
      obtain ⟨C, hC⟩ := h1.bound
      intro j
      use {0}, ⟨max C 1, by positivity⟩
      intro v
      simp only [Seminorm.comp_id, Fin.isValue, Finset.sup_singleton, Seminorm.smul_apply,
                 coe_normSeminorm, ]
      calc ‖v‖ ≤ C * seminormOfBilinearForm φ hpos hsymm v := hC.2 ⟨v⟩
        _ ≤ max C 1 * seminormOfBilinearForm φ hpos hsymm v := by
          gcongr; exact le_max_left C 1
        _ = max C 1 * seminormOfBilinearForm φ hpos hsymm v := rfl

lemma aux_tvs {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ)
   (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
   [FiniteDimensional ℝ (E x)] :
    Bornology.IsVonNBounded ℝ {v | (φ v) v < 1} := by
  rw [WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded
        (p := Function.const (Fin 1) (seminormOfBilinearForm φ hpos hsymm))
        (withSeminormsOfBilinearForm φ hpos hsymm hdef)]
  intro I
  letI J : Finset (Fin 1) := {1}
  suffices ∃ r > 0, ∀ x ∈ {v | (φ v) v < 1},
    (J.sup (Function.const (Fin 1) (seminormOfBilinearForm φ hpos hsymm))) x < r by
    obtain (rfl | h) : I = ∅ ∨ I = {default} := by
      by_cases h : I = ∅
      · simp only [Fin.default_eq_zero, Fin.isValue]
        exact Or.symm (Or.inr h)
      · rw [Finset.eq_singleton_iff_nonempty_unique_mem]
        refine Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr h, fun x hx ↦ Unique.uniq _ _⟩
    · use 1; simp
    · convert this
  simp only [Set.mem_setOf_eq, Finset.sup_singleton, J]
  refine ⟨1, by norm_num, fun x h ↦ ?_⟩
  simp only [seminormOfBilinearForm]
  change Real.sqrt (φ x x) < 1
  rw [Real.sqrt_lt' (by norm_num)]
  simp [h]

end section2

noncomputable section section3

variable
  {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  [TopologicalSpace B] [ChartedSpace HB B]
  [InnerProductSpace ℝ F]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

def g_global_bilin_aux (f : SmoothPartitionOfUnity B IB B) (p : B) :
    E p →L[ℝ] (E p →L[ℝ] ℝ) :=
  ∑ᶠ (j : B), (f j) p • g_bilin_aux F j p

private def evalAt (b : B) (v w : E b) :
    (E b →L[ℝ] (E b →L[ℝ] ℝ)) →+ ℝ where
  toFun f := (f.toFun v).toFun w
  map_zero' := by simp
  map_add' _ _ := rfl

private lemma g_global_bilin_aux_support_finite (f : SmoothPartitionOfUnity B IB B) (b : B) :
    (Function.support fun j ↦ ((f j) b • (g_bilin_aux F j b) :
      E b →L[ℝ] E b →L[ℝ] ℝ)).Finite :=
  (f.locallyFinite'.point_finite b).subset (fun i hi => by
    simp only [Function.mem_support, ne_eq, smul_eq_zero, not_or] at hi; exact hi.1)

lemma riemannian_metric_symm_aux (f : SmoothPartitionOfUnity B IB B) (b : B)
  (v w : E b) :
  ((g_global_bilin_aux (F := F) f b).toFun v).toFun w
   =
  ((g_global_bilin_aux (F := F) f b).toFun w).toFun v := by
  unfold g_global_bilin_aux
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
  have h1 := g_global_bilin_aux_support_finite (F := F) (E := E) f b
  rw [finsum_eq_sum _ h1]
  letI h : (j : B) → (E b →L[ℝ] (E b →L[ℝ] ℝ)) := fun j ↦ (f j) b • g_bilin_aux F j b
  have h2 : (Function.support h) ⊆ h1.toFinset := Finite.toFinset_subset.mp fun ⦃a⦄ a ↦ a
  have h3 : ∀ (u v : E b),
      ∑ j ∈ h1.toFinset, (((f j) b • g_bilin_aux F j b).toFun u).toFun v =
      ((∑ j ∈ h1.toFinset, (f j) b • g_bilin_aux F j b).toFun u).toFun v := by
    intros u v
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
    rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  calc ((∑ j ∈ h1.toFinset, (f j) b • g_bilin_aux F j b).toFun v).toFun w
      = ∑ j ∈ h1.toFinset, (((f j) b • g_bilin_aux F j b).toFun v).toFun w := (h3 v w).symm
    _ = ∑ᶠ (j : B), (((f j) b • g_bilin_aux F j b).toFun v).toFun w :=
          (map_finsum_of_support_subset (φ := (evalAt b v w : (E b →L[ℝ] (E b →L[ℝ] ℝ)) →+ ℝ))
            (f := h) (s := h1.toFinset) h2).symm
    _ = ∑ᶠ (j : B), (((f j) b • g_bilin_aux F j b).toFun w).toFun v :=
          finsum_congr (fun j ↦ congrArg (HMul.hMul ((f j) b)) (g_bilin_symm_aux j b v w))
    _ = ∑ j ∈ h1.toFinset, (((f j) b • g_bilin_aux F j b).toFun w).toFun v :=
          map_finsum_of_support_subset (evalAt b w v) (f := h) (s := h1.toFinset) h2
    _ = ((∑ j ∈ h1.toFinset, (f j) b • g_bilin_aux F j b).toFun w).toFun v := h3 w v

lemma riemannian_metric_pos_def_aux (f : SmoothPartitionOfUnity B IB B)
  (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
  (b : B) {v : E b} (hv : v ≠ 0) :
  0 < g_global_bilin_aux (F := F) f b v v := by
  unfold g_global_bilin_aux
  have h1 := g_global_bilin_aux_support_finite (F := F) (E := E) f b
  rw [finsum_eq_sum _ h1]
  have h2 : ∑ j ∈ h1.toFinset, (((f j) b • g_bilin_aux F j b).toFun v).toFun v =
            ((∑ j ∈ h1.toFinset, (f j) b • g_bilin_aux F j b).toFun v).toFun v := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
    rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  letI h : (j : B) → (E b →L[ℝ] (E b →L[ℝ] ℝ)) := fun j ↦ (f j) b • g_bilin_aux F j b
  letI h' x := f x b * ((g_bilin_aux F x b).toFun v).toFun v
  have h3 : (Function.support h) ⊆ h1.toFinset := Set.Finite.toFinset_subset.mp fun ⦃a⦄ a ↦ a
  have ⟨i, h5⟩ : ∃ i, 0 < f i b := by
    by_contra! hneg
    have : ∀ (x : B), f x b = 0 := fun x => le_antisymm (hneg x) (f.nonneg' x b)
    exact absurd ((finsum_eq_zero_of_forall_eq_zero this).symm.trans (f.sum_eq_one' b trivial))
      one_ne_zero.symm
  have h6 : b ∈ (trivializationAt F E i).baseSet ∩ (chartAt HB i).source :=
    hf i (subset_closure (Function.mem_support.mpr h5.ne'))
  have h7 : ∀ j, 0 ≤ h' j := fun j => mul_nonneg (f.nonneg' j b) (g_nonneg v)
  have h8 : ∃ j, 0 < h' j := ⟨i, mul_pos h5 (g_pos h6 v hv)⟩
  have h9 : (Function.support h').Finite := by
    apply (f.locallyFinite'.point_finite b).subset
    intro x hx
    simp only [Function.support_mul, Set.mem_inter_iff, Function.mem_support, ne_eq, h'] at hx
    exact mul_ne_zero_iff.mp (mul_ne_zero_iff.mpr hx) |>.1
  have hb : ∑ᶠ i, h' i =
            ∑ j ∈ h1.toFinset, (((f j) b • g_bilin_aux F j b).toFun v).toFun v :=
    (map_finsum_of_support_subset (evalAt b v v) (f := h) (s := h1.toFinset) h3) ▸ rfl
  exact lt_of_lt_of_eq (finsum_pos h7 h8 h9) (hb.trans h2)

lemma riemannian_unit_ball_bounded_aux (f : SmoothPartitionOfUnity B IB B)
  (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
  [∀ x, FiniteDimensional ℝ (E x)] (b : B) :
    Bornology.IsVonNBounded ℝ {v : E b | g_global_bilin_aux (F := F) f b v v < 1} :=
  aux_tvs (g_global_bilin_aux f b)
    (fun v => by
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · exact le_of_lt (riemannian_metric_pos_def_aux f hf b hv))
    (riemannian_metric_symm_aux f b)
    (fun v h => by
      by_contra hv
      exact lt_irrefl 0 (h ▸ riemannian_metric_pos_def_aux f hf b hv))

end section3

section smooth

variable
  {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  [TopologicalSpace B] [ChartedSpace HB B]
  [InnerProductSpace ℝ F]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ω F E IB]

lemma g_bilin_smooth_on_chart (i : B) :
  ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
    (g_bilin (F := F) (E := E) i)
    ((trivializationAt F E i).baseSet ∩ (chartAt HB i).source) := by
  unfold g_bilin
  intro b hb
  letI ψ := trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) i
  letI innerAtP : B → F →L[ℝ] F →L[ℝ] ℝ := fun x ↦ innerSL ℝ
  have h4 : ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
    (fun c => (c, innerAtP c)) ((trivializationAt F E i).baseSet ∩ (chartAt HB i).source) :=
    contMDiffOn_id.prodMk contMDiffOn_const
  have h5 : (trivializationAt F E i).baseSet ∩ (chartAt HB i).source ⊆
  (fun c ↦ (c, innerAtP c)) ⁻¹' ψ.target := by
    intro c hc
    simp only [Set.mem_preimage]
    rw [ψ.target_eq]
    simp only [Set.mem_prod, Set.mem_univ, and_true]
    have baseSet_eq : (trivializationAt F E i).baseSet =
    (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) i).baseSet := by
      simp only [hom_trivializationAt_baseSet, Trivial.fiberBundle_trivializationAt',
               Trivial.trivialization_baseSet, Set.inter_univ, Set.inter_self]
    rw [←baseSet_eq]
    exact hc.1
  refine (ContMDiffOn.congr ((contMDiffOn_symm _).comp h4 h5) ?_) b hb
  intro y hy
  simp only [Function.comp_apply]
  ext
  · rfl
  · simp only [innerAtP]
    rw [Trivialization.symm_apply ψ _ (innerSL ℝ)]
    · simp
    · exact (mk_mem_target ψ).mp (h5 hy)

noncomputable def g_global_bilin (f : SmoothPartitionOfUnity B IB B) (p : B) :
    E p →L[ℝ] (E p →L[ℝ] ℝ) :=
      ∑ᶠ (j : B), (f j) p • (g_bilin (F := F) j p).snd

lemma g_global_bilin_smooth (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source)) :
  ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
    (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g_global_bilin (F := F) (E := E) f x)) :=
  contMDiff_totalSpace_weighted_sum_of_local_sections
    (V := fun b => E b →L[ℝ] (E b →L[ℝ] Trivial B ℝ b))
    (F_fiber := F →L[ℝ] (F →L[ℝ] ℝ))
    (s_loc := fun (i b : B) => (g_bilin (F := F) i b).snd)
    (U := fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source)
    (hU_isOpen := fun i => ((trivializationAt F E i).open_baseSet.inter (chartAt HB i).open_source))
    (hρ_subord := h_sub)
    (h_smooth_s_loc := fun i =>
      (g_bilin_smooth_on_chart i).congr (by
        unfold g_bilin
        simp only [Set.mem_inter_iff, implies_true]))

end smooth

section section6

variable
  {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  [TopologicalSpace B] [ChartedSpace HB B]
  [InnerProductSpace ℝ F]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

lemma inCoordinates_apply_eq₂_spec
    {x₀ x : B} {ϕ : E x →L[ℝ] E x →L[ℝ] ℝ} {v w : F}
    (h₁x : x ∈ (trivializationAt F E x₀).baseSet) :
    ContinuousLinearMap.inCoordinates F E (F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] ℝ) x₀ x x₀ x ϕ v w =
    ϕ ((trivializationAt F E x₀).symm x v) ((trivializationAt F E x₀).symm x w) := by
  rw [inCoordinates_apply_eq₂ h₁x h₁x (by simp [Trivial.fiberBundle_trivializationAt'])]
  simp [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization]

lemma inCoordinates_apply_eq₂_spec_symm
    (x₀ x : B) (hb : x ∈ (trivializationAt F E x₀).baseSet)
    (ϕ : F →L[ℝ] F →L[ℝ] ℝ) (u v : E x) :
    (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) x₀).symm x ϕ u v =
    ϕ (trivializationAt F E x₀ |>.continuousLinearMapAt ℝ x u)
      (trivializationAt F E x₀ |>.continuousLinearMapAt ℝ x v) := by
  letI ψ := FiberBundle.trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
      (fun (x : B) ↦ E x →L[ℝ] E x →L[ℝ] ℝ) x₀
  letI χ := trivializationAt F E x₀
  letI w := ψ.symm x ϕ
  have hc : x ∈ ψ.baseSet := by
    rw [hom_trivializationAt_baseSet]
    simp only [hom_trivializationAt_baseSet, Trivial.fiberBundle_trivializationAt',
    Trivial.trivialization_baseSet, inter_univ, inter_self]
    exact mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) hb
  have h1 : ∀ u v,
      (((continuousLinearMapAt ℝ ψ x) (ψ.symmL ℝ x ϕ)) u) v = ϕ u v :=
    fun u v => by rw [continuousLinearMapAt_symmL ψ hc]
  have h2 : ∀ u v, ϕ u v = w (χ.symm x u) (χ.symm x v) := fun u v => by
    rw [← h1, continuousLinearMapAt_apply, linearMapAt_apply, hom_trivializationAt_apply,
      if_pos hc, ← inCoordinates_apply_eq₂_spec hb]
    simp only [symmL_apply]
    exact DFunLike.congr_fun rfl v
  have h3 : χ.symm x (χ.continuousLinearMapAt ℝ x u) = u :=
    symmL_continuousLinearMapAt (trivializationAt F E x₀) hb u
  have h4 : χ.symm x (χ.continuousLinearMapAt ℝ x v) = v :=
    symmL_continuousLinearMapAt (trivializationAt F E x₀) hb v
  rw [show w u v = ϕ (χ.continuousLinearMapAt ℝ x u) (χ.continuousLinearMapAt ℝ x v) from by
    rw [h2 (χ.continuousLinearMapAt ℝ x u) (χ.continuousLinearMapAt ℝ x v), h3, h4]]

lemma g_global_bilin_eq
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
    (p : B) (u v : E p) :
    g_global_bilin (F := F) (E := E) f p u v =
    g_global_bilin_aux (F := F) f p u v := by
  have : g_global_bilin (F := F) (E := E) f p = g_global_bilin_aux (F := F) f p := by
    unfold g_global_bilin g_global_bilin_aux
    congr 1
    ext j
    congr 2
    ext u v
    by_cases h : (f j) p = 0
    · have h2 : (f j) p • (g_bilin (F := F) (E := E) j p).snd = 0 :=
        smul_eq_zero_of_left h (g_bilin j p).snd
      have h3 : (f j) p • g_bilin_aux F (E := E) j p = 0 :=
        smul_eq_zero_of_left h (g_bilin_aux F j p)
      rw [h2, h3]
      rfl
    · have hp : p ∈ tsupport (f j) := by
        rw [tsupport]
        exact subset_closure h
      have hsupp : p ∈ (trivializationAt F E j).baseSet ∩ (chartAt HB j).source :=
        hf j hp
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
      congr 1
      unfold g_bilin g_bilin_aux
      simp only [ContinuousLinearMap.coe_coe]
      conv_lhs => rw [inCoordinates_apply_eq₂_spec_symm j p hsupp.1 (innerSL ℝ) u v]
      exact real_inner_comm _ _
  rw [this]

lemma riemannian_metric_symm
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
    (b : B) (v w : E b) :
    g_global_bilin (F := F) (E := E) f b v w =
    g_global_bilin (F := F) (E := E) f b w v := by
  rw [g_global_bilin_eq f hf b v w, g_global_bilin_eq f hf b w v]
  exact (riemannian_metric_symm_aux (F := F) f b v w)

lemma riemannian_metric_pos_def
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
    (b : B) (v : E b) (hv : v ≠ 0) :
    0 < g_global_bilin (F := F) (E := E) f b v v := by
  rw [g_global_bilin_eq (F := F) (E := E) f hf b v v]
  exact riemannian_metric_pos_def_aux f hf b hv

lemma riemannian_unit_ball_bounded (f : SmoothPartitionOfUnity B IB B)
  (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
  [∀ x, FiniteDimensional ℝ (E x)] (b : B) :
  Bornology.IsVonNBounded ℝ
    {v : E b | g_global_bilin (F := F) (E := E) f b v v < 1} := by
  simp_rw [fun v => g_global_bilin_eq f hf b v v]
  exact riemannian_unit_ball_bounded_aux f hf b

end section6

section section9

variable
  {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  [TopologicalSpace B] [ChartedSpace HB B]
  [InnerProductSpace ℝ F]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB ω B] [ContMDiffVectorBundle ω F E IB]
  [FiniteDimensional ℝ EB] [SigmaCompactSpace B] [T2Space B]

/--
Existence of a smooth Riemannian metric on a manifold.
-/
public theorem exists_riemannian_metric
  [∀ x, FiniteDimensional ℝ (E x)] :
    Nonempty (ContMDiffRiemannianMetric (IB := IB) (n := ∞) (F := F) (E := E)) :=
  let ⟨f, hf⟩ : ∃ (f : SmoothPartitionOfUnity B IB B),
      f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source) := by
    apply SmoothPartitionOfUnity.exists_isSubordinate
    · exact isClosed_univ
    · intro i
      exact IsOpen.inter (trivializationAt F E i).open_baseSet (chartAt HB i).open_source
    · intro b _
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      exact ⟨b, FiberBundle.mem_baseSet_trivializationAt' b, mem_chart_source HB b⟩
  ⟨{ inner := g_global_bilin (F := F) f
     symm := riemannian_metric_symm f hf
     pos := riemannian_metric_pos_def f hf
     isVonNBounded := riemannian_unit_ball_bounded f hf
     contMDiff := g_global_bilin_smooth f hf }⟩

end section9
