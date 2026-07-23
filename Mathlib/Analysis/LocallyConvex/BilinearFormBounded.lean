/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Dominic Steinitz
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! # Seminorms from positive-definite bilinear forms

This file constructs the seminorm associated to a positive-definite symmetric bilinear form and
establishes the boundedness properties needed for locally convex spaces.
-/

@[expose] public section

variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]

section

/-- `W φ hpos hsymm hdef` is a copy of `V` equipped with the norm
induced by the positive-definite bilinear form `φ`.

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
structure W
  (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) where
  val : V

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] in
lemma W.ext_iff (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
    (u v : W φ hpos hsymm hdef) :
  u = v ↔ u.val = (v.val : V) := by
  cases u; cases v; simp

instance (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Zero (W φ hpos hsymm hdef) where
  zero := ⟨0⟩

instance (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Add (W φ hpos hsymm hdef) where
  add u v := ⟨u.val + v.val⟩

instance (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Neg (W φ hpos hsymm hdef) where
  neg u := ⟨-u.val⟩

instance (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Sub (W φ hpos hsymm hdef) where
  sub u v := ⟨u.val - v.val⟩

instance (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  SMul ℝ (W φ hpos hsymm hdef) where
  smul a u := ⟨a • u.val⟩

noncomputable def seminormOfBilinearForm (φ : V →L[ℝ] V →L[ℝ] ℝ)
    (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
  Seminorm ℝ V where
  toFun v := Real.sqrt (φ v v)
  map_zero' := by simp
  add_le' r s := by
    rw [Real.sqrt_le_iff]
    · have h0 : ((φ r) s) * ((φ s) r) ≤ ((φ r) r) * ((φ s) s) :=
        LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le φ.toLinearMap₁₂ hpos r s
      have h1 : φ (r + s) (r + s) ≤ (Real.sqrt ((φ r) r) + Real.sqrt ((φ s) s)) ^ 2 := by
        calc φ (r + s) (r + s)
          = (φ r) r + (φ r) s + (φ s) r + (φ s) s := by
              simp only [map_add, add_apply]
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

noncomputable instance (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Norm (W φ hpos hsymm hdef) where
  norm v := seminormOfBilinearForm φ hpos hsymm v.val

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] in
lemma seminormOfBilinearForm_sub_self (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
    (v : W φ hpos hsymm hdef) :
  seminormOfBilinearForm φ hpos hsymm (v.val - v.val) = 0 := by
  unfold seminormOfBilinearForm
  simp

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] in
lemma seminormOfBilinearForm_sub_comm (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
    (u v : W φ hpos hsymm hdef) :
    seminormOfBilinearForm φ hpos hsymm (u.val - v.val) =
    seminormOfBilinearForm φ hpos hsymm (v.val - u.val) := by
  change √((φ (u.val - v.val)) (u.val - v.val)) = √((φ (v.val - u.val)) (v.val - u.val))
  simp only [map_sub, FunLike.coe_sub, Pi.sub_apply]
  ring_nf

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] in
lemma eq_of_dist_eq_zero_aux (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
    {u v : W φ hpos hsymm hdef} :
    (seminormOfBilinearForm φ hpos hsymm) (u.val - v.val) = 0 → u = v := by
    intro h
    rw [seminormOfBilinearForm] at h
    have h1 : u.val - v.val = 0 := hdef (u.val - v.val)
      ((Real.sqrt_eq_zero (hpos (u.val - v.val))).mp h)
    apply (W.ext_iff φ hpos hsymm hdef u v).mpr
    exact sub_eq_zero.mp h1

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] in
lemma dist_triangle_aux (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  ∀ (x y z : W φ hpos hsymm hdef),
    (seminormOfBilinearForm φ hpos hsymm) (x.val - z.val) ≤
      (seminormOfBilinearForm φ hpos hsymm) (x.val - y.val) +
      (seminormOfBilinearForm φ hpos hsymm) (y.val - z.val) := by
  intro u v w
  simpa [sub_add_sub_cancel] using
    map_add_le_add (seminormOfBilinearForm φ hpos hsymm) (u.val - v.val) (v.val - w.val)

noncomputable instance (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
    NormedAddCommGroup (W φ hpos hsymm hdef) where
  norm v := seminormOfBilinearForm φ hpos hsymm v.val
  dist_eq := by
    intros x y
    simp only [Neg.neg, Add.add, HAdd.hAdd]
    have : Add.add (-x.val) y.val = y.val - x.val := by
      rw [Add.add_eq_hAdd]
      exact neg_add_eq_sub x.val y.val
    rw [show Add.add (-x.val) y.val = y.val - x.val from this]
    exact seminormOfBilinearForm_sub_comm φ hpos hsymm hdef x y
  add_assoc u v w := W.ext_iff _ _ _ _ _ _|>.mpr (add_assoc u.val v.val w.val)
  zero_add u := W.ext_iff _ _ _ _ _ _ |>.mpr (zero_add u.val)
  add_zero u := W.ext_iff _ _ _ _ _ _ |>.mpr (add_zero u.val)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel u := W.ext_iff _ _ _ _ _ _ |>.mpr (neg_add_cancel u.val)
  add_comm u v := W.ext_iff _ _ _ _ _ _ |>.mpr (add_comm u.val v.val)
  sub_eq_add_neg u v := W.ext_iff _ _ _ _ _ _ |>.mpr (sub_eq_add_neg u.val v.val)
  dist_self := seminormOfBilinearForm_sub_self φ hpos hsymm hdef
  dist_comm := seminormOfBilinearForm_sub_comm φ hpos hsymm hdef
  dist_triangle := dist_triangle_aux φ hpos hsymm hdef
  eq_of_dist_eq_zero := eq_of_dist_eq_zero_aux φ hpos hsymm hdef

instance (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Module ℝ (W φ hpos hsymm hdef) where
  one_smul u := W.ext_iff _ _ _ _ _ _ |>.mpr (one_smul ℝ u.val)
  mul_smul a b u := W.ext_iff _ _ _ _ _ _ |>.mpr (mul_smul a b u.val)
  smul_add a u v := W.ext_iff _ _ _ _ _ _ |>.mpr (smul_add a u.val v.val)
  smul_zero a := W.ext_iff _ _ _ _ _ _ |>.mpr (smul_zero a)
  zero_smul u := W.ext_iff _ _ _ _ _ _ |>.mpr (zero_smul ℝ u.val)
  add_smul a b u := W.ext_iff _ _ _ _ _ _ |>.mpr (add_smul a b u.val)

instance (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  NormedSpace ℝ (W φ hpos hsymm hdef) where
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

def W.equiv (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
    V ≃ₗ[ℝ] W φ hpos hsymm hdef where
  toFun v := ⟨v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun u := u.val
  left_inv _ := rfl
  right_inv _ := rfl

end

instance (φ : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
    [FiniteDimensional ℝ (V)] :
    FiniteDimensional ℝ (W φ hpos hsymm hdef) := by
  exact LinearEquiv.finiteDimensional (W.equiv φ hpos hsymm hdef)

lemma withSeminormsOfBilinearForm
  (φ : V →L[ℝ] V →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0)
  [FiniteDimensional ℝ (V)] :
  WithSeminorms (Function.const (Fin 1) (seminormOfBilinearForm φ hpos hsymm)) := by
  let e : V ≃L[ℝ] W φ hpos hsymm hdef :=
    (W.equiv φ hpos hsymm hdef).toContinuousLinearEquiv
  have hfam : SeminormFamily.comp
      (fun _ : Fin 1 ↦ normSeminorm ℝ (W φ hpos hsymm hdef))
      (W.equiv φ hpos hsymm hdef).toLinearMap
      = Function.const (Fin 1) (seminormOfBilinearForm φ hpos hsymm) := by
    ext i v
    rfl
  rw [← hfam]
  exact e.toHomeomorph.isInducing.withSeminorms (norm_withSeminorms ℝ _)

lemma isVonNBounded_of_posDef (φ : V →L[ℝ] V →L[ℝ] ℝ)
   (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
   [FiniteDimensional ℝ (V)] :
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
    · rw [h]
      congr 1
  simp only [Set.mem_ofPred_eq, Finset.sup_singleton, J]
  refine ⟨1, by norm_num, fun x h ↦ ?_⟩
  simp only [seminormOfBilinearForm]
  change Real.sqrt (φ x x) < 1
  rw [Real.sqrt_lt' (by norm_num)]
  simp [h]

end
