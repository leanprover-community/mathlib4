import Mathlib

structure E where
  val : ℝ

instance : Coe E ℝ where
  coe w := w.val

lemma E.ext_iff (x y : E) : x = y ↔ x.val = y.val := by
  apply Iff.intro
  · intro h; rw [h]
  · intro h; cases x; cases y; simp_all

lemma E.mk_inj (x y : _) : (E.mk x = E.mk y) ↔ (x = y) := by
  apply Iff.intro
  · intro h; cases h; rfl
  · intro h; rw [h]

theorem E.mk_injective : Function.Injective E.mk :=
  fun _ _ h ↦ (E.mk_inj _ _).mp h

noncomputable def mynorm (x : E) : ℝ := 2 * ‖x.val‖

noncomputable instance : Norm E where
  norm x := mynorm x

instance : Zero E where
  zero := ⟨0⟩

instance : Add E where
  add a b := ⟨a.val + b.val⟩

instance : Neg E where neg a := ⟨-a.val⟩

instance : Sub E where
  sub a b := ⟨a.val - b.val⟩

lemma mynormSymm (xv yv : E) : mynorm (xv - yv) = mynorm (yv - xv) := by
  unfold mynorm
  have h1 : (xv - yv).val = xv.val - yv.val := rfl
  have h2 : |xv.val - yv.val| = |yv.val - xv.val| := abs_sub_comm xv.val yv.val
  simp
  exact h2

lemma mynormDef (xv : E) : mynorm (xv - xv) = 0 := by
  unfold mynorm
  have h2 : xv.val - xv.val = 0 := sub_self xv.val
  simp
  exact h2

noncomputable instance : NormedAddCommGroup E where
  add := fun x y => ⟨x.val + y.val⟩
  zero := ⟨0⟩
  neg := fun x => ⟨-x.val⟩
  norm := mynorm
  dist_eq := by intros; rfl
  add_assoc := fun x y z =>
    match x, y, z with
    | ⟨xv⟩, ⟨yv⟩, ⟨zv⟩ => congrArg E.mk (add_assoc xv yv zv)
  zero_add := fun x => match x with | ⟨xv⟩ => congrArg E.mk (zero_add xv)
  add_zero := fun x => match x with | ⟨xv⟩ => congrArg E.mk (add_zero xv)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := fun x => match x with | ⟨xv⟩ => congrArg E.mk (neg_add_cancel xv)
  add_comm := fun x y => match x, y with | ⟨xv⟩, ⟨yv⟩ => congrArg E.mk (add_comm xv yv)
  dist_self := fun x => mynormDef x
  dist_comm := fun x y => mynormSymm x y
  dist_triangle := fun x y z =>
     match x, y, z with
    | ⟨xv⟩, ⟨yv⟩, ⟨zv⟩ => by
      unfold mynorm
      simp
      have hxz : ((E.mk xv) - (E.mk zv)).val = (E.mk xv).val - (E.mk zv).val := rfl
      have hxy : ((E.mk xv) - (E.mk yv)).val = (E.mk xv).val - (E.mk yv).val := rfl
      have hyz : ((E.mk yv) - (E.mk zv)).val = (E.mk yv).val - (E.mk zv).val := rfl
      have hz : (E.mk zv).val = zv := rfl
      have hy : (E.mk yv).val = yv := rfl
      have hx : (E.mk xv).val = xv := rfl
      rw [hxz, hxy, hyz, hz, hy, hx]
      have h3 : |xv - zv| ≤ |xv - yv| + |yv - zv| := norm_sub_le_norm_sub_add_norm_sub xv yv zv
      have h4 : 2 * |xv - zv| ≤ 2 * (|xv - yv| + |yv - zv|) :=
        mul_le_mul_of_nonneg_left h3 zero_le_two
      have h5 : 2 * (|xv - yv| + |yv - zv|) = 2 * |xv - yv| + 2 * |yv - zv| :=
        LeftDistribClass.left_distrib 2 |xv - yv| |yv - zv|
      exact le_of_le_of_eq h4 h5
  eq_of_dist_eq_zero := by
    intro x y h
    have h1 : mynorm (x - y) = 0 := h
    have h5 : 2 * |x.val - y.val| = 0 := h
    have h6 : (2 : ℝ) * 0 = 0 := CommMonoidWithZero.mul_zero 2
    have h2 : 2 * |x.val - y.val| = 2 * 0 := by
      rw [<-h6] at h5
      exact h5
    have h4 : (2 : ℝ) ≠ 0 := Ne.symm (NeZero.ne' 2)
    have h3 : |x.val - y.val| = 0 := mul_left_cancel₀ h4 h2
    have h7 : x.val = y.val := by
      have : x.val - y.val = 0 := abs_eq_zero.mp h3
      have : x.val = y.val := sub_eq_zero.mp this
      exact this
    exact (E.ext_iff x y).mpr h7

instance : SMul ℝ E where
  smul a x := ⟨a * x.val⟩

instance : Module ℝ E where

  one_smul x := E.ext_iff _ _ |>.mpr (one_mul x.val)
  mul_smul a b x := E.ext_iff _ _ |>.mpr (mul_assoc a b x.val)
  smul_add a x y := E.ext_iff _ _ |>.mpr (mul_add a x.val y.val)
  smul_zero a := E.ext_iff _ _ |>.mpr (mul_zero a)
  zero_smul x := E.ext_iff _ _ |>.mpr (zero_mul x.val)
  add_smul a b x := E.ext_iff _ _ |>.mpr (add_mul a b x.val)

#check (by infer_instance : TopologicalSpace E)
#synth TopologicalSpace E

noncomputable instance : NormedSpace ℝ E where
  norm_smul_le a x := by
    change mynorm (a • x) ≤ ‖a‖ * mynorm x
    unfold mynorm
    change 2 * |(a • x).val| ≤ |a| * (2 * |x.val|)
    change 2 * |a * x.val| ≤ |a| * (2 * |x.val|)
    rw [abs_mul]
    ring_nf
    exact Std.IsPreorder.le_refl (|a| * |x.val| * 2)

lemma bbr_simple : WithSeminorms (fun (_ : Fin 1) => normSeminorm ℝ E) :=
  norm_withSeminorms ℝ E

#check LinearMap.continuous_of_finiteDimensional

def id_real_to_E : ℝ →L[ℝ] E :=
  let L : ℝ →ₗ[ℝ] E :=
  { toFun := fun x => ⟨x⟩,
    map_add' := by intro x y; rfl,
    map_smul' := by intro m x; rfl }

  { toLinearMap := L,
    cont := (LinearMap.continuous_of_finiteDimensional L) }

def toReal : E →ₗ[ℝ] ℝ :=
{ toFun := fun x => x.val,
  map_add' := by intro x y; rfl,
  map_smul' := by intro r x; rfl }

def fromReal : ℝ →ₗ[ℝ] E :=
{ toFun := fun x => ⟨x⟩,
  map_add' := by intro x y; rfl,
  map_smul' := by intro r x; rfl }

def equivEReal : E ≃ₗ[ℝ] ℝ :=
{ toLinearMap := toReal,
  invFun := fun x => ⟨x⟩,
  left_inv := by intro x; cases x; rfl,
  right_inv := by intro x; rfl }

instance : FiniteDimensional ℝ E := LinearEquiv.finiteDimensional (equivEReal.symm)

def id_E_to_real : E →L[ℝ] ℝ :=
  let L : E →ₗ[ℝ] ℝ :=
  { toFun := fun x => x,
    map_add' := by intro x y; rfl,
    map_smul' := by intro m x; rfl }

  { toLinearMap := L,
    cont := (LinearMap.continuous_of_finiteDimensional L) }


/-
Quoting
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Module/FiniteDimension.html

The fact that all norms are equivalent is not written explicitly,
as it would mean having two norms on a single space, which is not the way type classes work.
However, if one has a finite-dimensional vector space E with a norm,
and a copy E' of this type with another norm,
then the identities from E to E' and from E'to E are continuous thanks to
LinearMap.continuous_of_finiteDimensional. This gives the desired norm equivalence.
-/
