import Mathlib.Data.Real.Archimedean

/-!
# The reals are a conditionally complete linearly ordered field
-/

@[expose] public section

/-- The reals are a conditionally complete linearly ordered field. -/
noncomputable instance : ConditionallyCompleteLinearOrderedField ℝ := { }

/-- There exists no nontrivial ring homomorphism `ℝ →+* ℝ`. -/
instance Real.RingHom.unique : Unique (ℝ →+* ℝ) where
  default := RingHom.id ℝ
  uniq f := congr_arg OrderRingHom.toRingHom (@Subsingleton.elim (ℝ →+*o ℝ) _
      ⟨f, ringHom_monotone (fun r hr => ⟨√r, sq_sqrt hr⟩) f⟩ default)

@[simp]
theorem Real.ringHom_apply {F : Type*} [FunLike F ℝ ℝ] [RingHomClass F ℝ ℝ] (f : F) (r : ℝ) :
    f r = r :=
  DFunLike.congr_fun (Unique.eq_default (RingHomClass.toRingHom f)) r
