/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Nonneg.Ring
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.IsTensorProduct

/-!
# Additive localizations of semirings

Given a semiring `R` and a two-sided ideal `I`, `AddLocalization I.toAddSubmonoid` is naturally
equipped with the structure of a semiring.
In the case `I = R`, `GrothendieckAddGroup R` is the initial ring with a ring homomorphism from `R`
and may be called the Grothendieck ring of `R`.
-/

namespace Archimedean

variable {G : Type*} [AddCommGroup G]

/- TODO: multiplicativize Nonneg.inhabited, .zero, .add, .nsmul, .addMonoid, .coeAddMonoidHom,
.isOrderedAddMonoid, .isOrderedCancelAddMonoid, etc. -/
theorem isLocalizationMap [PartialOrder G] [AddLeftMono G] [Archimedean G]
    (S : AddSubmonoid {g : G // 0 ≤ g}) (hS : S ≠ ⊥) : S.IsLocalizationMap Subtype.val :=
  S.isLocalizationMap_of_addGroup Subtype.val_injective fun g ↦
    have ⟨p, hpS, hp0⟩ := (S.bot_or_exists_ne_zero).resolve_left hS
    have ⟨n, le⟩ := arch (-g) (p.2.lt_of_ne <| Subtype.coe_ne_coe.mpr hp0.symm)
    ⟨⟨g + n • p, by simpa using add_le_add_left le g⟩, _, nsmul_mem hpS n, by simp⟩

instance isLocalizationMap_top [LinearOrder G] [AddLeftMono G] [Archimedean G] :
    (⊤ : AddSubmonoid {g : G // 0 ≤ g}).IsLocalizationMap Subtype.val := by
  cases subsingleton_or_nontrivial G
  · exact AddSubmonoid.isLocalizationMap_of_addGroup Subtype.val_injective
      fun g ↦ ⟨0, 0, ⟨⟩, Subsingleton.elim ..⟩
  · exact isLocalizationMap ⊤ top_ne_bot

example : (⊤ : AddSubmonoid ℚ≥0).IsLocalizationMap ((↑) : ℚ≥0 → ℚ) := isLocalizationMap_top

end Archimedean

namespace AddLocalization

variable {R : Type*}

section SMul

variable {R M : Type*} [AddCommMonoid M] (S : AddSubmonoid M)

section DistribSMul

variable [DistribSMul R M] (h : ∀ r : R, ∀ s ∈ S, r • s ∈ S)

/-- Additive localizations inherit distributive scalar multiplications. -/
abbrev instDistribSMul : DistribSMul R (AddLocalization S) where
  smul r x := x.liftOn (fun m s ↦ .mk (r • m) ⟨_, h r s s.2⟩) fun {m₁ m₂ s₁ s₂} rel ↦
    have ⟨c, eq⟩ := r_iff_exists.mp rel
    mk_eq_mk_iff.mpr (r_iff_exists.mpr ⟨⟨_, h r c c.2⟩, by simpa using congr(r • $eq)⟩)
  smul_zero r := by
    rw [← mk_zero]
    exact congr_arg₂ mk (smul_zero _) (Subtype.ext <| smul_zero _)
  smul_add r x := by
    refine x.rec (fun mx sx y ↦ y.rec (fun my sy ↦ .trans ?_ (mk_add ..).symm) ?_) ?_
    on_goal 2 => rw [mk_add]; exact congr(mk $(smul_add ..) $(by simp))
    all_goals intros; rfl

theorem smul_def (r : R) (m : M) (s : S) : letI := instDistribSMul S h
    r • mk m s = mk (r • m) ⟨_, h r s s.2⟩ := rfl

end DistribSMul

/-- Additive localizations inherit distributive multiplication actions. -/
abbrev instDstribMulAction [Monoid R] [DistribMulAction R M] (h : ∀ r : R, ∀ s ∈ S, r • s ∈ S) :
    DistribMulAction R (AddLocalization S) where
  __ := instDistribSMul S h
  one_smul x := x.rec (fun _ _ ↦ congr(mk $(one_smul ..) $(Subtype.ext <| one_smul ..))) fun _ ↦ rfl
  mul_smul _ _ x := x.rec (fun _ _ ↦
    congr(mk $(mul_smul ..) $(Subtype.ext <| mul_smul ..))) fun _ ↦ rfl

instance [Semiring R] [Module R M] (S : Submodule R M) :
    Module R (AddLocalization S.toAddSubmonoid) where
  __ := instDstribMulAction _ fun r _ ↦ S.smul_mem r
  add_smul _ _ x := x.rec (fun _ _ ↦
    congr(mk $(add_smul ..) $(Subtype.ext <| add_smul ..)).trans (mk_add ..).symm) fun _ ↦ rfl
  zero_smul x := x.rec (fun _ _ ↦
    congr(mk $(zero_smul ..) $(Subtype.ext <| zero_smul ..)).trans mk_zero) fun _ ↦ rfl

end SMul

section Mul

variable [AddCommMonoid R] (M : AddSubmonoid R) [Mul R] [LeftDistribClass R] [RightDistribClass R]
variable (hl : ∀ r : R, ∀ s ∈ M, r * s ∈ M) (hr : ∀ r : R, ∀ s ∈ M, s * r ∈ M)
include hl hr

/-- Additive localizations inherit multiplication. -/
abbrev instMul : Mul (AddLocalization M) where
  mul x y := x.liftOn₂ y (fun rx sx ry sy ↦ .mk (rx * ry + sx * sy)
    ⟨rx * sy + sx * ry, add_mem (hl _ _ sy.2) (hr _ _ sx.2)⟩)
    fun {rx₁ rx₂ sx₁ sx₂ ry₁ ry₂ sy₁ sy₂} hx hy ↦ mk_eq_mk_iff.mpr <| by
      have ⟨cx, hx⟩ := r_iff_exists.mp hx
      have ⟨cy, hy⟩ := r_iff_exists.mp hy
      apply AddCon.trans (y := ⟨rx₁ * ry₂ + sx₁ * sy₂, rx₁ * sy₂ + sx₁ * ry₂,
        add_mem (hl _ _ sy₂.2) (hr _ _ sx₁.2)⟩) <;> rw [r_iff_exists]
      · use ⟨(rx₁ + sx₁) * cy, hl _ _ cy.2⟩
        simp_rw [add_add_add_comm, ← mul_add, add_comm ry₁, add_comm ry₂,
          add_mul, add_add_add_comm, ← mul_add, hy]
      · use ⟨cx * (sy₂ + ry₂), hr _ _ cx.2⟩
        simp_rw [add_comm (rx₁ * ry₂), add_comm (rx₂ * ry₂), add_add_add_comm]
        rw [add_add_add_comm (rx₁ * sy₂)]
        simp_rw [← add_mul, mul_add, add_add_add_comm _ (cx * ry₂), ← add_mul,
          add_comm rx₁, add_comm rx₂, hx]

theorem mk_mul (rx ry : R) (sx sy : M) : letI := instMul M hl hr
    mk rx sx * mk ry sy = mk (rx * ry + sx * sy)
      ⟨rx * sy + sx * ry, add_mem (hl _ _ sy.2) (hr _ _ sx.2)⟩ := rfl

instance : letI := instMul M hl hr; LeftDistribClass (AddLocalization M) :=
  letI := instMul M hl hr
  { left_distrib x := by
      refine x.rec (fun rx sx y ↦ y.rec (fun ry sy z ↦ z.rec (fun rz sz ↦ ?_) <|
        by intros; rfl) <| by intros; rfl) (by intros; rfl)
      simp_rw [mk_add, mk_mul, mk_add, M.coe_add, mul_add]
      congr 1
      on_goal 2 => apply Subtype.val_injective; simp_rw [M.mk_add_mk]
      all_goals ac_rfl }

instance : letI := instMul M hl hr; RightDistribClass (AddLocalization M) :=
  letI := instMul M hl hr
  { right_distrib x := by
      refine x.rec (fun rx sx y ↦ y.rec (fun ry sy z ↦ z.rec (fun rz sz ↦ ?_) <|
        by intros; rfl) <| by intros; rfl) (by intros; rfl)
      simp_rw [mk_add, mk_mul, mk_add, M.coe_add, add_mul]
      congr 1
      on_goal 2 => apply Subtype.val_injective; simp_rw [M.mk_add_mk]
      all_goals ac_rfl }

end Mul

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R] (M : AddSubmonoid R)
variable (hl : ∀ r : R, ∀ s ∈ M, r * s ∈ M) (hr : ∀ r : R, ∀ s ∈ M, s * r ∈ M)

/-- Additive localizations inherit non-unital non-associative semiring structures. -/
abbrev instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (AddLocalization M) where
  __ := instMul M hl hr
  __ := instLeftDistribClass M hl hr
  __ := instRightDistribClass M hl hr
  zero_mul x := x.rec (fun _ _ ↦ by
    simp_rw [← mk_zero, mk_mul, M.coe_zero, zero_mul, zero_add, M.zero_def]) fun _ ↦ rfl
  mul_zero x := x.rec (fun _ _ ↦ by
    simp_rw [← mk_zero, mk_mul, M.coe_zero, mul_zero, zero_add, M.zero_def]) fun _ ↦ rfl

theorem mk_zero_mul (x : R) (y : AddLocalization M) :
    letI := instNonUnitalNonAssocSemiring M hl hr
    letI := instDistribSMul M hl
    mk x 0 * y = x • y :=
  y.rec (fun ry my ↦ by simp_rw [mk_mul, M.coe_zero, zero_mul, add_zero, smul_def, smul_eq_mul])
    fun _ ↦ rfl

/-- The non-unital ring homomorphism from a semiring to its additive localization. -/
@[simps] def nonUnitalRingHom : letI := instNonUnitalNonAssocSemiring M hl hr
    R →ₙ+* AddLocalization M :=
  letI := instNonUnitalNonAssocSemiring M hl hr
  { toFun := addMonoidOf M
    map_add' := map_add _
    map_mul' x y := by
      simp_rw [← mk_zero_eq_addMonoidOf_mk, mk_mul]
      simp [AddSubmonoid.zero_def]
    map_zero' := map_zero (addMonoidOf M) }

end NonUnitalNonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring R] (M : AddSubmonoid R)
  (hl : ∀ r : R, ∀ s ∈ M, r * s ∈ M) (hr : ∀ r : R, ∀ s ∈ M, s * r ∈ M)

/-- Additive localizations inherit non-unital semiring structures. -/
abbrev instNonUnitalSemiring : NonUnitalSemiring (AddLocalization M) where
  __ := instNonUnitalNonAssocSemiring M hl hr
  mul_assoc x := by
    refine x.rec (fun rx sx y ↦ y.rec (fun ry sy z ↦ z.rec (fun rz sz ↦ ?_)
      fun _ ↦ rfl) fun _ ↦ rfl) fun _ ↦ rfl
    simp only [mk_mul, mul_add, add_mul]
    congr 1 <;> ac_rfl

instance instIsScalarTower :
    letI := instDistribSMul M hl
    letI := instNonUnitalSemiring M hl hr
    IsScalarTower R (AddLocalization M) (AddLocalization M) :=
  letI := instDistribSMul M hl
  letI := instNonUnitalSemiring M hl hr
  { smul_assoc x y z := by
      iterate 2 rw [smul_eq_mul, ← mk_zero_mul _ _ hr]
      rw [mul_assoc] }

end NonUnitalSemiring

section NonAssocSemiring

variable [NonAssocSemiring R] (M : AddSubmonoid R)
variable (hl : ∀ r : R, ∀ s ∈ M, r * s ∈ M) (hr : ∀ r : R, ∀ s ∈ M, s * r ∈ M)

/-- Additive localizations inherit non-associative semiring structures. -/
abbrev instNonAssocSemiring : NonAssocSemiring (AddLocalization M) where
  __ := instNonUnitalNonAssocSemiring M hl hr
  one := mk 1 0
  one_mul x := x.rec (fun r s ↦ (mk_mul ..).trans <| by simp) (by intros; rfl)
  mul_one x := x.rec (fun r s ↦ (mk_mul ..).trans <| by simp) (by intros; rfl)

theorem smul_one_eq_mk_zero (x : R) :
    letI := instDistribSMul M hl
    letI := instNonAssocSemiring M hl hr
    x • (1 : AddLocalization M) = mk x 0 :=
  (smul_def ..).trans <| congr(mk $(mul_one x) $(Subtype.ext <| mul_zero x))

theorem isLocalizationMap_smul_one :
    letI := instDistribSMul M hl
    letI := instNonAssocSemiring M hl hr
    M.IsLocalizationMap fun r ↦ r • (1 : AddLocalization M) := by
  simp_rw [smul_one_eq_mk_zero]; exact (addMonoidOf M).isLocalizationMap

include hr in
theorem faithfulSMul_of_isAddRegular (hM : ∀ x ∈ M, IsAddRegular x) :
    letI := instDistribSMul M hl
    FaithfulSMul R (AddLocalization M) :=
  letI := instDistribSMul M hl
  { eq_of_smul_eq_smul {_ _} eq := (addMonoidOf M).injective_iff.mpr hM <| by
      convert ← eq 1 <;> apply smul_one_eq_mk_zero _ _ hr }

include hr in
theorem faithfulSMul_of_isCancelAdd [IsCancelAdd R] : letI := instDistribSMul M hl
    FaithfulSMul R (AddLocalization M) :=
  faithfulSMul_of_isAddRegular _ _ hr fun _ _ ↦ .all _

/-- The ring homomorphism from a semiring to its additive localization. -/
@[simps] def ringHom : letI := instNonAssocSemiring M hl hr
    R →+* AddLocalization M :=
  letI := instNonAssocSemiring M hl hr
  { __ := nonUnitalRingHom M hl hr
    map_one' := rfl }

end NonAssocSemiring

/-- Additive localizations inherit semiring structures. -/
abbrev instSemiring [Semiring R] (M : AddSubmonoid R)
    (hl : ∀ r : R, ∀ s ∈ M, r * s ∈ M) (hr : ∀ r : R, ∀ s ∈ M, s * r ∈ M) :
    Semiring (AddLocalization M) where
  __ := instNonUnitalSemiring M hl hr
  __ := instNonAssocSemiring M hl hr

instance [Semiring R] (I : Ideal R) [I.IsTwoSided] :
    Semiring (AddLocalization I.toAddSubmonoid) :=
  instSemiring _ I.mul_mem_left fun _ _ ↦ I.mul_mem_right _

instance [Semiring R] (I : Ideal R) [I.IsTwoSided] :
    IsScalarTower R (AddLocalization I.toAddSubmonoid) (AddLocalization I.toAddSubmonoid) :=
  instIsScalarTower _ I.mul_mem_left fun _ _ ↦ I.mul_mem_right _

/-- The ring homomorphism from a semiring to its additive localization at an ideal. -/
@[simps!] abbrev ringHomᵢ [Semiring R] (I : Ideal R) [I.IsTwoSided] :
    R →+* AddLocalization I.toAddSubmonoid :=
  ringHom _ I.mul_mem_left fun _ _ ↦ I.mul_mem_right _

/-- Additive localizations inherit non-unital non-associative commutative semiring structures. -/
abbrev instNonUnitalNonAssocCommSemiring [NonUnitalNonAssocCommSemiring R] (M : AddSubmonoid R)
    (h : ∀ r : R, ∀ s ∈ M, r * s ∈ M) :
    NonUnitalNonAssocCommSemiring (AddLocalization M) where
  __ := instNonUnitalNonAssocSemiring M h (by simpa [mul_comm] using h)
  mul_comm x := x.rec (fun rx sx y ↦ y.rec (fun ry sy ↦ by
    simp_rw [mk_mul, mul_comm, add_comm]) <| by intros; rfl) (by intros; rfl)

/-- Additive localizations inherit non-unital commutative semiring structures. -/
abbrev instNonUnitalCommSemiring [NonUnitalCommSemiring R] (M : AddSubmonoid R)
    (h : ∀ r : R, ∀ s ∈ M, r * s ∈ M) :
    NonUnitalCommSemiring (AddLocalization M) where
  __ := instNonUnitalSemiring M h (by simpa [mul_comm] using h)
  __ := let _ : NonUnitalNonAssocCommSemiring R := {}; instNonUnitalNonAssocCommSemiring M h

/-- Additive localizations inherit commutative semiring structures. -/
abbrev instCommSemiring [CommSemiring R] (M : AddSubmonoid R) (h : ∀ r : R, ∀ s ∈ M, r * s ∈ M) :
    CommSemiring (AddLocalization M) where
  __ := instNonUnitalCommSemiring M h
  __ := instSemiring M h (by simpa [mul_comm] using h)

instance [CommSemiring R] (I : Ideal R) : CommSemiring (AddLocalization I.toAddSubmonoid) :=
  instCommSemiring _ I.mul_mem_left

instance [CommSemiring R] (I : Ideal R) : Algebra R (AddLocalization I.toAddSubmonoid) where
  __ := instDistribSMul I.toAddSubmonoid I.mul_mem_left
  algebraMap := ringHomᵢ I
  commutes' _ := mul_comm _
  smul_def' r x := x.rec (fun _ _ ↦ by simp [← mk_zero_eq_addMonoidOf_mk, mk_mul]; rfl) fun _ ↦ rfl

-- TODO: NonAssocCommSemiring after #28532

end AddLocalization

namespace AddSubmonoid.IsLocalizationMap

variable {R S T F G : Type*}

-- similarly one can prove a RightDistribClass version
protected theorem map_one [AddCommMonoid R] [MulOneClass R] [AddCommMonoid S] [MulOneClass S]
    [LeftDistribClass S] (M : AddSubmonoid R) [FunLike F R S] [MulHomClass F R S] {f : F}
    (hf : IsLocalizationMap M f) : f 1 = 1 :=
  have ⟨x, eq⟩ := hf.surj' 1
  (hf.map_add_units' x.2).add_right_cancel <| by
    rw [eq, ← mul_one (f 1), ← one_mul x.2.1, map_mul, ← mul_add, eq, ← map_mul, one_mul]

section CompatibleSMul

variable (N₁ N₂ : Type*) [Semiring S] [SMul R S]
  [AddCommMonoid N₁] [AddCommMonoid N₂] [Module S N₁] [Module S N₂]

theorem linearMapCompatibleSMul [Semiring R] [Module R N₁] [Module R N₂]
    [IsScalarTower R S N₁] [IsScalarTower R S N₂] (M : AddSubmonoid R)
    (hf : IsLocalizationMap M fun r : R ↦ r • (1 : S)) :
    LinearMap.CompatibleSMul N₁ N₂ S R where
  map_smul l s n := by
    have ⟨x, eq⟩ := hf.surj' s
    apply (((hf.map_add_units' x.2).smul_right n).map l).add_right_cancel
    rw [← map_add, ← add_smul, eq, smul_one_smul, map_smul, ← smul_one_smul S, ← eq, add_smul]
    simp_rw [smul_one_smul, map_smul]

open TensorProduct in
theorem tensorProductCompatibleSMul [CommSemiring R] [Module R N₁] [Module R N₂]
    [IsScalarTower R S N₁] [IsScalarTower R S N₂] (M : AddSubmonoid R)
    (hf : IsLocalizationMap M fun r : R ↦ r • (1 : S)) :
    CompatibleSMul R S N₁ N₂ where
  smul_tmul s n₁ n₂ := by
    have ⟨x, eq⟩ := hf.surj' s
    apply (((hf.map_add_units' x.2).smul_right n₁).tmul_right R n₂).add_right_cancel
    rw [← add_tmul, ← add_smul, eq, smul_one_smul, smul_tmul, ← smul_one_smul S, ← eq, add_smul]
    simp_rw [tmul_add, smul_one_smul, smul_tmul]

end CompatibleSMul

section NonUnital

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring T]
variable {M : AddSubmonoid R}
variable [FunLike F R S] [NonUnitalRingHomClass F R S] {f : F} (hf : IsLocalizationMap M f)
variable [FunLike G R T] [NonUnitalRingHomClass G R T] {g : G} (hg : ∀ m : M, IsAddUnit (g m))

open AddUnits in
/-- Given a localization map `f : R →ₙ+* S` for a submonoid `M ⊆ R` and a map of non-unital
semirings `g : R →ₙ+* T` such that `g y` is additively invertible for all `y : M`, the homomorphism
induced from `S` to `T` sending `z : S` to `g x - g y`, where `(x, y) : R × M` are such that
`z = f x - f y`. -/
noncomputable def liftNonUnitalRingHom : S →ₙ+* T where
  __ := LocalizationMap.lift ⟨f, hf⟩ (g := (g : R →+ T)) hg
  map_mul' x y := by
    set l : LocalizationMap M S := ⟨f, hf⟩
    obtain ⟨rx, mx, rfl⟩ := l.mk'_surjective x
    obtain ⟨ry, my, rfl⟩ := l.mk'_surjective y
    simp_rw [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, LocalizationMap.mk']
    simp only [map_add, mul_add, add_mul]
    congr
    on_goal 1 => trans g (rx * ry)
    on_goal 3 =>
      simp_rw [← coe_map_neg, ← val_mul_right, l.lift_eq, ← neg_mul_right,
        ← coe_map_neg, ← AddUnits.ext_iff, neg_inj, AddUnits.ext_iff]
      trans g (mx * ry)
    on_goal 5 =>
      simp_rw [← coe_map_neg, ← val_mul_left, l.lift_eq, ← neg_mul_left,
        ← coe_map_neg, ← AddUnits.ext_iff, neg_inj, AddUnits.ext_iff]
      trans g (rx * my)
    on_goal 7 => simp_rw [← coe_map_neg, AddUnits.neg_mul_neg]; trans g (mx * my)
    iterate 4
      · exact (congr_arg _ (map_mul f ..).symm).trans (l.lift_eq ..)
      · simp [IsAddUnit.liftRight]

@[simp] theorem liftNonUnitalRingHom_eq {r : R} : liftNonUnitalRingHom hf hg (f r) = g r :=
  LocalizationMap.lift_eq ..

theorem liftNonUnitalRingHom_unique {j : S →ₙ+* T} (hj : ∀ x, j (f x) = g x) :
    liftNonUnitalRingHom hf hg = j :=
  DFunLike.ext _ _ (DFunLike.congr_fun
    ((⟨f, hf⟩ : LocalizationMap M S).lift_unique (g := (g : R →+ T)) hg (j := (j : S →+ T)) hj) ·)

/-- If `f : R →ₙ+* S` and `g : R →ₙ+* T` are localization maps for the same additive submonoid `S`,
we get a ring isomorphism between `S` and `T`. -/
noncomputable def ringEquiv (hf : IsLocalizationMap M f) (hg : IsLocalizationMap M g) : S ≃* T where
  __ := LocalizationMap.addEquivOfLocalizations (S := M) (N := S) (P := T) ⟨f, hf⟩ ⟨g, hg⟩
  map_mul' := (liftNonUnitalRingHom ..).map_mul

end NonUnital

section Unital

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring T] {M : AddSubmonoid R}
variable [FunLike F R S] [NonUnitalRingHomClass F R S] {f : F} (hf : IsLocalizationMap M f)
variable [FunLike G R T] [RingHomClass G R T] {g : G} (hg : ∀ m : M, IsAddUnit (g m))

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of semirings
`g : R →+* T` such that `g y` is additively invertible for all `y : M`, the homomorphism
induced from `S` to `T` sending `z : S` to `g x - g y`, where `(x, y) : R × M` are such that
`z = f x - f y`. -/
noncomputable def liftRingHom : S →+* T where
  __ := hf.liftNonUnitalRingHom hg
  map_one' := by rw [← hf.map_one]; exact (liftNonUnitalRingHom_eq ..).trans (map_one g)

@[simp] theorem liftRingHom_eq {r : R} : liftRingHom hf hg (f r) = g r := LocalizationMap.lift_eq ..

theorem liftRingHom_unique {j : S →+* T} (hj : ∀ x, j (f x) = g x) : liftRingHom hf hg = j :=
  DFunLike.ext _ _ (DFunLike.congr_fun
    ((⟨f, hf⟩ : LocalizationMap M S).lift_unique (g := (g : R →+ T)) hg (j := (j : S →+ T)) hj) ·)

end Unital

end IsLocalizationMap

section Top

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G]

open TensorProduct in
/-- The Grothendieck group of an additive monoid is isomorphic to
its tensor product with `ℤ` over `ℕ`. -/
noncomputable def LocalizationMap.addMonoidHomTensor (f : LocalizationMap (⊤ : AddSubmonoid M) G) :
    G ≃+ ℤ ⊗[ℕ] M where
  __ := f.lift (g := TensorProduct.mk ℕ ℤ M 1) fun _ ↦ AddGroup.isAddUnit _
  invFun := liftAddHom (zmultiplesHom _ f.toAddMonoidHom)
      fun n z r ↦ by simp [mul_comm, mul_smul]
  left_inv g := by simp [lift_apply, IsAddUnit.liftRight, ← sec_spec]
  right_inv x := x.induction_on (by simp)
    (fun z m ↦ by simp [← tmul_eq_smul_one_tmul]) (by simp+contextual)

variable (M) in
open LocalizationMap in
/-- The map from an additive monoid `M` to `ℤ ⊗[ℕ] M` given by `m ↦ 1 ⊗ₜ m`
is a localization map. -/
theorem isLocalizationMap_tensorProductMk :
    IsLocalizationMap (⊤ : AddSubmonoid M) (TensorProduct.mk ℕ ℤ M 1) := by
  let l := AddLocalization.addMonoidOf (⊤ : AddSubmonoid M)
  convert (ofAddEquivOfLocalizations l l.addMonoidHomTensor).isLocalizationMap
  exact funext fun _ ↦ .symm <| (ofAddEquivOfLocalizations_apply ..).trans (l.lift_eq ..)

theorem isLocalizationMap_iff_isTensorProduct (f : M →ₗ[ℕ] G) :
    IsLocalizationMap ⊤ f ↔ IsTensorProduct (zmultiplesHom _ f).toNatLinearMap where
  mp h := (⟨f.toAddHom, h⟩ : LocalizationMap ⊤ G).addMonoidHomTensor.symm.bijective
  mpr h := by
    convert (isLocalizationMap_tensorProductMk M).comp_addEquiv h.equiv.toAddEquiv
    ext; simp

theorem isLocalizationMap_iff_isBaseChange (f : M →ₗ[ℕ] G) :
    IsLocalizationMap ⊤ f ↔ IsBaseChange ℤ f := isLocalizationMap_iff_isTensorProduct f

end Top

theorem isLocalizationMap_iff_isPushout {R S : Type*} [CommSemiring R] [CommRing S] [Algebra R S] :
    IsLocalizationMap ⊤ (algebraMap R S) ↔ Algebra.IsPushout ℕ ℤ R S :=
  (isLocalizationMap_iff_isBaseChange (algebraMap R S).toNatLinearMap).trans
    (Algebra.isPushout_iff ..).symm

end AddSubmonoid

namespace Algebra.GrothendieckAddGroup

variable (R M : Type*) [AddCommMonoid M]

instance [Semiring R] [Module R M] : Module R (GrothendieckAddGroup M) :=
  inferInstanceAs <| Module R <| AddLocalization (⊤ : Submodule R M).toAddSubmonoid

section Mul

variable [AddCommMonoid R] [Mul R] [LeftDistribClass R] [RightDistribClass R]

instance : Mul (GrothendieckAddGroup R) :=
  AddLocalization.instMul _ (fun _ _ _ ↦ ⟨⟩) fun _ _ _ ↦ ⟨⟩

instance : LeftDistribClass (GrothendieckAddGroup R) :=
  AddLocalization.instLeftDistribClass ⊤ (fun _ _ _ ↦ ⟨⟩) fun _ _ _ ↦ ⟨⟩

instance : RightDistribClass (GrothendieckAddGroup R) :=
  AddLocalization.instRightDistribClass ⊤ (fun _ _ _ ↦ ⟨⟩) fun _ _ _ ↦ ⟨⟩

end Mul

instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocRing (GrothendieckAddGroup R) where
  __ := AddLocalization.instNonUnitalNonAssocSemiring ⊤ (fun _ _ _ ↦ ⟨⟩) fun _ _ _ ↦ ⟨⟩
  __ : AddCommGroup _ := inferInstance

/-- The non-unital ring homomorphism from a semiring to its Grothendieck ring. -/
protected abbrev nonUnitalRingHom [NonUnitalNonAssocSemiring R] :
    R →ₙ+* GrothendieckAddGroup R :=
  AddLocalization.nonUnitalRingHom ⊤ (fun _ _ _ ↦ ⟨⟩) fun _ _ _ ↦ ⟨⟩

instance [NonUnitalNonAssocSemiring R] : DistribSMul R (GrothendieckAddGroup R) :=
  AddLocalization.instDistribSMul ⊤ fun _ _ _ ↦ ⟨⟩

instance [NonUnitalSemiring R] : NonUnitalRing (GrothendieckAddGroup R) where
  __ := AddLocalization.instNonUnitalSemiring ⊤ (fun _ _ _ ↦ ⟨⟩) fun _ _ _ ↦ ⟨⟩
  __ : AddCommGroup _ := inferInstance

instance [NonAssocSemiring R] : NonAssocRing (GrothendieckAddGroup R) where
  __ := AddLocalization.instNonAssocSemiring ⊤ (fun _ _ _ ↦ ⟨⟩) fun _ _ _ ↦ ⟨⟩
  __ : AddCommGroup _ := inferInstance

theorem isLocalizationMap_smul_one [NonAssocSemiring R] :
    (⊤ : AddSubmonoid R).IsLocalizationMap fun r ↦ r • (1 : GrothendieckAddGroup R) :=
  AddLocalization.isLocalizationMap_smul_one ⊤ _ _

instance [NonAssocSemiring R] [IsCancelAdd R] : FaithfulSMul R (GrothendieckAddGroup R) :=
  AddLocalization.faithfulSMul_of_isCancelAdd ⊤ (fun _ _ _ ↦ ⟨⟩) fun _ _ _ ↦ ⟨⟩

/-- The ring homomorphism from a semiring to its Grothendieck ring. -/
protected abbrev ringHom [NonAssocSemiring R] : R →+* GrothendieckAddGroup R :=
  AddLocalization.ringHom ⊤ (fun _ _ _ ↦ ⟨⟩) fun _ _ _ ↦ ⟨⟩

instance [Semiring R] : Ring (GrothendieckAddGroup R) where

instance [NonUnitalNonAssocCommSemiring R] :
    NonUnitalNonAssocCommRing (GrothendieckAddGroup R) where
  __ := AddLocalization.instNonUnitalNonAssocCommSemiring ⊤ fun _ _ _ ↦ ⟨⟩
  __ : AddCommGroup _ := inferInstance

instance [NonUnitalCommSemiring R] : NonUnitalCommRing (GrothendieckAddGroup R) where
  __ := AddLocalization.instNonUnitalCommSemiring ⊤ fun _ _ _ ↦ ⟨⟩
  __ : AddCommGroup _ := inferInstance

instance [CommSemiring R] : CommRing (GrothendieckAddGroup R) where

instance [CommSemiring R] : Algebra R (GrothendieckAddGroup R) :=
  inferInstanceAs <| Algebra R <| AddLocalization (⊤ : Ideal R).toAddSubmonoid

instance (R) [CommSemiring R] : Algebra.IsPushout ℕ ℤ R (GrothendieckAddGroup R) :=
  AddSubmonoid.isLocalizationMap_iff_isPushout.mp (AddLocalization.addMonoidOf _).isLocalizationMap

instance (R) [CommSemiring R] : Algebra.IsPushout ℕ R ℤ (GrothendieckAddGroup R) :=
  .symm inferInstance

end Algebra.GrothendieckAddGroup
