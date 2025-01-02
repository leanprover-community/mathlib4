import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.Tactic

variable (R : Type*) [CommSemiring R]

open TensorAlgebra Additive in
inductive SteinbergRel :
    (TensorAlgebra ℤ <| Additive Rˣ) →
    (TensorAlgebra ℤ <| Additive Rˣ) →
    Prop where
  | mk (a b : Rˣ) : (a : R) + b = 1 →
    SteinbergRel (ι _ (ofMul a) * ι _ (ofMul b)) 0

def MilnorK := RingQuot <| SteinbergRel R

instance : Ring (MilnorK R) :=
  inferInstanceAs <| Ring <| RingQuot <| SteinbergRel R

def tensorAlgebraToMilnorK : TensorAlgebra ℤ (Additive Rˣ) →+* MilnorK R :=
  RingQuot.mkRingHom _

namespace MilnorK

variable {R}
def ι : Additive Rˣ →+ MilnorK R :=
  (tensorAlgebraToMilnorK _).toAddMonoidHom.comp <| (TensorAlgebra.ι _).toAddMonoidHom

syntax "{" term,+ "}ₘ" : term

def symbolSingleton (a : Rˣ) : MilnorK R := ι <| .ofMul a
def symbolCons (a : Rˣ) (as : MilnorK R) : MilnorK R := ι (.ofMul a) * as

@[simp]
def symbolCons_add (a : Rˣ) (as bs : MilnorK R) :
    symbolCons a (as + bs) = symbolCons a as + symbolCons a bs :=
  mul_add _ _ _

@[simp]
def symbolCons_mul (a b : Rˣ) (as : MilnorK R) :
    symbolCons (a * b) as = symbolCons a as + symbolCons b as := by
  dsimp [symbolCons]
  simp [ι.map_add, add_mul]

@[simp]
def symbolCons_inv (a : Rˣ) (as : MilnorK R) :
    symbolCons (a⁻¹) as = - symbolCons a as := by
  simp [symbolCons]

macro_rules
  | `({$x:term}ₘ) => `(symbolSingleton $x)
  | `({$x:term, $xs:term,*}ₘ) => `(symbolCons $x {$xs,*}ₘ)

@[app_unexpander symbolCons]
def symbolMulUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $x {$xs,*}ₘ) => `({$x, $xs,*}ₘ)
  | _ => throw ()

@[app_unexpander symbolSingleton]
def symbolSingleUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $x) => `({$x}ₘ)
  | _ => throw ()

@[simp]
lemma ι_mul (x y : Rˣ) : {x * y}ₘ = {x}ₘ + {y}ₘ := by
  simp only [symbolSingleton, ι, ofMul_mul, map_add]

@[simp]
lemma ι_one : {(1 : Rˣ)}ₘ = 0 := by
  simp only [symbolSingleton, ι, ofMul_one, map_zero]

@[simp]
lemma ι_inv (x : Rˣ) : {x⁻¹}ₘ = -{x}ₘ := by
  simp only [symbolSingleton, ι, ofMul_inv, map_neg]

lemma eq_zero_of_steinberg (x y : Rˣ) (h : (x : R) + y = 1) : {x,y}ₘ = 0 := by
  dsimp [symbolSingleton, symbolCons, ι, tensorAlgebraToMilnorK]
  rw [← RingHom.map_mul, ← (RingQuot.mkRingHom (SteinbergRel R)).map_zero]
  apply RingQuot.mkRingHom_rel
  exact SteinbergRel.mk _ _ h

def lift {S : Type*} [Ring S] :
    {f : Additive Rˣ →+ S // ∀ ⦃x y : Rˣ⦄, (x : R) + y = 1 → f (.ofMul x) * f (.ofMul y) = 0 } ≃
    (MilnorK R →+* S) where
  toFun f := RingQuot.lift <| .mk
    (TensorAlgebra.lift _ <| f.val.toIntLinearMap).toRingHom <| by
      rintro x y ⟨a,b,h⟩
      simpa using f.property h
  invFun f := .mk
    (f.toAddMonoidHom.comp ι) <| by
      intro x y h
      simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
        Function.comp_apply]
      rw [← f.map_mul, ← f.map_zero]
      congr 1
      exact eq_zero_of_steinberg _ _ h
  left_inv x := by
    ext t : 2
    dsimp [ι, tensorAlgebraToMilnorK]
    convert RingQuot.lift_mkRingHom_apply _ _ _
    simp only [RingHom.coe_coe, TensorAlgebra.lift_ι_apply, AddMonoidHom.coe_toIntLinearMap]
  right_inv x := by
    apply RingQuot.ringQuot_ext
    apply RingHom.toIntAlgHom_injective
    apply TensorAlgebra.hom_ext
    ext1 t
    simp only [RingHom.toAddMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, LinearMap.coe_comp,
      Function.comp_apply, AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe, RingHom.coe_comp,
      RingQuot.lift_mkRingHom_apply, RingHom.coe_coe, TensorAlgebra.lift_ι_apply,
      AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe]
    rfl

lemma hom_ext {S : Type*} [Ring S] {f g : MilnorK R →+* S}
    (h : ∀ x : Rˣ, f {x}ₘ = g {x}ₘ) : f = g := by
  apply_fun lift.symm
  ext t
  exact h t

variable {F : Type*} [Field F]

@[simp]
lemma mul_neg_self (x : Fˣ) : {x,-x}ₘ = 0 := by
  by_cases h : 1 = x
  · simp [symbolSingleton, symbolCons, ← h]
  · have hx1 : ((1 : F) - x) ≠ 0 := by
      rw [sub_ne_zero]
      contrapose! h
      ext
      assumption
    let y : Fˣ := Units.mk0 _ hx1
    have h' : 1 ≠ x⁻¹ := by
      simp only [ne_eq, one_eq_inv]
      contrapose! h
      exact h.symm
    have hx2 : (1 : F) - ↑(x⁻¹) ≠ 0 := by
      rw [sub_ne_zero]
      contrapose! h'
      ext
      assumption
    let z : Fˣ := Units.mk0 _ hx2
    have : {x, -x}ₘ + {x, -y * x⁻¹}ₘ = 0 := by
      rw [← symbolCons_add, ← ι_mul]
      apply eq_zero_of_steinberg
      simp only [neg_mul, mul_neg, mul_inv_cancel_comm_assoc, neg_neg, Units.val_mk0,
        add_sub_cancel, y]
    calc
      {x, -x}ₘ = -{x, -y * x⁻¹}ₘ := by
        rwa [add_eq_zero_iff_eq_neg] at this
      _ = -{x, z}ₘ := by
        congr 4
        ext
        field_simp [y, z]
      _ = {x⁻¹, z}ₘ := symbolCons_inv _ _ |>.symm
      _ = 0 := by
        apply eq_zero_of_steinberg
        simp [z]

lemma mul_self (x : Fˣ) : {x, x}ₘ = {x, -1}ₘ := by
  conv =>
    enter [1, 2]
    rw [show x = (-x) * (-1) by simp]
  rw [ι_mul, symbolCons_add]
  simp only [mul_add, mul_neg_self, zero_add]

lemma mul_symm_eq_neg_mul (x y : Fˣ) : {x,y}ₘ = -{y,x}ₘ := by
  rw [← add_eq_zero_iff_eq_neg]
  calc
    _ = {x, -x}ₘ + {x, y}ₘ + {y, x}ₘ + {y, -y}ₘ := by simp
    _ = {x * y, -(x * y)}ₘ := by
      rw [symbolCons_mul x y]
      nth_rewrite 1 [show -(x * y) = (-x) * y by simp]
      nth_rewrite 1 [show -(x * y) = x * (-y) by simp]
      simp only [ι_mul, mul_neg_self, zero_add, add_zero, mul_add, symbolCons_add]
    _ = 0 := mul_neg_self _

end MilnorK
