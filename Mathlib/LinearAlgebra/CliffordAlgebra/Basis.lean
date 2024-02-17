/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Data.Sign

variable  (ι : Type) [LinearOrder ι]

noncomputable section

-- a list of indices, sorted
abbrev Model.Index := {l : List ι // l.Sorted (· < ·) }


variable {R : Type*} [CommRing R]

variable {M : Type*} [AddCommGroup M] [Module R M]


def Model (_Q : QuadraticForm R M) := Model.Index ι →₀ R


variable (Q : QuadraticForm R M)
instance : AddCommGroup (Model ι Q) := inferInstanceAs <| AddCommGroup (Model.Index ι →₀ R)
instance : Module R (Model ι Q) := inferInstanceAs <| Module R (Model.Index ι →₀ R)

variable {Q ι} in
def Model.ofFinsupp : (Model.Index ι →₀ R) ≃ₗ[R] Model ι Q :=
  LinearEquiv.refl _ _

instance : One (Model ι Q) where
  one := Model.ofFinsupp <| Finsupp.single ⟨[], by simp⟩ 1

@[simp]
lemma Model.ofFinsupp_symm_one :
    Model.ofFinsupp.symm (1 : Model ι Q) = Finsupp.single ⟨[], by simp⟩ 1 := by
  rfl

variable {ι}

@[simps]
def Model.Index.single (i : ι) : Model.Index ι := ⟨[i], by simp⟩

def Model.single (i : ι) : Model ι Q :=
  Model.ofFinsupp <| Finsupp.single (Model.Index.single i) 1

@[simp]
lemma Model.ofFinsupp_single_single (i : ι) :
  Model.ofFinsupp (Finsupp.single (.single i) 1) = Model.single Q i := rfl


def merge_with_sign : SignType → List ι → List ι → List ι × SignType
  | σ, [], l' => ⟨l',σ⟩
  | σ, l, [] => ⟨l,σ⟩
  | σ, a :: l, b :: l' =>
    if a=b
    then ⟨[],0⟩ -- the first entry will be ignored later anyway
    else if a < b
    then ⟨a :: (merge_with_sign σ l (b :: l')).1,σ⟩
    else
      let ⟨m,s⟩ := merge_with_sign σ (a :: l) l'
      ⟨b :: m,s*(-1)^(List.length l +1)⟩
  termination_by s l₁ l₂ => List.length l₁ +  List.length l₂

example : merge_with_sign 1 [1] [2] = ⟨[1,2],1⟩  := by
  unfold merge_with_sign
  simp

example : merge_with_sign 1 [2] [1] = ⟨[1,2],-1⟩  := by
  unfold merge_with_sign
  simp

example : merge_with_sign 1 [2] [2] = ⟨[],0⟩  := by
  unfold merge_with_sign
  simp

example : merge_with_sign 1 [4] [1,2,3] = ⟨[1,2,3,4],-1⟩  := by
  unfold merge_with_sign
  simp


def mul_helper : Model.Index ι → Model.Index ι → Model.Index ι × SignType := by
  intro l k
  let ms := merge_with_sign 1 l.1 k.1
  refine (⟨ms.1,?_⟩,ms.2)
  sorry

lemma single_mul_single_helper (i : ι) :
  (mul_helper (Model.Index.single i) (Model.Index.single i)).2 = 0 := by
  sorry

-- def list_sort_concat
open scoped BigOperators

variable {Q}
def mul (v w : Model ι Q) : Model ι Q :=
  (Model.ofFinsupp.symm v).sum fun i vi ↦
    (Model.ofFinsupp.symm w).sum fun j wj ↦
      let ⟨k,s⟩:=mul_helper i j
      Model.ofFinsupp <| Finsupp.single k (s * vi * wj)

instance : Mul (Model ι Q) where
  -- multiply pairwise
  mul v w :=
  (Model.ofFinsupp.symm v).sum fun i vi ↦
    (Model.ofFinsupp.symm w).sum fun j wj ↦
      let ⟨k,s⟩:=mul_helper i j
      Model.ofFinsupp <| Finsupp.single k (s * vi * wj)

#print instMulModel

lemma single_mul_single (i : ι) : Model.single Q i * Model.single Q i = 0 := by
  change Finsupp.sum _ _ = _
  dsimp only [mul,Model.single]
  simp
  sorry

#check Finsupp.sum_single_index


instance : Ring (Model ι Q) where
  -- inheritance in lean 4 is (somewhat) broken currently
  __ := inferInstanceAs (AddCommGroup (Model ι Q))

  left_distrib := sorry
  right_distrib := sorry

  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

instance : Algebra R (Model ι Q) where
  toFun := Finsupp.single ⟨[], by simp⟩
  map_one' := rfl
  map_mul' := sorry
  -- we came up with this by using `by simp`
  map_zero' := Finsupp.single_zero _
  map_add' x y := sorry
  commutes' r x := sorry
  smul_def' r x := sorry

variable {r: R}
@[simp]
lemma Model.ofFinsupp_symm_algebra_map :
    Model.ofFinsupp.symm (algebraMap R (Model ι Q) r) = Finsupp.single ⟨[], by simp⟩ r := by
  rfl


noncomputable def model_of_free_vsp : (ι →₀ R) →ₗ[R] Model ι Q :=
  Model.ofFinsupp.toLinearMap ∘ₗ Finsupp.lmapDomain R R (fun i ↦ Model.Index.single i)

@[simp]
lemma model_of_free_vsp_single (i : ι) :
    model_of_free_vsp (Finsupp.single i (1 : R)) = Model.single Q i := by
  unfold model_of_free_vsp
  simp

lemma two_vectors_square_zero (m: ι →₀ R) :
  model_of_free_vsp m * model_of_free_vsp m = 0 := by
  sorry



variable {A : Type} [Ring A] [Algebra R A]
variable {M : Type} [AddCommGroup M] [Module R M]

def liftToFun ( f : (ι →₀ R) →ₗ[R] A ) ( hf : ∀ m, f m * f m = 0 ) : (Model ι Q →ₐ[R] A) where
  toFun m := (Model.ofFinsupp.symm m).sum $
    λ ⟨i, _⟩ r =>
    r • (
      List.prod (
        List.map (fun x => f (Finsupp.single x 1)) i) : A)
  -- Alternative:
  -- toFun m := m.sum
  --   λ ⟨basis_elem, _⟩ scaler =>
  --     ((List.map f (List.map (λ v => by exact Finsupp.single v 1) basis_elem)).prod)
  map_one' := by simp
  map_mul' := sorry
  map_zero' := by simp
  map_add' x y:= by
    simp [Finsupp.sum_add_index, add_smul]
  commutes' r := by
    simp
    rw [@Algebra.algebraMap_eq_smul_one]

def liftInvFun (F : Model ι Q →ₐ[R] A) : { f : (ι →₀ R) →ₗ[R] A // ∀ m, f m * f m = 0 } where
  val := {
    toFun := fun v => F (model_of_free_vsp v)
    map_add' := by
      simp
    map_smul' := by
      simp
  }
  property := by
    intro m
    simp
    rw [← F.map_mul]
    rw [two_vectors_square_zero]
    simp


@[simps! symm_apply]
def lift :
    { f : (ι →₀ R) →ₗ[R] A // ∀ m, f m * f m = 0 }
    ≃ (Model ι Q →ₐ[R] A)
    where
      toFun := by
        intro f
        exact liftToFun f.val f.property
      invFun := liftInvFun
      left_inv := sorry
      right_inv := sorry

@[simp]
lemma liftToFun_composed_single (i : ι) (f : (ι →₀ R) →ₗ[R] A) (hf) :
    liftToFun f hf (Model.single Q i) = f (Finsupp.single i 1) := by
  sorry


@[ext high]
theorem Model.hom_ext {f g : Model ι Q →ₐ[R] A} :
    f.toLinearMap.comp (model_of_free_vsp) = g.toLinearMap.comp (model_of_free_vsp) → f = g := by
  intro h
  apply lift.symm.injective
  rw [lift_symm_apply, lift_symm_apply]
  sorry
  -- intro h
  -- apply (lift Q).symm.injective
  -- rw [lift_symm_apply, lift_symm_apply]
  -- simp only [h]
