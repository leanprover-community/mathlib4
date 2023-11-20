import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.GroupTheory.QuotientGroup

set_option autoImplicit false

open TensorProduct MulOpposite

section defs

universe uR uM uN uX

variable (R : Type uR) [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module Rᵐᵒᵖ M]
variable {N : Type uN} [AddCommMonoid N] [Module R N]
variable {X : Type uX} [AddCommMonoid X]

variable (M N X) in
structure BalancedBiAddMonoidHom extends (M →+ N →+ X) where
(balanced : ∀ (r : R) (m : M) (n : N), toAddMonoidHom (op r • m) n = toAddMonoidHom m (r • n))

instance BalancedBiAddMonoidHom.funLike :
    FunLike (BalancedBiAddMonoidHom R M N X) M (fun _ => N → X) where
  coe f := fun m => fun n => f.toAddMonoidHom m n
  coe_injective' f g h := by
    cases f
    cases g
    congr
    exact AddMonoidHom.ext fun m => AddMonoidHom.ext fun n => congr_fun (congr_fun h m) n

instance BalancedBiAddMonoidHom.addMonoidHomClass :
    AddMonoidHomClass (BalancedBiAddMonoidHom R M N X) M (N →+ X) where
  coe f m := f.toAddMonoidHom m
  coe_injective' f g h := FunLike.ext _ _ fun m => funext fun n =>
    FunLike.congr_fun (congr_fun h m) n
  map_add f _ _ := FunLike.ext _ _ fun _ => by
    exact FunLike.congr_fun (f.toAddMonoidHom.map_add _ _) _
  map_zero f := FunLike.ext _ _ fun _ => by
    exact FunLike.congr_fun (f.toAddMonoidHom.map_zero) _

@[simp] lemma BalancedBiAddMonoidHom.apply_apply_zero (f : BalancedBiAddMonoidHom R M N X) (m : M) :
    f m 0 = 0 :=
  (f.toAddMonoidHom m).map_zero

lemma BalancedBiAddMonoidHom.apply_apply_add (f : BalancedBiAddMonoidHom R M N X)
    (m : M) (n n' : N):
    f m (n + n') = f m n + f m n' :=
  (f.toAddMonoidHom m).map_add n n'

@[simp] lemma BalancedBiAddMonoidHom.apply_zero_apply (f : BalancedBiAddMonoidHom R M N X) (n : N) :
    f 0 n = 0 :=
  FunLike.congr_fun f.toAddMonoidHom.map_zero _

lemma BalancedBiAddMonoidHom.apply_add_apply (f : BalancedBiAddMonoidHom R M N X)
    (m m' : M) (n : N):
    f (m + m') n = f m n + f m' n :=
  FunLike.congr_fun (f.toAddMonoidHom.map_add m m') n

lemma BalancedBiAddMonoidHom.apply_smul_apply (f : BalancedBiAddMonoidHom R M N X)
    (r : R) (m : M) (n : N) :
    f (op r • m) n = f m (r • n) :=
  f.balanced r m n

class IsTensorProduct (tmul : BalancedBiAddMonoidHom R M N X) :=
(lift ⦃P : Type uX⦄ [AddCommMonoid P] (_ : BalancedBiAddMonoidHom R M N P) : X →+ P)
(lift_comp ⦃P : Type uX⦄ [AddCommMonoid P] (f : BalancedBiAddMonoidHom R M N P) (m : M) (n : N) :
  lift f (tmul m n) = f m n)
(lift_uniq ⦃P : Type uX⦄ [AddCommMonoid P] (f : BalancedBiAddMonoidHom R M N P) (fHat : X →+ P) :
  (∀ m n, fHat (tmul m n) = f m n) → lift f = fHat)

end defs

section addGroups
-- I feel like these should work for "semimodules" as well, but I don't know how to prove it
open IsTensorProduct

universe uR uM uN uX

variable (R : Type uR) [Semiring R]
variable {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable {N : Type uN} [AddCommGroup N] [Module R N]
variable {X : Type uX} [AddCommGroup X]

variable (tmul : BalancedBiAddMonoidHom R M N X) [IsTensorProduct R tmul]

lemma IsTensorProduct.mem_closure (x : X) :
    x ∈ AddSubgroup.closure { y | ∃ (m : M) (n : N), y = tmul m n } := by
  let l : AddSubgroup X := AddSubgroup.closure { y | ∃ (m : M) (n : N), y = tmul m n }
  let Q := X ⧸ l
  let b : BalancedBiAddMonoidHom R M N Q :=
  { toFun := fun m =>
    { toFun := fun n => QuotientAddGroup.mk' _ (tmul m n)
      map_zero' := by
        dsimp; rw [tmul.apply_apply_zero]; rfl
      map_add' := fun _ _ => by
        dsimp; rw [tmul.apply_apply_add]; rfl }
    map_zero' := FunLike.ext _ _ fun _ => by
      dsimp; rw [tmul.apply_zero_apply]; rfl
    map_add' := fun _ _ => FunLike.ext _ _ fun _ => by
      dsimp; rw [tmul.apply_add_apply]; rfl
    balanced := fun r m n => by
      dsimp; rw [tmul.apply_smul_apply] }
  let q : X →+ Q := lift tmul b
  let q' : X →+ Q := QuotientAddGroup.mk' _

  have eq1 : q = 0
  · refine lift_uniq (tmul := tmul) b 0 fun m n => ?_
    simp only [AddMonoidHom.zero_apply, QuotientAddGroup.mk'_apply]
    symm
    erw [QuotientAddGroup.eq_zero_iff]
    exact AddSubgroup.subset_closure ⟨m, n, rfl⟩
  have eq2 : q = q'
  · refine lift_uniq (tmul := tmul) b q' fun m n => rfl
  rw [eq1] at eq2
  exact (QuotientAddGroup.eq_zero_iff _).mp (FunLike.congr_fun eq2 x).symm

@[elab_as_elim]
lemma IsTensorProduct.induction {motive : X → Prop}
    (tensor : ∀ m n, motive (tmul m n))
    (add : ∀ x x', motive x → motive x' → motive (x + x'))
    (neg : ∀ x, motive x → motive (-x)) :
    ∀ x, motive x :=
  fun x => AddSubgroup.closure_induction (mem_closure R tmul x)
    (by rintro _ ⟨m, n, rfl⟩; exact tensor _ _)
    (by convert tensor 0 0 using 1; rw [tmul.apply_apply_zero]) add neg

end addGroups

section module_structure

open IsTensorProduct

section left_mod

universe uA uB uC uR

variable (A : Type uA) [Semiring A]
variable (B : Type uB) [Semiring B]
variable (C : Type uC) [Semiring C]
variable (R : Type uR) [Semiring R]

universe uM uN uX

-- M is (A, B)-bimodule
variable (M : Type uM) [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
-- N is left B-module
variable (N : Type uN) [AddCommGroup N] [Module B N]
variable (X : Type uX) [AddCommGroup X]
variable (tmul : BalancedBiAddMonoidHom B M N X) [IsTensorProduct B tmul]
-- Then X is a left A-module

variable {A B M N X}

def IsTensorProduct.leftSmul (a : A) : X →+ X := IsTensorProduct.lift tmul
{ toFun := fun m =>
  { toFun := fun n => tmul (a • m) n
    map_zero' := show tmul _ _ = _ by rw [tmul.apply_apply_zero]
    map_add' := fun n n' => show tmul _ _= tmul _ _ + tmul _ _ by rw [tmul.apply_apply_add] }
  map_zero' := FunLike.ext _ _ fun n => show tmul _ _ = _ by
    rw [smul_zero, tmul.apply_zero_apply, AddMonoidHom.zero_apply]
  map_add' := fun m m' => FunLike.ext _ _ fun n => show tmul _ _ = tmul _ _ + tmul _ _ by
    rw [smul_add, tmul.apply_add_apply]
  balanced := fun r' m n => by
    dsimp
    rw [smul_comm, tmul.apply_smul_apply] }

@[simp] lemma IsTensorProduct.leftSmul_tmul (a : A) (m : M) (n : N) :
    leftSmul tmul a (tmul m n) = tmul (a • m) n := by
  erw [lift_comp]; rfl

lemma IsTensorProduct.leftSmul.one_smul (x : X) : leftSmul tmul (1 : A) x = x := by
  suffices h : leftSmul tmul (1 : A) = AddMonoidHom.id _
  · rw [h]; rfl
  refine lift_uniq _ _ fun m n => ?_
  change tmul m n = tmul (1 • m) n
  rw [_root_.one_smul]

lemma IsTensorProduct.leftSmul.mul_smul (a a' : A) (x : X) :
    leftSmul tmul (a * a') x =
    leftSmul tmul a (leftSmul tmul a' x) := by
  refine IsTensorProduct.induction B tmul ?_ ?_ ?_ x
  · intro m n
    simp only [leftSmul_tmul]
    rw [MulAction.mul_smul]
  · intro x x' hx hx'
    simp only [map_add, hx, hx']
  · intro x
    simp only [map_neg, neg_inj, imp_self]

def IsTensorProduct.leftSmul.smul : SMul A X where
  smul r := leftSmul tmul r

def IsTensorProduct.leftSmul.mulAction : MulAction A X where
  __ := leftSmul.smul tmul
  one_smul := leftSmul.one_smul tmul
  mul_smul := leftSmul.mul_smul tmul

def IsTensorProduct.leftSmul.distribMulAction : DistribMulAction A X where
  __ := leftSmul.mulAction tmul
  smul_zero _ := show leftSmul tmul _ _ = 0 by simp
  smul_add a x y := show leftSmul tmul _ _ = leftSmul tmul _ _ + leftSmul tmul _ _ by simp

def IsTensorProduct.leftModule : Module A X where
  __ := leftSmul.distribMulAction tmul
  smul_add a x y := by simp
  add_smul a b x := show leftSmul tmul _ _ = leftSmul tmul _ _ + leftSmul tmul _ _ by
    refine IsTensorProduct.induction B tmul ?_ ?_ ?_ x
    · intro m n; simp only [leftSmul_tmul, add_smul, tmul.apply_add_apply]
    · intro x y hx hy
      simp only [map_add, hx, hy]
      abel
    · intro x hx
      simp only [map_neg, hx]
      abel
  zero_smul x := show leftSmul tmul _ _ = 0 by
    refine IsTensorProduct.induction B tmul ?_ ?_ ?_ x
    · intro m n; simp only [leftSmul_tmul, zero_smul, tmul.apply_zero_apply]
    · intro x y hx hy
      simp only [map_add, hx, hy]
      abel
    · intro x hx
      simp only [map_neg, hx]
      abel

end left_mod

section right_mod

universe uA uB uC uR

variable (A : Type uA) [Semiring A]
variable (B : Type uB) [Semiring B]
variable (C : Type uC) [Semiring C]
variable (R : Type uR) [Semiring R]

universe uM uN uX

-- M is right B-module
variable (M : Type uM) [AddCommGroup M] [Module Bᵐᵒᵖ M]
-- N is (B, C)-bimodule
variable (N : Type uN) [AddCommGroup N] [Module B N] [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]
variable (X : Type uX) [AddCommGroup X]
variable (tmul : BalancedBiAddMonoidHom B M N X) [IsTensorProduct B tmul]
-- then X is right C module

variable {A B C M N X}

def IsTensorProduct.rightSmul (r : Cᵐᵒᵖ) : X →+ X := lift tmul
{ toFun := fun m =>
  { toFun := fun n => tmul m (r • n)
    map_zero' := show tmul _ (r • (0 : N)) = _ by
      rw [smul_zero, tmul.apply_apply_zero]
    map_add' := fun n n' => show tmul _ _= tmul _ _ + tmul _ _ by
      rw [smul_add, tmul.apply_apply_add] }
  map_zero' := FunLike.ext _ _ fun n => show tmul _ _ = _ by
    rw [tmul.apply_zero_apply, AddMonoidHom.zero_apply]
  map_add' := fun m m' => FunLike.ext _ _ fun n => show tmul _ _ = tmul _ _ + tmul _ _ by
    rw [tmul.apply_add_apply]
  balanced := fun r' m n => by
    dsimp
    rw [tmul.apply_smul_apply, smul_comm] }

@[simp] lemma IsTensorProduct.rightSmul_tmul (a : Cᵐᵒᵖ) (m : M) (n : N) :
    rightSmul tmul a (tmul m n) = tmul m (a • n) := by
  erw [lift_comp]; rfl

lemma IsTensorProduct.rightSmul.one_smul (x : X) : rightSmul tmul (1 : Cᵐᵒᵖ) x = x := by
  suffices h : rightSmul tmul (1 : Cᵐᵒᵖ) = AddMonoidHom.id _
  · rw [h]; rfl
  refine lift_uniq _ _ fun m n => ?_
  change tmul m n = tmul m (1 • n)
  rw [_root_.one_smul]

lemma IsTensorProduct.rightSmul.mul_smul (a a' : Cᵐᵒᵖ) (x : X) :
    rightSmul tmul (a * a') x =
    rightSmul tmul a (rightSmul tmul a' x) := by
  refine IsTensorProduct.induction B tmul ?_ ?_ ?_ x
  · intro m n
    simp only [rightSmul_tmul]
    rw [MulAction.mul_smul]
  · intro x x' hx hx'
    simp only [map_add, hx, hx']
  · intro x
    simp only [map_neg, neg_inj, imp_self]

def IsTensorProduct.rightSmul.smul : SMul Cᵐᵒᵖ X where
  smul r := rightSmul tmul r

def IsTensorProduct.rightSmul.mulAction : MulAction Cᵐᵒᵖ X where
  __ := rightSmul.smul tmul
  one_smul := rightSmul.one_smul tmul
  mul_smul := rightSmul.mul_smul tmul

def IsTensorProduct.rightSmul.distribMulAction : DistribMulAction Cᵐᵒᵖ X where
  __ := rightSmul.mulAction tmul
  smul_zero _ := show rightSmul tmul _ _ = 0 by simp
  smul_add a x y := show rightSmul tmul _ _ = rightSmul tmul _ _ + rightSmul tmul _ _ by simp

def IsTensorProduct.rightModule : Module Cᵐᵒᵖ X where
  __ := rightSmul.distribMulAction tmul
  smul_add a x y := by simp
  add_smul a b x := show rightSmul tmul _ _ = rightSmul tmul _ _ + rightSmul tmul _ _ by
    refine IsTensorProduct.induction B tmul ?_ ?_ ?_ x
    · intro m n; simp only [rightSmul_tmul, add_smul, tmul.apply_apply_add]
    · intro x y hx hy
      simp only [map_add, hx, hy]
      abel
    · intro x hx
      simp only [map_neg, hx]
      abel
  zero_smul x := show rightSmul tmul _ _ = 0 by
    refine IsTensorProduct.induction B tmul ?_ ?_ ?_ x
    · intro m n; simp only [rightSmul_tmul, zero_smul, tmul.apply_apply_zero]
    · intro x y hx hy
      simp only [map_add, hx, hy]
      abel
    · intro x hx
      simp only [map_neg, hx]
      abel

end right_mod

end module_structure

noncomputable section examples

universe uR uS uM uN
variable (R : Type uR) [CommRing R]
variable (S : Type uS) [CommRing S]
variable (M : Type uM) [AddCommGroup M] [Module R M]
variable (N : Type uN) [AddCommGroup N] [Module R N] [Module S N] [SMulCommClass R S N]

local instance : Module Rᵐᵒᵖ M := Module.compHom M ((RingHom.id _).fromOpposite mul_comm)
local instance : Module Sᵐᵒᵖ N := Module.compHom N ((RingHom.id _).fromOpposite mul_comm)
local instance : SMulCommClass R Sᵐᵒᵖ N where
  smul_comm r s n := smul_comm r s.unop n

@[simps]
noncomputable def TensorProduct.mkAddHom : M →+ N →+ M ⊗[R] N where
  toFun := fun m =>
  { toFun := (m ⊗ₜ ·)
    map_zero' := tmul_zero _ _
    map_add' := tmul_add _ }
  map_zero' := by aesop
  map_add' := fun _ _ => FunLike.ext _ _ fun _ => add_tmul _ _ _

noncomputable instance isTensorProduct1 : IsTensorProduct R
  (⟨TensorProduct.mkAddHom R M N, fun r m n => smul_tmul r m n⟩ :
    BalancedBiAddMonoidHom R M N (M ⊗[R] N)) where
  lift P _ f := TensorProduct.liftAddHom f.toAddMonoidHom f.balanced
  lift_comp P _ f m n := rfl
  lift_uniq P _ f fHat H := FunLike.ext _ _ fun x => x.induction_on (by aesop)
    (fun m n => by rw [show fHat (m ⊗ₜ n) = _ from H m n]; rfl)
    (fun z z' h h' => by simp only [map_add, h, h'])

instance : Module S (M ⊗[R] N) :=
  have i1 := IsTensorProduct.rightModule (B := R) (C := S) (M := M) (N := N) (X := M ⊗[R] N)
  @Module.compHom _ _ (M ⊗[R] N) _ _ (@i1 _ (isTensorProduct1 R M N)) _
    ((RingHom.id S).toOpposite mul_comm)

example (s : S) (m : M) (n : N) : s • (m ⊗ₜ[R] n) = m ⊗ₜ (s • n) := rfl

end examples
