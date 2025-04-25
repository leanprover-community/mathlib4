/-
Copyright (c) 2025 Hanliu Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang ,Hanliu Jiang
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Algebra.DirectSum.Basic

set_option maxHeartbeats 1000000000000000000000000000000000000000000
set_option synthInstance.maxHeartbeats 1000000000000000000000000000000

suppress_compilation

variable {R : Type*} [CommRing R](I:Ideal R)
variable {S : Type*} [CommRing S][Algebra R S](J:Ideal S)
variable {M : Type*} [AddCommGroup M] [Module R M](N : Submodule R M)

variable {P : Type*} [AddCommGroup P] [Module R P]


namespace LinearMap
#check S
#check Submodule.mapQ


private def liftQ1 (f : S →ₗ[R] M) (hp:
J.1 ≤ (ker f).1):
    S ⧸J →ₗ[R] M :=
    { QuotientAddGroup.lift J.toAddSubgroup
    f.toAddMonoidHom hp with
    map_smul' := by rintro a ⟨x⟩; exact f.map_smulₛₗ a x }
private def mapQ1 (f : S →ₗ[R] M) (hp:
J.1 ≤ (Submodule.comap f N).1)
 :  S ⧸ J →ₗ[R] M ⧸ N:=
liftQ1  J (N.mkQ.comp f) <| by simpa [ker_comp] using hp
private def AlgebrareduceModIdealAux (f : S →ₗ[R] M)(hp:
(J • ⊤ : Submodule S S).1 ≤ (Submodule.comap f (I • ⊤ : Submodule R M)).1)
 :
   S ⧸ (J • ⊤ : Submodule S S) →ₗ[R] M ⧸ (I • ⊤ : Submodule R M) :=
  mapQ1 (J • ⊤ : Submodule S S) (I • ⊤ : Submodule R M) f
    (fun x hx ↦ by exact hp hx)

end LinearMap
namespace AdicCompletion
variable (f : S →ₗ[R] M) (hp:
(J • ⊤ : Submodule S S).1 ≤ (Submodule.comap f (I • ⊤ : Submodule R M)).1)
open LinearMap
private def help1:R →+* (AdicCauchySequence J S) where
  toFun a:= (algebraMap S (AdicCauchySequence J S)) ((algebraMap R S) a)
  map_one' :=by simp
  map_mul' _ _ :=by simp
  map_zero' :=by simp
  map_add' :=by simp
instance : Algebra R (AdicCauchySequence J S) :=by
 refine RingHom.toAlgebra (help1 J)
lemma Complete (n:ℕ):(J^n • ⊤ : Submodule S S).1 ≤
 (Submodule.comap f (I^n • ⊤ : Submodule R M)).1 :=sorry



def map  : AdicCauchySequence J S →ₗ[R] AdicCauchySequence I M where
  toFun a:= {
    val n:= f (a n)
    property :=by
     intro m n hmn
     rcases a with ⟨a1,a2⟩
     simp
     unfold IsAdicCauchy at a2



     sorry
  }
  map_add' a b:=by
    ext n
    simp
  map_smul' r a:=by
    sorry



private def ReduceModIdeal (n:ℕ)
 :
   S ⧸ (J^n • ⊤ : Submodule S S) →ₗ[R] M ⧸ (I^n • ⊤ : Submodule R M) :=
   mapQ1 (J^n • ⊤ : Submodule S S) (I^n • ⊤ : Submodule R M) f (Complete I J f n)
#check (ReduceModIdeal  I J f 1)
def adicCompletionAux  :
    AdicCompletion J S →ₗ[R] AdicCompletion I M :=
  AdicCompletion.lift I (fun n ↦ (ReduceModIdeal  I J f n) ∘ₗ AdicCompletion.eval J S n)
    (fun {m n} hmn ↦ by
     sorry
     )
end AdicCompletion
