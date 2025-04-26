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
variable (f : S →ₗ[R] M)
open LinearMap
private def help1:R →+* (AdicCauchySequence J S) where
  toFun a:= (algebraMap S (AdicCauchySequence J S)) ((algebraMap R S) a)
  map_one' :=by simp
  map_mul' _ _ :=by simp
  map_zero' :=by simp
  map_add' :=by simp
instance : Algebra R (AdicCauchySequence J S) :=by
 refine RingHom.toAlgebra (help1 J)
#check AddSubmonoid.smul_le
@[simp]
lemma equiv (a:AdicCauchySequence J S)(r:R)(n:ℕ) : (r•a) n =r• (a n) :=by
  have: r• a =((algebraMap R S) r)•a :=by rfl
  rw[this]
  simp
  exact Eq.symm (Algebra.smul_def r (a n))


def mapAlg (hp:∀ n,
(J^n • ⊤ : Submodule S S).1 ≤ (Submodule.comap f
 (I^n • ⊤ : Submodule R M)).1) : AdicCauchySequence J S →ₗ[R] AdicCauchySequence I M where
  toFun a:= ⟨fun n ↦ f (a n), fun {m n} hmn ↦ by
     rcases a with ⟨a1,a2⟩
     simp
     unfold IsAdicCauchy at a2
     have :=a2 hmn
     rw [SModEq.sub_mem ,← Submodule.mem_toAddSubmonoid] at this
     rw [SModEq.sub_mem,← map_sub ,← Submodule.mem_comap,← Submodule.mem_toAddSubmonoid]
     exact hp m this ⟩
  map_add' a b:=by ext n; simp
  map_smul' r a:=by
    ext n
    simp only [smul_apply, map_smul, RingHom.id_apply]
    rw[equiv]
    simp only [map_smul, AdicCauchySequence.smul_apply]

private def ReduceModIdeal (n:ℕ)(hp: ∀ n,
(J^n • ⊤ : Submodule S S).1 ≤ (Submodule.comap f (I^n • ⊤ : Submodule R M)).1)
 :
   S ⧸ (J^n • ⊤ : Submodule S S) →ₗ[R] M ⧸ (I^n • ⊤ : Submodule R M) :=
 mapQ1 (J^n • ⊤ : Submodule S S) (I^n • ⊤ : Submodule R M) f (hp n)

#check Ideal.mul_le_inf

@[simp]
theorem reduceModIdeal_apply (n:ℕ) (x : S) (hp: ∀ n,
(J^n • ⊤ : Submodule S S).1 ≤ (Submodule.comap f (I^n • ⊤ : Submodule R M)).1):
    (ReduceModIdeal  I J f n hp) (Submodule.Quotient.mk (p := (J^n • ⊤ : Submodule S S)) x) =
      Submodule.Quotient.mk (p := (I^n • ⊤ : Submodule R M)) (f x) :=by
    rfl


private def AlgebraAdicCompletion.eval (n:ℕ):
AdicCompletion J S →ₗ[R] S ⧸( J ^ n • ⊤: Submodule S S) where
  toFun := AdicCompletion.eval J S n
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
lemma adicequiv{m n :ℕ }(hmn :m≤ n)(hp: ∀ n,
(J^n • ⊤ : Submodule S S).1 ≤ (Submodule.comap f (I^n • ⊤ : Submodule R M)).1):
 transitionMap I M hmn ∘ₗ AdicCompletion.ReduceModIdeal I J f n hp ∘ₗ
 AdicCompletion.AlgebraAdicCompletion.eval J n =
    AdicCompletion.ReduceModIdeal I J f m hp ∘ₗ AdicCompletion.AlgebraAdicCompletion.eval J m:=by
    ext s
    rcases s with ⟨s1,s2⟩
    unfold AdicCompletion.AlgebraAdicCompletion.eval  eval
    simp
    rw[←(s2 hmn)]
    have:=by
      exact Submodule.Quotient.mk_surjective (J^n • ⊤ : Submodule S S)
    unfold Function.Surjective at this
    rcases (this (s1 n)) with ⟨r,rs⟩
    rw[← rs]
    simp[reduceModIdeal_apply]
    rfl

def adicCompletionAux  (hp: ∀ n,
(J^n • ⊤ : Submodule S S).1 ≤ (Submodule.comap f (I^n • ⊤ : Submodule R M)).1):
    AdicCompletion J S →ₗ[R] AdicCompletion I M := AdicCompletion.lift I
    (fun n ↦ (ReduceModIdeal  I J f n hp) ∘ₗ
   AlgebraAdicCompletion.eval J n) (fun {_ _} hle ↦ adicequiv I J f hle hp)

end AdicCompletion
