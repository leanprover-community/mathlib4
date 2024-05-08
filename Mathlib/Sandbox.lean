import Mathlib

open Submodule

/-- A version of `Ideal.associatesEquivIsPrincipal` with non zero divisors generators. -/
def Ideal.associatesNonZeroDivisorsEquivIsPrincipal (R : Type*) [CommRing R] [IsDomain R] :
    Associates R⁰ ≃ {I : (Ideal R)⁰ // IsPrincipal (I : Ideal R)} :=
  calc Associates R⁰ ≃ (Associates R)⁰ := (AssociatesNonZeroDivisorsMulEquiv R).toEquiv
    _ ≃ {I : {I : Ideal R // IsPrincipal I} // I.1 ∈ (Ideal R)⁰} :=
      Equiv.subtypeEquiv (Ideal.associatesEquivIsPrincipal R)
        (fun x ↦ by rw [← Associates.quot_out x, Associates_mk_mem_nonZeroDivisors,
          Ideal.associatesEquivIsPrincipal_mem_nonZeroDivisors])
    _ ≃ {I : Ideal R // IsPrincipal I ∧ I ∈ (Ideal R)⁰} :=
      Equiv.subtypeSubtypeEquivSubtypeInter (fun I ↦ IsPrincipal I) (fun I ↦ I ∈ (Ideal R)⁰)
    _ ≃ {I : Ideal R // I ∈ (Ideal R)⁰ ∧ IsPrincipal I} := Equiv.setCongr (by simp_rw [and_comm])
    _ ≃ {I : (Ideal R)⁰ // IsPrincipal I.1} := (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
