import Mathlib.Algebra.Module.PID
import Mathlib.FieldTheory.MvPolynomial

open Polynomial

universe u v
open Polynomial BigOperators

namespace Module

variable (R : Type u) (M : Type u) (N : Type u) [Field R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module.Finite R M] (φ : M →ₗ[R] M)

theorem fst_finite [Module R M] [Module R N] [Finite R (M × N)]: Finite R M :=
  Module.Finite.equiv (Submodule.fstEquiv R M N)

theorem snd_finite [Module R M] [Module R N] [Finite R (M × N)]: Finite R N :=
  Module.Finite.equiv (Submodule.sndEquiv R M N)


theorem LinearEquiv.uniqueProd {M N : Type u} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Unique N] :
    (N × M) ≃ₗ[R] M :=
  AddEquiv.uniqueProd.toLinearEquiv (fun _ _ => by simp [AddEquiv.uniqueProd])

theorem LinearEquiv.prodUnique {M N : Type u} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Unique N] :
    (M × N) ≃ₗ[R] M :=
  AddEquiv.prodUnique.toLinearEquiv (fun _ _ => by simp [AddEquiv.prodUnique])


theorem hehe : ∃ (ι : Type u) (_ : Fintype ι) (p : ι → R[X]) (_ : ∀ i, Irreducible <| p i) (e : ι → ℕ),
    Nonempty (AEval' φ ≃ₗ[R[X]] (Fin 0 →₀ R[X]) × DirectSum ι fun i ↦ R[X] ⧸ Submodule.span R[X] {p i ^ e i}) := by
  rcases equiv_free_prod_directSum.{_,u} (R := R[X]) (N := Module.AEval' φ) with
    ⟨n,ι,x,p,hp,e,⟨h⟩⟩
  have : Module.Finite R (AEval' φ) := inferInstance
  have : n = 0 := by
    by_contra x
    have holygrail := LinearEquiv.lift_rank_eq (MvPolynomial.pUnitAlgEquiv R).toLinearEquiv
    rw [MvPolynomial.rank_mvPolynomial (K:=R) (σ:=PUnit)] at holygrail
    simp only [Cardinal.mk_finsupp_lift_of_fintype, Cardinal.mk_eq_aleph0, Cardinal.lift_aleph0,
      Fintype.card_ofSubsingleton, pow_one, Cardinal.lift_id] at holygrail
    let S1 := (Fin n →₀ R[X])
    let S2 := (DirectSum ι fun i ↦ R[X] ⧸ Submodule.span R[X] {p i ^ e i})
    have := LinearEquiv.restrictScalars R h
    have := Module.Finite.equiv this
    have := fst_finite R S1 S2
    have := rank_finsupp R R[X] (Fin n)
    rw [Cardinal.lift_mk_fin, ← holygrail] at this
    simp only [Cardinal.lift_natCast,
      Cardinal.lift_id', ge_iff_le, ne_eq] at this
    rw [Cardinal.nat_mul_aleph0 x] at this
    have uwu := FiniteDimensional.rank_lt_aleph0 R S1
    rwa [this, lt_self_iff_false] at uwu
  rw [this] at h
  exact ⟨ι,x,p,hp,e,⟨h⟩⟩

theorem hehe2 : Subsingleton (Fin 0 →₀ R[X]) := inferInstance
theorem hehe3 : Unique (Fin 0 →₀ R[X]) := inferInstance
theorem hehe4 : ∃ (ι : Type u) (_ : Fintype ι) (p : ι → R[X]) (_ : ∀ i, Irreducible <| p i) (e : ι → ℕ),
    Nonempty (AEval' φ ≃ₗ[R[X]] DirectSum ι fun i ↦ R[X] ⧸ Submodule.span R[X] {p i ^ e i})  := by
  rcases hehe R M φ with ⟨ι,x,p,hp,e,⟨h⟩⟩
  refine ⟨ι,x,p,hp,e,⟨?_⟩⟩
  --have := LinearEquiv.uniqueProd (DirectSum ι fun i ↦ R[X] ⧸ Submodule.span R[X] {p i ^ e i}) (Fin 0 →₀ R[X])
  exact LinearEquiv h this
