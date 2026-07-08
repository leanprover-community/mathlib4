module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.RepresentationTheory.Character

open Representation MonoidAlgebra

@[expose] public noncomputable section

section Prelim

@[simp] lemma IntertwiningMap.toLinearMap_one {A G V : Type*}
    [CommSemiring A] [Monoid G] [AddCommMonoid V] [Module A V] (ρ : Representation A G V) :
  IntertwiningMap.toLinearMap (1 : ρ.IntertwiningMap ρ) = 1 := rfl

end Prelim

section sumConj

variable {A G V : Type*} [CommSemiring A] [Group G] [Fintype G] [DecidableEq G]
  [AddCommMonoid V] [Module A V] (ρ : Representation A G V) (c : ConjClasses G)

@[nolint docBlame] def IntertwiningMap.sumConj : ρ.IntertwiningMap ρ := by
  have mem_center : ∑ h ∈ c.carrier, (MonoidAlgebra.of A G h) ∈ Submonoid.center A[G] := by
    refine Submonoid.mem_center_iff.2 fun x ↦ (coeff_inj.1 <| Finsupp.ext fun i ↦ ?_)
    simp_rw [Finset.mul_sum, Finset.sum_mul, of_apply, coeff_sum, Finset.sum_apply',
      coeff_single_mul_apply, coeff_mul_single_apply, ← Finset.sum_set_coe, mul_one, one_mul]
    exact Fintype.sum_equiv (c.bijOn_conj i).equiv _ _ fun _ ↦ by simp [Set.BijOn.equiv, mul_assoc]
  exact IntertwiningMap.centralAlgebraMul ρ mem_center

lemma IntertwiningMap.sumConj.toLinearMap :
    (IntertwiningMap.sumConj ρ c).toLinearMap = ∑ h ∈ c.carrier, ρ h := by
  simp [sumConj, IntertwiningMap.centralAlgebraMul]

@[simp] lemma IntertwiningMap.sumConj_apply (v : V) :
    IntertwiningMap.sumConj ρ c v = ∑ h ∈ c.carrier, ρ h v := by
  simp [sumConj]

end sumConj

variable {G k V : Type*} [Group G] [Fintype G] [DecidableEq G] [Field k] [IsAlgClosed k]
  [CharZero k] [AddCommGroup V] [Nontrivial V] [Module k V] [FiniteDimensional k V]
  (g : G) (ρ : Representation k G V) [ρ.IsIrreducible]

example : IsIntegral ℤ <|
    (Module.finrank k V : k)⁻¹ * (ConjClasses.mk g).carrier.toFinset.card • ρ.character g := by
  set c := ConjClasses.mk g with c_def
  obtain ⟨ω, hω⟩ := IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed.surjective <|
    IntertwiningMap.sumConj ρ c
  rw [IntertwiningMap.algebraMap_apply] at hω
  set X : ℤ[G] := ∑ h ∈ c.carrier, (of ℤ G h) with X_def
  set f := ρ.asAlgebraHom.restrictScalars ℤ |>.comp <| mapAlgHom G (algebraMap ℤ k).toIntAlgHom
  have eq1 : f X = (IntertwiningMap.sumConj ρ c).toLinearMap := by
    ext; simp [f, X_def]
  obtain ⟨P, ⟨hP_monic, hP_eq⟩⟩ : IsIntegral ℤ (IntertwiningMap.sumConj ρ c).toLinearMap :=
    eq1 ▸ (IsIntegral.of_finite ℤ X).map _
  have eq3 : (P.aeval ω : k) • (1 : V →ₗ[k] V) = 0 := by
    rw [← hP_eq, ← hω, IntertwiningMap.toLinearMap_smul, ← Polynomial.aeval_def,
      IntertwiningMap.toLinearMap_one, ← Algebra.algebraMap_eq_smul_one,
      ← Algebra.algebraMap_eq_smul_one, P.aeval_algebraMap_apply (A := k) (B := V →ₗ[k] V) ω]
  simp only [smul_eq_zero, one_ne_zero, or_false] at eq3
  have ω_int : IsIntegral ℤ ω := ⟨P, ⟨hP_monic, eq3⟩⟩
  apply_fun (fun x ↦ LinearMap.trace k V x.toLinearMap) at hω
  simp only [IntertwiningMap.toLinearMap_smul, IntertwiningMap.toLinearMap_one, map_smul,
    LinearMap.trace_one, smul_eq_mul, IntertwiningMap.sumConj.toLinearMap, map_sum] at hω
  change ω * (Module.finrank k V) = ∑ x ∈ c.carrier, ρ.character x at hω
  rw [Finset.sum_eq_card_nsmul (b := ρ.character g)] at hω
  · rwa [← hω, mul_comm, mul_assoc, mul_inv_cancel₀, mul_one]
    exact Nat.cast_ne_zero.2 <| Nat.pos_iff_ne_zero.1 Module.finrank_pos
  · intro a ha
    simp only [c_def, Set.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq,
      ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at ha
    rcases ha with ⟨h, heq⟩
    rw [← heq, char_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

end
