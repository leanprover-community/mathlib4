import Mathlib.RepresentationTheory.GroupCohomology.hmmm
import Mathlib.FieldTheory.Galois
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.Norm
universe v u
suppress_compilation
section

variable (K L : Type*) [Field K] [Field L]
  [Algebra K L] [FiniteDimensional K L]

open BigOperators

/-- Given `f: Aut_K(L) → Lˣ`, the sum `∑ f(φ) • φ` for `φ ∈ Aut_K(L)`, as a function `L → L`. -/
noncomputable def aux (f : (L ≃ₐ[K] L) → Lˣ) : L → L :=
Finsupp.total (L ≃ₐ[K] L) (L → L) L (fun φ => φ)
  (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))

lemma aux_apply (f : (L ≃ₐ[K] L) → Lˣ) (x : L) :
    aux K L f x = ∑ g, f g * g x := by
  simp [aux, Finsupp.total, Finsupp.lsum_apply, Finsupp.sum_fintype,
    Finsupp.equivFunOnFinite_symm_apply_toFun, LinearMap.coe_smulRight, LinearMap.id_coe,
    id_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

lemma aux_ne_zero (f : (L ≃ₐ[K] L) → Lˣ) : aux K L f ≠ 0 :=
/- the set `Aut_K(L)` is linearly independent in the `L`-vector space `L → L`, by Dedekind's
linear independence of characters -/
  have : @LinearIndependent (L ≃ₐ[K] L) L (L → L) (fun f => f) _ _ _ :=
    @LinearIndependent.comp (L →* L) (L ≃ₐ[K] L) L (L → L) (fun f => f)
    _ _ _ (linearIndependent_monoidHom L L) (fun f => f)
    (fun x y h => by ext; exact FunLike.ext_iff.1 h _)
  have h := linearIndependent_iff.1 this
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))
  fun H => Units.ne_zero (f 1) (FunLike.ext_iff.1 (h H) 1)

variable {K L}

theorem Hilbert90 (f : (L ≃ₐ[K] L) → Lˣ)
  (hf : ∀ (g h : (L ≃ₐ[K] L)), f (g * h) = g (f h) * f g) :
  ∃ β : Lˣ, ∀ g : (L ≃ₐ[K] L), f g * Units.map g β = β := by
/- Let `z : L` be such that `∑ f(h) * h(z) ≠ 0`, for `h ∈ Aut_K(L)` -/
  obtain ⟨z, hz⟩ : ∃ z, aux K L f z ≠ 0 :=
    not_forall.1 (fun H => aux_ne_zero K L f $ funext $ fun x => H x)
/- Let `β = ∑ f(h) * h(z).` -/
  use Units.mk0 (aux K L f z) hz
  intro g
/- Then the equality follows from the hypothesis `hf` (that `f` is a 1-cocycle). -/
  simp_rw [Units.ext_iff, aux_apply, Units.val_mul, Units.coe_map,
    Units.val_mk0, MonoidHom.coe_coe, map_sum,
    map_mul, Finset.mul_sum, ←mul_assoc, mul_comm (f _ : L), ←hf, mul_comm (f _ : L)]
  exact Fintype.sum_bijective (fun i => g * i) (Group.mulLeft_bijective g) _ _ (fun i => rfl)

end

open CategoryTheory groupCohomology

variable (K L : Type) [Field K] [Field L]
  [Algebra K L] [FiniteDimensional K L]

abbrev autOnUnits : Rep ℤ (L ≃ₐ[K] L) :=
Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ

def Hilbert90again : Unique (H1 (autOnUnits K L)) where
  default := 0
  uniq := fun a => Quotient.inductionOn' a fun x => (Submodule.Quotient.mk_eq_zero _).2 <| by
    rcases Hilbert90 (Additive.toMul ∘ x.1) (fun g h => Units.ext_iff.1
      ((mem_oneCocycles_iff x.1).1 x.2 g h)) with ⟨β, hβ⟩
    use Additive.ofMul (β⁻¹ : Lˣ)
    ext g
    rw [LinearMap.codRestrict_apply]
    refine' Additive.toMul.bijective.1 _
    simp only [autOnUnits, Rep.ofMulDistribMulAction_apply_apply, dZero_apply, sub_eq_iff_eq_add]
    show Units.map g β⁻¹ / β⁻¹ = Additive.toMul (x.1 g)
    rw [map_inv, div_inv_eq_mul, mul_comm]
    exact (mul_inv_eq_iff_eq_mul (G := Lˣ)).2 (hβ g).symm
