/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.CharP.Pi
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # `algebraMap R (CliffordAlgebra Q)` is not always injective.

A formalization of [Darij Grinberg's answer](https://mathoverflow.net/questions/60596/clifford-pbw-theorem-for-quadratic-form/87958#87958)
to a "Clifford PBW theorem for quadratic form" post on MathOverflow, that provides a counterexample
to `Function.Injective (algebraMap R (CliffordAlgebra Q))`.

The outline is that we define:

* $k$ (`Q60596.K`) as the commutative ring $𝔽₂[α, β, γ] / (α², β², γ²)$
* $L$ (`Q60596.L`) as the $k$-module $⟨x,y,z⟩ / ⟨αx + βy + γz⟩$
* $Q$ (`Q60596.Q`) as the quadratic form sending $Q(\overline{ax + by + cz}) = a² + b² + c²$

and discover that $αβγ ≠ 0$ as an element of $K$, but $αβγ = 0$ as an element of $𝒞l(Q)$.

Some Zulip discussion at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.F0.9D.94.BD.E2.82.82.5B.CE.B1.2C.20.CE.B2.2C.20.CE.B3.5D.20.2F.20.28.CE.B1.C2.B2.2C.20.CE.B2.C2.B2.2C.20.CE.B3.C2.B2.29/near/222716333.

As a bonus result, we also show `BilinMap.not_forall_toQuadraticMap_surjective`: that there
are quadratic forms that cannot be expressed via even non-symmetric bilinear forms.
-/

noncomputable section

open LinearMap (BilinForm)
open LinearMap (BilinMap)

namespace Q60596

open MvPolynomial

/-- The monomial ideal generated by terms of the form $x_ix_i$. -/
def kIdeal : Ideal (MvPolynomial (Fin 3) (ZMod 2)) :=
  Ideal.span (Set.range fun i => (X i * X i : MvPolynomial (Fin 3) (ZMod 2)))

theorem mem_kIdeal_iff (x : MvPolynomial (Fin 3) (ZMod 2)) :
    x ∈ kIdeal ↔ ∀ m : Fin 3 →₀ ℕ, m ∈ x.support → ∃ i, 2 ≤ m i := by
  have :
      kIdeal = Ideal.span ((monomial · (1 : ZMod 2)) '' Set.range (Finsupp.single · 2)) := by
    simp_rw [kIdeal, X, monomial_mul, one_mul, ← Finsupp.single_add, ← Set.range_comp,
      Function.comp_def]
  rw [this, mem_ideal_span_monomial_image]
  simp

theorem X0_X1_X2_not_mem_kIdeal : (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) ∉ kIdeal := by
  intro h
  simp_rw [mem_kIdeal_iff, support_mul_X, support_X, Finset.map_singleton, addRightEmbedding_apply,
    Finset.mem_singleton, forall_eq, ← Fin.sum_univ_three fun i => Finsupp.single i 1,
    ← Finsupp.equivFunOnFinite_symm_eq_sum] at h
  contradiction

theorem mul_self_mem_kIdeal_of_X0_X1_X2_mul_mem {x : MvPolynomial (Fin 3) (ZMod 2)}
    (h : X 0 * X 1 * X 2 * x ∈ kIdeal) : x * x ∈ kIdeal := by
  rw [mem_kIdeal_iff] at h
  have : x ∈ Ideal.span ((X : Fin 3 → MvPolynomial _ (ZMod 2)) '' Set.univ) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    simp_rw [mul_assoc, support_X_mul, Finset.map_map, Finset.mem_map,
      Function.Embedding.trans_apply, addLeftEmbedding_apply, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂, ← add_assoc, ←
      Fin.sum_univ_three fun i => Finsupp.single i 1, ← Finsupp.equivFunOnFinite_symm_eq_sum,
      Finsupp.add_apply, Finsupp.equivFunOnFinite_symm_apply_toFun] at h
    refine (h _ hm).imp fun i hi => ⟨Set.mem_univ _, ?_⟩
    rintro hmi
    rw [hmi] at hi
    norm_num at hi
  rw [as_sum x, CharTwo.sum_mul_self]
  refine sum_mem fun m hm => ?_
  rw [mem_kIdeal_iff, monomial_mul]
  intro m' hm'
  obtain rfl := Finset.mem_singleton.1 (support_monomial_subset hm')
  rw [mem_ideal_span_X_image] at this
  obtain ⟨i, _, hi⟩ := this m hm
  simp_rw [← one_add_one_eq_two]
  refine ⟨i, Nat.add_le_add ?_ ?_⟩ <;> rwa [Nat.one_le_iff_ne_zero]

/-- `𝔽₂[α, β, γ] / (α², β², γ²)` -/
def K : Type _ := _ ⧸ kIdeal

instance : CommRing K := Ideal.Quotient.commRing _

theorem comap_C_kIdeal : kIdeal.comap (C : ZMod 2 →+* MvPolynomial (Fin 3) (ZMod 2)) = ⊥ := by
  refine bot_unique ?_
  refine (Ideal.comap_le_map_of_inverse _ _ _ (constantCoeff_C _)).trans ?_
  rw [kIdeal, Ideal.map_span]
  refine (Ideal.span_le).2 ?_
  rintro x ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [RingHom.map_mul, constantCoeff_X, mul_zero, Submodule.bot_coe,
    Set.mem_singleton_iff]

/-- `k` has characteristic 2. -/
instance K.charP : CharP K 2 := by
  dsimp only [K]
  rw [CharP.quotient_iff_le_ker_natCast]
  have : Nat.castRingHom (MvPolynomial (Fin 3) (ZMod 2)) = C.comp (Nat.castRingHom _) := by
    ext1 r; rfl
  rw [this, ← Ideal.comap_comap, ← RingHom.comap_ker, comap_C_kIdeal]
  exact Ideal.comap_mono bot_le

/-- The generators of `K`. -/
def K.gen (i : Fin 3) : K := Ideal.Quotient.mk _ (MvPolynomial.X i)

local notation "α" => K.gen 0
local notation "β" => K.gen 1
local notation "γ" => K.gen 2

/-- The elements above square to zero -/
@[simp]
theorem X_sq (i : Fin 3) : K.gen i * K.gen i = (0 : K) := by
  change Ideal.Quotient.mk _ _ = _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- If an element multiplied by `αβγ` is zero then it squares to zero. -/
theorem sq_zero_of_αβγ_mul {x : K} : α * β * γ * x = 0 → x * x = 0 := by
  induction x using Quotient.inductionOn'
  change Ideal.Quotient.mk _ _ = 0 → Ideal.Quotient.mk _ _ = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
  exact mul_self_mem_kIdeal_of_X0_X1_X2_mul_mem

/-- Though `αβγ` is not itself zero-/
theorem αβγ_ne_zero : α * β * γ ≠ 0 := fun h =>
  X0_X1_X2_not_mem_kIdeal <| Ideal.Quotient.eq_zero_iff_mem.1 h

/-- The 1-form on $K^3$, the kernel of which we will take a quotient by.

Our source uses $αx - βy - γz$, though since this is characteristic two we just use $αx + βy + γz$.
 -/
@[simps!]
def lFunc : (Fin 3 → K) →ₗ[K] K :=
  letI proj : Fin 3 → (Fin 3 → K) →ₗ[K] K := LinearMap.proj
  α • proj 0 + β • proj 1 + γ • proj 2

/-- The quotient of `K^3` by the specified relation. -/
abbrev L : Type _ := _ ⧸ LinearMap.ker lFunc

/-- The quadratic form corresponding to squaring a single coefficient. -/
def sq {ι R : Type*} [CommRing R] (i : ι) : QuadraticForm R (ι → R) :=
  QuadraticMap.sq.comp <| LinearMap.proj i

theorem sq_map_add_char_two {ι R : Type*} [CommRing R] [CharP R 2] (i : ι) (a b : ι → R) :
    sq i (a + b) = sq i a + sq i b :=
  CharTwo.add_mul_self _ _

theorem sq_map_sub_char_two {ι R : Type*} [CommRing R] [CharP R 2] (i : ι) (a b : ι → R) :
    sq i (a - b) = sq i a - sq i b := by
  haveI : Nonempty ι := ⟨i⟩
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, sq_map_add_char_two]

/-- The quadratic form (metric) is just euclidean -/
def Q' : QuadraticForm K (Fin 3 → K) :=
  ∑ i, sq i

theorem Q'_add (x y : Fin 3 → K) : Q' (x + y) = Q' x + Q' y := by
  simp only [Q', QuadraticMap.sum_apply, sq_map_add_char_two, Finset.sum_add_distrib]

theorem Q'_sub (x y : Fin 3 → K) : Q' (x - y) = Q' x - Q' y := by
  simp only [Q', QuadraticMap.sum_apply, sq_map_sub_char_two, Finset.sum_sub_distrib]

theorem Q'_apply (a : Fin 3 → K) : Q' a = a 0 * a 0 + a 1 * a 1 + a 2 * a 2 :=
  calc
    Q' a = a 0 * a 0 + (a 1 * a 1 + (a 2 * a 2 + 0)) := rfl
    _ = _ := by ring

theorem Q'_apply_single (i : Fin 3) (x : K) : Q' (Pi.single i x) = x * x :=
  calc
    Q' (Pi.single i x) = ∑ j : Fin 3, (Pi.single i x * Pi.single i x : Fin 3 → K) j := by
      simp [Q', sq]
    _ = _ := by simp_rw [← Pi.single_mul, Finset.sum_pi_single', Finset.mem_univ, if_pos]

theorem Q'_zero_under_ideal (v : Fin 3 → K) (hv : v ∈ LinearMap.ker lFunc) : Q' v = 0 := by
  rw [LinearMap.mem_ker, lFunc_apply] at hv
  have h0 : α * β * γ * v 0 = 0 := by
    have := congr_arg (β * γ * ·) hv
    simp only [mul_zero, mul_add, ← mul_assoc] at this
    rw [mul_comm (β * γ) α, ← mul_assoc, mul_right_comm β γ β, mul_assoc β γ γ, X_sq, X_sq] at this
    simpa only [mul_zero, zero_mul, add_zero, zero_add] using this
  have h1 : α * β * γ * v 1 = 0 := by
    have := congr_arg (α * γ * ·) hv
    simp only [mul_zero, mul_add, ← mul_assoc] at this
    rw [mul_right_comm α γ α, mul_assoc α γ γ, mul_right_comm α γ β, X_sq, X_sq] at this
    simpa only [mul_zero, zero_mul, add_zero, zero_add] using this
  have h2 : α * β * γ * v 2 = 0 := by
    have := congr_arg (α * β * ·) hv
    simp only [mul_zero, mul_add, ← mul_assoc] at this
    rw [mul_right_comm α β α, mul_assoc α β β, X_sq, X_sq] at this
    simpa only [mul_zero, zero_mul, add_zero, zero_add] using this
  rw [Q'_apply, sq_zero_of_αβγ_mul h0, sq_zero_of_αβγ_mul h1, sq_zero_of_αβγ_mul h2, add_zero,
    add_zero]

/-- `Q'`, lifted to operate on the quotient space `L`. -/
@[simps!]
def Q : QuadraticForm K L :=
  QuadraticMap.ofPolar
    (fun x =>
      Quotient.liftOn' x Q' fun a b h => by
        rw [Submodule.quotientRel_r_def] at h
        suffices Q' (a - b) = 0 by rwa [Q'_sub, sub_eq_zero] at this
        apply Q'_zero_under_ideal (a - b) h)
    (fun a x => by
      induction x using Quotient.inductionOn
      exact Q'.toFun_smul a _)
    (by rintro ⟨x⟩ ⟨x'⟩ ⟨y⟩; exact Q'.polar_add_left x x' y)
    (by rintro c ⟨x⟩ ⟨y⟩; exact Q'.polar_smul_left c x y)

open CliffordAlgebra

/-- Basis vectors in the Clifford algebra -/
def gen (i : Fin 3) : CliffordAlgebra Q := ι Q <| Submodule.Quotient.mk (Pi.single i 1)

local notation "x'" => gen 0
local notation "y'" => gen 1
local notation "z'" => gen 2

/-- The basis vectors square to one -/
@[simp]
theorem gen_mul_gen (i) : gen i * gen i = 1 := by
  dsimp only [gen]
  simp_rw [CliffordAlgebra.ι_sq_scalar, Q_apply, ← Submodule.Quotient.mk''_eq_mk,
    Quotient.liftOn'_mk'', Q'_apply_single, mul_one, map_one]

/-- By virtue of the quotient, terms of this form are zero -/
theorem quot_obv : α • x' - β • y' - γ • z' = 0 := by
  dsimp only [gen]
  simp_rw [← LinearMap.map_smul, ← LinearMap.map_sub, ← Submodule.Quotient.mk_smul _ (_ : K),
    ← Submodule.Quotient.mk_sub]
  convert LinearMap.map_zero _ using 2
  rw [Submodule.Quotient.mk_eq_zero]
  simp (config := {decide := true}) [sub_zero, Ideal.span, Pi.single_apply]

/-- The core of the proof - scaling `1` by `α * β * γ` gives zero -/
theorem αβγ_smul_eq_zero : (α * β * γ) • (1 : CliffordAlgebra Q) = 0 := by
  suffices α • 1 - β • (y' * x') - γ • (z' * x') = 0 by
    have := congr_arg (fun x => (β * γ) • x) this
    dsimp only at this
    simp_rw [smul_sub, smul_smul] at this
    rwa [mul_assoc β γ γ, mul_right_comm β γ β, mul_right_comm β γ α, mul_comm β α, X_sq, X_sq,
      zero_mul, mul_zero, zero_smul, zero_smul, sub_zero, sub_zero, smul_zero] at this
  have : (α • x' - β • y' - γ • z') * x' = α • 1 - β • (y' * x') - γ • (z' * x') := by
    simp_rw [sub_mul, smul_mul_assoc, gen_mul_gen]
  rw [← this]
  rw [quot_obv, zero_mul]

theorem algebraMap_αβγ_eq_zero : algebraMap K (CliffordAlgebra Q) (α * β * γ) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, αβγ_smul_eq_zero]

/-- Our final result: for the quadratic form `Q60596.Q`, the algebra map to the Clifford algebra
is not injective, as it sends the non-zero `α * β * γ` to zero. -/
theorem algebraMap_not_injective : ¬Function.Injective (algebraMap K <| CliffordAlgebra Q) :=
  fun h => αβγ_ne_zero <| h <| by rw [algebraMap_αβγ_eq_zero, RingHom.map_zero]

/-- Bonus counterexample: `Q` is a quadratic form that has no bilinear form. -/
theorem Q_not_in_range_toQuadraticForm : Q ∉ Set.range BilinMap.toQuadraticMap := by
  rintro ⟨B, hB⟩
  rw [← sub_zero Q] at hB
  apply algebraMap_not_injective
  eta_expand
  simp_rw [← changeForm_algebraMap hB, ← changeFormEquiv_apply]
  refine (LinearEquiv.injective _).comp ?_
  exact (ExteriorAlgebra.algebraMap_leftInverse _).injective

end Q60596

open Q60596 in
/-- The general statement: not every Clifford algebra over a module has an injective algebra map. -/
theorem CliffordAlgebra.not_forall_algebraMap_injective.{v} :
    -- TODO: make `R` universe polymorphic
    ¬∀ (R : Type) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] (Q : QuadraticForm R M),
      Function.Injective (algebraMap R <| CliffordAlgebra Q) :=
  fun h => algebraMap_not_injective fun x y hxy => by
    let uU := ULift.moduleEquiv (R := K) (M := L)
    let uQ := Q.comp uU.toLinearMap
    let f : Q →qᵢ uQ := { uU.symm with map_app' := fun _ => rfl }
    refine h K (ULift L) (Q.comp uU.toLinearMap) ?_
    let uC := CliffordAlgebra.map f
    have := uC.congr_arg hxy
    rwa [AlgHom.commutes, AlgHom.commutes] at this

open Q60596 in
/-- The general bonus statement: not every quadratic form is the diagonal of a bilinear form. -/
theorem BilinMap.not_forall_toQuadraticMap_surjective.{v} :
    -- TODO: make `R` universe polymorphic
    ¬∀ (R : Type) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M],
      Function.Surjective (BilinMap.toQuadraticMap : BilinForm R M → QuadraticForm R M) :=
  fun h => Q_not_in_range_toQuadraticForm <| by
    let uU := ULift.moduleEquiv (R := K) (M := L)
    obtain ⟨x, hx⟩ := h K (ULift L) (Q.comp uU)
    refine ⟨x.compl₁₂ uU.symm uU.symm, ?_⟩
    ext
    simp [BilinMap.toQuadraticMap_comp_same, hx]
