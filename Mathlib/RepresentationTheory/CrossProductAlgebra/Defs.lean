/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yunzhou Xie, Jujian Zhang
-/
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!

# Cross product algebra

This file constructs the cross product algebra associated to a 2-cocycle of a field extension
`K / F` and shows that it is indeed an `F`-algebra.

## TODOs

* Prove the cross product algebra is a central simple algebra over `F` of degree `n`
  where `n` is the degree of the extension `K / F`.

* Show that there is a map induced from `H^2 (Gal(K/F), Kˣ)` to Brauer group `Br(F)`, and the map
  is in fact a group homomorphism.

## References

* [Anthony W. Knapp, *Advanced Algebra*][anthony2016]

## Tags

Non-commutative algebra, galois cohomology, cross product algebra

-/

open groupCohomology Function Module

suppress_compilation

variable {R S F K : Type*} [Field F] [Field K] [Algebra F K] {f : (K ≃ₐ[F] K) × (K ≃ₐ[F] K) → Kˣ}

/-- Similarly to `MonoidAlgebra`, the underlying type/set is all finitely supported functions from
`Gal(K/F)` to `K` and we give the multiplication structure by
`single σ c * single τ d = f (σ, τ) • single (σ * τ) (c * σ d)` -/
@[ext]
structure CrossProductAlgebra (f : (K ≃ₐ[F] K) × (K ≃ₐ[F] K) → Kˣ) where
  /-- the underlying type -/
  val : (K ≃ₐ[F] K) →₀ K

namespace CrossProductAlgebra
variable {x y : CrossProductAlgebra f}

lemma val_injective : Injective (val (f := f)) := fun _ _ ↦ CrossProductAlgebra.ext
lemma val_surjective : Surjective (val (f := f)) := fun x ↦ ⟨⟨x⟩, rfl⟩
lemma val_bijective : Bijective (val (f := f)) := ⟨val_injective, val_surjective⟩

@[simp] lemma val_inj : x.val = y.val ↔ x = y := val_injective.eq_iff

lemma «forall» {P : CrossProductAlgebra f → Prop} : (∀ x, P x) ↔ ∀ x, P (mk x) := by
  rw [val_surjective.forall]

instance : Nontrivial (CrossProductAlgebra f) := val_surjective.nontrivial

instance : Zero (CrossProductAlgebra f) where
  zero := ⟨0⟩

instance : Add (CrossProductAlgebra f) where
  add x y := ⟨x.val + y.val⟩

instance : Neg (CrossProductAlgebra f) where
  neg x := ⟨-x.val⟩

instance : Sub (CrossProductAlgebra f) where
  sub x y := ⟨x.val - y.val⟩

instance [Semiring R] [Module R K] : SMul R (CrossProductAlgebra f) where
  smul r x := ⟨r • x.val⟩

@[simp] lemma val_zero : (0 : CrossProductAlgebra f).val = 0 := rfl
@[simp] lemma val_add (x y : CrossProductAlgebra f) : (x + y).val = x.val + y.val := rfl
@[simp] lemma val_smul [Semiring R] [Module R K] (r : R) (x : CrossProductAlgebra f) :
    (r • x).val = r • x.val := rfl
@[simp] lemma val_neg (x : CrossProductAlgebra f) : (-x).val = -x.val := rfl
@[simp] lemma val_sub (x y : CrossProductAlgebra f) : (x - y).val = x.val - y.val := rfl

@[simp] lemma mk_zero : (mk 0 : CrossProductAlgebra f) = 0 := rfl
@[simp] lemma mk_add_mk (x y : (K ≃ₐ[F] K) →₀ K) :
    (mk x + mk y : CrossProductAlgebra f) = mk (x + y) := rfl
@[simp] lemma smul_mk [Semiring R] [Module R K] (r : R) (x : (K ≃ₐ[F] K) →₀ K) :
    (r • mk x : CrossProductAlgebra f) = mk (r • x) := rfl
@[simp] lemma neg_mk (x : (K ≃ₐ[F] K) →₀ K) : (- mk x : CrossProductAlgebra f) = mk (-x) := rfl
@[simp] lemma mk_sub_mk (x y : (K ≃ₐ[F] K) →₀ K) :
    (mk x - mk y : CrossProductAlgebra f) = mk (x - y) := rfl

instance addCommGroup : AddCommGroup (CrossProductAlgebra f) :=
  val_injective.addCommGroup val val_zero val_add val_neg val_sub (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Any cross product algerba over `F` is isomorphic to its underlying type as an `AddEquiv` -/
@[simps]
def valAddEquiv : CrossProductAlgebra f ≃+ ((K ≃ₐ[F] K) →₀ K) where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := val_add

@[simp]
lemma val_finsuppSum {α M : Type*} [AddCommMonoid M] (g : α →₀ M)
    (h : α → M → CrossProductAlgebra f) :
    (g.sum h).val = g.sum (fun a m ↦ (h a m).val) := map_finsuppSum valAddEquiv ..

instance [Semiring R] [Module R K] : Module R (CrossProductAlgebra f) :=
  val_injective.module _ valAddEquiv.toAddMonoidHom val_smul

instance [Semiring R] [Semiring S] [Module R K] [Module S K] [Module R S] [IsScalarTower R S K] :
    IsScalarTower R S (CrossProductAlgebra f) where
  smul_assoc r s x := by ext; simp [smul_assoc]

/-- Any cross product algerba over `F` is linearly isomorphic to its underlying type -/
@[simps]
def valLinearEquiv [Semiring R] [Module R K] : CrossProductAlgebra f ≃ₗ[R] ((K ≃ₐ[F] K) →₀ K) where
  __ := valAddEquiv
  map_smul' := val_smul

/-- `Finsupp.single` forms a `K`-basis of `CrossProductAlgebra` -/
@[simps]
def basis : Basis (K ≃ₐ[F] K) K (CrossProductAlgebra f) where
  repr := valLinearEquiv

lemma basis_val (σ : (K ≃ₐ[F] K)) : (basis (f := f) σ).val = .single σ 1 := rfl
lemma mk_single_one (σ : (K ≃ₐ[F] K)) : mk (.single σ 1) = basis (f := f) σ := rfl

variable (f) in
/-- The multiplication of `CrossProductAlgebra` induced by multiplication for basis elements. -/
def mulLinearMap : ((K ≃ₐ[F] K) →₀ K) →ₗ[F] ((K ≃ₐ[F] K) →₀ K) →ₗ[F] ((K ≃ₐ[F] K) →₀ K) :=
  Finsupp.lsum F fun σ =>
  { toFun c := Finsupp.lsum F fun τ =>
      { toFun d := .single (σ * τ) (c * σ d * f (σ, τ))
        map_add' := by simp [mul_add, add_mul]
        map_smul' := by simp only [map_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
          RingHom.id_apply, Finsupp.smul_single, implies_true] }
    map_add' _ _ := by ext; simp [add_mul]
    map_smul' _ _ := by ext; simp only [Algebra.smul_mul_assoc, Finsupp.lsum_comp_lsingle,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.coe_comp, comp_apply,
      Finsupp.lsingle_apply, LinearMap.smul_apply, Finsupp.coe_lsum, map_zero, mul_zero, zero_mul,
      Finsupp.single_zero, Finsupp.sum_single_index, Finsupp.smul_single] }

variable (f) in
@[simp]
lemma mulLinearMap_single_single (c d : K) (σ τ : (K ≃ₐ[F] K)) :
    mulLinearMap f (.single σ c) (.single τ d) = .single (σ * τ) (c * σ d * f (σ, τ)) := by
  simp only [mulLinearMap, Finsupp.single_mul, Finsupp.coe_lsum, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.finsupp_sum_apply, map_zero, Finsupp.single_zero, mul_zero, zero_mul,
    Finsupp.sum_single_index]

variable (f) in
@[simp]
lemma mulLinearMap_single_left_apply (c : K) (σ : (K ≃ₐ[F] K))
    (x : (K ≃ₐ[F] K) →₀ K) (τ : (K ≃ₐ[F] K)) :
    mulLinearMap f (.single σ c) x τ = c * σ (x (σ⁻¹ * τ)) * f (σ, σ⁻¹ * τ) := by
  classical simp +contextual only [mulLinearMap, Finsupp.single_mul, Finsupp.coe_lsum,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.finsupp_sum_apply, Finsupp.single_zero, zero_mul,
    Finsupp.sum_zero, Finsupp.sum_single_index, Finsupp.sum_apply, Finsupp.mul_apply,
    Finsupp.single_apply, ← eq_inv_mul_iff_mul_eq, mul_ite, ↓reduceIte, mul_zero,
    Finsupp.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_not, ite_eq_right_iff, map_zero,
    implies_true]

variable (f) in
@[simp]
lemma mulLinearMap_single_right_apply (c : K) (σ : (K ≃ₐ[F] K))
    (x : (K ≃ₐ[F] K) →₀ K) (τ : (K ≃ₐ[F] K)) :
    mulLinearMap f x (.single σ c) τ = x (τ * σ⁻¹) * τ (σ⁻¹ c) * f (τ * σ⁻¹, σ) := by
  classical simp +contextual [mulLinearMap, Finsupp.single_apply, ← eq_mul_inv_iff_mul_eq]

instance : One (CrossProductAlgebra f) where
  one := ⟨.single 1 (f (1, 1))⁻¹⟩

instance : Mul (CrossProductAlgebra f) where
  mul x y := ⟨mulLinearMap f x.val y.val⟩

lemma one_def : (1 : CrossProductAlgebra f) = ⟨.single 1 (f (1, 1))⁻¹⟩ := rfl

@[simp] lemma val_one : (1 : CrossProductAlgebra f).val = .single 1 (f (1, 1))⁻¹ := rfl

@[simp] lemma val_mul (x y : CrossProductAlgebra f) :
    (x * y).val = mulLinearMap f x.val y.val := rfl

@[simp] lemma mk_mul_mk (x y : (K ≃ₐ[F] K) →₀ K) :
    (mk x * mk y : CrossProductAlgebra f) = mk (mulLinearMap f x y) := rfl

variable [Fact <| IsMulCocycle₂ f]

instance monoid : Monoid (CrossProductAlgebra f) where
  one_mul := by
    rintro ⟨x⟩
    ext : 1
    dsimp
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add => simp [*]
    | single σ a => simp [map_one_fst_of_isMulCocycle₂ Fact.out σ, mul_right_comm _ a]
  mul_one := by
    rintro ⟨x⟩
    ext : 1
    dsimp
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add => simp [*]
    | single σ a => simp [map_one_snd_of_isMulCocycle₂ Fact.out σ]
  mul_assoc := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    ext : 1
    dsimp
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add => simp [*]
    | single σ a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add => simp [*]
    | single τ b =>
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add => simp [-mulLinearMap_single_single, *]
    | single ν c =>
    simp only [mulLinearMap_single_single, mul_assoc, AlgEquiv.mul_apply, map_mul,
      mul_left_comm _ (σ (τ c))]
    congr 4
    simpa [mul_comm] using congr(($((Fact.out : IsMulCocycle₂ f) σ τ ν)).val)

instance : Ring (CrossProductAlgebra f) where
  __ := addCommGroup
  __ := monoid
  left_distrib := by intros; ext; simp
  right_distrib := by intros; ext; simp
  zero_mul := by intros; ext; simp
  mul_zero := by intros; ext; simp
  sub_eq_add_neg := by intros; ext; simp [sub_eq_add_neg]
  neg_add_cancel := by intros; ext; simp

@[simp]
lemma val_natCast (n : ℕ) : (n : CrossProductAlgebra f).val = n • .single 1 (f (1, 1))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, add_smul]

@[simp]
lemma val_intCast (n : ℤ) :
    (n : CrossProductAlgebra f).val = n • .single 1 (f (1, 1))⁻¹ := by
  cases n <;> simp [val_natCast, ← sub_eq_add_neg, sub_mul]

instance algebra [CommSemiring R] [Algebra R F] [Module R K] [IsScalarTower R F K] :
    Algebra R (CrossProductAlgebra f) := by
  refine .ofModule ?_ ?_ <;> intros <;> ext <;> simp

lemma algebraMap_val [CommSemiring R] [Algebra R F] [Algebra R K] [IsScalarTower R F K] (r : R) :
    (algebraMap R (CrossProductAlgebra f) r).val = .single 1 (algebraMap R K r * (f (1, 1))⁻¹) := by
  rw [Algebra.algebraMap_eq_smul_one]
  simp only [val_smul, val_one, Finsupp.smul_single,
    Units.val_inv_eq_inv_val, ← Algebra.smul_def]

end CrossProductAlgebra
