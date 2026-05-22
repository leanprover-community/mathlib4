/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Polynomial.Module.AEval

/-!
# Polynomial module

In this file, we define the polynomial module for an `R`-module `M`, i.e. the `R[X]`-module `M[X]`.

This is defined as a type alias `PolynomialModule R M := ℕ →₀ M`, since there might be different
module structures on `ℕ →₀ M` of interest. See the docstring of `PolynomialModule` for details.
-/

@[expose] public noncomputable section
universe u v
open Polynomial

/-- The `R[X]`-module `M[X]` for an `R`-module `M`.
This is isomorphic (as an `R`-module) to `M[X]` when `M` is a ring.

We require all the module instances `Module S (PolynomialModule R M)` to factor through `R` except
`Module R[X] (PolynomialModule R M)`.
In this constraint, we have the following instances for example :
- `R` acts on `PolynomialModule R R[X]`
- `R[X]` acts on `PolynomialModule R R[X]` as `R[Y]` acting on `R[X][Y]`
- `R` acts on `PolynomialModule R[X] R[X]`
- `R[X]` acts on `PolynomialModule R[X] R[X]` as `R[X]` acting on `R[X][Y]`
- `R[X][X]` acts on `PolynomialModule R[X] R[X]` as `R[X][Y]` acting on itself

This is also the reason why `R` is included in the alias, or else there will be two different
instances of `Module R[X] (PolynomialModule R[X])`.

See https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2315065.20polynomial.20modules
for the full discussion.
-/
@[nolint unusedArguments]
structure PolynomialModule (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  /-- Construct an element of the polynomial module `M[[]]` from its coefficients `ℕ →₀ M`. -/
  ofCoeff (R) ::
  /-- The coefficients `ℕ →₀ M` of an element of the additive monoid algebra `M[X]`. -/
  coeff : ℕ →₀ M

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

namespace PolynomialModule
variable {x y : PolynomialModule R M} {r r₁ r₂ : R} {m m' m₁ m₂ m₁' m₂' : M}

lemma coeff_ofCoeff (x : ℕ →₀ M) : (ofCoeff R x).coeff = x := rfl
lemma ofCoeff_coeff (x : PolynomialModule R M) : ofCoeff R x.coeff = x := rfl

variable (R) in
/-- `PolynomialModule.coeff` as an equiv. -/
@[simps! apply symm_apply]
def coeffEquiv : PolynomialModule R M ≃ (ℕ →₀ M) where
  toFun := coeff
  invFun := ofCoeff R
  left_inv _ := rfl
  right_inv _ := rfl

lemma «forall» {P : PolynomialModule R M → Prop} : (∀ p, P p) ↔ ∀ q, P (ofCoeff R q) :=
  (coeffEquiv R).forall_congr_left

lemma «exists» {P : PolynomialModule R M → Prop} : (∃ p, P p) ↔ ∃ q, P (ofCoeff R q) :=
  (coeffEquiv R).exists_congr_left

lemma coeff_injective : (coeff : PolynomialModule R M → ℕ →₀ M).Injective :=
  (coeffEquiv R).injective

lemma ofCoeff_injective : (ofCoeff R : (ℕ →₀ M) → PolynomialModule R M).Injective :=
  (coeffEquiv R).symm.injective

@[simp]
lemma coeff_inj : x.coeff = y.coeff ↔ x = y := coeff_injective.eq_iff

lemma ofCoeff_inj {x y : ℕ →₀ M} : ofCoeff R x = ofCoeff R y ↔ x = y := ofCoeff_injective.eq_iff

@[ext] alias ⟨ext, _⟩ := coeff_inj

instance instInhabited : Inhabited (PolynomialModule R M) := fast_instance% (coeffEquiv R).inhabited

instance instNontrivial [Nontrivial M] : Nontrivial (PolynomialModule R M) :=
  (coeffEquiv R).nontrivial

instance instUnique [Subsingleton M] : Unique (PolynomialModule R M) := fast_instance%
  (coeffEquiv R).unique

instance instDecidableEq [DecidableEq M] : DecidableEq (PolynomialModule R M) :=
  (coeffEquiv R).decidableEq

instance instAddCommGroup : AddCommGroup (PolynomialModule R M) := fast_instance%
  (coeffEquiv R).addCommGroup

instance instIsCancelAdd [IsCancelAdd R] : IsCancelAdd (PolynomialModule R M) :=
  (coeffEquiv R).isCancelAdd

/-- `PolynomialModule.coeff` as an `AddEquiv`. -/
@[simps! apply symm_apply]
def coeffAddEquiv : PolynomialModule R M ≃+ (ℕ →₀ M) := (coeffEquiv R).addEquiv

@[simp] lemma coeff_zero : coeff (0 : PolynomialModule R M) = 0 := rfl
@[simp] lemma ofCoeff_zero : (ofCoeff R 0 : PolynomialModule R M) = 0 := rfl
@[simp] lemma coeff_eq_zero : coeff x = 0 ↔ x = 0 := coeff_inj
@[simp] lemma ofCoeff_eq_zero {x : ℕ →₀ M} : ofCoeff R x = 0 ↔ x = 0 :=
  ofCoeff_inj

@[simp] lemma coeff_add (x y : PolynomialModule R M) : coeff (x + y) = coeff x + coeff y := rfl
@[simp] lemma ofCoeff_add (x y : ℕ →₀ M) : ofCoeff R (x + y) = ofCoeff R x + ofCoeff R y := rfl

@[simp]
lemma coeff_sum (s : Finset ι) (f : ι → PolynomialModule R M) :
    coeff (∑ i ∈ s, f i) = ∑ i ∈ s, coeff (f i) := map_sum coeffAddEquiv ..

@[simp]
lemma ofCoeff_sum (s : Finset ι) (f : ι → ℕ →₀ M) :
    ofCoeff R (∑ i ∈ s, f i) = ∑ i ∈ s, ofCoeff R (f i) := map_sum coeffAddEquiv.symm ..

@[simp]
lemma coeff_finsuppSum [AddCommMonoid N] (f : ι →₀ N) (g : ι → N → PolynomialModule R M) :
    coeff (f.sum g) = f.sum (fun i n ↦ coeff (g i n)) := map_finsuppSum coeffAddEquiv ..

@[simp]
lemma ofCoeff_finsuppSum [AddCommMonoid N] (f : ι →₀ N) (g : ι → N → ℕ →₀ M) :
    ofCoeff R (f.sum g) = f.sum (fun i n ↦ ofCoeff R (g i n)) :=
  map_finsuppSum coeffAddEquiv.symm ..

variable (R) in
/-- `MonoidAlgebra.single n m` for `m : M`, `r : R` is the element `rm : PolynomialModule R M`. -/
def single (n : ℕ) (m : M) : PolynomialModule R M := .ofCoeff R <| .single n m

@[simp] lemma coeff_single (n : ℕ) (m : M) : (single R n m).coeff = .single n m := rfl
@[simp] lemma ofCoeff_single (n : ℕ) (m : M) : ofCoeff R (.single n m) = single R n m := rfl

@[simp] lemma single_zero (n : ℕ) : single R n (0 : M) = 0 := by simp [single]

@[simp]
lemma single_add (n : ℕ) (m₁ m₂ : M) :
    single R n (m₁ + m₂) = single R n m₁ + single R n m₂ := by ext; simp

/-- Workaround to defeq problems: if we interpret a `PolynomialModule` as a `Finsupp`, also transfer
the `DFunLike` instance. -/
@[simp]
theorem funLike_eq (x : PolynomialModule R M) :
    DFunLike.coe (self := Finsupp.instFunLike) x = x := rfl

/-- This is required to have the `IsScalarTower S R M` instance to avoid diamonds. -/
instance : Module S (PolynomialModule R M) := (coeffEquiv R).module _

instance (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M] :
    IsScalarTower S R (PolynomialModule R M) := (coeffEquiv R).isScalarTower _ _

variable (R S) in
/-- `PolynomialModule.coeff` as a linear equiv. -/
@[simps! apply symm_apply]
def coeffLinearEquiv : PolynomialModule R M ≃ₗ[S] ℕ →₀ M := (coeffEquiv _).linearEquiv _

variable (R) in
/-- `PolynomialModule.single` as a linear map. -/
def lsingle (i : ℕ) : M →ₗ[R] PolynomialModule R M :=
  (coeffLinearEquiv R R).symm.comp <| Finsupp.lsingle i

theorem lsingle_apply (i : ℕ) (m : M) (n : ℕ) : (lsingle R i m).coeff n = ite (i = n) m 0 :=
  Finsupp.single_apply

theorem single_smul (i : ℕ) (r : R) (m : M) : single R i (r • m) = r • single R i m :=
  (lsingle R i).map_smul r m

@[elab_as_elim]
lemma induction_linear {p : PolynomialModule R M → Prop} (x : PolynomialModule R M) (zero : p 0)
    (add : ∀ x y : PolynomialModule R M, p x → p y → p (x + y))
    (single : ∀ n m, p (single R n m)) : p x :=
  Finsupp.induction_linear (motive := (p <| ofCoeff R ·)) x.coeff zero (fun _ _ ↦ add _ _)
    (fun _ _ ↦ single _ _)

instance polynomialModule : Module R[X] (PolynomialModule R M) :=
  inferInstanceAs <| Module R[X] <| Module.AEval' <| (coeffLinearEquiv R R).symm.comp <|
    (Finsupp.lmapDomain M R Nat.succ).comp (coeffLinearEquiv R R).toLinearMap

lemma smul_def (f : R[X]) (m : PolynomialModule R M) :
    f • m = aeval ((coeffLinearEquiv R R).symm.comp <|
    (Finsupp.lmapDomain M R Nat.succ).comp (coeffLinearEquiv R R).toLinearMap) f m := by
  rfl

instance isScalarTower' (M : Type u) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower S R M] : IsScalarTower S R[X] (PolynomialModule R M) := by
  haveI : IsScalarTower R R[X] (PolynomialModule R M) :=
    inferInstanceAs <| IsScalarTower R R[X] <| Module.AEval' <| (coeffLinearEquiv R R).symm.comp <|
    (Finsupp.lmapDomain M R Nat.succ).comp (coeffLinearEquiv R R).toLinearMap
  constructor
  intro x y z
  rw [← @IsScalarTower.algebraMap_smul S R, ← @IsScalarTower.algebraMap_smul S R, smul_assoc]

@[simp]
theorem monomial_smul_single (i : ℕ) (r : R) (j : ℕ) (m : M) :
    monomial i r • single R j m = single R (i + j) (r • m) := by
  simp only [Module.End.mul_apply, Polynomial.aeval_monomial, Module.End.pow_apply,
    Module.algebraMap_end_apply, smul_def]
  induction i generalizing r j m with
  | zero =>
    rw [Function.iterate_zero, zero_add]
    exact congr(ofCoeff R $(Finsupp.smul_single r j m))
  | succ n hn =>
    rw [Function.iterate_succ, Function.comp_apply, add_assoc, ← hn]
    congr 2
    rw [Nat.one_add]
    exact congr(ofCoeff R $(Finsupp.mapDomain_single))

@[simp]
theorem monomial_smul_lsingle (i : ℕ) (r : R) (j : ℕ) (m : M) :
    (monomial i) r • lsingle R j m = lsingle R (i + j) (r • m) :=
  monomial_smul_single ..

@[simp]
theorem monomial_smul_apply (i : ℕ) (r : R) (g : PolynomialModule R M) (n : ℕ) :
    (monomial i r • g).coeff n = ite (i ≤ n) (r • g.coeff (n - i)) 0 := by
  induction g using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp [smul_add, hp, hq, ite_add_ite]
  | single =>
    simp [monomial_smul_single, Finsupp.single_apply]
    grind

@[simp]
theorem smul_single_apply (i : ℕ) (f : R[X]) (m : M) (n : ℕ) :
    (f • single R i m).coeff n = ite (i ≤ n) (f.coeff (n - i) • m) 0 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [add_smul, hp, hq, ite_add_ite]
  | monomial => simp; grind [monomial_smul_single, coeff_monomial, zero_smul]

theorem smul_apply (f : R[X]) (g : PolynomialModule R M) (n : ℕ) :
    (f • g).coeff n = ∑ x ∈ Finset.antidiagonal n, f.coeff x.1 • g.coeff x.2 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [add_smul, hp, hq, ← Finset.sum_add_distrib]
  | monomial f_n f_a =>
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j =>
      (monomial f_n f_a).coeff i • g.coeff j, monomial_smul_apply]
    simp [Polynomial.coeff_monomial]

set_option backward.isDefEq.respectTransparency false in
/-- `PolynomialModule R R` is isomorphic to `R[X]` as an `R[X]` module. -/
def equivPolynomialSelf : PolynomialModule R R ≃ₗ[R[X]] R[X] where
  toAddEquiv := coeffAddEquiv.trans <| AddMonoidAlgebra.coeffAddEquiv.symm.trans
    (toFinsuppIso R).symm.toAddEquiv
  map_smul' r x := by
    dsimp
    induction x using induction_linear with
    | zero => simp
    | add _ _ hp hq => simp_all [smul_add, mul_add]
    | single n a =>
    ext i
    simp only [coeffAddEquiv_apply, AddMonoidAlgebra.coeffAddEquiv_symm_apply,
      toFinsuppIso_symm_apply, coeff_ofFinsupp, smul_single_apply, smul_eq_mul, coeff_single,
      AddMonoidAlgebra.ofCoeff_single, ofFinsupp_single]
    split_ifs with hn
    · rw [show i = (i - n) + n by lia, Polynomial.coeff_mul_monomial]
      simp
    · rw [Polynomial.coeff_mul, Finset.sum_eq_zero]
      simp [Polynomial.coeff_monomial]
      lia

/-- `PolynomialModule R S` is isomorphic to `S[X]` as an `R` module. -/
def equivPolynomial {S : Type*} [CommRing S] [Algebra R S] : PolynomialModule R S ≃ₗ[R] S[X] where
  toAddEquiv := coeffAddEquiv.trans <| AddMonoidAlgebra.coeffAddEquiv.symm.trans
    (toFinsuppIso _).symm.toAddEquiv
  map_smul' _ _ := rfl

@[simp]
lemma equivPolynomialSelf_apply_eq (p : PolynomialModule R R) :
    equivPolynomialSelf p = equivPolynomial p := rfl

@[simp]
lemma equivPolynomial_single {S : Type*} [CommRing S] [Algebra R S] (n : ℕ) (x : S) :
    equivPolynomial (single R n x) = monomial n x := rfl

@[simp]
lemma equivPolynomial_symm_monomial {S : Type*} [CommRing S] [Algebra R S] (n : ℕ) (x : S) :
    equivPolynomial.symm (monomial n x) = single R n x := rfl

@[simp]
lemma equivPolynomial_symm_one {S : Type*} [CommRing S] [Algebra R S] :
    equivPolynomial.symm (1 : S[X]) = single R 0 1 := rfl

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']
variable [Module R M']

/-- Two `R`-linear maps from `PolynomialModule R M` which are equal
after pre-composition with every `lsingle R a` are equal. -/
@[ext high]
theorem hom_ext {f g : PolynomialModule R M →ₗ[R] M'}
    (h : ∀ a, f ∘ₗ lsingle R a = g ∘ₗ lsingle R a) : f = g := by
  simpa [← DFunLike.coe_fn_eq, funext_iff, PolynomialModule.forall] using Finsupp.lhom_ext'
    (φ := f.comp (coeffLinearEquiv R R).symm.toLinearMap)
    (ψ := g.comp (coeffLinearEquiv R R (M := M)).symm.toLinearMap) h

/-- The image of a polynomial under a linear map. -/
def map (f : M →ₗ[R] M') : PolynomialModule R M →ₗ[R] PolynomialModule R' M' :=
  (coeffLinearEquiv ..).symm.toLinearMap.comp <| (Finsupp.mapRange.linearMap f).comp <|
    (coeffLinearEquiv ..).toLinearMap

@[simp]
theorem map_single (f : M →ₗ[R] M') (i : ℕ) (m : M) :
    map R' f (single R i m) = single R' i (f m) := by simp [map]

@[simp]
theorem map_lsingle (f : M →ₗ[R] M') (i : ℕ) (m : M) :
    map R' f (lsingle R i m) = lsingle R' i (f m) :=
  map_single ..

variable [Algebra R R'] [IsScalarTower R R' M']

theorem map_smul (f : M →ₗ[R] M') (p : R[X]) (q : PolynomialModule R M) :
    map R' f (p • q) = p.map (algebraMap R R') • map R' f q := by
  induction q using induction_linear with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add f g e₁ e₂ => rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  | single i m =>
    induction p using Polynomial.induction_on' with
    | add _ _ e₁ e₂ => rw [add_smul, map_add, e₁, e₂, Polynomial.map_add, add_smul]
    | monomial => rw [monomial_smul_single, map_single, Polynomial.map_monomial, map_single,
        monomial_smul_single, f.map_smul, algebraMap_smul]

/-- Evaluate a polynomial `p : PolynomialModule R M` at `r : R`. -/
@[simps! -isSimp]
def eval (r : R) : PolynomialModule R M →ₗ[R] M where
  toFun p := p.coeff.sum fun i m => r ^ i • m
  map_add' _ _ := Finsupp.sum_add_index' (fun _ => smul_zero _) fun _ _ _ => smul_add _ _ _
  map_smul' s m := by
    refine (Finsupp.sum_smul_index' ?_).trans ?_
    · exact fun i => smul_zero _
    · simp_rw [RingHom.id_apply, Finsupp.smul_sum]
      congr
      ext i c
      rw [smul_comm]

@[simp]
theorem eval_single (r : R) (i : ℕ) (m : M) : eval r (single R i m) = r ^ i • m :=
  Finsupp.sum_single_index (smul_zero _)

@[simp]
theorem eval_lsingle (r : R) (i : ℕ) (m : M) : eval r (lsingle R i m) = r ^ i • m :=
  eval_single r i m

@[simp]
theorem eval_smul (p : R[X]) (q : PolynomialModule R M) (r : R) :
    eval r (p • q) = p.eval r • eval r q := by
  induction q using induction_linear with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add f g e₁ e₂ => rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  | single i m =>
    induction p using Polynomial.induction_on' with
    | add _ _ e₁ e₂ => rw [add_smul, map_add, Polynomial.eval_add, e₁, e₂, add_smul]
    | monomial => simp only [monomial_smul_single, Polynomial.eval_monomial, eval_single]; module

@[simp]
theorem eval_map (f : M →ₗ[R] M') (q : PolynomialModule R M) (r : R) :
    eval (algebraMap R R' r) (map R' f q) = f (eval r q) := by
  induction q using induction_linear with
  | zero => simp_rw [map_zero]
  | add f g e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single i m => simp only [map_single, eval_single, f.map_smul]; module

@[simp]
theorem eval_map' (f : M →ₗ[R] M) (q : PolynomialModule R M) (r : R) :
    eval r (map R f q) = f (eval r q) :=
  eval_map R f q r

@[simp]
lemma aeval_equivPolynomial {S : Type*} [CommRing S] [Algebra S R]
    (f : PolynomialModule S S) (x : R) :
    aeval x (equivPolynomial f) = eval x (map R (Algebra.linearMap S R) f) := by
  induction f using induction_linear with
  | zero => simp
  | add f g e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single i m => rw [equivPolynomial_single, aeval_monomial, mul_comm, map_single,
      Algebra.linearMap_apply, eval_single, smul_eq_mul]

/-- `comp p q` is the composition of `p : R[X]` and `q : M[X]` as `q(p(x))`. -/
@[simps!]
def comp (p : R[X]) : PolynomialModule R M →ₗ[R] PolynomialModule R M :=
  LinearMap.comp ((eval p).restrictScalars R) (map R[X] (lsingle R 0))

theorem comp_single (p : R[X]) (i : ℕ) (m : M) : comp p (single R i m) = p ^ i • single R 0 m := by
  rw [comp_apply, map_single, eval_single]
  rfl

theorem comp_eval (p : R[X]) (q : PolynomialModule R M) (r : R) :
    eval r (comp p q) = eval (p.eval r) q := by
  rw [← LinearMap.comp_apply]
  induction q using induction_linear with
  | zero => simp_rw [map_zero]
  | add _ _ e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single i m =>
    rw [LinearMap.comp_apply, comp_single, eval_single, eval_smul, eval_single, eval_pow]
    module

theorem comp_smul (p p' : R[X]) (q : PolynomialModule R M) :
    comp p (p' • q) = p'.comp p • comp p q := by
  rw [comp_apply, map_smul, eval_smul, Polynomial.comp, Polynomial.eval_map, comp_apply]
  rfl

end PolynomialModule
