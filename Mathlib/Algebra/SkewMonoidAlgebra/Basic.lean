/-
Copyright (c) 2024 María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos Fernández, Xavier Généreux
-/
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Algebra.NonUnitalHom

/-!
# Skew Monoid Algebras

Given a monoid `G` acting on a ring `k`, the skew monoid algebra of `G` over `k` is the set
of finitely supported functions `f : G → k` for which addition is defined pointwise and
multiplication of two elements `f` and `g` is given by the finitely supported function whose
value at `a` is the sum of `f x * (x • g y)` over all pairs `x, y` such that `x * y = a`,
where `•` denotes the action of `G` on `k`. When this action is trivial, this product is
the usual convolution product.

In fact the construction of the skew monoid algebra makes sense when `G` is not even a monoid, but
merely a magma, i.e., when `G` carries a multiplication which is not required to satisfy any
conditions at all, and `k` is a not-necessarily-associative semiring. In this case the construction
yields a not-necessarily-unital, not-necessarily-associative algebra.

## Main Definitions
- `SkewMonoidAlgebra k G`: the skew monoid algebra of `G` over `k` is the type of finite formal
`k`-linear combinations of terms of `G`, endowed with a skewed convolution product.

## TODO
- the algebra instance (see #10541)
- lifting lemmas (see #10541)
-/


noncomputable section

/-- The skew monoid algebra of `G` over `k` is the type of finite formal `k`-linear
combinations of terms of `G`, endowed with a skewed convolution product. -/
structure SkewMonoidAlgebra (k : Type*) (G : Type*) [Zero k] where
  /-- The natural map from `G →₀ k` to `SkewMonoidAlgebra k G`. -/
  ofFinsupp ::
  /-- The natural map from `SkewMonoidAlgebra k G` to `G →₀ k`. -/
  toFinsupp : G →₀ k

open Function
namespace SkewMonoidAlgebra

variable {k G : Type*}

section AddMonoid

variable [AddMonoid k]

@[simp]
theorem eta (f : SkewMonoidAlgebra k G) : ofFinsupp f.toFinsupp = f := rfl

@[irreducible]
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

instance : Zero (SkewMonoidAlgebra k G) := ⟨⟨0⟩⟩

instance : Add (SkewMonoidAlgebra k G) := ⟨add⟩

instance {S : Type*} [SMulZeroClass S k] :
    SMulZeroClass S (SkewMonoidAlgebra k G) where
  smul s f := smul s f
  smul_zero a := by exact congr_arg ofFinsupp (smul_zero a)

@[simp]
theorem ofFinsupp_zero : (⟨0⟩ : SkewMonoidAlgebra k G) = 0 := rfl

@[simp]
theorem ofFinsupp_add {a b} : (⟨a + b⟩ : SkewMonoidAlgebra k G) = ⟨a⟩ + ⟨b⟩ :=
  show _ = add _ _ by rw [add]

@[simp]
theorem ofFinsupp_smul {S : Type*} [SMulZeroClass S k] (a : S) (b : G →₀ k) :
    (⟨a • b⟩ : SkewMonoidAlgebra k G) = (a • ⟨b⟩ : SkewMonoidAlgebra k G) :=
  show _ = smul _ _ by rw [smul]

@[simp]
theorem toFinsupp_zero : (0 : SkewMonoidAlgebra k G).toFinsupp = 0 := rfl

@[simp]
theorem toFinsupp_add (a b : SkewMonoidAlgebra k G) :
    (a + b).toFinsupp = a.toFinsupp + b.toFinsupp := by
  rw [← ofFinsupp_add]

@[simp]
theorem toFinsupp_smul {S : Type*} [SMulZeroClass S k] (a : S) (b : SkewMonoidAlgebra k G) :
    (a • b).toFinsupp = a • b.toFinsupp := by
  rw [← ofFinsupp_smul]

theorem _root_.IsSMulRegular.skewMonoidAlgebra {S : Type*} [Monoid S] [DistribMulAction S k] {a : S}
    (ha : IsSMulRegular k a) : IsSMulRegular (SkewMonoidAlgebra k G) a
  | ⟨_⟩, ⟨_⟩, h => by
    exact congr_arg _ <| ha.finsupp (ofFinsupp.inj h)

theorem toFinsupp_injective :
    Function.Injective (toFinsupp : SkewMonoidAlgebra k G → Finsupp _ _) :=
  fun ⟨_⟩ _ ↦ congr_arg _

@[simp]
theorem toFinsupp_inj {a b : SkewMonoidAlgebra k G} : a.toFinsupp = b.toFinsupp ↔ a = b :=
  toFinsupp_injective.eq_iff

theorem ofFinsupp_injective :
    Function.Injective (ofFinsupp : Finsupp _ _ → SkewMonoidAlgebra k G) :=
  fun _ _ ↦ congr_arg toFinsupp

/-- A variant of `SkewMonoidAlgebra.ofFinsupp_injective` in terms of `Iff`. -/
theorem ofFinsupp_inj {a b} : (⟨a⟩ : SkewMonoidAlgebra k G) = ⟨b⟩ ↔ a = b :=
  ofFinsupp_injective.eq_iff

@[simp]
theorem toFinsupp_eq_zero {a : SkewMonoidAlgebra k G} : a.toFinsupp = 0 ↔ a = 0 :=
  toFinsupp_inj

@[simp]
theorem ofFinsupp_eq_zero {a} : (⟨a⟩ : SkewMonoidAlgebra k G) = 0 ↔ a = 0 :=
  ofFinsupp_inj

instance : Inhabited (SkewMonoidAlgebra k G) := ⟨0⟩

instance [Nontrivial k] [Nonempty G] :
    Nontrivial (SkewMonoidAlgebra k G) := Function.Injective.nontrivial ofFinsupp_injective

instance [Subsingleton k] : Unique (SkewMonoidAlgebra k G) :=
  Function.Injective.unique toFinsupp_injective

instance : AddMonoid (SkewMonoidAlgebra k G) where
  __ := toFinsupp_injective.addMonoid _ toFinsupp_zero toFinsupp_add
    (fun _ _ ↦ toFinsupp_smul _ _)

section Support

/-- For `f : SkewMonoidAlgebra k G`, `f.support` is the set of all `a ∈ G` such that
`f a ≠ 0`. -/
def support : SkewMonoidAlgebra k G → Finset G
  | ⟨p⟩ => p.support

@[simp]
theorem support_ofFinsupp (p) : support (⟨p⟩ : SkewMonoidAlgebra k G) = p.support := by
  rw [support]

theorem support_toFinsupp (p : SkewMonoidAlgebra k G) : p.toFinsupp.support = p.support := by
  rw [support]

@[simp]
theorem support_zero : (0 : SkewMonoidAlgebra k G).support = ∅ := rfl

@[simp]
theorem support_eq_empty {p} : p.support = ∅ ↔ (p : SkewMonoidAlgebra k G) = 0 := by
  rcases p
  simp only [support, Finsupp.support_eq_empty, ofFinsupp_eq_zero]

end Support

section Coeff

/-- `coeff f a` (often denoted `f.coeff a`) is the coefficient of `a` in `f`. -/
def coeff : SkewMonoidAlgebra k G → G → k
  | ⟨p⟩ => p

@[simp]
theorem coeff_ofFinsupp (p) : coeff (⟨p⟩ : SkewMonoidAlgebra k G) = p := rfl

theorem coeff_injective : Injective (coeff : SkewMonoidAlgebra k G → G → k) := by
  rintro ⟨p⟩ ⟨q⟩
  simp only [coeff, DFunLike.coe_fn_eq, imp_self, ofFinsupp.injEq]

@[simp]
theorem coeff_inj (p q : SkewMonoidAlgebra k G) : p.coeff = q.coeff ↔ p = q :=
  coeff_injective.eq_iff

@[simp]
theorem toFinsupp_apply (f : SkewMonoidAlgebra k G) (g) : f.toFinsupp g = f.coeff g := rfl

@[simp]
theorem coeff_zero (g : G) : coeff (0 : SkewMonoidAlgebra k G) g = 0 := rfl

@[simp]
theorem mem_support_iff {f : SkewMonoidAlgebra k G} {a : G} : a ∈ f.support ↔ f.coeff a ≠ 0 := by
  rcases f with ⟨⟩
  simp only [coeff, support_ofFinsupp, Finsupp.mem_support_iff, ne_eq]

theorem notMem_support_iff {f : SkewMonoidAlgebra k G} {a : G} :
    a ∉ f.support ↔ f.coeff a = 0 := by
  simp only [mem_support_iff, ne_eq, not_not]

@[deprecated (since := "2025-05-23")] alias not_mem_support_iff := notMem_support_iff

theorem ext_iff {p q : SkewMonoidAlgebra k G} : p = q ↔ ∀ n, coeff p n = coeff q n := by
  rcases p with ⟨f : G →₀ k⟩
  rcases q with ⟨g : G →₀ k⟩
  simpa [coeff] using DFunLike.ext_iff (f := f) (g := g)

@[ext]
theorem ext {p q : SkewMonoidAlgebra k G} : (∀ a, coeff p a = coeff q a) → p = q := ext_iff.2

@[simp]
theorem coeff_add (p q : SkewMonoidAlgebra k G) (a : G) :
    coeff (p + q) a = coeff p a + coeff q a := by
  rcases p
  rcases q
  simp_rw [← ofFinsupp_add, coeff]
  exact Finsupp.add_apply _ _ _

@[simp]
theorem coeff_smul {S} [SMulZeroClass S k] (r : S) (p : SkewMonoidAlgebra k G) (a : G) :
    coeff (r • p) a = r • coeff p a := by
  rfl

end Coeff

section Single

/-- `single a b` is the finitely supported function with value `b` at `a` and zero otherwise. -/
def single (a : G) (b : k) : SkewMonoidAlgebra k G := ⟨Finsupp.single a b⟩

@[simp]
theorem toFinsupp_single (a : G) (b : k) : (single a b).toFinsupp = Finsupp.single a b := rfl

@[simp]
theorem ofFinsupp_single (a : G) (b : k) : ⟨Finsupp.single a b⟩ = single a b := rfl

theorem coeff_single (a : G) (b : k) [DecidableEq G] :
    coeff (single a b) = Pi.single a b := by
  simp [coeff, Finsupp.single_eq_pi_single]

theorem coeff_single_apply {a a' : G} {b : k} [Decidable (a = a')] :
    coeff (single a b) a' = if a = a' then b else 0 := by
  simp [coeff, Finsupp.single_apply]

theorem single_zero_right (a : G) : single a (0 : k) = 0 := by
  simp [← toFinsupp_inj]

@[simp]
theorem single_add (a : G) (b₁ b₂ : k) : single a (b₁ + b₂) = single a b₁ + single a b₂ := by
  simp [← toFinsupp_inj]

@[simp]
theorem single_zero (a : G) : (single a 0 : SkewMonoidAlgebra k G) = 0 := by
  simp [← toFinsupp_inj]

theorem single_eq_zero {a : G} {b : k} : single a b = 0 ↔ b = 0 := by
  simp [← toFinsupp_inj]

/-- Group isomorphism between `SkewMonoidAlgebra k G` and `G →₀ k`. -/
@[simps apply symm_apply]
def toFinsuppAddEquiv : SkewMonoidAlgebra k G ≃+ (G →₀ k) where
  toFun        := toFinsupp
  invFun       := ofFinsupp
  map_add'     := toFinsupp_add

theorem smul_single {S} [SMulZeroClass S k] (s : S) (a : G) (b : k) :
    s • single a b = single a (s • b) :=
  toFinsupp_injective <| by simp;

theorem single_injective (a : G) : Function.Injective (single a : k → SkewMonoidAlgebra k G) :=
  toFinsuppAddEquiv.symm.injective.comp (Finsupp.single_injective a)

theorem _root_.IsSMulRegular.skewMonoidAlgebra_iff {S : Type*} [Monoid S] [DistribMulAction S k]
    {a : S} [Nonempty G] : IsSMulRegular k a ↔ IsSMulRegular (SkewMonoidAlgebra k G) a := by
  inhabit G
  refine ⟨IsSMulRegular.skewMonoidAlgebra, fun ha b₁ b₂ inj ↦ ?_⟩
  rw [← (single_injective _).eq_iff, ← smul_single, ← smul_single] at inj
  exact single_injective (default) (ha inj)

end Single

end AddMonoid

section AddMonoidWithOne

section One

variable [One G] [AddMonoidWithOne k]

/-- The unit of the multiplication is `single 1 1`, i.e. the function that is `1` at `1` and
  zero elsewhere. -/
instance : One (SkewMonoidAlgebra k G) where
  one := single 1 1

instance : AddMonoidWithOne (SkewMonoidAlgebra k G) where

theorem ofFinsupp_one : (⟨Finsupp.single 1 1⟩ : SkewMonoidAlgebra k G) = 1 := rfl

@[simp]
theorem toFinsupp_one : (1 : SkewMonoidAlgebra k G).toFinsupp = Finsupp.single 1 1 := rfl

@[simp]
theorem toFinsupp_eq_single_one_one_iff {a : SkewMonoidAlgebra k G} :
    a.toFinsupp = Finsupp.single 1 1 ↔ a = 1 := by
  simp [← toFinsupp_inj]

@[simp]
theorem ofFinsupp_eq_one {a} :
    (⟨a⟩ : SkewMonoidAlgebra k G) = 1 ↔ a = Finsupp.single 1 1 := by
  simp [← toFinsupp_inj]

@[simp]
theorem single_one_one : single (1 : G) (1 : k) = 1 := rfl

theorem one_def : (1 : SkewMonoidAlgebra k G) = single 1 1 := rfl

@[simp]
theorem coeff_one_one : coeff (1 : SkewMonoidAlgebra k G) 1 = 1 := by
  simp only [coeff, toFinsupp_single, Finsupp.single_eq_same]

theorem coeff_one {a : G} [Decidable (a = 1)] :
    (1 : SkewMonoidAlgebra k G).coeff a = if a = 1 then 1 else 0 := by
  classical
  simpa [eq_comm (a := a)] using coeff_single_apply

theorem natCast_def (n : ℕ) : (n : SkewMonoidAlgebra k G) = single (1 : G) (n : k) := by
  induction n <;> simp_all

@[simp]
lemma single_nat (n : ℕ) : (single 1 n : SkewMonoidAlgebra k G) = n := (natCast_def _).symm

end One

end AddMonoidWithOne

section AddCommMonoid

variable [AddCommMonoid k]

instance : AddCommMonoid (SkewMonoidAlgebra k G) where
  __ := toFinsupp_injective.addCommMonoid _ toFinsupp_zero toFinsupp_add
    (fun _ _ ↦ toFinsupp_smul _ _)

section sum

instance [DecidableEq G] [DecidableEq k] : DecidableEq (SkewMonoidAlgebra k G) :=
  Equiv.decidableEq toFinsuppAddEquiv.toEquiv

/-- `sum f g` is the sum of `g a (f.coeff a)` over the support of `f`. -/
def sum {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G → k → N) : N :=
  f.toFinsupp.sum g

theorem sum_def {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G → k → N) :
    sum f g = f.toFinsupp.sum g := rfl

/-- Unfolded version of `sum_def` in terms of `Finset.sum`. -/
theorem sum_def' {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G → k → N) :
    sum f g = ∑ a ∈ f.support, g a (f.coeff a) := rfl

@[simp]
theorem sum_single_index {N} [AddCommMonoid N] {a : G} {b : k} {h : G → k → N}
    (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.single a b).sum h = h a b :=
  Finsupp.sum_single_index h_zero

theorem map_sum {N P : Type*} [AddCommMonoid N] [AddCommMonoid P] {H : Type*} [FunLike H N P]
    [AddMonoidHomClass H N P] (h : H) (f : SkewMonoidAlgebra k G) (g : G → k → N) :
    h (sum f g) = sum f fun a b ↦ h (g a b) :=
  _root_.map_sum h _ _

/-- Variant where the image of `g` is a `SkewMonoidAlgebra`. -/
theorem toFinsupp_sum' {k' G' : Type*} [AddCommMonoid k'] (f : SkewMonoidAlgebra k G)
    (g : G → k → SkewMonoidAlgebra k' G') :
    (sum f g).toFinsupp = Finsupp.sum f.toFinsupp (toFinsupp <| g · ·) :=
  _root_.map_sum toFinsuppAddEquiv (fun a ↦ g a (f.coeff a)) f.toFinsupp.support

theorem ofFinsupp_sum {k' G' : Type*} [AddCommMonoid k'] (f : G →₀ k)
    (g : G → k → G' →₀ k') :
    (⟨Finsupp.sum f g⟩ : SkewMonoidAlgebra k' G') = sum ⟨f⟩ (⟨g · ·⟩) := by
  apply toFinsupp_injective; simp only [toFinsupp_sum']

theorem sum_single (f : SkewMonoidAlgebra k G) : f.sum single = f := by
  apply toFinsupp_injective; simp only [toFinsupp_sum', toFinsupp_single, Finsupp.sum_single]

/-- Taking the `sum` under `h` is an additive homomorphism, if `h` is an additive homomorphism.
This is a more specific version of `SkewMonoidAlgebra.sum_add_index` with simpler hypotheses. -/
theorem sum_add_index' {S : Type*} [AddCommMonoid S] {f g : SkewMonoidAlgebra k G} {h : G → k → S}
    (hf : ∀ i, h i 0 = 0) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) :
    (f + g).sum h = f.sum h + g.sum h := by
  rw [show f + g = ⟨f.toFinsupp + g.toFinsupp⟩ by rw [ofFinsupp_add, eta]]
  exact Finsupp.sum_add_index' hf h_add

/-- Taking the `sum` under `h` is an additive homomorphism, if `h` is an additive homomorphism.
This is a more general version of `SkewMonoidAlgebra.sum_add_index'`;
the latter has simpler hypotheses. -/
theorem sum_add_index {S : Type*} [DecidableEq G] [AddCommMonoid S]
    {f g : SkewMonoidAlgebra k G} {h : G → k → S} (h_zero : ∀ a ∈ f.support ∪ g.support, h a 0 = 0)
    (h_add : ∀ a ∈ f.support ∪ g.support, ∀ b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) :
    (f + g).sum h = f.sum h + g.sum h := by
  rw [show f + g = ⟨f.toFinsupp + g.toFinsupp⟩ by rw [ofFinsupp_add, eta]]
  exact Finsupp.sum_add_index h_zero h_add

@[simp]
theorem sum_add {S : Type*} [AddCommMonoid S] (p : SkewMonoidAlgebra k G) (f g : G → k → S) :
    (p.sum fun n x ↦ f n x + g n x) = p.sum f + p.sum g := Finsupp.sum_add

@[simp]
theorem sum_zero_index {S : Type*} [AddCommMonoid S] {f : G → k → S} :
    (0 : SkewMonoidAlgebra k G).sum f = 0 := by simp [sum]

@[simp]
theorem sum_zero {N : Type*} [AddCommMonoid N] {f : SkewMonoidAlgebra k G} :
    (f.sum fun _ _ ↦ (0 : N)) = 0 := Finset.sum_const_zero

theorem sum_sum_index {α β M N P : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    {f : SkewMonoidAlgebra M α} {g : α → M → SkewMonoidAlgebra N β} {h : β → N → P}
    (h_zero : ∀ (a : β), h a 0 = 0)
    (h_add : ∀ (a : β) (b₁ b₂ : N), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    sum (sum f g) h = sum f fun a b ↦ sum (g a b) h := by
  rw [sum_def, toFinsupp_sum' f g, Finsupp.sum_sum_index h_zero h_add]; simp [sum_def]

@[simp]
theorem coeff_sum {k' G' : Type*} [AddCommMonoid k'] {f : SkewMonoidAlgebra k G}
    {g : G → k → SkewMonoidAlgebra k' G'} {a₂ : G'} :
    (f.sum g).coeff a₂ = f.sum fun a₁ b ↦ (g a₁ b).coeff a₂ := by
  simp_rw [coeff, toFinsupp_sum', sum_def, Finsupp.sum_apply]

theorem sum_mul {S : Type*} [NonUnitalNonAssocSemiring S] (b : S) (s : SkewMonoidAlgebra k G)
    {f : G → k → S} : s.sum f * b = s.sum fun a c ↦ f a c * b := by
  simp only [sum, Finsupp.sum, Finset.sum_mul]

theorem mul_sum {S : Type*} [NonUnitalNonAssocSemiring S] (b : S) (s : SkewMonoidAlgebra k G)
    {f : G → k → S} : b * s.sum f = s.sum fun a c ↦ b * f a c := by
  simp only [sum, Finsupp.sum, Finset.mul_sum]

/-- Analogue of `Finsupp.sum_ite_eq'` for `SkewMonoidAlgebra`. -/
@[simp]
theorem sum_ite_eq' {N : Type*} [AddCommMonoid N] [DecidableEq G] (f : SkewMonoidAlgebra k G)
    (a : G) (b : G → k → N) : (f.sum fun (x : G) (v : k) ↦ if x = a then b x v else 0) =
      if a ∈ f.support then b a (f.coeff a) else 0 := by
  simp only [sum_def', f.toFinsupp.support.sum_ite_eq', support]

theorem smul_sum {M : Type*} {R : Type*} [AddCommMonoid M] [DistribSMul R M]
    {v : SkewMonoidAlgebra k G} {c : R} {h : G → k → M} :
    c • v.sum h = v.sum fun a b ↦ c • h a b := Finsupp.smul_sum

theorem sum_congr {f : SkewMonoidAlgebra k G} {M : Type*} [AddCommMonoid M] {g₁ g₂ : G → k → M}
    (h : ∀ x ∈ f.support, g₁ x (f.coeff x) = g₂ x (f.coeff x)) :
    f.sum g₁ = f.sum g₂ := Finset.sum_congr rfl h

@[elab_as_elim]
theorem induction_on {p : SkewMonoidAlgebra k G → Prop} (f : SkewMonoidAlgebra k G)
    (zero : p 0) (single : ∀ g a, p (single g a)) (add : ∀ f g :
    SkewMonoidAlgebra k G, p f → p g → p (f + g)) : p f := by
  rw [← sum_single f, sum_def']
  exact Finset.sum_induction _ _ add zero (by simp_all)

/-- Slightly less general but more convenient version of `SkewMonoidAlgebra.induction_on`. -/
@[induction_eliminator]
theorem induction_on' [instNonempty : Nonempty G] {p : SkewMonoidAlgebra k G → Prop}
    (f : SkewMonoidAlgebra k G) (single : ∀ g a, p (single g a)) (add : ∀ f g :
    SkewMonoidAlgebra k G, p f → p g → p (f + g)) : p f :=
  induction_on f (by simpa using single (Classical.choice instNonempty) 0) single add

/-- If two additive homomorphisms from `SkewMonoidAlgebra k G ` are equal on each `single a b`,
then they are equal. -/
@[ext high]
theorem addHom_ext {M : Type*} [AddZeroClass M] {f g : SkewMonoidAlgebra k G →+ M}
    (h : ∀ a b, f (single a b) = g (single a b)) : f = g := by
  ext p; induction p using SkewMonoidAlgebra.induction_on <;> simp_all

end sum

section mapDomain

variable {G' G'' : Type*} (f : G → G') {g : G' → G''} (v : SkewMonoidAlgebra k G)

/-- Given `f : G → G'` and `v : SkewMonoidAlgebra k G`, `mapDomain f v : SkewMonoidAlgebra k G'`
is the finitely supported additive homomorphism whose value at `a : G'` is the sum of `v x` over
all `x` such that `f x = a`.
Note that `SkewMonoidAlgebra.mapDomain` is defined as an `AddHom`, while `MonoidAlgebra.mapDomain`
is defined as a function. -/
@[simps]
def mapDomain :
    SkewMonoidAlgebra k G →+ SkewMonoidAlgebra k G' where
  toFun v      := v.sum fun a ↦ single (f a)
  map_zero'    := sum_zero_index
  map_add' _ _ := sum_add_index' (fun _ ↦ single_zero _) fun _ ↦ single_add _

lemma toFinsupp_mapDomain :
    (mapDomain f v).toFinsupp = Finsupp.mapDomain f v.toFinsupp := by
  simp_rw [mapDomain_apply, Finsupp.mapDomain, toFinsupp_sum', single]

variable {f v}

theorem mapDomain_id : mapDomain id v = v := sum_single _

theorem mapDomain_comp : mapDomain (g ∘ f) v = mapDomain g (mapDomain f v) :=
  ((sum_sum_index (single_zero <| g ·) (single_add <| g ·)).trans
    (sum_congr fun _ _ ↦ sum_single_index (single_zero _))).symm

theorem sum_mapDomain_index {k' : Type*} [AddCommMonoid k'] {h : G' → k → k'}
    (h_zero : ∀ (b : G'), h b 0 = 0)
    (h_add : ∀ (b : G') (m₁ m₂ : k), h b (m₁ + m₂) = h b m₁ + h b m₂) :
    sum (mapDomain f v) h = sum v fun a m ↦ h (f a) m :=
  (sum_sum_index h_zero h_add).trans <| sum_congr fun _ _ ↦ sum_single_index (h_zero _)

theorem mapDomain_single {a : G} {b : k} : mapDomain f (single a b) = single (f a) b :=
  sum_single_index <| single_zero _

theorem mapDomain_smul {R : Type*} [Monoid R] [DistribMulAction R k] {b : R} :
    mapDomain f (b • v) = b • mapDomain f v := by
  simp_rw [← toFinsupp_inj, toFinsupp_smul, toFinsupp_mapDomain]
  simp [Finsupp.mapDomain_smul]

/-- A non-commutative version of `SkewMonoidAlgebra.lift`: given an additive homomorphism
`f : k →+ R` and a homomorphism `g : G → R`, returns the additive homomorphism from
`SkewMonoidAlgebra k G` such that `liftNC f g (single a b) = f b * g a`.

If `k` is a semiring and `f` is a ring homomorphism and for all `x : R`, `y : G` the equality
`(f (y • x)) * g y = (g y) * (f x))` holds, then the result is a ring homomorphism (see
`SkewMonoidAlgebra.liftNCRingHom`).

If `R` is a `k`-algebra and `f = algebraMap k R`, then the result is an algebra homomorphism called
`SkewMonoidAlgebra.lift`. -/
def liftNC {R : Type*} [NonUnitalNonAssocSemiring R] (f : k →+ R) (g : G → R) :
    SkewMonoidAlgebra k G →+ R :=
  (Finsupp.liftAddHom fun x ↦ (AddMonoidHom.mulRight (g x)).comp f).comp
    (AddEquiv.toAddMonoidHom toFinsuppAddEquiv)

@[simp] theorem liftNC_single {R : Type*} [NonUnitalNonAssocSemiring R] (f : k →+ R)
    (g : G → R) (a : G) (b : k) : liftNC f g (single a b) = f b * g a :=
  Finsupp.liftAddHom_apply_single _ _ _

theorem eq_liftNC {R : Type*} [NonUnitalNonAssocSemiring R] (f : k →+ R) (g : G → R)
    (l : SkewMonoidAlgebra k G →+ R) (h : ∀ a b, l (single a b) = f b * g a) : l = liftNC f g := by
  ext a b; simp_all

end mapDomain

end AddCommMonoid

section AddGroup

variable [AddGroup k]

private irreducible_def neg : SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩ => ⟨-a⟩

instance : Neg (SkewMonoidAlgebra k G) :=
  ⟨neg⟩

@[simp]
theorem ofFinsupp_neg {a} : (⟨-a⟩ : SkewMonoidAlgebra k G) = -⟨a⟩ :=
  show _ = neg _ by rw [neg_def]

instance : AddGroup (SkewMonoidAlgebra k G) where
  zsmul := zsmulRec
  neg_add_cancel a := by cases a; simp [← ofFinsupp_neg, ← ofFinsupp_add]

@[simp]
theorem toFinsupp_neg (a : SkewMonoidAlgebra k G) : (-a).toFinsupp = -a.toFinsupp :=
  toFinsuppAddEquiv.map_neg a

@[simp]
theorem ofFinsupp_sub {a b} : (⟨a - b⟩ : SkewMonoidAlgebra k G) = ⟨a⟩ - ⟨b⟩ :=
  toFinsuppAddEquiv.symm.map_sub a b

@[simp]
theorem toFinsupp_sub (a b : SkewMonoidAlgebra k G) :
    (a - b).toFinsupp = a.toFinsupp - b.toFinsupp :=
  toFinsuppAddEquiv.map_sub a b

@[simp]
theorem single_neg (a : G) (b : k) : single a (-b) = -single a b := by
  simp [← ofFinsupp_single]

end AddGroup

section AddCommGroup

variable [AddCommGroup k]

instance : AddCommGroup (SkewMonoidAlgebra k G) where
  add_comm

end AddCommGroup

section AddGroupWithOne

variable [AddGroupWithOne k] [One G]

instance : AddGroupWithOne (SkewMonoidAlgebra k G) where
  __ := instAddGroup

theorem intCast_def (z : ℤ) : (z : SkewMonoidAlgebra k G) = single (1 : G) (z : k) := by
  cases z <;> simp

end AddGroupWithOne

section Mul

/- Interaction of `sum` and `•` assuming some multiplication structure. -/
theorem sum_smul_index {N : Type*} [AddCommMonoid N] [NonUnitalNonAssocSemiring k]
    {g : SkewMonoidAlgebra k G} {b : k} {h : G → k → N} (h0 : ∀ i, h i 0 = 0) :
    (b • g).sum h = g.sum (h · <| b * ·) := by
  simp [sum_def, Finsupp.sum_smul_index' h0]

/- Variant of the interaction of `sum` and `•` assuming some scalar multiplication structure. -/
theorem sum_smul_index' {N R : Type*} [AddCommMonoid k]
    [DistribSMul R k] [AddCommMonoid N]
    {g : SkewMonoidAlgebra k G} {b : R} {h : G → k → N} (h0 : ∀ i, h i 0 = 0) :
    (b • g).sum h = g.sum (h · <| b • ·) := by
  simp only [sum_def, toFinsupp_smul, Finsupp.sum_smul_index' h0]

@[simp]
theorem liftNC_one {g_hom R : Type*} [NonAssocSemiring k] [One G] [Semiring R] [FunLike g_hom G R]
    [OneHomClass g_hom G R] (f : k →+* R) (g : g_hom) : liftNC (f : k →+ R) g 1 = 1 := by
  simp only [one_def, liftNC_single, AddMonoidHom.coe_coe, map_one, mul_one]

end Mul

section Mul

variable [Mul G]

section SMul

variable [SMul G k] [NonUnitalNonAssocSemiring k]

/-- The product of `f g : SkewMonoidAlgebra k G` is the finitely supported function whose value
  at `a` is the sum of `f x * (x • g y)` over all pairs `x, y` such that `x * y = a`.
  (Think of a skew group ring.) -/
instance : Mul (SkewMonoidAlgebra k G) :=
  ⟨fun f g ↦ f.sum fun a₁ b₁ ↦ g.sum fun a₂ b₂ ↦ single (a₁ * a₂) (b₁ * (a₁ • b₂))⟩

theorem mul_def {f g : SkewMonoidAlgebra k G} :
    f * g = f.sum fun a₁ b₁ ↦ g.sum fun a₂ b₂ ↦ single (a₁ * a₂) (b₁ * (a₁ • b₂)) :=
  rfl

end SMul

section DistribSMul

instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring k] [DistribSMul G k] :
    NonUnitalNonAssocSemiring (SkewMonoidAlgebra k G) where
  left_distrib f g h := by
    classical
    simp only [mul_def]
    refine Eq.trans (congr_arg (sum f) (funext₂ fun _ _ ↦ sum_add_index ?_ ?_)) ?_ <;>
      simp only [smul_zero, smul_add, mul_add, mul_zero, single_zero, single_add,
        forall_true_iff, sum_add]
  right_distrib f g h := by
    classical
    simp only [mul_def]
    refine Eq.trans (sum_add_index ?_ ?_) ?_ <;>
      simp only [add_mul, zero_mul, single_zero, single_add, forall_true_iff, sum_zero, sum_add]
  zero_mul f := sum_zero_index
  mul_zero f := Eq.trans (congr_arg (sum f) (funext₂ fun _ _ ↦ sum_zero_index)) sum_zero

variable {R : Type*} [Semiring R] [NonAssocSemiring k] [SMul G k]

theorem liftNC_mul {g_hom : Type*} [FunLike g_hom G R]
    [MulHomClass g_hom G R] (f : k →+* R) (g : g_hom) (a b : SkewMonoidAlgebra k G)
    (h_comm : ∀ {x y}, y ∈ a.support → (f (y • b.coeff x)) * g y = (g y) * (f (b.coeff x))) :
    liftNC (f : k →+ R) g (a * b) = liftNC (f : k →+ R) g a * liftNC (f : k →+ R) g b := by
  conv_rhs => rw [← sum_single a, ← sum_single b]
  simp_rw [mul_def, map_sum, liftNC_single, sum_mul, mul_sum]
  refine sum_congr fun y hy ↦ sum_congr fun x _hx ↦ ?_
  simp only [AddMonoidHom.coe_coe, map_mul]
  rw [mul_assoc, ← mul_assoc (f (y • b.coeff x)), h_comm hy, mul_assoc, mul_assoc]

end DistribSMul

end Mul

/-! #### Semiring structure -/

section Semiring

variable [Semiring k] [Monoid G] [MulSemiringAction G k]

open MulSemiringAction

instance : NonUnitalSemiring (SkewMonoidAlgebra k G) where
  mul_assoc f g h := by
    induction f with
    | single x a => induction g with
      | single y b => induction h with
        | single z c => simp [mul_assoc, mul_smul, mul_def]
        | add => simp_all [mul_add]
      | add => simp_all [add_mul, mul_add]
    | add => simp_all [add_mul]

instance : NonAssocSemiring (SkewMonoidAlgebra k G) where
  one_mul f := by
    induction f with
    | single g a => rw [one_def, mul_def, sum_single_index] <;> simp
    | add f g _ _ => simp_all [mul_add]
  mul_one f := by
    induction f with
    | single g a => rw [one_def, mul_def, sum_single_index, sum_single_index] <;> simp
    | add f g _ _ => simp_all [add_mul]

instance : Semiring (SkewMonoidAlgebra k G) where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring

variable {R : Type*} [Semiring R]

/-- `liftNC` as a `RingHom`, for when `f x` and `g y` commute -/
def liftNCRingHom (f : k →+* R) (g : G →* R) (h_comm : ∀ {x y}, (f (y • x)) * g y = (g y) * (f x)) :
    SkewMonoidAlgebra k G →+* R where
  __ := liftNC (f : k →+ R) g
  map_one' := liftNC_one _ _
  map_mul' _ _ :=  liftNC_mul _ _ _ _ fun {_ _} _ ↦ h_comm

end Semiring

/-! #### Derived instances -/

section DerivedInstances

instance instNonUnitalNonAssocRing [Ring k] [Monoid G] [MulSemiringAction G k] :
    NonUnitalNonAssocRing (SkewMonoidAlgebra k G) where
  __ := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

instance instNonUnitalRing [Ring k] [Monoid G] [MulSemiringAction G k] :
    NonUnitalRing (SkewMonoidAlgebra k G) where
  __ := instAddCommGroup
  __ := instNonUnitalSemiring

instance instNonAssocRing [Ring k] [Monoid G] [MulSemiringAction G k] :
    NonAssocRing (SkewMonoidAlgebra k G) where
  __ := instAddCommGroup
  __ := instNonAssocSemiring

instance instCommSemiring [CommSemiring k] [CommMonoid G] [MulSemiringAction G k]
    [SMulCommClass G k k] : CommSemiring (SkewMonoidAlgebra k G) where
  mul_comm a b := by
    have hgk (g : G) (r : k) : g • r = r := by
      rw [← Algebra.algebraMap_self_apply r, smul_algebraMap g r]
    simp only [mul_def, hgk, sum_def]
    rw [Finsupp.sum_comm]
    exact Finsupp.sum_congr (fun x _ ↦ Finsupp.sum_congr
      (fun y _ ↦ by rw [mul_comm, mul_comm (a.toFinsupp y) _]))

instance instRing [Ring k] [Monoid G] [MulSemiringAction G k] : Ring (SkewMonoidAlgebra k G) where
  __ := instNonAssocRing
  __ := instSemiring

variable {S S₁ S₂ : Type*}

instance [AddMonoid k] [DistribSMul S k] :
    DistribSMul S (SkewMonoidAlgebra k G) where
  __ := toFinsupp_injective.distribSMul ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩
    toFinsupp_smul

instance [Monoid S] [AddMonoid k] [DistribMulAction S k] :
    DistribMulAction S (SkewMonoidAlgebra k G) where
  __ := toFinsupp_injective.distribMulAction ⟨⟨toFinsupp, toFinsupp_zero (k := k)⟩, toFinsupp_add⟩
      toFinsupp_smul

instance [Semiring S] [AddCommMonoid k] [Module S k] :
    Module S (SkewMonoidAlgebra k G) where
  __ := toFinsupp_injective.module _ ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩ toFinsupp_smul

instance instFaithfulSMul [AddMonoid k] [SMulZeroClass S k] [FaithfulSMul S k] [Nonempty G] :
    FaithfulSMul S (SkewMonoidAlgebra k G) where
  eq_of_smul_eq_smul {_s₁ _s₂} h := by
    apply eq_of_smul_eq_smul fun a : G →₀ k ↦ congr_arg toFinsupp _
    intro a
    simp_rw [ofFinsupp_smul, h]

instance [AddMonoid k] [SMul S₁ S₂] [SMulZeroClass S₁ k] [SMulZeroClass S₂ k]
    [IsScalarTower S₁ S₂ k] : IsScalarTower S₁ S₂ (SkewMonoidAlgebra k G) :=
  ⟨fun _ _ ⟨_⟩ ↦ by simp_rw [← ofFinsupp_smul, smul_assoc]⟩

instance [AddMonoid k] [SMulZeroClass S₁ k] [SMulZeroClass S₂ k] [SMulCommClass S₁ S₂ k] :
    SMulCommClass S₁ S₂ (SkewMonoidAlgebra k G) :=
  ⟨fun _ _ ⟨_⟩ ↦ by simp_rw [← ofFinsupp_smul, smul_comm _ _ _]⟩

instance [AddMonoid k] [SMulZeroClass S k] [SMulZeroClass Sᵐᵒᵖ k] [IsCentralScalar S k] :
    IsCentralScalar S (SkewMonoidAlgebra k G) :=
  ⟨fun _ ⟨_⟩ ↦ by simp_rw [← ofFinsupp_smul, op_smul_eq_smul]⟩

section Module.Free

variable [Semiring S]

/-- Linear equivalence between `SkewMonoidAlgebra k G` and `G →₀ k`. -/
def toFinsuppLinearEquiv [AddCommMonoid k] [Module S k] : SkewMonoidAlgebra k G ≃ₗ[S] (G →₀ k) :=
  AddEquiv.toLinearEquiv toFinsuppAddEquiv (by simp)

/-- The basis on `SkewMonoidAlgebra k G` with basis vectors `fun i ↦ single i 1` -/
def basisSingleOne [Semiring k] : Module.Basis G k (SkewMonoidAlgebra k G) where
  repr := toFinsuppLinearEquiv

instance [Semiring k] : Module.Free k (SkewMonoidAlgebra k G) :=
  Module.Free.of_basis basisSingleOne

end Module.Free

variable {M α : Type*} [Monoid G] [AddCommMonoid M] [MulAction G α]

/-- Scalar multiplication acting on the domain.

This is not an instance as it would conflict with the action on the range.
See the file `test/instance_diamonds.lean` for examples of such conflicts. -/
def comapSMul [AddCommMonoid M] : SMul G (SkewMonoidAlgebra M α) where smul g := mapDomain (g • ·)

attribute [local instance] comapSMul

theorem comapSMul_def (g : G) (f : SkewMonoidAlgebra M α) : g • f = mapDomain (g • ·) f := rfl

@[simp]
theorem comapSMul_single (g : G) (a : α) (b : M) : g • single a b = single (g • a) b :=
  mapDomain_single

/-- `comapSMul` is multiplicative -/
def comapMulAction : MulAction G (SkewMonoidAlgebra M α) where
  one_smul f := by rw [comapSMul_def, one_smul_eq_id, mapDomain_id]
  mul_smul g g' f := by
    rw [comapSMul_def, comapSMul_def, comapSMul_def, ← comp_smul_left, mapDomain_comp]

attribute [local instance] comapMulAction
/-- This is not an instance as it conflicts with `SkewMonoidAlgebra.distribMulAction`
  when `G = kˣ`. -/
def comapDistribMulActionSelf [AddCommMonoid k] :
    DistribMulAction G (SkewMonoidAlgebra k G) where
  smul_zero g := by
    ext
    simp [comapSMul_def, mapDomain]
  smul_add g f f' := by
    ext
    simp [comapSMul_def, map_add]

end DerivedInstances

section coeff_mul

variable [Semiring k]

section Monoid

variable [Monoid G] [MulSemiringAction G k]

theorem coeff_mul [DecidableEq G] (f g : SkewMonoidAlgebra k G)
    (x : G) : (f * g).coeff x = f.sum fun a₁ b₁ ↦ g.sum fun a₂ b₂ ↦
      if a₁ * a₂ = x then b₁ * a₁ • b₂ else 0 := by
  rw [mul_def, coeff_sum]; congr; ext
  rw [coeff_sum]; congr; ext
  exact coeff_single_apply

theorem coeff_mul_antidiagonal_of_finset (f g : SkewMonoidAlgebra k G) (x : G)
    (s : Finset (G × G)) (hs : ∀ {p : G × G}, p ∈ s ↔ p.1 * p.2 = x) :
    (f * g).coeff x = ∑ p ∈ s, f.coeff p.1 * p.1 • g.coeff p.2 := by
  classical
  let F : G × G → k := fun p ↦ if p.1 * p.2 = x then f.coeff p.1 * p.1 • g.coeff p.2 else 0
  calc
    (f * g).coeff x = ∑ a₁ ∈ f.support, ∑ a₂ ∈ g.support, F (a₁, a₂) := coeff_mul f g x
    _ = ∑ p ∈ f.support ×ˢ g.support, F p := by rw [← Finset.sum_product _ _ _]
    _ = ∑ p ∈ (f.support ×ˢ g.support).filter fun p : G × G ↦ p.1 * p.2 = x,
      f.coeff p.1 * p.1 • g.coeff p.2 := (Finset.sum_filter _ _).symm
    _ = ∑ p ∈ s.filter fun p : G × G ↦ p.1 ∈ f.support ∧ p.2 ∈ g.support,
      f.coeff p.1 * p.1 • g.coeff p.2 :=
      (Finset.sum_congr (by ext; simp [Finset.mem_filter, Finset.mem_product, hs, and_comm])
        fun _ _ ↦ rfl)
    _ = ∑ p ∈ s, f.coeff p.1 * p.1 • g.coeff p.2 :=
      Finset.sum_subset (Finset.filter_subset _ _) fun p hps hp ↦ by
        simp only [Finset.mem_filter, mem_support_iff, not_and, Classical.not_not] at hp ⊢
        by_cases h1 : f.coeff p.1 = 0 <;> simp_all

theorem coeff_mul_antidiagonal_finsum (f g : SkewMonoidAlgebra k G) (x : G) :
    (f * g).coeff x = ∑ᶠ p ∈ {p : G × G | p.1 * p.2 = x}, f.coeff p.1 * p.1 • g.coeff p.2 := by
  have : ({p : G × G | p.1 * p.2 = x}
      ∩ Function.support fun p ↦ f.coeff p.1 * p.1 • g.coeff p.2).Finite := by
    apply Set.Finite.inter_of_right
    apply Set.Finite.subset (Finset.finite_toSet ((f.support).product (g.support)))
    aesop
  rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ this]
  classical
  let s := Set.Finite.toFinset (s := ({p : G × G | p.1 * p.2 = x}
    ∩ Function.support fun p ↦ f.coeff p.1 * p.1 • g.coeff p.2)) this
  let F : G × G → k := fun p ↦ if p.1 * p.2 = x then f.coeff p.1 * p.1 • g.coeff p.2 else 0
  calc
    (f * g).coeff x = ∑ a₁ ∈ f.support, ∑ a₂ ∈ g.support, F (a₁, a₂) := coeff_mul f g x
    _ = ∑ p ∈ f.support ×ˢ g.support, F p := by rw [← Finset.sum_product _ _ _]
    _ = ∑ p ∈ (f.support ×ˢ g.support).filter fun p : G × G ↦ p.1 * p.2 = x,
      f.coeff p.1 * p.1 • g.coeff p.2 := (Finset.sum_filter _ _).symm
    _ = ∑ p ∈ s.filter fun p : G × G ↦ p.1 ∈ f.support ∧ p.2 ∈ g.support,
      f.coeff p.1 * p.1 • g.coeff p.2 := by
        apply Finset.sum_congr_of_eq_on_inter <;> aesop
    _ = ∑ p ∈ s, f.coeff p.1 * p.1 • g.coeff p.2 :=
      Finset.sum_subset (Finset.filter_subset _ _) fun p hps hp ↦ by
        simp only [Finset.mem_filter, mem_support_iff, not_and, Classical.not_not] at hp ⊢
        by_cases h1 : f.coeff p.1 = 0 <;> simp_all

theorem coeff_mul_single_aux (f : SkewMonoidAlgebra k G) {r : k} {x y z : G}
    (H : ∀ a, a * x = z ↔ a = y) : (f * single x r).coeff z = f.coeff y * y • r := by
  classical
  have A : ∀ a₁ b₁, ((single x r).sum fun a₂ b₂ ↦ ite (a₁ * a₂ = z) (b₁ * a₁ • b₂) 0) =
      ite (a₁ * x = z) (b₁ * a₁ • r) 0 :=
    fun a₁ b₁ ↦ sum_single_index <| by simp
  calc
    (f * (single x r)).coeff z =
        sum f fun a b ↦ if a = y then b * y • r else 0 := by simp [coeff_mul, A, H, sum_ite_eq']
    _ = if y ∈ f.support then f.coeff y * y • r else 0 := (f.support.sum_ite_eq' _ _)
    _ = f.coeff y * y • r := by
      split_ifs with h <;> simp [support] at h <;> simp [h]

theorem coeff_mul_single_one (f : SkewMonoidAlgebra k G) (r : k) (x : G) :
    (f * single 1 r).coeff x = f.coeff x * x • r :=
  f.coeff_mul_single_aux fun a ↦ by rw [mul_one]

theorem coeff_mul_single_of_not_exists_mul (r : k) {g g' : G} (x : SkewMonoidAlgebra k G)
    (h : ∀ x, ¬g' = x * g) : (x * single g r).coeff g' = 0 := by
  classical
  simp only [coeff_mul, smul_zero, mul_zero, ite_self, sum_single_index]
  apply Finset.sum_eq_zero
  simp_rw [ite_eq_right_iff]
  rintro _ _ rfl
  exact False.elim (h _ rfl)

theorem coeff_single_mul_aux (f : SkewMonoidAlgebra k G) {r : k} {x y z : G}
    (H : ∀ a, x * a = y ↔ a = z) : (single x r * f).coeff y = r * x • f.coeff z := by
  classical
  have : (f.sum fun a b ↦ ite (x * a = y) (0 * x • b) 0) = 0 := by simp
  calc
    ((single x r) *  f).coeff y =
        sum f fun a b ↦ ite (x * a = y) (r * x • b) 0 :=
      (coeff_mul _ _ _).trans <| sum_single_index this
    _ = f.sum fun a b ↦ ite (a = z) (r * x • b) 0 := by simp [H]
    _ = if z ∈ f.support then r * x • f.coeff z else 0 := (f.support.sum_ite_eq' _ _)
    _ = _ := by split_ifs with h <;> simp [support] at h <;> simp [h]

theorem coeff_single_one_mul (f : SkewMonoidAlgebra k G) (r : k) (x : G) :
    (single (1 : G) r * f).coeff x = r * f.coeff x := by
  simp [coeff_single_mul_aux, one_smul]

theorem coeff_single_mul_of_not_exists_mul (r : k) {g g' : G} (x : SkewMonoidAlgebra k G)
    (h : ¬∃ d, g' = g * d) : (single g r * x).coeff g' = 0 := by
  classical
  rw [coeff_mul, sum_single_index]
  · apply Finset.sum_eq_zero
    simp_rw [ite_eq_right_iff]
    rintro g'' _hg'' rfl
    exact absurd ⟨_, rfl⟩ h
  · simp

end Monoid

section Group

-- We now prove some additional statements that hold for group algebras.
variable [Group G] [MulSemiringAction G k]

@[simp]
theorem coeff_mul_single (f : SkewMonoidAlgebra k G) (r : k) (x y : G) :
    (f * single x r).coeff y = f.coeff (y * x⁻¹) * (y * x⁻¹) • r :=
  f.coeff_mul_single_aux fun _a ↦ eq_mul_inv_iff_mul_eq.symm

@[simp]
theorem coeff_single_mul (r : k) (x : G) (f : SkewMonoidAlgebra k G) (y : G) :
    (single x r * f).coeff y = r * x • f.coeff (x⁻¹ * y) :=
  f.coeff_single_mul_aux fun _z ↦ eq_inv_mul_iff_mul_eq.symm

theorem coeff_mul_left (f g : SkewMonoidAlgebra k G) (x : G) :
    (f * g).coeff x = f.sum fun a b ↦ b * a • g.coeff (a⁻¹ * x) :=
  calc
    (f * g).coeff x = sum f fun a b ↦ (single a b * g).coeff x := by
      rw [← coeff_sum, ← sum_mul g f, f.sum_single]
    _ = _ := by simp

theorem coeff_mul_right (f g : SkewMonoidAlgebra k G) (x : G) :
    (f * g).coeff x = g.sum fun a b ↦ f.coeff (x * a⁻¹) * (x * a⁻¹) • b :=
  calc
    (f * g).coeff x = sum g fun a b ↦ (f * single a b).coeff x := by
      rw [← coeff_sum, ← mul_sum f g, g.sum_single]
    _ = _ := by simp

end Group

end coeff_mul

section AddHom

variable [AddCommMonoid k]

/-- `single` as an `AddMonoidHom`.

See `lsingle` for the stronger version as a linear map. -/
@[simps]
def singleAddHom (a : G) : k →+ SkewMonoidAlgebra k G where
  toFun := single a
  map_zero' := single_zero a
  map_add' _ := single_add a _

@[ext high]
theorem addHom_ext' {N : Type*} [AddZeroClass N] ⦃f g : SkewMonoidAlgebra k G →+ N⦄
    (H : ∀ x, f.comp (singleAddHom x) = g.comp (singleAddHom x)) : f = g :=
  addHom_ext fun x => DFunLike.congr_fun (H x)

end AddHom

section Semiring

variable [Semiring k]

section singleOneRingHom

variable [Monoid G] [MulSemiringAction G k]

@[simp]
theorem single_mul_single {a₁ a₂ : G} {b₁ b₂ : k} :
    (single a₁ b₁) * (single a₂ b₂) = single (a₁ * a₂) (b₁ * a₁ • b₂) :=
  (sum_single_index (by simp [zero_mul, single_zero, sum_zero])).trans
    (sum_single_index (by simp [smul_zero, mul_zero, single_zero]))

/-- `single 1` as a `RingHom` -/
def singleOneRingHom : k →+* SkewMonoidAlgebra k G where
  __ := singleAddHom 1
  map_one' := rfl
  map_mul' x y := by simp [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, singleAddHom_apply,
    single_mul_single, mul_one, one_smul]

/-- If two ring homomorphisms from `SkewMonoidAlgebra k G` are equal on all `single a 1`
and `single 1 b`, then they are equal. -/
theorem ringHom_ext {f g : SkewMonoidAlgebra k G →+* k} (h₁ : ∀ b, f (single 1 b) = g (single 1 b))
    (h_of : ∀ a, f (single a 1) = g (single a 1)) : f = g :=
  have {a : G} {b₁ b₂ : k} : (single 1 b₁) * (single a b₂) = single a (b₁ * b₂) := by
    simp [single_mul_single, one_mul, one_smul]
  RingHom.coe_addMonoidHom_injective <|
    addHom_ext fun a b => by rw [← mul_one b, ← this, AddMonoidHom.coe_coe f,
      AddMonoidHom.coe_coe g, f.map_mul, g.map_mul, h₁, h_of]

end singleOneRingHom

section MapDomain

variable {α α₂ β F : Type*} [Semiring β] [Monoid α] [Monoid α₂] [FunLike F α α₂]

/-- Like `mapDomain_zero`, but for the `1` we define in this file -/
theorem mapDomain_one [MonoidHomClass F α α₂] (f : F) :
    (mapDomain f (1 : SkewMonoidAlgebra β α) : SkewMonoidAlgebra β α₂) =
      (1 : SkewMonoidAlgebra β α₂) := by
  simp_rw [one_def, mapDomain_single, map_one]

/- Like `mapDomain_add`, but for the skewed convolutive multiplication we define in this
  file. This theorem holds assuming that `(hf : ∀ (a : α) (x : β), a • x = (f a) • x)`. -/
theorem mapDomain_mul [MulSemiringAction α β] [MulSemiringAction α₂ β]
    [MulHomClass F α α₂] {f : F} (x y : SkewMonoidAlgebra β α)
    (hf : ∀ (a : α) (x : β), a • x = (f a) • x) :
    mapDomain f (x * y) = mapDomain f x * mapDomain f y := by
  rw [mul_def, map_sum]
  have : (sum x fun a b => sum y fun a₂ b₂ => mapDomain (↑f) (single (a * a₂) (b * a • b₂))) =
      sum (mapDomain (↑f) x) fun a₁ b₁ =>
        sum (mapDomain (↑f) y) fun a₂ b₂ => single (a₁ * a₂) (b₁ * a₁ • b₂) := by
    simp_rw [mapDomain_single, map_mul]
    rw [sum_mapDomain_index (by simp) (by simp [add_mul, single_add, sum_add])]
    congr
    ext a b c
    rw [sum_mapDomain_index (by simp) (by simp [smul_add, mul_add, single_add])]
    simp_rw [hf]
  convert this using 4
  rw [map_sum]

/-- If f : G → H is a multiplicative homomorphism between two monoids and
  `∀ (a : G) (x : k), a • x = (f a) • x`, then `mapDomain f` is a ring homomorphism
  between their skew monoid algebras. -/
def mapDomainRingHom [MulSemiringAction α β] [MulSemiringAction α₂ β]
    [MonoidHomClass F α α₂] {f : F} (hf : ∀ (a : α) (x : β), a • x = (f a) • x) :
    SkewMonoidAlgebra β α →+* SkewMonoidAlgebra β α₂ where
  __ := (mapDomain f : SkewMonoidAlgebra β α →+ SkewMonoidAlgebra β α₂)
  map_one' := mapDomain_one f
  map_mul' x y := mapDomain_mul x y hf

end MapDomain

section of

variable (k G)

variable [Monoid G] [MulSemiringAction G k]

/-- The embedding of a monoid into its skew monoid algebra. -/
def of : G →* SkewMonoidAlgebra k G where
  toFun a      := single a 1
  map_one'     := rfl
  map_mul' a b := by simp

@[simp]
lemma of_apply (a : G) : (of k G) a = single a 1 := by
  simp [of, MonoidHom.coe_mk, OneHom.coe_mk]

theorem smul_of (g : G) (r : k) : r • of k G g = single g r := by
  rw [of_apply, smul_single, smul_eq_mul, mul_one]

theorem of_injective [Nontrivial k] :
    Function.Injective (of k G) := fun a b h => by
  simp_rw [of_apply, ← toFinsupp_inj] at h
  simpa using (Finsupp.single_eq_single_iff _ _ _ _).mp h

/-- If two ring homomorphisms from `SkewMonoidAlgebra k G` are equal on all `single a 1`
and `single 1 b`, then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext high]
theorem ringHom_ext' {f g : SkewMonoidAlgebra k G →+* k}
    (h₁ : f.comp singleOneRingHom = g.comp singleOneRingHom)
    (h_of : (f : SkewMonoidAlgebra k G →* k).comp (of k G) =
      (g : SkewMonoidAlgebra k G →* k).comp (of k G)) : f = g :=
  ringHom_ext (RingHom.congr_fun h₁) (DFunLike.congr_fun h_of)

end of

/-! #### Non-unital, non-associative algebra structure -/

section NonUnitalNonAssocAlgebra

theorem liftNC_smul [MulOneClass G] {R : Type*} [Semiring R] (f : k →+* R) (g : G →* R) (c : k)
    (φ : SkewMonoidAlgebra k G) :
    liftNC (f : k →+ R) g (c • φ) = f c * liftNC (f : k →+ R) g φ := by
  suffices this :
    (liftNC ↑f g).comp (smulAddHom k (SkewMonoidAlgebra k G) c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC ↑f g) by exact DFunLike.congr_fun this φ
  refine addHom_ext' fun a => AddMonoidHom.ext fun b => ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, singleAddHom_apply, smulAddHom_apply,
    smul_single, smul_eq_mul, AddMonoidHom.coe_mulLeft]
  simp [liftNC_single, liftNC_single, AddMonoidHom.coe_coe, map_mul, mul_assoc]

variable (k G) [Monoid G] [MulSemiringAction G k]

instance isScalarTower_self [IsScalarTower k k k] :
    IsScalarTower k (SkewMonoidAlgebra k G) (SkewMonoidAlgebra k G) :=
  ⟨fun t a b => by
    classical
    simp only [smul_eq_mul]
    refine Eq.trans (sum_smul_index' (g := a) (b := t) ?_) ?_ <;>
      simp only [← smul_sum, smul_mul_assoc, ← smul_single,
        zero_mul, imp_true_iff, sum_zero, single_zero]; rfl⟩

end NonUnitalNonAssocAlgebra

end Semiring

section DistribMulActionHom

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]

/-- `single` as a `DistribMulActionSemiHom`.

See also `lsingle` for the version as a linear map. -/
@[simps]
def DistribMulActionHom.single [DistribMulAction R M] {α : Type*} (a : α) :
    M →+[R] SkewMonoidAlgebra M α where
  __ := singleAddHom a
  map_smul' k m := by simp [singleAddHom, smul_single, MonoidHom.id_apply]

theorem distribMulActionHom_ext [DistribMulAction R M] [DistribMulAction R N] {α : Type*}
    {f g : SkewMonoidAlgebra M α →+[R] N}
    (h : ∀ (a : α) (m : M), f (single a m) = g (single a m)) : f = g :=
  DistribMulActionHom.toAddMonoidHom_injective <| addHom_ext h

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem distribMulActionHom_ext' [DistribMulAction R M] [DistribMulAction R N] {α : Type*}
    {f g : SkewMonoidAlgebra M α →+[R] N}
    (h : ∀ a : α, f.comp (DistribMulActionHom.single a) = g.comp (DistribMulActionHom.single a)) :
    f = g :=
  distribMulActionHom_ext fun a => DistribMulActionHom.congr_fun (h a)

/-- Interpret `single a` as a linear map. -/
def lsingle {α : Type*} (a : α) [Module R M] : M →ₗ[R] (SkewMonoidAlgebra M α) where
  __ := singleAddHom a
  map_smul' _ _ := (smul_single _ _ _).symm

/-- Two `R`-linear maps from `SkewMonoidAlgebra M α` which agree on each `single x y`
  agree everywhere. -/
theorem lhom_ext {α : Type*} [Module R M] [Module R N] ⦃φ ψ : SkewMonoidAlgebra M α →ₗ[R] N⦄
    (h : ∀ a b, φ (single a b) = ψ (single a b)) : φ = ψ :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext h

@[ext high]
theorem lhom_ext' {α : Type*} [Module R M] [Module R N] ⦃φ ψ : SkewMonoidAlgebra M α →ₗ[R] N⦄
    (h : ∀ a, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ :=
  lhom_ext fun a => LinearMap.congr_fun (h a)

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Monoid G] [Semiring k] [MulSemiringAction G k]
open NonUnitalAlgHom

/-- A non_unital `k`-algebra homomorphism from `SkewMonoidAlgebra k G` is uniquely defined by its
values on the functions `single a 1`. -/
theorem nonUnitalAlgHom_ext [DistribMulAction k A] {φ₁ φ₂ : SkewMonoidAlgebra k G →ₙₐ[k] A}
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ := by
  apply NonUnitalAlgHom.to_distribMulActionHom_injective
  apply distribMulActionHom_ext'
  intro a
  ext
  simp [DistribMulActionHom.comp_apply, NonUnitalAlgHom.coe_to_distribMulActionHom,
    DistribMulActionHom.single_toFun, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
    singleAddHom_apply, h]

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem nonUnitalAlgHom_ext' [DistribMulAction k A] {φ₁ φ₂ : SkewMonoidAlgebra k G →ₙₐ[k] A}
    (h : φ₁.toMulHom.comp (of k G).toMulHom = φ₂.toMulHom.comp (of k G).toMulHom) : φ₁ = φ₂ :=
  nonUnitalAlgHom_ext <| DFunLike.congr_fun h

end DistribMulActionHom

end SkewMonoidAlgebra
