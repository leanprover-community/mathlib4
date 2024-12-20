/-
Copyright (c) 2024 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Algebra.Operad.Clone
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Tactic.Ring.RingNF
import Mathlib.LinearAlgebra.StdBasis

/-! This file provides several important examples of `Clone`s, enough to build all of Post's
  Lattice. Functions indexed by arity, i.e. `(Fin k → α) → α`, form the most basic example of
  a clone. This is given as `Func_Clone`.

  Then, there are certain predicates `P` so that the subtype of functions obeying this predicate,
  `{ f : (Fin k → α) → α // P f}`, form a clone. The definition `ClonalProperty` gives necessary
  conditions for such a predicate to form a clone, as proved in `clone_ClonalProperty`.

  There are several such properties given, and proved to be clonal:
  - `clonal_Monotone`, for `Monotone` functions on a `Preorder α`
  - `clonal_Conjunctive`, for `Function.Conjunctive` functions on `Min α`
  - `clonal_Disjunctive`, for `Function.Disjunctive` functions on `Max α`
  - `clonal_CommutesWithEndo`, for `Function.CommutesWithEndo`
  - `clonal_EssentiallyUnary`, for `Function.EssentiallyUnary`
  - `clonal_IsMultiargAffine`, for `Function.IsMultiargAffine` functions on a `Semiring α`
  -/

variable {α β γ : Type*}

open BigOperators

/-- A function is Conjunctive if `f (min a b) = min (f a) (f b)`. -/
def Function.Conjunctive [Min α] [Min β] (f : α → β) : Prop :=
  ∀ ⦃a b⦄, f (min a b) = min (f a) (f b)

@[simp]
theorem conjunctive_min [Min α] [Min β] {f : α → β} (a b : α) (h : f.Conjunctive) :
  min (f a) (f b) = f (min a b) :=
    Eq.symm (@h a b)

/-- A function is Disjunctive if `f (max a b) = max (f a) (f b)`. -/
def Function.Disjunctive [Max α] [Max β] (f : α → β) : Prop :=
  ∀ ⦃a b⦄, f (max a b) = max (f a) (f b)

@[simp]
theorem disjunctive_max [Max α] [Max β] {f : α → β} (a b : α) (h : f.Disjunctive) :
  max (f a) (f b) = f (max a b) :=
    Eq.symm (@h a b)

/-- States that the multiargument funtion `f`, whose arguments are indexed by the type `α`
  commutes with an endomorphism `φ : t → t` applied argumentwise. -/
def Function.CommutesWithEndo {α t : Type*} (φ : t → t) (f : (α → t) → t) : Prop :=
  ∀ ts, φ (f ts) = f (fun i ↦ φ (ts i))

/-- The standard notion of superposition in a clone, for functions. Usually stated for `Fin n`
 and `Fin m` indexed lists of arguments, here we generalize to arbitrary index types α and β.-/
@[reducible]
def function_superpose (a : (α → γ) → γ) (b : α → (β → γ) → γ) : (β → γ) → γ :=
  fun ts ↦ a (b · ts)

/-- The k-indexed family of "k-argument functions from T to T" forms a clone. -/
instance Func_Clone {t : Type*} : Clone (fun k ↦ (Fin k → t) → t) where
  superpose := function_superpose
  proj := fun _ k ts ↦ ts k
  one := fun ts ↦ ts 0

  one_proj := rfl
  superpose_assoc := fun _ _ _ ↦ rfl
  proj_left := fun _ _ ↦ rfl
  proj_right := fun _ ↦ by rfl

section property_clones

/-- A function property `p`, applicable to `k` argument functions `t^k → t`, is "superposable"
   iff it is closed under superposition -- `function_superpose`. -/
def SuperposableProperty (p : {k : ℕ} → ((Fin k → γ) → γ) → Prop) : Prop
  := ∀ {n m : ℕ} (a : Subtype (@p (k := n))) (b : Fin n → Subtype (@p (k := m))),
    p (function_superpose a.1 (Subtype.val ∘ b))

/-- A function property `p`, applicable to `k` argument functions `t^k → t`, is "projectable"
   if it holds for all projector functions π_k^i. -/
def ProjectableProperty (p : {k : ℕ} → ((Fin k → γ) → γ) → Prop) : Prop
  := ∀ (n : ℕ) (k : Fin n), p (fun ts ↦ ts k)

/-- A function property is a `ClonalProperty` iff it is both superposable and projectable. -/
def ClonalProperty (t : Type*) (p : {k : ℕ} → ((Fin k → t) → t) → Prop) : Prop :=
  (SuperposableProperty p) ∧ (ProjectableProperty p)

/-- The intersection of two clonal properties is again a clonal property. -/
theorem and_ClonalProperty {p1 p2} (h₁ : ClonalProperty γ p1)
    (h₂ : ClonalProperty γ p2) : ClonalProperty γ (fun ts ↦ p1 ts ∧ p2 ts) :=
  ⟨fun a b ↦ ⟨
    h₁.1 ⟨_, a.2.1⟩ fun i ↦ ⟨_, (b i).2.1⟩,
    h₂.1 ⟨_, a.2.2⟩ fun i ↦ ⟨_, (b i).2.2⟩⟩,
  fun _ _ ↦ ⟨h₁.2 _ _, h₂.2 _ _⟩⟩

/-- The subtype of functions `t^k ↦ t` that obey a `ClonalProperty`, form a clone. -/
instance clone_ClonalProperty {p} (h : ClonalProperty γ p) :
    Clone (fun k ↦ Subtype (p (k := k))) where
  superpose := fun a b ↦ ⟨function_superpose a.1 (Subtype.val ∘ b), h.1 a b⟩
  proj := fun _ _ ↦ ⟨fun ts ↦ ts _, h.2 _ _⟩
  one := ⟨fun ts ↦ ts 0, h.2 1 0⟩
  one_proj := rfl
  superpose_assoc := fun _ _ _ ↦ rfl
  proj_left := fun _ _ ↦ rfl
  proj_right := fun _ ↦ rfl

/-- Monotonicity is a `clonal_function_property`; monotone functions from a clone. -/
theorem clonal_Monotone [Preorder γ] : ClonalProperty γ (fun {_} ↦ Monotone) :=
  ⟨fun a b _ _ h ↦ a.2 fun _ ↦ (b _).2 h, fun _ _ _ _ h ↦ h _⟩

/-- Functions that are `Function.Conjunctive` over a preorder form a clone. -/
theorem clonal_Conjunctive [Min γ] : ClonalProperty γ (fun {_} ↦ Function.Conjunctive) :=
  ⟨fun a b _ _ ↦ by
    rw [← a.property, function_superpose]
    congr! with z
    apply (b z).property,
  fun _ _ _ _ ↦ rfl⟩

/-- Functions that are `Function.Disjunctive` over a preorder form a clone. -/
theorem clonal_Disjunctive [Max γ] : ClonalProperty γ (fun {_} ↦ Function.Disjunctive) :=
  ⟨fun a b _ _ ↦ by
    rw [← a.property, function_superpose]
    congr! with z
    apply (b z).property,
  fun _ _ _ _ ↦ rfl⟩

/-- For an endomorphism `φ : t → t`, the multiargument functions that commute with `φ` form
  a clone (the `Function.CommutesWithEndo`) -/
theorem clonal_CommutesWithEndo (φ : γ → γ) :
  ClonalProperty γ (fun {_} ↦ Function.CommutesWithEndo φ) :=
  ⟨fun a b _ ↦ by
    dsimp [function_superpose]
    rw [a.property]
    congr!
    exact (b _).property _, fun _ _ _ ↦ rfl⟩

/-- A multiargument function is _essentially unary_ if there is one argument that entirely
  determines the value of the function. -/
def Function.EssentiallyUnary {α t : Type*} (f : (α → t) → t) : Prop :=
  ∃(i : α) (fi : t → t), ∀ts, f ts = fi (ts i)

theorem clonal_EssentiallyUnary : ClonalProperty γ (fun {_} ↦ Function.EssentiallyUnary) :=
  ⟨fun a b ↦ by
    rcases a with ⟨_, ⟨ai, fa, ha⟩⟩
    set! bai := b ai with hbai
    rcases bai.2 with ⟨bi, fb, hb⟩
    refine ⟨bi, fa ∘ fb, fun _ ↦ ?_⟩
    dsimp [function_superpose]
    rw [← hb, hbai, ha],
  fun _ _ ↦ ⟨_, id, fun _ ↦ rfl⟩⟩

/-- Whether a multiargument function `f : t^α → t` is `k`-wise P-preserving, for an integer
  k and a `P : t → Prop` is defined as follows. Given `k`-tuple `kts` of arguments (each argument
  `ts` of type `t^α`), call it "elementwise in P" if each index `i : Fin m` has at least one
  `(kts j) i ∈ P` for some `j : Fin k`. Then `f` maps tuples that are elementwise in P to a
  1-tuple that is elementwise in P. That is, `∃ j : Fin k` such that `f (kts j) ∈ P`.

  Being `k`-wise P-preserving implies also being `k₂`-wise P-preserving for any `k₂ ≤ k`. There
  is also the extension to `k = ∞`, which says the property holds for all `k`. For this reason,
  we take `k` to be a `WithTop ℕ`, and allow any m ≤ k as the size of the tuple. An important
  case is `k=1`, which simply states that `f` applied to a vector of `P` values is also in `P`.

  Although the property is normally discussed on functions whose arguments are indexed by
  `Fin m`, we can allow the index to be an arbitrary `α`. -/
def kWisePropPreserving {t : Type*} (k : WithTop ℕ) (P : t → Prop) (f : (α → t) → t) : Prop :=
  ∀ {m : ℕ} (_ : m ≤ k) (kts : Fin m → (α → t)),
    (∀ i, ∃ j, P ((kts j) i)) → ∃ j, P (f (kts j))

theorem clonal_kWisePropPreserving (k : WithTop ℕ) (P : γ → Prop) :
    ClonalProperty γ (fun {_} ↦ kWisePropPreserving k P) :=
  ⟨fun a b _ hm kts h ↦ a.2 hm
    (fun _ _ ↦ (b _).1 (kts _))
    (fun _ ↦ (((b _).2 hm) _) (fun _ ↦ h _)),
  fun _ _ _ _ _ h ↦ h _⟩

section affine

variable [Fintype α] [DecidableEq α]

/-- The Prop that a function from `t^α → t`, written as `(α → t) → t`, is affine: there is a list
  of coefficients `c : t` at each index `i : α`, and a constant, that determine the full map.
  `multiargAffine_iff_AffineMap`. -/
def Function.IsMultiargAffine [NonUnitalNonAssocSemiring γ] (f : (α → γ) → γ) : Prop :=
  ∃ c, ∃ (cs : α → γ), ∀ x, f x = c + ∑ i, (cs i) * (x i)

section semiring
variable [Semiring γ]

/-- `Function.IsMultiargAffine` maps over a `Semiring` form a clone. -/
theorem clonal_IsMultiargAffine : ClonalProperty γ Function.IsMultiargAffine :=
  ⟨fun ⟨av, ⟨ca, csa, hca⟩⟩ b ↦ by
    unfold Function.IsMultiargAffine at b
    replace b := fun i ↦ (b i).2
    simp_rw [Classical.skolem] at b
    rcases b with ⟨cbi, csbi, hcsbi⟩
    use ca + ∑ j, csa j * cbi j
    use fun i ↦ ∑ j, csa j * csbi j i
    intro xs
    dsimp [function_superpose]
    simp_rw [hca, hcsbi, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm, add_assoc],
    fun n k ↦ by
      use 0, fun i ↦ if k = i then (1:γ) else 0
      simp
  ⟩

end semiring
section ring

/-- A function `IsAffineMap` if it is equal to some `AffineMap`. -/
def Function.IsAffineMap [Ring γ] (f : (α → γ) → γ) : Prop :=
  ∃ a : AffineMap γ (α → γ) γ, a = f

/-- `AffineMap`s form a clone. -/
instance clone_AffineMap [Ring γ] : Clone (fun {k} ↦ AffineMap γ (Fin k → γ) γ) where
  superpose := (AffineMap.comp · <| AffineMap.pi ·)
  proj _ k := AffineMap.mk' (· k) ⟨⟨(· k), fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩
    0 (fun _ ↦ eq_add_of_sub_eq rfl)
  one := AffineMap.mk' (· 0) ⟨⟨(· 0), fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩
    0 (fun _ ↦ eq_add_of_sub_eq rfl)

  one_proj := rfl
  superpose_assoc _ _ _ := rfl
  proj_left _ _ := rfl
  proj_right _ := rfl

end ring
section commring

/-- A function is `Function.IsMultiargAffine` iff there is an equivalent AffineMap. -/
theorem IsMultiargAffine_iff_IsAffineMap [CommRing γ] (f : (α → γ) → γ) :
  f.IsMultiargAffine ↔ f.IsAffineMap := by
    constructor
    · rintro ⟨c, cs, hc⟩
      use AffineMap.mk' f ⟨⟨(f · - f 0), by
        intros
        simp_rw [hc, Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.zero_apply,
          mul_zero, Finset.sum_const_zero]
        abel
      ⟩, by
        intros
        simp_rw [RingHom.id_apply, smul_eq_mul, hc, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
          Pi.smul_apply, smul_eq_mul, mul_sub, add_zero, mul_add, Finset.mul_sum, ← mul_assoc,
          mul_comm _ (cs _)]
        abel
      ⟩ 0 (by simp)
      apply AffineMap.coe_mk'
    · rintro ⟨f, rfl⟩
      use f 0, fun i ↦ f (Pi.single i 1) - f 0
      intro x
      rw [add_comm]
      convert f.map_vadd 0 x using 2
      · simp only [vadd_eq_add, add_zero]
      have h := fun i ↦ f.map_vadd 0 (Pi.single i 1)
      simp_rw [vadd_eq_add, add_zero] at h
      simp_rw [h, add_sub_cancel_right, mul_comm]
      symm
      convert LinearMap.pi_apply_eq_sum_univ f.linear x
      convert Pi.single_apply _ _ _ using 2
      exact eq_comm

/-- Functions that `IsAffineMap` form a clone-/
theorem clonal_IsAffineMap [CommRing γ] : ClonalProperty γ Function.IsAffineMap := by
  convert clonal_IsMultiargAffine
  · ext
    symm
    apply IsMultiargAffine_iff_IsAffineMap

end commring
end affine

local notation "FuncWithProperty[ " t "," p "]" => (fun k ↦ @Subtype ((Fin k → t) → t) p)

instance Monotone_Clone [Preorder γ] : Clone FuncWithProperty[γ, Monotone] :=
  clone_ClonalProperty clonal_Monotone

instance Conjunctive_Clone [Min γ] : Clone FuncWithProperty[γ, Function.Conjunctive] :=
  clone_ClonalProperty clonal_Conjunctive

instance Disjunctive_Clone [Max γ] : Clone FuncWithProperty[γ, Function.Disjunctive] :=
  clone_ClonalProperty clonal_Disjunctive

instance Commute_with_φ_Clone (φ : γ → γ) :
    Clone FuncWithProperty[γ, Function.CommutesWithEndo φ] :=
  clone_ClonalProperty (clonal_CommutesWithEndo φ)

instance EssentiallyUnary_Clone : Clone FuncWithProperty[γ, Function.EssentiallyUnary] :=
  clone_ClonalProperty clonal_EssentiallyUnary

instance kWisePropPreserving_Clone (k : WithTop ℕ) (P : γ → Prop) :
    Clone FuncWithProperty[γ, kWisePropPreserving k P] :=
  clone_ClonalProperty (clonal_kWisePropPreserving k P)

instance IsMultiargAffine_Clone [Semiring γ] :
    Clone FuncWithProperty[γ, Function.IsMultiargAffine] :=
  clone_ClonalProperty clonal_IsMultiargAffine

end property_clones
