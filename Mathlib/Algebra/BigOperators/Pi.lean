/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Algebra.Ring.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Big operators for Pi Types

This file contains theorems relevant to big operators in binary and arbitrary product
of monoids and groups
-/

open scoped Finset

variable {ι κ M N R α : Type*}

namespace Pi

@[to_additive]
theorem list_prod_apply {α : Type*} {M : α → Type*} [∀ a, Monoid (M a)] (a : α)
    (l : List (∀ a, M a)) : l.prod a = (l.map fun f : ∀ a, M a ↦ f a).prod :=
  map_list_prod (evalMonoidHom M a) _

@[to_additive]
theorem multiset_prod_apply {α : Type*} {M : α → Type*} [∀ a, CommMonoid (M a)] (a : α)
    (s : Multiset (∀ a, M a)) : s.prod a = (s.map fun f : ∀ a, M a ↦ f a).prod :=
  (evalMonoidHom M a).map_multiset_prod _

end Pi

@[to_additive (attr := simp)]
theorem Finset.prod_apply {α : Type*} {M : α → Type*} [∀ a, CommMonoid (M a)] (a : α)
    (s : Finset ι) (g : ι → ∀ a, M a) : (∏ c ∈ s, g c) a = ∏ c ∈ s, g c a :=
  map_prod (Pi.evalMonoidHom M a) _ _

/-- An 'unapplied' analogue of `Finset.prod_apply`. -/
@[to_additive /-- An 'unapplied' analogue of `Finset.sum_apply`. -/]
theorem Finset.prod_fn {α : Type*} {M : α → Type*} {ι} [∀ a, CommMonoid (M a)] (s : Finset ι)
    (g : ι → ∀ a, M a) : ∏ c ∈ s, g c = fun a ↦ ∏ c ∈ s, g c a :=
  funext fun _ ↦ Finset.prod_apply _ _ _

@[to_additive]
theorem Fintype.prod_apply {α : Type*} {M : α → Type*} [Fintype ι] [∀ a, CommMonoid (M a)] (a : α)
    (g : ι → ∀ a, M a) : (∏ c, g c) a = ∏ c, g c a :=
  Finset.prod_apply a Finset.univ g

@[to_additive prod_mk_sum]
theorem prod_mk_prod [CommMonoid M] [CommMonoid N] (s : Finset ι) (f : ι → M) (g : ι → N) :
    (∏ x ∈ s, f x, ∏ x ∈ s, g x) = ∏ x ∈ s, (f x, g x) :=
  haveI := Classical.decEq ι
  Finset.induction_on s rfl (by simp +contextual [Prod.ext_iff])

/-- decomposing `x : ι → R` as a sum along the canonical basis -/
theorem pi_eq_sum_univ {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [NonAssocSemiring R]
    (x : ι → R) : x = ∑ i, (x i) • fun j => if i = j then (1 : R) else 0 := by
  ext
  simp

/-- Decomposing `x : ι → R` as a sum along the canonical basis `Pi.single i 1` for `i : ι`. -/
theorem pi_eq_sum_univ' {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [NonAssocSemiring R]
    (x : ι → R) : x = ∑ i, (x i) • Pi.single (M := fun _ ↦ R) i 1 := by
  convert pi_eq_sum_univ x
  aesop

section CommSemiring
variable [CommSemiring R]

lemma prod_indicator_apply (s : Finset ι) (f : ι → Set κ) (g : ι → κ → R) (j : κ) :
    ∏ i ∈ s, (f i).indicator (g i) j = (⋂ x ∈ s, f x).indicator (∏ i ∈ s, g i) j := by
  rw [Set.indicator]
  split_ifs with hj
  · rw [Finset.prod_apply]
    congr! 1 with i hi
    simp only [Set.mem_iInter] at hj
    exact Set.indicator_of_mem (hj _ hi) _
  · obtain ⟨i, hi, hj⟩ := by simpa using hj
    exact Finset.prod_eq_zero hi <| Set.indicator_of_notMem hj _

lemma prod_indicator (s : Finset ι) (f : ι → Set κ) (g : ι → κ → R) :
    ∏ i ∈ s, (f i).indicator (g i) = (⋂ x ∈ s, f x).indicator (∏ i ∈ s, g i) := by
  ext a; simpa using prod_indicator_apply ..

lemma prod_indicator_const_apply (s : Finset ι) (f : ι → Set κ) (g : κ → R) (j : κ) :
    ∏ i ∈ s, (f i).indicator g j = (⋂ x ∈ s, f x).indicator (g ^ #s) j := by
  simp [prod_indicator_apply]

lemma prod_indicator_const (s : Finset ι) (f : ι → Set κ) (g : κ → R) :
    ∏ i ∈ s, (f i).indicator g = (⋂ x ∈ s, f x).indicator (g ^ #s) := by simp [prod_indicator]

end CommSemiring

section MulSingle

variable {I : Type*} [DecidableEq I] {M : I → Type*}
variable [∀ i, CommMonoid (M i)]

@[to_additive]
theorem Finset.univ_prod_mulSingle [Fintype I] (f : ∀ i, M i) :
    (∏ i, Pi.mulSingle i (f i)) = f := by
  ext a
  simp

@[to_additive]
theorem MonoidHom.functions_ext [Finite I] (N : Type*) [CommMonoid N] (g h : (∀ i, M i) →* N)
    (H : ∀ i x, g (Pi.mulSingle i x) = h (Pi.mulSingle i x)) : g = h := by
  cases nonempty_fintype I
  ext k
  rw [← Finset.univ_prod_mulSingle k, map_prod, map_prod]
  simp only [H]

/-- This is used as the ext lemma instead of `MonoidHom.functions_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[to_additive (attr := ext)
      /-- This is used as the ext lemma instead of `AddMonoidHom.functions_ext` for reasons
      explained in note [partially-applied ext lemmas]. -/]
theorem MonoidHom.functions_ext' [Finite I] (N : Type*) [CommMonoid N] (g h : (∀ i, M i) →* N)
    (H : ∀ i, g.comp (MonoidHom.mulSingle M i) = h.comp (MonoidHom.mulSingle M i)) : g = h :=
  g.functions_ext N h fun i => DFunLike.congr_fun (H i)

end MulSingle

section RingHom

open Pi

variable {I : Type*} [DecidableEq I] {R : I → Type*}
variable [∀ i, NonAssocSemiring (R i)]

@[ext]
theorem RingHom.functions_ext [Finite I] (S : Type*) [NonAssocSemiring S] (g h : (∀ i, R i) →+* S)
    (H : ∀ (i : I) (x : R i), g (single i x) = h (single i x)) : g = h :=
  RingHom.coe_addMonoidHom_injective <|
    @AddMonoidHom.functions_ext I _ R _ _ S _ (g : (∀ i, R i) →+ S) h H

end RingHom

namespace Prod

variable [CommMonoid M] [CommMonoid N] {s : Finset ι} {f : ι → M × N}

@[to_additive]
theorem fst_prod : (∏ c ∈ s, f c).1 = ∏ c ∈ s, (f c).1 :=
  map_prod (MonoidHom.fst ..) f s

@[to_additive]
theorem snd_prod : (∏ c ∈ s, f c).2 = ∏ c ∈ s, (f c).2 :=
  map_prod (MonoidHom.snd ..) f s

end Prod

section MulEquiv

/-- The canonical isomorphism between the monoid of homomorphisms from a finite product of
commutative monoids to another commutative monoid and the product of the homomorphism monoids. -/
@[to_additive /-- The canonical isomorphism between the additive monoid of homomorphisms from
a finite product of additive commutative monoids to another additive commutative monoid and
the product of the homomorphism monoids. -/]
def Pi.monoidHomMulEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι → Type*)
    [(i : ι) → CommMonoid (M i)] (M' : Type*) [CommMonoid M'] :
    (((i : ι) → M i) →* M') ≃* ((i : ι) → (M i →* M')) where
  toFun φ i := φ.comp <| MonoidHom.mulSingle M i
  invFun φ := ∏ (i : ι), (φ i).comp (Pi.evalMonoidHom M i)
  left_inv φ := by
    ext
    simp only [MonoidHom.finset_prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      evalMonoidHom_apply, MonoidHom.mulSingle_apply, ← map_prod]
    refine congrArg _ <| funext fun _ ↦ ?_
    rw [Fintype.prod_apply]
    exact Fintype.prod_pi_mulSingle ..
  right_inv φ := by
    ext i m
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply,
      MonoidHom.finset_prod_apply, evalMonoidHom_apply, ]
    let φ' i : M i → M' := ⇑(φ i)
    conv =>
      enter [1, 2, j]
      rw [show φ j = φ' j from rfl, Pi.apply_mulSingle φ' (fun i ↦ map_one (φ i))]
    rw [show φ' i = φ i from rfl]
    exact Fintype.prod_pi_mulSingle' ..
  map_mul' φ ψ := by
    ext
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply,
      MonoidHom.mul_apply, mul_apply]

end MulEquiv

variable [Finite ι] [DecidableEq ι] {M : Type*}

-- manually additivized to fix variable names
-- See https://github.com/leanprover-community/mathlib4/issues/11462
lemma Pi.single_induction [AddCommMonoid M] (p : (ι → M) → Prop) (f : ι → M)
    (zero : p 0) (add : ∀ f g, p f → p g → p (f + g))
    (single : ∀ i m, p (Pi.single i m)) : p f := by
  cases nonempty_fintype ι
  rw [← Finset.univ_sum_single f]
  exact Finset.sum_induction _ _ add zero (by simp [single])

@[to_additive existing (attr := elab_as_elim)]
lemma Pi.mulSingle_induction [CommMonoid M] (p : (ι → M) → Prop) (f : ι → M)
    (one : p 1) (mul : ∀ f g, p f → p g → p (f * g))
    (mulSingle : ∀ i m, p (Pi.mulSingle i m)) : p f := by
  cases nonempty_fintype ι
  rw [← Finset.univ_prod_mulSingle f]
  exact Finset.prod_induction _ _ mul one (by simp [mulSingle])

section EqOn

@[to_additive]
theorem eqOn_finsetProd {ι α β : Type*} [CommMonoid α]
    {s : Set β} {f f' : ι → β → α} (h : ∀ (i : ι), Set.EqOn (f i) (f' i) s) (v : Finset ι) :
    Set.EqOn (∏ i ∈ v, f i) (∏ i ∈ v, f' i) s :=
  fun t ht => by simp [funext fun i ↦ h i ht]

@[to_additive]
theorem eqOn_fun_finsetProd {ι α β : Type*} [CommMonoid α]
    {s : Set β} {f f' : ι → β → α} (h : ∀ (i : ι), Set.EqOn (f i) (f' i) s) (v : Finset ι) :
    Set.EqOn (fun b ↦ ∏ i ∈ v, f i b) (fun b ↦ ∏ i ∈ v, f' i b) s := by
  convert eqOn_finsetProd h v <;> simp

end EqOn
