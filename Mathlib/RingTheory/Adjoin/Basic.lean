/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Algebra.Subalgebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.Algebra.Module.Submodule.EqLocus
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.LinearAlgebra.Prod
/-!
# Adjoining elements to form subalgebras

This file develops the basic theory of subalgebras of an R-algebra generated
by a set of elements. A basic interface for `adjoin` is set up.

## Tags

adjoin, algebra

-/

assert_not_exists Polynomial

universe uR uS uA uB

open Pointwise

open Submodule Subsemiring

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

namespace Algebra

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]
variable {s t : Set A}

@[aesop safe 20 apply (rule_sets := [SetLike])]
theorem subset_adjoin : s ⊆ adjoin R s :=
  Algebra.gc.le_u_l s

theorem adjoin_le {S : Subalgebra R A} (H : s ⊆ S) : adjoin R s ≤ S :=
  Algebra.gc.l_le H

theorem adjoin_eq_sInf : adjoin R s = sInf { p : Subalgebra R A | s ⊆ p } :=
  le_antisymm (le_sInf fun _ h => adjoin_le h) (sInf_le subset_adjoin)

theorem adjoin_le_iff {S : Subalgebra R A} : adjoin R s ≤ S ↔ s ⊆ S :=
  Algebra.gc _ _

theorem adjoin_mono (H : s ⊆ t) : adjoin R s ≤ adjoin R t :=
  Algebra.gc.monotone_l H

theorem adjoin_eq_of_le (S : Subalgebra R A) (h₁ : s ⊆ S) (h₂ : S ≤ adjoin R s) : adjoin R s = S :=
  le_antisymm (adjoin_le h₁) h₂

theorem adjoin_eq (S : Subalgebra R A) : adjoin R ↑S = S :=
  adjoin_eq_of_le _ (Set.Subset.refl _) subset_adjoin

theorem adjoin_iUnion {α : Type*} (s : α → Set A) :
    adjoin R (Set.iUnion s) = ⨆ i : α, adjoin R (s i) :=
  (@Algebra.gc R A _ _ _).l_iSup

theorem adjoin_attach_biUnion [DecidableEq A] {α : Type*} {s : Finset α} (f : s → Finset A) :
    adjoin R (s.attach.biUnion f : Set A) = ⨆ x, adjoin R (f x) := by simp [adjoin_iUnion]

@[elab_as_elim]
theorem adjoin_induction {p : (x : A) → x ∈ adjoin R s → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (subset_adjoin hx))
    (algebraMap : ∀ r, p (algebraMap R A r) (algebraMap_mem _ r))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x : A} (hx : x ∈ adjoin R s) : p x hx :=
  let S : Subalgebra R A :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := by rintro _ _ ⟨_, hpx⟩ ⟨_, hpy⟩; exact ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := by rintro _ _ ⟨_, hpx⟩ ⟨_, hpy⟩; exact ⟨_, add _ _ _ _ hpx hpy⟩
      algebraMap_mem' := fun r ↦ ⟨_, algebraMap r⟩ }
  adjoin_le (S := S) (fun y hy ↦ ⟨subset_adjoin hy, mem y hy⟩) hx |>.elim fun _ ↦ _root_.id

@[deprecated adjoin_induction (since := "2024-10-10")]
alias adjoin_induction'' := adjoin_induction

/-- Induction principle for the algebra generated by a set `s`: show that `p x y` holds for any
`x y ∈ adjoin R s` given that it holds for `x y ∈ s` and that it satisfies a number of
natural properties. -/
@[elab_as_elim]
theorem adjoin_induction₂ {s : Set A} {p : (x y : A) → x ∈ adjoin R s → y ∈ adjoin R s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (subset_adjoin hx) (subset_adjoin hy))
    (algebraMap_both : ∀ r₁ r₂, p (algebraMap R A r₁) (algebraMap R A r₂) (algebraMap_mem _ r₁)
      (algebraMap_mem _ r₂))
    (algebraMap_left : ∀ (r) (x) (hx : x ∈ s), p (algebraMap R A r) x (algebraMap_mem _ r)
      (subset_adjoin hx))
    (algebraMap_right : ∀ (r) (x) (hx : x ∈ s), p x (algebraMap R A r) (subset_adjoin hx)
      (algebraMap_mem _ r))
    (add_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x + y) z (add_mem hx hy) hz)
    (add_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y + z) hx (add_mem hy hz))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    {x y : A} (hx : x ∈ adjoin R s) (hy : y ∈ adjoin R s) :
    p x y hx hy := by
  induction hy using adjoin_induction with
  | mem z hz => induction hx using adjoin_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | algebraMap _ => exact algebraMap_left _ _ hz
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
  | algebraMap r =>
    induction hx using adjoin_induction with
    | mem _ h => exact algebraMap_right _ _ h
    | algebraMap _ => exact algebraMap_both _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂

/-- The difference with `Algebra.adjoin_induction` is that this acts on the subtype. -/
@[elab_as_elim, deprecated adjoin_induction (since := "2024-10-11")]
theorem adjoin_induction' {p : adjoin R s → Prop} (mem : ∀ (x) (h : x ∈ s), p ⟨x, subset_adjoin h⟩)
    (algebraMap : ∀ r, p (algebraMap R _ r)) (add : ∀ x y, p x → p y → p (x + y))
    (mul : ∀ x y, p x → p y → p (x * y)) (x : adjoin R s) : p x :=
  Subtype.recOn x fun x hx => by
    induction hx using adjoin_induction with
    | mem _ h => exact mem _ h
    | algebraMap _ => exact algebraMap _
    | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add _ _ h₁ h₂

@[simp]
theorem adjoin_adjoin_coe_preimage {s : Set A} : adjoin R (((↑) : adjoin R s → A) ⁻¹' s) = ⊤ := by
  refine eq_top_iff.2 fun ⟨x, hx⟩ ↦
      adjoin_induction (fun a ha ↦ ?_) (fun r ↦ ?_) (fun _ _ _ _ ↦ ?_) (fun _ _ _ _ ↦ ?_) hx
  · exact subset_adjoin ha
  · exact Subalgebra.algebraMap_mem _ r
  · exact Subalgebra.add_mem _
  · exact Subalgebra.mul_mem _

theorem adjoin_union (s t : Set A) : adjoin R (s ∪ t) = adjoin R s ⊔ adjoin R t :=
  (Algebra.gc : GaloisConnection _ ((↑) : Subalgebra R A → Set A)).l_sup

variable (R A)

@[simp]
theorem adjoin_empty : adjoin R (∅ : Set A) = ⊥ :=
  show adjoin R ⊥ = ⊥ by
    apply GaloisConnection.l_bot
    exact Algebra.gc

@[simp]
theorem adjoin_univ : adjoin R (Set.univ : Set A) = ⊤ :=
  eq_top_iff.2 fun _x => subset_adjoin <| Set.mem_univ _

variable {A} (s)

theorem adjoin_eq_span : Subalgebra.toSubmodule (adjoin R s) = span R (Submonoid.closure s) := by
  apply le_antisymm
  · intro r hr
    rcases Subsemiring.mem_closure_iff_exists_list.1 hr with ⟨L, HL, rfl⟩
    clear hr
    induction' L with hd tl ih
    · exact zero_mem _
    rw [List.forall_mem_cons] at HL
    rw [List.map_cons, List.sum_cons]
    refine Submodule.add_mem _ ?_ (ih HL.2)
    replace HL := HL.1
    clear ih tl
    suffices ∃ (z r : _) (_hr : r ∈ Submonoid.closure s), z • r = List.prod hd by
      rcases this with ⟨z, r, hr, hzr⟩
      rw [← hzr]
      exact smul_mem _ _ (subset_span hr)
    induction' hd with hd tl ih
    · exact ⟨1, 1, (Submonoid.closure s).one_mem', one_smul _ _⟩
    rw [List.forall_mem_cons] at HL
    rcases ih HL.2 with ⟨z, r, hr, hzr⟩
    rw [List.prod_cons, ← hzr]
    rcases HL.1 with (⟨hd, rfl⟩ | hs)
    · refine ⟨hd * z, r, hr, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, (algebraMap _ _).map_mul, _root_.mul_assoc]
    · exact
        ⟨z, hd * r, Submonoid.mul_mem _ (Submonoid.subset_closure hs) hr,
          (mul_smul_comm _ _ _).symm⟩
  refine span_le.2 ?_
  change Submonoid.closure s ≤ (adjoin R s).toSubsemiring.toSubmonoid
  exact Submonoid.closure_le.2 subset_adjoin

theorem span_le_adjoin (s : Set A) : span R s ≤ Subalgebra.toSubmodule (adjoin R s) :=
  span_le.mpr subset_adjoin

theorem adjoin_toSubmodule_le {s : Set A} {t : Submodule R A} :
    Subalgebra.toSubmodule (adjoin R s) ≤ t ↔ ↑(Submonoid.closure s) ⊆ (t : Set A) := by
  rw [adjoin_eq_span, span_le]

theorem adjoin_eq_span_of_subset {s : Set A} (hs : ↑(Submonoid.closure s) ⊆ (span R s : Set A)) :
    Subalgebra.toSubmodule (adjoin R s) = span R s :=
  le_antisymm ((adjoin_toSubmodule_le R).mpr hs) (span_le_adjoin R s)

@[simp]
theorem adjoin_span {s : Set A} : adjoin R (Submodule.span R s : Set A) = adjoin R s :=
  le_antisymm (adjoin_le (span_le_adjoin _ _)) (adjoin_mono Submodule.subset_span)

theorem adjoin_image (f : A →ₐ[R] B) (s : Set A) : adjoin R (f '' s) = (adjoin R s).map f :=
  le_antisymm (adjoin_le <| Set.image_subset _ subset_adjoin) <|
    Subalgebra.map_le.2 <| adjoin_le <| Set.image_subset_iff.1 <| by
      -- Porting note: I don't understand how this worked in Lean 3 with just `subset_adjoin`
      simp only [Set.image_id', coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
        Subalgebra.coe_comap]
      exact fun x hx => subset_adjoin ⟨x, hx, rfl⟩

@[simp]
theorem adjoin_insert_adjoin (x : A) : adjoin R (insert x ↑(adjoin R s)) = adjoin R (insert x s) :=
  le_antisymm
    (adjoin_le
      (Set.insert_subset_iff.mpr
        ⟨subset_adjoin (Set.mem_insert _ _), adjoin_mono (Set.subset_insert _ _)⟩))
    (Algebra.adjoin_mono (Set.insert_subset_insert Algebra.subset_adjoin))

theorem adjoin_prod_le (s : Set A) (t : Set B) :
    adjoin R (s ×ˢ t) ≤ (adjoin R s).prod (adjoin R t) :=
  adjoin_le <| Set.prod_mono subset_adjoin subset_adjoin

theorem mem_adjoin_of_map_mul {s} {x : A} {f : A →ₗ[R] B} (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂)
    (h : x ∈ adjoin R s) : f x ∈ adjoin R (f '' (s ∪ {1})) := by
  induction h using adjoin_induction with
  | mem a ha => exact subset_adjoin ⟨a, ⟨Set.subset_union_left ha, rfl⟩⟩
  | algebraMap r =>
    have : f 1 ∈ adjoin R (f '' (s ∪ {1})) :=
      subset_adjoin ⟨1, ⟨Set.subset_union_right <| Set.mem_singleton 1, rfl⟩⟩
    convert Subalgebra.smul_mem (adjoin R (f '' (s ∪ {1}))) this r
    rw [algebraMap_eq_smul_one]
    exact f.map_smul _ _
  | add y z _ _ hy hz => simpa [hy, hz] using Subalgebra.add_mem _ hy hz
  | mul y z _ _ hy hz => simpa [hf, hy, hz] using Subalgebra.mul_mem _ hy hz

theorem adjoin_inl_union_inr_eq_prod (s) (t) :
    adjoin R (LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1})) =
      (adjoin R s).prod (adjoin R t) := by
  apply le_antisymm
  · simp only [adjoin_le_iff, Set.insert_subset_iff, Subalgebra.zero_mem, Subalgebra.one_mem,
      subset_adjoin,-- the rest comes from `squeeze_simp`
      Set.union_subset_iff,
      LinearMap.coe_inl, Set.mk_preimage_prod_right, Set.image_subset_iff, SetLike.mem_coe,
      Set.mk_preimage_prod_left, LinearMap.coe_inr, and_self_iff, Set.union_singleton,
      Subalgebra.coe_prod]
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    let P := adjoin R (LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1}))
    have Ha : (a, (0 : B)) ∈ adjoin R (LinearMap.inl R A B '' (s ∪ {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inl_map_mul ha
    have Hb : ((0 : A), b) ∈ adjoin R (LinearMap.inr R A B '' (t ∪ {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inr_map_mul hb
    replace Ha : (a, (0 : B)) ∈ P := adjoin_mono Set.subset_union_left Ha
    replace Hb : ((0 : A), b) ∈ P := adjoin_mono Set.subset_union_right Hb
    simpa [P] using Subalgebra.add_mem _ Ha Hb

lemma adjoin_le_centralizer_centralizer (s : Set A) :
    adjoin R s ≤ Subalgebra.centralizer R (Subalgebra.centralizer R s) :=
  adjoin_le Set.subset_centralizer_centralizer

/-- If all elements of `s : Set A` commute pairwise, then `adjoin s` is a commutative semiring. -/
abbrev adjoinCommSemiringOfComm {s : Set A} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommSemiring (adjoin R s) :=
  { (adjoin R s).toSemiring with
    mul_comm := fun ⟨_, h₁⟩ ⟨_, h₂⟩ ↦
      have := adjoin_le_centralizer_centralizer R s
      Subtype.ext <| Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂) }

variable {R}

lemma commute_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A}
    (hb : b ∈ adjoin R s) (h : ∀ b ∈ s, Commute a b) :
    Commute a b := by
  induction hb using adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r => exact commutes r a |>.symm
  | add y z _ _ hy hz => exact hy.add_right hz
  | mul y z _ _ hy hz => exact hy.mul_right hz

lemma commute_of_mem_adjoin_singleton_of_commute {a b c : A}
    (hc : c ∈ adjoin R {b}) (h : Commute a b) :
    Commute a c :=
  commute_of_mem_adjoin_of_forall_mem_commute hc <| by simpa

lemma commute_of_mem_adjoin_self {a b : A} (hb : b ∈ adjoin R {a}) :
    Commute a b :=
  commute_of_mem_adjoin_singleton_of_commute hb rfl

variable (R)

theorem adjoin_singleton_one : adjoin R ({1} : Set A) = ⊥ :=
  eq_bot_iff.2 <| adjoin_le <| Set.singleton_subset_iff.2 <| SetLike.mem_coe.2 <| one_mem _

theorem self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : Set A) :=
  Algebra.subset_adjoin (Set.mem_singleton_iff.mpr rfl)

variable (A) in
theorem adjoin_algebraMap (s : Set S) :
    adjoin R (algebraMap S A '' s) = (adjoin R s).map (IsScalarTower.toAlgHom R S A) :=
  adjoin_image R (IsScalarTower.toAlgHom R S A) s

theorem adjoin_algebraMap_image_union_eq_adjoin_adjoin (s : Set S) (t : Set A) :
    adjoin R (algebraMap S A '' s ∪ t) = (adjoin (adjoin R s) t).restrictScalars R :=
  le_antisymm
    (closure_mono <|
      Set.union_subset (Set.range_subset_iff.2 fun r => Or.inl ⟨algebraMap R (adjoin R s) r,
        (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩)
        (Set.union_subset_union_left _ fun _ ⟨_x, hx, hxs⟩ => hxs ▸ ⟨⟨_, subset_adjoin hx⟩, rfl⟩))
    (closure_le.2 <|
      Set.union_subset (Set.range_subset_iff.2 fun x => adjoin_mono Set.subset_union_left <|
        Algebra.adjoin_algebraMap R A s ▸ ⟨x, x.prop, rfl⟩)
        (Set.Subset.trans Set.subset_union_right subset_adjoin))

theorem adjoin_adjoin_of_tower (s : Set A) : adjoin S (adjoin R s : Set A) = adjoin S s := by
  apply le_antisymm (adjoin_le _)
  · exact adjoin_mono subset_adjoin
  · change adjoin R s ≤ (adjoin S s).restrictScalars R
    refine adjoin_le ?_
    -- Porting note: unclear why this was broken
    have : (Subalgebra.restrictScalars R (adjoin S s) : Set A) = adjoin S s := rfl
    rw [this]
    exact subset_adjoin

theorem Subalgebra.restrictScalars_adjoin {s : Set A} :
    (adjoin S s).restrictScalars R = (IsScalarTower.toAlgHom R S A).range ⊔ adjoin R s := by
  refine le_antisymm (fun _ hx ↦ adjoin_induction
    (fun x hx ↦ le_sup_right (α := Subalgebra R A) (subset_adjoin hx))
    (fun x ↦ le_sup_left (α := Subalgebra R A) ⟨x, rfl⟩)
    (fun _ _ _ _ ↦ add_mem) (fun _ _ _ _ ↦ mul_mem) <|
    (Subalgebra.mem_restrictScalars _).mp hx) (sup_le ?_ <| adjoin_le subset_adjoin)
  rintro _ ⟨x, rfl⟩; exact algebraMap_mem (adjoin S s) x

@[simp]
theorem adjoin_top {A} [Semiring A] [Algebra S A] (t : Set A) :
    adjoin (⊤ : Subalgebra R S) t = (adjoin S t).restrictScalars (⊤ : Subalgebra R S) :=
  let equivTop : Subalgebra (⊤ : Subalgebra R S) A ≃o Subalgebra S A :=
    { toFun := fun s => { s with algebraMap_mem' := fun r => s.algebraMap_mem ⟨r, trivial⟩ }
      invFun := fun s => s.restrictScalars _
      left_inv := fun _ => SetLike.coe_injective rfl
      right_inv := fun _ => SetLike.coe_injective rfl
      map_rel_iff' := @fun _ _ => Iff.rfl }
  le_antisymm
    (adjoin_le <| show t ⊆ adjoin S t from subset_adjoin)
    (equivTop.symm_apply_le.mpr <|
      adjoin_le <| show t ⊆ adjoin (⊤ : Subalgebra R S) t from subset_adjoin)

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A]
variable [Algebra R A] {s t : Set A}
variable (R s t)

theorem adjoin_union_eq_adjoin_adjoin :
    adjoin R (s ∪ t) = (adjoin (adjoin R s) t).restrictScalars R := by
  simpa using adjoin_algebraMap_image_union_eq_adjoin_adjoin R s t

theorem adjoin_union_coe_submodule :
    Subalgebra.toSubmodule (adjoin R (s ∪ t)) =
      Subalgebra.toSubmodule (adjoin R s) * Subalgebra.toSubmodule (adjoin R t) := by
  rw [adjoin_eq_span, adjoin_eq_span, adjoin_eq_span, span_mul_span]
  congr 1 with z; simp [Submonoid.closure_union, Submonoid.mem_sup, Set.mem_mul]

variable {R}

theorem pow_smul_mem_of_smul_subset_of_mem_adjoin [CommSemiring B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (r : A) (s : Set B) (B' : Subalgebra R B) (hs : r • s ⊆ B') {x : B}
    (hx : x ∈ adjoin R s) (hr : algebraMap A B r ∈ B') : ∃ n₀ : ℕ, ∀ n ≥ n₀, r ^ n • x ∈ B' := by
  change x ∈ Subalgebra.toSubmodule (adjoin R s) at hx
  rw [adjoin_eq_span, Finsupp.mem_span_iff_linearCombination] at hx
  rcases hx with ⟨l, rfl : (l.sum fun (i : Submonoid.closure s) (c : R) => c • (i : B)) = x⟩
  choose n₁ n₂ using fun x : Submonoid.closure s => Submonoid.pow_smul_mem_closure_smul r s x.prop
  use l.support.sup n₁
  intro n hn
  rw [Finsupp.smul_sum]
  refine B'.toSubmodule.sum_mem ?_
  intro a ha
  have : n ≥ n₁ a := le_trans (Finset.le_sup ha) hn
  dsimp only
  rw [← tsub_add_cancel_of_le this, pow_add, ← smul_smul, ←
    IsScalarTower.algebraMap_smul A (l a) (a : B), smul_smul (r ^ n₁ a), mul_comm, ← smul_smul,
    smul_def, map_pow, IsScalarTower.algebraMap_smul]
  apply Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hr _) _
  refine Subalgebra.smul_mem _ ?_ _
  change _ ∈ B'.toSubmonoid
  rw [← Submonoid.closure_eq B'.toSubmonoid]
  apply Submonoid.closure_mono hs (n₂ a)

theorem pow_smul_mem_adjoin_smul (r : R) (s : Set A) {x : A} (hx : x ∈ adjoin R s) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, r ^ n • x ∈ adjoin R (r • s) :=
  pow_smul_mem_of_smul_subset_of_mem_adjoin r s _ subset_adjoin hx (Subalgebra.algebraMap_mem _ _)

end CommSemiring

section Ring

variable [CommRing R] [Ring A]
variable [Algebra R A] {s t : Set A}

theorem mem_adjoin_iff {s : Set A} {x : A} :
    x ∈ adjoin R s ↔ x ∈ Subring.closure (Set.range (algebraMap R A) ∪ s) :=
  ⟨fun hx =>
    Subsemiring.closure_induction Subring.subset_closure (Subring.zero_mem _) (Subring.one_mem _)
      (fun _ _ _ _ => Subring.add_mem _) (fun _ _ _ _ => Subring.mul_mem _) hx,
    suffices Subring.closure (Set.range (algebraMap R A) ∪ s) ≤ (adjoin R s).toSubring
      from (show (_ : Set A) ⊆ _ from this) (a := x)
    -- Porting note: Lean doesn't seem to recognize the defeq between the order on subobjects and
    -- subsets of their coercions to sets as easily as in Lean 3
    Subring.closure_le.2 Subsemiring.subset_closure⟩

theorem adjoin_eq_ring_closure (s : Set A) :
    (adjoin R s).toSubring = Subring.closure (Set.range (algebraMap R A) ∪ s) :=
  Subring.ext fun _x => mem_adjoin_iff

variable (R)

/-- If all elements of `s : Set A` commute pairwise, then `adjoin R s` is a commutative
ring. -/
abbrev adjoinCommRingOfComm {s : Set A} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommRing (adjoin R s) :=
  { (adjoin R s).toRing, adjoinCommSemiringOfComm R hcomm with }

end Ring

end Algebra

open Algebra Subalgebra

namespace AlgHom

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem map_adjoin (φ : A →ₐ[R] B) (s : Set A) : (adjoin R s).map φ = adjoin R (φ '' s) :=
  (adjoin_image _ _ _).symm

@[simp]
theorem map_adjoin_singleton (e : A →ₐ[R] B) (x : A) :
    (adjoin R {x}).map e = adjoin R {e x} := by
  rw [map_adjoin, Set.image_singleton]

theorem adjoin_le_equalizer (φ₁ φ₂ : A →ₐ[R] B) {s : Set A} (h : s.EqOn φ₁ φ₂) :
    adjoin R s ≤ equalizer φ₁ φ₂ :=
  adjoin_le h

theorem ext_of_adjoin_eq_top {s : Set A} (h : adjoin R s = ⊤) ⦃φ₁ φ₂ : A →ₐ[R] B⦄
    (hs : s.EqOn φ₁ φ₂) : φ₁ = φ₂ :=
  ext fun _x => adjoin_le_equalizer φ₁ φ₂ hs <| h.symm ▸ trivial

/-- Two algebra morphisms are equal on `Algebra.span s`iff they are equal on s -/
theorem eqOn_adjoin_iff {φ ψ : A →ₐ[R] B} {s : Set A}  :
    Set.EqOn φ ψ (adjoin R s) ↔ Set.EqOn φ ψ s := by
  have (S : Set A) : S ≤ equalizer φ ψ ↔ Set.EqOn φ ψ S := Iff.rfl
  simp only [← this, Set.le_eq_subset, SetLike.coe_subset_coe, adjoin_le_iff]

theorem adjoin_ext {s : Set A} ⦃φ₁ φ₂ : adjoin R s →ₐ[R] B⦄
    (h : ∀ x hx, φ₁ ⟨x, subset_adjoin hx⟩ = φ₂ ⟨x, subset_adjoin hx⟩) : φ₁ = φ₂ :=
  ext fun ⟨x, hx⟩ ↦ adjoin_induction h (fun _ ↦ φ₂.commutes _ ▸ φ₁.commutes _)
    (fun _ _ _ _ h₁ h₂ ↦ by convert congr_arg₂ (· + ·) h₁ h₂ <;> rw [← map_add] <;> rfl)
    (fun _ _ _ _ h₁ h₂ ↦ by convert congr_arg₂ (· * ·) h₁ h₂ <;> rw [← map_mul] <;> rfl) hx

theorem ext_of_eq_adjoin {S : Subalgebra R A} {s : Set A} (hS : S = adjoin R s) ⦃φ₁ φ₂ : S →ₐ[R] B⦄
    (h : ∀ x hx, φ₁ ⟨x, hS.ge (subset_adjoin hx)⟩ = φ₂ ⟨x, hS.ge (subset_adjoin hx)⟩) :
    φ₁ = φ₂ := by
  subst hS; exact adjoin_ext h

end AlgHom

section NatInt

theorem Algebra.adjoin_nat {R : Type*} [Semiring R] (s : Set R) :
    adjoin ℕ s = subalgebraOfSubsemiring (Subsemiring.closure s) :=
  le_antisymm (adjoin_le Subsemiring.subset_closure)
    (Subsemiring.closure_le.2 subset_adjoin : Subsemiring.closure s ≤ (adjoin ℕ s).toSubsemiring)

theorem Algebra.adjoin_int {R : Type*} [Ring R] (s : Set R) :
    adjoin ℤ s = subalgebraOfSubring (Subring.closure s) :=
  le_antisymm (adjoin_le Subring.subset_closure)
    (Subring.closure_le.2 subset_adjoin : Subring.closure s ≤ (adjoin ℤ s).toSubring)

/-- The `ℕ`-algebra equivalence between `Subsemiring.closure s` and `Algebra.adjoin ℕ s` given
by the identity map. -/
def Subsemiring.closureEquivAdjoinNat {R : Type*} [Semiring R] (s : Set R) :
    Subsemiring.closure s ≃ₐ[ℕ] Algebra.adjoin ℕ s :=
  Subalgebra.equivOfEq (subalgebraOfSubsemiring <| Subsemiring.closure s) _ (adjoin_nat s).symm

/-- The `ℤ`-algebra equivalence between `Subring.closure s` and `Algebra.adjoin ℤ s` given by
the identity map. -/
def Subring.closureEquivAdjoinInt {R : Type*} [Ring R] (s : Set R) :
    Subring.closure s ≃ₐ[ℤ] Algebra.adjoin ℤ s :=
  Subalgebra.equivOfEq (subalgebraOfSubring <| Subring.closure s) _ (adjoin_int s).symm

end NatInt

section

variable (F E : Type*) {K : Type*} [CommSemiring E] [Semiring K] [SMul F E] [Algebra E K]

/-- If `K / E / F` is a ring extension tower, `L` is a submonoid of `K / F` which is generated by
`S` as an `F`-module, then `E[L]` is generated by `S` as an `E`-module. -/
theorem Submonoid.adjoin_eq_span_of_eq_span [Semiring F] [Module F K] [IsScalarTower F E K]
    (L : Submonoid K) {S : Set K} (h : (L : Set K) = span F S) :
    toSubmodule (adjoin E (L : Set K)) = span E S := by
  rw [adjoin_eq_span, L.closure_eq, h]
  exact (span_le.mpr <| span_subset_span _ _ _).antisymm (span_mono subset_span)

variable [CommSemiring F] [Algebra F K] [IsScalarTower F E K] (L : Subalgebra F K) {F}

/-- If `K / E / F` is a ring extension tower, `L` is a subalgebra of `K / F` which is generated by
`S` as an `F`-module, then `E[L]` is generated by `S` as an `E`-module. -/
theorem Subalgebra.adjoin_eq_span_of_eq_span {S : Set K} (h : toSubmodule L = span F S) :
    toSubmodule (adjoin E (L : Set K)) = span E S :=
  L.toSubmonoid.adjoin_eq_span_of_eq_span F E (congr_arg ((↑) : _ → Set K) h)

/-- If `K / E / F` is a ring extension tower, `L` is a subalgebra of `K / F`,
then `E[L]` is generated by any basis of `L / F` as an `E`-module. -/
theorem Subalgebra.adjoin_eq_span_basis {ι : Type*} (bL : Basis ι F L) :
    toSubmodule (adjoin E (L : Set K)) = span E (Set.range fun i : ι ↦ (bL i).1) :=
  L.adjoin_eq_span_of_eq_span E <| by
    simpa only [← L.range_val, Submodule.map_span, Submodule.map_top, ← Set.range_comp]
      using congr_arg (Submodule.map L.val) bL.span_eq.symm

theorem Algebra.restrictScalars_adjoin (F : Type*) [CommSemiring F] {E : Type*} [CommSemiring E]
    [Algebra F E] (K : Subalgebra F E) (S : Set E) :
    (Algebra.adjoin K S).restrictScalars F = Algebra.adjoin F (K ∪ S) := by
  conv_lhs => rw [← Algebra.adjoin_eq K, ← Algebra.adjoin_union_eq_adjoin_adjoin]

/-- If `E / L / F` and `E / L' / F` are two ring extension towers, `L ≃ₐ[F] L'` is an isomorphism
compatible with `E / L` and `E / L'`, then for any subset `S` of `E`, `L[S]` and `L'[S]` are
equal as subalgebras of `E / F`. -/
theorem Algebra.restrictScalars_adjoin_of_algEquiv
    {F E L L' : Type*} [CommSemiring F] [CommSemiring L] [CommSemiring L'] [Semiring E]
    [Algebra F L] [Algebra L E] [Algebra F L'] [Algebra L' E] [Algebra F E]
    [IsScalarTower F L E] [IsScalarTower F L' E] (i : L ≃ₐ[F] L')
    (hi : algebraMap L E = (algebraMap L' E) ∘ i) (S : Set E) :
    (Algebra.adjoin L S).restrictScalars F = (Algebra.adjoin L' S).restrictScalars F := by
  apply_fun Subalgebra.toSubsemiring using fun K K' h ↦ by rwa [SetLike.ext'_iff] at h ⊢
  change Subsemiring.closure _ = Subsemiring.closure _
  erw [hi, Set.range_comp, i.toEquiv.range_eq_univ, Set.image_univ]

end

namespace Subalgebra

variable [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

theorem comap_map_eq (f : A →ₐ[R] B) (S : Subalgebra R A) :
    (S.map f).comap f = S ⊔ Algebra.adjoin R (f ⁻¹' {0}) := by
  apply le_antisymm
  · intro x hx
    rw [mem_comap, mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    replace hxy : x - y ∈ f ⁻¹' {0} := by simp [hxy]
    rw [← Algebra.adjoin_eq S, ← Algebra.adjoin_union, ← add_sub_cancel y x]
    exact Subalgebra.add_mem _
      (Algebra.subset_adjoin <| Or.inl hy) (Algebra.subset_adjoin <| Or.inr hxy)
  · rw [← map_le, Algebra.map_sup, f.map_adjoin]
    apply le_of_eq
    rw [sup_eq_left, Algebra.adjoin_le_iff]
    exact (Set.image_preimage_subset f {0}).trans (Set.singleton_subset_iff.2 (S.map f).zero_mem)

theorem comap_map_eq_self {f : A →ₐ[R] B} {S : Subalgebra R A}
    (h : f ⁻¹' {0} ⊆ S) : (S.map f).comap f = S := by
  convert comap_map_eq f S
  rwa [left_eq_sup, Algebra.adjoin_le_iff]

end Subalgebra
