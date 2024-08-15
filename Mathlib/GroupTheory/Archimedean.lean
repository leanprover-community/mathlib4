/-
Copyright (c) 2020 Heather Macbeth, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Patrick Massot
-/
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Order.Group.TypeTags

/-!
# Archimedean groups

This file proves a few facts about ordered groups which satisfy the `Archimedean` property, that is:
`class Archimedean (α) [OrderedAddCommMonoid α] : Prop :=`
`(arch : ∀ (x : α) {y}, 0 < y → ∃ n : ℕ, x ≤ n • y)`

They are placed here in a separate file (rather than incorporated as a continuation of
`Algebra.Order.Archimedean`) because they rely on some imports from `GroupTheory` -- bundled
subgroups in particular.

The main result is `AddSubgroup.cyclic_of_min`:  a subgroup of a decidable archimedean abelian
group is cyclic, if its set of positive elements has a minimal element.

This result is used in this file to deduce `Int.subgroup_cyclic`, proving that every subgroup of `ℤ`
is cyclic.  (There are several other methods one could use to prove this fact, including more purely
algebraic methods, but none seem to exist in mathlib as of writing.  The closest is
`Subgroup.is_cyclic`, but that has not been transferred to `AddSubgroup`.)

The file also supports multiplicative groups via `MulArchimedean`.

The result is also used in `Topology.Instances.Real` as an ingredient in the classification of
subgroups of `ℝ`.
-/

open Set
variable {G : Type*} [LinearOrderedCommGroup G]

-- no earlier file imports possible
@[to_additive]
lemma Subgroup.mem_closure_singleton_iff_existsUnique_zpow {a b : G} (ha : a ≠ 1) :
    (b ∈ closure {a}) ↔ ∃! k : ℤ, a ^ k = b := by
  constructor <;> intro h
  · wlog ha : 1 < a generalizing a b
    · simp only [not_lt] at ha
      rcases ha.eq_or_lt with rfl|ha
      · contradiction
      specialize @this a⁻¹ b (by simpa) (by simpa) (by simpa)
      simp only [inv_zpow'] at this
      obtain ⟨k, rfl, hk'⟩ := this
      refine ⟨-k, rfl, ?_⟩
      intro y hy
      rw [← neg_eq_iff_eq_neg]
      exact hk' _ (by simpa using hy)
    · rw [mem_closure_singleton] at h
      obtain ⟨k, hk⟩ := h
      refine ⟨k, hk, ?_⟩
      rintro l rfl
      exact (zpow_right_strictMono ha).injective hk.symm
  · rw [mem_closure_singleton]
    exact h.exists

open Subgroup in
/-- In two linearly ordered groups, the closure of an element of one group
is isomorphic (and order-isomorphic) to the closure of an element in the other group. -/
@[to_additive "In two linearly ordered additive groups, the closure of an element of one group
is isomorphic (and order-isomorphic) to the closure of an element in the other group."]
noncomputable def LinearOrderedCommGroup.closure_equiv_closure {G G' : Type*}
    [LinearOrderedCommGroup G] [LinearOrderedCommGroup G'] (x : G) (y : G') (hxy : x = 1 ↔ y = 1) :
    {f : closure ({x} : Set G) ≃* closure ({y} : Set G') // StrictMono f} :=
  if hx : x = 1 then by
    refine ⟨⟨⟨fun _ ↦ ⟨1, by simp [hxy.mp hx]⟩, fun _ ↦ ⟨1, by simp [hx]⟩, ?_, ?_⟩, ?_⟩, ?_⟩
    · intro ⟨a, ha⟩
      simpa [hx, closure_singleton_one, eq_comm] using ha
    · intro ⟨a, ha⟩
      simpa [hxy.mp hx, closure_singleton_one, eq_comm] using ha
    · intros
      simp
    · intro ⟨a, ha⟩ ⟨b, hb⟩
      simp only [hx, closure_singleton_one, mem_bot] at ha hb
      simp [ha, hb]
  else by
    set x' := max x x⁻¹ with hx'
    have xpos : 1 < x' := by
      simp [hx', eq_comm, hx]
    set y' := max y y⁻¹ with hy'
    have ypos : 1 < y' := by
      simp [hy', eq_comm, ← hxy, hx]
    have hxc : closure {x} = closure {x'} := by
      rcases max_cases x x⁻¹ with H|H <;>
      simp [hx', H.left]
    have hyc : closure {y} = closure {y'} := by
      rcases max_cases y y⁻¹ with H|H <;>
      simp [hy', H.left]
    refine ⟨⟨⟨
      fun a ↦ ⟨y' ^ ((mem_closure_singleton).mp
        (by simpa [hxc] using a.prop)).choose, ?_⟩,
      fun a ↦ ⟨x' ^ ((mem_closure_singleton).mp
        (by simpa [hyc] using a.prop)).choose, ?_⟩,
        ?_, ?_⟩, ?_⟩, ?_⟩
    · rw [hyc, mem_closure_singleton]
      exact ⟨_, rfl⟩
    · rw [hxc, mem_closure_singleton]
      exact ⟨_, rfl⟩
    · intro a
      generalize_proofs A B C D
      rw [Subtype.ext_iff, ← (C a).choose_spec, (zpow_right_strictMono xpos).injective.eq_iff,
          ← (zpow_right_strictMono ypos).injective.eq_iff, (A ⟨_, D a⟩).choose_spec]
    · intro a
      generalize_proofs A B C D
      rw [Subtype.ext_iff, ← (C a).choose_spec, (zpow_right_strictMono ypos).injective.eq_iff,
          ← (zpow_right_strictMono xpos).injective.eq_iff, (A ⟨_, D a⟩).choose_spec]
    · intro a b
      generalize_proofs A B C D E F
      simp only [Submonoid.coe_mul, coe_toSubmonoid, Submonoid.mk_mul_mk, Subtype.mk.injEq]
      rw [← zpow_add, (zpow_right_strictMono ypos).injective.eq_iff,
          ← (zpow_right_strictMono xpos).injective.eq_iff, zpow_add,
          (A a).choose_spec, (A b).choose_spec, (A (a * b)).choose_spec]
      simp
    · intro a b hab
      simp only [MulEquiv.coe_mk, Equiv.coe_fn_mk, Subtype.mk_lt_mk]
      generalize_proofs A B C D
      rw [(zpow_right_strictMono ypos).lt_iff_lt, ← (zpow_right_strictMono xpos).lt_iff_lt,
          A.choose_spec, B.choose_spec]
      simpa using hab

variable [MulArchimedean G]

/-- Given a subgroup `H` of a decidable linearly ordered mul-archimedean abelian group `G`, if there
exists a minimal element `a` of `H ∩ G_{>1}` then `H` is generated by `a`. -/
@[to_additive AddSubgroup.cyclic_of_min "Given a subgroup `H` of a decidable linearly ordered
archimedean abelian group `G`, if there exists a minimal element `a` of `H ∩ G_{>0}` then `H` is
generated by `a`. "]
theorem Subgroup.cyclic_of_min {H : Subgroup G} {a : G}
    (ha : IsLeast { g : G | g ∈ H ∧ 1 < g } a) : H = closure {a} := by
  obtain ⟨⟨a_in, a_pos⟩, a_min⟩ := ha
  refine le_antisymm ?_ (H.closure_le.mpr <| by simp [a_in])
  intro g g_in
  obtain ⟨k, ⟨nonneg, lt⟩, _⟩ := existsUnique_zpow_near_of_one_lt a_pos g
  have h_zero : g / (a ^ k) = 1 := by
    by_contra h
    have h : a ≤ g / (a ^ k) := by
      refine a_min ⟨?_, ?_⟩
      · exact Subgroup.div_mem H g_in (Subgroup.zpow_mem H a_in k)
      · exact lt_of_le_of_ne (by simpa using nonneg) (Ne.symm h)
    have h' : ¬a ≤ g / (a ^ k) := not_le.mpr (by simpa [zpow_add_one, div_lt_iff_lt_mul'] using lt)
    contradiction
  simp [div_eq_one.mp h_zero, mem_closure_singleton]

/-- If a nontrivial subgroup of a linear ordered commutative group is disjoint
with the interval `Set.Ioo 1 a` for some `1 < a`, then the set of elements greater than 1 of this
group admits the least element. -/
@[to_additive "If a nontrivial additive subgroup of a linear ordered additive commutative group is
disjoint with the interval `Set.Ioo 0 a` for some positive `a`, then the set of positive elements of
this group admits the least element."]
theorem Subgroup.exists_isLeast_one_lt {H : Subgroup G} (hbot : H ≠ ⊥) {a : G} (h₀ : 1 < a)
    (hd : Disjoint (H : Set G) (Ioo 1 a)) : ∃ b, IsLeast { g : G | g ∈ H ∧ 1 < g } b := by
  -- todo: move to a lemma?
  have hex : ∀ g > 1, ∃ n : ℕ, g ∈ Ioc (a ^ n) (a ^ (n + 1)) := fun g hg => by
    rcases existsUnique_mul_zpow_mem_Ico h₀ 1 (g / a) with ⟨m, ⟨hm, hm'⟩, -⟩
    simp only [one_mul, div_le_iff_le_mul, div_mul_cancel, ← zpow_add_one] at hm hm'
    lift m to ℕ
    · rw [← Int.lt_add_one_iff, ← zpow_lt_zpow_iff h₀, zpow_zero]
      exact hg.trans_le hm
    · simp only [← Nat.cast_succ, zpow_natCast] at hm hm'
      exact ⟨m, hm', hm⟩
  have : ∃ n : ℕ, Set.Nonempty (H ∩ Ioc (a ^ n) (a ^ (n + 1))) := by
    rcases (bot_or_exists_ne_one H).resolve_left hbot with ⟨g, hgH, hg₀⟩
    rcases hex |g|ₘ (one_lt_mabs.2 hg₀) with ⟨n, hn⟩
    exact ⟨n, _, (@mabs_mem_iff (Subgroup G) G _ _).2 hgH, hn⟩
  classical rcases Nat.findX this with ⟨n, ⟨x, hxH, hnx, hxn⟩, hmin⟩
  by_contra hxmin
  simp only [IsLeast, not_and, mem_setOf_eq, mem_lowerBounds, not_exists, not_forall,
    not_le] at hxmin
  rcases hxmin x ⟨hxH, (one_le_pow_of_one_le'  h₀.le _).trans_lt hnx⟩ with ⟨y, ⟨hyH, hy₀⟩, hxy⟩
  rcases hex y hy₀ with ⟨m, hm⟩
  cases' lt_or_le m n with hmn hnm
  · exact hmin m hmn ⟨y, hyH, hm⟩
  · refine disjoint_left.1 hd (div_mem hxH hyH) ⟨one_lt_div'.2 hxy, div_lt_iff_lt_mul'.2 ?_⟩
    calc x ≤ a^ (n + 1) := hxn
    _ ≤ a ^ (m + 1) := pow_le_pow_right' h₀.le (add_le_add_right hnm _)
    _ = a ^ m * a := pow_succ _ _
    _ < y * a := mul_lt_mul_right' hm.1 _

/-- If a subgroup of a linear ordered commutative group is disjoint with the
interval `Set.Ioo 1 a` for some `1 < a`, then this is a cyclic subgroup. -/
@[to_additive AddSubgroup.cyclic_of_isolated_zero "If an additive subgroup of a linear ordered
additive commutative group is disjoint with the interval `Set.Ioo 0 a` for some positive `a`, then
this is a cyclic subgroup."]
theorem Subgroup.cyclic_of_isolated_one {H : Subgroup G} {a : G} (h₀ : 1 < a)
    (hd : Disjoint (H : Set G) (Ioo 1 a)) : ∃ b, H = closure {b} := by
  rcases eq_or_ne H ⊥ with rfl | hbot
  · exact ⟨1, closure_singleton_one.symm⟩
  · exact (exists_isLeast_one_lt hbot h₀ hd).imp fun _ => cyclic_of_min

@[to_additive]
lemma Subgroup.isLeast_of_closure_iff_eq_mabs {a b : G} :
    IsLeast {y : G | y ∈ closure ({a} : Set G) ∧ 1 < y} b ↔ b = |a|ₘ ∧ 1 < b := by
  constructor <;> intro h
  · have := Subgroup.cyclic_of_min h
    have ha : a ∈ closure ({b} : Set G) := by
      simp [← this]
    rw [mem_closure_singleton] at ha
    obtain ⟨n, rfl⟩ := ha
    have := h.left
    simp only [mem_closure_singleton, mem_setOf_eq, ← mul_zsmul] at this
    obtain ⟨m, hm⟩ := this.left
    have key : m * n = 1 := by
      rw [← (zpow_right_strictMono this.right).injective.eq_iff, zpow_mul', hm, zpow_one]
    rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at key
    rw [eq_comm]
    rcases key with ⟨rfl, rfl⟩|⟨rfl, rfl⟩ <;>
    simp [this.right.le, this.right, mabs]
  · wlog ha : 1 ≤ a generalizing a
    · convert @this (a⁻¹) ?_ (by simpa using le_of_not_le ha) using 4
      · simp
      · rwa [mabs_inv]
    rw [mabs, sup_eq_left.mpr ((inv_le_one'.mpr ha).trans ha)] at h
    rcases h with ⟨rfl, h⟩
    refine ⟨?_, ?_⟩
    · simp [h]
    · intro x
      simp only [mem_closure_singleton, mem_setOf_eq, and_imp, forall_exists_index]
      rintro k rfl hk
      rw [← zpow_one b, ← zpow_mul, one_mul, zpow_le_zpow_iff h, ← zero_add 1,
          ← Int.lt_iff_add_one_le]
      contrapose! hk
      rw [← Left.one_le_inv_iff, ← zpow_neg]
      exact one_le_zpow ha (by simp [hk])

/-- Every subgroup of `ℤ` is cyclic. -/
theorem Int.subgroup_cyclic (H : AddSubgroup ℤ) : ∃ a, H = AddSubgroup.closure {a} :=
  have : Ioo (0 : ℤ) 1 = ∅ := eq_empty_of_forall_not_mem fun m hm =>
    hm.1.not_le (lt_add_one_iff.1 hm.2)
  AddSubgroup.cyclic_of_isolated_zero one_pos <| by simp [this]

lemma AddSubgroup.closure_singleton_int_one_eq_top : closure ({1} : Set ℤ) = ⊤ := by
  rw [eq_comm]
  apply cyclic_of_min
  refine ⟨?_, ?_⟩
  · simp
  · intro x
    simp only [mem_top, true_and, mem_setOf_eq]
    exact id

/-- If an element of a linearly ordered archimedean additive group is the least positive element,
then the whole group is isomorphic (and order-isomorphic) to the integers. -/
noncomputable def LinearOrderedAddCommGroup.int_addEquiv_of_isLeast_pos {G : Type*}
    [LinearOrderedAddCommGroup G] [Archimedean G] {x : G} (h : IsLeast {y : G | 0 < y} x) :
    {f : G ≃+ ℤ // StrictMono f} := by
  have : IsLeast {y : G | y ∈ (⊤ : AddSubgroup G) ∧ 0 < y} x := by simpa using h
  replace this := AddSubgroup.cyclic_of_min this
  let e : G ≃+ (⊤ : AddSubgroup G) := AddSubsemigroup.topEquiv.symm
  let e' : (⊤ : AddSubgroup G) ≃+ AddSubgroup.closure {x} :=
    AddEquiv.subsemigroupCongr (by simp [this])
  let g : ℤ ≃+ (⊤ : AddSubgroup ℤ) := AddSubsemigroup.topEquiv.symm
  let g' : (⊤ : AddSubgroup ℤ) ≃+ AddSubgroup.closure ({1} : Set ℤ) :=
    (.subsemigroupCongr (by simp [AddSubgroup.closure_singleton_int_one_eq_top]))
  let f := closure_equiv_closure x (1 : ℤ) (by simp [h.left.ne'])
  refine ⟨(((e.trans e').trans f.val).trans g'.symm).trans g.symm, ?_⟩
  intro a b hab
  have hab' : f.val (e' (e a)) < f.val (e' (e b)) := by
    rw [f.prop.lt_iff_lt]
    exact hab
  exact hab'

/-- If an element of a linearly ordered mul-archimedean group is the least element greater than 1,
then the whole group is isomorphic (and order-isomorphic) to the multiplicative integers. -/
@[to_additive existing LinearOrderedAddCommGroup.int_addEquiv_of_isLeast_pos]
noncomputable def LinearOrderedCommGroup.multiplicative_int_mulEquiv_of_isLeast_one_lt
    {x : G} (h : IsLeast {y : G | 1 < y} x) :
    {f : G ≃* Multiplicative ℤ // StrictMono f} := by
  have : IsLeast {y : Additive G | 0 < y} (.ofMul x) := h
  let f' := LinearOrderedAddCommGroup.int_addEquiv_of_isLeast_pos (G := Additive G) this
  exact ⟨AddEquiv.toMultiplicative' f'.val, f'.prop⟩

/-- Any linearly ordered archimedean additive group is either is isomorphic (and order-isomorphic)
to the integers, or is densely ordered. -/
lemma LinearOrderedAddCommGroup.discrete_or_denselyOrdered (G : Type*) [LinearOrderedAddCommGroup G]
    [Archimedean G] : (∃ f : G ≃+ ℤ, StrictMono f) ∨ DenselyOrdered G := by
  by_cases H : ∃ x, IsLeast {y : G | 0 < y} x
  · obtain ⟨x, hx⟩ := H
    exact Or.inl ⟨_, (LinearOrderedAddCommGroup.int_addEquiv_of_isLeast_pos hx).prop⟩
  · push_neg at H
    refine Or.inr ⟨?_⟩
    intro x y hxy
    specialize H (y - x)
    obtain ⟨z, hz⟩ : ∃ z : G, 0 < z ∧ z < y - x := by
      contrapose! H
      refine ⟨by simp [hxy], fun _ ↦ H _⟩
    refine ⟨x + z, ?_, ?_⟩
    · simp [hz.left]
    · simpa [lt_sub_iff_add_lt'] using hz.right

variable (G) in
/-- Any linearly ordered mul-archimedean group is either is isomorphic (and order-isomorphic)
to the multiplicative integers, or is densely ordered. -/
@[to_additive existing]
lemma LinearOrderedCommGroup.discrete_or_denselyOrdered :
    (∃ f : G ≃* Multiplicative ℤ, StrictMono f) ∨ DenselyOrdered G := by
  refine (LinearOrderedAddCommGroup.discrete_or_denselyOrdered (Additive G)).imp ?_ id
  rintro ⟨f, hf⟩
  exact ⟨AddEquiv.toMultiplicative' f, hf⟩
