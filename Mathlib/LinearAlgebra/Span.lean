/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathlib.LinearAlgebra.Basic
import Mathlib.Order.CompactlyGenerated
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Tactic.Ring

#align_import linear_algebra.span from "leanprover-community/mathlib"@"10878f6bf1dab863445907ab23fbfcefcb5845d0"

/-!
# The span of a set of vectors, as a submodule

* `Submodule.span s` is defined to be the smallest submodule containing the set `s`.

## Notations

* We introduce the notation `R ∙ v` for the span of a singleton, `Submodule.span R {v}`.  This is
  `\.`, not the same as the scalar multiplication `•`/`\bub`.

-/

variable {R R₂ K M M₂ V S : Type*}

namespace Submodule

open Function Set

open Pointwise

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {x : M} (p p' : Submodule R M)

variable [Semiring R₂] {σ₁₂ : R →+* R₂}

variable [AddCommMonoid M₂] [Module R₂ M₂] {F : Type*} [SemilinearMapClass F σ₁₂ M M₂]

section

variable (R)

/-- The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`. -/
def span (s : Set M) : Submodule R M :=
  sInf { p | s ⊆ p }
#align submodule.span Submodule.span

end

variable {s t : Set M}

theorem mem_span : x ∈ span R s ↔ ∀ p : Submodule R M, s ⊆ p → x ∈ p :=
  mem_iInter₂
#align submodule.mem_span Submodule.mem_span

theorem subset_span : s ⊆ span R s := fun _ h => mem_span.2 fun _ hp => hp h
#align submodule.subset_span Submodule.subset_span

theorem span_le {p} : span R s ≤ p ↔ s ⊆ p :=
  ⟨Subset.trans subset_span, fun ss _ h => mem_span.1 h _ ss⟩
#align submodule.span_le Submodule.span_le

theorem span_mono (h : s ⊆ t) : span R s ≤ span R t :=
  span_le.2 <| Subset.trans h subset_span
#align submodule.span_mono Submodule.span_mono

theorem span_monotone : Monotone (span R : Set M → Submodule R M) := fun _ _ => span_mono
#align submodule.span_monotone Submodule.span_monotone

theorem span_eq_of_le (h₁ : s ⊆ p) (h₂ : p ≤ span R s) : span R s = p :=
  le_antisymm (span_le.2 h₁) h₂
#align submodule.span_eq_of_le Submodule.span_eq_of_le

theorem span_eq : span R (p : Set M) = p :=
  span_eq_of_le _ (Subset.refl _) subset_span
#align submodule.span_eq Submodule.span_eq

theorem span_eq_span (hs : s ⊆ span R t) (ht : t ⊆ span R s) : span R s = span R t :=
  le_antisymm (span_le.2 hs) (span_le.2 ht)
#align submodule.span_eq_span Submodule.span_eq_span

/-- A version of `Submodule.span_eq` for when the span is by a smaller ring. -/
@[simp]
theorem span_coe_eq_restrictScalars [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :
    span S (p : Set M) = p.restrictScalars S :=
  span_eq (p.restrictScalars S)
#align submodule.span_coe_eq_restrict_scalars Submodule.span_coe_eq_restrictScalars

theorem map_span [RingHomSurjective σ₁₂] (f : F) (s : Set M) :
    (span R s).map f = span R₂ (f '' s) :=
  Eq.symm <|
    span_eq_of_le _ (Set.image_subset f subset_span) <|
      map_le_iff_le_comap.2 <| span_le.2 fun x hx => subset_span ⟨x, hx, rfl⟩
#align submodule.map_span Submodule.map_span

alias _root_.LinearMap.map_span := Submodule.map_span
#align linear_map.map_span LinearMap.map_span

theorem map_span_le [RingHomSurjective σ₁₂] (f : F) (s : Set M) (N : Submodule R₂ M₂) :
    map f (span R s) ≤ N ↔ ∀ m ∈ s, f m ∈ N := by
  rw [map_span, span_le, Set.image_subset_iff]
  -- ⊢ s ⊆ ↑f ⁻¹' ↑N ↔ ∀ (m : M), m ∈ s → ↑f m ∈ N
  exact Iff.rfl
  -- 🎉 no goals
#align submodule.map_span_le Submodule.map_span_le

alias _root_.LinearMap.map_span_le := Submodule.map_span_le
#align linear_map.map_span_le LinearMap.map_span_le

@[simp]
theorem span_insert_zero : span R (insert (0 : M) s) = span R s := by
  refine' le_antisymm _ (Submodule.span_mono (Set.subset_insert 0 s))
  -- ⊢ span R (insert 0 s) ≤ span R s
  rw [span_le, Set.insert_subset_iff]
  -- ⊢ 0 ∈ ↑(span R s) ∧ s ⊆ ↑(span R s)
  exact ⟨by simp only [SetLike.mem_coe, Submodule.zero_mem], Submodule.subset_span⟩
  -- 🎉 no goals
#align submodule.span_insert_zero Submodule.span_insert_zero

-- See also `span_preimage_eq` below.
theorem span_preimage_le (f : F) (s : Set M₂) :
    span R (f ⁻¹' s) ≤ (span R₂ s).comap f := by
  rw [span_le, comap_coe]
  -- ⊢ ↑f ⁻¹' s ⊆ ↑f ⁻¹' ↑(span R₂ s)
  exact preimage_mono subset_span
  -- 🎉 no goals
#align submodule.span_preimage_le Submodule.span_preimage_le

alias _root_.LinearMap.span_preimage_le := Submodule.span_preimage_le
#align linear_map.span_preimage_le LinearMap.span_preimage_le

theorem closure_subset_span {s : Set M} : (AddSubmonoid.closure s : Set M) ⊆ span R s :=
  (@AddSubmonoid.closure_le _ _ _ (span R s).toAddSubmonoid).mpr subset_span
#align submodule.closure_subset_span Submodule.closure_subset_span

theorem closure_le_toAddSubmonoid_span {s : Set M} :
    AddSubmonoid.closure s ≤ (span R s).toAddSubmonoid :=
  closure_subset_span
#align submodule.closure_le_to_add_submonoid_span Submodule.closure_le_toAddSubmonoid_span

@[simp]
theorem span_closure {s : Set M} : span R (AddSubmonoid.closure s : Set M) = span R s :=
  le_antisymm (span_le.mpr closure_subset_span) (span_mono AddSubmonoid.subset_closure)
#align submodule.span_closure Submodule.span_closure

/-- An induction principle for span membership. If `p` holds for 0 and all elements of `s`, and is
preserved under addition and scalar multiplication, then `p` holds for all elements of the span of
`s`. -/
@[elab_as_elim]
theorem span_induction {p : M → Prop} (h : x ∈ span R s) (Hs : ∀ x ∈ s, p x) (H0 : p 0)
    (H1 : ∀ x y, p x → p y → p (x + y)) (H2 : ∀ (a : R) (x), p x → p (a • x)) : p x :=
  ((@span_le (p := ⟨ ⟨⟨p, by intros x y; exact H1 x y⟩, H0⟩, H2⟩)) s).2 Hs h
                             -- ⊢ x ∈ p → y ∈ p → x + y ∈ p
                                         -- 🎉 no goals
#align submodule.span_induction Submodule.span_induction

/-- An induction principle for span membership. This is a version of `Submodule.span_induction`
for binary predicates. -/
theorem span_induction₂ {p : M → M → Prop} {a b : M} (ha : a ∈ Submodule.span R s)
    (hb : b ∈ Submodule.span R s) (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y)
    (H0_left : ∀ y, p 0 y) (H0_right : ∀ x, p x 0)
    (Hadd_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hsmul_left : ∀ (r : R) x y, p x y → p (r • x) y)
    (Hsmul_right : ∀ (r : R) x y, p x y → p x (r • y)) : p a b :=
  Submodule.span_induction ha
    (fun x hx => Submodule.span_induction hb (Hs x hx) (H0_right x) (Hadd_right x) fun r =>
      Hsmul_right r x)
    (H0_left b) (fun x₁ x₂ => Hadd_left x₁ x₂ b) fun r x => Hsmul_left r x b

/-- A dependent version of `Submodule.span_induction`. -/
theorem span_induction' {p : ∀ x, x ∈ span R s → Prop}
    (Hs : ∀ (x) (h : x ∈ s), p x (subset_span h))
    (H0 : p 0 (Submodule.zero_mem _))
    (H1 : ∀ x hx y hy, p x hx → p y hy → p (x + y) (Submodule.add_mem _ ‹_› ‹_›))
    (H2 : ∀ (a : R) (x hx), p x hx → p (a • x) (Submodule.smul_mem _ _ ‹_›)) {x}
    (hx : x ∈ span R s) : p x hx := by
  refine' Exists.elim _ fun (hx : x ∈ span R s) (hc : p x hx) => hc
  -- ⊢ ∃ x_1, p x x_1
  refine'
    span_induction hx (fun m hm => ⟨subset_span hm, Hs m hm⟩) ⟨zero_mem _, H0⟩
      (fun x y hx hy =>
        Exists.elim hx fun hx' hx =>
          Exists.elim hy fun hy' hy => ⟨add_mem hx' hy', H1 _ _ _ _ hx hy⟩)
      fun r x hx => Exists.elim hx fun hx' hx => ⟨smul_mem _ _ hx', H2 r _ _ hx⟩
#align submodule.span_induction' Submodule.span_induction'

@[simp]
theorem span_span_coe_preimage : span R (((↑) : span R s → M) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun x ↦ Subtype.recOn x fun x hx _ ↦ by
    refine' span_induction' (p := fun x hx ↦ (⟨x, hx⟩ : span R s) ∈ span R (Subtype.val ⁻¹' s))
      (fun x' hx' ↦ subset_span hx') _ (fun x _ y _ ↦ _) (fun r x _ ↦ _) hx
    · exact zero_mem _
      -- 🎉 no goals
    · exact add_mem
      -- 🎉 no goals
    · exact smul_mem _ _
      -- 🎉 no goals
#align submodule.span_span_coe_preimage Submodule.span_span_coe_preimage

theorem span_nat_eq_addSubmonoid_closure (s : Set M) :
    (span ℕ s).toAddSubmonoid = AddSubmonoid.closure s := by
  refine' Eq.symm (AddSubmonoid.closure_eq_of_le subset_span _)
  -- ⊢ (span ℕ s).toAddSubmonoid ≤ AddSubmonoid.closure s
  apply (OrderIso.to_galoisConnection (AddSubmonoid.toNatSubmodule (M := M)).symm).l_le
     (a := span ℕ s) (b := AddSubmonoid.closure s)
  rw [span_le]
  -- ⊢ s ⊆ ↑(↑(OrderIso.symm (OrderIso.symm AddSubmonoid.toNatSubmodule)) (AddSubmo …
  exact AddSubmonoid.subset_closure
  -- 🎉 no goals
#align submodule.span_nat_eq_add_submonoid_closure Submodule.span_nat_eq_addSubmonoid_closure

@[simp]
theorem span_nat_eq (s : AddSubmonoid M) : (span ℕ (s : Set M)).toAddSubmonoid = s := by
  rw [span_nat_eq_addSubmonoid_closure, s.closure_eq]
  -- 🎉 no goals
#align submodule.span_nat_eq Submodule.span_nat_eq

theorem span_int_eq_addSubgroup_closure {M : Type*} [AddCommGroup M] (s : Set M) :
    (span ℤ s).toAddSubgroup = AddSubgroup.closure s :=
  Eq.symm <|
    AddSubgroup.closure_eq_of_le _ subset_span fun x hx =>
      span_induction hx (fun x hx => AddSubgroup.subset_closure hx) (AddSubgroup.zero_mem _)
        (fun _ _ => AddSubgroup.add_mem _) fun _ _ _ => AddSubgroup.zsmul_mem _ ‹_› _
#align submodule.span_int_eq_add_subgroup_closure Submodule.span_int_eq_addSubgroup_closure

@[simp]
theorem span_int_eq {M : Type*} [AddCommGroup M] (s : AddSubgroup M) :
    (span ℤ (s : Set M)).toAddSubgroup = s := by rw [span_int_eq_addSubgroup_closure, s.closure_eq]
                                                 -- 🎉 no goals
#align submodule.span_int_eq Submodule.span_int_eq

section

variable (R M)

/-- `span` forms a Galois insertion with the coercion from submodule to set. -/
protected def gi : GaloisInsertion (@span R M _ _ _) (↑)
    where
  choice s _ := span R s
  gc _ _ := span_le
  le_l_u _ := subset_span
  choice_eq _ _ := rfl
#align submodule.gi Submodule.gi

end

@[simp]
theorem span_empty : span R (∅ : Set M) = ⊥ :=
  (Submodule.gi R M).gc.l_bot
#align submodule.span_empty Submodule.span_empty

@[simp]
theorem span_univ : span R (univ : Set M) = ⊤ :=
  eq_top_iff.2 <| SetLike.le_def.2 <| subset_span
#align submodule.span_univ Submodule.span_univ

theorem span_union (s t : Set M) : span R (s ∪ t) = span R s ⊔ span R t :=
  (Submodule.gi R M).gc.l_sup
#align submodule.span_union Submodule.span_union

theorem span_iUnion {ι} (s : ι → Set M) : span R (⋃ i, s i) = ⨆ i, span R (s i) :=
  (Submodule.gi R M).gc.l_iSup
#align submodule.span_Union Submodule.span_iUnion

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem span_iUnion₂ {ι} {κ : ι → Sort*} (s : ∀ i, κ i → Set M) :
    span R (⋃ (i) (j), s i j) = ⨆ (i) (j), span R (s i j) :=
  (Submodule.gi R M).gc.l_iSup₂
#align submodule.span_Union₂ Submodule.span_iUnion₂

theorem span_attach_biUnion [DecidableEq M] {α : Type*} (s : Finset α) (f : s → Finset M) :
    span R (s.attach.biUnion f : Set M) = ⨆ x, span R (f x) := by simp [span_iUnion]
                                                                  -- 🎉 no goals
#align submodule.span_attach_bUnion Submodule.span_attach_biUnion

theorem sup_span : p ⊔ span R s = span R (p ∪ s) := by rw [Submodule.span_union, p.span_eq]
                                                       -- 🎉 no goals
#align submodule.sup_span Submodule.sup_span

theorem span_sup : span R s ⊔ p = span R (s ∪ p) := by rw [Submodule.span_union, p.span_eq]
                                                       -- 🎉 no goals
#align submodule.span_sup Submodule.span_sup

-- mathport name: «expr ∙ »
notation:1000
  /- Note that the character `∙` U+2219 used below is different from the scalar multiplication
character `•` U+2022. -/
R " ∙ " x => span R (singleton x)

theorem span_eq_iSup_of_singleton_spans (s : Set M) : span R s = ⨆ x ∈ s, R ∙ x := by
  simp only [← span_iUnion, Set.biUnion_of_singleton s]
  -- 🎉 no goals
#align submodule.span_eq_supr_of_singleton_spans Submodule.span_eq_iSup_of_singleton_spans

theorem span_range_eq_iSup {ι : Type*} {v : ι → M} : span R (range v) = ⨆ i, R ∙ v i := by
  rw [span_eq_iSup_of_singleton_spans, iSup_range]
  -- 🎉 no goals
#align submodule.span_range_eq_supr Submodule.span_range_eq_iSup

theorem span_smul_le (s : Set M) (r : R) : span R (r • s) ≤ span R s := by
  rw [span_le]
  -- ⊢ r • s ⊆ ↑(span R s)
  rintro _ ⟨x, hx, rfl⟩
  -- ⊢ (fun x => r • x) x ∈ ↑(span R s)
  exact smul_mem (span R s) r (subset_span hx)
  -- 🎉 no goals
#align submodule.span_smul_le Submodule.span_smul_le

theorem subset_span_trans {U V W : Set M} (hUV : U ⊆ Submodule.span R V)
    (hVW : V ⊆ Submodule.span R W) : U ⊆ Submodule.span R W :=
  (Submodule.gi R M).gc.le_u_l_trans hUV hVW
#align submodule.subset_span_trans Submodule.subset_span_trans

/-- See `submodule.span_smul_eq` (in `RingTheory.Ideal.Operations`) for
`span R (r • s) = r • span R s` that holds for arbitrary `r` in a `CommSemiring`. -/
theorem span_smul_eq_of_isUnit (s : Set M) (r : R) (hr : IsUnit r) : span R (r • s) = span R s := by
  apply le_antisymm
  -- ⊢ span R (r • s) ≤ span R s
  · apply span_smul_le
    -- 🎉 no goals
  · convert span_smul_le (r • s) ((hr.unit⁻¹ : _) : R)
    -- ⊢ s = ↑(IsUnit.unit hr)⁻¹ • r • s
    rw [smul_smul]
    -- ⊢ s = (↑(IsUnit.unit hr)⁻¹ * r) • s
    erw [hr.unit.inv_val]
    -- ⊢ s = 1 • s
    rw [one_smul]
    -- 🎉 no goals
#align submodule.span_smul_eq_of_is_unit Submodule.span_smul_eq_of_isUnit

@[simp]
theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] (S : ι → Submodule R M)
    (H : Directed (· ≤ ·) S) : ((iSup S : Submodule R M) : Set M) = ⋃ i, S i := by
  refine' Subset.antisymm _ (iUnion_subset <| le_iSup S)
  -- ⊢ ↑(iSup S) ⊆ ⋃ (i : ι), ↑(S i)
  suffices (span R (⋃ i, (S i : Set M)) : Set M) ⊆ ⋃ i : ι, ↑(S i) by
    simpa only [span_iUnion, span_eq] using this
  refine' fun x hx => span_induction hx (fun _ => id) _ _ _ <;> simp only [mem_iUnion, exists_imp]
                                                                -- ⊢ ∃ i, 0 ∈ ↑(S i)
                                                                -- ⊢ ∀ (x y : M) (x_1 : ι), x ∈ ↑(S x_1) → ∀ (x_2 : ι), y ∈ ↑(S x_2) → ∃ i, x + y …
                                                                -- ⊢ ∀ (a : R) (x : M) (x_1 : ι), x ∈ ↑(S x_1) → ∃ i, a • x ∈ ↑(S i)
  · exact hι.elim fun i => ⟨i, (S i).zero_mem⟩
    -- 🎉 no goals
  · intro x y i hi j hj
    -- ⊢ ∃ i, x + y ∈ ↑(S i)
    rcases H i j with ⟨k, ik, jk⟩
    -- ⊢ ∃ i, x + y ∈ ↑(S i)
    exact ⟨k, add_mem (ik hi) (jk hj)⟩
    -- 🎉 no goals
  · exact fun a x i hi => ⟨i, smul_mem _ a hi⟩
    -- 🎉 no goals
#align submodule.coe_supr_of_directed Submodule.coe_iSup_of_directed

@[simp]
theorem mem_iSup_of_directed {ι} [Nonempty ι] (S : ι → Submodule R M) (H : Directed (· ≤ ·) S) {x} :
    x ∈ iSup S ↔ ∃ i, x ∈ S i := by
  rw [← SetLike.mem_coe, coe_iSup_of_directed S H, mem_iUnion]
  -- ⊢ (∃ i, x ∈ ↑(S i)) ↔ ∃ i, x ∈ S i
  rfl
  -- 🎉 no goals
#align submodule.mem_supr_of_directed Submodule.mem_iSup_of_directed

theorem mem_sSup_of_directed {s : Set (Submodule R M)} {z} (hs : s.Nonempty)
    (hdir : DirectedOn (· ≤ ·) s) : z ∈ sSup s ↔ ∃ y ∈ s, z ∈ y := by
  have : Nonempty s := hs.to_subtype
  -- ⊢ z ∈ sSup s ↔ ∃ y, y ∈ s ∧ z ∈ y
  simp only [sSup_eq_iSup', mem_iSup_of_directed _ hdir.directed_val, SetCoe.exists, Subtype.coe_mk,
    exists_prop]
#align submodule.mem_Sup_of_directed Submodule.mem_sSup_of_directed

@[norm_cast, simp]
theorem coe_iSup_of_chain (a : ℕ →o Submodule R M) : (↑(⨆ k, a k) : Set M) = ⋃ k, (a k : Set M) :=
  coe_iSup_of_directed a a.monotone.directed_le
#align submodule.coe_supr_of_chain Submodule.coe_iSup_of_chain

/-- We can regard `coe_iSup_of_chain` as the statement that `(↑) : (Submodule R M) → Set M` is
Scott continuous for the ω-complete partial order induced by the complete lattice structures. -/
theorem coe_scott_continuous :
    OmegaCompletePartialOrder.Continuous' ((↑) : Submodule R M → Set M) :=
  ⟨SetLike.coe_mono, coe_iSup_of_chain⟩
#align submodule.coe_scott_continuous Submodule.coe_scott_continuous

@[simp]
theorem mem_iSup_of_chain (a : ℕ →o Submodule R M) (m : M) : (m ∈ ⨆ k, a k) ↔ ∃ k, m ∈ a k :=
  mem_iSup_of_directed a a.monotone.directed_le
#align submodule.mem_supr_of_chain Submodule.mem_iSup_of_chain

section

variable {p p'}

theorem mem_sup : x ∈ p ⊔ p' ↔ ∃ y ∈ p, ∃ z ∈ p', y + z = x :=
  ⟨fun h => by
    rw [← span_eq p, ← span_eq p', ← span_union] at h
    -- ⊢ ∃ y, y ∈ p ∧ ∃ z, z ∈ p' ∧ y + z = x
    refine span_induction h ?_ ?_ ?_ ?_
    · rintro y (h | h)
      -- ⊢ ∃ y_1, y_1 ∈ p ∧ ∃ z, z ∈ p' ∧ y_1 + z = y
      · exact ⟨y, h, 0, by simp, by simp⟩
        -- 🎉 no goals
      · exact ⟨0, by simp, y, h, by simp⟩
        -- 🎉 no goals
    · exact ⟨0, by simp, 0, by simp⟩
      -- 🎉 no goals
    · rintro _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      -- ⊢ ∃ y, y ∈ p ∧ ∃ z, z ∈ p' ∧ y + z = y₁ + z₁ + (y₂ + z₂)
      exact ⟨_, add_mem hy₁ hy₂, _, add_mem hz₁ hz₂, by
        rw [add_assoc, add_assoc, ← add_assoc y₂, ← add_assoc z₁, add_comm y₂]⟩
    · rintro a _ ⟨y, hy, z, hz, rfl⟩
      -- ⊢ ∃ y_1, y_1 ∈ p ∧ ∃ z_1, z_1 ∈ p' ∧ y_1 + z_1 = a • (y + z)
      exact ⟨_, smul_mem _ a hy, _, smul_mem _ a hz, by simp [smul_add]⟩, by
      -- 🎉 no goals
    rintro ⟨y, hy, z, hz, rfl⟩
    -- ⊢ y + z ∈ p ⊔ p'
    exact add_mem ((le_sup_left : p ≤ p ⊔ p') hy) ((le_sup_right : p' ≤ p ⊔ p') hz)⟩
    -- 🎉 no goals
#align submodule.mem_sup Submodule.mem_sup

theorem mem_sup' : x ∈ p ⊔ p' ↔ ∃ (y : p) (z : p'), (y : M) + z = x :=
  mem_sup.trans <| by simp only [Subtype.exists, exists_prop]
                      -- 🎉 no goals
#align submodule.mem_sup' Submodule.mem_sup'

variable (p p')

theorem coe_sup : ↑(p ⊔ p') = (p + p' : Set M) := by
  ext
  -- ⊢ x✝ ∈ ↑(p ⊔ p') ↔ x✝ ∈ ↑p + ↑p'
  rw [SetLike.mem_coe, mem_sup, Set.mem_add]
  -- ⊢ (∃ y, y ∈ p ∧ ∃ z, z ∈ p' ∧ y + z = x✝) ↔ ∃ x y, x ∈ ↑p ∧ y ∈ ↑p' ∧ x + y = x✝
  simp
  -- 🎉 no goals
#align submodule.coe_sup Submodule.coe_sup

theorem sup_toAddSubmonoid : (p ⊔ p').toAddSubmonoid = p.toAddSubmonoid ⊔ p'.toAddSubmonoid := by
  ext x
  -- ⊢ x ∈ (p ⊔ p').toAddSubmonoid ↔ x ∈ p.toAddSubmonoid ⊔ p'.toAddSubmonoid
  rw [mem_toAddSubmonoid, mem_sup, AddSubmonoid.mem_sup]
  -- ⊢ (∃ y, y ∈ p ∧ ∃ z, z ∈ p' ∧ y + z = x) ↔ ∃ y, y ∈ p.toAddSubmonoid ∧ ∃ z, z  …
  rfl
  -- 🎉 no goals
#align submodule.sup_to_add_submonoid Submodule.sup_toAddSubmonoid

theorem sup_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p p' : Submodule R M) : (p ⊔ p').toAddSubgroup = p.toAddSubgroup ⊔ p'.toAddSubgroup := by
  ext x
  -- ⊢ x ∈ toAddSubgroup (p ⊔ p') ↔ x ∈ toAddSubgroup p ⊔ toAddSubgroup p'
  rw [mem_toAddSubgroup, mem_sup, AddSubgroup.mem_sup]
  -- ⊢ (∃ y, y ∈ p ∧ ∃ z, z ∈ p' ∧ y + z = x) ↔ ∃ y, y ∈ toAddSubgroup p ∧ ∃ z, z ∈ …
  rfl
  -- 🎉 no goals
#align submodule.sup_to_add_subgroup Submodule.sup_toAddSubgroup

end

theorem mem_span_singleton_self (x : M) : x ∈ R ∙ x :=
  subset_span rfl
#align submodule.mem_span_singleton_self Submodule.mem_span_singleton_self

theorem nontrivial_span_singleton {x : M} (h : x ≠ 0) : Nontrivial (R ∙ x) :=
  ⟨by
    use 0, ⟨x, Submodule.mem_span_singleton_self x⟩
    -- ⊢ 0 ≠ { val := x, property := (_ : x ∈ span R {x}) }
    intro H
    -- ⊢ False
    rw [eq_comm, Submodule.mk_eq_zero] at H
    -- ⊢ False
    exact h H⟩
    -- 🎉 no goals
#align submodule.nontrivial_span_singleton Submodule.nontrivial_span_singleton

theorem mem_span_singleton {y : M} : (x ∈ R ∙ y) ↔ ∃ a : R, a • y = x :=
  ⟨fun h => by
    refine span_induction h ?_ ?_ ?_ ?_
    · rintro y (rfl | ⟨⟨_⟩⟩)
      -- ⊢ ∃ a, a • y = y
      exact ⟨1, by simp⟩
      -- 🎉 no goals
    · exact ⟨0, by simp⟩
      -- 🎉 no goals
    · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      -- ⊢ ∃ a_1, a_1 • y = a • y + b • y
      exact ⟨a + b, by simp [add_smul]⟩
      -- 🎉 no goals
    · rintro a _ ⟨b, rfl⟩
      -- ⊢ ∃ a_1, a_1 • y = a • b • y
      exact ⟨a * b, by simp [smul_smul]⟩, by
      -- 🎉 no goals
    rintro ⟨a, y, rfl⟩; exact smul_mem _ _ (subset_span <| by simp)⟩
    -- ⊢ a • y ∈ span R {y}
                        -- 🎉 no goals
#align submodule.mem_span_singleton Submodule.mem_span_singleton

theorem le_span_singleton_iff {s : Submodule R M} {v₀ : M} :
    (s ≤ R ∙ v₀) ↔ ∀ v ∈ s, ∃ r : R, r • v₀ = v := by simp_rw [SetLike.le_def, mem_span_singleton]
                                                      -- 🎉 no goals
#align submodule.le_span_singleton_iff Submodule.le_span_singleton_iff

variable (R)

theorem span_singleton_eq_top_iff (x : M) : (R ∙ x) = ⊤ ↔ ∀ v, ∃ r : R, r • x = v := by
  rw [eq_top_iff, le_span_singleton_iff]
  -- ⊢ (∀ (v : M), v ∈ ⊤ → ∃ r, r • x = v) ↔ ∀ (v : M), ∃ r, r • x = v
  tauto
  -- 🎉 no goals
#align submodule.span_singleton_eq_top_iff Submodule.span_singleton_eq_top_iff

@[simp]
theorem span_zero_singleton : (R ∙ (0 : M)) = ⊥ := by
  ext
  -- ⊢ x✝ ∈ span R {0} ↔ x✝ ∈ ⊥
  simp [mem_span_singleton, eq_comm]
  -- 🎉 no goals
#align submodule.span_zero_singleton Submodule.span_zero_singleton

theorem span_singleton_eq_range (y : M) : ↑(R ∙ y) = range ((· • y) : R → M) :=
  Set.ext fun _ => mem_span_singleton
#align submodule.span_singleton_eq_range Submodule.span_singleton_eq_range

theorem span_singleton_smul_le {S} [Monoid S] [SMul S R] [MulAction S M] [IsScalarTower S R M]
    (r : S) (x : M) : (R ∙ r • x) ≤ R ∙ x := by
  rw [span_le, Set.singleton_subset_iff, SetLike.mem_coe]
  -- ⊢ r • x ∈ span R {x}
  exact smul_of_tower_mem _ _ (mem_span_singleton_self _)
  -- 🎉 no goals
#align submodule.span_singleton_smul_le Submodule.span_singleton_smul_le

theorem span_singleton_group_smul_eq {G} [Group G] [SMul G R] [MulAction G M] [IsScalarTower G R M]
    (g : G) (x : M) : (R ∙ g • x) = R ∙ x := by
  refine' le_antisymm (span_singleton_smul_le R g x) _
  -- ⊢ span R {x} ≤ span R {g • x}
  convert span_singleton_smul_le R g⁻¹ (g • x)
  -- ⊢ x = g⁻¹ • g • x
  exact (inv_smul_smul g x).symm
  -- 🎉 no goals
#align submodule.span_singleton_group_smul_eq Submodule.span_singleton_group_smul_eq

variable {R}

theorem span_singleton_smul_eq {r : R} (hr : IsUnit r) (x : M) : (R ∙ r • x) = R ∙ x := by
  lift r to Rˣ using hr
  -- ⊢ span R {↑r • x} = span R {x}
  rw [← Units.smul_def]
  -- ⊢ span R {r • x} = span R {x}
  exact span_singleton_group_smul_eq R r x
  -- 🎉 no goals
#align submodule.span_singleton_smul_eq Submodule.span_singleton_smul_eq

theorem disjoint_span_singleton {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    {s : Submodule K E} {x : E} : Disjoint s (K ∙ x) ↔ x ∈ s → x = 0 := by
  refine' disjoint_def.trans ⟨fun H hx => H x hx <| subset_span <| mem_singleton x, _⟩
  -- ⊢ (x ∈ s → x = 0) → ∀ (x_1 : E), x_1 ∈ s → x_1 ∈ span K {x} → x_1 = 0
  intro H y hy hyx
  -- ⊢ y = 0
  obtain ⟨c, rfl⟩ := mem_span_singleton.1 hyx
  -- ⊢ c • x = 0
  by_cases hc : c = 0
  -- ⊢ c • x = 0
  · rw [hc, zero_smul]
    -- 🎉 no goals
  · rw [s.smul_mem_iff hc] at hy
    -- ⊢ c • x = 0
    rw [H hy, smul_zero]
    -- 🎉 no goals
#align submodule.disjoint_span_singleton Submodule.disjoint_span_singleton

theorem disjoint_span_singleton' {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    {p : Submodule K E} {x : E} (x0 : x ≠ 0) : Disjoint p (K ∙ x) ↔ x ∉ p :=
  disjoint_span_singleton.trans ⟨fun h₁ h₂ => x0 (h₁ h₂), fun h₁ h₂ => (h₁ h₂).elim⟩
#align submodule.disjoint_span_singleton' Submodule.disjoint_span_singleton'

theorem mem_span_singleton_trans {x y z : M} (hxy : x ∈ R ∙ y) (hyz : y ∈ R ∙ z) : x ∈ R ∙ z := by
  rw [← SetLike.mem_coe, ← singleton_subset_iff] at *
  -- ⊢ {x} ⊆ ↑(span R {z})
  exact Submodule.subset_span_trans hxy hyz
  -- 🎉 no goals
#align submodule.mem_span_singleton_trans Submodule.mem_span_singleton_trans

theorem span_insert (x) (s : Set M) : span R (insert x s) = (R ∙ x) ⊔ span R s := by
  rw [insert_eq, span_union]
  -- 🎉 no goals
#align submodule.span_insert Submodule.span_insert

theorem span_insert_eq_span (h : x ∈ span R s) : span R (insert x s) = span R s :=
  span_eq_of_le _ (Set.insert_subset_iff.mpr ⟨h, subset_span⟩) (span_mono <| subset_insert _ _)
#align submodule.span_insert_eq_span Submodule.span_insert_eq_span

theorem span_span : span R (span R s : Set M) = span R s :=
  span_eq _
#align submodule.span_span Submodule.span_span

theorem mem_span_insert {y} :
    x ∈ span R (insert y s) ↔ ∃ a : R, ∃ z ∈ span R s, x = a • y + z := by
  simp [span_insert, mem_sup, mem_span_singleton, eq_comm (a := x)]
  -- 🎉 no goals
#align submodule.mem_span_insert Submodule.mem_span_insert

theorem mem_span_pair {x y z : M} :
    z ∈ span R ({x, y} : Set M) ↔ ∃ a b : R, a • x + b • y = z := by
  simp_rw [mem_span_insert, mem_span_singleton, exists_exists_eq_and, eq_comm]
  -- 🎉 no goals
#align submodule.mem_span_pair Submodule.mem_span_pair

variable (R S s)

/-- If `R` is "smaller" ring than `S` then the span by `R` is smaller than the span by `S`. -/
theorem span_le_restrictScalars [Semiring S] [SMul R S] [Module S M] [IsScalarTower R S M] :
    span R s ≤ (span S s).restrictScalars R :=
  Submodule.span_le.2 Submodule.subset_span
#align submodule.span_le_restrict_scalars Submodule.span_le_restrictScalars

/-- A version of `Submodule.span_le_restrictScalars` with coercions. -/
@[simp]
theorem span_subset_span [Semiring S] [SMul R S] [Module S M] [IsScalarTower R S M] :
    ↑(span R s) ⊆ (span S s : Set M) :=
  span_le_restrictScalars R S s
#align submodule.span_subset_span Submodule.span_subset_span

/-- Taking the span by a large ring of the span by the small ring is the same as taking the span
by just the large ring. -/
theorem span_span_of_tower [Semiring S] [SMul R S] [Module S M] [IsScalarTower R S M] :
    span S (span R s : Set M) = span S s :=
  le_antisymm (span_le.2 <| span_subset_span R S s) (span_mono subset_span)
#align submodule.span_span_of_tower Submodule.span_span_of_tower

variable {R S s}

theorem span_eq_bot : span R (s : Set M) = ⊥ ↔ ∀ x ∈ s, (x : M) = 0 :=
  eq_bot_iff.trans
    ⟨fun H _ h => (mem_bot R).1 <| H <| subset_span h, fun H =>
      span_le.2 fun x h => (mem_bot R).2 <| H x h⟩
#align submodule.span_eq_bot Submodule.span_eq_bot

@[simp]
theorem span_singleton_eq_bot : (R ∙ x) = ⊥ ↔ x = 0 :=
  span_eq_bot.trans <| by simp
                          -- 🎉 no goals
#align submodule.span_singleton_eq_bot Submodule.span_singleton_eq_bot

@[simp]
theorem span_zero : span R (0 : Set M) = ⊥ := by rw [← singleton_zero, span_singleton_eq_bot]
                                                 -- 🎉 no goals
#align submodule.span_zero Submodule.span_zero

@[simp]
theorem span_singleton_le_iff_mem (m : M) (p : Submodule R M) : (R ∙ m) ≤ p ↔ m ∈ p := by
  rw [span_le, singleton_subset_iff, SetLike.mem_coe]
  -- 🎉 no goals
#align submodule.span_singleton_le_iff_mem Submodule.span_singleton_le_iff_mem

theorem span_singleton_eq_span_singleton {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [NoZeroSMulDivisors R M] {x y : M} : ((R ∙ x) = R ∙ y) ↔ ∃ z : Rˣ, z • x = y := by
  constructor
  -- ⊢ span R {x} = span R {y} → ∃ z, z • x = y
  · simp only [le_antisymm_iff, span_singleton_le_iff_mem, mem_span_singleton]
    -- ⊢ ((∃ a, a • y = x) ∧ ∃ a, a • x = y) → ∃ z, z • x = y
    rintro ⟨⟨a, rfl⟩, b, hb⟩
    -- ⊢ ∃ z, z • a • y = y
    rcases eq_or_ne y 0 with rfl | hy; · simp
    -- ⊢ ∃ z, z • a • 0 = 0
                                         -- 🎉 no goals
    refine ⟨⟨b, a, ?_, ?_⟩, hb⟩
    -- ⊢ b * a = 1
    · apply smul_left_injective R hy
      -- ⊢ (fun c => c • y) (b * a) = (fun c => c • y) 1
      simpa only [mul_smul, one_smul]
      -- 🎉 no goals
    · rw [← hb] at hy
      -- ⊢ a * b = 1
      apply smul_left_injective R (smul_ne_zero_iff.1 hy).2
      -- ⊢ (fun c => c • a • y) (a * b) = (fun c => c • a • y) 1
      simp only [mul_smul, one_smul, hb]
      -- 🎉 no goals
  · rintro ⟨u, rfl⟩
    -- ⊢ span R {x} = span R {u • x}
    exact (span_singleton_group_smul_eq _ _ _).symm
    -- 🎉 no goals
#align submodule.span_singleton_eq_span_singleton Submodule.span_singleton_eq_span_singleton

@[simp]
theorem span_image [RingHomSurjective σ₁₂] (f : F) :
    span R₂ (f '' s) = map f (span R s) :=
  (map_span f s).symm
#align submodule.span_image Submodule.span_image

theorem apply_mem_span_image_of_mem_span [RingHomSurjective σ₁₂] (f : F) {x : M}
    {s : Set M} (h : x ∈ Submodule.span R s) : f x ∈ Submodule.span R₂ (f '' s) := by
  rw [Submodule.span_image]
  -- ⊢ ↑f x ∈ map f (span R s)
  exact Submodule.mem_map_of_mem h
  -- 🎉 no goals
#align submodule.apply_mem_span_image_of_mem_span Submodule.apply_mem_span_image_of_mem_span

theorem apply_mem_span_image_iff_mem_span [RingHomSurjective σ₁₂] {f : F} {x : M}
    {s : Set M} (hf : Function.Injective f) :
    f x ∈ Submodule.span R₂ (f '' s) ↔ x ∈ Submodule.span R s := by
  rw [← Submodule.mem_comap, ← Submodule.map_span, Submodule.comap_map_eq_of_injective hf]
  -- 🎉 no goals

@[simp]
theorem map_subtype_span_singleton {p : Submodule R M} (x : p) :
    map p.subtype (R ∙ x) = R ∙ (x : M) := by simp [← span_image]
                                              -- 🎉 no goals
#align submodule.map_subtype_span_singleton Submodule.map_subtype_span_singleton

/-- `f` is an explicit argument so we can `apply` this theorem and obtain `h` as a new goal. -/
theorem not_mem_span_of_apply_not_mem_span_image [RingHomSurjective σ₁₂] (f : F) {x : M}
    {s : Set M} (h : f x ∉ Submodule.span R₂ (f '' s)) : x ∉ Submodule.span R s :=
  h.imp (apply_mem_span_image_of_mem_span f)
#align submodule.not_mem_span_of_apply_not_mem_span_image Submodule.not_mem_span_of_apply_not_mem_span_image

theorem iSup_span {ι : Sort*} (p : ι → Set M) : ⨆ i, span R (p i) = span R (⋃ i, p i) :=
  le_antisymm (iSup_le fun i => span_mono <| subset_iUnion _ i) <|
    span_le.mpr <| iUnion_subset fun i _ hm => mem_iSup_of_mem i <| subset_span hm
#align submodule.supr_span Submodule.iSup_span

theorem iSup_eq_span {ι : Sort*} (p : ι → Submodule R M) : ⨆ i, p i = span R (⋃ i, ↑(p i)) := by
  simp_rw [← iSup_span, span_eq]
  -- 🎉 no goals
#align submodule.supr_eq_span Submodule.iSup_eq_span

theorem iSup_toAddSubmonoid {ι : Sort*} (p : ι → Submodule R M) :
    (⨆ i, p i).toAddSubmonoid = ⨆ i, (p i).toAddSubmonoid := by
  refine' le_antisymm (fun x => _) (iSup_le fun i => toAddSubmonoid_mono <| le_iSup _ i)
  -- ⊢ x ∈ (⨆ (i : ι), p i).toAddSubmonoid → x ∈ ⨆ (i : ι), (p i).toAddSubmonoid
  simp_rw [iSup_eq_span, AddSubmonoid.iSup_eq_closure, mem_toAddSubmonoid, coe_toAddSubmonoid]
  -- ⊢ x ∈ span R (⋃ (i : ι), ↑(p i)) → x ∈ AddSubmonoid.closure (⋃ (i : ι), ↑(p i))
  intro hx
  -- ⊢ x ∈ AddSubmonoid.closure (⋃ (i : ι), ↑(p i))
  refine' Submodule.span_induction hx (fun x hx => _) _ (fun x y hx hy => _) fun r x hx => _
  · exact AddSubmonoid.subset_closure hx
    -- 🎉 no goals
  · exact AddSubmonoid.zero_mem _
    -- 🎉 no goals
  · exact AddSubmonoid.add_mem _ hx hy
    -- 🎉 no goals
  · refine AddSubmonoid.closure_induction hx ?_ ?_ ?_
    · rintro x ⟨_, ⟨i, rfl⟩, hix : x ∈ p i⟩
      -- ⊢ r • x ∈ AddSubmonoid.closure (⋃ (i : ι), ↑(p i))
      apply AddSubmonoid.subset_closure (Set.mem_iUnion.mpr ⟨i, _⟩)
      -- ⊢ r • x ∈ ↑(p i)
      exact smul_mem _ r hix
      -- 🎉 no goals
    · rw [smul_zero]
      -- ⊢ 0 ∈ AddSubmonoid.closure (⋃ (i : ι), ↑(p i))
      exact AddSubmonoid.zero_mem _
      -- 🎉 no goals
    · intro x y hx hy
      -- ⊢ r • (x + y) ∈ AddSubmonoid.closure (⋃ (i : ι), ↑(p i))
      rw [smul_add]
      -- ⊢ r • x + r • y ∈ AddSubmonoid.closure (⋃ (i : ι), ↑(p i))
      exact AddSubmonoid.add_mem _ hx hy
      -- 🎉 no goals
#align submodule.supr_to_add_submonoid Submodule.iSup_toAddSubmonoid

/-- An induction principle for elements of `⨆ i, p i`.
If `C` holds for `0` and all elements of `p i` for all `i`, and is preserved under addition,
then it holds for all elements of the supremum of `p`. -/
@[elab_as_elim]
theorem iSup_induction {ι : Sort*} (p : ι → Submodule R M) {C : M → Prop} {x : M}
    (hx : x ∈ ⨆ i, p i) (hp : ∀ (i), ∀ x ∈ p i, C x) (h0 : C 0)
    (hadd : ∀ x y, C x → C y → C (x + y)) : C x := by
  rw [← mem_toAddSubmonoid, iSup_toAddSubmonoid] at hx
  -- ⊢ C x
  exact AddSubmonoid.iSup_induction (x := x) _ hx hp h0 hadd
  -- 🎉 no goals
#align submodule.supr_induction Submodule.iSup_induction

/-- A dependent version of `submodule.iSup_induction`. -/
@[elab_as_elim]
theorem iSup_induction' {ι : Sort*} (p : ι → Submodule R M) {C : ∀ x, (x ∈ ⨆ i, p i) → Prop}
    (hp : ∀ (i) (x) (hx : x ∈ p i), C x (mem_iSup_of_mem i hx)) (h0 : C 0 (zero_mem _))
    (hadd : ∀ x y hx hy, C x hx → C y hy → C (x + y) (add_mem ‹_› ‹_›)) {x : M}
    (hx : x ∈ ⨆ i, p i) : C x hx := by
  refine' Exists.elim _ fun (hx : x ∈ ⨆ i, p i) (hc : C x hx) => hc
  -- ⊢ ∃ x_1, C x x_1
  refine' iSup_induction p (C := fun x : M ↦ ∃ (hx : x ∈ ⨆ i, p i), C x hx) hx
    (fun i x hx => _) _ fun x y => _
  · exact ⟨_, hp _ _ hx⟩
    -- 🎉 no goals
  · exact ⟨_, h0⟩
    -- 🎉 no goals
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    -- ⊢ ∃ hx, C (x + y) hx
    refine' ⟨_, hadd _ _ _ _ Cx Cy⟩
    -- 🎉 no goals
#align submodule.supr_induction' Submodule.iSup_induction'

theorem singleton_span_isCompactElement (x : M) :
    CompleteLattice.IsCompactElement (span R {x} : Submodule R M) := by
  rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le]
  -- ⊢ ∀ (s : Set (Submodule R M)), Set.Nonempty s → DirectedOn (fun x x_1 => x ≤ x …
  intro d hemp hdir hsup
  -- ⊢ ∃ x_1, x_1 ∈ d ∧ span R {x} ≤ x_1
  have : x ∈ (sSup d) := (SetLike.le_def.mp hsup) (mem_span_singleton_self x)
  -- ⊢ ∃ x_1, x_1 ∈ d ∧ span R {x} ≤ x_1
  obtain ⟨y, ⟨hyd, hxy⟩⟩ := (mem_sSup_of_directed hemp hdir).mp this
  -- ⊢ ∃ x_1, x_1 ∈ d ∧ span R {x} ≤ x_1
  exact ⟨y, ⟨hyd, by simpa only [span_le, singleton_subset_iff] ⟩⟩
  -- 🎉 no goals
#align submodule.singleton_span_is_compact_element Submodule.singleton_span_isCompactElement

/-- The span of a finite subset is compact in the lattice of submodules. -/
theorem finset_span_isCompactElement (S : Finset M) :
    CompleteLattice.IsCompactElement (span R S : Submodule R M) := by
  rw [span_eq_iSup_of_singleton_spans]
  -- ⊢ CompleteLattice.IsCompactElement (⨆ (x : M) (_ : x ∈ ↑S), span R {x})
  simp only [Finset.mem_coe]
  -- ⊢ CompleteLattice.IsCompactElement (⨆ (x : M) (_ : x ∈ S), span R {x})
  rw [← Finset.sup_eq_iSup]
  -- ⊢ CompleteLattice.IsCompactElement (Finset.sup S fun x => span R {x})
  exact
    CompleteLattice.finset_sup_compact_of_compact S fun x _ => singleton_span_isCompactElement x
#align submodule.finset_span_is_compact_element Submodule.finset_span_isCompactElement

/-- The span of a finite subset is compact in the lattice of submodules. -/
theorem finite_span_isCompactElement (S : Set M) (h : S.Finite) :
    CompleteLattice.IsCompactElement (span R S : Submodule R M) :=
  Finite.coe_toFinset h ▸ finset_span_isCompactElement h.toFinset
#align submodule.finite_span_is_compact_element Submodule.finite_span_isCompactElement

instance : IsCompactlyGenerated (Submodule R M) :=
  ⟨fun s =>
    ⟨(fun x => span R {x}) '' s,
      ⟨fun t ht => by
        rcases(Set.mem_image _ _ _).1 ht with ⟨x, _, rfl⟩
        -- ⊢ CompleteLattice.IsCompactElement (span R {x})
        apply singleton_span_isCompactElement, by
        -- 🎉 no goals
        rw [sSup_eq_iSup, iSup_image, ← span_eq_iSup_of_singleton_spans, span_eq]⟩⟩⟩
        -- 🎉 no goals

/-- A submodule is equal to the supremum of the spans of the submodule's nonzero elements. -/
theorem submodule_eq_sSup_le_nonzero_spans (p : Submodule R M) :
    p = sSup { T : Submodule R M | ∃ (m : M) (_ : m ∈ p) (_ : m ≠ 0), T = span R {m} } := by
  let S := { T : Submodule R M | ∃ (m : M) (_ : m ∈ p) (_ : m ≠ 0), T = span R {m} }
  -- ⊢ p = sSup {T | ∃ m x x, T = span R {m}}
  apply le_antisymm
  -- ⊢ p ≤ sSup {T | ∃ m x x, T = span R {m}}
  · intro m hm
    -- ⊢ m ∈ sSup {T | ∃ m x x, T = span R {m}}
    by_cases h : m = 0
    -- ⊢ m ∈ sSup {T | ∃ m x x, T = span R {m}}
    · rw [h]
      -- ⊢ 0 ∈ sSup {T | ∃ m x x, T = span R {m}}
      simp
      -- 🎉 no goals
    · exact @le_sSup _ _ S _ ⟨m, ⟨hm, ⟨h, rfl⟩⟩⟩ m (mem_span_singleton_self m)
      -- 🎉 no goals
  · rw [sSup_le_iff]
    -- ⊢ ∀ (b : Submodule R M), b ∈ {T | ∃ m x x, T = span R {m}} → b ≤ p
    rintro S ⟨_, ⟨_, ⟨_, rfl⟩⟩⟩
    -- ⊢ span R {w✝²} ≤ p
    rwa [span_singleton_le_iff_mem]
    -- 🎉 no goals
#align submodule.submodule_eq_Sup_le_nonzero_spans Submodule.submodule_eq_sSup_le_nonzero_spans

theorem lt_sup_iff_not_mem {I : Submodule R M} {a : M} : (I < I ⊔ R ∙ a) ↔ a ∉ I := by simp
                                                                                       -- 🎉 no goals
#align submodule.lt_sup_iff_not_mem Submodule.lt_sup_iff_not_mem

theorem mem_iSup {ι : Sort*} (p : ι → Submodule R M) {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N := by
  rw [← span_singleton_le_iff_mem, le_iSup_iff]
  -- ⊢ (∀ (b : Submodule R M), (∀ (i : ι), p i ≤ b) → span R {m} ≤ b) ↔ ∀ (N : Subm …
  simp only [span_singleton_le_iff_mem]
  -- 🎉 no goals
#align submodule.mem_supr Submodule.mem_iSup

section

/-- For every element in the span of a set, there exists a finite subset of the set
such that the element is contained in the span of the subset. -/
theorem mem_span_finite_of_mem_span {S : Set M} {x : M} (hx : x ∈ span R S) :
    ∃ T : Finset M, ↑T ⊆ S ∧ x ∈ span R (T : Set M) := by
  classical
  refine' span_induction hx (fun x hx => _) _ _ _
  · refine' ⟨{x}, _, _⟩
    · rwa [Finset.coe_singleton, Set.singleton_subset_iff]
    · rw [Finset.coe_singleton]
      exact Submodule.mem_span_singleton_self x
  · use ∅
    simp
  · rintro x y ⟨X, hX, hxX⟩ ⟨Y, hY, hyY⟩
    refine' ⟨X ∪ Y, _, _⟩
    · rw [Finset.coe_union]
      exact Set.union_subset hX hY
    rw [Finset.coe_union, span_union, mem_sup]
    exact ⟨x, hxX, y, hyY, rfl⟩
  · rintro a x ⟨T, hT, h2⟩
    exact ⟨T, hT, smul_mem _ _ h2⟩
#align submodule.mem_span_finite_of_mem_span Submodule.mem_span_finite_of_mem_span

end

variable {M' : Type*} [AddCommMonoid M'] [Module R M'] (q₁ q₁' : Submodule R M')

/-- The product of two submodules is a submodule. -/
def prod : Submodule R (M × M') :=
  { p.toAddSubmonoid.prod q₁.toAddSubmonoid with
    carrier := p ×ˢ q₁
    smul_mem' := by rintro a ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨smul_mem _ a hx, smul_mem _ a hy⟩ }
                    -- ⊢ a • (x, y) ∈ { toAddSubsemigroup := { carrier := ↑p ×ˢ ↑q₁, add_mem' := (_ : …
                                              -- 🎉 no goals
#align submodule.prod Submodule.prod

@[simp]
theorem prod_coe : (prod p q₁ : Set (M × M')) = (p : Set M) ×ˢ (q₁ : Set M') :=
  rfl
#align submodule.prod_coe Submodule.prod_coe

@[simp]
theorem mem_prod {p : Submodule R M} {q : Submodule R M'} {x : M × M'} :
    x ∈ prod p q ↔ x.1 ∈ p ∧ x.2 ∈ q :=
  Set.mem_prod
#align submodule.mem_prod Submodule.mem_prod

theorem span_prod_le (s : Set M) (t : Set M') : span R (s ×ˢ t) ≤ prod (span R s) (span R t) :=
  span_le.2 <| Set.prod_mono subset_span subset_span
#align submodule.span_prod_le Submodule.span_prod_le

@[simp]
theorem prod_top : (prod ⊤ ⊤ : Submodule R (M × M')) = ⊤ := by ext; simp
                                                               -- ⊢ x✝ ∈ prod ⊤ ⊤ ↔ x✝ ∈ ⊤
                                                                    -- 🎉 no goals
#align submodule.prod_top Submodule.prod_top

@[simp]
theorem prod_bot : (prod ⊥ ⊥ : Submodule R (M × M')) = ⊥ := by ext ⟨x, y⟩; simp [Prod.zero_eq_mk]
                                                               -- ⊢ (x, y) ∈ prod ⊥ ⊥ ↔ (x, y) ∈ ⊥
                                                                           -- 🎉 no goals
#align submodule.prod_bot Submodule.prod_bot

-- Porting note: Added nonrec
nonrec theorem prod_mono {p p' : Submodule R M} {q q' : Submodule R M'} :
    p ≤ p' → q ≤ q' → prod p q ≤ prod p' q' :=
  prod_mono
#align submodule.prod_mono Submodule.prod_mono

@[simp]
theorem prod_inf_prod : prod p q₁ ⊓ prod p' q₁' = prod (p ⊓ p') (q₁ ⊓ q₁') :=
  SetLike.coe_injective Set.prod_inter_prod
#align submodule.prod_inf_prod Submodule.prod_inf_prod

@[simp]
theorem prod_sup_prod : prod p q₁ ⊔ prod p' q₁' = prod (p ⊔ p') (q₁ ⊔ q₁') := by
  refine'
    le_antisymm (sup_le (prod_mono le_sup_left le_sup_left) (prod_mono le_sup_right le_sup_right)) _
  simp [SetLike.le_def]; intro xx yy hxx hyy
  -- ⊢ ∀ (a : M) (b : M'), a ∈ p ⊔ p' → b ∈ q₁ ⊔ q₁' → (a, b) ∈ prod p q₁ ⊔ prod p' …
                         -- ⊢ (xx, yy) ∈ prod p q₁ ⊔ prod p' q₁'
  rcases mem_sup.1 hxx with ⟨x, hx, x', hx', rfl⟩
  -- ⊢ (x + x', yy) ∈ prod p q₁ ⊔ prod p' q₁'
  rcases mem_sup.1 hyy with ⟨y, hy, y', hy', rfl⟩
  -- ⊢ (x + x', y + y') ∈ prod p q₁ ⊔ prod p' q₁'
  refine' mem_sup.2 ⟨(x, y), ⟨hx, hy⟩, (x', y'), ⟨hx', hy'⟩, rfl⟩
  -- 🎉 no goals
#align submodule.prod_sup_prod Submodule.prod_sup_prod

end AddCommMonoid

section AddCommGroup

variable [Ring R] [AddCommGroup M] [Module R M]

@[simp]
theorem span_neg (s : Set M) : span R (-s) = span R s :=
  calc
    span R (-s) = span R ((-LinearMap.id : M →ₗ[R] M) '' s) := by simp
                                                                  -- 🎉 no goals
    _ = map (-LinearMap.id) (span R s) := (map_span (-LinearMap.id) _).symm
    _ = span R s := by simp
                       -- 🎉 no goals
#align submodule.span_neg Submodule.span_neg

theorem mem_span_insert' {x y} {s : Set M} :
    x ∈ span R (insert y s) ↔ ∃ a : R, x + a • y ∈ span R s := by
  rw [mem_span_insert]; constructor
  -- ⊢ (∃ a z, z ∈ span R s ∧ x = a • y + z) ↔ ∃ a, x + a • y ∈ span R s
                        -- ⊢ (∃ a z, z ∈ span R s ∧ x = a • y + z) → ∃ a, x + a • y ∈ span R s
  · rintro ⟨a, z, hz, rfl⟩
    -- ⊢ ∃ a_1, a • y + z + a_1 • y ∈ span R s
    exact ⟨-a, by simp [hz, add_assoc]⟩
    -- 🎉 no goals
  · rintro ⟨a, h⟩
    -- ⊢ ∃ a z, z ∈ span R s ∧ x = a • y + z
    exact ⟨-a, _, h, by simp [add_comm, add_left_comm]⟩
    -- 🎉 no goals
#align submodule.mem_span_insert' Submodule.mem_span_insert'

instance : IsModularLattice (Submodule R M) :=
  ⟨fun y z xz a ha => by
    rw [mem_inf, mem_sup] at ha
    -- ⊢ a ∈ x✝ ⊔ y ⊓ z
    rcases ha with ⟨⟨b, hb, c, hc, rfl⟩, haz⟩
    -- ⊢ b + c ∈ x✝ ⊔ y ⊓ z
    rw [mem_sup]
    -- ⊢ ∃ y_1, y_1 ∈ x✝ ∧ ∃ z_1, z_1 ∈ y ⊓ z ∧ y_1 + z_1 = b + c
    refine' ⟨b, hb, c, mem_inf.2 ⟨hc, _⟩, rfl⟩
    -- ⊢ c ∈ z
    rw [← add_sub_cancel c b, add_comm]
    -- ⊢ b + c - b ∈ z
    apply z.sub_mem haz (xz hb)⟩
    -- 🎉 no goals

end AddCommGroup

section AddCommGroup

variable [Semiring R] [Semiring R₂]

variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]

variable {F : Type*} [sc : SemilinearMapClass F τ₁₂ M M₂]

theorem comap_map_eq (f : F) (p : Submodule R M) : comap f (map f p) = p ⊔ LinearMap.ker f := by
  refine' le_antisymm _ (sup_le (le_comap_map _ _) (comap_mono bot_le))
  -- ⊢ comap f (map f p) ≤ p ⊔ LinearMap.ker f
  rintro x ⟨y, hy, e⟩
  -- ⊢ x ∈ p ⊔ LinearMap.ker f
  exact mem_sup.2 ⟨y, hy, x - y, by simpa using sub_eq_zero.2 e.symm, by simp⟩
  -- 🎉 no goals
#align submodule.comap_map_eq Submodule.comap_map_eq

theorem comap_map_eq_self {f : F} {p : Submodule R M} (h : LinearMap.ker f ≤ p) :
    comap f (map f p) = p := by rw [Submodule.comap_map_eq, sup_of_le_left h]
                                -- 🎉 no goals
#align submodule.comap_map_eq_self Submodule.comap_map_eq_self

end AddCommGroup

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- There is no vector subspace between `p` and `(K ∙ x) ⊔ p`, `Wcovby` version. -/
theorem wcovby_span_singleton_sup (x : V) (p : Submodule K V) : Wcovby p ((K ∙ x) ⊔ p) := by
  refine ⟨le_sup_right, fun q hpq hqp ↦ hqp.not_le ?_⟩
  -- ⊢ span K {x} ⊔ p ≤ q
  rcases SetLike.exists_of_lt hpq with ⟨y, hyq, hyp⟩
  -- ⊢ span K {x} ⊔ p ≤ q
  obtain ⟨c, z, hz, rfl⟩ : ∃ c : K, ∃ z ∈ p, c • x + z = y := by
    simpa [mem_sup, mem_span_singleton] using hqp.le hyq
  rcases eq_or_ne c 0 with rfl | hc
  -- ⊢ span K {x} ⊔ p ≤ q
  · simp [hz] at hyp
    -- 🎉 no goals
  · have : x ∈ q
    -- ⊢ x ∈ q
    · rwa [q.add_mem_iff_left (hpq.le hz), q.smul_mem_iff hc] at hyq
      -- 🎉 no goals
    simp [hpq.le, this]
    -- 🎉 no goals

/-- There is no vector subspace between `p` and `(K ∙ x) ⊔ p`, `Covby` version. -/
theorem covby_span_singleton_sup {x : V} {p : Submodule K V} (h : x ∉ p) : Covby p ((K ∙ x) ⊔ p) :=
  ⟨by simpa, (wcovby_span_singleton_sup _ _).2⟩
      -- 🎉 no goals

end DivisionRing

end Submodule

namespace LinearMap

open Submodule Function

section AddCommGroup

variable [Semiring R] [Semiring R₂]

variable [AddCommGroup M] [AddCommGroup M₂]

variable [Module R M] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]

variable {F : Type*} [sc : SemilinearMapClass F τ₁₂ M M₂]

protected theorem map_le_map_iff (f : F) {p p'} : map f p ≤ map f p' ↔ p ≤ p' ⊔ ker f := by
  rw [map_le_iff_le_comap, Submodule.comap_map_eq]
  -- 🎉 no goals
#align linear_map.map_le_map_iff LinearMap.map_le_map_iff

theorem map_le_map_iff' {f : F} (hf : ker f = ⊥) {p p'} : map f p ≤ map f p' ↔ p ≤ p' := by
  rw [LinearMap.map_le_map_iff, hf, sup_bot_eq]
  -- 🎉 no goals
#align linear_map.map_le_map_iff' LinearMap.map_le_map_iff'

theorem map_injective {f : F} (hf : ker f = ⊥) : Injective (map f) := fun _ _ h =>
  le_antisymm ((map_le_map_iff' hf).1 (le_of_eq h)) ((map_le_map_iff' hf).1 (ge_of_eq h))
#align linear_map.map_injective LinearMap.map_injective

theorem map_eq_top_iff {f : F} (hf : range f = ⊤) {p : Submodule R M} :
    p.map f = ⊤ ↔ p ⊔ LinearMap.ker f = ⊤ := by
  simp_rw [← top_le_iff, ← hf, range_eq_map, LinearMap.map_le_map_iff]
  -- 🎉 no goals
#align linear_map.map_eq_top_iff LinearMap.map_eq_top_iff

end AddCommGroup

section

variable (R) (M) [Semiring R] [AddCommMonoid M] [Module R M]

/-- Given an element `x` of a module `M` over `R`, the natural map from
    `R` to scalar multiples of `x`.-/
@[simps!]
def toSpanSingleton (x : M) : R →ₗ[R] M :=
  LinearMap.id.smulRight x
#align linear_map.to_span_singleton LinearMap.toSpanSingleton

/-- The range of `toSpanSingleton x` is the span of `x`.-/
theorem span_singleton_eq_range (x : M) : (R ∙ x) = range (toSpanSingleton R M x) :=
  Submodule.ext fun y => by
    refine' Iff.trans _ LinearMap.mem_range.symm
    -- ⊢ y ∈ span R {x} ↔ ∃ y_1, ↑(toSpanSingleton R M x) y_1 = y
    exact mem_span_singleton
    -- 🎉 no goals
#align linear_map.span_singleton_eq_range LinearMap.span_singleton_eq_range

-- @[simp] -- Porting note: simp can prove this
theorem toSpanSingleton_one (x : M) : toSpanSingleton R M x 1 = x :=
  one_smul _ _
#align linear_map.to_span_singleton_one LinearMap.toSpanSingleton_one

@[simp]
theorem toSpanSingleton_zero : toSpanSingleton R M 0 = 0 := by
  ext
  -- ⊢ ↑(toSpanSingleton R M 0) 1 = ↑0 1
  simp
  -- 🎉 no goals
#align linear_map.to_span_singleton_zero LinearMap.toSpanSingleton_zero

end

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable [Semiring R₂] [AddCommMonoid M₂] [Module R₂ M₂]

variable {F : Type*} {σ₁₂ : R →+* R₂} [SemilinearMapClass F σ₁₂ M M₂]

/-- Two linear maps are equal on `Submodule.span s` iff they are equal on `s`. -/
theorem eqOn_span_iff {s : Set M} {f g : F} : Set.EqOn f g (span R s) ↔ Set.EqOn f g s := by
  rw [← le_eqLocus, span_le]; rfl
  -- ⊢ s ⊆ ↑(eqLocus f g) ↔ Set.EqOn (↑f) (↑g) s
                              -- 🎉 no goals

/-- If two linear maps are equal on a set `s`, then they are equal on `Submodule.span s`.

This version uses `Set.EqOn`, and the hidden argument will expand to `h : x ∈ (span R s : Set M)`.
See `LinearMap.eqOn_span` for a version that takes `h : x ∈ span R s` as an argument. -/
theorem eqOn_span' {s : Set M} {f g : F} (H : Set.EqOn f g s) :
    Set.EqOn f g (span R s : Set M) :=
  eqOn_span_iff.2 H
#align linear_map.eq_on_span' LinearMap.eqOn_span'

/-- If two linear maps are equal on a set `s`, then they are equal on `Submodule.span s`.

See also `LinearMap.eqOn_span'` for a version using `Set.EqOn`. -/
theorem eqOn_span {s : Set M} {f g : F} (H : Set.EqOn f g s) ⦃x⦄ (h : x ∈ span R s) :
    f x = g x :=
  eqOn_span' H h
#align linear_map.eq_on_span LinearMap.eqOn_span

/-- If `s` generates the whole module and linear maps `f`, `g` are equal on `s`, then they are
equal. -/
theorem ext_on {s : Set M} {f g : F} (hv : span R s = ⊤) (h : Set.EqOn f g s) : f = g :=
  FunLike.ext _ _ fun _ => eqOn_span h (eq_top_iff'.1 hv _)
#align linear_map.ext_on LinearMap.ext_on

/-- If the range of `v : ι → M` generates the whole module and linear maps `f`, `g` are equal at
each `v i`, then they are equal. -/
theorem ext_on_range {ι : Type*} {v : ι → M} {f g : F} (hv : span R (Set.range v) = ⊤)
    (h : ∀ i, f (v i) = g (v i)) : f = g :=
  ext_on hv (Set.forall_range_iff.2 h)
#align linear_map.ext_on_range LinearMap.ext_on_range

end AddCommMonoid

section NoZeroDivisors

variable (R M)
variable [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]

theorem ker_toSpanSingleton {x : M} (h : x ≠ 0) : LinearMap.ker (toSpanSingleton R M x) = ⊥ :=
  SetLike.ext fun _ => smul_eq_zero.trans <| or_iff_left_of_imp fun h' => (h h').elim
#align linear_map.ker_to_span_singleton LinearMap.ker_toSpanSingleton

end NoZeroDivisors

section Field

variable [Field K] [AddCommGroup V] [Module K V]

theorem span_singleton_sup_ker_eq_top (f : V →ₗ[K] K) {x : V} (hx : f x ≠ 0) :
    (K ∙ x) ⊔ ker f = ⊤ :=
  top_unique fun y _ =>
    Submodule.mem_sup.2
      ⟨(f y * (f x)⁻¹) • x, Submodule.mem_span_singleton.2 ⟨f y * (f x)⁻¹, rfl⟩,
        ⟨y - (f y * (f x)⁻¹) • x, by simp [hx]⟩⟩
                                     -- 🎉 no goals
#align linear_map.span_singleton_sup_ker_eq_top LinearMap.span_singleton_sup_ker_eq_top

end Field

end LinearMap

open LinearMap

namespace LinearEquiv

variable (R M)
variable [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] (x : M) (h : x ≠ 0)

/-- Given a nonzero element `x` of a torsion-free module `M` over a ring `R`, the natural
isomorphism from `R` to the span of `x` given by $r \mapsto r \cdot x$. -/
noncomputable
def toSpanNonzeroSingleton : R ≃ₗ[R] R ∙ x :=
  LinearEquiv.trans
    (LinearEquiv.ofInjective (LinearMap.toSpanSingleton R M x)
      (ker_eq_bot.1 <| ker_toSpanSingleton R M h))
    (LinearEquiv.ofEq (range $ toSpanSingleton R M x) (R ∙ x) (span_singleton_eq_range R M x).symm)
#align linear_equiv.to_span_nonzero_singleton LinearEquiv.toSpanNonzeroSingleton

theorem toSpanNonzeroSingleton_one :
    LinearEquiv.toSpanNonzeroSingleton R M x h 1 =
      (⟨x, Submodule.mem_span_singleton_self x⟩ : R ∙ x) := by
  apply SetLike.coe_eq_coe.mp
  -- ⊢ ↑(↑(toSpanNonzeroSingleton R M x h) 1) = ↑{ val := x, property := (_ : x ∈ S …
  have : ↑(toSpanNonzeroSingleton R M x h 1) = toSpanSingleton R M x 1 := rfl
  -- ⊢ ↑(↑(toSpanNonzeroSingleton R M x h) 1) = ↑{ val := x, property := (_ : x ∈ S …
  rw [this, toSpanSingleton_one, Submodule.coe_mk]
  -- 🎉 no goals
#align linear_equiv.to_span_nonzero_singleton_one LinearEquiv.toSpanNonzeroSingleton_one

/-- Given a nonzero element `x` of a torsion-free module `M` over a ring `R`, the natural
isomorphism from the span of `x` to `R` given by $r \cdot x \mapsto r$. -/
noncomputable
abbrev coord : (R ∙ x) ≃ₗ[R] R :=
  (toSpanNonzeroSingleton R M x h).symm
#align linear_equiv.coord LinearEquiv.coord

theorem coord_self : (coord R M x h) (⟨x, Submodule.mem_span_singleton_self x⟩ : R ∙ x) = 1 := by
  rw [← toSpanNonzeroSingleton_one R M x h, LinearEquiv.symm_apply_apply]
  -- 🎉 no goals
#align linear_equiv.coord_self LinearEquiv.coord_self

theorem coord_apply_smul (y : Submodule.span R ({x} : Set M)) : coord R M x h y • x = y :=
  Subtype.ext_iff.1 <| (toSpanNonzeroSingleton R M x h).apply_symm_apply _
#align linear_equiv.coord_apply_smul LinearEquiv.coord_apply_smul

end LinearEquiv
