/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.Single
import Mathlib.Tactic.FastInstance

/-!
# Additive monoid structure on `ι →₀ M`
-/

assert_not_exists MonoidWithZero

open Finset

noncomputable section

variable {ι F M N O G H : Type*}

namespace Finsupp
section Zero
variable [Zero M] [Zero N]

lemma apply_single [FunLike F M N] [ZeroHomClass F M N] (e : F) (i : ι) (m : M) (b : ι) :
    e (single i m b) = single i (e m) b := apply_single' e (map_zero e) i m b

end Zero

section AddZeroClass
variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

instance instAdd : Add (ι →₀ M) where add := zipWith (· + ·) (add_zero 0)

@[simp, norm_cast] lemma coe_add (f g : ι →₀ M) : ⇑(f + g) = f + g := rfl

lemma add_apply (g₁ g₂ : ι →₀ M) (a : ι) : (g₁ + g₂) a = g₁ a + g₂ a := rfl

lemma support_add [DecidableEq ι] : (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support := support_zipWith

lemma support_add_eq [DecidableEq ι] (h : Disjoint g₁.support g₂.support) :
    (g₁ + g₂).support = g₁.support ∪ g₂.support :=
  le_antisymm support_zipWith fun a ha => by
    cases (Finset.mem_union_of_disjoint h).mp ha <;> simp_all

instance instAddZeroClass : AddZeroClass (ι →₀ M) :=
  fast_instance% DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

instance instIsLeftCancelAdd [IsLeftCancelAdd M] : IsLeftCancelAdd (ι →₀ M) where
  add_left_cancel _ _ _ h := ext fun x => add_left_cancel <| DFunLike.congr_fun h x

/-- When ι is finite and M is an AddMonoid,
  then Finsupp.equivFunOnFinite gives an AddEquiv -/
noncomputable def addEquivFunOnFinite {ι : Type*} [Finite ι] :
    (ι →₀ M) ≃+ (ι → M) where
  __ := Finsupp.equivFunOnFinite
  map_add' _ _ := rfl

/-- AddEquiv between (ι →₀ M) and M, when ι has a unique element -/
noncomputable def _root_.AddEquiv.finsuppUnique {ι : Type*} [Unique ι] :
    (ι →₀ M) ≃+ M where
  __ := Equiv.finsuppUnique
  map_add' _ _ := rfl

@[simp]
lemma _root_.AddEquiv.finsuppUnique_apply {ι : Type*} [Unique ι] (v : ι →₀ M) :
    AddEquiv.finsuppUnique v = Equiv.finsuppUnique v := rfl

instance instIsRightCancelAdd [IsRightCancelAdd M] : IsRightCancelAdd (ι →₀ M) where
  add_right_cancel _ _ _ h := ext fun x => add_right_cancel <| DFunLike.congr_fun h x

instance instIsCancelAdd [IsCancelAdd M] : IsCancelAdd (ι →₀ M) where

/-- Evaluation of a function `f : ι →₀ M` at a point as an additive monoid homomorphism.

See `Finsupp.lapply` in `Mathlib/LinearAlgebra/Finsupp/Defs.lean` for the stronger version as a
linear map. -/
@[simps apply]
def applyAddHom (a : ι) : (ι →₀ M) →+ M where
  toFun g := g a
  map_zero' := zero_apply
  map_add' _ _ := add_apply _ _ _

/-- Coercion from a `Finsupp` to a function type is an `AddMonoidHom`. -/
@[simps]
noncomputable def coeFnAddHom : (ι →₀ M) →+ ι → M where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

lemma mapRange_add {hf : f 0 = 0} (hf' : ∀ x y, f (x + y) = f x + f y) (v₁ v₂ : ι →₀ M) :
    mapRange f hf (v₁ + v₂) = mapRange f hf v₁ + mapRange f hf v₂ :=
  ext fun _ => by simp only [hf', add_apply, mapRange_apply]

lemma mapRange_add' [FunLike F M N] [AddMonoidHomClass F M N] {f : F} (g₁ g₂ : ι →₀ M) :
    mapRange f (map_zero f) (g₁ + g₂) = mapRange f (map_zero f) g₁ + mapRange f (map_zero f) g₂ :=
  mapRange_add (map_add f) g₁ g₂

/-- Bundle `Finsupp.embDomain f` as an additive map from `ι →₀ M` to `F →₀ M`. -/
@[simps]
def embDomain.addMonoidHom (f : ι ↪ F) : (ι →₀ M) →+ F →₀ M where
  toFun v := embDomain f v
  map_zero' := by simp
  map_add' v w := by
    ext b
    by_cases h : b ∈ Set.range f
    · rcases h with ⟨a, rfl⟩
      simp
    · simp only [coe_add, Pi.add_apply, embDomain_notin_range _ _ _ h, add_zero]

@[simp]
lemma embDomain_add (f : ι ↪ F) (v w : ι →₀ M) :
    embDomain f (v + w) = embDomain f v + embDomain f w := (embDomain.addMonoidHom f).map_add v w

@[simp]
lemma single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) = single a b₁ + single a b₂ :=
  (zipWith_single_single _ _ _ _ _).symm

lemma single_add_apply (a : ι) (m₁ m₂ : M) (b : ι) :
    single a (m₁ + m₂) b = single a m₁ b + single a m₂ b := by simp

lemma support_single_add {a : ι} {b : M} {f : ι →₀ M} (ha : a ∉ f.support) (hb : b ≠ 0) :
    support (single a b + f) = cons a f.support ha := by
  classical
  have H := support_single_ne_zero a hb
  rw [support_add_eq, H, cons_eq_insert, insert_eq]
  rwa [H, disjoint_singleton_left]

lemma support_add_single {a : ι} {b : M} {f : ι →₀ M} (ha : a ∉ f.support) (hb : b ≠ 0) :
    support (f + single a b) = cons a f.support ha := by
  classical
  have H := support_single_ne_zero a hb
  rw [support_add_eq, H, union_comm, cons_eq_insert, insert_eq]
  rwa [H, disjoint_singleton_right]

lemma _root_.AddEquiv.finsuppUnique_symm {M : Type*} [AddZeroClass M] (d : M) :
    AddEquiv.finsuppUnique.symm d = single () d := by
  rw [Finsupp.unique_single (AddEquiv.finsuppUnique.symm d), Finsupp.unique_single_eq_iff]
  simp [AddEquiv.finsuppUnique]

theorem addCommute_iff_inter [DecidableEq ι] {f g : ι →₀ M} :
    AddCommute f g ↔ ∀ x ∈ f.support ∩ g.support, AddCommute (f x) (g x) where
  mp h := fun x _ ↦ Finsupp.ext_iff.1 h x
  mpr h := by
    ext x
    by_cases hf : x ∈ f.support
    · by_cases hg : x ∈ g.support
      · exact h _ (mem_inter_of_mem hf hg)
      · simp_all
    · simp_all

theorem addCommute_of_disjoint {f g : ι →₀ M} (h : Disjoint f.support g.support) :
    AddCommute f g := by
  classical simp_all [addCommute_iff_inter, Finset.disjoint_iff_inter_eq_empty]

/-- `Finsupp.single` as an `AddMonoidHom`.

See `Finsupp.lsingle` in `Mathlib/LinearAlgebra/Finsupp/Defs.lean` for the stronger version as a
linear map. -/
@[simps]
def singleAddHom (a : ι) : M →+ ι →₀ M where
  toFun := single a
  map_zero' := single_zero a
  map_add' := single_add a

lemma update_eq_single_add_erase (f : ι →₀ M) (a : ι) (b : M) :
    f.update a b = single a b + f.erase a := by
  classical
    ext j
    rcases eq_or_ne j a with (rfl | h)
    · simp
    · simp [h, erase_ne]

lemma update_eq_erase_add_single (f : ι →₀ M) (a : ι) (b : M) :
    f.update a b = f.erase a + single a b := by
  classical
    ext j
    rcases eq_or_ne j a with (rfl | h)
    · simp
    · simp [h, erase_ne]

lemma update_eq_single_add {f : ι →₀ M} {a : ι} (h : f a = 0) (b : M) :
    f.update a b = single a b + f := by
  rw [update_eq_single_add_erase, erase_of_notMem_support (by simpa)]

lemma update_eq_add_single {f : ι →₀ M} {a : ι} (h : f a = 0) (b : M) :
    f.update a b = f + single a b := by
  rw [update_eq_erase_add_single, erase_of_notMem_support (by simpa)]

lemma single_add_erase (a : ι) (f : ι →₀ M) : single a (f a) + f.erase a = f := by
  rw [← update_eq_single_add_erase, update_self]

lemma erase_add_single (a : ι) (f : ι →₀ M) : f.erase a + single a (f a) = f := by
  rw [← update_eq_erase_add_single, update_self]

@[simp]
lemma erase_add (a : ι) (f f' : ι →₀ M) : erase a (f + f') = erase a f + erase a f' := by
  ext s; by_cases hs : s = a
  · rw [hs, add_apply, erase_same, erase_same, erase_same, add_zero]
  rw [add_apply, erase_ne hs, erase_ne hs, erase_ne hs, add_apply]

/-- `Finsupp.erase` as an `AddMonoidHom`. -/
@[simps]
def eraseAddHom (a : ι) : (ι →₀ M) →+ ι →₀ M where
  toFun := erase a
  map_zero' := erase_zero a
  map_add' := erase_add a

@[elab_as_elim]
protected lemma induction {motive : (ι →₀ M) → Prop} (f : ι →₀ M) (zero : motive 0)
    (single_add : ∀ (a b) (f : ι →₀ M),
      a ∉ f.support → b ≠ 0 → motive f → motive (single a b + f)) : motive f :=
  suffices ∀ (s) (f : ι →₀ M), f.support = s → motive f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf => by
    suffices motive (single a (f a) + f.erase a) by rwa [single_add_erase] at this
    classical
      apply single_add
      · rw [support_erase, mem_erase]
        exact fun H => H.1 rfl
      · rw [← mem_support_iff, hf]
        exact mem_cons_self _ _
      · apply ih _ _
        rw [support_erase, hf, Finset.erase_cons]

@[elab_as_elim]
lemma induction₂ {motive : (ι →₀ M) → Prop} (f : ι →₀ M) (zero : motive 0)
    (add_single : ∀ (a b) (f : ι →₀ M),
      a ∉ f.support → b ≠ 0 → motive f → motive (f + single a b)) : motive f := by
  classical
  refine f.induction zero ?_
  convert add_single using 7
  apply (addCommute_of_disjoint _).eq
  simp_all [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem, single_apply]

@[elab_as_elim]
lemma induction_linear {motive : (ι →₀ M) → Prop} (f : ι →₀ M) (zero : motive 0)
    (add : ∀ f g : ι →₀ M, motive f → motive g → motive (f + g))
    (single : ∀ a b, motive (single a b)) : motive f :=
  induction₂ f zero fun _a _b _f _ _ w => add _ _ w (single _ _)

section LinearOrder

variable [LinearOrder ι] {p : (ι →₀ M) → Prop}

/-- A finitely supported function can be built by adding up `single a b` for increasing `a`.

The lemma `induction_on_max₂` swaps the argument order in the sum. -/
lemma induction_on_max (f : ι →₀ M) (zero : p 0)
    (single_add : ∀ a b (f : ι →₀ M), (∀ c ∈ f.support, c < a) → b ≠ 0 → p f → p (single a b + f)) :
    p f := by
  suffices ∀ (s) (f : ι →₀ M), f.support = s → p f from this _ _ rfl
  refine fun s => s.induction_on_max (fun f h => ?_) (fun a s hm hf f hs => ?_)
  · rwa [support_eq_empty.1 h]
  · have hs' : (erase a f).support = s := by
      rw [support_erase, hs, erase_insert (fun ha => (hm a ha).false)]
    rw [← single_add_erase a f]
    refine single_add _ _ _ (fun c hc => hm _ <| hs'.symm ▸ hc) ?_ (hf _ hs')
    rw [← mem_support_iff, hs]
    exact mem_insert_self a s

/-- A finitely supported function can be built by adding up `single a b` for decreasing `a`.

The lemma `induction_on_min₂` swaps the argument order in the sum. -/
lemma induction_on_min (f : ι →₀ M) (zero : p 0)
    (single_add : ∀ a b (f : ι →₀ M), (∀ c ∈ f.support, a < c) → b ≠ 0 → p f → p (single a b + f)) :
    p f :=
  induction_on_max (ι := ιᵒᵈ) f zero single_add

/-- A finitely supported function can be built by adding up `single a b` for increasing `a`.

The lemma `induction_on_max` swaps the argument order in the sum. -/
lemma induction_on_max₂ (f : ι →₀ M) (zero : p 0)
    (add_single : ∀ a b (f : ι →₀ M), (∀ c ∈ f.support, c < a) → b ≠ 0 → p f → p (f + single a b)) :
    p f := by
  classical
  refine f.induction_on_max zero ?_
  convert add_single using 7 with _ _ _ H
  have := fun c hc ↦ (H c hc).ne
  apply (addCommute_of_disjoint _).eq
  simp_all [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem, single_apply, not_imp_not]

/-- A finitely supported function can be built by adding up `single a b` for decreasing `a`.

The lemma `induction_on_min` swaps the argument order in the sum. -/
lemma induction_on_min₂ (f : ι →₀ M) (h0 : p 0)
    (ha : ∀ (a b) (f : ι →₀ M), (∀ c ∈ f.support, a < c) → b ≠ 0 → p f → p (f + single a b)) :
    p f :=
  induction_on_max₂ (ι := ιᵒᵈ) f h0 ha

end LinearOrder

end AddZeroClass

section AddMonoid
variable [AddMonoid M]

/-- Note the general `SMul` instance for `Finsupp` doesn't apply as `ℕ` is not distributive
unless `F i`'s addition is commutative. -/
instance instNatSMul : SMul ℕ (ι →₀ M) where smul n v := v.mapRange (n • ·) (nsmul_zero _)

@[simp, norm_cast] lemma coe_nsmul (n : ℕ) (f : ι →₀ M) : ⇑(n • f) = n • ⇑f := rfl

lemma nsmul_apply (n : ℕ) (f : ι →₀ M) (x : ι) : (n • f) x = n • f x := rfl

instance instAddMonoid : AddMonoid (ι →₀ M) :=
  fast_instance% DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

instance instIsAddTorsionFree [IsAddTorsionFree M] : IsAddTorsionFree (ι →₀ M) :=
  DFunLike.coe_injective.isAddTorsionFree coeFnAddHom

end AddMonoid

section AddCommMonoid
variable [AddCommMonoid M]

instance instAddCommMonoid : AddCommMonoid (ι →₀ M) :=
  fast_instance% DFunLike.coe_injective.addCommMonoid
    DFunLike.coe coe_zero coe_add (fun _ _ => rfl)

lemma single_add_single_eq_single_add_single {k l m n : ι} {u v : M} (hu : u ≠ 0) (hv : v ≠ 0) :
    single k u + single l v = single m u + single n v ↔
      (k = m ∧ l = n) ∨ (u = v ∧ k = n ∧ l = m) ∨ (u + v = 0 ∧ k = l ∧ m = n) := by
  classical
    simp_rw [DFunLike.ext_iff, coe_add, single_eq_pi_single, ← funext_iff]
    exact Pi.single_add_single_eq_single_add_single hu hv

end AddCommMonoid

instance instNeg [NegZeroClass G] : Neg (ι →₀ G) where neg := mapRange Neg.neg neg_zero

@[simp, norm_cast] lemma coe_neg [NegZeroClass G] (g : ι →₀ G) : ⇑(-g) = -g := rfl

lemma neg_apply [NegZeroClass G] (g : ι →₀ G) (a : ι) : (-g) a = -g a :=
  rfl

lemma mapRange_neg [NegZeroClass G] [NegZeroClass H] {f : G → H} {hf : f 0 = 0}
    (hf' : ∀ x, f (-x) = -f x) (v : ι →₀ G) : mapRange f hf (-v) = -mapRange f hf v :=
  ext fun _ => by simp only [hf', neg_apply, mapRange_apply]

instance instSub [SubNegZeroMonoid G] : Sub (ι →₀ G) :=
  ⟨zipWith Sub.sub (sub_zero _)⟩

@[simp, norm_cast] lemma coe_sub [SubNegZeroMonoid G] (g₁ g₂ : ι →₀ G) : ⇑(g₁ - g₂) = g₁ - g₂ := rfl

lemma sub_apply [SubNegZeroMonoid G] (g₁ g₂ : ι →₀ G) (a : ι) : (g₁ - g₂) a = g₁ a - g₂ a := rfl

lemma mapRange_sub [SubNegZeroMonoid G] [SubNegZeroMonoid H] {f : G → H} {hf : f 0 = 0}
    (hf' : ∀ x y, f (x - y) = f x - f y) (v₁ v₂ : ι →₀ G) :
    mapRange f hf (v₁ - v₂) = mapRange f hf v₁ - mapRange f hf v₂ :=
  ext fun _ => by simp only [hf', sub_apply, mapRange_apply]

section AddGroup
variable [AddGroup G] {p : ι → Prop} {v v' : ι →₀ G}

lemma mapRange_neg' [SubtractionMonoid H] [FunLike F G H] [AddMonoidHomClass F G H]
    {f : F} (v : ι →₀ G) :
    mapRange f (map_zero f) (-v) = -mapRange f (map_zero f) v :=
  mapRange_neg (map_neg f) v

lemma mapRange_sub' [SubtractionMonoid H] [FunLike F G H] [AddMonoidHomClass F G H]
    {f : F} (v₁ v₂ : ι →₀ G) :
    mapRange f (map_zero f) (v₁ - v₂) = mapRange f (map_zero f) v₁ - mapRange f (map_zero f) v₂ :=
  mapRange_sub (map_sub f) v₁ v₂

/-- Note the general `SMul` instance for `Finsupp` doesn't apply as `ℤ` is not distributive
unless `F i`'s addition is commutative. -/
instance instIntSMul : SMul ℤ (ι →₀ G) :=
  ⟨fun n v => v.mapRange (n • ·) (zsmul_zero _)⟩

instance instAddGroup : AddGroup (ι →₀ G) :=
  fast_instance% DFunLike.coe_injective.addGroup DFunLike.coe coe_zero coe_add coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

@[simp]
lemma support_neg (f : ι →₀ G) : support (-f) = support f :=
  Finset.Subset.antisymm support_mapRange
    (calc
      support f = support (- -f) := congr_arg support (neg_neg _).symm
      _ ⊆ support (-f) := support_mapRange
      )

lemma support_sub [DecidableEq ι] {f g : ι →₀ G} : support (f - g) ⊆ support f ∪ support g := by
  rw [sub_eq_add_neg, ← support_neg g]
  exact support_add

lemma erase_eq_sub_single (f : ι →₀ G) (a : ι) : f.erase a = f - single a (f a) := by
  ext a'
  rcases eq_or_ne a' a with (rfl | h)
  · simp
  · simp [h]

lemma update_eq_sub_add_single (f : ι →₀ G) (a : ι) (b : G) :
    f.update a b = f - single a (f a) + single a b := by
  rw [update_eq_erase_add_single, erase_eq_sub_single]

@[simp]
lemma single_neg (a : ι) (b : G) : single a (-b) = -single a b :=
  (singleAddHom a : G →+ _).map_neg b

@[simp]
lemma single_sub (a : ι) (b₁ b₂ : G) : single a (b₁ - b₂) = single a b₁ - single a b₂ :=
  (singleAddHom a : G →+ _).map_sub b₁ b₂

@[simp]
lemma erase_neg (a : ι) (f : ι →₀ G) : erase a (-f) = -erase a f :=
  (eraseAddHom a : (_ →₀ G) →+ _).map_neg f

@[simp]
lemma erase_sub (a : ι) (f₁ f₂ : ι →₀ G) : erase a (f₁ - f₂) = erase a f₁ - erase a f₂ :=
  (eraseAddHom a : (_ →₀ G) →+ _).map_sub f₁ f₂

end AddGroup

instance instAddCommGroup [AddCommGroup G] : AddCommGroup (ι →₀ G) :=
  fast_instance% DFunLike.coe_injective.addCommGroup DFunLike.coe coe_zero coe_add coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

end Finsupp
