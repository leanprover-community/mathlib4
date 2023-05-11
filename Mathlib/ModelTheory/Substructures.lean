/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module model_theory.substructures
! leanprover-community/mathlib commit 0602c59878ff3d5f71dea69c2d32ccf2e93e5398
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Closure
import Mathbin.ModelTheory.Semantics
import Mathbin.ModelTheory.Encoding

/-!
# First-Order Substructures
This file defines substructures of first-order structures in a similar manner to the various
substructures appearing in the algebra library.

## Main Definitions
* A `first_order.language.substructure` is defined so that `L.substructure M` is the type of all
substructures of the `L`-structure `M`.
* `first_order.language.substructure.closure` is defined so that if `s : set M`, `closure L s` is
the least substructure of `M` containing `s`.
* `first_order.language.substructure.comap` is defined so that `s.comap f` is the preimage of the
substructure `s` under the homomorphism `f`, as a substructure.
* `first_order.language.substructure.map` is defined so that `s.map f` is the image of the
substructure `s` under the homomorphism `f`, as a substructure.
* `first_order.language.hom.range` is defined so that `f.map` is the range of the
the homomorphism `f`, as a substructure.
* `first_order.language.hom.dom_restrict` and `first_order.language.hom.cod_restrict` restrict
the domain and codomain respectively of first-order homomorphisms to substructures.
* `first_order.language.embedding.dom_restrict` and `first_order.language.embedding.cod_restrict`
restrict the domain and codomain respectively of first-order embeddings to substructures.
* `first_order.language.substructure.inclusion` is the inclusion embedding between substructures.

## Main Results
* `L.substructure M` forms a `complete_lattice`.

-/


universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} {N P : Type _}

variable [L.Structure M] [L.Structure N] [L.Structure P]

open FirstOrder Cardinal

open Structure Cardinal

section ClosedUnder

open Set

variable {n : ℕ} (f : L.Functions n) (s : Set M)

/-- Indicates that a set in a given structure is a closed under a function symbol. -/
def ClosedUnder : Prop :=
  ∀ x : Fin n → M, (∀ i : Fin n, x i ∈ s) → funMap f x ∈ s
#align first_order.language.closed_under FirstOrder.Language.ClosedUnder

variable (L)

@[simp]
theorem closedUnder_univ : ClosedUnder f (univ : Set M) := fun _ _ => mem_univ _
#align first_order.language.closed_under_univ FirstOrder.Language.closedUnder_univ

variable {L f s} {t : Set M}

namespace ClosedUnder

theorem inter (hs : ClosedUnder f s) (ht : ClosedUnder f t) : ClosedUnder f (s ∩ t) := fun x h =>
  mem_inter (hs x fun i => mem_of_mem_inter_left (h i)) (ht x fun i => mem_of_mem_inter_right (h i))
#align first_order.language.closed_under.inter FirstOrder.Language.ClosedUnder.inter

theorem inf (hs : ClosedUnder f s) (ht : ClosedUnder f t) : ClosedUnder f (s ⊓ t) :=
  hs.inter ht
#align first_order.language.closed_under.inf FirstOrder.Language.ClosedUnder.inf

variable {S : Set (Set M)}

theorem infₛ (hS : ∀ s, s ∈ S → ClosedUnder f s) : ClosedUnder f (infₛ S) := fun x h s hs =>
  hS s hs x fun i => h i s hs
#align first_order.language.closed_under.Inf FirstOrder.Language.ClosedUnder.infₛ

end ClosedUnder

end ClosedUnder

variable (L) (M)

/-- A substructure of a structure `M` is a set closed under application of function symbols. -/
structure Substructure where
  carrier : Set M
  fun_mem : ∀ {n}, ∀ f : L.Functions n, ClosedUnder f carrier
#align first_order.language.substructure FirstOrder.Language.Substructure

variable {L} {M}

namespace Substructure

instance : SetLike (L.Substructure M) M :=
  ⟨Substructure.carrier, fun p q h => by cases p <;> cases q <;> congr ⟩

/-- See Note [custom simps projection] -/
def Simps.coe (S : L.Substructure M) : Set M :=
  S
#align first_order.language.substructure.simps.coe FirstOrder.Language.Substructure.Simps.coe

initialize_simps_projections Substructure (carrier → coe)

@[simp]
theorem mem_carrier {s : L.Substructure M} {x : M} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align first_order.language.substructure.mem_carrier FirstOrder.Language.Substructure.mem_carrier

/-- Two substructures are equal if they have the same elements. -/
@[ext]
theorem ext {S T : L.Substructure M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align first_order.language.substructure.ext FirstOrder.Language.Substructure.ext

/-- Copy a substructure replacing `carrier` with a set that is equal to it. -/
protected def copy (S : L.Substructure M) (s : Set M) (hs : s = S) : L.Substructure M
    where
  carrier := s
  fun_mem n f := hs.symm ▸ S.fun_mem f
#align first_order.language.substructure.copy FirstOrder.Language.Substructure.copy

end Substructure

variable {S : L.Substructure M}

theorem Term.realize_mem {α : Type _} (t : L.term α) (xs : α → M) (h : ∀ a, xs a ∈ S) :
    t.realize xs ∈ S := by
  induction' t with a n f ts ih
  · exact h a
  · exact substructure.fun_mem _ _ _ ih
#align first_order.language.term.realize_mem FirstOrder.Language.Term.realize_mem

namespace Substructure

@[simp]
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl
#align first_order.language.substructure.coe_copy FirstOrder.Language.Substructure.coe_copy

theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align first_order.language.substructure.copy_eq FirstOrder.Language.Substructure.copy_eq

theorem constants_mem (c : L.Constants) : ↑c ∈ S :=
  mem_carrier.2 (S.fun_mem c _ Fin.elim0)
#align first_order.language.substructure.constants_mem FirstOrder.Language.Substructure.constants_mem

/-- The substructure `M` of the structure `M`. -/
instance : Top (L.Substructure M) :=
  ⟨{  carrier := Set.univ
      fun_mem := fun n f x h => Set.mem_univ _ }⟩

instance : Inhabited (L.Substructure M) :=
  ⟨⊤⟩

@[simp]
theorem mem_top (x : M) : x ∈ (⊤ : L.Substructure M) :=
  Set.mem_univ x
#align first_order.language.substructure.mem_top FirstOrder.Language.Substructure.mem_top

@[simp]
theorem coe_top : ((⊤ : L.Substructure M) : Set M) = Set.univ :=
  rfl
#align first_order.language.substructure.coe_top FirstOrder.Language.Substructure.coe_top

/-- The inf of two substructures is their intersection. -/
instance : Inf (L.Substructure M) :=
  ⟨fun S₁ S₂ =>
    { carrier := S₁ ∩ S₂
      fun_mem := fun n f => (S₁.fun_mem f).inf (S₂.fun_mem f) }⟩

@[simp]
theorem coe_inf (p p' : L.Substructure M) : ((p ⊓ p' : L.Substructure M) : Set M) = p ∩ p' :=
  rfl
#align first_order.language.substructure.coe_inf FirstOrder.Language.Substructure.coe_inf

@[simp]
theorem mem_inf {p p' : L.Substructure M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
#align first_order.language.substructure.mem_inf FirstOrder.Language.Substructure.mem_inf

instance : InfSet (L.Substructure M) :=
  ⟨fun s =>
    { carrier := ⋂ t ∈ s, ↑t
      fun_mem := fun n f =>
        ClosedUnder.infₛ
          (by
            rintro _ ⟨t, rfl⟩
            by_cases h : t ∈ s
            · simpa [h] using t.fun_mem f
            · simp [h]) }⟩

@[simp, norm_cast]
theorem coe_infₛ (S : Set (L.Substructure M)) :
    ((infₛ S : L.Substructure M) : Set M) = ⋂ s ∈ S, ↑s :=
  rfl
#align first_order.language.substructure.coe_Inf FirstOrder.Language.Substructure.coe_infₛ

theorem mem_infₛ {S : Set (L.Substructure M)} {x : M} : x ∈ infₛ S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_interᵢ₂
#align first_order.language.substructure.mem_Inf FirstOrder.Language.Substructure.mem_infₛ

theorem mem_infᵢ {ι : Sort _} {S : ι → L.Substructure M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i :=
  by simp only [infᵢ, mem_Inf, Set.forall_range_iff]
#align first_order.language.substructure.mem_infi FirstOrder.Language.Substructure.mem_infᵢ

@[simp, norm_cast]
theorem coe_infᵢ {ι : Sort _} {S : ι → L.Substructure M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [infᵢ, coe_Inf, Set.binterᵢ_range]
#align first_order.language.substructure.coe_infi FirstOrder.Language.Substructure.coe_infᵢ

/-- Substructures of a structure form a complete lattice. -/
instance : CompleteLattice (L.Substructure M) :=
  {
    completeLatticeOfInf (L.Substructure M) fun s =>
      IsGLB.of_image (fun S T => show (S : Set M) ≤ T ↔ S ≤ T from SetLike.coe_subset_coe)
        isGLB_binfᵢ with
    le := (· ≤ ·)
    lt := (· < ·)
    top := ⊤
    le_top := fun S x hx => mem_top x
    inf := (· ⊓ ·)
    infₛ := InfSet.infₛ
    le_inf := fun a b c ha hb x hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun a b x => And.left
    inf_le_right := fun a b x => And.right }

variable (L)

/-- The `L.substructure` generated by a set. -/
def closure : LowerAdjoint (coe : L.Substructure M → Set M) :=
  ⟨fun s => infₛ { S | s ⊆ S }, fun s S =>
    ⟨Set.Subset.trans fun x hx => mem_infₛ.2 fun S hS => hS hx, fun h => infₛ_le h⟩⟩
#align first_order.language.substructure.closure FirstOrder.Language.Substructure.closure

variable {L} {s : Set M}

theorem mem_closure {x : M} : x ∈ closure L s ↔ ∀ S : L.Substructure M, s ⊆ S → x ∈ S :=
  mem_infₛ
#align first_order.language.substructure.mem_closure FirstOrder.Language.Substructure.mem_closure

/-- The substructure generated by a set includes the set. -/
@[simp]
theorem subset_closure : s ⊆ closure L s :=
  (closure L).le_closure s
#align first_order.language.substructure.subset_closure FirstOrder.Language.Substructure.subset_closure

theorem not_mem_of_not_mem_closure {P : M} (hP : P ∉ closure L s) : P ∉ s := fun h =>
  hP (subset_closure h)
#align first_order.language.substructure.not_mem_of_not_mem_closure FirstOrder.Language.Substructure.not_mem_of_not_mem_closure

@[simp]
theorem closed (S : L.Substructure M) : (closure L).closed (S : Set M) :=
  congr rfl ((closure L).eq_of_le Set.Subset.rfl fun x xS => mem_closure.2 fun T hT => hT xS)
#align first_order.language.substructure.closed FirstOrder.Language.Substructure.closed

open Set

/-- A substructure `S` includes `closure L s` if and only if it includes `s`. -/
@[simp]
theorem closure_le : closure L s ≤ S ↔ s ⊆ S :=
  (closure L).closure_le_closed_iff_le s S.closed
#align first_order.language.substructure.closure_le FirstOrder.Language.Substructure.closure_le

/-- Substructure closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure L s ≤ closure L t`. -/
theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : closure L s ≤ closure L t :=
  (closure L).Monotone h
#align first_order.language.substructure.closure_mono FirstOrder.Language.Substructure.closure_mono

theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure L s) : closure L s = S :=
  (closure L).eq_of_le h₁ h₂
#align first_order.language.substructure.closure_eq_of_le FirstOrder.Language.Substructure.closure_eq_of_le

theorem coe_closure_eq_range_term_realize :
    (closure L s : Set M) = range (@Term.realize L _ _ _ (coe : s → M)) :=
  by
  let S : L.substructure M := ⟨range (term.realize coe), fun n f x hx => _⟩
  · change _ = (S : Set M)
    rw [← SetLike.ext'_iff]
    refine' closure_eq_of_le (fun x hx => ⟨var ⟨x, hx⟩, rfl⟩) (le_infₛ fun S' hS' => _)
    · rintro _ ⟨t, rfl⟩
      exact t.realize_mem _ fun i => hS' i.2
  · simp only [mem_range] at *
    refine' ⟨func f fun i => Classical.choose (hx i), _⟩
    simp only [term.realize, fun i => Classical.choose_spec (hx i)]
#align first_order.language.substructure.coe_closure_eq_range_term_realize FirstOrder.Language.Substructure.coe_closure_eq_range_term_realize

instance small_closure [Small.{u} s] : Small.{u} (closure L s) :=
  by
  rw [← SetLike.coe_sort_coe, substructure.coe_closure_eq_range_term_realize]
  exact small_range _
#align first_order.language.substructure.small_closure FirstOrder.Language.Substructure.small_closure

theorem mem_closure_iff_exists_term {x : M} :
    x ∈ closure L s ↔ ∃ t : L.term s, t.realize (coe : s → M) = x := by
  rw [← SetLike.mem_coe, coe_closure_eq_range_term_realize, mem_range]
#align first_order.language.substructure.mem_closure_iff_exists_term FirstOrder.Language.Substructure.mem_closure_iff_exists_term

theorem lift_card_closure_le_card_term : Cardinal.lift.{max u w} (#closure L s) ≤ (#L.term s) :=
  by
  rw [← SetLike.coe_sort_coe, coe_closure_eq_range_term_realize]
  rw [← Cardinal.lift_id'.{w, max u w} (#L.term s)]
  exact Cardinal.mk_range_le_lift
#align first_order.language.substructure.lift_card_closure_le_card_term FirstOrder.Language.Substructure.lift_card_closure_le_card_term

theorem lift_card_closure_le :
    Cardinal.lift.{u, w} (#closure L s) ≤
      max ℵ₀ (Cardinal.lift.{u, w} (#s) + Cardinal.lift.{w, u} (#Σi, L.Functions i)) :=
  by
  rw [← lift_umax]
  refine' lift_card_closure_le_card_term.trans (term.card_le.trans _)
  rw [mk_sum, lift_umax]
#align first_order.language.substructure.lift_card_closure_le FirstOrder.Language.Substructure.lift_card_closure_le

variable (L)

theorem Set.Countable.substructure_closure [Countable (Σl, L.Functions l)] (h : s.Countable) :
    Countable.{w + 1} (closure L s) :=
  by
  haveI : Countable s := h.to_subtype
  rw [← mk_le_aleph_0_iff, ← lift_le_aleph_0]
  exact lift_card_closure_le_card_term.trans mk_le_aleph_0
#align set.countable.substructure_closure Set.Countable.substructure_closure

variable {L} (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under function symbols, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_elim]
theorem closure_induction {p : M → Prop} {x} (h : x ∈ closure L s) (Hs : ∀ x ∈ s, p x)
    (Hfun : ∀ {n : ℕ} (f : L.Functions n), ClosedUnder f (setOf p)) : p x :=
  (@closure_le L M _ ⟨setOf p, fun n => Hfun⟩ _).2 Hs h
#align first_order.language.substructure.closure_induction FirstOrder.Language.Substructure.closure_induction

/-- If `s` is a dense set in a structure `M`, `substructure.closure L s = ⊤`, then in order to prove
that some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify
that `p` is preserved under function symbols. -/
@[elab_as_elim]
theorem dense_induction {p : M → Prop} (x : M) {s : Set M} (hs : closure L s = ⊤)
    (Hs : ∀ x ∈ s, p x) (Hfun : ∀ {n : ℕ} (f : L.Functions n), ClosedUnder f (setOf p)) : p x :=
  by
  have : ∀ x ∈ closure L s, p x := fun x hx => closure_induction hx Hs fun n => Hfun
  simpa [hs] using this x
#align first_order.language.substructure.dense_induction FirstOrder.Language.Substructure.dense_induction

variable (L) (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure L M _) coe
    where
  choice s _ := closure L s
  gc := (closure L).gc
  le_l_u s := subset_closure
  choice_eq s h := rfl
#align first_order.language.substructure.gi FirstOrder.Language.Substructure.gi

variable {L} {M}

/-- Closure of a substructure `S` equals `S`. -/
@[simp]
theorem closure_eq : closure L (S : Set M) = S :=
  (Substructure.gi L M).l_u_eq S
#align first_order.language.substructure.closure_eq FirstOrder.Language.Substructure.closure_eq

@[simp]
theorem closure_empty : closure L (∅ : Set M) = ⊥ :=
  (Substructure.gi L M).gc.l_bot
#align first_order.language.substructure.closure_empty FirstOrder.Language.Substructure.closure_empty

@[simp]
theorem closure_univ : closure L (univ : Set M) = ⊤ :=
  @coe_top L M _ ▸ closure_eq ⊤
#align first_order.language.substructure.closure_univ FirstOrder.Language.Substructure.closure_univ

theorem closure_union (s t : Set M) : closure L (s ∪ t) = closure L s ⊔ closure L t :=
  (Substructure.gi L M).gc.l_sup
#align first_order.language.substructure.closure_union FirstOrder.Language.Substructure.closure_union

theorem closure_unionᵢ {ι} (s : ι → Set M) : closure L (⋃ i, s i) = ⨆ i, closure L (s i) :=
  (Substructure.gi L M).gc.l_supᵢ
#align first_order.language.substructure.closure_Union FirstOrder.Language.Substructure.closure_unionᵢ

instance small_bot : Small.{u} (⊥ : L.Substructure M) :=
  by
  rw [← closure_empty]
  exact substructure.small_closure
#align first_order.language.substructure.small_bot FirstOrder.Language.Substructure.small_bot

/-!
### `comap` and `map`
-/


/-- The preimage of a substructure along a homomorphism is a substructure. -/
@[simps]
def comap (φ : M →[L] N) (S : L.Substructure N) : L.Substructure M
    where
  carrier := φ ⁻¹' S
  fun_mem n f x hx := by
    rw [mem_preimage, φ.map_fun]
    exact S.fun_mem f (φ ∘ x) hx
#align first_order.language.substructure.comap FirstOrder.Language.Substructure.comap

@[simp]
theorem mem_comap {S : L.Substructure N} {f : M →[L] N} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl
#align first_order.language.substructure.mem_comap FirstOrder.Language.Substructure.mem_comap

theorem comap_comap (S : L.Substructure P) (g : N →[L] P) (f : M →[L] N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl
#align first_order.language.substructure.comap_comap FirstOrder.Language.Substructure.comap_comap

@[simp]
theorem comap_id (S : L.Substructure P) : S.comap (Hom.id _ _) = S :=
  ext (by simp)
#align first_order.language.substructure.comap_id FirstOrder.Language.Substructure.comap_id

/-- The image of a substructure along a homomorphism is a substructure. -/
@[simps]
def map (φ : M →[L] N) (S : L.Substructure M) : L.Substructure N
    where
  carrier := φ '' S
  fun_mem n f x hx :=
    (mem_image _ _ _).1
      ⟨funMap f fun i => Classical.choose (hx i),
        S.fun_mem f _ fun i => (Classical.choose_spec (hx i)).1,
        by
        simp only [hom.map_fun, SetLike.mem_coe]
        exact congr rfl (funext fun i => (Classical.choose_spec (hx i)).2)⟩
#align first_order.language.substructure.map FirstOrder.Language.Substructure.map

@[simp]
theorem mem_map {f : M →[L] N} {S : L.Substructure M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  mem_image_iff_bex
#align first_order.language.substructure.mem_map FirstOrder.Language.Substructure.mem_map

theorem mem_map_of_mem (f : M →[L] N) {S : L.Substructure M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx
#align first_order.language.substructure.mem_map_of_mem FirstOrder.Language.Substructure.mem_map_of_mem

theorem apply_coe_mem_map (f : M →[L] N) (S : L.Substructure M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.Prop
#align first_order.language.substructure.apply_coe_mem_map FirstOrder.Language.Substructure.apply_coe_mem_map

theorem map_map (g : N →[L] P) (f : M →[L] N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _
#align first_order.language.substructure.map_map FirstOrder.Language.Substructure.map_map

theorem map_le_iff_le_comap {f : M →[L] N} {S : L.Substructure M} {T : L.Substructure N} :
    S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff
#align first_order.language.substructure.map_le_iff_le_comap FirstOrder.Language.Substructure.map_le_iff_le_comap

theorem gc_map_comap (f : M →[L] N) : GaloisConnection (map f) (comap f) := fun S T =>
  map_le_iff_le_comap
#align first_order.language.substructure.gc_map_comap FirstOrder.Language.Substructure.gc_map_comap

theorem map_le_of_le_comap {T : L.Substructure N} {f : M →[L] N} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le
#align first_order.language.substructure.map_le_of_le_comap FirstOrder.Language.Substructure.map_le_of_le_comap

theorem le_comap_of_map_le {T : L.Substructure N} {f : M →[L] N} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u
#align first_order.language.substructure.le_comap_of_map_le FirstOrder.Language.Substructure.le_comap_of_map_le

theorem le_comap_map {f : M →[L] N} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _
#align first_order.language.substructure.le_comap_map FirstOrder.Language.Substructure.le_comap_map

theorem map_comap_le {S : L.Substructure N} {f : M →[L] N} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _
#align first_order.language.substructure.map_comap_le FirstOrder.Language.Substructure.map_comap_le

theorem monotone_map {f : M →[L] N} : Monotone (map f) :=
  (gc_map_comap f).monotone_l
#align first_order.language.substructure.monotone_map FirstOrder.Language.Substructure.monotone_map

theorem monotone_comap {f : M →[L] N} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u
#align first_order.language.substructure.monotone_comap FirstOrder.Language.Substructure.monotone_comap

@[simp]
theorem map_comap_map {f : M →[L] N} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _
#align first_order.language.substructure.map_comap_map FirstOrder.Language.Substructure.map_comap_map

@[simp]
theorem comap_map_comap {S : L.Substructure N} {f : M →[L] N} :
    ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _
#align first_order.language.substructure.comap_map_comap FirstOrder.Language.Substructure.comap_map_comap

theorem map_sup (S T : L.Substructure M) (f : M →[L] N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (gc_map_comap f).l_sup
#align first_order.language.substructure.map_sup FirstOrder.Language.Substructure.map_sup

theorem map_supᵢ {ι : Sort _} (f : M →[L] N) (s : ι → L.Substructure M) :
    (supᵢ s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_supᵢ
#align first_order.language.substructure.map_supr FirstOrder.Language.Substructure.map_supᵢ

theorem comap_inf (S T : L.Substructure N) (f : M →[L] N) :
    (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
  (gc_map_comap f).u_inf
#align first_order.language.substructure.comap_inf FirstOrder.Language.Substructure.comap_inf

theorem comap_infᵢ {ι : Sort _} (f : M →[L] N) (s : ι → L.Substructure N) :
    (infᵢ s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_infᵢ
#align first_order.language.substructure.comap_infi FirstOrder.Language.Substructure.comap_infᵢ

@[simp]
theorem map_bot (f : M →[L] N) : (⊥ : L.Substructure M).map f = ⊥ :=
  (gc_map_comap f).l_bot
#align first_order.language.substructure.map_bot FirstOrder.Language.Substructure.map_bot

@[simp]
theorem comap_top (f : M →[L] N) : (⊤ : L.Substructure N).comap f = ⊤ :=
  (gc_map_comap f).u_top
#align first_order.language.substructure.comap_top FirstOrder.Language.Substructure.comap_top

@[simp]
theorem map_id (S : L.Substructure M) : S.map (Hom.id L M) = S :=
  ext fun x => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩
#align first_order.language.substructure.map_id FirstOrder.Language.Substructure.map_id

theorem map_closure (f : M →[L] N) (s : Set M) : (closure L s).map f = closure L (f '' s) :=
  Eq.symm <|
    closure_eq_of_le (Set.image_subset f subset_closure) <|
      map_le_iff_le_comap.2 <| closure_le.2 fun x hx => subset_closure ⟨x, hx, rfl⟩
#align first_order.language.substructure.map_closure FirstOrder.Language.Substructure.map_closure

@[simp]
theorem closure_image (f : M →[L] N) : closure L (f '' s) = map f (closure L s) :=
  (map_closure f s).symm
#align first_order.language.substructure.closure_image FirstOrder.Language.Substructure.closure_image

section GaloisCoinsertion

variable {ι : Type _} {f : M →[L] N} (hf : Function.Injective f)

include hf

/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]
#align first_order.language.substructure.gci_map_comap FirstOrder.Language.Substructure.gciMapComap

theorem comap_map_eq_of_injective (S : L.Substructure M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _
#align first_order.language.substructure.comap_map_eq_of_injective FirstOrder.Language.Substructure.comap_map_eq_of_injective

theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective
#align first_order.language.substructure.comap_surjective_of_injective FirstOrder.Language.Substructure.comap_surjective_of_injective

theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective
#align first_order.language.substructure.map_injective_of_injective FirstOrder.Language.Substructure.map_injective_of_injective

theorem comap_inf_map_of_injective (S T : L.Substructure M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap hf).u_inf_l _ _
#align first_order.language.substructure.comap_inf_map_of_injective FirstOrder.Language.Substructure.comap_inf_map_of_injective

theorem comap_infᵢ_map_of_injective (S : ι → L.Substructure M) :
    (⨅ i, (S i).map f).comap f = infᵢ S :=
  (gciMapComap hf).u_infᵢ_l _
#align first_order.language.substructure.comap_infi_map_of_injective FirstOrder.Language.Substructure.comap_infᵢ_map_of_injective

theorem comap_sup_map_of_injective (S T : L.Substructure M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap hf).u_sup_l _ _
#align first_order.language.substructure.comap_sup_map_of_injective FirstOrder.Language.Substructure.comap_sup_map_of_injective

theorem comap_supᵢ_map_of_injective (S : ι → L.Substructure M) :
    (⨆ i, (S i).map f).comap f = supᵢ S :=
  (gciMapComap hf).u_supᵢ_l _
#align first_order.language.substructure.comap_supr_map_of_injective FirstOrder.Language.Substructure.comap_supᵢ_map_of_injective

theorem map_le_map_iff_of_injective {S T : L.Substructure M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap hf).l_le_l_iff
#align first_order.language.substructure.map_le_map_iff_of_injective FirstOrder.Language.Substructure.map_le_map_iff_of_injective

theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strictMono_l
#align first_order.language.substructure.map_strict_mono_of_injective FirstOrder.Language.Substructure.map_strictMono_of_injective

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type _} {f : M →[L] N} (hf : Function.Surjective f)

include hf

/-- `map f` and `comap f` form a `galois_insertion` when `f` is surjective. -/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩
#align first_order.language.substructure.gi_map_comap FirstOrder.Language.Substructure.giMapComap

theorem map_comap_eq_of_surjective (S : L.Substructure N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _
#align first_order.language.substructure.map_comap_eq_of_surjective FirstOrder.Language.Substructure.map_comap_eq_of_surjective

theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective
#align first_order.language.substructure.map_surjective_of_surjective FirstOrder.Language.Substructure.map_surjective_of_surjective

theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective
#align first_order.language.substructure.comap_injective_of_surjective FirstOrder.Language.Substructure.comap_injective_of_surjective

theorem map_inf_comap_of_surjective (S T : L.Substructure N) :
    (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
  (giMapComap hf).l_inf_u _ _
#align first_order.language.substructure.map_inf_comap_of_surjective FirstOrder.Language.Substructure.map_inf_comap_of_surjective

theorem map_infᵢ_comap_of_surjective (S : ι → L.Substructure N) :
    (⨅ i, (S i).comap f).map f = infᵢ S :=
  (giMapComap hf).l_infᵢ_u _
#align first_order.language.substructure.map_infi_comap_of_surjective FirstOrder.Language.Substructure.map_infᵢ_comap_of_surjective

theorem map_sup_comap_of_surjective (S T : L.Substructure N) :
    (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
  (giMapComap hf).l_sup_u _ _
#align first_order.language.substructure.map_sup_comap_of_surjective FirstOrder.Language.Substructure.map_sup_comap_of_surjective

theorem map_supᵢ_comap_of_surjective (S : ι → L.Substructure N) :
    (⨆ i, (S i).comap f).map f = supᵢ S :=
  (giMapComap hf).l_supᵢ_u _
#align first_order.language.substructure.map_supr_comap_of_surjective FirstOrder.Language.Substructure.map_supᵢ_comap_of_surjective

theorem comap_le_comap_iff_of_surjective {S T : L.Substructure N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (giMapComap hf).u_le_u_iff
#align first_order.language.substructure.comap_le_comap_iff_of_surjective FirstOrder.Language.Substructure.comap_le_comap_iff_of_surjective

theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u
#align first_order.language.substructure.comap_strict_mono_of_surjective FirstOrder.Language.Substructure.comap_strictMono_of_surjective

end GaloisInsertion

instance inducedStructure {S : L.Substructure M} : L.Structure S
    where
  funMap n f x := ⟨funMap f fun i => x i, S.fun_mem f (fun i => x i) fun i => (x i).2⟩
  rel_map n r x := RelMap r fun i => (x i : M)
#align first_order.language.substructure.induced_Structure FirstOrder.Language.Substructure.inducedStructure

/-- The natural embedding of an `L.substructure` of `M` into `M`. -/
def subtype (S : L.Substructure M) : S ↪[L] M
    where
  toFun := coe
  inj' := Subtype.coe_injective
#align first_order.language.substructure.subtype FirstOrder.Language.Substructure.subtype

@[simp]
theorem coeSubtype : ⇑S.Subtype = coe :=
  rfl
#align first_order.language.substructure.coe_subtype FirstOrder.Language.Substructure.coeSubtype

/-- The equivalence between the maximal substructure of a structure and the structure itself. -/
def topEquiv : (⊤ : L.Substructure M) ≃[L] M
    where
  toFun := subtype ⊤
  invFun m := ⟨m, mem_top m⟩
  left_inv m := by simp
  right_inv m := rfl
#align first_order.language.substructure.top_equiv FirstOrder.Language.Substructure.topEquiv

@[simp]
theorem coe_topEquiv : ⇑(topEquiv : (⊤ : L.Substructure M) ≃[L] M) = coe :=
  rfl
#align first_order.language.substructure.coe_top_equiv FirstOrder.Language.Substructure.coe_topEquiv

/-- A dependent version of `substructure.closure_induction`. -/
@[elab_as_elim]
theorem closure_induction' (s : Set M) {p : ∀ x, x ∈ closure L s → Prop}
    (Hs : ∀ (x) (h : x ∈ s), p x (subset_closure h))
    (Hfun : ∀ {n : ℕ} (f : L.Functions n), ClosedUnder f { x | ∃ hx, p x hx }) {x}
    (hx : x ∈ closure L s) : p x hx :=
  by
  refine' Exists.elim _ fun (hx : x ∈ closure L s) (hc : p x hx) => hc
  exact closure_induction hx (fun x hx => ⟨subset_closure hx, Hs x hx⟩) @Hfun
#align first_order.language.substructure.closure_induction' FirstOrder.Language.Substructure.closure_induction'

end Substructure

namespace Lhom

open Substructure

variable {L' : Language} [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]

include φ

/-- Reduces the language of a substructure along a language hom. -/
def substructureReduct : L'.Substructure M ↪o L.Substructure M
    where
  toFun S :=
    { carrier := S
      fun_mem := fun n f x hx =>
        by
        have h := S.fun_mem (φ.on_function f) x hx
        simp only [Lhom.map_on_function, substructure.mem_carrier] at h
        exact h }
  inj' S T h := by
    simp only [SetLike.coe_set_eq] at h
    exact h
  map_rel_iff' S T := Iff.rfl
#align first_order.language.Lhom.substructure_reduct FirstOrder.Language.LHom.substructureReduct

@[simp]
theorem mem_substructureReduct {x : M} {S : L'.Substructure M} :
    x ∈ φ.substructureReduct S ↔ x ∈ S :=
  Iff.rfl
#align first_order.language.Lhom.mem_substructure_reduct FirstOrder.Language.LHom.mem_substructureReduct

@[simp]
theorem coe_substructureReduct {S : L'.Substructure M} : (φ.substructureReduct S : Set M) = ↑S :=
  rfl
#align first_order.language.Lhom.coe_substructure_reduct FirstOrder.Language.LHom.coe_substructureReduct

end Lhom

namespace Substructure

/-- Turns any substructure containing a constant set `A` into a `L[[A]]`-substructure. -/
def withConstants (S : L.Substructure M) {A : Set M} (h : A ⊆ S) : L[[A]].Substructure M
    where
  carrier := S
  fun_mem n f := by
    cases f
    · exact S.fun_mem f
    · cases n
      · exact fun _ _ => h f.2
      · exact isEmptyElim f
#align first_order.language.substructure.with_constants FirstOrder.Language.Substructure.withConstants

variable {A : Set M} {s : Set M} (h : A ⊆ S)

@[simp]
theorem mem_withConstants {x : M} : x ∈ S.withConstants h ↔ x ∈ S :=
  Iff.rfl
#align first_order.language.substructure.mem_with_constants FirstOrder.Language.Substructure.mem_withConstants

@[simp]
theorem coe_withConstants : (S.withConstants h : Set M) = ↑S :=
  rfl
#align first_order.language.substructure.coe_with_constants FirstOrder.Language.Substructure.coe_withConstants

@[simp]
theorem reduct_withConstants : (L.lhomWithConstants A).substructureReduct (S.withConstants h) = S :=
  by
  ext
  simp
#align first_order.language.substructure.reduct_with_constants FirstOrder.Language.Substructure.reduct_withConstants

theorem subset_closure_withConstants : A ⊆ closure (L[[A]]) s :=
  by
  intro a ha
  simp only [SetLike.mem_coe]
  let a' : L[[A]].Constants := Sum.inr ⟨a, ha⟩
  exact constants_mem a'
#align first_order.language.substructure.subset_closure_with_constants FirstOrder.Language.Substructure.subset_closure_withConstants

theorem closure_withConstants_eq :
    closure (L[[A]]) s =
      (closure L (A ∪ s)).withConstants ((A.subset_union_left s).trans subset_closure) :=
  by
  refine' closure_eq_of_le ((A.subset_union_right s).trans subset_closure) _
  rw [← (L.Lhom_with_constants A).substructureReduct.le_iff_le]
  simp only [subset_closure, reduct_with_constants, closure_le, Lhom.coe_substructure_reduct,
    Set.union_subset_iff, and_true_iff]
  · exact subset_closure_with_constants
  · infer_instance
  · infer_instance
#align first_order.language.substructure.closure_with_constants_eq FirstOrder.Language.Substructure.closure_withConstants_eq

end Substructure

namespace Hom

open Substructure

/-- The restriction of a first-order hom to a substructure `s ⊆ M` gives a hom `s → N`. -/
@[simps]
def domRestrict (f : M →[L] N) (p : L.Substructure M) : p →[L] N :=
  f.comp p.Subtype.toHom
#align first_order.language.hom.dom_restrict FirstOrder.Language.Hom.domRestrict

/-- A first-order hom `f : M → N` whose values lie in a substructure `p ⊆ N` can be restricted to a
hom `M → p`. -/
@[simps]
def codRestrict (p : L.Substructure N) (f : M →[L] N) (h : ∀ c, f c ∈ p) : M →[L] p
    where
  toFun c := ⟨f c, h c⟩
  map_rel' n R x h := f.map_rel R x h
#align first_order.language.hom.cod_restrict FirstOrder.Language.Hom.codRestrict

@[simp]
theorem comp_codRestrict (f : M →[L] N) (g : N →[L] P) (p : L.Substructure P) (h : ∀ b, g b ∈ p) :
    ((codRestrict p g h).comp f : M →[L] p) = codRestrict p (g.comp f) fun b => h _ :=
  ext fun b => rfl
#align first_order.language.hom.comp_cod_restrict FirstOrder.Language.Hom.comp_codRestrict

@[simp]
theorem subtype_comp_codRestrict (f : M →[L] N) (p : L.Substructure N) (h : ∀ b, f b ∈ p) :
    p.Subtype.toHom.comp (codRestrict p f h) = f :=
  ext fun b => rfl
#align first_order.language.hom.subtype_comp_cod_restrict FirstOrder.Language.Hom.subtype_comp_codRestrict

/-- The range of a first-order hom `f : M → N` is a submodule of `N`.
See Note [range copy pattern]. -/
def range (f : M →[L] N) : L.Substructure N :=
  (map f ⊤).copy (Set.range f) Set.image_univ.symm
#align first_order.language.hom.range FirstOrder.Language.Hom.range

theorem range_coe (f : M →[L] N) : (range f : Set N) = Set.range f :=
  rfl
#align first_order.language.hom.range_coe FirstOrder.Language.Hom.range_coe

@[simp]
theorem mem_range {f : M →[L] N} {x} : x ∈ range f ↔ ∃ y, f y = x :=
  Iff.rfl
#align first_order.language.hom.mem_range FirstOrder.Language.Hom.mem_range

theorem range_eq_map (f : M →[L] N) : f.range = map f ⊤ :=
  by
  ext
  simp
#align first_order.language.hom.range_eq_map FirstOrder.Language.Hom.range_eq_map

theorem mem_range_self (f : M →[L] N) (x : M) : f x ∈ f.range :=
  ⟨x, rfl⟩
#align first_order.language.hom.mem_range_self FirstOrder.Language.Hom.mem_range_self

@[simp]
theorem range_id : range (id L M) = ⊤ :=
  SetLike.coe_injective Set.range_id
#align first_order.language.hom.range_id FirstOrder.Language.Hom.range_id

theorem range_comp (f : M →[L] N) (g : N →[L] P) : range (g.comp f : M →[L] P) = map g (range f) :=
  SetLike.coe_injective (Set.range_comp g f)
#align first_order.language.hom.range_comp FirstOrder.Language.Hom.range_comp

theorem range_comp_le_range (f : M →[L] N) (g : N →[L] P) : range (g.comp f : M →[L] P) ≤ range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)
#align first_order.language.hom.range_comp_le_range FirstOrder.Language.Hom.range_comp_le_range

theorem range_eq_top {f : M →[L] N} : range f = ⊤ ↔ Function.Surjective f := by
  rw [SetLike.ext'_iff, range_coe, coe_top, Set.range_iff_surjective]
#align first_order.language.hom.range_eq_top FirstOrder.Language.Hom.range_eq_top

theorem range_le_iff_comap {f : M →[L] N} {p : L.Substructure N} : range f ≤ p ↔ comap f p = ⊤ := by
  rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]
#align first_order.language.hom.range_le_iff_comap FirstOrder.Language.Hom.range_le_iff_comap

theorem map_le_range {f : M →[L] N} {p : L.Substructure M} : map f p ≤ range f :=
  SetLike.coe_mono (Set.image_subset_range f p)
#align first_order.language.hom.map_le_range FirstOrder.Language.Hom.map_le_range

/-- The substructure of elements `x : M` such that `f x = g x` -/
def eqLocus (f g : M →[L] N) : Substructure L M
    where
  carrier := { x : M | f x = g x }
  fun_mem n fn x hx :=
    by
    have h : f ∘ x = g ∘ x := by
      ext
      repeat' rw [Function.comp_apply]
      apply hx
    simp [h]
#align first_order.language.hom.eq_locus FirstOrder.Language.Hom.eqLocus

/-- If two `L.hom`s are equal on a set, then they are equal on its substructure closure. -/
theorem eqOn_closure {f g : M →[L] N} {s : Set M} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure L s) :=
  show closure L s ≤ f.eqLocus g from closure_le.2 h
#align first_order.language.hom.eq_on_closure FirstOrder.Language.Hom.eqOn_closure

theorem eq_of_eqOn_top {f g : M →[L] N} (h : Set.EqOn f g (⊤ : Substructure L M)) : f = g :=
  ext fun x => h trivial
#align first_order.language.hom.eq_of_eq_on_top FirstOrder.Language.Hom.eq_of_eqOn_top

variable {s : Set M}

theorem eq_of_eqOn_dense (hs : closure L s = ⊤) {f g : M →[L] N} (h : s.EqOn f g) : f = g :=
  eq_of_eqOn_top <| hs ▸ eqOn_closure h
#align first_order.language.hom.eq_of_eq_on_dense FirstOrder.Language.Hom.eq_of_eqOn_dense

end Hom

namespace Embedding

open Substructure

/-- The restriction of a first-order embedding to a substructure `s ⊆ M` gives an embedding `s → N`.
-/
def domRestrict (f : M ↪[L] N) (p : L.Substructure M) : p ↪[L] N :=
  f.comp p.Subtype
#align first_order.language.embedding.dom_restrict FirstOrder.Language.Embedding.domRestrict

@[simp]
theorem domRestrict_apply (f : M ↪[L] N) (p : L.Substructure M) (x : p) : f.domRestrict p x = f x :=
  rfl
#align first_order.language.embedding.dom_restrict_apply FirstOrder.Language.Embedding.domRestrict_apply

/-- A first-order embedding `f : M → N` whose values lie in a substructure `p ⊆ N` can be restricted
to an embedding `M → p`. -/
def codRestrict (p : L.Substructure N) (f : M ↪[L] N) (h : ∀ c, f c ∈ p) : M ↪[L] p
    where
  toFun := f.toHom.codRestrict p h
  inj' a b ab := f.Injective (Subtype.mk_eq_mk.1 ab)
  map_fun' n F x := (f.toHom.codRestrict p h).map_fun' F x
  map_rel' n r x := by
    simp only
    rw [← p.subtype.map_rel, Function.comp.assoc]
    change rel_map r (hom.comp p.subtype.to_hom (f.to_hom.cod_restrict p h) ∘ x) ↔ _
    rw [hom.subtype_comp_cod_restrict, ← f.map_rel]
    rfl
#align first_order.language.embedding.cod_restrict FirstOrder.Language.Embedding.codRestrict

@[simp]
theorem codRestrict_apply (p : L.Substructure N) (f : M ↪[L] N) {h} (x : M) :
    (codRestrict p f h x : N) = f x :=
  rfl
#align first_order.language.embedding.cod_restrict_apply FirstOrder.Language.Embedding.codRestrict_apply

@[simp]
theorem comp_codRestrict (f : M ↪[L] N) (g : N ↪[L] P) (p : L.Substructure P) (h : ∀ b, g b ∈ p) :
    ((codRestrict p g h).comp f : M ↪[L] p) = codRestrict p (g.comp f) fun b => h _ :=
  ext fun b => rfl
#align first_order.language.embedding.comp_cod_restrict FirstOrder.Language.Embedding.comp_codRestrict

@[simp]
theorem subtype_comp_codRestrict (f : M ↪[L] N) (p : L.Substructure N) (h : ∀ b, f b ∈ p) :
    p.Subtype.comp (codRestrict p f h) = f :=
  ext fun b => rfl
#align first_order.language.embedding.subtype_comp_cod_restrict FirstOrder.Language.Embedding.subtype_comp_codRestrict

/-- The equivalence between a substructure `s` and its image `s.map f.to_hom`, where `f` is an
  embedding. -/
noncomputable def substructureEquivMap (f : M ↪[L] N) (s : L.Substructure M) : s ≃[L] s.map f.toHom
    where
  toFun := codRestrict (s.map f.toHom) (f.domRestrict s) fun ⟨m, hm⟩ => ⟨m, hm, rfl⟩
  invFun n := ⟨Classical.choose n.2, (Classical.choose_spec n.2).1⟩
  left_inv := fun ⟨m, hm⟩ =>
    Subtype.mk_eq_mk.2
      (f.Injective
        (Classical.choose_spec
            (codRestrict (s.map f.toHom) (f.domRestrict s) (fun ⟨m, hm⟩ => ⟨m, hm, rfl⟩)
                ⟨m, hm⟩).2).2)
  right_inv := fun ⟨n, hn⟩ => Subtype.mk_eq_mk.2 (Classical.choose_spec hn).2
#align first_order.language.embedding.substructure_equiv_map FirstOrder.Language.Embedding.substructureEquivMap

@[simp]
theorem substructureEquivMap_apply (f : M ↪[L] N) (p : L.Substructure M) (x : p) :
    (f.substructureEquivMap p x : N) = f x :=
  rfl
#align first_order.language.embedding.substructure_equiv_map_apply FirstOrder.Language.Embedding.substructureEquivMap_apply

/-- The equivalence between the domain and the range of an embedding `f`. -/
noncomputable def equivRange (f : M ↪[L] N) : M ≃[L] f.toHom.range
    where
  toFun := codRestrict f.toHom.range f f.toHom.mem_range_self
  invFun n := Classical.choose n.2
  left_inv m :=
    f.Injective (Classical.choose_spec (codRestrict f.toHom.range f f.toHom.mem_range_self m).2)
  right_inv := fun ⟨n, hn⟩ => Subtype.mk_eq_mk.2 (Classical.choose_spec hn)
#align first_order.language.embedding.equiv_range FirstOrder.Language.Embedding.equivRange

@[simp]
theorem equivRange_apply (f : M ↪[L] N) (x : M) : (f.equivRange x : N) = f x :=
  rfl
#align first_order.language.embedding.equiv_range_apply FirstOrder.Language.Embedding.equivRange_apply

end Embedding

namespace Equiv

theorem toHom_range (f : M ≃[L] N) : f.toHom.range = ⊤ :=
  by
  ext n
  simp only [hom.mem_range, coe_to_hom, substructure.mem_top, iff_true_iff]
  exact ⟨f.symm n, apply_symm_apply _ _⟩
#align first_order.language.equiv.to_hom_range FirstOrder.Language.Equiv.toHom_range

end Equiv

namespace Substructure

/-- The embedding associated to an inclusion of substructures. -/
def inclusion {S T : L.Substructure M} (h : S ≤ T) : S ↪[L] T :=
  S.Subtype.codRestrict _ fun x => h x.2
#align first_order.language.substructure.inclusion FirstOrder.Language.Substructure.inclusion

@[simp]
theorem coe_inclusion {S T : L.Substructure M} (h : S ≤ T) :
    (inclusion h : S → T) = Set.inclusion h :=
  rfl
#align first_order.language.substructure.coe_inclusion FirstOrder.Language.Substructure.coe_inclusion

theorem range_subtype (S : L.Substructure M) : S.Subtype.toHom.range = S :=
  by
  ext x
  simp only [hom.mem_range, embedding.coe_to_hom, coeSubtype]
  refine' ⟨_, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  rintro ⟨⟨y, hy⟩, rfl⟩
  exact hy
#align first_order.language.substructure.range_subtype FirstOrder.Language.Substructure.range_subtype

end Substructure

end Language

end FirstOrder

