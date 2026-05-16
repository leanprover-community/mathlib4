/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Gabin Kolly
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.Closure
public import Mathlib.ModelTheory.Semantics
public import Mathlib.ModelTheory.Encoding

/-!
# First-Order Substructures

This file defines substructures of first-order structures in a similar manner to the various
substructures appearing in the algebra library.

## Main Definitions

- A `FirstOrder.Language.Substructure` is defined so that `L.Substructure M` is the type of all
    substructures of the `L`-structure `M`.
- `FirstOrder.Language.Substructure.closure` is defined so that if `s : Set M`, `closure L s` is
    the least substructure of `M` containing `s`.
- `FirstOrder.Language.Substructure.comap` is defined so that `s.comap f` is the preimage of the
    substructure `s` under the homomorphism `f`, as a substructure.
- `FirstOrder.Language.Substructure.map` is defined so that `s.map f` is the image of the
    substructure `s` under the homomorphism `f`, as a substructure.
- `FirstOrder.Language.Hom.range` is defined so that `f.range` is the range of the
    homomorphism `f`, as a substructure.
- `FirstOrder.Language.Hom.domRestrict` and `FirstOrder.Language.Hom.codRestrict` restrict
    the domain and codomain respectively of first-order homomorphisms to substructures.
- `FirstOrder.Language.Embedding.domRestrict` and `FirstOrder.Language.Embedding.codRestrict`
    restrict the domain and codomain respectively of first-order embeddings to substructures.
- `FirstOrder.Language.Substructure.inclusion` is the inclusion embedding between substructures.
- `FirstOrder.Language.Substructure.PartialEquiv` is defined so that `PartialEquiv L M N` is
  the type of equivalences between substructures of `M` and `N`.

## Main Results

- `L.Substructure M` forms a `CompleteLattice`.
-/

@[expose] public section

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} {N P : Type*}
variable [L.Structure M] [L.Structure N] [L.Structure P]

open FirstOrder Cardinal

open Structure

section ClosedUnder

open Set

variable {n : ℕ} (f : L.Functions n) (s : Set M)

/-- Indicates that a set in a given structure is a closed under a function symbol. -/
def ClosedUnder : Prop :=
  ∀ x : Fin n → M, (∀ i : Fin n, x i ∈ s) → funMap f x ∈ s

variable (L)

@[simp]
theorem closedUnder_univ : ClosedUnder f (univ : Set M) := fun _ _ => mem_univ _

variable {L f s} {t : Set M}

namespace ClosedUnder

theorem inter (hs : ClosedUnder f s) (ht : ClosedUnder f t) : ClosedUnder f (s ∩ t) := fun x h =>
  mem_inter (hs x fun i => mem_of_mem_inter_left (h i)) (ht x fun i => mem_of_mem_inter_right (h i))

theorem inf (hs : ClosedUnder f s) (ht : ClosedUnder f t) : ClosedUnder f (s ⊓ t) :=
  hs.inter ht

variable {S : Set (Set M)}

theorem sInf (hS : ∀ s, s ∈ S → ClosedUnder f s) : ClosedUnder f (sInf S) := fun x h s hs =>
  hS s hs x fun i => h i s hs

end ClosedUnder

end ClosedUnder

variable (L) (M)

/-- A substructure of a structure `M` is a set closed under application of function symbols. -/
structure Substructure where
  /-- The underlying set of this substructure -/
  carrier : Set M
  fun_mem : ∀ {n}, ∀ f : L.Functions n, ClosedUnder f carrier

variable {L} {M}

namespace Substructure

attribute [coe] Substructure.carrier

instance instSetLike : SetLike (L.Substructure M) M :=
  ⟨Substructure.carrier, fun p q h => by cases p; cases q; congr⟩

instance : PartialOrder (L.Substructure M) := .ofSetLike (L.Substructure M) M

/-- See Note [custom simps projection] -/
def Simps.coe (S : L.Substructure M) : Set M :=
  S

initialize_simps_projections Substructure (carrier → coe, as_prefix coe)

@[simp]
theorem mem_carrier {s : L.Substructure M} {x : M} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

/-- Two substructures are equal if they have the same elements. -/
@[ext]
theorem ext {S T : L.Substructure M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy a substructure replacing `carrier` with a set that is equal to it. -/
protected def copy (S : L.Substructure M) (s : Set M) (hs : s = S) : L.Substructure M where
  carrier := s
  fun_mem _ f := hs.symm ▸ S.fun_mem _ f

end Substructure

variable {S : L.Substructure M}

theorem Term.realize_mem {α : Type*} (t : L.Term α) (xs : α → M) (h : ∀ a, xs a ∈ S) :
    t.realize xs ∈ S := by
  induction t with
  | var a => exact h a
  | func f ts ih => exact Substructure.fun_mem _ _ _ ih

namespace Substructure

@[simp]
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl

theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs

theorem constants_mem (c : L.Constants) : (c : M) ∈ S :=
  mem_carrier.2 (S.fun_mem c _ finZeroElim)

/-- The substructure `M` of the structure `M`. -/
instance instTop : Top (L.Substructure M) :=
  ⟨{  carrier := Set.univ
      fun_mem := fun {_} _ _ _ => Set.mem_univ _ }⟩

instance instInhabited : Inhabited (L.Substructure M) :=
  ⟨⊤⟩

@[simp]
theorem mem_top (x : M) : x ∈ (⊤ : L.Substructure M) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : L.Substructure M) : Set M) = Set.univ :=
  rfl

/-- The inf of two substructures is their intersection. -/
instance instInf : Min (L.Substructure M) :=
  ⟨fun S₁ S₂ =>
    { carrier := (S₁ : Set M) ∩ (S₂ : Set M)
      fun_mem := fun {_} f => (S₁.fun_mem f).inf (S₂.fun_mem f) }⟩

@[simp]
theorem coe_inf (p p' : L.Substructure M) :
    ((p ⊓ p' : L.Substructure M) : Set M) = (p : Set M) ∩ (p' : Set M) :=
  rfl

@[simp]
theorem mem_inf {p p' : L.Substructure M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

instance instInfSet : InfSet (L.Substructure M) :=
  ⟨fun s =>
    { carrier := ⋂ t ∈ s, (t : Set M)
      fun_mem := fun {n} f =>
        ClosedUnder.sInf
          (by
            rintro _ ⟨t, rfl⟩
            by_cases h : t ∈ s
            · simpa [h] using t.fun_mem f
            · simp [h]) }⟩

@[simp, norm_cast]
theorem coe_sInf (S : Set (L.Substructure M)) :
    ((sInf S : L.Substructure M) : Set M) = ⋂ s ∈ S, (s : Set M) :=
  rfl

theorem mem_sInf {S : Set (L.Substructure M)} {x : M} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂

theorem mem_iInf {ι : Sort*} {S : ι → L.Substructure M} {x : M} :
    x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} {S : ι → L.Substructure M} :
    ((⨅ i, S i : L.Substructure M) : Set M) = ⋂ i, (S i : Set M) := by
  simp only [iInf, coe_sInf, Set.biInter_range]

/-- Substructures of a structure form a complete lattice. -/
instance instCompleteLattice : CompleteLattice (L.Substructure M) :=
  { completeLatticeOfInf (L.Substructure M) fun _ =>
      IsGLB.of_image
        (fun {S T : L.Substructure M} => show (S : Set M) ≤ T ↔ S ≤ T from SetLike.coe_subset_coe)
        isGLB_biInf with
    le := (· ≤ ·)
    lt := (· < ·)
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    le_inf := fun _a _b _c ha hb _x hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

variable (L)

/-- The `L.Substructure` generated by a set. -/
def closure : LowerAdjoint ((↑) : L.Substructure M → Set M) :=
  ⟨fun s => sInf { S | s ⊆ S }, fun _ _ =>
    ⟨Set.Subset.trans fun _x hx => mem_sInf.2 fun _S hS => hS hx, fun h => sInf_le h⟩⟩

variable {L} {s : Set M}

theorem mem_closure {x : M} : x ∈ closure L s ↔ ∀ S : L.Substructure M, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The substructure generated by a set includes the set. -/
@[simp]
theorem subset_closure : s ⊆ closure L s :=
  (closure L).le_closure s

theorem notMem_of_notMem_closure {P : M} (hP : P ∉ closure L s) : P ∉ s := fun h =>
  hP (subset_closure h)

@[simp]
theorem closed (S : L.Substructure M) : (closure L).closed (S : Set M) :=
  congr rfl ((closure L).eq_of_le Set.Subset.rfl fun _x xS => mem_closure.2 fun _T hT => hT xS)

open Set

/-- A substructure `S` includes `closure L s` if and only if it includes `s`. -/
@[simp]
theorem closure_le : closure L s ≤ S ↔ s ⊆ S :=
  (closure L).closure_le_closed_iff_le s S.closed

/-- Substructure closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure L s ≤ closure L t`. -/
@[gcongr]
theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : closure L s ≤ closure L t :=
  (closure L).monotone h

theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure L s) : closure L s = S :=
  (closure L).eq_of_le h₁ h₂

theorem coe_closure_eq_range_term_realize :
    (closure L s : Set M) = range (@Term.realize L _ _ _ ((↑) : s → M)) := by
  let S : L.Substructure M := ⟨range (Term.realize (L := L) ((↑) : s → M)), fun {n} f x hx => by
    simp only [mem_range] at *
    refine ⟨func f fun i => Classical.choose (hx i), ?_⟩
    simp only [Term.realize, fun i => Classical.choose_spec (hx i)]⟩
  change _ = (S : Set M)
  rw [← SetLike.ext'_iff]
  refine closure_eq_of_le (fun x hx => ⟨var ⟨x, hx⟩, rfl⟩) (le_sInf fun S' hS' => ?_)
  rintro _ ⟨t, rfl⟩
  exact t.realize_mem _ fun i => hS' i.2

instance small_closure [Small.{u} s] : Small.{u} (closure L s) := by
  rw [← SetLike.coe_sort_coe, Substructure.coe_closure_eq_range_term_realize]
  exact small_range _

theorem mem_closure_iff_exists_term {x : M} :
    x ∈ closure L s ↔ ∃ t : L.Term s, t.realize ((↑) : s → M) = x := by
  rw [← SetLike.mem_coe, coe_closure_eq_range_term_realize, mem_range]

theorem lift_card_closure_le_card_term : Cardinal.lift.{max u w} #(closure L s) ≤ #(L.Term s) := by
  rw [← SetLike.coe_sort_coe, coe_closure_eq_range_term_realize]
  rw [← Cardinal.lift_id'.{w, max u w} #(L.Term s)]
  exact Cardinal.mk_range_le_lift

theorem lift_card_closure_le :
    Cardinal.lift.{u, w} #(closure L s) ≤
      max ℵ₀ (Cardinal.lift.{u, w} #s + Cardinal.lift.{w, u} #(Σ i, L.Functions i)) := by
  rw [← lift_umax]
  refine lift_card_closure_le_card_term.trans (Term.card_le.trans ?_)
  rw [mk_sum, lift_umax.{w, u}]

lemma mem_closed_iff (s : Set M) :
    s ∈ (closure L).closed ↔ ∀ {n}, ∀ f : L.Functions n, ClosedUnder f s := by
  refine ⟨fun h n f => ?_, fun h => ?_⟩
  · rw [← h]
    exact Substructure.fun_mem _ _
  · have h' : closure L s = ⟨s, h⟩ := closure_eq_of_le (refl _) subset_closure
    exact congr_arg _ h'

variable (L)

lemma mem_closed_of_isRelational [L.IsRelational] (s : Set M) : s ∈ (closure L).closed :=
  (mem_closed_iff s).2 isEmptyElim

@[simp]
lemma closure_eq_of_isRelational [L.IsRelational] (s : Set M) : closure L s = s :=
  LowerAdjoint.closure_eq_self_of_mem_closed _ (mem_closed_of_isRelational L s)

@[simp]
lemma mem_closure_iff_of_isRelational [L.IsRelational] (s : Set M) (m : M) :
    m ∈ closure L s ↔ m ∈ s := by
  rw [← SetLike.mem_coe, closure_eq_of_isRelational]

theorem _root_.Set.Countable.substructure_closure
    [Countable (Σ l, L.Functions l)] (h : s.Countable) : Countable.{w + 1} (closure L s) := by
  haveI : Countable s := h.to_subtype
  rw [← mk_le_aleph0_iff, ← lift_le_aleph0]
  exact lift_card_closure_le_card_term.trans mk_le_aleph0

variable {L} (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under function symbols, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_elim]
theorem closure_induction {p : M → Prop} {x} (h : x ∈ closure L s) (Hs : ∀ x ∈ s, p x)
    (Hfun : ∀ {n : ℕ} (f : L.Functions n), ClosedUnder f (setOf p)) : p x :=
  (@closure_le L M _ ⟨setOf p, fun {_} => Hfun⟩ _).2 Hs h

/-- If `s` is a dense set in a structure `M`, `Substructure.closure L s = ⊤`, then in order to prove
that some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify
that `p` is preserved under function symbols. -/
@[elab_as_elim]
theorem dense_induction {p : M → Prop} (x : M) {s : Set M} (hs : closure L s = ⊤)
    (Hs : ∀ x ∈ s, p x) (Hfun : ∀ {n : ℕ} (f : L.Functions n), ClosedUnder f (setOf p)) : p x := by
  have : ∀ x ∈ closure L s, p x := fun x hx => closure_induction hx Hs fun {n} => Hfun
  simpa [hs] using this x

variable (L) (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure L M _) (↑) where
  choice s _ := closure L s
  gc := (closure L).gc
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

variable {L} {M}

/-- Closure of a substructure `S` equals `S`. -/
@[simp]
theorem closure_eq : closure L (S : Set M) = S :=
  (Substructure.gi L M).l_u_eq S

@[simp]
theorem closure_empty : closure L (∅ : Set M) = ⊥ :=
  (Substructure.gi L M).gc.l_bot

@[simp]
theorem closure_univ : closure L (univ : Set M) = ⊤ :=
  @coe_top L M _ ▸ closure_eq ⊤

theorem closure_union (s t : Set M) : closure L (s ∪ t) = closure L s ⊔ closure L t :=
  (Substructure.gi L M).gc.l_sup

theorem closure_iUnion {ι} (s : ι → Set M) : closure L (⋃ i, s i) = ⨆ i, closure L (s i) :=
  (Substructure.gi L M).gc.l_iSup

theorem closure_insert (s : Set M) (m : M) : closure L (insert m s) = closure L {m} ⊔ closure L s :=
  closure_union {m} s

instance small_bot : Small.{u} (⊥ : L.Substructure M) := by
  rw [← closure_empty]
  haveI : Small.{u} (∅ : Set M) := small_subsingleton _
  exact Substructure.small_closure

theorem iSup_eq_closure {ι : Sort*} (S : ι → L.Substructure M) :
    ⨆ i, S i = closure L (⋃ i, (S i : Set M)) := by simp_rw [closure_iUnion, closure_eq]

-- This proof uses the fact that `Substructure.closure` is finitary.
theorem mem_iSup_of_directed {ι : Type*} [hι : Nonempty ι] {S : ι → L.Substructure M}
    (hS : Directed (· ≤ ·) S) {x : M} :
    x ∈ ⨆ i, S i ↔ ∃ i, x ∈ S i := by
  refine ⟨?_, fun ⟨i, hi⟩ ↦ le_iSup S i hi⟩
  suffices x ∈ closure L (⋃ i, (S i : Set M)) → ∃ i, x ∈ S i by
    simpa only [closure_iUnion, closure_eq (S _)] using this
  refine fun hx ↦ closure_induction hx (fun _ ↦ mem_iUnion.1) (fun f v hC ↦ ?_)
  simp_rw [Set.mem_setOf] at *
  have ⟨i, hi⟩ := hS.finite_le (fun i ↦ Classical.choose (hC i))
  refine ⟨i, (S i).fun_mem f v (fun j ↦ hi j (Classical.choose_spec (hC j)))⟩

-- This proof uses the fact that `Substructure.closure` is finitary.
theorem mem_sSup_of_directedOn {S : Set (L.Substructure M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : M} :
    x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]

variable (L) (M)

instance [IsEmpty L.Constants] : IsEmpty (⊥ : L.Substructure M) := by
  refine (isEmpty_subtype _).2 (fun x => ?_)
  have h : (∅ : Set M) ∈ (closure L).closed := by
    rw [mem_closed_iff]
    intro n f
    cases n
    · exact isEmptyElim f
    · intro x hx
      simp only [mem_empty_iff_false, forall_const] at hx
  rw [← closure_empty, ← SetLike.mem_coe, h]
  exact Set.notMem_empty _

variable {L} {M}

/-!
### `comap` and `map`
-/


/-- The preimage of a substructure along a homomorphism is a substructure. -/
@[simps]
def comap (φ : M →[L] N) (S : L.Substructure N) : L.Substructure M where
  carrier := φ ⁻¹' S
  fun_mem {n} f x hx := by
    rw [mem_preimage, φ.map_fun]
    exact S.fun_mem f (φ ∘ x) hx

@[simp]
theorem mem_comap {S : L.Substructure N} {f : M →[L] N} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

theorem comap_comap (S : L.Substructure P) (g : N →[L] P) (f : M →[L] N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[simp]
theorem comap_id (S : L.Substructure P) : S.comap (Hom.id _ _) = S :=
  ext (by simp)

/-- The image of a substructure along a homomorphism is a substructure. -/
@[simps]
def map (φ : M →[L] N) (S : L.Substructure M) : L.Substructure N where
  carrier := φ '' S
  fun_mem {n} f x hx :=
    (mem_image _ _ _).1
      ⟨funMap f fun i => Classical.choose (hx i),
        S.fun_mem f _ fun i => (Classical.choose_spec (hx i)).1, by
        simp only [Hom.map_fun, SetLike.mem_coe]
        exact congr rfl (funext fun i => (Classical.choose_spec (hx i)).2)⟩

@[simp]
theorem mem_map {f : M →[L] N} {S : L.Substructure M} {y : N} :
    y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  Iff.rfl

theorem mem_map_of_mem (f : M →[L] N) {S : L.Substructure M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx

theorem apply_coe_mem_map (f : M →[L] N) (S : L.Substructure M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.prop

theorem map_map (g : N →[L] P) (f : M →[L] N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _

theorem map_le_iff_le_comap {f : M →[L] N} {S : L.Substructure M} {T : L.Substructure N} :
    S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff

theorem gc_map_comap (f : M →[L] N) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

theorem map_le_of_le_comap {T : L.Substructure N} {f : M →[L] N} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le

theorem le_comap_of_map_le {T : L.Substructure N} {f : M →[L] N} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u

theorem le_comap_map {f : M →[L] N} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _

theorem map_comap_le {S : L.Substructure N} {f : M →[L] N} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _

theorem monotone_map {f : M →[L] N} : Monotone (map f) :=
  (gc_map_comap f).monotone_l

theorem monotone_comap {f : M →[L] N} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u

@[simp]
theorem map_comap_map {f : M →[L] N} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _

@[simp]
theorem comap_map_comap {S : L.Substructure N} {f : M →[L] N} :
    ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _

theorem map_sup (S T : L.Substructure M) (f : M →[L] N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (gc_map_comap f).l_sup

theorem map_iSup {ι : Sort*} (f : M →[L] N) (s : ι → L.Substructure M) :
    (⨆ i, s i).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

theorem comap_inf (S T : L.Substructure N) (f : M →[L] N) :
    (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
  (gc_map_comap f).u_inf

theorem comap_iInf {ι : Sort*} (f : M →[L] N) (s : ι → L.Substructure N) :
    (⨅ i, s i).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
theorem map_bot (f : M →[L] N) : (⊥ : L.Substructure M).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem comap_top (f : M →[L] N) : (⊤ : L.Substructure N).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[simp]
theorem map_id (S : L.Substructure M) : S.map (Hom.id L M) = S :=
  SetLike.coe_injective <| Set.image_id _

theorem map_closure (f : M →[L] N) (s : Set M) : (closure L s).map f = closure L (f '' s) :=
  Eq.symm <|
    closure_eq_of_le (Set.image_mono subset_closure) <|
      map_le_iff_le_comap.2 <| closure_le.2 fun x hx => subset_closure ⟨x, hx, rfl⟩

@[simp]
theorem closure_image (f : M →[L] N) : closure L (f '' s) = map f (closure L s) :=
  (map_closure f s).symm

section GaloisCoinsertion

variable {ι : Type*} {f : M →[L] N}

/-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/
def gciMapComap (hf : Function.Injective f) : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]

variable (hf : Function.Injective f)
include hf

theorem comap_map_eq_of_injective (S : L.Substructure M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _

theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective

theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective

theorem comap_inf_map_of_injective (S T : L.Substructure M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap hf).u_inf_l _ _

theorem comap_iInf_map_of_injective (S : ι → L.Substructure M) :
    (⨅ i, (S i).map f).comap f = ⨅ i, S i :=
  (gciMapComap hf).u_iInf_l _

theorem comap_sup_map_of_injective (S T : L.Substructure M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap hf).u_sup_l _ _

theorem comap_iSup_map_of_injective (S : ι → L.Substructure M) :
    (⨆ i, (S i).map f).comap f = ⨆ i, S i :=
  (gciMapComap hf).u_iSup_l _

theorem map_le_map_iff_of_injective {S T : L.Substructure M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap hf).l_le_l_iff

theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strictMono_l

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type*} {f : M →[L] N} (hf : Function.Surjective f)
include hf

/-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩

theorem map_comap_eq_of_surjective (S : L.Substructure N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _

theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective

theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective

theorem map_inf_comap_of_surjective (S T : L.Substructure N) :
    (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
  (giMapComap hf).l_inf_u _ _

theorem map_iInf_comap_of_surjective (S : ι → L.Substructure N) :
    (⨅ i, (S i).comap f).map f = ⨅ i, S i :=
  (giMapComap hf).l_iInf_u _

theorem map_sup_comap_of_surjective (S T : L.Substructure N) :
    (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
  (giMapComap hf).l_sup_u _ _

theorem map_iSup_comap_of_surjective (S : ι → L.Substructure N) :
    (⨆ i, (S i).comap f).map f = ⨆ i, S i :=
  (giMapComap hf).l_iSup_u _

theorem comap_le_comap_iff_of_surjective {S T : L.Substructure N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (giMapComap hf).u_le_u_iff

theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u

end GaloisInsertion

instance inducedStructure {S : L.Substructure M} : L.Structure S where
  funMap {_} f x := ⟨funMap f fun i => x i, S.fun_mem f (fun i => x i) fun i => (x i).2⟩
  RelMap {_} r x := RelMap r fun i => (x i : M)

/-- The natural embedding of an `L.Substructure` of `M` into `M`. -/
def subtype (S : L.Substructure M) : S ↪[L] M where
  toFun := (↑)
  inj' := Subtype.coe_injective

@[simp]
theorem subtype_apply {S : L.Substructure M} {x : S} : subtype S x = x :=
  rfl

theorem subtype_injective (S : L.Substructure M) : Function.Injective (subtype S) :=
  Subtype.coe_injective

@[simp]
theorem coe_subtype : ⇑S.subtype = ((↑) : S → M) :=
  rfl

/-- The equivalence between the maximal substructure of a structure and the structure itself. -/
def topEquiv : (⊤ : L.Substructure M) ≃[L] M where
  toFun := subtype ⊤
  invFun m := ⟨m, mem_top m⟩
  left_inv m := by simp

@[simp]
theorem coe_topEquiv :
    ⇑(topEquiv : (⊤ : L.Substructure M) ≃[L] M) = ((↑) : (⊤ : L.Substructure M) → M) :=
  rfl

@[simp]
theorem realize_boundedFormula_top {α : Type*} {n : ℕ} {φ : L.BoundedFormula α n}
    {v : α → (⊤ : L.Substructure M)} {xs : Fin n → (⊤ : L.Substructure M)} :
    φ.Realize v xs ↔ φ.Realize (((↑) : _ → M) ∘ v) ((↑) ∘ xs) := by
  rw [← StrongHomClass.realize_boundedFormula Substructure.topEquiv φ]
  simp

@[simp]
theorem realize_formula_top {α : Type*} {φ : L.Formula α} {v : α → (⊤ : L.Substructure M)} :
    φ.Realize v ↔ φ.Realize (((↑) : (⊤ : L.Substructure M) → M) ∘ v) := by
  rw [← StrongHomClass.realize_formula Substructure.topEquiv φ]
  simp

/-- A dependent version of `Substructure.closure_induction`. -/
@[elab_as_elim]
theorem closure_induction' (s : Set M) {p : ∀ x, x ∈ closure L s → Prop}
    (Hs : ∀ (x) (h : x ∈ s), p x (subset_closure h))
    (Hfun : ∀ {n : ℕ} (f : L.Functions n), ClosedUnder f { x | ∃ hx, p x hx }) {x}
    (hx : x ∈ closure L s) : p x hx := by
  refine Exists.elim ?_ fun (hx : x ∈ closure L s) (hc : p x hx) => hc
  exact closure_induction hx (fun x hx => ⟨subset_closure hx, Hs x hx⟩) @Hfun

end Substructure

open Substructure

namespace LHom

variable {L' : Language} [L'.Structure M]

/-- Reduces the language of a substructure along a language hom. -/
def substructureReduct (φ : L →ᴸ L') [φ.IsExpansionOn M] :
    L'.Substructure M ↪o L.Substructure M where
  toFun S :=
    { carrier := S
      fun_mem := fun {n} f x hx => by
        have h := S.fun_mem (φ.onFunction f) x hx
        simp only [LHom.map_onFunction, Substructure.mem_carrier] at h
        exact h }
  inj' S T h := by
    simp only [SetLike.coe_set_eq, Substructure.mk.injEq] at h
    exact h
  map_rel_iff' {_ _} := Iff.rfl

variable (φ : L →ᴸ L') [φ.IsExpansionOn M]

@[simp]
theorem mem_substructureReduct {x : M} {S : L'.Substructure M} :
    x ∈ φ.substructureReduct S ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_substructureReduct {S : L'.Substructure M} : (φ.substructureReduct S : Set M) = ↑S :=
  rfl

end LHom

namespace Substructure

/-- Turns any substructure containing a constant set `A` into a `L[[A]]`-substructure. -/
def withConstants (S : L.Substructure M) {A : Set M} (h : A ⊆ S) : L[[A]].Substructure M where
  carrier := S
  fun_mem {n} f := by
    obtain f | f := f
    · exact S.fun_mem f
    · cases n
      · exact fun _ _ => h f.2
      · exact isEmptyElim f

variable {A : Set M} {s : Set M} (h : A ⊆ S)

@[simp]
theorem mem_withConstants {x : M} : x ∈ S.withConstants h ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_withConstants : (S.withConstants h : Set M) = ↑S :=
  rfl

@[simp]
theorem reduct_withConstants :
    (L.lhomWithConstants A).substructureReduct (S.withConstants h) = S := by
  ext
  simp

theorem subset_closure_withConstants : A ⊆ closure L[[A]] s := by
  intro a ha
  simp only [SetLike.mem_coe]
  let a' : L[[A]].Constants := Sum.inr ⟨a, ha⟩
  exact constants_mem a'

theorem closure_withConstants_eq :
    closure L[[A]] s =
      (closure L (A ∪ s)).withConstants ((A.subset_union_left).trans subset_closure) := by
  refine closure_eq_of_le ((A.subset_union_right).trans subset_closure) ?_
  rw [← (L.lhomWithConstants A).substructureReduct.le_iff_le]
  simp only [subset_closure, reduct_withConstants, closure_le, LHom.coe_substructureReduct,
    Set.union_subset_iff, and_true]
  exact subset_closure_withConstants

end Substructure

namespace Hom

/-- The restriction of a first-order hom to a substructure `s ⊆ M` gives a hom `s → N`. -/
@[simps!]
def domRestrict (f : M →[L] N) (p : L.Substructure M) : p →[L] N :=
  f.comp p.subtype.toHom

/-- A first-order hom `f : M → N` whose values lie in a substructure `p ⊆ N` can be restricted to a
hom `M → p`. -/
@[simps]
def codRestrict (p : L.Substructure N) (f : M →[L] N) (h : ∀ c, f c ∈ p) : M →[L] p where
  toFun c := ⟨f c, h c⟩
  map_fun' {n} f x := by aesop
  map_rel' {_} R x h := f.map_rel R x h

@[simp]
theorem comp_codRestrict (f : M →[L] N) (g : N →[L] P) (p : L.Substructure P) (h : ∀ b, g b ∈ p) :
    ((codRestrict p g h).comp f : M →[L] p) = codRestrict p (g.comp f) fun _ => h _ :=
  ext fun _ => rfl

@[simp]
theorem subtype_comp_codRestrict (f : M →[L] N) (p : L.Substructure N) (h : ∀ b, f b ∈ p) :
    p.subtype.toHom.comp (codRestrict p f h) = f :=
  ext fun _ => rfl

@[simp]
theorem domRestrict_comp_codRestrict (g : N →[L] P) (f : M →[L] N) (p : L.Substructure N)
    (h : ∀ b, f b ∈ p) :
    (g.domRestrict p).comp (f.codRestrict p h) = g.comp f :=
  rfl

/-- The range of a first-order hom `f : M → N` is a submodule of `N`.
See Note [range copy pattern]. -/
def range (f : M →[L] N) : L.Substructure N :=
  (map f ⊤).copy (Set.range f) Set.image_univ.symm

theorem range_coe (f : M →[L] N) : (range f : Set N) = Set.range f :=
  rfl

@[simp]
theorem mem_range {f : M →[L] N} {x} : x ∈ range f ↔ ∃ y, f y = x :=
  Iff.rfl

theorem range_eq_map (f : M →[L] N) : f.range = map f ⊤ := by
  ext
  simp

theorem mem_range_self (f : M →[L] N) (x : M) : f x ∈ f.range :=
  ⟨x, rfl⟩

@[simp]
theorem range_id : range (id L M) = ⊤ :=
  SetLike.coe_injective Set.range_id

theorem range_comp (f : M →[L] N) (g : N →[L] P) : range (g.comp f : M →[L] P) = map g (range f) :=
  SetLike.coe_injective (Set.range_comp g f)

theorem range_comp_le_range (f : M →[L] N) (g : N →[L] P) : range (g.comp f : M →[L] P) ≤ range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

theorem range_eq_top {f : M →[L] N} : range f = ⊤ ↔ Function.Surjective f := by
  rw [SetLike.ext'_iff, range_coe, coe_top, Set.range_eq_univ]

theorem range_le_iff_comap {f : M →[L] N} {p : L.Substructure N} : range f ≤ p ↔ comap f p = ⊤ := by
  rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]

theorem map_le_range {f : M →[L] N} {p : L.Substructure M} : map f p ≤ range f :=
  SetLike.coe_mono (Set.image_subset_range f p)

/-- The substructure of elements `x : M` such that `f x = g x` -/
def eqLocus (f g : M →[L] N) : Substructure L M where
  carrier := { x : M | f x = g x }
  fun_mem {n} fn x hx := by
    have h : f ∘ x = g ∘ x := by
      ext
      repeat' rw [Function.comp_apply]
      apply hx
    simp [h]

@[simp]
theorem mem_eqLocus {f g : M →[L] N} {x : M} : x ∈ f.eqLocus g ↔ f x = g x := Iff.rfl

/-- If two `L.Hom`s are equal on a set, then they are equal on its substructure closure. -/
theorem eqOn_closure {f g : M →[L] N} {s : Set M} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure L s) :=
  show closure L s ≤ f.eqLocus g from closure_le.2 h

theorem eq_of_eqOn_top {f g : M →[L] N} (h : Set.EqOn f g (⊤ : Substructure L M)) : f = g :=
  ext fun _ => h trivial

variable {s : Set M}

theorem eq_of_eqOn_dense (hs : closure L s = ⊤) {f g : M →[L] N} (h : s.EqOn f g) : f = g :=
  eq_of_eqOn_top <| hs ▸ eqOn_closure h

end Hom

namespace Substructure

theorem map_comap (S : L.Substructure N) (f : M →[L] N) :
    (S.comap f).map f = S ⊓ f.range := by
  rw [le_antisymm_iff]
  refine ⟨le_inf map_comap_le Hom.map_le_range, ?_⟩
  intro x ⟨x_in_S, x_in_range⟩
  rw [mem_map]
  rw [SetLike.mem_coe, Hom.mem_range] at x_in_range
  let ⟨y, hy⟩ := x_in_range
  use y
  rw [mem_comap, hy]
  trivial

end Substructure

namespace Embedding

/-- The restriction of a first-order embedding to a substructure `s ⊆ M` gives an embedding `s → N`.
-/
def domRestrict (f : M ↪[L] N) (p : L.Substructure M) : p ↪[L] N :=
  f.comp p.subtype

@[simp]
theorem domRestrict_apply (f : M ↪[L] N) (p : L.Substructure M) (x : p) : f.domRestrict p x = f x :=
  rfl

/-- A first-order embedding `f : M → N` whose values lie in a substructure `p ⊆ N` can be restricted
to an embedding `M → p`. -/
def codRestrict (p : L.Substructure N) (f : M ↪[L] N) (h : ∀ c, f c ∈ p) : M ↪[L] p where
  toFun := f.toHom.codRestrict p h
  inj' _ _ ab := f.injective (Subtype.mk_eq_mk.1 ab)
  map_fun' {_} F x := (f.toHom.codRestrict p h).map_fun' F x
  map_rel' {n} r x := by
    rw [← p.subtype.map_rel]
    change RelMap r (Hom.comp p.subtype.toHom (f.toHom.codRestrict p h) ∘ x) ↔ _
    rw [Hom.subtype_comp_codRestrict, ← f.map_rel]
    rfl

@[simp]
theorem codRestrict_apply (p : L.Substructure N) (f : M ↪[L] N) {h} (x : M) :
    (codRestrict p f h x : N) = f x :=
  rfl

@[simp]
theorem codRestrict_apply' (p : L.Substructure N) (f : M ↪[L] N) {h} (x : M) :
    codRestrict p f h x = ⟨f x, h x⟩ :=
  rfl

@[simp]
theorem comp_codRestrict (f : M ↪[L] N) (g : N ↪[L] P) (p : L.Substructure P) (h : ∀ b, g b ∈ p) :
    ((codRestrict p g h).comp f : M ↪[L] p) = codRestrict p (g.comp f) fun _ => h _ :=
  ext fun _ => rfl

@[simp]
theorem subtype_comp_codRestrict (f : M ↪[L] N) (p : L.Substructure N) (h : ∀ b, f b ∈ p) :
    p.subtype.comp (codRestrict p f h) = f :=
  ext fun _ => rfl

/-- The equivalence between a substructure `s` and its image `s.map f.toHom`, where `f` is an
  embedding. -/
noncomputable def substructureEquivMap (f : M ↪[L] N) (s : L.Substructure M) :
    s ≃[L] s.map f.toHom where
  toFun := codRestrict (s.map f.toHom) (f.domRestrict s) fun ⟨m, hm⟩ => ⟨m, hm, rfl⟩
  invFun n := ⟨Classical.choose n.2, (Classical.choose_spec n.2).1⟩
  left_inv := fun ⟨m, hm⟩ =>
    Subtype.mk_eq_mk.2
      (f.injective
        (Classical.choose_spec
            (codRestrict (s.map f.toHom) (f.domRestrict s) (fun ⟨m, hm⟩ => ⟨m, hm, rfl⟩)
                ⟨m, hm⟩).2).2)
  right_inv := fun ⟨_, hn⟩ => Subtype.mk_eq_mk.2 (Classical.choose_spec hn).2
  map_fun' {n} f x := by simp
  map_rel' {n} R x := by simp

@[simp]
theorem substructureEquivMap_apply (f : M ↪[L] N) (p : L.Substructure M) (x : p) :
    (f.substructureEquivMap p x : N) = f x :=
  rfl

@[simp]
theorem subtype_substructureEquivMap (f : M ↪[L] N) (s : L.Substructure M) :
    (subtype _).comp (f.substructureEquivMap s).toEmbedding = f.comp (subtype _) := by
  ext; rfl

/-- The equivalence between the domain and the range of an embedding `f`. -/
@[simps toEquiv_apply] noncomputable def equivRange (f : M ↪[L] N) : M ≃[L] f.toHom.range where
  toFun := codRestrict f.toHom.range f f.toHom.mem_range_self
  invFun n := Classical.choose n.2
  left_inv m :=
    f.injective (Classical.choose_spec (codRestrict f.toHom.range f f.toHom.mem_range_self m).2)
  right_inv := fun ⟨_, hn⟩ => Subtype.mk_eq_mk.2 (Classical.choose_spec hn)
  map_fun' {n} f x := by simp
  map_rel' {n} R x := by simp

@[simp]
theorem equivRange_apply (f : M ↪[L] N) (x : M) : (f.equivRange x : N) = f x :=
  rfl

@[simp]
theorem subtype_equivRange (f : M ↪[L] N) : (subtype _).comp f.equivRange.toEmbedding = f := by
  ext; rfl

end Embedding

namespace Equiv

theorem toHom_range (f : M ≃[L] N) : f.toHom.range = ⊤ := by
  ext n
  simp only [Hom.mem_range, coe_toHom, Substructure.mem_top, iff_true]
  exact ⟨f.symm n, apply_symm_apply _ _⟩

end Equiv

namespace Substructure

/-- The embedding associated to an inclusion of substructures. -/
def inclusion {S T : L.Substructure M} (h : S ≤ T) : S ↪[L] T :=
  S.subtype.codRestrict _ fun x => h x.2

@[simp]
theorem inclusion_self (S : L.Substructure M) : inclusion (le_refl S) = Embedding.refl L S := rfl

@[simp]
theorem coe_inclusion {S T : L.Substructure M} (h : S ≤ T) :
    (inclusion h : S → T) = Set.inclusion h :=
  rfl

theorem range_subtype (S : L.Substructure M) : S.subtype.toHom.range = S := by
  ext x
  simp only [Hom.mem_range, Embedding.coe_toHom, coe_subtype]
  refine ⟨?_, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  rintro ⟨⟨y, hy⟩, rfl⟩
  exact hy

@[simp]
lemma subtype_comp_inclusion {S T : L.Substructure M} (h : S ≤ T) :
    T.subtype.comp (inclusion h) = S.subtype := rfl

namespace Equiv

/-- Equivalence between equal substructures. -/
def ofEq {S T : L.Substructure M} (h : S = T) : S ≃[L] T :=
  { Equiv.setCongr (congr_arg _ h) with }

@[simp]
theorem ofEq_refl (S : L.Substructure M) : (ofEq (Eq.refl S)) = Equiv.refl L S := rfl

@[simp]
theorem symm_ofEq {S T : L.Substructure M} (h : S = T) :
    (ofEq h).symm = ofEq h.symm := rfl

@[simp]
theorem ofEq_comp_ofEq {S T U : L.Substructure M} (h : S = T) (h' : T = U) :
    (ofEq h').comp (ofEq h) = ofEq (h.trans h') := rfl

@[simp]
theorem ofEq_apply {S T : L.Substructure M} (h : S = T) {m : M} (hm : m ∈ S) :
    ofEq h ⟨m, hm⟩ = ⟨m, h ▸ hm⟩ := rfl

@[simp]
theorem subtype_comp_EquivOfEq {S T : L.Substructure M} (h : S = T) :
    T.subtype.comp (ofEq h).toEmbedding = S.subtype := rfl

@[simp]
theorem substructureEquivMap_refl (S : L.Substructure M) :
    (Embedding.refl L M).substructureEquivMap S = ofEq (map_id S).symm := by
  ext ⟨⟩
  simp only [Embedding.refl_toHom]
  rfl

@[simp]
theorem substructureEquivMap_comp_substructureEquivMap (f : M ↪[L] N) (g : N ↪[L] P)
    (S : L.Substructure M) : (g.substructureEquivMap (S.map f.toHom)).comp
    (f.substructureEquivMap S) = (ofEq (S.map_map ..).symm).comp
    ((g.comp f).substructureEquivMap S) := by
  apply Equiv.injective_toEmbedding
  apply (subtype _).comp_injective
  simp only [Equiv.comp_toEmbedding, ← Embedding.comp_assoc, Embedding.subtype_substructureEquivMap,
    subtype_comp_EquivOfEq]
  ext
  rfl

end Equiv

end Substructure

end Language

end FirstOrder
