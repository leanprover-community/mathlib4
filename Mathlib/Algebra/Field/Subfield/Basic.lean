/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Subfields

Let `K` be a division ring, for example a field.
This file concerns the "bundled" subfield type `Subfield K`, a type
whose terms correspond to subfields of `K`. Note we do not require the "subfields" to be
commutative, so they are really sub-division rings / skew fields. This is the preferred way to talk
about subfields in mathlib. Unbundled subfields (`s : Set K` and `IsSubfield s`)
are not in this file, and they will ultimately be deprecated.

We prove that subfields are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set K` to `Subfield K`, sending a subset of `K`
to the subfield it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(K : Type u) [DivisionRing K] (L : Type u) [DivisionRing L] (f g : K →+* L)`
`(A : Subfield K) (B : Subfield L) (s : Set K)`

* `instance : CompleteLattice (Subfield K)` : the complete lattice structure on the subfields.

* `Subfield.closure` : subfield closure of a set, i.e., the smallest subfield that includes the set.

* `Subfield.gi` : `closure : Set M → Subfield M` and coercion `(↑) : Subfield M → Set M`
  form a `GaloisInsertion`.

* `comap f B : Subfield K` : the preimage of a subfield `B` along the ring homomorphism `f`

* `map f A : Subfield L` : the image of a subfield `A` along the ring homomorphism `f`.

* `f.fieldRange : Subfield L` : the range of the ring homomorphism `f`.

* `eqLocusField f g : Subfield K` : given ring homomorphisms `f g : K →+* R`,
     the subfield of `K` where `f x = g x`

## Implementation notes

A subfield is implemented as a subring which is closed under `⁻¹`.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subfield's underlying set.

## Tags
subfield, subfields
-/


universe u v w

variable {K : Type u} {L : Type v} {M : Type w}
variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

namespace Subfield

variable (s t : Subfield K)

section DerivedFromSubfieldClass

/-- Product of a list of elements in a subfield is in the subfield. -/
protected theorem list_prod_mem {l : List K} : (∀ x ∈ l, x ∈ s) → l.prod ∈ s :=
  list_prod_mem

/-- Sum of a list of elements in a subfield is in the subfield. -/
protected theorem list_sum_mem {l : List K} : (∀ x ∈ l, x ∈ s) → l.sum ∈ s :=
  list_sum_mem

/-- Sum of a multiset of elements in a `Subfield` is in the `Subfield`. -/
protected theorem multiset_sum_mem (m : Multiset K) : (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
  multiset_sum_mem m

/-- Sum of elements in a `Subfield` indexed by a `Finset` is in the `Subfield`. -/
protected theorem sum_mem {ι : Type*} {t : Finset ι} {f : ι → K} (h : ∀ c ∈ t, f c ∈ s) :
    (∑ i ∈ t, f i) ∈ s :=
  sum_mem h

end DerivedFromSubfieldClass

/-! # top -/


/-- The subfield of `K` containing all elements of `K`. -/
instance : Top (Subfield K) :=
  ⟨{ (⊤ : Subring K) with inv_mem' := fun x _ => Subring.mem_top x }⟩

instance : Inhabited (Subfield K) :=
  ⟨⊤⟩

@[simp]
theorem mem_top (x : K) : x ∈ (⊤ : Subfield K) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : Subfield K) : Set K) = Set.univ :=
  rfl

/-- The ring equiv between the top element of `Subfield K` and `K`. -/
def topEquiv : (⊤ : Subfield K) ≃+* K :=
  Subsemiring.topEquiv

/-! # comap -/


variable (f : K →+* L)

/-- The preimage of a subfield along a ring homomorphism is a subfield. -/
def comap (s : Subfield L) : Subfield K :=
  { s.toSubring.comap f with
    inv_mem' := fun x hx =>
      show f x⁻¹ ∈ s by
        rw [map_inv₀ f]
        exact s.inv_mem hx }

@[simp]
theorem coe_comap (s : Subfield L) : (s.comap f : Set K) = f ⁻¹' s :=
  rfl

@[simp]
theorem mem_comap {s : Subfield L} {f : K →+* L} {x : K} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl

theorem comap_comap (s : Subfield M) (g : L →+* M) (f : K →+* L) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-! # map -/


/-- The image of a subfield along a ring homomorphism is a subfield. -/
def map (s : Subfield K) : Subfield L :=
  { s.toSubring.map f with
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, s.inv_mem hx, map_inv₀ f x⟩ }

@[simp]
theorem coe_map : (s.map f : Set L) = f '' s :=
  rfl

@[simp]
theorem mem_map {f : K →+* L} {s : Subfield K} {y : L} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y := by
  unfold map
  simp only [mem_mk, Subring.mem_mk, Subring.mem_toSubsemiring, Subring.mem_map, mem_toSubring]

theorem map_map (g : L →+* M) (f : K →+* L) : (s.map f).map g = s.map (g.comp f) :=
  SetLike.ext' <| Set.image_image _ _ _

theorem map_le_iff_le_comap {f : K →+* L} {s : Subfield K} {t : Subfield L} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff

theorem gc_map_comap (f : K →+* L) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

end Subfield

namespace RingHom

variable (g : L →+* M) (f : K →+* L)

/-! # range -/


/-- The range of a ring homomorphism, as a subfield of the target. See Note [range copy pattern]. -/
def fieldRange : Subfield L :=
  ((⊤ : Subfield K).map f).copy (Set.range f) Set.image_univ.symm

@[simp]
theorem coe_fieldRange : (f.fieldRange : Set L) = Set.range f :=
  rfl

@[simp]
theorem mem_fieldRange {f : K →+* L} {y : L} : y ∈ f.fieldRange ↔ ∃ x, f x = y :=
  Iff.rfl

theorem fieldRange_eq_map : f.fieldRange = Subfield.map f ⊤ := by
  ext
  simp

theorem map_fieldRange : f.fieldRange.map g = (g.comp f).fieldRange := by
  simpa only [fieldRange_eq_map] using (⊤ : Subfield K).map_map g f

theorem mem_fieldRange_self (x : K) : f x ∈ f.fieldRange :=
  exists_apply_eq_apply _ _

theorem fieldRange_eq_top_iff {f : K →+* L} :
    f.fieldRange = ⊤ ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans Set.range_eq_univ

/-- The range of a morphism of fields is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `Subtype.Fintype` if `L` is also a fintype. -/
instance fintypeFieldRange [Fintype K] [DecidableEq L] (f : K →+* L) : Fintype f.fieldRange :=
  Set.fintypeRange f

end RingHom

namespace Subfield

/-! # inf -/


/-- The inf of two subfields is their intersection. -/
instance : Min (Subfield K) :=
  ⟨fun s t =>
    { s.toSubring ⊓ t.toSubring with
      inv_mem' := fun _ hx =>
        Subring.mem_inf.mpr
          ⟨s.inv_mem (Subring.mem_inf.mp hx).1, t.inv_mem (Subring.mem_inf.mp hx).2⟩ }⟩

@[simp]
theorem coe_inf (p p' : Subfield K) : ((p ⊓ p' : Subfield K) : Set K) = p.carrier ∩ p'.carrier :=
  rfl

@[simp]
theorem mem_inf {p p' : Subfield K} {x : K} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

instance : InfSet (Subfield K) :=
  ⟨fun S =>
    { sInf (Subfield.toSubring '' S) with
      inv_mem' := by
        rintro x hx
        apply Subring.mem_sInf.mpr
        rintro _ ⟨p, p_mem, rfl⟩
        exact p.inv_mem (Subring.mem_sInf.mp hx p.toSubring ⟨p, p_mem, rfl⟩) }⟩

@[simp, norm_cast]
theorem coe_sInf (S : Set (Subfield K)) : ((sInf S : Subfield K) : Set K) = ⋂ s ∈ S, ↑s :=
  show ((sInf (Subfield.toSubring '' S) : Subring K) : Set K) = ⋂ s ∈ S, ↑s by
    ext x
    rw [Subring.coe_sInf, Set.mem_iInter, Set.mem_iInter]
    exact
      ⟨fun h s s' ⟨s_mem, s'_eq⟩ => h s.toSubring _ ⟨⟨s, s_mem, rfl⟩, s'_eq⟩,
        fun h s s' ⟨⟨s'', s''_mem, s_eq⟩, (s'_eq : ↑s = s')⟩ =>
        h s'' _ ⟨s''_mem, by simp [← s_eq, ← s'_eq]⟩⟩

theorem mem_sInf {S : Set (Subfield K)} {x : K} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Subring.mem_sInf.trans
    ⟨fun h p hp => h p.toSubring ⟨p, hp, rfl⟩, fun h _ ⟨p', hp', p_eq⟩ => p_eq ▸ h p' hp'⟩

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} {S : ι → Subfield K} : (↑(⨅ i, S i) : Set K) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

theorem mem_iInf {ι : Sort*} {S : ι → Subfield K} {x : K} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]
theorem sInf_toSubring (s : Set (Subfield K)) :
    (sInf s).toSubring = ⨅ t ∈ s, Subfield.toSubring t := by
  ext x
  simp [mem_sInf, ← sInf_image, Subring.mem_sInf]

theorem isGLB_sInf (S : Set (Subfield K)) : IsGLB S (sInf S) := by
  have : ∀ {s t : Subfield K}, (s : Set K) ≤ t ↔ s ≤ t := by simp [SetLike.coe_subset_coe]
  refine IsGLB.of_image this ?_
  convert isGLB_biInf (s := S) (f := SetLike.coe)
  exact coe_sInf _

/-- Subfields of a ring form a complete lattice. -/
instance : CompleteLattice (Subfield K) :=
  { completeLatticeOfInf (Subfield K) isGLB_sInf with
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩ }

/-! # subfield closure of a subset -/

/-- The `Subfield` generated by a set. -/
def closure (s : Set K) : Subfield K := sInf {S | s ⊆ S}

theorem mem_closure {x : K} {s : Set K} : x ∈ closure s ↔ ∀ S : Subfield K, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The subfield generated by a set includes the set. -/
@[simp, aesop safe 20 apply (rule_sets := [SetLike])]
theorem subset_closure {s : Set K} : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx

theorem subring_closure_le (s : Set K) : Subring.closure s ≤ (closure s).toSubring :=
  Subring.closure_le.mpr subset_closure

theorem notMem_of_notMem_closure {s : Set K} {P : K} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

@[deprecated (since := "2025-05-23")] alias not_mem_of_not_mem_closure := notMem_of_notMem_closure

/-- A subfield `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
theorem closure_le {s : Set K} {t : Subfield K} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h _ hx => mem_closure.mp hx t h⟩

/-- Subfield closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[gcongr]
theorem closure_mono ⦃s t : Set K⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure

theorem closure_eq_of_le {s : Set K} {t : Subfield K} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all
elements of the closure of `s`. -/
@[elab_as_elim]
theorem closure_induction {s : Set K} {p : ∀ x ∈ closure s, Prop}
    (mem : ∀ x hx, p x (subset_closure hx))
    (one : p 1 (one_mem _)) (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (neg : ∀ x hx, p x hx → p (-x) (neg_mem hx)) (inv : ∀ x hx, p x hx → p x⁻¹ (inv_mem hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (h : x ∈ closure s) : p x h :=
  letI : Subfield K :=
    { carrier := {x | ∃ hx, p x hx}
      mul_mem' := by rintro _ _ ⟨_, hx⟩ ⟨_, hy⟩; exact ⟨_, mul _ _ _ _ hx hy⟩
      one_mem' := ⟨_, one⟩
      add_mem' := by rintro _ _ ⟨_, hx⟩ ⟨_, hy⟩; exact ⟨_, add _ _ _ _ hx hy⟩
      zero_mem' := ⟨zero_mem _, by
        simp_rw [← @add_neg_cancel K _ 1]; exact add _ _ _ _ one (neg _ _ one)⟩
      neg_mem' := by rintro _ ⟨_, hx⟩; exact ⟨_, neg _ _ hx⟩
      inv_mem' := by rintro _ ⟨_, hx⟩; exact ⟨_, inv _ _ hx⟩ }
  ((closure_le (t := this)).2 (fun x hx ↦ ⟨_, mem x hx⟩) h).2

variable (K) in
/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure K _) (↑) where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

/-- Closure of a subfield `S` equals `S`. -/
@[simp]
theorem closure_eq (s : Subfield K) : closure (s : Set K) = s :=
  (Subfield.gi K).l_u_eq s

@[simp]
theorem closure_empty : closure (∅ : Set K) = ⊥ :=
  (Subfield.gi K).gc.l_bot

@[simp]
theorem closure_univ : closure (Set.univ : Set K) = ⊤ :=
  @coe_top K _ ▸ closure_eq ⊤

theorem closure_union (s t : Set K) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Subfield.gi K).gc.l_sup

theorem closure_iUnion {ι} (s : ι → Set K) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subfield.gi K).gc.l_iSup

theorem closure_sUnion (s : Set (Set K)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
  (Subfield.gi K).gc.l_sSup

theorem map_sup (s t : Subfield K) (f : K →+* L) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup

theorem map_iSup {ι : Sort*} (f : K →+* L) (s : ι → Subfield K) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

theorem map_inf (s t : Subfield K) (f : K →+* L) : (s ⊓ t).map f = s.map f ⊓ t.map f :=
  SetLike.coe_injective (Set.image_inter f.injective)

theorem map_iInf {ι : Sort*} [Nonempty ι] (f : K →+* L) (s : ι → Subfield K) :
    (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective f.injective).image_iInter_eq (s := SetLike.coe ∘ s)

theorem comap_inf (s t : Subfield L) (f : K →+* L) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf

theorem comap_iInf {ι : Sort*} (f : K →+* L) (s : ι → Subfield L) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
theorem map_bot (f : K →+* L) : (⊥ : Subfield K).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem comap_top (f : K →+* L) : (⊤ : Subfield L).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- The underlying set of a non-empty directed sSup of subfields is just a union of the subfields.
  Note that this fails without the directedness assumption (the union of two subfields is
  typically not a subfield) -/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subfield K} (hS : Directed (· ≤ ·) S)
    {x : K} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  let s : Subfield K :=
    { __ := Subring.copy _ _ (Subring.coe_iSup_of_directed hS).symm
      inv_mem' := fun _ hx ↦ have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (S i).inv_mem hi⟩ }
  have : iSup S = s := le_antisymm
    (iSup_le fun i ↦ le_iSup (fun i ↦ (S i : Set K)) i) (Set.iUnion_subset fun _ ↦ le_iSup S _)
  exact this ▸ Set.mem_iUnion

theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subfield K} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subfield K) : Set K) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]

theorem mem_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S)
    {x : K} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]

theorem coe_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set K) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

end Subfield

namespace RingHom

variable {s : Subfield K}

open Subfield

/-- Restriction of a ring homomorphism to its range interpreted as a subfield. -/
def rangeRestrictField (f : K →+* L) : K →+* f.fieldRange :=
  f.rangeSRestrict

@[simp]
theorem coe_rangeRestrictField (f : K →+* L) (x : K) : (f.rangeRestrictField x : L) = f x :=
  rfl

theorem rangeRestrictField_bijective (f : K →+* L) : Function.Bijective (rangeRestrictField f) :=
  (Equiv.ofInjective f f.injective).bijective

section eqLocus

variable {L : Type v} [Semiring L]

/-- The subfield of elements `x : R` such that `f x = g x`, i.e.,
the equalizer of f and g as a subfield of R -/
def eqLocusField (f g : K →+* L) : Subfield K where
  __ := (f : K →+* L).eqLocus g
  inv_mem' _ := eq_on_inv₀ f g
  carrier := { x | f x = g x }

/-- If two ring homomorphisms are equal on a set, then they are equal on its subfield closure. -/
theorem eqOn_field_closure {f g : K →+* L} {s : Set K} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocusField g from closure_le.2 h

theorem eq_of_eqOn_subfield_top {f g : K →+* L} (h : Set.EqOn f g (⊤ : Subfield K)) : f = g :=
  ext fun _ => h trivial

theorem eq_of_eqOn_of_field_closure_eq_top {s : Set K} (hs : closure s = ⊤) {f g : K →+* L}
    (h : s.EqOn f g) : f = g :=
  eq_of_eqOn_subfield_top <| hs ▸ eqOn_field_closure h

end eqLocus

theorem field_closure_preimage_le (f : K →+* L) (s : Set L) :
    closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a ring homomorphism of the subfield generated by a set equals
the subfield generated by the image of the set. -/
theorem map_field_closure (f : K →+* L) (s : Set K) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subfield.gi L).gc (Subfield.gi K).gc
    fun _ ↦ rfl

end RingHom

namespace Subfield

open RingHom

/-- The ring homomorphism associated to an inclusion of subfields. -/
def inclusion {S T : Subfield K} (h : S ≤ T) : S →+* T :=
  S.subtype.codRestrict _ fun x => h x.2

@[simp]
theorem fieldRange_subtype (s : Subfield K) : s.subtype.fieldRange = s :=
  SetLike.ext' <| (coe_rangeS _).trans Subtype.range_coe

end Subfield

namespace RingEquiv

variable {s t : Subfield K}

/-- Makes the identity isomorphism from a proof two subfields of a multiplicative
    monoid are equal. -/
def subfieldCongr (h : s = t) : s ≃+* t :=
  { Equiv.setCongr <| SetLike.ext'_iff.1 h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

end RingEquiv

namespace Subfield

variable {s : Set K}

theorem closure_preimage_le (f : K →+* L) (s : Set L) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

section Commutative

variable {K : Type u} [Field K] (s : Subfield K)

/-- Product of a multiset of elements in a subfield is in the subfield. -/
protected theorem multiset_prod_mem (m : Multiset K) : (∀ a ∈ m, a ∈ s) → m.prod ∈ s :=
  multiset_prod_mem m

/-- Product of elements of a subfield indexed by a `Finset` is in the subfield. -/
protected theorem prod_mem {ι : Type*} {t : Finset ι} {f : ι → K} (h : ∀ c ∈ t, f c ∈ s) :
    (∏ i ∈ t, f i) ∈ s :=
  prod_mem h

instance toAlgebra : Algebra s K :=
  RingHom.toAlgebra s.subtype

/-- The `Subfield` generated by a set in a field. -/
private def commClosure (s : Set K) : Subfield K where
  carrier := {z : K | ∃ x ∈ Subring.closure s, ∃ y ∈ Subring.closure s, x / y = z}
  zero_mem' := ⟨0, Subring.zero_mem _, 1, Subring.one_mem _, div_one _⟩
  one_mem' := ⟨1, Subring.one_mem _, 1, Subring.one_mem _, div_one _⟩
  neg_mem' {x} := by
    rintro ⟨y, hy, z, hz, x_eq⟩
    exact ⟨-y, Subring.neg_mem _ hy, z, hz, x_eq ▸ neg_div _ _⟩
  inv_mem' x := by rintro ⟨y, hy, z, hz, x_eq⟩; exact ⟨z, hz, y, hy, x_eq ▸ (inv_div _ _).symm⟩
  add_mem' x_mem y_mem := by
    -- Use `id` in the next 2 `obtain`s so that assumptions stay there for the `rwa`s below
    obtain ⟨nx, hnx, dx, hdx, rfl⟩ := id x_mem
    obtain ⟨ny, hny, dy, hdy, rfl⟩ := id y_mem
    by_cases hx0 : dx = 0; · rwa [hx0, div_zero, zero_add]
    by_cases hy0 : dy = 0; · rwa [hy0, div_zero, add_zero]
    exact
      ⟨nx * dy + dx * ny, Subring.add_mem _ (Subring.mul_mem _ hnx hdy) (Subring.mul_mem _ hdx hny),
        dx * dy, Subring.mul_mem _ hdx hdy, (div_add_div nx ny hx0 hy0).symm⟩
  mul_mem' := by
    rintro _ _ ⟨nx, hnx, dx, hdx, rfl⟩ ⟨ny, hny, dy, hdy, rfl⟩
    exact ⟨nx * ny, Subring.mul_mem _ hnx hny, dx * dy, Subring.mul_mem _ hdx hdy,
      (div_mul_div_comm _ _ _ _).symm⟩

private theorem commClosure_eq_closure {s : Set K} : commClosure s = closure s :=
  le_antisymm
    (fun _ ⟨_, hy, _, hz, eq⟩ ↦ eq ▸ div_mem (subring_closure_le s hy) (subring_closure_le s hz))
    (closure_le.mpr fun x hx ↦ ⟨x, Subring.subset_closure hx, 1, Subring.one_mem _, div_one x⟩)

theorem mem_closure_iff {s : Set K} {x} :
    x ∈ closure s ↔ ∃ y ∈ Subring.closure s, ∃ z ∈ Subring.closure s, y / z = x := by
  rw [← commClosure_eq_closure]; rfl

end Commutative

end Subfield

namespace Subfield

theorem map_comap_eq (f : K →+* L) (s : Subfield L) : (s.comap f).map f = s ⊓ f.fieldRange :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

theorem map_comap_eq_self
    {f : K →+* L} {s : Subfield L} (h : s ≤ f.fieldRange) : (s.comap f).map f = s := by
  simpa only [inf_of_le_left h] using map_comap_eq f s

theorem map_comap_eq_self_of_surjective
    {f : K →+* L} (hf : Function.Surjective f) (s : Subfield L) : (s.comap f).map f = s :=
  SetLike.coe_injective (Set.image_preimage_eq _ hf)

theorem comap_map (f : K →+* L) (s : Subfield K) : (s.map f).comap f = s :=
  SetLike.coe_injective (Set.preimage_image_eq _ f.injective)

end Subfield

/-! ## Actions by `Subfield`s

These are just copies of the definitions about `Subsemiring` starting from
`Subsemiring.MulAction`.
-/
section Actions

namespace Subfield

variable {X Y}

/-- The action by a subfield is the action by the underlying field. -/
instance [SMul K X] (F : Subfield K) : SMul F X :=
  inferInstanceAs (SMul F.toSubsemiring X)

theorem smul_def [SMul K X] {F : Subfield K} (g : F) (m : X) : g • m = (g : K) • m :=
  rfl

instance smulCommClass_left [SMul K Y] [SMul X Y] [SMulCommClass K X Y] (F : Subfield K) :
    SMulCommClass F X Y :=
  inferInstanceAs (SMulCommClass F.toSubsemiring X Y)

instance smulCommClass_right [SMul X Y] [SMul K Y] [SMulCommClass X K Y] (F : Subfield K) :
    SMulCommClass X F Y :=
  inferInstanceAs (SMulCommClass X F.toSubsemiring Y)

/-- Note that this provides `IsScalarTower F K K` which is needed by `smul_mul_assoc`. -/
instance [SMul X Y] [SMul K X] [SMul K Y] [IsScalarTower K X Y] (F : Subfield K) :
    IsScalarTower F X Y :=
  inferInstanceAs (IsScalarTower F.toSubsemiring X Y)

instance [SMul K X] [FaithfulSMul K X] (F : Subfield K) : FaithfulSMul F X :=
  inferInstanceAs (FaithfulSMul F.toSubsemiring X)

/-- The action by a subfield is the action by the underlying field. -/
instance [MulAction K X] (F : Subfield K) : MulAction F X :=
  inferInstanceAs (MulAction F.toSubsemiring X)

/-- The action by a subfield is the action by the underlying field. -/
instance [AddMonoid X] [DistribMulAction K X] (F : Subfield K) : DistribMulAction F X :=
  inferInstanceAs (DistribMulAction F.toSubsemiring X)

/-- The action by a subfield is the action by the underlying field. -/
instance [Monoid X] [MulDistribMulAction K X] (F : Subfield K) : MulDistribMulAction F X :=
  inferInstanceAs (MulDistribMulAction F.toSubsemiring X)

/-- The action by a subfield is the action by the underlying field. -/
instance [Zero X] [SMulWithZero K X] (F : Subfield K) : SMulWithZero F X :=
  inferInstanceAs (SMulWithZero F.toSubsemiring X)

/-- The action by a subfield is the action by the underlying field. -/
instance [Zero X] [MulActionWithZero K X] (F : Subfield K) : MulActionWithZero F X :=
  inferInstanceAs (MulActionWithZero F.toSubsemiring X)

/-- The action by a subfield is the action by the underlying field. -/
instance [AddCommMonoid X] [Module K X] (F : Subfield K) : Module F X :=
  inferInstanceAs (Module F.toSubsemiring X)

/-- The action by a subfield is the action by the underlying field. -/
instance [Semiring X] [MulSemiringAction K X] (F : Subfield K) : MulSemiringAction F X :=
  inferInstanceAs (MulSemiringAction F.toSubsemiring X)

end Subfield

end Actions
