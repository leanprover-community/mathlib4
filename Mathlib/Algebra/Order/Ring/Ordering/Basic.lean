/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
module

public import Mathlib.Algebra.Order.Ring.Ordering.Defs
public import Mathlib.Algebra.Ring.Semireal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Ring orderings

We prove basic properties of (pre)orderings on rings and their supports.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

@[expose] public section

variable {R : Type*} [CommRing R] {P : RingPreordering R}

/-!
### Preorderings
-/

namespace RingPreordering

theorem toSubsemiring_le_toSubsemiring {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring ≤ P₂.toSubsemiring ↔ P₁ ≤ P₂ := .rfl

theorem toSubsemiring_lt_toSubsemiring {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring < P₂.toSubsemiring ↔ P₁ < P₂ := .rfl

@[gcongr] alias ⟨_, GCongr.toSubsemiring_le_toSubsemiring⟩ := toSubsemiring_le_toSubsemiring
@[gcongr] alias ⟨_, GCongr.toSubsemiring_lt_toSubsemiring⟩ := toSubsemiring_lt_toSubsemiring

@[mono]
theorem toSubsemiring_mono : Monotone (toSubsemiring : RingPreordering R → _) :=
  fun _ _ => id

@[mono]
theorem toSubsemiring_strictMono : StrictMono (toSubsemiring : RingPreordering R → _) :=
  fun _ _ => id

@[aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem unitsInv_mem {a : Rˣ} (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  have : (a * (a⁻¹ * a⁻¹) : R) ∈ P := by aesop (config := { enableSimp := false })
  simp_all

@[aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem inv_mem {F : Type*} [Field F] {P : RingPreordering F} {a : F} (ha : a ∈ P) :
    a⁻¹ ∈ P := by
  have mem : a * (a⁻¹ * a⁻¹) ∈ P := by aesop
  field_simp at mem
  simp_all

@[aesop unsafe 80% apply (rule_sets := [SetLike])]
theorem mem_of_isSumSq {x : R} (hx : IsSumSq x) : x ∈ P := by
  induction hx using IsSumSq.rec' <;> aesop

section mk'

variable {R : Type*} [CommRing R] {P : Set R} {add} {mul} {sq} {neg_one}

/-- Construct a preordering from a minimal set of axioms. -/
def mk' {R : Type*} [CommRing R] (P : Set R)
    (add : ∀ {x y : R}, x ∈ P → y ∈ P → x + y ∈ P)
    (mul : ∀ {x y : R}, x ∈ P → y ∈ P → x * y ∈ P)
    (sq : ∀ x : R, x * x ∈ P)
    (neg_one : -1 ∉ P) :
    RingPreordering R where
  carrier := P
  add_mem' {x y} := by simpa using add
  mul_mem' {x y} := by simpa using mul
  zero_mem' := by simpa using sq 0
  one_mem' := by simpa using sq 1

@[simp] theorem mem_mk' {x : R} : x ∈ mk' P add mul sq neg_one ↔ x ∈ P := .rfl
@[simp, norm_cast] theorem coe_mk' : mk' P add mul sq neg_one = P := rfl

end mk'

/-!
### Supports
-/

section ne_top

variable (P)

theorem one_notMem_supportAddSubgroup : 1 ∉ P.supportAddSubgroup :=
  fun h => RingPreordering.neg_one_notMem P h.2

theorem one_notMem_support [P.HasIdealSupport] : 1 ∉ P.support := by
  simpa using one_notMem_supportAddSubgroup P

theorem supportAddSubgroup_ne_top : P.supportAddSubgroup ≠ ⊤ :=
  fun h => RingPreordering.neg_one_notMem P (by simp [h] : 1 ∈ P.supportAddSubgroup).2

theorem support_ne_top [P.HasIdealSupport] : P.support ≠ ⊤ := by
  apply_fun Submodule.toAddSubgroup
  simpa using supportAddSubgroup_ne_top P

/-- Constructor for IsOrdering that doesn't require `ne_top'`. -/
theorem IsOrdering.mk' [HasMemOrNegMem P]
    (h : ∀ {x y}, x * y ∈ P.support → x ∈ P.support ∨ y ∈ P.support) : P.IsOrdering where
  ne_top' := support_ne_top P
  mem_or_mem' := h

end ne_top

namespace HasIdealSupport

theorem smul_mem [P.HasIdealSupport]
    (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : x * a ∈ P := by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

theorem neg_smul_mem [P.HasIdealSupport]
    (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : -(x * a) ∈ P := by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

end HasIdealSupport

theorem hasIdealSupport_of_isUnit_two (h : IsUnit (2 : R)) : P.HasIdealSupport := by
  rw [hasIdealSupport_iff]
  intro x a _ _
  rcases h.exists_right_inv with ⟨half, h2⟩
  set y := (1 + x) * half
  set z := (1 - x) * half
  rw [show x = y ^ 2 - z ^ 2 by
    linear_combination (- x - x * half * 2) * h2]
  ring_nf
  aesop (add simp sub_eq_add_neg)

instance [h : Fact (IsUnit (2 : R))] : P.HasIdealSupport := hasIdealSupport_of_isUnit_two h.out

section Field

variable {F : Type*} [Field F] (P : RingPreordering F)

variable {P} in
@[aesop unsafe 70% apply]
protected theorem eq_zero_of_mem_of_neg_mem {x} (h : x ∈ P) (h2 : -x ∈ P) : x = 0 := by
  by_contra
  have mem : -x * x⁻¹ ∈ P := by aesop (erase simp neg_mul)
  field_simp at mem
  exact RingPreordering.neg_one_notMem P mem

theorem supportAddSubgroup_eq_bot : P.supportAddSubgroup = ⊥ := by
  ext; aesop (add simp mem_supportAddSubgroup)

instance : P.HasIdealSupport where
  smul_mem_support := by simp [supportAddSubgroup_eq_bot]

@[simp] theorem support_eq_bot : P.support = ⊥ := by
  simpa [← Submodule.toAddSubgroup_inj] using supportAddSubgroup_eq_bot P

instance : P.support.IsPrime := by simpa using Ideal.bot_prime

end Field

theorem isOrdering_iff :
    P.IsOrdering ↔ ∀ a b : R, -(a * b) ∈ P → a ∈ P ∨ b ∈ P := by
  refine ⟨fun _ a b _ => ?_, fun h => ?_⟩
  · by_contra
    have : a * b ∈ P := by simpa using mul_mem (by aesop : -a ∈ P) (by aesop : -b ∈ P)
    have : a ∈ P.support ∨ b ∈ P.support :=
      Ideal.IsPrime.mem_or_mem inferInstance (by simp_all [mem_support])
    simp_all [mem_support]
  · have : HasMemOrNegMem P := ⟨by simp [h]⟩
    refine IsOrdering.mk' P (fun {x y} _ => ?_)
    by_contra
    have := h (-x) y
    have := h (-x) (-y)
    have := h x y
    have := h x (-y)
    cases (by aesop : x ∈ P ∨ -x ∈ P) <;> simp_all [mem_support]

/-!
### Supports
-/

@[gcongr]
theorem supportAddSubgroup_mono {Q : RingPreordering R} (h : P ≤ Q) :
    P.supportAddSubgroup ≤ Q.supportAddSubgroup :=
  fun _ ↦ by aesop (add simp mem_supportAddSubgroup)

@[gcongr]
theorem support_mono {Q : RingPreordering R} [P.HasIdealSupport] [Q.HasIdealSupport] (h : P ≤ Q) :
    P.support ≤ Q.support := fun _ ↦ by aesop (add simp mem_support)

/-! ## Order operations -/

section Inf
variable (P₁ P₂ : RingPreordering R)

instance : Min (RingPreordering R) where
  min P₁ P₂ := { toSubsemiring := min P₁.toSubsemiring P₂.toSubsemiring }

@[simp]
theorem toSubsemiring_inf : (P₁ ⊓ P₂).toSubsemiring = P₁.toSubsemiring ⊓ P₂.toSubsemiring := rfl
@[simp] theorem mem_inf (x : R) : x ∈ P₁ ⊓ P₂ ↔ x ∈ P₁ ∧ x ∈ P₂ := .rfl
@[simp, norm_cast] theorem coe_inf : ↑(P₁ ⊓ P₂) = (P₁ ∩ P₂ : Set R) := rfl

@[simp]
theorem supportAddSubgroup_inf :
    (P₁ ⊓ P₂).supportAddSubgroup = P₁.supportAddSubgroup ⊓ P₂.supportAddSubgroup := by
  aesop (add simp mem_supportAddSubgroup)

instance [P₁.HasIdealSupport] [P₂.HasIdealSupport] : (P₁ ⊓ P₂).HasIdealSupport := by
  simp_all [hasIdealSupport_iff]

@[simp]
theorem support_inf [P₁.HasIdealSupport] [P₂.HasIdealSupport] :
    (P₁ ⊓ P₂).support = P₁.support ⊓ P₂.support := by
  apply_fun Submodule.toAddSubgroup using Submodule.toAddSubgroup_injective
  simpa [-Submodule.toAddSubgroup_inj] using supportAddSubgroup_inf (P₁ := P₁) (P₂ := P₂)

instance : SemilatticeInf (RingPreordering R) where
  inf := (· ⊓ ·)
  inf_le_left _ _ := by simp_all [← SetLike.coe_subset_coe]
  inf_le_right _ _ := by simp_all [← SetLike.coe_subset_coe]
  le_inf _ _ _ _ _ := by simp_all [← SetLike.coe_subset_coe]

end Inf

section sInf
variable {S : Set (RingPreordering R)} (hS : S.Nonempty)

variable (S) in
/-- The intersection of a nonempty set of preorderings is a ring preordering. -/
def sInf : RingPreordering R where
  __ := InfSet.sInf (RingPreordering.toSubsemiring '' S)
  mem_of_isSquare' x := by aesop (add simp Submonoid.mem_iInf)
  neg_one_notMem' := by simpa [Submonoid.mem_iInf] using
    ⟨_, Set.Nonempty.some_mem hS, RingPreordering.neg_one_notMem _⟩

@[simp]
theorem sInf_toSubsemiring :
  (sInf S hS).toSubsemiring = InfSet.sInf (RingPreordering.toSubsemiring '' S) := rfl

@[simp, norm_cast]
theorem coe_sInf : (sInf S hS : Set R) = ⋂ P ∈ S, P := by
  have : (sInf S hS : Set R) = ⋂ P ∈ (RingPreordering.toSubsemiring '' S), P := rfl
  simp_all

@[simp]
theorem mem_sInf (x : R) : x ∈ sInf S hS ↔ ∀ p ∈ S, x ∈ p := by
  rw [show x ∈ sInf S hS ↔ x ∈ (sInf S hS : Set R) by simp [-coe_sInf]]
  simp_all

@[simp]
theorem supportAddSubgroup_sInf :
    (sInf S hS).supportAddSubgroup = InfSet.sInf (supportAddSubgroup '' S) := by
  aesop (add simp mem_supportAddSubgroup)

protected theorem HasIdealSupport.sInf (h : ∀ P ∈ S, P.HasIdealSupport) :
    (sInf S hS).HasIdealSupport := by
  simp_all [hasIdealSupport_iff]

@[simp]
theorem support_sInf (h : ∀ P ∈ S, P.HasIdealSupport) :
    letI _ := HasIdealSupport.sInf hS h
    (sInf S hS).support =
    InfSet.sInf {s | ∃ P, ∃ hP : P ∈ S, letI _ := h _ hP; s = P.support} := by
  aesop (add simp mem_support)

theorem sInf_le {P} (hP : P ∈ S) : sInf S hS ≤ P := by
  rw [← SetLike.coe_subset_coe]
  simpa using Set.biInter_subset_of_mem hP

theorem le_sInf {P} (hP : ∀ Q ∈ S, P ≤ Q) : P ≤ sInf S hS := by
  rw [← SetLike.coe_subset_coe]
  simpa using Set.subset_iInter₂ hP

end sInf

section Bot
variable [IsSemireal R]

instance : Bot (RingPreordering R) where
  bot.toSubsemiring := Subsemiring.sumSq R
  bot.neg_one_notMem' := by simpa using IsSemireal.not_isSumSq_neg_one

@[simp] theorem bot_toSubsemiring : (⊥ : RingPreordering R).toSubsemiring = .sumSq R := rfl

@[simp] theorem mem_bot (a) : a ∈ (⊥ : RingPreordering R) ↔ IsSumSq a :=
  show a ∈ Subsemiring.sumSq R ↔ IsSumSq a by simp

@[simp, norm_cast] theorem coe_bot : (⊥ : RingPreordering R) = {x : R | IsSumSq x} :=
  show Subsemiring.sumSq R = {x : R | IsSumSq x} by simp

instance : OrderBot (RingPreordering R) where
  bot_le P a := by aesop

end Bot

theorem nonempty_ringPreordering_iff_isSemireal : Nonempty (RingPreordering R) ↔ IsSemireal R where
  mp h := Nonempty.elim h fun P ↦ by
    refine ⟨fun {x} hx hx₂ ↦ ?_⟩
    apply P.neg_one_notMem
    rw [show -1 = x by linear_combination -hx₂]
    aesop
  mpr h := ⟨⊥⟩

theorem isSemireal (P : RingPreordering R) : IsSemireal R :=
  nonempty_ringPreordering_iff_isSemireal.mp ⟨P⟩

section sSup
variable {S : Set (RingPreordering R)} (hS : S.Nonempty) (hSd : DirectedOn (· ≤ ·) S)

-- TODO : define under `isSemireal` and add dummy valued when not directed
--        use class `CompletePartialOrder`

variable (S) in
/-- The union of a directed set of preorderings is a preordering. -/
def sSup : RingPreordering R where
  __ := SupSet.sSup (toSubsemiring '' S)
  mem_of_isSquare' x := by
    have : DirectedOn (· ≤ ·) (toSubsemiring '' S) := directedOn_image.mpr hSd
    aesop (add simp Subsemiring.mem_sSup_of_directedOn,
               unsafe forward (Set.Nonempty.some_mem hS))
  neg_one_notMem' := by
    have : DirectedOn (· ≤ ·) (toSubsemiring '' S) := directedOn_image.mpr hSd
    aesop (add simp Subsemiring.mem_sSup_of_directedOn,
               unsafe forward (Set.Nonempty.some_mem hS))

@[simp]
theorem sSup_toSubsemiring :
    (sSup S hS hSd).toSubsemiring = SupSet.sSup (RingPreordering.toSubsemiring '' S) := rfl

@[simp, norm_cast]
theorem coe_sSup : (sSup S hS hSd : Set R) = ⋃ P ∈ S, P := by
  have : (sSup S hS hSd : Set R) = SupSet.sSup (toSubsemiring '' S) := rfl
  simp_all [Subsemiring.coe_sSup_of_directedOn (by aesop) <| directedOn_image.mpr hSd]

@[simp]
theorem mem_sSup {x : R} : x ∈ sSup S hS hSd ↔ ∃ p ∈ S, x ∈ p := by
  rw [show x ∈ sSup S hS hSd ↔ x ∈ (sSup S hS hSd : Set R) by simp [-coe_sSup]]
  simp_all

theorem le_sSup {P} (hP : P ∈ S) : P ≤ sSup S hS hSd := by
  rw [← SetLike.coe_subset_coe]
  simpa using Set.subset_biUnion_of_mem hP

theorem sSup_le {P} (hP : ∀ Q ∈ S, Q ≤ P) : sSup S hS hSd ≤ P := by
  rw [← SetLike.coe_subset_coe]
  simpa using Set.iUnion₂_subset hP

include hSd in
theorem directedOn_image_supportAddSubgroup :
    DirectedOn (fun x1 x2 ↦ x1 ≤ x2) (supportAddSubgroup '' S) := by
  rw [directedOn_image]
  intro _ hx _ hy
  rcases hSd _ hx _ hy with ⟨z, _⟩
  exact ⟨z, by aesop (add safe apply supportAddSubgroup_mono)⟩

@[simp]
theorem supportAddSubgroup_sSup :
    (sSup S hS hSd).supportAddSubgroup = SupSet.sSup (supportAddSubgroup '' S) := by
  ext x
  rw [AddSubgroup.mem_sSup_of_directedOn (by simp_all) (directedOn_image_supportAddSubgroup hSd)]
  simp only [mem_supportAddSubgroup, mem_sSup, Set.mem_image, exists_exists_and_eq_and]
  refine ⟨?_, by aesop⟩
  rintro ⟨⟨_, hs₁, _⟩, ⟨_, hs₂, _⟩⟩
  rcases hSd _ hs₁ _ hs₂ with ⟨s, hs⟩
  exact ⟨s, by aesop⟩

protected theorem HasIdealSupport.sSup (h : ∀ P ∈ S, P.HasIdealSupport) :
    (sSup S hS hSd).HasIdealSupport := by
  simp_rw [hasIdealSupport_iff, mem_sSup] at *
  rintro x a ⟨P, hP, hP'⟩ ⟨Q, hQ, hQ'⟩
  rcases hSd _ hP _ hQ with ⟨R, hR, hPR, hQR⟩
  have := h _ hR x a (hPR hP') (hQR hQ')
  aesop

@[simp]
theorem support_sSup (h : ∀ P ∈ S, P.HasIdealSupport) :
    letI _ := HasIdealSupport.sSup hS hSd h
    (sSup S hS hSd).support =
    SupSet.sSup {s | ∃ P, ∃ hP : P ∈ S, letI _ := h _ hP; s = P.support} := by
  generalize_proofs
  ext x
  have : x ∈ (sSup S hS hSd).support ↔ x ∈ SupSet.sSup (supportAddSubgroup '' S) := by
    simp [← supportAddSubgroup_sSup (hS := hS) (hSd := hSd)]
  rw [this,
      AddSubgroup.mem_sSup_of_directedOn (by simp_all) (directedOn_image_supportAddSubgroup hSd),
      Submodule.mem_sSup_of_directed]
  · aesop
  · rcases hS with ⟨P, hP⟩
    exact ⟨let _ := h P hP; P.support, by aesop⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rcases hSd _ hx _ hy with ⟨z, hz, _, _⟩
    let _ := h _ hx
    let _ := h _ hy
    let _ := h _ hz
    exact ⟨z.support, by aesop (add safe apply support_mono)⟩

end sSup

theorem nonempty_chain_bddAbove {S : Set (RingPreordering R)}
    (hS : S.Nonempty) (hSc : IsChain (· ≤ ·) S) : BddAbove S :=
  ⟨sSup S hS <| IsChain.directedOn hSc, fun _ => le_sSup hS <| IsChain.directedOn hSc⟩

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-! ## comap -/

section comap

variable (f : A →+* B) (P : RingPreordering B)

/-- The preimage of a preordering along a ring homomorphism is a preordering. -/
def comap : RingPreordering A where
  __ := P.toSubsemiring.comap f
  mem_of_isSquare' := by aesop

@[simp]
theorem coe_comap : (P.comap f : Set A) = f ⁻¹' P := rfl

@[simp]
theorem mem_comap (x) : x ∈ P.comap f ↔ f x ∈ P := .rfl

theorem comap_comap (Q : RingPreordering C) (g : B →+* C) :
    (Q.comap g).comap f = Q.comap (g.comp f) := rfl

instance [HasMemOrNegMem P] : HasMemOrNegMem (P.comap f) where
  mem_or_neg_mem x := by have := mem_or_neg_mem P (f x); aesop

theorem mem_comap_supportAddSubgroup (x) :
    x ∈ (P.comap f).supportAddSubgroup ↔ f x ∈ P.supportAddSubgroup := by
  simp [mem_supportAddSubgroup]

@[simp]
theorem comap_supportAddSubgroup :
    (P.comap f).supportAddSubgroup = (P.supportAddSubgroup).comap f := by
  ext; simp [mem_comap_supportAddSubgroup]

instance [P.HasIdealSupport] : HasIdealSupport (P.comap f) where
  smul_mem_support x a ha := by have := smul_mem_support P (f x) (by simpa using ha); simp_all

theorem mem_comap_support [P.HasIdealSupport] (x) :
    x ∈ (P.comap f).support ↔ f x ∈ P.support := by
  simpa using mem_comap_supportAddSubgroup _ P _

@[simp]
theorem comap_support [P.HasIdealSupport] :
    (P.comap f).support = (P.support).comap f := by ext; simp [mem_comap_support]

/-- The preimage of an ordering along a ring homomorphism is an ordering. -/
instance [P.IsOrdering] : IsOrdering (comap f P) where
  __ : (P.comap f).support.IsPrime := by rw [comap_support]; infer_instance

end comap

/-! ## map -/

section map

variable {f : A →+* B} {P : RingPreordering A} (hf : Function.Surjective f)
    (hsupp : (RingHom.ker f : Set A) ⊆ P.supportAddSubgroup)

variable (f P) in
/-- The image of a preordering `P` along a surjective ring homomorphism
with kernel contained in the support of `P` is a preordering. -/
def map : RingPreordering B where
  __ := P.toSubsemiring.map f
  mem_of_isSquare' hx := by
    rcases isSquare_subset_image_isSquare hf hx with ⟨x, hx, hfx⟩
    exact ⟨x, by aesop⟩
  neg_one_notMem' := fun ⟨x', hx', _⟩ => by
    have : -(x' + 1) + x' ∈ P := add_mem (hsupp (show f (x' + 1) = 0 by simp_all)).2 hx'
    aesop

@[simp]
theorem coe_map : (map f P hf hsupp : Set B) = f '' P := rfl

@[simp]
theorem mem_map (y) : y ∈ map f P hf hsupp ↔ ∃ x ∈ P, f x = y := .rfl

instance [HasMemOrNegMem P] : HasMemOrNegMem (map f P hf hsupp) where
  mem_or_neg_mem x := by
    obtain ⟨x', rfl⟩ := hf x
    have := mem_or_neg_mem P x'
    aesop

theorem mem_map_supportAddSubgroup (x) :
    x ∈ (map f P hf hsupp).supportAddSubgroup ↔ ∃ y ∈ P.supportAddSubgroup, f y = x := by
  refine ⟨fun ⟨⟨a, ⟨ha₁, ha₂⟩⟩, ⟨b, ⟨hb₁, hb₂⟩⟩⟩ => ?_, by aesop (add simp mem_supportAddSubgroup)⟩
  have : -(a + b) + b ∈ P := by exact add_mem (hsupp (show f (a + b) = 0 by simp_all)).2 hb₁
  aesop (add simp mem_supportAddSubgroup)

@[simp]
theorem map_supportAddSubgroup :
    (map f P hf hsupp).supportAddSubgroup = (P.supportAddSubgroup).map f := by
  ext; simp [mem_map_supportAddSubgroup]

instance [P.HasIdealSupport] : HasIdealSupport <| map f P hf hsupp where
  smul_mem_support x a ha := by
    rw [mem_map_supportAddSubgroup] at ha
    rcases ha with ⟨a', ha', rfl⟩
    rcases hf x with ⟨x', rfl⟩
    have := smul_mem_support P x' ha'
    aesop

theorem mem_map_support [P.HasIdealSupport] (x) :
    x ∈ (map f P hf hsupp).support ↔ ∃ y ∈ P.support, f y = x := by
  simpa using mem_map_supportAddSubgroup ..

@[simp]
theorem map_support [P.HasIdealSupport] :
    (map f P hf hsupp).support = (P.support).map f := by
  ext; simp [mem_map_support, Ideal.mem_map_iff_of_surjective f hf]

/-- The image of an ordering `P` along a surjective ring homomorphism
with kernel contained in the support of `P` is an ordering. -/
instance [P.IsOrdering] : IsOrdering <| map f P hf hsupp where
  __ : (map f P hf hsupp).support.IsPrime := by
    simpa using Ideal.map_isPrime_of_surjective hf hsupp

end map

end RingPreordering
