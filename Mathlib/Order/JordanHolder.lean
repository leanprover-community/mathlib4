/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Order.Lattice
import Mathlib.Data.List.Sort
import Mathlib.Logic.Equiv.Fin
import Mathlib.Logic.Equiv.Functor
import Mathlib.Data.Fintype.Card
import Mathlib.Order.RelSeries

#align_import order.jordan_holder from "leanprover-community/mathlib"@"91288e351d51b3f0748f0a38faa7613fb0ae2ada"

/-!
# Jordan-Hölder Theorem

This file proves the Jordan Hölder theorem for a `JordanHolderLattice`, a class also defined in
this file. Examples of `JordanHolderLattice` include `Subgroup G` if `G` is a group, and
`Submodule R M` if `M` is an `R`-module. Using this approach the theorem need not be proved
separately for both groups and modules, the proof in this file can be applied to both.

## Main definitions
The main definitions in this file are `JordanHolderLattice` and `CompositionSeries`,
and the relation `Equivalent` on `CompositionSeries`

A `JordanHolderLattice` is the class for which the Jordan Hölder theorem is proved. A
Jordan Hölder lattice is a lattice equipped with a notion of maximality, `IsMaximal`, and a notion
of isomorphism of pairs `Iso`. In the example of subgroups of a group, `IsMaximal H K` means that
`H` is a maximal normal subgroup of `K`, and `Iso (H₁, K₁) (H₂, K₂)` means that the quotient
`H₁ / K₁` is isomorphic to the quotient `H₂ / K₂`. `Iso` must be symmetric and transitive and must
satisfy the second isomorphism theorem `Iso (H, H ⊔ K) (H ⊓ K, K)`.

A `CompositionSeries X` is a finite nonempty series of elements of the lattice `X` such that
each element is maximal inside the next. The length of a `CompositionSeries X` is
one less than the number of elements in the series. Note that there is no stipulation
that a series start from the bottom of the lattice and finish at the top.
For a composition series `s`, `s.last` is the largest element of the series,
and `s.head` is the least element.

Two `CompositionSeries X`, `s₁` and `s₂` are equivalent if there is a bijection
`e : Fin s₁.length ≃ Fin s₂.length` such that for any `i`,
`Iso (s₁ i, s₁ i.succ) (s₂ (e i), s₂ (e i.succ))`

## Main theorems

The main theorem is `CompositionSeries.jordan_holder`, which says that if two composition
series have the same least element and the same largest element,
then they are `Equivalent`.

## TODO

Provide instances of `JordanHolderLattice` for subgroups, and potentially for modular lattices.

It is not entirely clear how this should be done. Possibly there should be no global instances
of `JordanHolderLattice`, and the instances should only be defined locally in order to prove
the Jordan-Hölder theorem for modules/groups and the API should be transferred because many of the
theorems in this file will have stronger versions for modules. There will also need to be an API for
mapping composition series across homomorphisms. It is also probably possible to
provide an instance of `JordanHolderLattice` for any `ModularLattice`, and in this case the
Jordan-Hölder theorem will say that there is a well defined notion of length of a modular lattice.
However an instance of `JordanHolderLattice` for a modular lattice will not be able to contain
the correct notion of isomorphism for modules, so a separate instance for modules will still be
required and this will clash with the instance for modular lattices, and so at least one of these
instances should not be a global instance.

> [!NOTE]
> The previous paragraph indicates that the instance of `JordanHolderLattice` for submodules should
> be obtained via `ModularLattice`. This is not the case in `mathlib4`.
> See `JordanHolderModule.instJordanHolderLattice`.
-/


universe u

open Set RelSeries

/-- A `JordanHolderLattice` is the class for which the Jordan Hölder theorem is proved. A
Jordan Hölder lattice is a lattice equipped with a notion of maximality, `IsMaximal`, and a notion
of isomorphism of pairs `Iso`. In the example of subgroups of a group, `IsMaximal H K` means that
`H` is a maximal normal subgroup of `K`, and `Iso (H₁, K₁) (H₂, K₂)` means that the quotient
`H₁ / K₁` is isomorphic to the quotient `H₂ / K₂`. `Iso` must be symmetric and transitive and must
satisfy the second isomorphism theorem `Iso (H, H ⊔ K) (H ⊓ K, K)`.
Examples include `Subgroup G` if `G` is a group, and `Submodule R M` if `M` is an `R`-module.
-/
class JordanHolderLattice (X : Type u) [Lattice X] where
  IsMaximal : X → X → Prop
  lt_of_isMaximal : ∀ {x y}, IsMaximal x y → x < y
  sup_eq_of_isMaximal : ∀ {x y z}, IsMaximal x z → IsMaximal y z → x ≠ y → x ⊔ y = z
  isMaximal_inf_left_of_isMaximal_sup :
    ∀ {x y}, IsMaximal x (x ⊔ y) → IsMaximal y (x ⊔ y) → IsMaximal (x ⊓ y) x
  Iso : X × X → X × X → Prop
  iso_symm : ∀ {x y}, Iso x y → Iso y x
  iso_trans : ∀ {x y z}, Iso x y → Iso y z → Iso x z
  second_iso : ∀ {x y}, IsMaximal x (x ⊔ y) → Iso (x, x ⊔ y) (x ⊓ y, y)
#align jordan_holder_lattice JordanHolderLattice

namespace JordanHolderLattice

variable {X : Type u} [Lattice X] [JordanHolderLattice X]

theorem isMaximal_inf_right_of_isMaximal_sup {x y : X} (hxz : IsMaximal x (x ⊔ y))
    (hyz : IsMaximal y (x ⊔ y)) : IsMaximal (x ⊓ y) y := by
  rw [inf_comm]
  rw [sup_comm] at hxz hyz
  exact isMaximal_inf_left_of_isMaximal_sup hyz hxz
#align jordan_holder_lattice.is_maximal_inf_right_of_is_maximal_sup JordanHolderLattice.isMaximal_inf_right_of_isMaximal_sup

theorem isMaximal_of_eq_inf (x b : X) {a y : X} (ha : x ⊓ y = a) (hxy : x ≠ y) (hxb : IsMaximal x b)
    (hyb : IsMaximal y b) : IsMaximal a y := by
  have hb : x ⊔ y = b := sup_eq_of_isMaximal hxb hyb hxy
  substs a b
  exact isMaximal_inf_right_of_isMaximal_sup hxb hyb
#align jordan_holder_lattice.is_maximal_of_eq_inf JordanHolderLattice.isMaximal_of_eq_inf

theorem second_iso_of_eq {x y a b : X} (hm : IsMaximal x a) (ha : x ⊔ y = a) (hb : x ⊓ y = b) :
    Iso (x, a) (b, y) := by substs a b; exact second_iso hm
#align jordan_holder_lattice.second_iso_of_eq JordanHolderLattice.second_iso_of_eq

theorem IsMaximal.iso_refl {x y : X} (h : IsMaximal x y) : Iso (x, y) (x, y) :=
  second_iso_of_eq h (sup_eq_right.2 (le_of_lt (lt_of_isMaximal h)))
    (inf_eq_left.2 (le_of_lt (lt_of_isMaximal h)))
#align jordan_holder_lattice.is_maximal.iso_refl JordanHolderLattice.IsMaximal.iso_refl

end JordanHolderLattice

open JordanHolderLattice

attribute [symm] iso_symm

attribute [trans] iso_trans

/-- A `CompositionSeries X` is a finite nonempty series of elements of a
`JordanHolderLattice` such that each element is maximal inside the next. The length of a
`CompositionSeries X` is one less than the number of elements in the series.
Note that there is no stipulation that a series start from the bottom of the lattice and finish at
the top. For a composition series `s`, `s.last` is the largest element of the series,
and `s.head` is the least element.
-/
abbrev CompositionSeries (X : Type u) [Lattice X] [JordanHolderLattice X] : Type u :=
  RelSeries (IsMaximal (X := X))
#align composition_series CompositionSeries

namespace CompositionSeries

variable {X : Type u} [Lattice X] [JordanHolderLattice X]

#noalign composition_series.has_coe_to_fun
#align composition_series.has_inhabited RelSeries.instInhabited
#align composition_series.step RelSeries.membership

theorem lt_succ (s : CompositionSeries X) (i : Fin s.length) :
    s (Fin.castSucc i) < s (Fin.succ i) :=
  lt_of_isMaximal (s.step _)
#align composition_series.lt_succ CompositionSeries.lt_succ

protected theorem strictMono (s : CompositionSeries X) : StrictMono s :=
  Fin.strictMono_iff_lt_succ.2 s.lt_succ
#align composition_series.strict_mono CompositionSeries.strictMono

protected theorem injective (s : CompositionSeries X) : Function.Injective s :=
  s.strictMono.injective
#align composition_series.injective CompositionSeries.injective

@[simp]
protected theorem inj (s : CompositionSeries X) {i j : Fin s.length.succ} : s i = s j ↔ i = j :=
  s.injective.eq_iff
#align composition_series.inj CompositionSeries.inj

#align composition_series.has_mem RelSeries.membership
#align composition_series.mem_def RelSeries.mem_def

theorem total {s : CompositionSeries X} {x y : X} (hx : x ∈ s) (hy : y ∈ s) : x ≤ y ∨ y ≤ x := by
  rcases Set.mem_range.1 hx with ⟨i, rfl⟩
  rcases Set.mem_range.1 hy with ⟨j, rfl⟩
  rw [s.strictMono.le_iff_le, s.strictMono.le_iff_le]
  exact le_total i j
#align composition_series.total CompositionSeries.total

#align composition_series.to_list RelSeries.toList
#align composition_series.ext_fun RelSeries.ext
#align composition_series.length_to_list RelSeries.length_toList
#align composition_series.to_list_ne_nil RelSeries.toList_ne_nil
#align composition_series.to_list_injective RelSeries.toList_injective

#align composition_series.chain'_to_list RelSeries.toList_chain'

theorem toList_sorted (s : CompositionSeries X) : s.toList.Sorted (· < ·) :=
  List.pairwise_iff_get.2 fun i j h => by
    dsimp only [RelSeries.toList]
    rw [List.get_ofFn, List.get_ofFn]
    exact s.strictMono h
#align composition_series.to_list_sorted CompositionSeries.toList_sorted

theorem toList_nodup (s : CompositionSeries X) : s.toList.Nodup :=
  s.toList_sorted.nodup
#align composition_series.to_list_nodup CompositionSeries.toList_nodup

#align composition_series.mem_to_list RelSeries.mem_toList
#align composition_series.of_list RelSeries.fromListChain'
#align composition_series.length_of_list RelSeries.fromListChain'_length
#noalign composition_series.of_list_to_list
#noalign composition_series.of_list_to_list'
#noalign composition_series.to_list_of_list

/-- Two `CompositionSeries` are equal if they have the same elements. See also `ext_fun`. -/
@[ext]
theorem ext {s₁ s₂ : CompositionSeries X} (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ :=
  toList_injective <|
    List.eq_of_perm_of_sorted
      (by
        classical
        exact List.perm_of_nodup_nodup_toFinset_eq s₁.toList_nodup s₂.toList_nodup
          (Finset.ext <| by simpa only [List.mem_toFinset, RelSeries.mem_toList]))
      s₁.toList_sorted s₂.toList_sorted
#align composition_series.ext CompositionSeries.ext

#align composition_series.top RelSeries.last
#align composition_series.top_mem RelSeries.last_mem

@[simp]
theorem le_last {s : CompositionSeries X} (i : Fin (s.length + 1)) : s i ≤ s.last :=
  s.strictMono.monotone (Fin.le_last _)
#align composition_series.le_top CompositionSeries.le_last

theorem le_last_of_mem {s : CompositionSeries X} {x : X} (hx : x ∈ s) : x ≤ s.last :=
  let ⟨_i, hi⟩ := Set.mem_range.2 hx
  hi ▸ le_last _
#align composition_series.le_top_of_mem CompositionSeries.le_last_of_mem

#align composition_series.bot RelSeries.head
#align composition_series.bot_mem RelSeries.head_mem

@[simp]
theorem head_le {s : CompositionSeries X} (i : Fin (s.length + 1)) : s.head ≤ s i :=
  s.strictMono.monotone (Fin.zero_le _)
#align composition_series.bot_le CompositionSeries.head_le

theorem head_le_of_mem {s : CompositionSeries X} {x : X} (hx : x ∈ s) : s.head ≤ x :=
  let ⟨_i, hi⟩ := Set.mem_range.2 hx
  hi ▸ head_le _
#align composition_series.bot_le_of_mem CompositionSeries.head_le_of_mem

-- The aligned versions of the following two lemmas are not exactly the same as the original
-- but they are mathematically equivalent.
#align composition_series.length_pos_of_mem_ne RelSeries.length_pos_of_nontrivial
#align composition_series.forall_mem_eq_of_length_eq_zero RelSeries.subsingleton_of_length_eq_zero
#align composition_series.erase_top RelSeries.eraseLast
#align composition_series.top_erase_top RelSeries.last_eraseLast

theorem last_eraseLast_le (s : CompositionSeries X) : s.eraseLast.last ≤ s.last := by
  simp [eraseLast, last, s.strictMono.le_iff_le, Fin.le_iff_val_le_val, tsub_le_self]
#align composition_series.erase_top_top_le CompositionSeries.last_eraseLast_le

#align composition_series.bot_erase_top RelSeries.head_eraseLast

theorem mem_eraseLast_of_ne_of_mem {s : CompositionSeries X} {x : X}
    (hx : x ≠ s.last) (hxs : x ∈ s) : x ∈ s.eraseLast := by
  rcases hxs with ⟨i, rfl⟩
  have hi : (i : ℕ) < (s.length - 1).succ := by
    conv_rhs => rw [← Nat.succ_sub (length_pos_of_nontrivial ⟨_, ⟨i, rfl⟩, _, s.last_mem, hx⟩),
      Nat.add_one_sub_one]
    exact lt_of_le_of_ne (Nat.le_of_lt_succ i.2) (by simpa [last, s.inj, Fin.ext_iff] using hx)
  refine ⟨Fin.castSucc (n := s.length + 1) i, ?_⟩
  simp [Fin.ext_iff, Nat.mod_eq_of_lt hi]
#align composition_series.mem_erase_top_of_ne_of_mem CompositionSeries.mem_eraseLast_of_ne_of_mem

theorem mem_eraseLast {s : CompositionSeries X} {x : X} (h : 0 < s.length) :
    x ∈ s.eraseLast ↔ x ≠ s.last ∧ x ∈ s := by
  simp only [RelSeries.mem_def, eraseLast]
  constructor
  · rintro ⟨i, rfl⟩
    have hi : (i : ℕ) < s.length := by
      conv_rhs => rw [← Nat.add_one_sub_one s.length, Nat.succ_sub h]
      exact i.2
    -- porting note (#10745): was `simp [top, Fin.ext_iff, ne_of_lt hi]`.
    simp [last, Fin.ext_iff, ne_of_lt hi, -Set.mem_range, Set.mem_range_self]
  · intro h
    exact mem_eraseLast_of_ne_of_mem h.1 h.2
#align composition_series.mem_erase_top CompositionSeries.mem_eraseLast

theorem lt_last_of_mem_eraseLast {s : CompositionSeries X} {x : X} (h : 0 < s.length)
    (hx : x ∈ s.eraseLast) : x < s.last :=
  lt_of_le_of_ne (le_last_of_mem ((mem_eraseLast h).1 hx).2) ((mem_eraseLast h).1 hx).1
#align composition_series.lt_top_of_mem_erase_top CompositionSeries.lt_last_of_mem_eraseLast

theorem isMaximal_eraseLast_last {s : CompositionSeries X} (h : 0 < s.length) :
    IsMaximal s.eraseLast.last s.last := by
  have : s.length - 1 + 1 = s.length := by
    conv_rhs => rw [← Nat.add_one_sub_one s.length]; rw [Nat.succ_sub h]
  rw [last_eraseLast, last]
  convert s.step ⟨s.length - 1, by omega⟩; ext; simp [this]
#align composition_series.is_maximal_erase_top_top CompositionSeries.isMaximal_eraseLast_last

section FinLemmas

#noalign composition_series.append_cast_add_aux
#noalign composition_series.append_succ_cast_add_aux
#noalign composition_series.append_nat_add_aux
#noalign composition_series.append_succ_nat_add_aux

end FinLemmas

#align composition_series.append RelSeries.smash
#noalign composition_series.coe_append
#align composition_series.append_cast_add RelSeries.smash_castAdd
#align composition_series.append_succ_cast_add RelSeries.smash_succ_castAdd
#align composition_series.append_nat_add RelSeries.smash_natAdd
#align composition_series.append_succ_nat_add RelSeries.smash_succ_natAdd
#align composition_series.snoc RelSeries.snoc
#align composition_series.top_snoc RelSeries.last_snoc
#align composition_series.snoc_last RelSeries.last_snoc
#align composition_series.snoc_cast_succ RelSeries.snoc_castSucc
#align composition_series.bot_snoc RelSeries.head_snoc
#align composition_series.mem_snoc RelSeries.mem_snoc

theorem eq_snoc_eraseLast {s : CompositionSeries X} (h : 0 < s.length) :
    s = snoc (eraseLast s) s.last (isMaximal_eraseLast_last h) := by
  ext x
  simp only [mem_snoc, mem_eraseLast h, ne_eq]
  by_cases h : x = s.last <;> simp [*, s.last_mem]
#align composition_series.eq_snoc_erase_top CompositionSeries.eq_snoc_eraseLast

@[simp]
theorem snoc_eraseLast_last {s : CompositionSeries X} (h : IsMaximal s.eraseLast.last s.last) :
    s.eraseLast.snoc s.last h = s :=
  have h : 0 < s.length :=
    Nat.pos_of_ne_zero (fun hs => ne_of_gt (lt_of_isMaximal h) <| by simp [last, Fin.ext_iff, hs])
  (eq_snoc_eraseLast h).symm
#align composition_series.snoc_erase_top_top CompositionSeries.snoc_eraseLast_last

/-- Two `CompositionSeries X`, `s₁` and `s₂` are equivalent if there is a bijection
`e : Fin s₁.length ≃ Fin s₂.length` such that for any `i`,
`Iso (s₁ i) (s₁ i.succ) (s₂ (e i), s₂ (e i.succ))` -/
def Equivalent (s₁ s₂ : CompositionSeries X) : Prop :=
  ∃ f : Fin s₁.length ≃ Fin s₂.length,
    ∀ i : Fin s₁.length, Iso (s₁ (Fin.castSucc i), s₁ i.succ)
      (s₂ (Fin.castSucc (f i)), s₂ (Fin.succ (f i)))
#align composition_series.equivalent CompositionSeries.Equivalent

namespace Equivalent

@[refl]
theorem refl (s : CompositionSeries X) : Equivalent s s :=
  ⟨Equiv.refl _, fun _ => (s.step _).iso_refl⟩
#align composition_series.equivalent.refl CompositionSeries.Equivalent.refl

@[symm]
theorem symm {s₁ s₂ : CompositionSeries X} (h : Equivalent s₁ s₂) : Equivalent s₂ s₁ :=
  ⟨h.choose.symm, fun i => iso_symm (by simpa using h.choose_spec (h.choose.symm i))⟩
#align composition_series.equivalent.symm CompositionSeries.Equivalent.symm

@[trans]
theorem trans {s₁ s₂ s₃ : CompositionSeries X} (h₁ : Equivalent s₁ s₂) (h₂ : Equivalent s₂ s₃) :
    Equivalent s₁ s₃ :=
  ⟨h₁.choose.trans h₂.choose,
    fun i => iso_trans (h₁.choose_spec i) (h₂.choose_spec (h₁.choose i))⟩
#align composition_series.equivalent.trans CompositionSeries.Equivalent.trans

protected theorem smash {s₁ s₂ t₁ t₂ : CompositionSeries X}
    (hs : s₁.last = s₂.head) (ht : t₁.last = t₂.head)
    (h₁ : Equivalent s₁ t₁) (h₂ : Equivalent s₂ t₂) :
    Equivalent (smash s₁ s₂ hs) (smash t₁ t₂ ht) :=
  let e : Fin (s₁.length + s₂.length) ≃ Fin (t₁.length + t₂.length) :=
    calc
      Fin (s₁.length + s₂.length) ≃ Sum (Fin s₁.length) (Fin s₂.length) := finSumFinEquiv.symm
      _ ≃ Sum (Fin t₁.length) (Fin t₂.length) := Equiv.sumCongr h₁.choose h₂.choose
      _ ≃ Fin (t₁.length + t₂.length) := finSumFinEquiv
  ⟨e, by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa [-smash_toFun, e, smash_castAdd, smash_succ_castAdd] using h₁.choose_spec i
    · intro i
      simpa [-smash_toFun, e, smash_natAdd, smash_succ_natAdd] using h₂.choose_spec i⟩
#align composition_series.equivalent.append CompositionSeries.Equivalent.smash

protected theorem snoc {s₁ s₂ : CompositionSeries X} {x₁ x₂ : X} {hsat₁ : IsMaximal s₁.last x₁}
    {hsat₂ : IsMaximal s₂.last x₂} (hequiv : Equivalent s₁ s₂)
    (hlast : Iso (s₁.last, x₁) (s₂.last, x₂)) : Equivalent (s₁.snoc x₁ hsat₁) (s₂.snoc x₂ hsat₂) :=
  let e : Fin s₁.length.succ ≃ Fin s₂.length.succ :=
    calc
      Fin (s₁.length + 1) ≃ Option (Fin s₁.length) := finSuccEquivLast
      _ ≃ Option (Fin s₂.length) := Functor.mapEquiv Option hequiv.choose
      _ ≃ Fin (s₂.length + 1) := finSuccEquivLast.symm
  ⟨e, fun i => by
    refine Fin.lastCases ?_ ?_ i
    · simpa [e, apply_last] using hlast
    · intro i
      simpa [e, Fin.succ_castSucc] using hequiv.choose_spec i⟩
#align composition_series.equivalent.snoc CompositionSeries.Equivalent.snoc

theorem length_eq {s₁ s₂ : CompositionSeries X} (h : Equivalent s₁ s₂) : s₁.length = s₂.length := by
  simpa using Fintype.card_congr h.choose
#align composition_series.equivalent.length_eq CompositionSeries.Equivalent.length_eq

theorem snoc_snoc_swap {s : CompositionSeries X} {x₁ x₂ y₁ y₂ : X} {hsat₁ : IsMaximal s.last x₁}
    {hsat₂ : IsMaximal s.last x₂} {hsaty₁ : IsMaximal (snoc s x₁ hsat₁).last y₁}
    {hsaty₂ : IsMaximal (snoc s x₂ hsat₂).last y₂} (hr₁ : Iso (s.last, x₁) (x₂, y₂))
    (hr₂ : Iso (x₁, y₁) (s.last, x₂)) :
    Equivalent (snoc (snoc s x₁ hsat₁) y₁ hsaty₁) (snoc (snoc s x₂ hsat₂) y₂ hsaty₂) :=
  let e : Fin (s.length + 1 + 1) ≃ Fin (s.length + 1 + 1) :=
    Equiv.swap (Fin.last _) (Fin.castSucc (Fin.last _))
  have h1 : ∀ {i : Fin s.length},
      (Fin.castSucc (Fin.castSucc i)) ≠ (Fin.castSucc (Fin.last _)) := fun {_} =>
    ne_of_lt (by simp [Fin.castSucc_lt_last])
  have h2 : ∀ {i : Fin s.length},
      (Fin.castSucc (Fin.castSucc i)) ≠ Fin.last _ := fun {_} =>
    ne_of_lt (by simp [Fin.castSucc_lt_last])
  ⟨e, by
    intro i
    dsimp only [e]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · erw [Equiv.swap_apply_left, snoc_castSucc,
      show (snoc s x₁ hsat₁).toFun (Fin.last _) = x₁ from last_snoc _ _ _, Fin.succ_last,
      show ((s.snoc x₁ hsat₁).snoc y₁ hsaty₁).toFun (Fin.last _) = y₁ from last_snoc _ _ _,
      snoc_castSucc, snoc_castSucc, Fin.succ_castSucc, snoc_castSucc, Fin.succ_last,
      show (s.snoc _ hsat₂).toFun (Fin.last _) = x₂ from last_snoc _ _ _]
      exact hr₂
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · erw [Equiv.swap_apply_right, snoc_castSucc, snoc_castSucc, snoc_castSucc,
          Fin.succ_castSucc, snoc_castSucc, Fin.succ_last, last_snoc', last_snoc', last_snoc']
        exact hr₁
      · erw [Equiv.swap_apply_of_ne_of_ne h2 h1, snoc_castSucc, snoc_castSucc,
          snoc_castSucc, snoc_castSucc, Fin.succ_castSucc, snoc_castSucc,
          Fin.succ_castSucc, snoc_castSucc, snoc_castSucc, snoc_castSucc]
        exact (s.step i).iso_refl⟩
#align composition_series.equivalent.snoc_snoc_swap CompositionSeries.Equivalent.snoc_snoc_swap

end Equivalent

theorem length_eq_zero_of_head_eq_head_of_last_eq_last_of_length_eq_zero
    {s₁ s₂ : CompositionSeries X} (hb : s₁.head = s₂.head)
    (ht : s₁.last = s₂.last) (hs₁ : s₁.length = 0) : s₂.length = 0 := by
  have : Fin.last s₂.length = (0 : Fin s₂.length.succ) :=
    s₂.injective (hb.symm.trans ((congr_arg s₁ (Fin.ext (by simp [hs₁]))).trans ht)).symm
  simpa [Fin.ext_iff]
#align composition_series.length_eq_zero_of_head_eq_head_of_last_eq_last_of_length_eq_zero CompositionSeries.length_eq_zero_of_head_eq_head_of_last_eq_last_of_length_eq_zero

theorem length_pos_of_head_eq_head_of_last_eq_last_of_length_pos {s₁ s₂ : CompositionSeries X}
    (hb : s₁.head = s₂.head) (ht : s₁.last = s₂.last) : 0 < s₁.length → 0 < s₂.length :=
  not_imp_not.1
    (by
      simpa only [pos_iff_ne_zero, ne_eq, Decidable.not_not] using
        length_eq_zero_of_head_eq_head_of_last_eq_last_of_length_eq_zero hb.symm ht.symm)
#align composition_series.length_pos_of_head_eq_head_of_last_eq_last_of_length_pos CompositionSeries.length_pos_of_head_eq_head_of_last_eq_last_of_length_pos

theorem eq_of_head_eq_head_of_last_eq_last_of_length_eq_zero {s₁ s₂ : CompositionSeries X}
    (hb : s₁.head = s₂.head) (ht : s₁.last = s₂.last) (hs₁0 : s₁.length = 0) : s₁ = s₂ := by
  have : ∀ x, x ∈ s₁ ↔ x = s₁.last := fun x =>
    ⟨fun hx =>  subsingleton_of_length_eq_zero hs₁0 hx s₁.last_mem, fun hx => hx.symm ▸ s₁.last_mem⟩
  have : ∀ x, x ∈ s₂ ↔ x = s₂.last := fun x =>
    ⟨fun hx =>
      subsingleton_of_length_eq_zero
        (length_eq_zero_of_head_eq_head_of_last_eq_last_of_length_eq_zero hb ht
          hs₁0) hx s₂.last_mem,
      fun hx => hx.symm ▸ s₂.last_mem⟩
  ext
  simp [*]
#align composition_series.eq_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero CompositionSeries.eq_of_head_eq_head_of_last_eq_last_of_length_eq_zero

/-- Given a `CompositionSeries`, `s`, and an element `x`
such that `x` is maximal inside `s.last` there is a series, `t`,
such that `t.last = x`, `t.head = s.head`
and `snoc t s.last _` is equivalent to `s`. -/
theorem exists_last_eq_snoc_equivalent (s : CompositionSeries X) (x : X) (hm : IsMaximal x s.last)
    (hb : s.head ≤ x) :
    ∃ t : CompositionSeries X,
      t.head = s.head ∧ t.length + 1 = s.length ∧
      ∃ htx : t.last = x,
        Equivalent s (snoc t s.last (show IsMaximal t.last _ from htx.symm ▸ hm)) := by
  induction' hn : s.length with n ih generalizing s x
  · exact
      (ne_of_gt (lt_of_le_of_lt hb (lt_of_isMaximal hm))
          (subsingleton_of_length_eq_zero hn s.last_mem s.head_mem)).elim
  · have h0s : 0 < s.length := hn.symm ▸ Nat.succ_pos _
    by_cases hetx : s.eraseLast.last = x
    · use s.eraseLast
      simp [← hetx, hn]
      -- Porting note: `rfl` is required.
      rfl
    · have imxs : IsMaximal (x ⊓ s.eraseLast.last) s.eraseLast.last :=
        isMaximal_of_eq_inf x s.last rfl (Ne.symm hetx) hm (isMaximal_eraseLast_last h0s)
      have := ih _ _ imxs (le_inf (by simpa) (le_last_of_mem s.eraseLast.head_mem)) (by simp [hn])
      rcases this with ⟨t, htb, htl, htt, hteqv⟩
      have hmtx : IsMaximal t.last x :=
        isMaximal_of_eq_inf s.eraseLast.last s.last (by rw [inf_comm, htt]) hetx
          (isMaximal_eraseLast_last h0s) hm
      use snoc t x hmtx
      refine ⟨by simp [htb], by simp [htl], by simp, ?_⟩
      have : s.Equivalent ((snoc t s.eraseLast.last <| show IsMaximal t.last _ from
        htt.symm ▸ imxs).snoc s.last
          (by simpa using isMaximal_eraseLast_last h0s)) := by
        conv_lhs => rw [eq_snoc_eraseLast h0s]
        exact Equivalent.snoc hteqv (by simpa using (isMaximal_eraseLast_last h0s).iso_refl)
      refine this.trans <| Equivalent.snoc_snoc_swap
        (iso_symm
            (second_iso_of_eq hm
              (sup_eq_of_isMaximal hm (isMaximal_eraseLast_last h0s) (Ne.symm hetx)) htt.symm))
        (second_iso_of_eq (isMaximal_eraseLast_last h0s)
            (sup_eq_of_isMaximal (isMaximal_eraseLast_last h0s) hm hetx) (by rw [inf_comm, htt]))

/-- The **Jordan-Hölder** theorem, stated for any `JordanHolderLattice`.
If two composition series start and finish at the same place, they are equivalent. -/
theorem jordan_holder (s₁ s₂ : CompositionSeries X)
    (hb : s₁.head = s₂.head) (ht : s₁.last = s₂.last) :
    Equivalent s₁ s₂ := by
  induction' hle : s₁.length with n ih generalizing s₁ s₂
  · rw [eq_of_head_eq_head_of_last_eq_last_of_length_eq_zero hb ht hle]
  · have h0s₂ : 0 < s₂.length :=
      length_pos_of_head_eq_head_of_last_eq_last_of_length_pos hb ht (hle.symm ▸ Nat.succ_pos _)
    rcases exists_last_eq_snoc_equivalent s₁ s₂.eraseLast.last
        (ht.symm ▸ isMaximal_eraseLast_last h0s₂)
        (hb.symm ▸ s₂.head_eraseLast ▸ head_le_of_mem (last_mem _)) with
      ⟨t, htb, htl, htt, hteq⟩
    have := ih t s₂.eraseLast (by simp [htb, ← hb]) htt (Nat.succ_inj'.1 (htl.trans hle))
    refine hteq.trans ?_
    conv_rhs => rw [eq_snoc_eraseLast h0s₂]
    simp only [ht]
    exact Equivalent.snoc this (by simpa [htt] using (isMaximal_eraseLast_last h0s₂).iso_refl)
#align composition_series.jordan_holder CompositionSeries.jordan_holder

end CompositionSeries
