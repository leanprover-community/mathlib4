/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Torsion

/-!
# Basic results on subgroups

We prove basic results on the definitions of subgroups. The bundled subgroups use bundled monoid
homomorphisms.

Special thanks goes to Amelia Livingston and Yury Kudryashov for their help and inspiration.

## Main definitions

Notation used here:

- `G N` are `Group`s

- `A` is an `AddGroup`

- `H K` are `Subgroup`s of `G` or `AddSubgroup`s of `A`

- `x` is an element of type `G` or type `A`

- `f g : N →* G` are group homomorphisms

- `s k` are sets of elements of type `G`

Definitions in the file:

* `Subgroup.prod H K` : the product of subgroups `H`, `K` of groups `G`, `N` respectively, `H × K`
  is a subgroup of `G × N`

## Implementation notes

Subgroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subgroup's underlying set.

## Tags
subgroup, subgroups
-/

assert_not_exists OrderedAddCommMonoid Multiset Ring

open Function
open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']
variable {A : Type*} [AddGroup A]

section SubgroupClass

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

@[to_additive]
theorem div_mem_comm_iff {a b : G} : a / b ∈ H ↔ b / a ∈ H :=
  inv_div b a ▸ inv_mem_iff

end SubgroupClass

namespace Subgroup

variable (H K : Subgroup G)

@[to_additive]
protected theorem div_mem_comm_iff {a b : G} : a / b ∈ H ↔ b / a ∈ H :=
  div_mem_comm_iff

variable {k : Set G}

open Set

variable {N : Type*} [Group N] {P : Type*} [Group P]

/-- Given `Subgroup`s `H`, `K` of groups `G`, `N` respectively, `H × K` as a subgroup of `G × N`. -/
@[to_additive prod
      /-- Given `AddSubgroup`s `H`, `K` of `AddGroup`s `A`, `B` respectively, `H × K`
      as an `AddSubgroup` of `A × B`. -/]
def prod (H : Subgroup G) (K : Subgroup N) : Subgroup (G × N) :=
  { Submonoid.prod H.toSubmonoid K.toSubmonoid with
    inv_mem' := fun hx => ⟨H.inv_mem' hx.1, K.inv_mem' hx.2⟩ }

@[to_additive coe_prod]
theorem coe_prod (H : Subgroup G) (K : Subgroup N) :
    (H.prod K : Set (G × N)) = (H : Set G) ×ˢ (K : Set N) :=
  rfl

@[to_additive mem_prod]
theorem mem_prod {H : Subgroup G} {K : Subgroup N} {p : G × N} : p ∈ H.prod K ↔ p.1 ∈ H ∧ p.2 ∈ K :=
  Iff.rfl

open scoped Relator in
@[to_additive prod_mono]
theorem prod_mono : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) (@prod G _ N _) (@prod G _ N _) :=
  fun _s _s' hs _t _t' ht => Set.prod_mono hs ht

@[to_additive prod_mono_right]
theorem prod_mono_right (K : Subgroup G) : Monotone fun t : Subgroup N => K.prod t :=
  prod_mono (le_refl K)

@[to_additive prod_mono_left]
theorem prod_mono_left (H : Subgroup N) : Monotone fun K : Subgroup G => K.prod H := fun _ _ hs =>
  prod_mono hs (le_refl H)

@[to_additive prod_top]
theorem prod_top (K : Subgroup G) : K.prod (⊤ : Subgroup N) = K.comap (MonoidHom.fst G N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_fst]

@[to_additive top_prod]
theorem top_prod (H : Subgroup N) : (⊤ : Subgroup G).prod H = H.comap (MonoidHom.snd G N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_snd]

@[to_additive (attr := simp) top_prod_top]
theorem top_prod_top : (⊤ : Subgroup G).prod (⊤ : Subgroup N) = ⊤ :=
  (top_prod _).trans <| comap_top _

@[to_additive (attr := simp) bot_prod_bot]
theorem bot_prod_bot : (⊥ : Subgroup G).prod (⊥ : Subgroup N) = ⊥ :=
  SetLike.coe_injective <| by simp [coe_prod]

@[deprecated (since := "2025-03-11")]
alias _root_.AddSubgroup.bot_sum_bot := AddSubgroup.bot_prod_bot

@[to_additive le_prod_iff]
theorem le_prod_iff {H : Subgroup G} {K : Subgroup N} {J : Subgroup (G × N)} :
    J ≤ H.prod K ↔ map (MonoidHom.fst G N) J ≤ H ∧ map (MonoidHom.snd G N) J ≤ K := by
  simpa only [← Subgroup.toSubmonoid_le] using Submonoid.le_prod_iff

@[to_additive prod_le_iff]
theorem prod_le_iff {H : Subgroup G} {K : Subgroup N} {J : Subgroup (G × N)} :
    H.prod K ≤ J ↔ map (MonoidHom.inl G N) H ≤ J ∧ map (MonoidHom.inr G N) K ≤ J := by
  simpa only [← Subgroup.toSubmonoid_le] using Submonoid.prod_le_iff

@[to_additive (attr := simp) prod_eq_bot_iff]
theorem prod_eq_bot_iff {H : Subgroup G} {K : Subgroup N} : H.prod K = ⊥ ↔ H = ⊥ ∧ K = ⊥ := by
  simpa only [← Subgroup.toSubmonoid_inj] using Submonoid.prod_eq_bot_iff

@[to_additive closure_prod]
theorem closure_prod {s : Set G} {t : Set N} (hs : 1 ∈ s) (ht : 1 ∈ t) :
    closure (s ×ˢ t) = (closure s).prod (closure t) :=
  le_antisymm
    (closure_le _ |>.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, subset_closure⟩)
    (prod_le_iff.2 ⟨
      map_le_iff_le_comap.2 <| closure_le _ |>.2 fun _x hx => subset_closure ⟨hx, ht⟩,
      map_le_iff_le_comap.2 <| closure_le _ |>.2 fun _y hy => subset_closure ⟨hs, hy⟩⟩)

/-- Product of subgroups is isomorphic to their product as groups. -/
@[to_additive prodEquiv
      /-- Product of additive subgroups is isomorphic to their product
      as additive groups -/]
def prodEquiv (H : Subgroup G) (K : Subgroup N) : H.prod K ≃* H × K :=
  { Equiv.Set.prod (H : Set G) (K : Set N) with map_mul' := fun _ _ => rfl }

section Pi

variable {η : Type*} {f : η → Type*}

-- defined here and not in Algebra.Group.Submonoid.Operations to have access to Algebra.Group.Pi
/-- A version of `Set.pi` for submonoids. Given an index set `I` and a family of submodules
`s : Π i, Submonoid f i`, `pi I s` is the submonoid of dependent functions `f : Π i, f i` such that
`f i` belongs to `Pi I s` whenever `i ∈ I`. -/
@[to_additive /-- A version of `Set.pi` for `AddSubmonoid`s. Given an index set `I` and a family
  of submodules `s : Π i, AddSubmonoid f i`, `pi I s` is the `AddSubmonoid` of dependent functions
  `f : Π i, f i` such that `f i` belongs to `pi I s` whenever `i ∈ I`. -/]
def _root_.Submonoid.pi [∀ i, MulOneClass (f i)] (I : Set η) (s : ∀ i, Submonoid (f i)) :
    Submonoid (∀ i, f i) where
  carrier := I.pi fun i => (s i).carrier
  one_mem' i _ := (s i).one_mem
  mul_mem' hp hq i hI := (s i).mul_mem (hp i hI) (hq i hI)

variable [∀ i, Group (f i)]

/-- A version of `Set.pi` for subgroups. Given an index set `I` and a family of submodules
`s : Π i, Subgroup f i`, `pi I s` is the subgroup of dependent functions `f : Π i, f i` such that
`f i` belongs to `pi I s` whenever `i ∈ I`. -/
@[to_additive
      /-- A version of `Set.pi` for `AddSubgroup`s. Given an index set `I` and a family
      of submodules `s : Π i, AddSubgroup f i`, `pi I s` is the `AddSubgroup` of dependent functions
      `f : Π i, f i` such that `f i` belongs to `pi I s` whenever `i ∈ I`. -/]
def pi (I : Set η) (H : ∀ i, Subgroup (f i)) : Subgroup (∀ i, f i) :=
  { Submonoid.pi I fun i => (H i).toSubmonoid with
    inv_mem' := fun hp i hI => (H i).inv_mem (hp i hI) }

@[to_additive]
theorem coe_pi (I : Set η) (H : ∀ i, Subgroup (f i)) :
    (pi I H : Set (∀ i, f i)) = Set.pi I fun i => (H i : Set (f i)) :=
  rfl

@[to_additive]
theorem mem_pi (I : Set η) {H : ∀ i, Subgroup (f i)} {p : ∀ i, f i} :
    p ∈ pi I H ↔ ∀ i : η, i ∈ I → p i ∈ H i :=
  Iff.rfl

@[to_additive]
theorem pi_top (I : Set η) : (pi I fun i => (⊤ : Subgroup (f i))) = ⊤ :=
  ext fun x => by simp [mem_pi]

@[to_additive]
theorem pi_empty (H : ∀ i, Subgroup (f i)) : pi ∅ H = ⊤ :=
  ext fun x => by simp [mem_pi]

@[to_additive]
theorem pi_bot : (pi Set.univ fun i => (⊥ : Subgroup (f i))) = ⊥ :=
  (eq_bot_iff_forall _).mpr fun p hp => by
    simp only [mem_pi, mem_bot] at *
    ext j
    exact hp j trivial

@[to_additive]
theorem le_pi_iff {I : Set η} {H : ∀ i, Subgroup (f i)} {J : Subgroup (∀ i, f i)} :
    J ≤ pi I H ↔ ∀ i : η, i ∈ I → map (Pi.evalMonoidHom f i) J ≤ H i := by
  constructor
  · intro h i hi
    rintro _ ⟨x, hx, rfl⟩
    exact (h hx) _ hi
  · intro h x hx i hi
    exact h i hi ⟨_, hx, rfl⟩

@[to_additive (attr := simp)]
theorem mulSingle_mem_pi [DecidableEq η] {I : Set η} {H : ∀ i, Subgroup (f i)} (i : η) (x : f i) :
    Pi.mulSingle i x ∈ pi I H ↔ i ∈ I → x ∈ H i := by
  constructor
  · intro h hi
    simpa using h i hi
  · intro h j hj
    by_cases heq : j = i
    · subst heq
      simpa using h hj
    · simp [heq, one_mem]

@[to_additive]
theorem pi_eq_bot_iff (H : ∀ i, Subgroup (f i)) : pi Set.univ H = ⊥ ↔ ∀ i, H i = ⊥ := by
  classical
    simp only [eq_bot_iff_forall]
    constructor
    · intro h i x hx
      have : MonoidHom.mulSingle f i x = 1 :=
        h (MonoidHom.mulSingle f i x) ((mulSingle_mem_pi i x).mpr fun _ => hx)
      simpa using congr_fun this i
    · exact fun h x hx => funext fun i => h _ _ (hx i trivial)

end Pi

instance instIsMulTorsionFree [IsMulTorsionFree G] : IsMulTorsionFree H where
  pow_left_injective n hn a b := by
    have := pow_left_injective hn (M := G) (a₁ := a) (a₂ := b)
    dsimp at *
    norm_cast at this

end Subgroup

namespace Subgroup

variable {H K : Subgroup G}

variable (H)

/-- A subgroup is characteristic if it is fixed by all automorphisms.
  Several equivalent conditions are provided by lemmas of the form `Characteristic.iff...` -/
structure Characteristic : Prop where
  /-- `H` is fixed by all automorphisms -/
  fixed : ∀ ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H

attribute [class] Characteristic

instance (priority := 100) normal_of_characteristic [h : H.Characteristic] : H.Normal :=
  ⟨fun a ha b => (SetLike.ext_iff.mp (h.fixed (MulAut.conj b)) a).mpr ha⟩

end Subgroup

namespace AddSubgroup

variable (H : AddSubgroup A)

/-- An `AddSubgroup` is characteristic if it is fixed by all automorphisms.
  Several equivalent conditions are provided by lemmas of the form `Characteristic.iff...` -/
structure Characteristic : Prop where
  /-- `H` is fixed by all automorphisms -/
  fixed : ∀ ϕ : A ≃+ A, H.comap ϕ.toAddMonoidHom = H

attribute [to_additive] Subgroup.Characteristic

attribute [class] Characteristic

instance (priority := 100) normal_of_characteristic [h : H.Characteristic] : H.Normal :=
  ⟨fun a ha b => (SetLike.ext_iff.mp (h.fixed (AddAut.conj b)) a).mpr ha⟩

end AddSubgroup

namespace Subgroup

variable {H K : Subgroup G}

@[to_additive]
theorem characteristic_iff_comap_eq : H.Characteristic ↔ ∀ ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H :=
  ⟨Characteristic.fixed, Characteristic.mk⟩

@[to_additive]
theorem characteristic_iff_comap_le : H.Characteristic ↔ ∀ ϕ : G ≃* G, H.comap ϕ.toMonoidHom ≤ H :=
  characteristic_iff_comap_eq.trans
    ⟨fun h ϕ => le_of_eq (h ϕ), fun h ϕ =>
      le_antisymm (h ϕ) fun g hg => h ϕ.symm ((congr_arg (· ∈ H) (ϕ.symm_apply_apply g)).mpr hg)⟩

@[to_additive]
theorem characteristic_iff_le_comap : H.Characteristic ↔ ∀ ϕ : G ≃* G, H ≤ H.comap ϕ.toMonoidHom :=
  characteristic_iff_comap_eq.trans
    ⟨fun h ϕ => ge_of_eq (h ϕ), fun h ϕ =>
      le_antisymm (fun g hg => (congr_arg (· ∈ H) (ϕ.symm_apply_apply g)).mp (h ϕ.symm hg)) (h ϕ)⟩

@[to_additive]
theorem characteristic_iff_map_eq : H.Characteristic ↔ ∀ ϕ : G ≃* G, H.map ϕ.toMonoidHom = H := by
  simp_rw [map_equiv_eq_comap_symm']
  exact characteristic_iff_comap_eq.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

@[to_additive]
theorem characteristic_iff_map_le : H.Characteristic ↔ ∀ ϕ : G ≃* G, H.map ϕ.toMonoidHom ≤ H := by
  simp_rw [map_equiv_eq_comap_symm']
  exact characteristic_iff_comap_le.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

@[to_additive]
theorem characteristic_iff_le_map : H.Characteristic ↔ ∀ ϕ : G ≃* G, H ≤ H.map ϕ.toMonoidHom := by
  simp_rw [map_equiv_eq_comap_symm']
  exact characteristic_iff_le_comap.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

@[to_additive]
instance botCharacteristic : Characteristic (⊥ : Subgroup G) :=
  characteristic_iff_le_map.mpr fun _ϕ => bot_le

@[to_additive]
instance topCharacteristic : Characteristic (⊤ : Subgroup G) :=
  characteristic_iff_map_le.mpr fun _ϕ => le_top


variable (H)

section Normalizer

variable {H}

@[to_additive]
theorem normalizer_eq_top_iff : H.normalizer = ⊤ ↔ H.Normal :=
  eq_top_iff.trans
    ⟨fun h => ⟨fun a ha b => (h (mem_top b) a).mp ha⟩, fun h a _ha b =>
      ⟨fun hb => h.conj_mem b hb a, fun hb => by rwa [h.mem_comm_iff, inv_mul_cancel_left] at hb⟩⟩

variable (H) in
@[to_additive]
theorem normalizer_eq_top [h : H.Normal] : H.normalizer = ⊤ :=
  normalizer_eq_top_iff.mpr h

variable {N : Type*} [Group N]

/-- The preimage of the normalizer is contained in the normalizer of the preimage. -/
@[to_additive /-- The preimage of the normalizer is contained in the normalizer of the preimage. -/]
theorem le_normalizer_comap (f : N →* G) :
    H.normalizer.comap f ≤ (H.comap f).normalizer := fun x => by
  simp only [mem_normalizer_iff, mem_comap]
  intro h n
  simp [h (f n)]

/-- The image of the normalizer is contained in the normalizer of the image. -/
@[to_additive /-- The image of the normalizer is contained in the normalizer of the image. -/]
theorem le_normalizer_map (f : G →* N) : H.normalizer.map f ≤ (H.map f).normalizer := fun _ => by
  simp only [and_imp, mem_map, exists_imp, mem_normalizer_iff]
  rintro x hx rfl n
  constructor
  · rintro ⟨y, hy, rfl⟩
    use x * y * x⁻¹, (hx y).1 hy
    simp
  · rintro ⟨y, hyH, hy⟩
    use x⁻¹ * y * x
    rw [hx]
    simp [hy, hyH, mul_assoc]

@[to_additive]
theorem comap_normalizer_eq_of_le_range {f : N →* G} (h : H ≤ f.range) :
    comap f H.normalizer = (comap f H).normalizer := by
  apply le_antisymm (le_normalizer_comap f)
  rw [← map_le_iff_le_comap]
  apply (le_normalizer_map f).trans
  rw [map_comap_eq_self h]

@[to_additive]
theorem subgroupOf_normalizer_eq {H N : Subgroup G} (h : H ≤ N) :
    H.normalizer.subgroupOf N = (H.subgroupOf N).normalizer :=
  comap_normalizer_eq_of_le_range (h.trans_eq N.range_subtype.symm)

@[to_additive]
theorem normal_subgroupOf_iff_le_normalizer (h : H ≤ K) :
    (H.subgroupOf K).Normal ↔ K ≤ H.normalizer := by
  rw [← subgroupOf_eq_top, subgroupOf_normalizer_eq h, normalizer_eq_top_iff]

@[to_additive]
theorem normal_subgroupOf_iff_le_normalizer_inf :
    (H.subgroupOf K).Normal ↔ K ≤ (H ⊓ K).normalizer :=
  inf_subgroupOf_right H K ▸ normal_subgroupOf_iff_le_normalizer inf_le_right

@[to_additive]
instance (priority := 100) normal_in_normalizer : (H.subgroupOf H.normalizer).Normal :=
  (normal_subgroupOf_iff_le_normalizer H.le_normalizer).mpr le_rfl

@[to_additive]
theorem le_normalizer_of_normal_subgroupOf [hK : (H.subgroupOf K).Normal] (HK : H ≤ K) :
    K ≤ H.normalizer :=
  (normal_subgroupOf_iff_le_normalizer HK).mp hK

@[to_additive]
theorem subset_normalizer_of_normal {S : Set G} [hH : H.Normal] : S ⊆ H.normalizer :=
  (@normalizer_eq_top _ _ H hH) ▸ le_top

@[to_additive]
theorem le_normalizer_of_normal [H.Normal] : K ≤ H.normalizer := subset_normalizer_of_normal

@[to_additive]
theorem inf_normalizer_le_normalizer_inf : H.normalizer ⊓ K.normalizer ≤ (H ⊓ K).normalizer :=
  fun _ h g ↦ and_congr (h.1 g) (h.2 g)

variable (G) in
/-- Every proper subgroup `H` of `G` is a proper normal subgroup of the normalizer of `H` in `G`. -/
def _root_.NormalizerCondition :=
  ∀ H : Subgroup G, H < ⊤ → H < normalizer H

/-- Alternative phrasing of the normalizer condition: Only the full group is self-normalizing.
This may be easier to work with, as it avoids inequalities and negations. -/
theorem _root_.normalizerCondition_iff_only_full_group_self_normalizing :
    NormalizerCondition G ↔ ∀ H : Subgroup G, H.normalizer = H → H = ⊤ := by
  apply forall_congr'; intro H
  simp only [lt_iff_le_and_ne, le_normalizer, le_top, Ne]
  tauto

variable (H)

end Normalizer

end Subgroup

namespace Group

variable {s : Set G}

/-- Given a set `s`, `conjugatesOfSet s` is the set of all conjugates of
the elements of `s`. -/
def conjugatesOfSet (s : Set G) : Set G :=
  ⋃ a ∈ s, conjugatesOf a

theorem mem_conjugatesOfSet_iff {x : G} : x ∈ conjugatesOfSet s ↔ ∃ a ∈ s, IsConj a x := by
  rw [conjugatesOfSet, Set.mem_iUnion₂]
  simp only [conjugatesOf, isConj_iff, Set.mem_setOf_eq, exists_prop]

theorem subset_conjugatesOfSet : s ⊆ conjugatesOfSet s := fun (x : G) (h : x ∈ s) =>
  mem_conjugatesOfSet_iff.2 ⟨x, h, IsConj.refl _⟩

theorem conjugatesOfSet_mono {s t : Set G} (h : s ⊆ t) : conjugatesOfSet s ⊆ conjugatesOfSet t :=
  Set.biUnion_subset_biUnion_left h

theorem conjugates_subset_normal {N : Subgroup G} [tn : N.Normal] {a : G} (h : a ∈ N) :
    conjugatesOf a ⊆ N := by
  rintro a hc
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  exact tn.conj_mem a h c

theorem conjugatesOfSet_subset {s : Set G} {N : Subgroup G} [N.Normal] (h : s ⊆ N) :
    conjugatesOfSet s ⊆ N :=
  Set.iUnion₂_subset fun _x H => conjugates_subset_normal (h H)

/-- The set of conjugates of `s` is closed under conjugation. -/
theorem conj_mem_conjugatesOfSet {x c : G} :
    x ∈ conjugatesOfSet s → c * x * c⁻¹ ∈ conjugatesOfSet s := fun H => by
  rcases mem_conjugatesOfSet_iff.1 H with ⟨a, h₁, h₂⟩
  exact mem_conjugatesOfSet_iff.2 ⟨a, h₁, h₂.trans (isConj_iff.2 ⟨c, rfl⟩)⟩

end Group

namespace Subgroup

open Group

variable {s : Set G}

/-- The normal closure of a set `s` is the subgroup closure of all the conjugates of
elements of `s`. It is the smallest normal subgroup containing `s`. -/
def normalClosure (s : Set G) : Subgroup G :=
  closure (conjugatesOfSet s)

theorem conjugatesOfSet_subset_normalClosure : conjugatesOfSet s ⊆ normalClosure s :=
  subset_closure

theorem subset_normalClosure : s ⊆ normalClosure s :=
  Set.Subset.trans subset_conjugatesOfSet conjugatesOfSet_subset_normalClosure

theorem le_normalClosure {H : Subgroup G} : H ≤ normalClosure ↑H := fun _ h =>
  subset_normalClosure h

/-- The normal closure of `s` is a normal subgroup. -/
instance normalClosure_normal : (normalClosure s).Normal :=
  ⟨fun n h g => by
    refine Subgroup.closure_induction (fun x hx => ?_) ?_ (fun x y _ _ ihx ihy => ?_)
      (fun x _ ihx => ?_) h
    · exact conjugatesOfSet_subset_normalClosure (conj_mem_conjugatesOfSet hx)
    · simp
    · rw [← conj_mul]
      exact mul_mem ihx ihy
    · rw [← conj_inv]
      exact inv_mem ihx⟩

/-- The normal closure of `s` is the smallest normal subgroup containing `s`. -/
theorem normalClosure_le_normal {N : Subgroup G} [N.Normal] (h : s ⊆ N) : normalClosure s ≤ N := by
  intro a w
  refine closure_induction (fun x hx => ?_) ?_ (fun x y _ _ ihx ihy => ?_) (fun x _ ihx => ?_) w
  · exact conjugatesOfSet_subset h hx
  · exact one_mem _
  · exact mul_mem ihx ihy
  · exact inv_mem ihx

theorem normalClosure_subset_iff {N : Subgroup G} [N.Normal] : s ⊆ N ↔ normalClosure s ≤ N :=
  ⟨normalClosure_le_normal, Set.Subset.trans subset_normalClosure⟩

@[gcongr]
theorem normalClosure_mono {s t : Set G} (h : s ⊆ t) : normalClosure s ≤ normalClosure t :=
  normalClosure_le_normal (Set.Subset.trans h subset_normalClosure)

theorem normalClosure_eq_iInf :
    normalClosure s = ⨅ (N : Subgroup G) (_ : Normal N) (_ : s ⊆ N), N :=
  le_antisymm (le_iInf fun _ => le_iInf fun _ => le_iInf normalClosure_le_normal)
    (iInf_le_of_le (normalClosure s)
      (iInf_le_of_le (by infer_instance) (iInf_le_of_le subset_normalClosure le_rfl)))

@[simp]
theorem normalClosure_eq_self (H : Subgroup G) [H.Normal] : normalClosure ↑H = H :=
  le_antisymm (normalClosure_le_normal rfl.subset) le_normalClosure

theorem normalClosure_idempotent : normalClosure ↑(normalClosure s) = normalClosure s :=
  normalClosure_eq_self _

theorem closure_le_normalClosure {s : Set G} : closure s ≤ normalClosure s := by
  simp only [subset_normalClosure, closure_le]

@[simp]
theorem normalClosure_closure_eq_normalClosure {s : Set G} :
    normalClosure ↑(closure s) = normalClosure s :=
  le_antisymm (normalClosure_le_normal closure_le_normalClosure) (normalClosure_mono subset_closure)

/-- The normal core of a subgroup `H` is the largest normal subgroup of `G` contained in `H`,
as shown by `Subgroup.normalCore_eq_iSup`. -/
def normalCore (H : Subgroup G) : Subgroup G where
  carrier := { a : G | ∀ b : G, b * a * b⁻¹ ∈ H }
  one_mem' a := by rw [mul_one, mul_inv_cancel]; exact H.one_mem
  inv_mem' {_} h b := (congr_arg (· ∈ H) conj_inv).mp (H.inv_mem (h b))
  mul_mem' {_ _} ha hb c := (congr_arg (· ∈ H) conj_mul).mp (H.mul_mem (ha c) (hb c))

theorem normalCore_le (H : Subgroup G) : H.normalCore ≤ H := fun a h => by
  rw [← mul_one a, ← inv_one, ← one_mul a]
  exact h 1

instance normalCore_normal (H : Subgroup G) : H.normalCore.Normal :=
  ⟨fun a h b c => by
    rw [mul_assoc, mul_assoc, ← mul_inv_rev, ← mul_assoc, ← mul_assoc]; exact h (c * b)⟩

theorem normal_le_normalCore {H : Subgroup G} {N : Subgroup G} [hN : N.Normal] :
    N ≤ H.normalCore ↔ N ≤ H :=
  ⟨ge_trans H.normalCore_le, fun h_le n hn g => h_le (hN.conj_mem n hn g)⟩

theorem normalCore_mono {H K : Subgroup G} (h : H ≤ K) : H.normalCore ≤ K.normalCore :=
  normal_le_normalCore.mpr (H.normalCore_le.trans h)

theorem normalCore_eq_iSup (H : Subgroup G) :
    H.normalCore = ⨆ (N : Subgroup G) (_ : Normal N) (_ : N ≤ H), N :=
  le_antisymm
    (le_iSup_of_le H.normalCore
      (le_iSup_of_le H.normalCore_normal (le_iSup_of_le H.normalCore_le le_rfl)))
    (iSup_le fun _ => iSup_le fun _ => iSup_le normal_le_normalCore.mpr)

@[simp]
theorem normalCore_eq_self (H : Subgroup G) [H.Normal] : H.normalCore = H :=
  le_antisymm H.normalCore_le (normal_le_normalCore.mpr le_rfl)

theorem normalCore_idempotent (H : Subgroup G) : H.normalCore.normalCore = H.normalCore :=
  H.normalCore.normalCore_eq_self

end Subgroup

namespace MonoidHom

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

open Subgroup

section Ker

variable {M : Type*} [MulOneClass M]

@[to_additive prodMap_comap_prod]
theorem prodMap_comap_prod {G' : Type*} {N' : Type*} [Group G'] [Group N'] (f : G →* N)
    (g : G' →* N') (S : Subgroup N) (S' : Subgroup N') :
    (S.prod S').comap (prodMap f g) = (S.comap f).prod (S'.comap g) :=
  SetLike.coe_injective <| Set.preimage_prod_map_prod f g _ _

@[deprecated (since := "2025-03-11")]
alias _root_.AddMonoidHom.sumMap_comap_sum := AddMonoidHom.prodMap_comap_prod

@[to_additive ker_prodMap]
theorem ker_prodMap {G' : Type*} {N' : Type*} [Group G'] [Group N'] (f : G →* N) (g : G' →* N') :
    (prodMap f g).ker = f.ker.prod g.ker := by
  rw [← comap_bot, ← comap_bot, ← comap_bot, ← prodMap_comap_prod, bot_prod_bot]

@[deprecated (since := "2025-03-11")]
alias _root_.AddMonoidHom.ker_sumMap := AddMonoidHom.ker_prodMap

@[to_additive (attr := simp)]
lemma ker_fst : ker (fst G G') = .prod ⊥ ⊤ := SetLike.ext fun _ => (iff_of_eq (and_true _)).symm

@[to_additive (attr := simp)]
lemma ker_snd : ker (snd G G') = .prod ⊤ ⊥ := SetLike.ext fun _ => (iff_of_eq (true_and _)).symm

end Ker

end MonoidHom

namespace Subgroup

variable {N : Type*} [Group N] (H : Subgroup G)

@[to_additive]
theorem Normal.map {H : Subgroup G} (h : H.Normal) (f : G →* N) (hf : Function.Surjective f) :
    (H.map f).Normal := by
  rw [← normalizer_eq_top_iff, ← top_le_iff, ← f.range_eq_top_of_surjective hf, f.range_eq_map,
    ← H.normalizer_eq_top]
  exact le_normalizer_map _

end Subgroup

namespace Subgroup

open MonoidHom

variable {N : Type*} [Group N] (f : G →* N)

/-- The preimage of the normalizer is equal to the normalizer of the preimage of a surjective
  function. -/
@[to_additive
      /-- The preimage of the normalizer is equal to the normalizer of the preimage of
      a surjective function. -/]
theorem comap_normalizer_eq_of_surjective (H : Subgroup G) {f : N →* G}
    (hf : Function.Surjective f) : H.normalizer.comap f = (H.comap f).normalizer :=
  comap_normalizer_eq_of_le_range fun x _ ↦ hf x

@[deprecated (since := "2025-03-13")]
alias comap_normalizer_eq_of_injective_of_le_range := comap_normalizer_eq_of_le_range

@[deprecated (since := "2025-03-13")]
alias _root_.AddSubgroup.comap_normalizer_eq_of_injective_of_le_range :=
  AddSubgroup.comap_normalizer_eq_of_le_range

/-- The image of the normalizer is equal to the normalizer of the image of an isomorphism. -/
@[to_additive
      /-- The image of the normalizer is equal to the normalizer of the image of an
      isomorphism. -/]
theorem map_equiv_normalizer_eq (H : Subgroup G) (f : G ≃* N) :
    H.normalizer.map f.toMonoidHom = (H.map f.toMonoidHom).normalizer := by
  ext x
  simp only [mem_normalizer_iff, mem_map_equiv]
  rw [f.toEquiv.forall_congr]
  intro
  simp

/-- The image of the normalizer is equal to the normalizer of the image of a bijective
  function. -/
@[to_additive
      /-- The image of the normalizer is equal to the normalizer of the image of a bijective
        function. -/]
theorem map_normalizer_eq_of_bijective (H : Subgroup G) {f : G →* N} (hf : Function.Bijective f) :
    H.normalizer.map f = (H.map f).normalizer :=
  map_equiv_normalizer_eq H (MulEquiv.ofBijective f hf)

end Subgroup

namespace MonoidHom

variable {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]
variable (f : G₁ →* G₂) (f_inv : G₂ → G₁)

/-- Auxiliary definition used to define `liftOfRightInverse` -/
@[to_additive /-- Auxiliary definition used to define `liftOfRightInverse` -/]
def liftOfRightInverseAux (hf : Function.RightInverse f_inv f) (g : G₁ →* G₃) (hg : f.ker ≤ g.ker) :
    G₂ →* G₃ where
  toFun b := g (f_inv b)
  map_one' := hg (hf 1)
  map_mul' := by
    intro x y
    rw [← g.map_mul, ← mul_inv_eq_one, ← g.map_inv, ← g.map_mul, ← g.mem_ker]
    apply hg
    rw [f.mem_ker, f.map_mul, f.map_inv, mul_inv_eq_one, f.map_mul]
    simp only [hf _]

@[to_additive (attr := simp)]
theorem liftOfRightInverseAux_comp_apply (hf : Function.RightInverse f_inv f) (g : G₁ →* G₃)
    (hg : f.ker ≤ g.ker) (x : G₁) : (f.liftOfRightInverseAux f_inv hf g hg) (f x) = g x := by
  dsimp [liftOfRightInverseAux]
  rw [← mul_inv_eq_one, ← g.map_inv, ← g.map_mul, ← g.mem_ker]
  apply hg
  rw [f.mem_ker, f.map_mul, f.map_inv, mul_inv_eq_one]
  simp only [hf _]

/-- `liftOfRightInverse f hf g hg` is the unique group homomorphism `φ`

* such that `φ.comp f = g` (`MonoidHom.liftOfRightInverse_comp`),
* where `f : G₁ →+* G₂` has a RightInverse `f_inv` (`hf`),
* and `g : G₂ →+* G₃` satisfies `hg : f.ker ≤ g.ker`.

See `MonoidHom.eq_liftOfRightInverse` for the uniqueness lemma.

```
   G₁.
   |  \
 f |   \ g
   |    \
   v     \⌟
   G₂----> G₃
      ∃!φ
```
-/
@[to_additive
      /-- `liftOfRightInverse f f_inv hf g hg` is the unique additive group homomorphism `φ`
      * such that `φ.comp f = g` (`AddMonoidHom.liftOfRightInverse_comp`),
      * where `f : G₁ →+ G₂` has a RightInverse `f_inv` (`hf`),
      * and `g : G₂ →+ G₃` satisfies `hg : f.ker ≤ g.ker`.
      See `AddMonoidHom.eq_liftOfRightInverse` for the uniqueness lemma.
      ```
         G₁.
         |  \
       f |   \ g
         |    \
         v     \⌟
         G₂----> G₃
            ∃!φ
      ``` -/]
def liftOfRightInverse (hf : Function.RightInverse f_inv f) :
    { g : G₁ →* G₃ // f.ker ≤ g.ker } ≃ (G₂ →* G₃) where
  toFun g := f.liftOfRightInverseAux f_inv hf g.1 g.2
  invFun φ := ⟨φ.comp f, fun x hx ↦ mem_ker.mpr <| by simp [mem_ker.mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]

/-- A non-computable version of `MonoidHom.liftOfRightInverse` for when no computable right
inverse is available, that uses `Function.surjInv`. -/
@[to_additive (attr := simp)
      /-- A non-computable version of `AddMonoidHom.liftOfRightInverse` for when no
      computable right inverse is available. -/]
noncomputable abbrev liftOfSurjective (hf : Function.Surjective f) :
    { g : G₁ →* G₃ // f.ker ≤ g.ker } ≃ (G₂ →* G₃) :=
  f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)

@[to_additive (attr := simp)]
theorem liftOfRightInverse_comp_apply (hf : Function.RightInverse f_inv f)
    (g : { g : G₁ →* G₃ // f.ker ≤ g.ker }) (x : G₁) :
    (f.liftOfRightInverse f_inv hf g) (f x) = g.1 x :=
  f.liftOfRightInverseAux_comp_apply f_inv hf g.1 g.2 x

@[to_additive (attr := simp)]
theorem liftOfRightInverse_comp (hf : Function.RightInverse f_inv f)
    (g : { g : G₁ →* G₃ // f.ker ≤ g.ker }) : (f.liftOfRightInverse f_inv hf g).comp f = g :=
  MonoidHom.ext <| f.liftOfRightInverse_comp_apply f_inv hf g

@[to_additive]
theorem eq_liftOfRightInverse (hf : Function.RightInverse f_inv f) (g : G₁ →* G₃)
    (hg : f.ker ≤ g.ker) (h : G₂ →* G₃) (hh : h.comp f = g) :
    h = f.liftOfRightInverse f_inv hf ⟨g, hg⟩ := by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm

end MonoidHom

variable {N : Type*} [Group N]

namespace Subgroup

-- Here `H.Normal` is an explicit argument so we can use dot notation with `comap`.
@[to_additive]
theorem Normal.comap {H : Subgroup N} (hH : H.Normal) (f : G →* N) : (H.comap f).Normal :=
  ⟨fun _ => by simp +contextual [Subgroup.mem_comap, hH.conj_mem]⟩

@[to_additive]
instance (priority := 100) normal_comap {H : Subgroup N} [nH : H.Normal] (f : G →* N) :
    (H.comap f).Normal :=
  nH.comap _

-- Here `H.Normal` is an explicit argument so we can use dot notation with `subgroupOf`.
@[to_additive]
theorem Normal.subgroupOf {H : Subgroup G} (hH : H.Normal) (K : Subgroup G) :
    (H.subgroupOf K).Normal :=
  hH.comap _

@[to_additive]
instance (priority := 100) normal_subgroupOf {H N : Subgroup G} [N.Normal] :
    (N.subgroupOf H).Normal :=
  Subgroup.normal_comap _

theorem map_normalClosure (s : Set G) (f : G →* N) (hf : Surjective f) :
    (normalClosure s).map f = normalClosure (f '' s) := by
  have : Normal (map f (normalClosure s)) := Normal.map inferInstance f hf
  apply le_antisymm
  · simp [map_le_iff_le_comap, normalClosure_le_normal, coe_comap,
      ← Set.image_subset_iff, subset_normalClosure]
  · exact normalClosure_le_normal (Set.image_mono subset_normalClosure)

theorem comap_normalClosure (s : Set N) (f : G ≃* N) :
    normalClosure (f ⁻¹' s) = (normalClosure s).comap f := by
  have := Set.preimage_equiv_eq_image_symm s f.toEquiv
  simp_all [comap_equiv_eq_map_symm, map_normalClosure s (f.symm : N →* G) f.symm.surjective]

lemma Normal.of_map_injective {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) {L : Subgroup G} (n : (L.map φ).Normal) : L.Normal :=
  L.comap_map_eq_self_of_injective hφ ▸ n.comap φ

theorem Normal.of_map_subtype {K : Subgroup G} {L : Subgroup K}
    (n : (Subgroup.map K.subtype L).Normal) : L.Normal :=
  n.of_map_injective K.subtype_injective

end Subgroup

namespace Subgroup

section SubgroupNormal

@[to_additive]
theorem normal_subgroupOf_iff {H K : Subgroup G} (hHK : H ≤ K) :
    (H.subgroupOf K).Normal ↔ ∀ h k, h ∈ H → k ∈ K → k * h * k⁻¹ ∈ H :=
  ⟨fun hN h k hH hK => hN.conj_mem ⟨h, hHK hH⟩ hH ⟨k, hK⟩, fun hN =>
    { conj_mem := fun h hm k => hN h.1 k.1 hm k.2 }⟩

@[to_additive prod_addSubgroupOf_prod_normal]
instance prod_subgroupOf_prod_normal {H₁ K₁ : Subgroup G} {H₂ K₂ : Subgroup N}
    [h₁ : (H₁.subgroupOf K₁).Normal] [h₂ : (H₂.subgroupOf K₂).Normal] :
    ((H₁.prod H₂).subgroupOf (K₁.prod K₂)).Normal where
  conj_mem n hgHK g :=
    ⟨h₁.conj_mem ⟨(n : G × N).fst, (mem_prod.mp n.2).1⟩ hgHK.1
        ⟨(g : G × N).fst, (mem_prod.mp g.2).1⟩,
      h₂.conj_mem ⟨(n : G × N).snd, (mem_prod.mp n.2).2⟩ hgHK.2
        ⟨(g : G × N).snd, (mem_prod.mp g.2).2⟩⟩

@[deprecated (since := "2025-03-11")]
alias _root_.AddSubgroup.sum_addSubgroupOf_sum_normal := AddSubgroup.prod_addSubgroupOf_prod_normal

@[to_additive prod_normal]
instance prod_normal (H : Subgroup G) (K : Subgroup N) [hH : H.Normal] [hK : K.Normal] :
    (H.prod K).Normal where
  conj_mem n hg g :=
    ⟨hH.conj_mem n.fst (Subgroup.mem_prod.mp hg).1 g.fst,
      hK.conj_mem n.snd (Subgroup.mem_prod.mp hg).2 g.snd⟩

@[deprecated (since := "2025-03-11")]
alias _root_.AddSubgroup.sum_normal := AddSubgroup.prod_normal

@[to_additive]
theorem inf_subgroupOf_inf_normal_of_right (A B' B : Subgroup G)
    [hN : (B'.subgroupOf B).Normal] : ((A ⊓ B').subgroupOf (A ⊓ B)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer_inf] at hN ⊢
  rw [inf_inf_inf_comm, inf_idem]
  exact le_trans (inf_le_inf A.le_normalizer hN) (inf_normalizer_le_normalizer_inf)

@[to_additive]
theorem inf_subgroupOf_inf_normal_of_left {A' A : Subgroup G} (B : Subgroup G)
    [hN : (A'.subgroupOf A).Normal] : ((A' ⊓ B).subgroupOf (A ⊓ B)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer_inf] at hN ⊢
  rw [inf_inf_inf_comm, inf_idem]
  exact le_trans (inf_le_inf hN B.le_normalizer) (inf_normalizer_le_normalizer_inf)

@[to_additive]
instance normal_inf_normal (H K : Subgroup G) [hH : H.Normal] [hK : K.Normal] : (H ⊓ K).Normal :=
  ⟨fun n hmem g => ⟨hH.conj_mem n hmem.1 g, hK.conj_mem n hmem.2 g⟩⟩

@[to_additive]
theorem normal_iInf_normal {ι : Type*} {a : ι → Subgroup G}
    (norm : ∀ i : ι, (a i).Normal) : (iInf a).Normal := by
  constructor
  intro g g_in_iInf h
  rw [Subgroup.mem_iInf] at g_in_iInf ⊢
  intro i
  exact (norm i).conj_mem g (g_in_iInf i) h

@[to_additive]
theorem SubgroupNormal.mem_comm {H K : Subgroup G} (hK : H ≤ K) [hN : (H.subgroupOf K).Normal]
    {a b : G} (hb : b ∈ K) (h : a * b ∈ H) : b * a ∈ H := by
  have := (normal_subgroupOf_iff hK).mp hN (a * b) b h hb
  rwa [mul_assoc, mul_assoc, mul_inv_cancel, mul_one] at this

/-- Elements of disjoint, normal subgroups commute. -/
@[to_additive /-- Elements of disjoint, normal subgroups commute. -/]
theorem commute_of_normal_of_disjoint (H₁ H₂ : Subgroup G) (hH₁ : H₁.Normal) (hH₂ : H₂.Normal)
    (hdis : Disjoint H₁ H₂) (x y : G) (hx : x ∈ H₁) (hy : y ∈ H₂) : Commute x y := by
  suffices x * y * x⁻¹ * y⁻¹ = 1 by
    change x * y = y * x
    · rw [mul_assoc, mul_eq_one_iff_eq_inv] at this
      simpa
  apply hdis.le_bot
  constructor
  · suffices x * (y * x⁻¹ * y⁻¹) ∈ H₁ by simpa [mul_assoc]
    exact H₁.mul_mem hx (hH₁.conj_mem _ (H₁.inv_mem hx) _)
  · change x * y * x⁻¹ * y⁻¹ ∈ H₂
    apply H₂.mul_mem _ (H₂.inv_mem hy)
    apply hH₂.conj_mem _ hy

@[to_additive]
theorem normal_subgroupOf_of_le_normalizer {H N : Subgroup G}
    (hLE : H ≤ N.normalizer) : (N.subgroupOf H).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer_inf]
  exact (le_inf hLE H.le_normalizer).trans inf_normalizer_le_normalizer_inf

@[to_additive]
theorem normal_subgroupOf_sup_of_le_normalizer {H N : Subgroup G}
    (hLE : H ≤ N.normalizer) : (N.subgroupOf (H ⊔ N)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer le_sup_right]
  exact sup_le hLE le_normalizer

end SubgroupNormal

end Subgroup

namespace IsConj

open Subgroup

theorem normalClosure_eq_top_of {N : Subgroup G} [hn : N.Normal] {g g' : G} {hg : g ∈ N}
    {hg' : g' ∈ N} (hc : IsConj g g') (ht : normalClosure ({⟨g, hg⟩} : Set N) = ⊤) :
    normalClosure ({⟨g', hg'⟩} : Set N) = ⊤ := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  have h : ∀ x : N, (MulAut.conj c) x ∈ N := by
    rintro ⟨x, hx⟩
    exact hn.conj_mem _ hx c
  have hs : Function.Surjective (((MulAut.conj c).toMonoidHom.restrict N).codRestrict _ h) := by
    rintro ⟨x, hx⟩
    refine ⟨⟨c⁻¹ * x * c, ?_⟩, ?_⟩
    · have h := hn.conj_mem _ hx c⁻¹
      rwa [inv_inv] at h
    simp only [MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.restrict_apply, Subtype.mk_eq_mk, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [eq_top_iff, ← MonoidHom.range_eq_top.2 hs, MonoidHom.range_eq_map]
  refine le_trans (map_mono (eq_top_iff.1 ht)) (map_le_iff_le_comap.2 (normalClosure_le_normal ?_))
  rw [Set.singleton_subset_iff, SetLike.mem_coe]
  simp only [MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    MonoidHom.restrict_apply, mem_comap]
  exact subset_normalClosure (Set.mem_singleton _)

end IsConj

namespace ConjClasses

/-- The conjugacy classes that are not trivial. -/
def noncenter (G : Type*) [Monoid G] : Set (ConjClasses G) :=
  {x | x.carrier.Nontrivial}

@[simp] lemma mem_noncenter {G} [Monoid G] (g : ConjClasses G) :
    g ∈ noncenter G ↔ g.carrier.Nontrivial := Iff.rfl

end ConjClasses

/-- Suppose `G` acts on `M` and `I` is a subgroup of `M`.
The inertia subgroup of `I` is the subgroup of `G` whose action is trivial mod `I`. -/
def AddSubgroup.inertia {M : Type*} [AddGroup M] (I : AddSubgroup M) (G : Type*)
    [Group G] [MulAction G M] : Subgroup G where
  carrier := { σ | ∀ x, σ • x - x ∈ I }
  mul_mem' {a b} ha hb x := by simpa [mul_smul] using add_mem (ha (b • x)) (hb x)
  one_mem' := by simp [zero_mem]
  inv_mem' {a} ha x := by simpa using sub_mem_comm_iff.mp (ha (a⁻¹ • x))

@[simp] lemma AddSubgroup.mem_inertia {M : Type*} [AddGroup M] {I : AddSubgroup M} {G : Type*}
    [Group G] [MulAction G M] {σ : G} : σ ∈ I.inertia G ↔ ∀ x, σ • x - x ∈ I := .rfl
