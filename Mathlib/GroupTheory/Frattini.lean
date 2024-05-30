--import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib

/--
The infimum of all coatoms.

This notion specializes, e.g. in the subgroup lattice of a group to the Frattini subgroup,
or in the lattices of ideals in a ring `R` to the Jacobson ideal.
-/
def Order.radical (α : Type*) [Preorder α] [OrderTop α] [InfSet α] : α :=
   ⨅ a ∈ {H | IsCoatom H}, a

namespace Order

variable {α : Type*} [CompleteLattice α]

lemma radical_le_coatom {a : α} (h : IsCoatom a) :
    radical α ≤ a :=
  biInf_le _ h

variable {β : Type*} [CompleteLattice β]

theorem radical_characteristic (f : α ≃o β) : f (Order.radical α) = Order.radical β := by
  unfold radical
  simp only [OrderIso.map_iInf]
  fapply Equiv.iInf_congr
  · exact f.toEquiv
  · intros
    simp

theorem radical_nongenerating [IsCoatomic α] {a : α} (h : a ⊔ radical α = ⊤) :
    a = ⊤ := by
  obtain (rfl | w) := eq_top_or_exists_le_coatom a
  · rfl
  · obtain ⟨m, c, le⟩ := w
    have q : a ⊔ radical α ≤ m := sup_le le (radical_le_coatom c)
    rw [h] at q
    simp only [top_le_iff] at q
    simpa using c.1 q

end Order

/-- The Frattini subgroup of a group is the intersection of the maximal subgroups. -/
def frattini (G : Type*) [Group G] : Subgroup G :=
  Order.radical (Subgroup G)

variable {G H : Type*} [Group G] [Group H]

open Subgroup

/--
An isomorphism of groups gives an order isomorphism between the lattices of subgroups,
defined by sending subgroups to their inverse images.

See also `MulEquiv.mapSubgroup` which maps subgroups to their forward images.
-/
@[simps]
def MulEquiv.comapSubgroup (f : G ≃* H) : Subgroup H ≃o Subgroup G where
  toFun := Subgroup.comap f
  invFun := Subgroup.comap f.symm
  left_inv sg := by simp [Subgroup.comap_comap]
  right_inv sh := by simp [Subgroup.comap_comap]
  map_rel_iff' {sg1 sg2} :=
    ⟨fun h => by simpa [Subgroup.comap_comap] using
      Subgroup.comap_mono (f := (f.symm : H →* G)) h, Subgroup.comap_mono⟩

@[simp]
theorem MulEquiv.isCoatom_comap (f : G ≃* H) {K : Subgroup H} :
    IsCoatom (comap (f : G →* H) K) ↔ IsCoatom K :=
  OrderIso.isCoatom_iff (f.comapSubgroup) K

variable (G)

/-- The Frattini subgroup is characteristic. -/
instance frattini_characteristic : (frattini G).Characteristic := by
  rw [characteristic_iff_comap_eq]
  intro φ
  apply Order.radical_characteristic φ.comapSubgroup

variable {G}

lemma frattini_le_coatom {K : Subgroup G} (h: IsCoatom K) : frattini G ≤ K :=
  biInf_le _ h

theorem frattini_nongenerating [IsCoatomic (Subgroup G)] {K : Subgroup G} (h : K ⊔ frattini G = ⊤) :
    K = ⊤ :=
  Order.radical_nongenerating h

noncomputable section

-- The Sylow files unnecessarily use `Fintype` (computable) where often `Finite` would suffice,
-- so wwe need this:
attribute [local instance] Fintype.ofFinite

-- This is surely in Mathlib?!
-- Asked at https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/normal.20subgroups/near/441573924
theorem foo {K : Subgroup G} {L : Subgroup K} (n : (map K.subtype L).Normal) : L.Normal := by
  obtain ⟨conj_mem⟩ := n
  simp at conj_mem
  constructor
  intro l l_mem k
  specialize conj_mem l l.2 l_mem k
  obtain ⟨_, h⟩ := conj_mem
  exact h

/-- When `G` is finite, the Frattini subgroup is nilpotent. -/
theorem frattini_nilpotent [Fintype G] : Group.IsNilpotent (frattini G) := by
  -- We use the characterisation of nilpotency in terms of all Sylow subgroups being normal.
  have q := isNilpotent_of_finite_tFAE (G := frattini G)
  have r := q.out 0 3
  rw [r]; clear q r
  -- Consider each prime `p` and Sylow `p`-subgroup `P` of `frattini G`.
  intro p p_prime P
  -- The Frattini argument shows that the normalizer of `P` in `G`
  -- together with `frattini G` generates `G`.
  have frat_arg := Sylow.normalizer_sup_eq_top P
  -- and hence by the nongenerating property of the Frattini subgroup that
  -- the normalzer of `P` in `G` is `G`.
  have := frattini_nongenerating frat_arg
  -- This means that `P` is normal as a subgroup of `G`
  have : (map (frattini G).subtype ↑P).Normal := by exact normalizer_eq_top.mp this
  -- and hence also as a subgroup of `frattini G`.
  have pn : Normal (G := frattini G) P := foo this
  exact pn






/-!
Some results we don't actually use above, but seem like they are missing and related!
-/

-- Provided by Eric Wieser at https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Group.20isomorphism.20gives.20an.20order.20isomorphism.20on.20subgroups/near/441230172
-- We may actually prefer the version via `comap` below!
-- See also `Submodule.orderIsoMapComap`, which is stated in a slightly more general form,
-- and uses `map` for the forward direction and `comap` for the reverse direction.
@[simps]
def MulEquiv.mapSubgroup (f : G ≃* H) : Subgroup G ≃o Subgroup H where
  toFun := Subgroup.map f
  invFun := Subgroup.map f.symm
  left_inv sg := by simp [Subgroup.map_map]
  right_inv sh := by simp [Subgroup.map_map]
  map_rel_iff' {sg1 sg2} :=
    ⟨fun h => by simpa [Subgroup.map_map] using
      Subgroup.map_mono (f := (f.symm : H →* G)) h, Subgroup.map_mono⟩

@[simp]
theorem MulEquiv.isCoatom_map (f : G ≃* H) {K : Subgroup G} :
    IsCoatom (map (f : G →* H) K) ↔ IsCoatom K :=
  OrderIso.isCoatom_iff (f.mapSubgroup) K

@[simp]
theorem Subgroup.map_symm (f : G ≃* H) {K : Subgroup H} : map f.symm K = comap (f : G →* H) K := by
  aesop
@[simp]
theorem Subgroup.comap_symm (f : G ≃* H) {K : Subgroup G} : comap (f.symm : H →* G) K = map f K := by
  aesop

theorem comap_equiv_strictMono (f : G ≃* H) : StrictMono (comap (f : G →* H)) :=
  OrderIso.strictMono (f.comapSubgroup)

@[simp]
theorem MulEquiv.range (f : G ≃* H) : (f : G →* H).range = ⊤ := by
  ext x
  simp only [MonoidHom.mem_range, MonoidHom.coe_coe, mem_top, iff_true]
  exact ⟨f.symm x, by simp⟩

@[simp]
theorem Subgroup.map_comap_equiv (f : G ≃* H) {K : Subgroup H} :
    map (f : G →* H) (comap (f : G →* H) K) = K := by
  rw [map_comap_eq_self]
  simp

@[simp]
theorem Subgroup.map_equiv_top (f : G ≃* H) : map (f : G →* H) ⊤ = ⊤ :=
  OrderIso.map_top (f.mapSubgroup)

@[simp]
theorem Subgroup.comap_equiv_top (f : G ≃* H) : comap (f : G →* H) ⊤ = ⊤ :=
  OrderIso.map_top (f.comapSubgroup)

attribute [simp] OrderIso.map_top -- why is this not a global simp lemma?
