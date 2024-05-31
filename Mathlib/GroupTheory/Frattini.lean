--import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib

/--
The infimum of all coatoms.

This notion specializes, e.g. in the subgroup lattice of a group to the Frattini subgroup,
or in the lattices of ideals in a ring `R` to the Jacobson ideal.
-/
def Order.radical (α : Type*) [Preorder α] [OrderTop α] [InfSet α] : α :=
   ⨅ a ∈ {H | IsCoatom H}, a

section Order.radical

variable {α : Type*} [CompleteLattice α]

lemma Order.radical_le_coatom {a : α} (h : IsCoatom a) : radical α ≤ a := biInf_le _ h

variable {β : Type*} [CompleteLattice β]

theorem OrderIso.map_radical(f : α ≃o β) : f (Order.radical α) = Order.radical β := by
  unfold Order.radical
  simp only [OrderIso.map_iInf]
  fapply Equiv.iInf_congr
  · exact f.toEquiv
  · intros
    simp

theorem Order.radical_nongenerating [IsCoatomic α] {a : α} (h : a ⊔ radical α = ⊤) :
    a = ⊤ := by
  obtain (rfl | w) := eq_top_or_exists_le_coatom a
  · rfl
  · obtain ⟨m, c, le⟩ := w
    have q : a ⊔ radical α ≤ m := sup_le le (radical_le_coatom c)
    rw [h, top_le_iff] at q
    simpa using c.1 q

end Order.radical

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
  apply φ.comapSubgroup.map_radical

variable {G}

lemma frattini_le_coatom {K : Subgroup G} (h : IsCoatom K) : frattini G ≤ K :=
  Order.radical_le_coatom h

/--
The Frattini subgroup consists of "non-generating" elements in the following sense:

If a subgroup together with the Frattini subgroup generates the whole group,
then the subgroup is already the whole group.
-/
theorem frattini_nongenerating [IsCoatomic (Subgroup G)] {K : Subgroup G} (h : K ⊔ frattini G = ⊤) :
    K = ⊤ :=
  Order.radical_nongenerating h

noncomputable section

-- The Sylow files unnecessarily use `Fintype` (computable) where often `Finite` would suffice,
-- so wwe need this:
attribute [local instance] Fintype.ofFinite

-- This is surely in Mathlib?!
-- Asked at https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/normal.20subgroups/near/441573924
-- No answer, so it is apparently not in Mathlib.
theorem normal_of_map_subtype_normal {K : Subgroup G} {L : Subgroup K}
    (n : (map K.subtype L).Normal) : L.Normal := by
  obtain ⟨conj_mem⟩ := n
  simp only [mem_map, coeSubtype, Subtype.exists, exists_and_right, exists_eq_right,
    forall_exists_index] at conj_mem
  exact ⟨fun l l_mem k => (conj_mem l l.2 l_mem k).2⟩

/-- When `G` is finite, the Frattini subgroup is nilpotent. -/
theorem frattini_nilpotent [Fintype G] : Group.IsNilpotent (frattini G) := by
  -- We use the characterisation of nilpotency in terms of all Sylow subgroups being normal.
  have q := (isNilpotent_of_finite_tFAE (G := frattini G)).out 0 3
  rw [q]; clear q
  -- Consider each prime `p` and Sylow `p`-subgroup `P` of `frattini G`.
  intro p p_prime P
  -- The Frattini argument shows that the normalizer of `P` in `G`
  -- together with `frattini G` generates `G`.
  have frattini_argument := Sylow.normalizer_sup_eq_top P
  -- and hence by the nongenerating property of the Frattini subgroup that
  -- the normalizer of `P` in `G` is `G`.
  have normalizer_P := frattini_nongenerating frattini_argument
  -- This means that `P` is normal as a subgroup of `G`
  have P_normal_in_G : (map (frattini G).subtype ↑P).Normal := normalizer_eq_top.mp normalizer_P
  -- and hence also as a subgroup of `frattini G`, which was the remaining goal.
  exact normal_of_map_subtype_normal P_normal_in_G


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
