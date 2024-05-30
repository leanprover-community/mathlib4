--import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib

/-- The Frattini subgroup of a group is the intersection of the maximal subgroups. -/
def frattini (G : Type*) [Group G] : Subgroup G :=
   ⨅ a ∈ {H | IsCoatom H}, a

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
theorem frattini_characteristic : (frattini G).Characteristic := by
    rw [characteristic_iff_comap_eq]
    intro φ
    unfold frattini
    simp only [comap_iInf]
    fapply Equiv.iInf_congr
    · exact φ.comapSubgroup.toEquiv
    · intros
      simp
      rfl


-- variable {X : Set (G)}

theorem frattini_nongenerating_subset : ∀ X : Set (G), Subgroup.closure ( X) ⊔ frattini G = ⊤ → Subgroup.closure (X) = G  := by
  intro X
  intro h
  unfold frattini at h
  simp at h
  sorry

#check Or

lemma frattini_le_coatom(K : Subgroup G)(h: IsCoatom K) : frattini G ≤ K :=
  biInf_le _ h

variable {G}

theorem frattini_nongenerating[IsCoatomic (Subgroup G)] {K : Subgroup G} (h: K ⊔ frattini G = ⊤): K = ⊤  := by
  --unfold frattini at h
  --simp at h
  have w := eq_top_or_exists_le_coatom K
  cases w
  case inl p => assumption
  case inr p =>
    obtain ⟨ M, c, le⟩:= p
    have q : K ⊔ frattini G ≤ M := by
      have r:= frattini_le_coatom G M c
      exact sup_le le r
    rw [h] at q
    simp at q
    have:= c.1 q
    contradiction

-- fix implicitness of Sylow.nonempty

theorem frattini_nilpotent[Fintype G] : Group.IsNilpotent (frattini G) := by
  have n : Normal (frattini G) := inferInstance
      -- normal_of_characteristic (frattini G)
  have frat_fin : Fintype (frattini G) := sorry
  have q := isNilpotent_of_finite_tFAE (G:= frattini G)
  have r := q.out 0 3
  rw [r]
  intro p p_prime P
  --obtain ⟨ P ⟩:= Sylow.nonempty ( p:= p) (G:= frattini G)
  have frat_arg := Sylow.normalizer_sup_eq_top P
  have := frattini_nongenerating frat_arg
  have pn : Normal (G := frattini G) P := by
        exact normal_inf_normal (G:= G) (map (frattini G).subtype P) (frattini G)

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
