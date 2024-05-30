import Mathlib.Algebra.Group.Subgroup.Basic

def frattini (G : Type*) [Group G] : Subgroup G :=
   ⨅ a ∈ {H | IsCoatom H}, a

variable {G H : Type*} [Group G] [Group H]

open Subgroup

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

-- @[simps] -- This breaks the proof below,
-- but it can be fixed by proving `MulEquiv.isCoatom_comap` even further below!
def MulEquiv.comapSubgroup (f : G ≃* H) : Subgroup H ≃o Subgroup G where
  toFun := Subgroup.comap f
  invFun := Subgroup.comap f.symm
  left_inv sg := by simp [Subgroup.comap_comap]
  right_inv sh := by simp [Subgroup.comap_comap]
  map_rel_iff' {sg1 sg2} :=
    ⟨fun h => by simpa [Subgroup.comap_comap] using
      Subgroup.comap_mono (f := (f.symm : H →* G)) h, Subgroup.comap_mono⟩




variable (G)

theorem frattini_characteristic :  (frattini G).Characteristic := by
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

theorem frattini_nongenerating : ∀ X : Set (G), Subgroup.closure ( X) ⊔ frattini G = ⊤ → Subgroup.closure (X) = G  := by
  intro X
  intro h
  unfold frattini at h
  simp at h
  sorry


/-!
Some results we don't actually use above, but seem like they are missing and related!
-/

@[simp]
theorem Subgroup.map_symm (f : G ≃* H) {K : Subgroup H} : map f.symm K = comap (f : G →* H) K := by
  aesop
@[simp]
theorem Subgroup.comap_symm (f : G ≃* H) {K : Subgroup G} : comap (f.symm : H →* G) K = map f K := by
  aesop

@[simp]
theorem MulEquiv.isCoatom_comap (f : G ≃* H) {K : Subgroup H} :
    IsCoatom (comap (f : G →* H) K) ↔ IsCoatom K := by
  dsimp [IsCoatom]
  sorry
