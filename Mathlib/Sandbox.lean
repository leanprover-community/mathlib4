import Mathlib.FieldTheory.Galois.IsGaloisGroup

variable {G K L : Type*} [Field K] [Field L] [Algebra K L] [Group G]
  [MulSemiringAction G L] {F : IntermediateField K L}

theorem IsGaloisGroup.smul_eq_self (H : Subgroup G) [IsGaloisGroup H F L] (g : G)
    (hg : g ∈ H) (x : F) : g • (x : L) = x :=
  smul_algebraMap (⟨g, hg⟩ : H) x

variable (N : Subgroup G) [hN : N.Normal]
theorem IsGaloisGroup.smul_mem_of_normal [hF : IsGaloisGroup N F L] (g : G) (x : F) :
    g • (x : L) ∈ F := by
  have := hF.isInvariant.isInvariant (g • x) ?_
  · obtain ⟨y, hy⟩ := this
    simp [← hy]
  · intro n
    rw [← smul_assoc, MulAction.subgroup_smul_def, smul_eq_mul,
      show n * g = g * (g⁻¹ * n * g) by group, ← smul_eq_mul, smul_assoc,
      IsGaloisGroup.smul_eq_self N (g⁻¹ * (n : G) * g)]
    exact hN.conj_mem' n n.prop g

variable [hF : IsGaloisGroup N F L]

instance : SMul (G ⧸ N) F where
  smul g := by
    refine Quotient.liftOn' g
      (fun g x ↦ ⟨g • (x : L), IsGaloisGroup.smul_mem_of_normal N g x⟩) fun g g' h ↦ ?_
    ext
    rw [smul_eq_iff_eq_inv_smul, ← smul_assoc, smul_eq_mul, IsGaloisGroup.smul_eq_self N]
    rwa [← QuotientGroup.leftRel_apply]

@[simp]
lemma coe_quotient_smul (g : G) (x : F) :
    ((g : G ⧸ N) • x : F) = g • (x : L) := rfl

set_option backward.isDefEq.respectTransparency false in
instance : MulSemiringAction (G ⧸ N) F where
  one_smul _ := Subtype.ext <| by rw [← QuotientGroup.mk_one, coe_quotient_smul, one_smul]
  smul_zero g := Quotient.inductionOn' g fun g ↦ Subtype.ext <| by simp
  mul_smul g g' x := Quotient.inductionOn₂' g g' fun g g' ↦ Subtype.ext <| by
    simp [← QuotientGroup.mk_mul, coe_quotient_smul, mul_smul]
  smul_add g x y := Quotient.inductionOn' g fun g ↦ Subtype.ext <| by simp [smul_add]
  smul_one g := Quotient.inductionOn' g fun g ↦ Subtype.ext <| by simp
  smul_mul g x y := Quotient.inductionOn' g fun g ↦ Subtype.ext <| by simp [smul_mul']

set_option backward.isDefEq.respectTransparency false in
instance [SMulCommClass G K L] : SMulCommClass (G ⧸ N) K F :=
  ⟨fun g k x ↦ Quotient.inductionOn' g fun g ↦ Subtype.ext <| by simp [smul_comm]⟩

variable [hG : IsGaloisGroup G K L]

set_option backward.isDefEq.respectTransparency false in
instance IsGaloisGroup.quotient : IsGaloisGroup (G ⧸ N) K F where
  faithful := ⟨fun {g₁} {g₂} ↦ Quotient.inductionOn₂' g₁ g₂ fun g₁ g₂ h ↦ by
    rw [QuotientGroup.eq]
    have : N = fixingSubgroup G (F : Set L) := by sorry
    rw [this]
    rw [mem_fixingSubgroup_iff]
    intro x hx
    rw [mul_smul]
    rw [inv_smul_eq_iff]
    have := congr_arg Subtype.val <| h ⟨x, hx⟩
    rwa [coe_quotient_smul, coe_quotient_smul, eq_comm] at this⟩
  commutes := inferInstance
  isInvariant := ⟨fun x h ↦ by
    have : ∀ (g : G), g • (x : L) = x := fun g ↦ by
      simpa [coe_quotient_smul] using congr_arg Subtype.val (h g)
    obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant x this
    refine ⟨a, ?_⟩
    apply FaithfulSMul.algebraMap_injective F L
    rw [← IsScalarTower.algebraMap_apply, ha, IntermediateField.algebraMap_apply]⟩
