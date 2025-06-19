import Mathlib.Data.Real.OfDigits
import Mathlib.Topology.UnitInterval

universe u v w

def DiscreteTopology.equiv_to_homeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace Y] [DiscreteTopology Y] (eq : X ≃ Y) : X ≃ₜ Y :=
  eq.toHomeomorph (by simp)

def finTwoHomeoBool : Fin 2 ≃ₜ Bool :=
  DiscreteTopology.equiv_to_homeomorph finTwoEquiv

noncomputable def fromBinary (b : ℕ → Bool) : unitInterval :=
  let φ : (ℕ → Bool) ≃ₜ (ℕ → Fin 2) := Homeomorph.piCongrRight (fun _ ↦ finTwoHomeoBool.symm)
  let x : ℝ := ofDigits (φ b)
  have hx : x ∈ Set.Icc 0 1 := by
    simp [x]
    constructor
    · exact ofDigits_nonneg
    · exact ofDigits_le_one
  ⟨x, hx⟩

theorem fromBinary_continuous : Continuous fromBinary := by
  unfold fromBinary
  apply Continuous.subtype_mk
  have : (fun x ↦ ofDigits ((Homeomorph.piCongrRight fun _ ↦ finTwoHomeoBool.symm) x)) =
      ofDigits ∘ (Homeomorph.piCongrRight fun _ ↦ finTwoHomeoBool.symm) := by
    ext
    simp
  rw [this, Homeomorph.comp_continuous_iff']
  exact ofDigits_continuous

theorem fromBinary_surjective : Function.Surjective fromBinary := by
  intro x
  obtain ⟨x, hx⟩ := x
  by_cases hx_one : x = 1
  · use fun _ ↦ true
    have : fromBinary (fun _ ↦ true) = ofDigits (b := 2) (fun _ ↦ 1) := by
      simp [fromBinary, finTwoHomeoBool, DiscreteTopology.equiv_to_homeomorph]
      congr
    simp [Subtype.eq_iff, this, ofDigits, ofDigitsTerm, hx_one, pow_succ, ← inv_pow]
    rw [Summable.tsum_mul_left]
    · rw [tsum_geometric_inv_two]
      simp
    · convert summable_geometric_two
      eta_expand
      simp
  replace hx : x ∈ Set.Ico 0 1 := by
    simp at hx ⊢
    exact ⟨hx.left, by apply hx.right.lt_of_ne' (by symm; simpa)⟩
  use finTwoEquiv ∘ (toDigits x 2)
  simp [fromBinary, ← Function.comp_assoc, toDigits_ofDigits]
  conv => rhs; rw [← toDigits_ofDigits 2 x (by simp) hx]
  congr
  ext n
  simp
  congr
  simp [finTwoHomeoBool, DiscreteTopology.equiv_to_homeomorph]

def uncurry_homeomorph (X : Type u) (Y : Type v) (Z : Type w)
    [TopologicalSpace Z] :
    (X → Y → Z) ≃ₜ (X × Y → Z) where
  toFun := Function.uncurry
  invFun := Function.curry
  left_inv := by exact congrFun rfl
  right_inv := by exact congrFun rfl

def cantorSet_pow : (ℕ → Bool) ≃ₜ (ℕ → ℕ → Bool) :=
    (Homeomorph.piCongrLeft (Y := fun _ ↦ Bool) Nat.pairEquiv.symm).trans
    (uncurry_homeomorph _ _ _).symm

noncomputable def cantorToHilbert (x : ℕ → Bool) : ℕ → unitInterval :=
  Pi.map (fun _ b ↦ fromBinary b) (cantorSet_pow x)

theorem cantorToHilbert_continuous : Continuous cantorToHilbert := by
  unfold cantorToHilbert
  apply continuous_pi
  intro i
  apply fromBinary_continuous.comp
  fun_prop

theorem cantorToHilbert_surjective : Function.Surjective cantorToHilbert := by
  unfold cantorToHilbert
  change Function.Surjective ((Pi.map (fun x b ↦ fromBinary b)) ∘ cantorSet_pow)
  apply Function.Surjective.comp
  · apply Function.Surjective.piMap
    intro _
    apply fromBinary_surjective
  · exact Homeomorph.surjective cantorSet_pow
