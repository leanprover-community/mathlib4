import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Killing

namespace LieSubalgebra

variable {k L V : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]

local notation "π" => LieModule.toEnd k

open Module LieAlgebra LieModule in
lemma exists_weight_eq_mul_root [FiniteDimensional k V]
    (H : LieSubalgebra k L) [H.IsCartanSubalgebra] 
    (χ : Weight k H V) (α : Weight k H L) :
    ∃ r : ℚ, ∀ (e : rootSpace H α) (f : rootSpace H (-⇑α)) (h : H),
      ⁅(e : L), (f : L)⁆ = h → χ h = r * α h := by
  classical
  let ι := {n : ℤ // genWeightSpace V (χ + n • α : H → k) ≠ ⊥ ∧ ((α : H → k) = 0 → n = 0)}
  let w (n : ι) : Weight k H V := ⟨χ + n.1 • α, n.2.1⟩ 
  let W (n : ι) : LieSubmodule k H V := genWeightSpace V (w n)
  let U : Submodule k V := ⨆ i, ((fun i ↦ ↑(genWeightSpace V ⇑i)) ∘ w) i
  have hw : w.Injective := by
    intro m n hmn
    ext
    by_cases hα : (α : H → k) = 0
    · rw [m.2.2 hα, n.2.2 hα]
    obtain ⟨x, hx⟩ : ∃ x, α x ≠ 0 := by
      contrapose! hα
      ext
      apply hα
    rw [Weight.ext_iff] at hmn
    specialize hmn x
    simpa only [ne_eq, zsmul_eq_mul, Pi.intCast_def, Weight.coe_weight_mk, Pi.add_apply,
      Pi.mul_apply, add_right_inj, mul_eq_mul_right_iff, Int.cast_inj, hx, or_false, w, ι] using hmn
  have : Fintype ι := Fintype.ofInjective w hw
  let N : ℤ := ∑ n : ι, finrank k (W n) * n.1
  let D : ℕ := ∑ n : ι, finrank k (W n)
  use - N / D
  intro e f h hh
  suffices D * χ h + N * α h = 0 by
    rw [mul_comm] at this
    have hD : (D : k) ≠ 0 := by
      simp only [ne_eq, Weight.coe_weight_mk, Nat.cast_eq_zero, Finset.sum_eq_zero_iff,
        Finset.mem_univ, forall_const, not_forall, Subtype.exists, zsmul_eq_mul,
        Weight.coe_eq_zero_iff, exists_prop, D, ι, w, W]
      use 0
      rw [← ne_eq, ← ne_eq, ← Nat.pos_iff_ne_zero, finrank_pos_iff,
        LieSubmodule.nontrivial_iff_ne_bot]
      simp only [Int.cast_zero, implies_true, and_true, zero_mul, add_zero, zero_smul, and_self]
      exact χ.2
    field_simp [eq_neg_iff_add_eq_zero, this]
  have aux := (LieSubmodule.iSupIndep_iff_toSubmodule.mp <| iSupIndep_genWeightSpace' k H V).comp hw
  have Hh' (i : ι) : Set.MapsTo (π H V h) ↑(genWeightSpace V (w i)) ↑(genWeightSpace V (w i)) :=
    fun v hv ↦ LieSubmodule.lie_mem _ hv
  have Hh : Set.MapsTo (π L V h) U U := by
    simpa only [Set.mem_univ, iSup_pos] using LinearMap.mapsTo_biSup_of_mapsTo (.univ : Set ι) Hh'
  have key : (((π L V h).restrict Hh).trace k U) = ∑ n : ι, (((π H (W n) h)).trace k (W n)) :=
    LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup
      Finset.univ (aux.comp Subtype.coe_injective) (f := π L V h) Hh' U (by simp [U]) Hh
  suffices (((π L V h).restrict Hh).trace k U) = 0 by
    simpa only [ne_eq, Weight.coe_weight_mk, Nat.cast_sum, Finset.sum_mul, Int.cast_sum,
      Int.cast_mul, Int.cast_natCast, mul_assoc, trace_toEnd_genWeightSpace, zsmul_eq_mul,
      Pi.add_apply, smul_add, nsmul_eq_mul, Finset.sum_add_distrib, this, D, W, w, N] using key.symm
  clear key
  have aux' (m : ℤ) (e : rootSpace H (m • ⇑α)) : Set.MapsTo (π L V e) U U := by
    show U ≤ U.comap (π L V e)
    simp only [Function.comp_apply, iSup_pos, iSup_le_iff, U]
    intro n v hv
    simp only [Submodule.mem_comap, toEnd_apply_apply]
    by_cases hev : ⁅(e:L), v⁆ = 0
    · simpa only [hev] using Submodule.zero_mem _
    have hev_mem : ⁅(e:L), v⁆ ∈ genWeightSpace V (χ + (n.1 + m) • α : H → k) := by
      have := LieAlgebra.mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace k L H V _ (w n) e.2 hv
      suffices ⇑χ + (↑n + m) • ⇑α = m • ⇑α + ⇑(w n) by rwa [this]
      simp only [zsmul_eq_mul, Int.cast_add, Pi.intCast_def, Weight.coe_weight_mk, w]
      ring
    by_cases hα : (α : H → k) = 0
    · exact le_iSup (fun n ↦ (W n).toSubmodule) n <| by
        simpa only [ne_eq, hα, smul_zero, add_zero, W, w] using hev_mem
    have hn : genWeightSpace V (χ + (n.1 + m) • α : H → k) ≠ ⊥ := by
      rw [← LieSubmodule.nontrivial_iff_ne_bot]
      apply nontrivial_of_ne ⟨_, hev_mem⟩ 0
      simpa only [ne_eq, Subtype.ext_iff] using hev
    let n' : ι := ⟨n.1 + m, ⟨hn, by simp [hα]⟩⟩
    exact le_iSup (fun n ↦ (W n).toSubmodule) n' hev_mem
  have He : Set.MapsTo (π L V e) U U := by
    specialize aux' 1
    simp only [Subtype.forall, one_smul] at aux'
    exact aux' e e.2
  have Hf : Set.MapsTo (π L V f) U U := by
    specialize aux' (-1)
    simp only [Int.reduceNeg, Subtype.forall, neg_smul, one_smul] at aux'
    exact aux' f f.2
  suffices (π L V h).restrict Hh = ⁅(π L V e).restrict He, (π L V f).restrict Hf⁆ by
    simp only [LinearMap.trace_lie, this]
  simp only [← hh, LieHom.map_lie]
  rfl

end LieSubalgebra

namespace LieAlgebra

variable {k L V : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]

local notation "π" => LieModule.toEnd k

example [IsSemisimple k L] : HasTrivialRadical k L := by
  infer_instance

example [Module.Finite k L] [IsKilling k L] : IsSemisimple k L := by
  infer_instance

example [Module.Finite k L] [IsKilling k L] : HasTrivialRadical k L := by
  infer_instance

open LieAlgebra in
lemma exists_traceForm_ne_zero_of_perfect [FiniteDimensional k L] [FiniteDimensional k V]
    [LieModule.IsTriangularizable k L V]
    [Nontrivial L] (hL : LieAlgebra.derivedSeries k L 1 = ⊤) (hLsub : Function.Injective (π L V)) :
    ∃ x : L, LieModule.traceForm k L V x x ≠ 0 := by
  by_contra! hLV
  obtain ⟨e, he⟩ := LieAlgebra.exists_isCartanSubalgebra_engel k L
  set H := LieSubalgebra.engel k e
  suffices LieRing.IsNilpotent L by
    rw [LieRing.IsNilpotent, LieModule.isNilpotent_iff k] at this
    obtain ⟨n, hn⟩ := this
    suffices LieModule.lowerCentralSeries k L L n = ⊤ by
      rw [this] at hn
      exact top_ne_bot hn
    clear hn
    induction n with
    | zero => simp
    | succ n ih => simpa [ih] using hL
  suffices LieAlgebra.rootSpace H (0 : H → k) = ⊤ by
    sorry
  suffices ∀ α : H → k, α ≠ 0 → LieAlgebra.rootSpace H α = ⊥ by
    sorry
  suffices LieModule.genWeightSpace V (0 : H → k) = ⊤ by
    sorry
  suffices ∀ χ : H → k, LieModule.genWeightSpace V χ ≠ ⊥ → χ = 0 by
    sorry
  intro χ' hχ
  let χ : LieModule.Weight k H V := ⟨χ', hχ⟩
  suffices ∀ (α : LieModule.Weight k H L) (e : rootSpace H α) (f : rootSpace H (-⇑α)) (h : H),
    ⁅(e:L), (f:L)⁆ = h → χ h = 0 by
    sorry
  intro α e f h hh
  have key := LieModule.traceForm_eq_sum_finrank_nsmul_mul k H V h h
  replace hLV : LieModule.traceForm k H V h h = 0 := hLV h
  choose r hr using LieSubalgebra.exists_weight_eq_mul_root (k := k) (L := L) (V := V) H
  replace hr := fun χ ↦ hr χ α e f h hh
  simp_rw [hLV, nsmul_eq_mul, ← pow_two, hr, mul_pow, ← mul_assoc, ← Finset.sum_mul] at key
  rw [eq_comm, mul_eq_zero, pow_two, mul_eq_zero, or_self] at key
  by_cases hα : α h = 0
  · simpa [hα] using hr χ
  simp only [hα, or_false] at key
  norm_cast at key
  rw [Finset.sum_eq_zero_iff_of_nonneg] at key
  swap; · intros; positivity
  specialize key χ (Finset.mem_univ χ)
  rw [mul_eq_zero, pow_two, mul_eq_zero, or_self] at key
  by_cases hrχ : r χ α = 0
  · simpa [hrχ] using hr χ
  simp only [hrχ, or_false] at key
  norm_cast at key
  rw [Module.finrank_zero_iff] at key
  rw [← LieSubmodule.nontrivial_iff_ne_bot] at hχ
  apply (not_nontrivial _ hχ).elim

-- move this
instance [Subsingleton L] : IsSolvable k L := by
  constructor
  use 0
  ext x
  simp [Subsingleton.elim x 0]

-- move this
/-- The Killing form is symmetric. -/
lemma killingForm_symm (X Y : L) : killingForm k L X Y = killingForm k L Y X :=
  LieModule.traceForm_comm _ _ _ _ _

/-- The Killing form is symmetric. -/
lemma killingForm_isSymm : (killingForm k L).IsSymm :=
  LieModule.traceForm_isSymm _ _ _

private theorem isSolvable_iff_of_algClosed [Module.Finite k L] [IsAlgClosed k] :
    IsSolvable k L ↔ ∀ X Y : L, Y ∈ LieAlgebra.derivedSeries k L 1 → killingForm k L X Y = 0 := by
  obtain _ | _ := subsingleton_or_nontrivial L
  · simp; infer_instance
  constructor
  · intro h
    obtain ⟨χ, hχ⟩ := LieModule.exists_forall_lie_eq_smul_of_isSolvable k L L
    obtain ⟨⟨Z, hZ⟩, hZ0⟩ := exists_ne (0 : LieModule.weightSpace L χ) 
    simp only [ne_eq, LieSubmodule.mk_eq_zero] at hZ0
    simp only [LieModule.mem_weightSpace] at hZ
    sorry
  · intro h
    sorry

theorem isSolvable_iff [Module.Finite k L] :
    IsSolvable k L ↔ ∀ X Y : L, Y ∈ LieAlgebra.derivedSeries k L 1 → killingForm k L X Y = 0 := by
  obtain _ | _ := subsingleton_or_nontrivial L
  · simp; infer_instance
  constructor
  · intro h
    -- WLOG: k is algebraically closed
    -- have := LieModule.exists_forall_lie_eq_smul_of_isSolvable k L L
    sorry
  · intro h
    sorry

instance [Module.Finite k L] [HasTrivialRadical k L] : IsKilling k L := by
  constructor
  suffices IsSolvable k (LieIdeal.killingCompl k L ⊤) from HasTrivialRadical.eq_bot_of_isSolvable _
  rw [isSolvable_iff]
  intro X Y hY
  rw [LieIdeal.killingForm_eq]
  show killingForm k L X Y = 0
  have := X.2
  rw [LieIdeal.mem_killingCompl] at this
  rw [killingForm_symm]
  apply this
  simp

example [Module.Finite k L] [IsSemisimple k L] : IsKilling k L := by
  infer_instance

example [Module.Finite k L] [HasTrivialRadical k L] : IsSemisimple k L := by
  infer_instance

end LieAlgebra
