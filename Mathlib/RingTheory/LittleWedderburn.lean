import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Tactic.ByContra

/-!
# Little Wedderburn TODO
-/


open scoped NNReal BigOperators Polynomial

namespace LittleWedderburn

universe u v
variable {D : Type u} [DivisionRing D] {R : Type v} [Ring R]

variable (D)

def InductionHyp : Prop :=
  ∀ R : Subring D, R < ⊤ → ∀ ⦃x y⦄, x ∈ R → y ∈ R → x * y = y * x

namespace InductionHyp

open FiniteDimensional Polynomial

variable {D}


open scoped Classical in
protected noncomputable def field [Fintype D] (hD : InductionHyp D) (R : Subring D) (hR : R < ⊤) :
    Field R :=
  { show DivisionRing R from Fintype.divisionRingOfIsDomain R with
    mul_comm := fun x y ↦ Subtype.ext <| hD R hR x.2 y.2 }

theorem center_eq_top [Finite D] (hD : InductionHyp D) : Subring.center D = ⊤ := by
  classical
  cases nonempty_fintype D
  set Z := Subring.center D
  by_contra hZ
  replace hZ := Ne.lt_top hZ
  letI : Field Z := hD.field Z hZ
  set q := Fintype.card Z with card_Z
  have hq : 1 < q := by rw [card_Z]; exact Fintype.one_lt_card
  let n := finrank Z D
  cases' le_or_lt n 1 with hn hn
  · rw [finrank_le_one_iff] at hn
    rcases hn with ⟨x, hx⟩
    refine' not_le_of_lt hZ _
    rintro y - z
    obtain ⟨r, rfl⟩ := hx y; obtain ⟨s, rfl⟩ := hx z
    show s.1 * x * (r.1 * x) = r.1 * x * (s.1 * x)
    rw [← r.2, ← s.2, mul_assoc, mul_assoc, ← r.2, ← s.2, mul_assoc, mul_assoc, r.2]
  have card_D : Fintype.card D = q ^ n := card_eq_pow_finrank
  have h1qn : 1 ≤ q ^ n := by rw [← card_D]; exact Fintype.card_pos
  have key := Group.nat_card_center_add_sum_card_noncenter_eq_card (Dˣ)
  simp only [Nat.card_eq_fintype_card] at key
  rw [Fintype.card_congr (show _ ≃* Zˣ from Subgroup.centerUnitsEquivUnitsCenter D).toEquiv,
      Fintype.card_units, ← card_Z, Fintype.card_units, card_D] at key
  let Φ := cyclotomic n ℤ
  have aux : Φ.eval ↑q ∣ (q : ℤ) ^ n - 1 := by
    simpa only [eval_X, eval_one, eval_pow, eval_sub, coe_evalRingHom] using
      (evalRingHom (q : ℤ)).map_dvd (cyclotomic.dvd_X_pow_sub_one n ℤ)
  apply_fun (Nat.cast : ℕ → ℤ) at key
  simp only [Nat.cast_one, Nat.cast_pow, Nat.cast_add, Nat.cast_sub h1qn] at key aux
  rw [← key, dvd_add_left, ← Int.natAbs_dvd, ← Int.dvd_natAbs] at aux
  simp only [Int.natAbs_ofNat, Int.coe_nat_dvd] at aux
  · refine' (Nat.le_of_dvd _ aux).not_lt (sub_one_lt_natAbs_cyclotomic_eval hn hq.ne')
    exact tsub_pos_of_lt hq
  suffices Φ.eval ↑q ∣ ↑(∑ x in (ConjClasses.noncenter (Dˣ)).toFinset, Fintype.card x.carrier)
    by
    convert this using 2
    convert finsum_cond_eq_sum_of_cond_iff _ _
    simp only [iff_self_iff, Set.mem_toFinset, imp_true_iff]
  simp only [Nat.cast_sum]
  apply Finset.dvd_sum
  rintro ⟨x⟩ hx
  simp only [ConjClasses.quot_mk_eq_mk]
  set Zx := Subring.centralizer ({↑x} : Set D)
  rw [ConjClasses.card_carrier, ←Fintype.card_congr
        (show Zxˣ ≃* _ from unitsCentralizerEquiv _ x).toEquiv, Fintype.card_units, card_D]
  have hZx : Zx < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hZx
    simp only [Set.mem_toFinset, ConjClasses.quot_mk_eq_mk] at hx
    refine (ConjClasses.mk_bijOn (Dˣ)).1 (Set.subset_center_units ?_) hx
    exact Subring.centralizer_eq_top_iff_subset.mp hZx <| Set.mem_singleton _
  letI : Field Zx := hD.field _ hZx
  letI : Algebra Z Zx :=
    (Subring.inclusion <| Subring.center_le_centralizer {(x : D)}).toAlgebra
  let d := finrank Z Zx
  have card_Zx : Fintype.card Zx = q ^ d := card_eq_pow_finrank
  have h1qd : 1 ≤ q ^ d := by rw [← card_Zx]; exact Fintype.card_pos
  haveI : IsScalarTower Z Zx D := ⟨fun x y z ↦ mul_assoc _ _ _⟩
  have hdn : d ∣ n := ⟨_, (finrank_mul_finrank Z Zx D).symm⟩
  rw [Fintype.card_units, card_Zx, Int.coe_nat_div]
  simp only [Nat.cast_sub h1qd, Nat.cast_sub h1qn, Nat.cast_one, Nat.cast_pow]
  suffices hd : d < n
  · apply Int.dvd_div_of_mul_dvd
    have aux : ∀ {k : ℕ}, ((X : ℤ[X]) ^ k - 1).eval ↑q = (q : ℤ) ^ k - 1 := by
      simp only [eval_X, eval_one, eval_pow, eval_sub, eq_self_iff_true, forall_const]
    rw [← aux, ← aux, ← eval_mul]
    refine' (evalRingHom ↑q).map_dvd (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ _)
    exact Nat.mem_properDivisors.mpr ⟨hdn, hd⟩
  rw [← (Nat.pow_right_strictMono hq).lt_iff_lt]
  dsimp
  rw [← card_D, ← card_Zx]
  obtain ⟨b, -, hb⟩ := SetLike.exists_of_lt hZx
  refine' Fintype.card_lt_of_injective_of_not_mem _ Subtype.val_injective (_ : b ∉ _)
  simp only [not_exists, Set.mem_range]
  rintro y rfl
  exact hb y.2

end InductionHyp

theorem center_eq_top [Finite D] : Subring.center D = ⊤ := by
  classical
  cases nonempty_fintype D
  suffices
    ∀ (n : ℕ) (D : Type _) [DivisionRing D] [Fintype D], Fintype.card D ≤ n → Subring.center D = ⊤
    by exact this _ D le_rfl
  clear! D
  intro n
  induction' n using Nat.strong_induction_on with n IH
  intros D _D_dr _D_fin hD
  apply InductionHyp.center_eq_top
  intro R hR x y hx hy
  suffices (⟨y, hy⟩ : R) ∈ Subring.center R by exact congr_arg Subtype.val (this ⟨x, hx⟩)
  letI R_dr : DivisionRing R := Fintype.divisionRingOfIsDomain R
  rw [IH (Fintype.card R) _ R le_rfl]
  · trivial
  obtain ⟨b, -, hb⟩ := SetLike.exists_of_lt hR
  refine' (Fintype.card_lt_of_injective_of_not_mem _ Subtype.val_injective _).trans_le hD
  · exact b
  simp only [not_exists, Set.mem_range]
  rintro y rfl
  exact hb y.2


end LittleWedderburn

def littleWedderburn (D : Type _) [hD : DivisionRing D] [Finite D] : Field D :=
  { hD with
    mul_comm := fun x y ↦ eq_top_iff.mp (LittleWedderburn.center_eq_top D) (Subring.mem_top y) x }
