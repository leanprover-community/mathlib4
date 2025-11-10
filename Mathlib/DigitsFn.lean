import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Indexes
import Mathlib.Data.Nat.Digits.Lemmas

/--
The first `l` digits, in little-endian order, of a natural number `n` in a specified base `b`.
Unlike `Nat.digits`, the last digits can be equal to `0` if `n` is too small.
-/
def Nat.digitsFin (b l : ℕ) : ℕ → Fin l → ℕ := fun x i ↦ (b.digits x)[i]?.getD 0

variable {b : ℕ} (n x : ℕ) (i : Fin n)

@[simp]
theorem Nat.digitsFin_apply_of_le (hb : 1 < b) (hx : b ^ i.val ≤ x) :
    haveI : i < (b.digits x).length := (Nat.lt_digits_length_iff hb _).mpr hx
    b.digitsFin n x i = (b.digits x)[↑i] := by
  rw [digitsFin, getElem?_pos, Option.getD_some]

@[simp]
theorem Nat.digitsFin_apply_of_lt (hb : 1 < b) (hx : x < b ^ i.val) : b.digitsFin n x i = 0 := by
  rw [digitsFin, getElem?_neg _ _ (by rwa [lt_digits_length_iff hb, not_le]), Option.getD_none]

@[simp]
theorem Nat.digitsFin_lt (hb : 1 < b) : b.digitsFin n x i < b := by
  by_cases hx : b ^ i.val ≤ x
  · rw [Nat.digitsFin_apply_of_le _ _ _ hb hx]
    exact Nat.digits_lt_base hb <| List.mem_of_getElem rfl
  · rw [Nat.digitsFin_apply_of_lt _ _ _ hb (by rwa [← not_le])]
    exact zero_lt_of_lt hb

theorem Nat.ofDigits_ofFn (f : Fin n → ℕ) :
    Nat.ofDigits b (List.ofFn f) = ∑ i, f i * b ^ i.val := by
  rw [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, Fin.sum_ofFn,
    ← Equiv.sum_comp (finCongr (List.length_ofFn)).symm]
  simp

theorem Nat.ofFn_digitsFin_of_lt (hb : 1 < b) (hx : x < b ^ n) :
    List.ofFn (b.digitsFin n x) = b.digits x ++ List.replicate (n - (b.digits x).length) 0 := by
  refine List.ext_getElem ?_ ?_
  · rw [List.length_ofFn, List.length_append, List.length_replicate, Nat.add_sub_cancel']
    rwa [Nat.digits_length_le_iff hb]
  · intro i hi hj
    rw [List.getElem_ofFn, List.getElem_append]
    split_ifs with h
    · rw [Nat.digitsFin_apply_of_le _ _ _ hb, Fin.getElem_fin]
      rwa [← Nat.lt_digits_length_iff hb]
    · rw [List.getElem_replicate, Nat.digitsFin_apply_of_lt _ _ _ hb]
      rwa [← Nat.digits_length_le_iff hb, ← not_lt]

theorem Nat.ofDigits_digitsFin (hb : 1 < b) (hx : x < b ^ n) :
    ofDigits b (List.ofFn (b.digitsFin n x)) = x := by
  rw [Nat.ofFn_digitsFin_of_lt _ _ hb hx, ofDigits_append_replicate_zero, ofDigits_digits]

example (hb : 1 < b) (hx : x < b ^ n) :
    ∑ i, b.digitsFin n x i * b ^ i.val = x := by
  rw [← Nat.ofDigits_ofFn, Nat.ofDigits_digitsFin _ _ hb hx]

theorem Nat.digitsFin_ofDigits (hb : 1 < b) (f : Fin n → ℕ)
    (hf : ∀ i, f i ∈ Finset.range b) :
    b.digitsFin n (ofDigits b (List.ofFn f)) = f := by
  simp only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.length_ofFn, List.get_eq_getElem,
    Fin.coe_cast, List.getElem_ofFn, Fin.eta, Fin.sum_ofFn]
  rw [← List.ofFn_inj]
  apply Nat.ofDigits_inj_of_len_eq hb
  · simp
  · intro _ h
    rw [List.mem_ofFn'] at h
    obtain ⟨i, rfl⟩ := h
    apply Nat.digitsFin_lt _ _ _ hb
  · simpa using hf
  rw [← Nat.ofDigits_ofFn, Nat.ofDigits_digitsFin _ _ hb]
  convert Nat.ofDigits_lt_base_pow_length hb (l := List.ofFn f) (by simpa using hf)
  rw [List.length_ofFn]

theorem Nat.digitsFin_sum (hb : 1 < b) (hx : x < b ^ n) :
    ∑ i, b.digitsFin n x i = (b.digits x).sum := by
  rw [← Fin.sum_ofFn, Nat.ofFn_digitsFin_of_lt _ _ hb hx, List.sum_append, List.sum_replicate,
    nsmul_zero, add_zero]

theorem Nat.digitsFin_mapsTo (hb : 1 < b) :
    Set.MapsTo (b.digitsFin n) (Finset.range (b ^ n))
      (Fintype.piFinset fun _ : Fin n ↦ Finset.range b) := by
  exact fun x hx ↦ Fintype.mem_piFinset.mpr fun _ ↦ Finset.mem_range.mpr <| digitsFin_lt n x _ hb

theorem Nat.digitsFin_injOn (hb : 1 < b) :
    Set.InjOn (Nat.digitsFin b n) (Finset.range (b ^ n)) := by
  rintro x hx y hy hxy
  rw [Finset.coe_range] at hx hy
  have := congr_arg (fun x ↦ ofDigits b (List.ofFn x)) hxy
  simpa [Nat.ofDigits_digitsFin _ _ hb hx, Nat.ofDigits_digitsFin _ _ hb hy] using this

theorem Nat.digitsFin_surjOn (hb : 1 < b) :
    Set.SurjOn (Nat.digitsFin b n) (Finset.range (b ^ n))
      (Fintype.piFinset fun _ : Fin n ↦ Finset.range b) := by
  intro f hf
  refine ⟨ofDigits b (List.ofFn f), ?_, ?_⟩
  · rw [Finset.coe_range, Set.mem_Iio]
    convert Nat.ofDigits_lt_base_pow_length hb ?_
    · exact List.length_ofFn.symm
    · grind [Fintype.coe_piFinset]
  · rw [digitsFin_ofDigits _ hb]
    simpa using hf

theorem Nat.digitsFin_bijOn (hb : 1 < b) :
    Set.BijOn (Nat.digitsFin b n) (Finset.range (b ^ n))
      (Fintype.piFinset fun _ : Fin n ↦ Finset.range b) :=
  ⟨digitsFin_mapsTo n hb, digitsFin_injOn n hb, digitsFin_surjOn n hb⟩

example (b l : ℕ) (hb : 1 < b) :
    ∑ x ∈ Finset.range (b ^ l), (b.digits x).sum = l * b ^ (l - 1) * (b * (b - 1) / 2) := by
  rw [Finset.sum_nbij (b.digitsFin l) (by exact b.digitsFin_mapsTo l hb)
    (Nat.digitsFin_injOn l hb) (Nat.digitsFin_surjOn l hb)
    (fun x hx ↦ (Nat.digitsFin_sum l x hb (List.mem_range.mp hx)).symm)]
  rw [Finset.sum_comm]
  simp_rw +contextual [fun i ↦ Finset.sum_comp
    (s := Fintype.piFinset fun x : Fin l ↦ Finset.range b) (f := fun x ↦ x) (g := fun x ↦ x i),
    Fintype.eval_image_piFinset_const, Fintype.card_filter_piFinset_const_eq_of_mem,
    Finset.card_range, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_range_id, Fintype.card_fin]
  ring
