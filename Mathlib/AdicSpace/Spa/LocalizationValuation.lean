-- import Mathlib.AdicSpace.Spa.RationalOpenData

-- /-!
-- # Extending continuous valuations on Huber rings

-- In this file, we extend continuous valuations on Huber rings R
-- to rational localizations R(T/s) and their completions.

-- This is an important step in the definition of the structure presheaf on the adic spectrum.
-- -/

-- -- noncomputable theory

-- -- local attribute [instance] valued.subgroups_basis valued.uniform_space

-- -- local postfix `⁺` : 66 := λ A : Huber_pair, A.plus

-- variable {A : HuberPair}
--   -- {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀] {v : valuation A Γ₀}
--   {rd : spa.rationalOpenData A} (v : Spv A) (hv : v.IsContinuous)

-- namespace HuberPair
-- -- open valuation linear_ordered_structure

-- open scoped Pointwise

-- -- local attribute [instance] set.smul_set_action

-- -- local notation `A⟮T/s⟯` := spa.rational_open_data.localization rd
-- -- local notation `s` := rd.s
-- -- local notation `T` := rd.T

-- /-- An auxilliary definition that constructs s as unit in the valuation field
-- of a valuation v, under the assumption that v s ≠ 0.-/
-- def unit_s (hs : v rd.s ≠ 0) : units (valuation_field v) :=
-- units.mk0 (valuation_field_mk v s) $ valuation_field_mk_ne_zero v s hs

-- example : (λ r, localization.of (valuation_ID_mk v r)) = valuation_field_mk v := rfl

-- set_option class.instance_max_depth 64

-- /--The set T/s (for some rational open subset D(T,s)) considered as subset of the valuation field.-/
-- def v_T_over_s (hs : v s ≠ 0) : set (valuation_field v) :=
-- ((unit_s hs)⁻¹ : v.valuation_field) • ((valuation_field_mk v) '' rd.T)

-- lemma v_T_over_s_le_one (hs : v s ≠ 0) (hT2 : ∀ t : A, t ∈ T → v t ≤ v s) :
--   v_T_over_s hs ⊆ {x : valuation_field v | valuation_field.canonical_valuation v x ≤ 1} :=
-- begin
--   let v' := valuation_field.canonical_valuation v,
--   intros k Hk,
--   show v' k ≤ 1,
--   let u := unit_s hs,
--   have remember_this : valuation_field_mk v s = u.val := rfl,
--   unfold v_T_over_s at Hk,
--   rcases Hk with ⟨l, ⟨t, ht, rfl⟩, rfl⟩,
--   rw [smul_eq_mul, v'.map_mul],
--   change v' (↑(unit_s hs)⁻¹) * _ ≤ _,
--   rw mul_comm,
--   apply le_of_le_mul_right
--     (group_with_zero.unit_ne_zero $ units.map (v' : v.valuation_field →* (value_monoid v)) u),
--   show v' _ * v' _ * v' u ≤ _,
--   rw [mul_assoc, one_mul, ← v'.map_mul, units.inv_mul, v'.map_one, mul_one],
--   change canonical_valuation v t ≤ v' u.val,
--   rw ← remember_this,
--   change _ ≤ canonical_valuation v s,
--   rw canonical_valuation_is_equiv v,
--   exact hT2 _ ht,
-- end

-- lemma v_le_one_is_bounded {R : Type*} [comm_ring R] (v : valuation R Γ₀) :
--   is_bounded {x : valuation_field v | valuation_field.canonical_valuation v x ≤ 1} :=
-- begin
--   let v' := valuation_field.canonical_valuation v,
--   intros U HU,
--   rcases subgroups_basis.mem_nhds_zero.mp HU with ⟨_, ⟨γ, rfl⟩, H⟩,
--   let V := {k : valuation_field v | v' k < ↑γ},
--   use V,
--   existsi _, swap,
--   { rw subgroups_basis.mem_nhds_zero,
--     use [V, set.mem_range_self _] },
--   intros w Hw b Hb,
--   change V ⊆ U at H,
--   change v' w < γ at Hw,
--   change v' b ≤ 1 at Hb,
--   apply set.mem_of_mem_of_subset _ H,
--   change v' (w * b) < γ,
--   rw v'.map_mul,
--   exact actual_ordered_comm_monoid.mul_lt_of_lt_of_nongt_one' Hw Hb,
-- end

-- lemma v_le_one_is_power_bounded {R : Type*} [comm_ring R] (v : valuation R Γ₀) :
--   is_power_bounded_subset {x : valuation_field v | valuation_field.canonical_valuation v x ≤ 1} :=
-- begin
--   let v' := valuation_field.canonical_valuation v,
--   refine is_bounded.subset _ (v_le_one_is_bounded v),
--   intros x hx,
--   induction hx with a ha a b ha' hb' ha hb,
--   { assumption },
--   { show v' 1 ≤ 1, rw v'.map_one, },
--   { show v' (a * b) ≤ 1, rw v'.map_mul,
--     exact actual_ordered_comm_monoid.mul_nongt_one' ha hb, }
-- end

-- lemma v_T_over_s_is_power_bounded (hs : v s ≠ 0) (hT2 : ∀ t : A, t ∈ T → v t ≤ v s) :
--   is_power_bounded_subset (v_T_over_s hs) :=
-- begin
--   apply power_bounded.subset (v_T_over_s_le_one hs hT2),
--   exact v_le_one_is_power_bounded v
-- end

-- /--The natural map from the localization A⟮T/s⟯ of a Huber pair A
-- at a rational open subset R(T/s)
-- to the valuation field of a valuation that does not have s in its support.-/
-- noncomputable def to_valuation_field (hs : v s ≠ 0) : A⟮T/s⟯ → (valuation_field v) :=
-- Huber_ring.away.lift T s (valuation_field_mk v) (unit_s hs) rfl

-- /-- The natural map from A⟮T/s⟯ to the valuation field is a ring homomorphism. -/
-- instance (hs : v s ≠ 0) : is_ring_hom (to_valuation_field hs) :=
-- by delta to_valuation_field; apply_instance

-- local attribute [instance] valued.subgroups_basis

-- theorem to_valuation_field_cts' (hs : v s ≠ 0)(hT2 : ∀ t : A, t ∈ T → v t ≤ v s) (hv : is_continuous v) :
--   continuous (to_valuation_field hs) :=
-- Huber_ring.away.lift_continuous T s (by convert subgroups_basis.nonarchimedean)
--   (continuous_valuation_field_mk_of_continuous v hv) _ rfl (rd.Hopen)
--   (v_T_over_s_is_power_bounded hs hT2)

-- -- now we need that the triangles commute when we fix v but change s.

-- theorem to_valuation_field_commutes (r1 r2 : spa.rational_open_data A) (h : r1 ≤ r2)
--   (hs1 : v r1.s ≠ 0) (hs2 : v r2.s ≠ 0) :
-- to_valuation_field hs1 = (to_valuation_field hs2) ∘ (spa.rational_open_data.localization_map h) :=
-- begin
--   refine localization.funext
--     (to_valuation_field hs1 : localization A (powers r1.s) → valuation_field v)
--     ((to_valuation_field hs2) ∘ (spa.rational_open_data.localization_map h) :
--       localization A (powers r1.s) → valuation_field v) _,
--   intro r,
--   delta to_valuation_field spa.rational_open_data.localization_map function.comp,
--   erw Huber_ring.away.lift_of,
--   erw Huber_ring.away.lift_of,
--   change _ = Huber_ring.away.lift (r2.T) (r2.s) _ _ _ (localization.of r),
--   rw Huber_ring.away.lift_of,
-- end

-- namespace rational_open_data

-- lemma to_valuation_field_cts_aux {r : spa.rational_open_data A} {v : spa A}
-- (hv : v ∈ r.open_set) : (Spv.out v.1) (r.s) ≠ 0 := hv.2

-- /-- The natural map from A(T/s) to the valuation field of a valuation v contained in
-- the rational open subset R(T/s). -/
-- def to_valuation_field {r : spa.rational_open_data A} {v : spa A} (hv : v ∈ r.open_set) :
--   spa.rational_open_data.localization r → valuation_field (Spv.out (v.val)) :=
-- (to_valuation_field $ to_valuation_field_cts_aux hv)

-- /-- The natural map from A(T/s) to the valuation field of a valuation v contained in
-- the rational open subset R(T/s) is a ring homomorphism. -/
-- instance {r : spa.rational_open_data A} {v : spa A} (hv : v ∈ r.open_set) :
--   is_ring_hom (to_valuation_field hv) := by {delta to_valuation_field, apply_instance}

-- /-- If v : spa A is in D(T,s) then the map A(T/s) -> K_v is continuous -/
-- theorem to_valuation_field_cts {r : spa.rational_open_data A} {v : spa A}
--   (hv : v ∈ r.open_set) : continuous (to_valuation_field hv) :=
-- Huber_pair.to_valuation_field_cts' hv.2 hv.1 v.2.1

-- -- Now we need to show that if r1 <= r2 then these to_valuation_field maps
-- -- are compatible.

-- theorem to_valuation_field_commutes {r1 r2 : spa.rational_open_data A} {v : spa A}
--   (hv1 : v ∈ r1.open_set) (hv2 : v ∈ r2.open_set) (h : r1 ≤ r2) :
--   (to_valuation_field hv1) =
--   (to_valuation_field hv2) ∘ (spa.rational_open_data.localization_map h) :=
-- to_valuation_field_commutes r1 r2 h hv1.2 hv2.2

-- end rational_open_data

-- end Huber_pair
