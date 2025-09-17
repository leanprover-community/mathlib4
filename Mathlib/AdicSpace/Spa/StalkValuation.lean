import Mathlib.AdicSpace.Spa.StructurePresheaf

universe u

open Topology CategoryTheory TopologicalSpace UniformSpace TopCat

section Valuation

def TopCat.Presheaf.forgetToRing {X : TopCat.{u}} (ℱ : X.Presheaf TopCommRingCat) :
    X.Presheaf CommRingCat :=
  ℱ ⋙ forget₂ TopCommRingCat CommRingCat

namespace spa

-- namespace rational_open_data

-- /-- The natural map from A<T/s> to the completion of the valuation field of a valuation v
-- contained in R(T/s). -/
-- noncomputable def to_complete_valuation_field (r : rational_open_data A) {v : spa A}
--   (hv : v ∈ r.open_set) :
--   rat_open_data_completion r → completion (valuation_field (Spv.out v.1)) :=
-- completion.map (Huber_pair.rational_open_data.to_valuation_field hv)

-- variables {r r1 r2 : rational_open_data A} {v : spa A} (hv : v ∈ r.open_set)

-- /-- The natural map from A<T/s> to the completion of the valuation field of a valuation v
-- contained in R(T/s) is a ring homomorphism. -/
-- instance to_complete_valuation_field_is_ring_hom :
--   is_ring_hom (r.to_complete_valuation_field hv) :=
-- completion.is_ring_hom_map (Huber_pair.rational_open_data.to_valuation_field_cts hv)

-- -- Next we need to show that the completed maps to K_v-hat
-- -- all commute with the restriction maps.

-- /-- The maps from rationals opens to completions commute with allowable restriction maps. -/
-- theorem to_valuation_field_commutes (hv1 : v ∈ r1.open_set) (hv2 : v ∈ r2.open_set)
--   (h : r1 ≤ r2) :
--   (r2.to_complete_valuation_field hv2) ∘ (rat_open_data_completion.restriction h) =
--   (r1.to_complete_valuation_field hv1) :=
-- begin
--   delta to_complete_valuation_field,
--   delta rat_open_data_completion.restriction,
--   have uc1 : uniform_continuous (rational_open_data.localization_map h),
--     from rational_open_data.localization_map_is_uniform_continuous h,
--   have uc2 : uniform_continuous (Huber_pair.rational_open_data.to_valuation_field hv2),
--     from uniform_continuous_of_continuous (Huber_pair.rational_open_data.to_valuation_field_cts
--       hv2),
--   rw [Huber_pair.rational_open_data.to_valuation_field_commutes hv1 hv2 h,
--     completion.map_comp uc2 uc1]
-- end

-- end rational_open_data

-- -- Now we need to show that for any 𝒪_X(U) with v in U we have a map to K_v-hat.
-- -- First let's write a noncomputable function which gets a basis element.
-- section
-- variables {v : spa A} {U : opens (spa A)}

-- lemma exists_rational_open_subset (hv : v ∈ U) :
--   ∃ r : rational_open_data_subsets U, v ∈ r.1.open_set :=
-- begin
--   suffices : U.1 ∈ nhds v,
--   { rw mem_nhds_of_is_topological_basis (rational_basis.is_basis) at this,
--     rcases this with ⟨_, ⟨r, rfl⟩, hv, hr⟩,
--     use ⟨r, hr⟩,
--     exact hv, },
--   apply mem_nhds_sets U.2 hv,
-- end

-- /-- Given an open set U and a valuation v, this function chooses a random rational open subset
-- containing v and contained in U. -/
-- noncomputable def rational_open_subset_nhd (hv : v ∈ U) :
--   rational_open_data_subsets U :=
-- classical.some $ spa.exists_rational_open_subset hv

-- lemma mem_rational_open_subset_nhd (hv : v ∈ U) :
--   v ∈ (spa.rational_open_subset_nhd hv).1.open_set :=
-- classical.some_spec $ spa.exists_rational_open_subset hv

-- end

-- namespace presheaf
-- open rational_open_data
-- variables {v : spa A} {U : opens (spa A)} (hv : v ∈ U) (f : spa.presheaf_value U)

-- /-- The map from F(U) to K_v for v ∈ U, that restricts a section of the structure presheaf
-- to the completion of the valuation field of v. -/
-- noncomputable def to_valuation_field_completion :
--   completion (valuation_field (Spv.out v.1)) :=
-- to_complete_valuation_field _ (spa.mem_rational_open_subset_nhd hv) $
--   f.1 $ spa.rational_open_subset_nhd hv

-- /--
-- Restricting a section of the structure presheaf to a smaller open set is a ring homomorphism.
-- -/
-- instance restriction_is_ring_hom (U : opens (spa A)) (r : rational_open_data_subsets U) :
--   is_ring_hom (λ (f : presheaf_value U), f.val r) :=
-- { map_one := rfl,
--   map_mul := λ _ _, rfl,
--   map_add := λ _ _, rfl }

-- /-- The map that restricts a section of the structure presheaf above U to the completion of
-- the valuation field of v ∈ U is a ring homomorphism. -/
-- instance : is_ring_hom (to_valuation_field_completion hv) :=
-- begin
--   show is_ring_hom
--     ((to_complete_valuation_field _ (spa.mem_rational_open_subset_nhd hv)) ∘
--       (λ (f : presheaf_value U), (f.val (spa.rational_open_subset_nhd hv)))),
--   exact is_ring_hom.comp _ _,
-- end

-- -- We need to prove that if V ⊆ U then to_valuation_field_completion commutes with restriction.

-- -- Before we even start with this terrifying noncomputable spa.rational_open_subset_nhd
-- -- let's check that spa.rat_open_data_completion.to_complete_valuation_field commutes with ≤.

-- -- We will place these helper lemmas in a separate namespace

-- namespace to_valuation_field_completion_well_defined
-- variables {r1 r2 : rational_open_data_subsets U}
-- variables (h1 : v ∈ r1.1.open_set) (h2 : v ∈ r2.1.open_set)
-- include h1 h2

-- lemma aux₁ :
--   to_complete_valuation_field _ h1 (f.1 r1) = to_complete_valuation_field _
--     (show v ∈ (r1.1.inter r2.1).open_set, by { rw inter_open_set, exact ⟨h1, h2⟩ })
--   (f.1 (rational_open_data_subsets_inter r1 r2)) :=
-- begin
--   rw ← to_valuation_field_commutes h1 _ (rational_open_data.le_inter_left r1.1 r2.1),
--   swap, { rw rational_open_data.inter_open_set, exact ⟨h1, h2⟩ },
--   delta function.comp,
--   congr' 1,
--   -- exact times out here; convert closes the goal really quickly
--   convert f.2 r1 (rational_open_data_subsets_inter r1 r2) _,
-- end

-- -- now the other way
-- lemma aux₂ :
--   to_complete_valuation_field _ h2 (f.1 r2) = to_complete_valuation_field _
--     (show v ∈ (r1.1.inter r2.1).open_set, by { rw inter_open_set, exact ⟨h1, h2⟩ })
--   (f.1 (rational_open_data_subsets_inter r1 r2)) :=
-- begin
--   rw ← to_valuation_field_commutes h2 _ (rational_open_data.le_inter_right r1.1 r2.1),
--   swap, { rw rational_open_data.inter_open_set, exact ⟨h1, h2⟩ },
--   delta function.comp,
--   congr' 1,
--   -- exact times out here; convert closes the goal really quickly
--   convert f.2 r2 (rational_open_data_subsets_inter r1 r2) _,
-- end

-- -- now let's check it agrees on any rational_open_data_subsets
-- lemma aux₃ :
--   to_complete_valuation_field _ h1 (f.1 r1) = to_complete_valuation_field _ h2 (f.1 r2) :=
-- by rw [aux₁ f h1 h2, aux₂ f h1 h2]

-- end to_valuation_field_completion_well_defined

-- -- next I will prove that for every r : rational_open_data_subsets U with v ∈ r.1.rational_open,
-- -- f gets sent to the same thing.
-- lemma to_valuation_field_completion_well_defined
--   (r : rational_open_data_subsets U) (hr : v ∈ r.1.open_set) :
--   to_valuation_field_completion hv f = to_complete_valuation_field _ hr (f.1 r) :=
-- to_valuation_field_completion_well_defined.aux₃ f _ hr

-- -- now the main goal

-- /-- If v ∈ U then the map from 𝒪_X(U) to `completion (valuation_field v)`
--     commutes with restriction (so we can get a map from the stalk at v) -/
-- theorem to_valuation_field_completion_commutes {U V : opens (spa A)} (hv : v ∈ U)
--   (hUV : U ⊆ V) (f : spa.presheaf_value V) :
--   to_valuation_field_completion (hUV hv) f =
--   to_valuation_field_completion hv (spa.presheaf_map hUV f) :=
-- begin
--   -- to_valuation_field_completion involves choosing a random basis element.
--   let rU := rational_open_subset_nhd hv,
--   let rV := rational_open_subset_nhd (hUV hv),
--   -- we now need to intersect these two things.
--   let rUV1 := rU.1.inter rV.1,
--   rw [to_valuation_field_completion_well_defined hv (spa.presheaf_map hUV f) ⟨rUV1, _⟩,
--       to_valuation_field_completion_well_defined (hUV hv) f ⟨rUV1, _⟩],
--   { refl },
--   { rw rational_open_data.inter_open_set,
--     exact ⟨mem_rational_open_subset_nhd hv, mem_rational_open_subset_nhd _⟩, },
--   { rw rational_open_data.inter_open_set,
--     exact set.subset.trans (set.inter_subset_left _ _) rU.2 },
-- end

-- set_option class.instance_max_depth 49

-- /--An auxiliary function in the definition of the valuations on the stalks
-- of the structure presheaf of the adic spectrum of a Huber pair:
-- the valuation is obtained by pulling back a valuation along this function.

-- It is the natural map from the stalk above a point in spa(A),
-- which is an equivalence class of valuations,
-- to the completion of the valuation field of a valuation
-- that is a representative of this equivalence class. -/
-- noncomputable def stalk_to_valuation_field (x : spa A) :
--   stalk_of_rings (spa.presheaf_of_topological_rings A).to_presheaf_of_rings x →
--   completion (valuation_field (Spv.out x.1)) :=
-- to_stalk.rec (spa.presheaf_of_topological_rings A).to_presheaf_of_rings x
--   (completion (valuation_field (Spv.out x.1))) (λ U hxU, to_valuation_field_completion hxU)
--   (λ U V HUV r hxU, (to_valuation_field_completion_commutes hxU HUV r).symm)

-- /-- The natural map from the stalk above a point v in spa(A) to the
-- completion of the valuation field of v is a ring homomorphism. -/
-- instance stalk_to_valuation_field.is_ring_hom (x : spa A) :
--   is_ring_hom (stalk_to_valuation_field x) := to_stalk.rec_is_ring_hom _ _ _ _ _

/-- The valuation on the stalk of the structure presheaf of the adic spectrum. -/
def stalk_valuation (A : HuberPair) (x : of (spa A)) :
    Spv (((spa.presheaf A).forgetToRing).stalk x) :=
  sorry

-- end presheaf

end spa

end Valuation
