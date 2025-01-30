/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

/-
For every displayed fibration we associate a 2-functor `C ⥤ Cat` whose value at an object `X` is the
is displayed fibres and the action on the morphism is given by the transport operation.
-/
-- todo: import needed stuff


-- def map (f : c ⟶ d) : (P⁻¹ c) ⥤ (P⁻¹ d) where
--   obj := CoTransport (P:= P) f
--   map :=  @fun x y g ↦ by let g₁ : x ⟶[𝟙 c] y := ⟨g.1, by simp [g.2]⟩
--                           let g₂ : y ⟶[f] CoTransport (P:= P) f y := (colift f y).lift
--                           let g₃ : x ⟶[(𝟙 c) ≫ f] CoTransport (P:= P) f y := BasedLift.Comp g₁ g₂
--                           let g₄ : x ⟶[f ≫ (𝟙 d)] CoTransport (P:= P) f y := BasedLift.EquivCompId.toFun (BasedLift.EquivIdComp.invFun g₃)
--                           refine {
--                             val := CoGapMap (g:= BasedLift f x) (𝟙 d) g₄   --((colift f x).is_cart.uniq_colift (𝟙 d) (g₄)).default.1.hom
--                             property := by simp only [Transport, Fib.mk_coe, BasedLift.Comp, Equiv.toFun_as_coe, BasedLift.EquivCompId, BasedLift.Id,
--                             comp_id, BasedLift.EquivIdComp, id_comp, Set.mem_setOf_eq, Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk,
--                             BasedLift.proj, Fib.proj, eqToHom_naturality, eqToHom_trans] -- aesop? generated proof
--                           }
--   map_id := by intro x; simp; symm; refine CoGapMap_uniq (BasedLift f x) (BasedLift.Comp (BasedLift f x) (BasedLift.Id x)  ) (BasedLift.Id (CoTransport (P:= P) f x)) ?_ -- apply Classical.choose_spec-- uniqueness of UP of lift
--   --apply ((colift f x).is_cart.uniq_colift (𝟙 d) _).uniq ⟨(BasedLift.Id (CoTransport (P:= P) f x)), sorry⟩  -- apply Classical.choose_spec-- uniqueness of UP of lift
--   map_comp := sorry -- uniquess of UP of lift


-- covariant functor of fibres.
-- map (f : c ⟶ d) : (F c) ⥤ (F d)
