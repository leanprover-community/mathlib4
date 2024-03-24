import Mathlib.Data.Sym2.Basic
import Mathlib.Data.Finset.Prod

namespace Sym2

variable {α : Type*} [DecidableEq α]

theorem filter_image_mk_isDiag (s : Finset α) :
    ((s ×ˢ s).image Sym2.mk).filter IsDiag = s.diag.image Sym2.mk := by
  simp_rw [Finset.filter_image, isDiag_iff_proj_eq, Finset.filter_eq_product_eq_diag]
#align sym2.filter_image_quotient_mk_is_diag Sym2.filter_image_mk_isDiag

theorem filter_image_mk_not_isDiag (s : Finset α) :
    (((s ×ˢ s).image Sym2.mk).filter fun a : Sym2 α => ¬a.IsDiag) =
      s.offDiag.image Sym2.mk := by
  simp_rw [Finset.filter_image, isDiag_iff_proj_eq, Finset.offDiag]
#align sym2.filter_image_quotient_mk_not_is_diag Sym2.filter_image_mk_not_isDiag
