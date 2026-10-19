/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Nyll.JacobianVarieties.Generalized.PoincareFrameQuotient
import Nyll.AlgebraicCurves.RelativeDivisors.LineBundles.InvertibleI
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealComapOpenImmersion
import Nyll.AlgebraicCurves.Geometry.Schemes.BaseChange.HomPullbackKerPowInvModuleIso

/-! # The actual Cartier ideal of the full modulus on the original curve -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicCurves.Geometry.Schemes.Proofs
open Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso.AlgebraicGeometry.BCKerGlue

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The full modulus ideal on the original curve, including every multiplicity. -/
abbrev modulusCurveIdeal : C.IdealSheafData := (modulusCurveMap D).ker

/-- The original-curve ideal is the transport of the given relative Cartier ideal. -/
theorem modulusCurveIdeal_eq_comap :
    modulusCurveIdeal D = D.I.comap (inv (pullback.fst c (𝟙 _))) := by
  let e := asIso (pullback.fst c (𝟙 (Spec (CommRingCat.of K))))
  have h : modulusCurveMap D ≫ e.inv = D.I.subschemeι := by
    change (D.I.subschemeι ≫ e.hom) ≫ e.inv = D.I.subschemeι
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  have hk := ker_comap_eq_ker e.inv D.I.subschemeι (modulusCurveMap D) h
  rw [Scheme.IdealSheafData.ker_subschemeι] at hk
  exact hk.symm

/-- Transport to the original curve preserves inclusion of the full ideals. -/
theorem modulusCurveIdeal_mono {d' : ℕ}
    (E : RelEffCartierDiv c d' (𝟙 (Spec (CommRingCat.of K))))
    (h : D.I ≤ E.I) : modulusCurveIdeal D ≤ modulusCurveIdeal E := by
  rw [modulusCurveIdeal_eq_comap, modulusCurveIdeal_eq_comap]
  exact Scheme.IdealSheafData.comap_mono _ h

/-- Actual relative Cartier data make the original full-modulus ideal invertible. -/
theorem modulusCurveIdeal_isInvertible [IsSeparated c] [SmoothOfRelativeDimension 1 c] :
    (modulusCurveIdeal D).IsInvertible := by
  rw [modulusCurveIdeal_eq_comap]
  exact (RelEffCartierDiv.isInvertible_I D).comap_of_isOpenImmersion _

end AlgebraicGeometry.GeneralizedJacobian
