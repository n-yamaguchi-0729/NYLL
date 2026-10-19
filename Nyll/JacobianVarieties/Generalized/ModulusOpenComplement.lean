/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusCurveIdeal
import Nyll.JacobianVarieties.Generalized.ModulusAbelFamily
import Nyll.AlgebraicCurves.Models.Charts.FiniteComplIsOpen
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.IEqProper

/-! # Realizing an open curve as a full modulus complement

Over any field, the finite closed boundary of a nonempty open on a smooth
proper integral curve supplies an actual relative effective Cartier divisor.
Its ideal is the reduced vanishing ideal of that boundary. This construction
does not require rational boundary points or an algebraically closed field.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [IsIntegral C]

/-- The original domain of a rational curve map is exactly the complement
of a constructed relative Cartier modulus, over the original field. -/
theorem exists_modulusComplement_eq (U : C.Opens) (hU : (U : Set C).Nonempty) :
    ∃ (d : ℕ) (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))),
      modulusComplement (modulusCurveMap D) = U := by
  let I : C.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal U.compl
  have hfinI : (I.support : Set C).Finite := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact AlgebraicCurve.finite_compl_of_isOpen c U hU
  have hfin : ((I.comap (pullback.fst c (𝟙 (Spec (CommRingCat.of K))))).support :
      Set ↥(pullback c (𝟙 (Spec (CommRingCat.of K))))).Finite := by
    rw [Scheme.IdealSheafData.support_comap]
    change ((pullback.fst c (𝟙 (Spec (CommRingCat.of K)))) ⁻¹' (I.support : Set C)).Finite
    exact Set.Finite.preimage
      (pullback.fst c (𝟙 (Spec (CommRingCat.of K)))).isOpenEmbedding.injective.injOn hfinI
  obtain ⟨d, D, hD⟩ := RelEffCartierDiv.exists_I_eq_of_isProper_of_support_finite
    (𝟙 (Spec (CommRingCat.of K))) _ hfin
  have hDI : modulusCurveIdeal D = I := by
    rw [modulusCurveIdeal_eq_comap, hD, ← Scheme.IdealSheafData.comap_comp,
      IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  refine ⟨d, D, ?_⟩
  change (modulusCurveIdeal D).support.compl = U
  rw [hDI]
  apply SetLike.coe_injective
  change (I.support : Set C)ᶜ = (U : Set C)
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact compl_compl (U : Set C)

end AlgebraicGeometry.GeneralizedJacobian
