/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Charts.OpenPointValues
import Nyll.AlgebraicCurves.Models.FunctionFields.CurveRingEquivFunctionField
import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusFunctoriality
import Nyll.AlgebraicCurves.Models.Divisors.CartierModulus
import Nyll.JacobianVarieties.Generalized.ModulusAbelFamily
import Nyll.JacobianVarieties.Generalized.ModulusCurveIdeal
import Nyll.JacobianVarieties.Generalized.ModulusEvaluation

/-! # The full modulus condition for an actual regular group-valued map

This condition is the principal-divisor definition applied to the actual
morphism's constructed values. Its scope here is an algebraically closed
base field. It does not assert existence of a modulus for a general map.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory NeronModelInfra
open AlgebraicGeometry.GeneralizedJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
  (G : CommGrp (Over (Spec (CommRingCat.of K))))
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom)

/-- The principal-divisor modulus condition for the given actual regular map. -/
def regularMapHasModulus : Prop :=
  (M.cartierModulus (modulusCurveIdeal D) (modulusCurveIdeal_isInvertible D)).HasModulus
    (M.regularMapValues (modulusComplement (modulusCurveMap D)) G q)


/-- An actual group-scheme homomorphism preserves the full modulus of a regular map. -/
theorem regularMapHasModulus_comp (hmod : M.regularMapHasModulus D G q)
    (H : CommGrp (Over (Spec (CommRingCat.of K)))) (φ : G ⟶ H) :
    M.regularMapHasModulus D H
      ((GoodReductionJacobian.commGroupPointEquiv H
        ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)).symm
          ((GoodReductionJacobian.commGroupPointEquiv G
            ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) q) ≫
              φ.hom.hom.hom)) := by
  have hcurve : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have : HasPrincipalDivisors K F := hcurve.toHasPrincipalDivisors
  let f := (IsMonHom.monoidHom φ.hom.hom.hom
    (Over.mk (𝟙 (Spec (CommRingCat.of K))))).toAdditive
  have hmap := Modulus.HasModulus.map hmod f
  change (M.cartierModulus (modulusCurveIdeal D)
    (modulusCurveIdeal_isInvertible D)).HasModulus _ at hmap ⊢
  have heq := funext (M.regularMapValues_comp
    (modulusComplement (modulusCurveMap D)) G H q φ)
  rw [heq]
  exact hmap

end AlgebraicCurve.CurveModel
