/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusFunctoriality
import Nyll.AlgebraicCurves.Models.Charts.OpenPointValues
import Nyll.AlgebraicCurves.Models.FunctionFields.CurveRingEquivFunctionField
import Nyll.JacobianVarieties.Generalized.DivisorClassPoints
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniqueness
import Nyll.JacobianVarieties.Generalized.ModulusClassAbel
import Nyll.JacobianVarieties.Generalized.ModulusMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusEmptyRegularMap
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.CommGroupRelativeLaw

/-! # The actual Abel morphism has its full modulus

The principal-divisor quotient relation is transported through the proved
divisor-class comparison. This also proves the converse to universal
factorization, without replacing the modulus condition by a factorization
assumption in its definition.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GeneralizedJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  [GeometricallyIntegral M.toBase]
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))

/-- The actual pointed Abel morphism satisfies the full principal-divisor
modulus condition, in every degree. -/
theorem regularMapHasModulus_abel :
    M.regularMapHasModulus D (groupScheme M.toBase D)
      ⟨(modulusAbelMap M.toBase D ε).left, Over.w (modulusAbelMap M.toBase D ε)⟩ := by
  have hcurve : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have : HasPrincipalDivisors K F := hcurve.toHasPrincipalDivisors
  have ha := ((M.functionFieldModulus D).hasModulus_classAbel
    (M.modulusPlace D ε) (M.functionFieldModulus_modulusPlace_eq_zero D ε)
    (M.place_deg_eq_one (M.modulusPlace D ε))).map
      (M.divisorClassPointEquiv D).toAddMonoidHom
  apply Modulus.HasModulus.congr ha
  intro w hw
  obtain ⟨x, rfl⟩ := M.exists_modulusPlace_eq D w hw
  change M.divisorClassPointEquiv D
      ((M.functionFieldModulus D).classAbel (M.modulusPlace D ε)
        (M.functionFieldModulus_modulusPlace_eq_zero D ε)
        (M.place_deg_eq_one (M.modulusPlace D ε)) (M.modulusPlace D x)) =
    M.regularMapValues (modulusComplement (modulusCurveMap D))
      (groupScheme M.toBase D) _
      (M.openPointPlace (modulusComplement (modulusCurveMap D)) ⟨x.left, Over.w x⟩)
  rw [M.divisorClassPointEquiv_abel, M.regularMapValues_apply]
  rfl

/-- For a normalized regular map, the original principal-divisor condition
is equivalent to existence of an actual group-scheme Abel factor. -/
theorem regularMapHasModulus_iff_exists_groupHom
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom)
    (hε : ε ≫ Over.homMk q.1 q.2 = 1) :
    M.regularMapHasModulus D G q ↔
      ∃ φ : groupScheme M.toBase D ⟶ G,
        modulusAbelMap M.toBase D ε ≫ φ.hom.hom.hom = Over.homMk q.1 q.2 := by
  refine ⟨fun hmod => (M.existsUnique_groupHom_fullModulus D ε G q hmod hε).exists, ?_⟩
  rintro ⟨φ, hφ⟩
  let a : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)
      (groupScheme M.toBase D).X.hom :=
    ⟨(modulusAbelMap M.toBase D ε).left, Over.w (modulusAbelMap M.toBase D ε)⟩
  have hmod := M.regularMapHasModulus_comp D (groupScheme M.toBase D) a
    (M.regularMapHasModulus_abel D ε) G φ
  have hq :
      (commGroupPointEquiv G
        ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)).symm
          ((commGroupPointEquiv (groupScheme M.toBase D)
            ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) a) ≫ φ.hom.hom.hom) = q := by
    apply Subtype.ext
    exact congrArg (fun f => f.left) hφ
  rw [hq] at hmod
  exact hmod

end AlgebraicCurve.CurveModel
