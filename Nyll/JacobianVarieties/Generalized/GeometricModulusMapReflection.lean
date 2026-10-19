/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeometricModulusMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusMapScalarExtension
import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusFunctoriality
import Nyll.AlgebraicCurves.Models.Charts.OpenPointValues
import Nyll.AlgebraicCurves.Models.FunctionFields.CurveRingEquivFunctionField
import Nyll.SchemeTheory.GroupSchemes.AbelianScheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # Reflection of the full modulus through group embeddings

The actual point evaluator commutes with a group-scheme homomorphism. An
injective map on these points therefore reflects the full principal-divisor
condition. Pullback preserves monomorphisms, so the same reflection holds
over every algebraically closed extension, in particular for a closed
immersion of commutative group schemes.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GeneralizedJacobian AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
  (G H : CommGrp (Over (Spec (CommRingCat.of K))))
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom)
  (φ : G ⟶ H)

/-- Injectivity on the actual rational group points reflects the complete
principal-divisor modulus of a regular map, including its multiplicities. -/
theorem regularMapHasModulus_comp_iff_of_injective
    (hφ : Function.Injective (fun x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X =>
      x ≫ φ.hom.hom.hom)) :
    M.regularMapHasModulus D H
        ((commGroupPointEquiv H
          ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)).symm
          ((commGroupPointEquiv G
            ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) q) ≫
              φ.hom.hom.hom)) ↔ M.regularMapHasModulus D G q := by
  have hcurve : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have : HasPrincipalDivisors K F := hcurve.toHasPrincipalDivisors
  let f := (IsMonHom.monoidHom φ.hom.hom.hom
    (Over.mk (𝟙 (Spec (CommRingCat.of K))))).toAdditive
  have hf : Function.Injective f := by
    intro x y hxy
    exact congrArg Additive.ofMul (hφ (congrArg Additive.toMul hxy))
  change (M.cartierModulus (modulusCurveIdeal D)
    (modulusCurveIdeal_isInvertible D)).HasModulus _ ↔
      (M.cartierModulus (modulusCurveIdeal D)
        (modulusCurveIdeal_isInvertible D)).HasModulus _
  rw [funext (M.regularMapValues_comp (modulusComplement (modulusCurveMap D)) G H q φ)]
  exact Modulus.hasModulus_map_iff f hf

end AlgebraicCurve.CurveModel

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (G H : CommGrp (Over (Spec (CommRingCat.of K))))
  (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X)
  (φ : G ⟶ H)

/-- A monomorphism of actual group schemes reflects the full geometric
modulus. Its scalar extensions remain monomorphisms, and the constructed
point evaluators detect each principal-divisor relation before composition. -/
theorem geometricRegularMapHasModulus_comp_iff [Mono φ.hom.hom.hom] :
    geometricRegularMapHasModulus c D H (q ≫ φ.hom.hom.hom) ↔
      geometricRegularMapHasModulus c D G q := by
  refine ⟨?_, fun hmod => geometricRegularMapHasModulus_comp c D G H q hmod φ⟩
  intro hmod L fieldL algebraL closedL cL DL algL ML qL
  let G_L := (GroupSchemes.baseChange (specMap K L)).obj G
  let HL := (GroupSchemes.baseChange (specMap K L)).obj H
  let φL := (GroupSchemes.baseChange (specMap K L)).map φ
  have : Mono φL.hom.hom.hom := by
    change Mono ((Over.pullback (specMap K L)).map φ.hom.hom.hom)
    infer_instance
  apply (ML.regularMapHasModulus_comp_iff_of_injective DL G_L HL
    ⟨qL.left, Over.w qL⟩ φL (fun _ _ h => (cancel_mono φL.hom.hom.hom).mp h)).mp
  change ML.regularMapHasModulus DL HL
    ((commGroupPointEquiv HL ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm
      (qL ≫ φL.hom.hom.hom))
  rw [← modulusGroupMapScalarExtension_comp c D L G H q φ]
  exact hmod L

/-- A closed immersion of commutative group schemes neither creates nor
loses a geometric full modulus for an actual regular curve map. -/
theorem geometricRegularMapHasModulus_comp_iff_of_isClosedImmersion
    [IsClosedImmersion φ.hom.hom.hom.left] :
    geometricRegularMapHasModulus c D H (q ≫ φ.hom.hom.hom) ↔
      geometricRegularMapHasModulus c D G q := by
  have : Mono φ.hom.hom.hom := Over.mono_of_mono_left φ.hom.hom.hom
  exact geometricRegularMapHasModulus_comp_iff c D G H q φ

end AlgebraicGeometry.GeneralizedJacobian
