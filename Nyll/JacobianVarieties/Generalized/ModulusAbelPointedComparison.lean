/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelOneMap
import Nyll.JacobianVarieties.Generalized.ModulusAbelMap
import Nyll.JacobianVarieties.Generalized.PicardOnePointedConstruction
import Nyll.JacobianVarieties.Generalized.PicardOneSheafTorsor

/-! # Actual point translation identifies the intrinsic and pointed Abel morphisms -/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))

/-- Tensoring the actual point difference with its basepoint recovers the original point class. -/
theorem modulusAbelOneClass_eq_translation
    {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    modulusPicardOneTranslationEquiv c (modulusCurveMap D) ε T
        (modulusAbelZeroClass c (modulusCurveMap D) ε x) =
      (modulusAbelOnePresheafMap c (modulusCurveMap D)).app (op T) (ULift.up x) := by
  apply Subtype.ext
  exact div_mul_cancel (modulusAbelPointClass c (modulusCurveMap D) (T := T) x)
    (modulusGroundClass c (modulusCurveMap D)
      (modulusAbelPointClass c (modulusCurveMap D)
        (T := Over.mk (𝟙 (Spec (CommRingCat.of K)))) ε) T)

/-- The same equality holds for the actual fppf classes, with their chosen rigidifications. -/
theorem modulusAbelOneSheafClass_eq_translation
    {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    modulusPicardOneSheafTranslationEquiv c (modulusCurveMap D) ε T
        (modulusAbelZeroSheafClass c D ε x) =
      (modulusAbelOneSheafMap c (modulusCurveMap D)).app (op T) (ULift.up x) :=
  (modulusPicardOneSheafTranslationEquiv_actual c (modulusCurveMap D) ε T
    (modulusAbelZeroClass c (modulusCurveMap D) ε x)).trans
      (congrArg ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (modulusPicardOnePresheaf c (modulusCurveMap D))).app (op T))
          (modulusAbelOneClass_eq_translation c D ε x))

/-- On the pointed carrier the degree-one and point-difference constructions give one morphism. -/
theorem modulusAbelOneMap_eq_pointed : modulusAbelOneMap c D ε = modulusAbelMap c D ε := by
  apply (picardOnePointedRepresentable c D ε).homEquiv.injective
  have hOne := modulusAbelOneMap_classifies c D ε (𝟙 _)
  have hZero := modulusAbelMap_classifies c D ε (𝟙 _)
  rw [Category.id_comp] at hOne hZero
  rw [hOne]
  change _ = modulusPicardOneSheafTranslationEquiv c (modulusCurveMap D) ε _
    ((groupRepresentable c D).homEquiv (modulusAbelMap c D ε))
  rw [hZero]
  exact (modulusAbelOneSheafClass_eq_translation c D ε (𝟙 _)).symm

/-- An actual rational complement point trivializes the descended Picard-one torsor. -/
def picardOneTrivialization : picardOne c D ≅ (groupScheme c D).X :=
  (picardOneRepresentable c D).uniqueUpToIso (picardOnePointedRepresentable c D ε)

/-- Trivializing the intrinsic Abel morphism gives the actual pointed Abel morphism. -/
theorem abelOneMap_trivializes :
    abelOneMap c D ≫ (picardOneTrivialization c D ε).hom = modulusAbelMap c D ε := by
  rw [← modulusAbelOneMap_eq_pointed c D ε]
  apply (picardOnePointedRepresentable c D ε).homEquiv.injective
  change (picardOnePointedRepresentable c D ε).homEquiv
      (abelOneMap c D ≫ (picardOnePointedRepresentable c D ε).homEquiv.symm
        ((picardOneRepresentable c D).homEquiv (𝟙 _))) = _
  rw [(picardOnePointedRepresentable c D ε).homEquiv_comp, Equiv.apply_symm_apply,
    ← (picardOneRepresentable c D).homEquiv_comp, Category.comp_id]
  have hOne := modulusAbelOneMap_classifies c D ε (𝟙 _)
  have h := abelOneMap_classifies c D (𝟙 _)
  rw [Category.id_comp] at hOne h
  exact h.trans hOne.symm

end AlgebraicGeometry.GeneralizedJacobian
