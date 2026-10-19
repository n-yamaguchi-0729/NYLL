/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeometricModulusUniversalProperty
import Nyll.JacobianVarieties.Generalized.PicardOneEquivariantMap
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniquenessGeometric
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorCoordinates

/-! # Pointed universality in every modulus degree

The intrinsic torsor theorem yields the translated group factorization.
The empty modulus, arbitrary ground fields and nonproper separated group
targets are all included in the same statement.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
  (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated H.X.hom]
  (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ H.X)

/-- A geometric full modulus gives the unique translated group factor,
including degree zero. The translation is exactly the original map's value
at the chosen complement point. -/
theorem existsUnique_groupHom_geometricModulus_translation
    (hmod : geometricRegularMapHasModulus c D H q) :
    ∃! φ : groupScheme c D ⟶ H,
      modulusAbelMap c D ε ≫ φ.hom.hom.hom =
        q / (toUnit (Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) ≫ ε ≫ q) := by
  let _ : ModObj H.X H.X := ModObj.regular H.X
  have : IsIso (ModObj.leftSMul H.X H.X) :=
    SchemeTheory.PointedTorsor.isIso_leftSMul_regular H.X
  have ht : geometricTorsorMapHasModulus c D H H.X q := by
    apply (geometricTorsorMapHasModulus_iff_coordinate c D H H.X q η[H.X]).mpr
    simpa only [SchemeTheory.PointedTorsor.coordinate_regular_unit, Category.comp_id] using hmod
  obtain ⟨fg, hfg, _⟩ :=
    existsUnique_picardOneMapFromGeometricModulus_unpointed c D H H.X q ht
  have hp : (ε ≫ abelOneMap c D) ≫ fg.2 = ε ≫ q := by
    rw [Category.assoc, hfg.1]
  have hf := picardOneEquivariantMap_unique c D fg.1
    (ε ≫ abelOneMap c D) (ε ≫ q) fg.2 hp hfg.2
  have hab := abelOneMap_equivariantMap c D ε fg.1 (ε ≫ q)
    (𝟙 (Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)))
  simp only [Category.id_comp, ← hf, hfg.1] at hab
  change q = (modulusAbelMap c D ε ≫ fg.1.hom.hom.hom) *
    (toUnit (Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) ≫ ε ≫ q) at hab
  have hfac : modulusAbelMap c D ε ≫ fg.1.hom.hom.hom =
      q / (toUnit (Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) ≫ ε ≫ q) :=
    eq_div_of_mul_eq' hab.symm
  refine ⟨fg.1, hfac, ?_⟩
  intro φ hφ
  exact modulusAbel_groupHom_ext c D ε H φ fg.1 (hφ.trans hfac.symm)

/-- When the original map sends the basepoint to the identity, its unique
factor has no translation term, over every field and in every degree. -/
theorem existsUnique_groupHom_geometricModulus
    (hmod : geometricRegularMapHasModulus c D H q) (hε : ε ≫ q = 1) :
    ∃! φ : groupScheme c D ⟶ H, modulusAbelMap c D ε ≫ φ.hom.hom.hom = q := by
  simpa only [hε, MonObj.comp_one, div_one] using
    existsUnique_groupHom_geometricModulus_translation c D ε H q hmod

end AlgebraicGeometry.GeneralizedJacobian
