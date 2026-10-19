/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusUnitRepresentation
import Nyll.JacobianVarieties.Generalized.ModulusUnitBaseChange
import Nyll.SchemeTheory.Affine.AffineFppfComparisonUnit
import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientZariski
import Nyll.SchemeTheory.CategoryTheory.SheafificationLocalLifts

/-!
# Zariski local representatives of the actual modulus-unit sheaf

The explicit projective norm charts lift to actual units. The affine
comparison preserves raw sections, so the intrinsic fppf sheaf has actual
unit classes Zariski locally. This statement survives every base change
and applies to actual scalar frames whenever a reference frame is given.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Module
open SchemeTheory SchemeTheory.Affine SchemeTheory.Affine.FiniteScheme

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {K : Type u} [Field K] {D : Scheme.{u}}
  (q : D ⟶ Spec (CommRingCat.of K)) [IsFinite q]
  {n : ℕ} (b : Basis (Fin (n + 1)) K (coordinateAlgebra q))

include b

/-- The intrinsic modulus-unit sheaf has actual raw unit-class representatives
on Zariski covers, not merely on arbitrary fppf covers. -/
theorem modulusUnit_toSheafify_isLocallySurjective_zariski :
    Presheaf.IsLocallySurjective
      (Scheme.zariskiTopology.over (Spec (CommRingCat.of K)))
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (liftedModulusUnitQuotientPresheaf q)) := by
  have := ScalarQuotientSchemePresheaf.toSheafify_isLocallySurjective_zariski b
  exact toSheafify_isLocallySurjective_zariski_of_affineIso (CommRingCat.of K)
    (affineRestrictionIsoOfSpecRestriction (CommRingCat.of K)
      (scalarQuotientLiftedAffineIso q))

variable {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K))

/-- Actual Zariski representatives persist for the pulled finite modulus. -/
theorem modulusUnitBaseChange_toSheafify_isLocallySurjective_zariski :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S)
      (toSheafify (Scheme.fppfTopology.over S)
        (liftedModulusUnitQuotientPresheaf (pullback.snd q s))) := by
  have := modulusUnit_toSheafify_isLocallySurjective_zariski q b
  have := toSheafify_isLocallySurjective_overMap s (liftedModulusUnitQuotientPresheaf q)
  exact toSheafify_isLocallySurjective_of_iso.{u + 1, u, u + 1} _ _
    (liftedModulusUnitPresheafBaseChangeIso q s)

/-- A genuine reference frame identifies scalar classes with unit classes,
so every sheaf section has an actual scalar frame Zariski locally. -/
theorem scalarFrameBaseChange_toSheafify_isLocallySurjective_zariski
    {M : (pullback q s).Modules} (e : M ≅ 𝟙_ (pullback q s).Modules) :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S)
      (toSheafify (Scheme.fppfTopology.over S)
        (liftedScalarFramePresheaf (pullback.snd q s) M)) := by
  have := modulusUnitBaseChange_toSheafify_isLocallySurjective_zariski q b s
  let ec : liftedModulusUnitQuotientPresheaf (pullback.snd q s) ≅
      liftedScalarFramePresheaf (pullback.snd q s) M :=
    (Functor.isoWhiskerRight (scalarFrameCoordinatesIso (pullback.snd q s) e)
      CategoryTheory.uliftFunctor.{u + 1, u}).symm
  exact toSheafify_isLocallySurjective_of_iso.{u + 1, u, u + 1} _ _ ec

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
