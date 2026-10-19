/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareRawFamily
import Nyll.SchemeTheory.WeilRestriction.RelativeTotalLocalBijection

/-!
# Actual local representatives for the total frame family

Relative frame sheafification is a local bijection on the actual parameter
scheme. Passing to the total family preserves this property over the original
field. Thus the represented family is locally described by actual scalar frames.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open SchemeTheory.WeilRestriction AlgebraicGeometry.RelPicard
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)

/-- Every total frame-family section is fppf locally represented by actual scalar frames. -/
instance poincareRawToFrameFamily_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (poincareRawToFrameFamily D h) := by
  have : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over J.P)
      (toScalarFrameSheaf (pullback.snd (modulusBaseMap D) J.toBase)
        (poincareModulusBundle D h)) :=
    inferInstanceAs (Presheaf.IsLocallySurjective (Scheme.fppfTopology.over J.P)
      (toSheafify (Scheme.fppfTopology.over J.P)
        (liftedScalarFramePresheaf (pullback.snd (modulusBaseMap D) J.toBase)
          (poincareModulusBundle D h))))
  exact relativeTotalMap_isLocallySurjective.{u, u + 1} Scheme.fppfTopology J.toBase _

/-- Equality in the total frame family is witnessed fppf locally on actual raw frames. -/
instance poincareRawToFrameFamily_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (poincareRawToFrameFamily D h) := by
  have : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over J.P)
      (toScalarFrameSheaf (pullback.snd (modulusBaseMap D) J.toBase)
        (poincareModulusBundle D h)) :=
    inferInstanceAs (Presheaf.IsLocallyInjective (Scheme.fppfTopology.over J.P)
      (toSheafify (Scheme.fppfTopology.over J.P)
        (liftedScalarFramePresheaf (pullback.snd (modulusBaseMap D) J.toBase)
          (poincareModulusBundle D h))))
  exact relativeTotalMap_isLocallyInjective.{u, u + 1} Scheme.fppfTopology J.toBase _

end AlgebraicGeometry.GeneralizedJacobian
