/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelPointNormalization
import Nyll.JacobianVarieties.Generalized.ModulusAbelZeroClass

/-! # The actual Abel rigidification is the canonical normalized point rigidification -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [SmoothOfRelativeDimension 1 c]

section

variable [IsSeparated c]

/-- Pulling back the diagonal family preserves the actual canonical point rigidification. -/
def modulusAbelBundleAtCanonicalIso {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t ((modulusComplement i).ι ≫ c)) :
    RigidifiedLineBundle.Iso (modulusAbelBundleAt c i x)
      (modulusCanonicalPointBundle c i x) := by
  let M : RigidifiedLineBundle (modulusBaseChange c i t) := modulusAbelBundleAt c i x
  let E : RelEffCartierDiv c 1 t := RelEffCartierDiv.ofPoint c
    (x.1 ≫ (modulusComplement i).ι) ((Category.assoc _ _ _).trans x.2)
  let s : 𝟙_ (pullback c t).Modules ⟶ M.L :=
    Scheme.Modules.pullbackSection (baseChangeSnd c x)
      (modulusAbelDivisor c i).I.invModuleSection
  have hs : Scheme.Modules.pullbackSection (modulusBaseChange c i t) s ≫
      M.trivialization.hom = 𝟙 _ := modulusAbelBundleAt_normalized c i x
  have hz : Scheme.Modules.zeroSchemeIdeal s = E.I := modulusAbelBundleAt_zeroIdeal c i x
  exact RigidifiedLineBundle.zeroDivisorIso M s hs E.I
    (RelEffCartierDiv.isInvertible_I E) hz (modulusPointDivisor_avoids c i x)

end

/-- The point class defined by the diagonal family equals the class of the
actual canonically normalized point bundle, including its full modulus frame. -/
theorem modulusAbelPointClass_eq_canonical [IsProper c] [GeometricallyIntegral c]
    {T : Over (Spec (CommRingCat.of R))}
    (x : T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    modulusAbelPointClass c i x =
      RigidifiedLineBundle.classOf (modulusCanonicalPointBundle c i
        ⟨x.left, Over.w x⟩) :=
  (RigidifiedLineBundle.classOf_eq_iff _ _).mpr
    ⟨modulusAbelBundleAtCanonicalIso c i ⟨x.left, Over.w x⟩⟩

end AlgebraicGeometry.GeneralizedJacobian
