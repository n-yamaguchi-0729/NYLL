/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusCanonicalPointBundle
import Nyll.JacobianVarieties.Generalized.RigidifiedNormalizedPullback

/-! # The actual Abel rigidification is the canonical normalized point rigidification -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsSeparated c] [SmoothOfRelativeDimension 1 c]

/-- The pulled-back diagonal section remains normalized on the whole modulus. -/
theorem modulusAbelBundleAt_normalized {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t ((modulusComplement i).ι ≫ c)) :
    Scheme.Modules.pullbackSection (modulusBaseChange c i t)
      (Scheme.Modules.pullbackSection (baseChangeSnd c x)
        (modulusAbelDivisor c i).I.invModuleSection) ≫
      (modulusAbelBundleAt c i x).trivialization.hom = 𝟙 _ :=
  RigidifiedLineBundle.pullback_normalized_section (baseChangeSnd c x)
    (baseChangeSnd (i ≫ c) x) (modulusBaseChange_naturality c i x)
    (modulusAbelBundle c i) (modulusAbelDivisor c i).I.invModuleSection
    (modulusAbelBundle_section c i)

omit [IsClosedImmersion i] in
/-- The zero ideal of the pulled-back canonical section is the actual moving point graph. -/
theorem modulusAbelBundleAt_zeroIdeal {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t ((modulusComplement i).ι ≫ c)) :
    Scheme.Modules.zeroSchemeIdeal
      (Scheme.Modules.pullbackSection (baseChangeSnd c x)
        (modulusAbelDivisor c i).I.invModuleSection) =
      (RelEffCartierDiv.ofPoint c (x.1 ≫ (modulusComplement i).ι)
        ((Category.assoc _ _ _).trans x.2)).I := by
  let E := modulusAbelDivisor c i
  let f := baseChangeSnd c x
  have hI : E.I.IsInvertible := RelEffCartierDiv.isInvertible_I E
  have he : E.I.comap f =
      (RelEffCartierDiv.ofPoint c (x.1 ≫ (modulusComplement i).ι)
        ((Category.assoc _ _ _).trans x.2)).I :=
    congrArg RelEffCartierDiv.I
      (RelEffCartierDiv.pullbackAlong_ofPoint c (modulusComplement i).ι rfl x.1 x.2)
  exact (Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal f
    hI.isInvertible_invModule E.I.invModuleSection).symm.trans
      ((congrArg (fun J => J.comap f) hI.zeroSchemeIdeal_invModuleSection).trans he)

end AlgebraicGeometry.GeneralizedJacobian
