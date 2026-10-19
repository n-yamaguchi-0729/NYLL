/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelFamily
import Nyll.AlgebraicCurves.RelativeDivisors.BaseChange.PullbackOfPoint
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealPullbackInvModuleIso

/-! # The Abel family classifies the line bundle of the actual moving point -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsSeparated c] [SmoothOfRelativeDimension 1 c]

/-- On every test scheme, the Abel family is the inverse ideal of that test point's graph. -/
def modulusAbelBundlePullbackIso {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t ((modulusComplement i).ι ≫ c)) :
    (Scheme.Modules.pullback (RelPicard.baseChangeSnd c x)).obj (modulusAbelBundle c i).L ≅
      (RelEffCartierDiv.ofPoint c (x.1 ≫ (modulusComplement i).ι)
        ((Category.assoc _ _ _).trans x.2)).I.invModule := by
  let E := modulusAbelDivisor c i
  let f := mapOnProdOver c x.1 x.2
  have hI : E.I.IsInvertible := RelEffCartierDiv.isInvertible_I E
  have hI' : (E.I.comap f).IsInvertible :=
    RelEffCartierDiv.isInvertible_I (E.pullbackAlong x.1 x.2)
  have he : (E.I.comap f) =
      (RelEffCartierDiv.ofPoint c (x.1 ≫ (modulusComplement i).ι)
        ((Category.assoc _ _ _).trans x.2)).I :=
    congrArg RelEffCartierDiv.I
      (RelEffCartierDiv.pullbackAlong_ofPoint c (modulusComplement i).ι rfl x.1 x.2)
  exact (Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso f hI hI').some ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.invModule he)

end AlgebraicGeometry.GeneralizedJacobian
