/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedNormalizedPullback

/-! # Canonical rigidifications under an identified ideal pullback -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

/-- Identifying the whole pulled-back ideal also identifies its canonical normalized frame. -/
def ofInvertibleIdealPullbackIsoOfEq
    {X X' D D' : Scheme.{u}} {i : D ⟶ X} {i' : D' ⟶ X'}
    (f : X' ⟶ X) (g : D' ⟶ D) (w : i' ≫ f = g ≫ i)
    (I : X.IdealSheafData) (hI : I.IsInvertible)
    (havoid : ∀ y : D, i.base y ∉ I.support)
    (J : X'.IdealSheafData) (hJ : J.IsInvertible)
    (havoid' : ∀ y : D', i'.base y ∉ J.support)
    (hIJ : I.comap f = J) :
    Iso ((ofInvertibleIdeal i I hI havoid).pullback f g w)
      (ofInvertibleIdeal i' J hJ havoid') :=
  zeroDivisorIso ((ofInvertibleIdeal i I hI havoid).pullback f g w)
    (pullbackSection f I.invModuleSection)
    (pullback_normalized_section f g w (ofInvertibleIdeal i I hI havoid)
      I.invModuleSection (ofInvertibleIdeal_section i I hI havoid))
    J hJ ((IsInvertible.comap_zeroSchemeIdeal f hI.isInvertible_invModule
      I.invModuleSection).symm.trans
        ((congrArg (fun Q => Q.comap f) hI.zeroSchemeIdeal_invModuleSection).trans hIJ))
    havoid'

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
