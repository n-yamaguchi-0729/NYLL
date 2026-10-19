/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.UnrigidifiedLocalRigidification
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Representation

/-!
# Local Poincaré classification of an actual unrigidified family

An algebraically trivial family is locally isomorphic to the actual Poincaré
pullback on its section-restriction trivializing cover. The cover is constructed
from the given line bundle, without assuming a global pointed rigidification.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C T : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {t : T ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {J : RelativePic0Designation R c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)
  (M : Unrigidified.LineBundle c t) (hM : Unrigidified.FibrewiseZero M)

/-- The actual local pointed family has its ordinary Poincaré classifying map. -/
def localPoincareMap (j : (Unrigidified.localRigidificationCover ε M).val.I₀) :
    SchemeHomOver ((Unrigidified.localRigidificationCover ε M).val.f j ≫ t) J.toBase :=
  h.classify _ (Unrigidified.localPointedBundle ε M j)
    (Unrigidified.localPointedBundle_mem_zero ε M hM j)

/-- The actual Poincaré pullback is isomorphic to the original family's local restriction. -/
def localPoincareIso (j : (Unrigidified.localRigidificationCover ε M).val.I₀) :
    (h.poincare.pullbackAlong (localPoincareMap h M hM j)).L ≅
      (Scheme.Modules.pullback
        (baseChangeSnd c (⟨(Unrigidified.localRigidificationCover ε M).val.f j, rfl⟩ :
          SchemeHomOver ((Unrigidified.localRigidificationCover ε M).val.f j ≫ t) t))).obj M.1 :=
  (h.classify_spec _ (Unrigidified.localPointedBundle ε M j)
    (Unrigidified.localPointedBundle_mem_zero ε M hM j)).some

end AlgebraicGeometry.GeneralizedJacobian
