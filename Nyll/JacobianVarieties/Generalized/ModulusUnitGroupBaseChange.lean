/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusUnitBaseChange
import Nyll.JacobianVarieties.Generalized.ModulusUnitGroupRepresentation

/-! # Arbitrary base change of the intrinsic modulus-unit group sheaf

The actual pullback-pasting comparison of units and parameter scalars retains
the commutative group structure when passing to the big-site value universe
and to fppf sheafification.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y S S' : Scheme.{u}} (q : Y ⟶ S) (f : S' ⟶ S)

/-- Pullback of actual modulus units modulo scalars, as lifted commutative groups. -/
def liftedModulusUnitGroupPresheafBaseChangeIso :
    (Over.map f).op ⋙ liftedModulusUnitQuotientGroupPresheaf q ≅
      liftedModulusUnitQuotientGroupPresheaf (pullback.snd q f) :=
  (Functor.associator (Over.map f).op (modulusUnitQuotientPresheaf q)
    CommGrpCat.uliftFunctor.{u + 1, u}).symm ≪≫
      Functor.isoWhiskerRight (modulusUnitPresheafBaseChangeIso q f)
        CommGrpCat.uliftFunctor.{u + 1, u}

/-- The fppf kernel group sheaf commutes with arbitrary base change, with its actual
unit multiplication and scalar quotient. -/
def modulusUnitGroupSheafBaseChangeIso :
    (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} f).obj
      (modulusUnitQuotientGroupSheaf q) ≅
        modulusUnitQuotientGroupSheaf (pullback.snd q f) :=
  ((Functor.pushforwardContinuousSheafificationCompatibility
    (G := Over.map f) (A := CommGrpCat.{u + 1})
    (J := Scheme.fppfTopology.over S') (K := Scheme.fppfTopology.over S)).app
      (liftedModulusUnitQuotientGroupPresheaf q)).symm ≪≫
        (presheafToSheaf (Scheme.fppfTopology.over S') CommGrpCat.{u + 1}).mapIso
          (liftedModulusUnitGroupPresheafBaseChangeIso q f)

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
