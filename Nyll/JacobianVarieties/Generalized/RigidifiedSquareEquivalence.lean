/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardGroupFunctor
import Nyll.JacobianVarieties.Generalized.RigidifiedCongr

/-! # Transport of chosen rigidifications across an isomorphism of squares -/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X X' D D' : Scheme.{u}} {i : D ⟶ X} {i' : D' ⟶ X'}
  (e : X' ≅ X) (a : D' ≅ D) (w : i' ≫ e.hom = a.hom ≫ i)

/-- Actual pullback across a square of scheme isomorphisms is a group equivalence
on compatible-isomorphism classes with their specified trivializations. -/
def classesPullbackMulEquiv : Classes i ≃* Classes i' where
  toEquiv := classesPullbackEquiv e a w
  map_mul' := classesPullback_tensor e.hom a.hom w

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
