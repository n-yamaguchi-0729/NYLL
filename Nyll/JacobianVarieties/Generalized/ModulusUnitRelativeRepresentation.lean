/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusUnitRepresentation
import Nyll.JacobianVarieties.Generalized.ModulusUnitBaseChange
import Nyll.SchemeTheory.WeilRestriction.Restriction

/-!
# Relative representations of the modulus unit and local frame sheaves

The intrinsic unit-sheaf representation survives arbitrary base change.
For a finite positive-rank modulus over a field, every base-changed unit
sheaf is represented by the corresponding pullback of the concrete norm
open. A genuine trivialization of a module on that base-changed modulus
then supplies its local scalar-frame representation.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Module
open SchemeTheory.Affine SchemeTheory.Affine.FiniteScheme
open SchemeTheory.WeilRestriction

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y S S' : Scheme.{u}} (q : Y ⟶ S) (f : S' ⟶ S)

/-- An existing unit-sheaf representation pulls back to the actual base-changed modulus. -/
def modulusUnitRepresentableBaseChange {W : Over S}
    (h : (modulusUnitQuotientSheaf q).obj.RepresentableBy W) :
    (modulusUnitQuotientSheaf (pullback.snd q f)).obj.RepresentableBy
      ((Over.pullback f).obj W) :=
  (representableByBaseChange f h).ofIso
    ((sheafToPresheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
      (modulusUnitSheafBaseChangeIso q f))

/-- A chosen frame yields an actual local representation after any base change. -/
def scalarFrameRepresentableBaseChange {W : Over S}
    (h : (modulusUnitQuotientSheaf q).obj.RepresentableBy W)
    {M : (pullback q f).Modules} (e : M ≅ 𝟙_ (pullback q f).Modules) :
    (scalarFrameSheaf (pullback.snd q f) M).obj.RepresentableBy ((Over.pullback f).obj W) :=
  (modulusUnitRepresentableBaseChange q f h).ofIso
    ((sheafToPresheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
      (scalarFrameSheafCoordinatesIso (pullback.snd q f) e).symm)

variable {K : Type u} [Field K] {Y : Scheme.{u}}
  (q : Y ⟶ Spec (CommRingCat.of K)) [IsFinite q]
  {n : ℕ} (b : Basis (Fin (n + 1)) K (coordinateAlgebra q))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))

/-- The relative modulus-unit representer is the actual base change of the norm open. -/
def finiteModulusUnitRelativeRepresentable :
    (modulusUnitQuotientSheaf (pullback.snd q t)).obj.RepresentableBy
      ((Over.pullback t).obj (ScalarQuotientSchemePresheaf.representingObject b)) :=
  modulusUnitRepresentableBaseChange q t (modulusUnitSheafRepresentable q b)

/-- The supplied reference frame represents its scalar-frame sheaf by the same relative scheme. -/
def finiteScalarFrameRelativeRepresentable {M : (pullback q t).Modules}
    (e : M ≅ 𝟙_ (pullback q t).Modules) :
    (scalarFrameSheaf (pullback.snd q t) M).obj.RepresentableBy
      ((Over.pullback t).obj (ScalarQuotientSchemePresheaf.representingObject b)) :=
  scalarFrameRepresentableBaseChange q t (modulusUnitSheafRepresentable q b) e

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
