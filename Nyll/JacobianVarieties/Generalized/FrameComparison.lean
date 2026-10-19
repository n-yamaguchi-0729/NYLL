/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FrameRepresentability
import Nyll.SchemeTheory.WeilRestriction.Restriction

/-!
# Comparisons of the actual glued frame scheme

The representing properties fix the comparison with the scheme constructed
after arbitrary base change. An actual global frame identifies the glued
scheme with the modulus-unit scheme. These isomorphisms retain the structure
map to the parameter scheme and do not assume a globally trivial family.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SchemeTheory.WeilRestriction

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y S S' : Scheme.{u}} (q : Y ⟶ S) [IsFinite q]
  {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
  {W : Over S} (h : (modulusUnitQuotientSheaf q).obj.RepresentableBy W)

/-- The actual glued frame scheme commutes with arbitrary change of parameters. -/
def scalarFrameRepresenterBaseChangeIso (f : S' ⟶ S) :
    (Over.pullback f).obj (scalarFrameRepresenter q hM h) ≅
      scalarFrameRepresenter (pullback.snd q f) (hM.pullback (pullback.fst q f))
        (modulusUnitRepresentableBaseChange q f h) :=
  ((representableByBaseChange f (scalarFrameRepresentable q hM h)).ofIso
    ((sheafToPresheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
      (scalarFrameSheafBaseChangeIso q f M))).uniqueUpToIso
        (scalarFrameRepresentable (pullback.snd q f) (hM.pullback (pullback.fst q f))
          (modulusUnitRepresentableBaseChange q f h))

/-- A genuine frame trivializes the same glued scheme over its base. -/
def scalarFrameRepresenterFrameIso (e : M ≅ 𝟙_ Y.Modules) :
    scalarFrameRepresenter q hM h ≅ W :=
  (scalarFrameRepresentable q hM h).uniqueUpToIso
    (h.ofIso ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type (u + 1))).mapIso
      (scalarFrameSheafCoordinatesIso q e).symm))

/-- A frame after base change identifies the actual pulled scheme with its unit model. -/
def scalarFrameRepresenterPullbackFrameIso (f : S' ⟶ S)
    (e : (Scheme.Modules.pullback (pullback.fst q f)).obj M ≅
      𝟙_ (pullback q f).Modules) :
    (Over.pullback f).obj (scalarFrameRepresenter q hM h) ≅ (Over.pullback f).obj W :=
  scalarFrameRepresenterBaseChangeIso q hM h f ≪≫
    scalarFrameRepresenterFrameIso (pullback.snd q f) (hM.pullback (pullback.fst q f))
      (modulusUnitRepresentableBaseChange q f h) e

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
