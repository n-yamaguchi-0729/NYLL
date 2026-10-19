/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Frames.IsFrameOnPullbackLocalSection
import Nyll.SchemeTheory.Modules.Functoriality.ClosedImmersionUnit
import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Actual transitions between closed pullback quotients

For a triangle of original scheme morphisms, the adjunction unit on
the intermediate scheme and the original composition comparisons
construct the map between the two direct images of pullbacks. This
map commutes with both original units on the ambient scheme.

When the smaller scheme is closed and the source is quasicoherent,
the resulting transition is epimorphic. These are the original
quotient maps needed for a tower of free modules on thickenings.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_pullbackLocalSection

variable {X Y Z : Scheme.{u}} (g : Z ⟶ X) (f : X ⟶ Y) (k : Z ⟶ Y)
  (h : g ≫ f = k) (M : Y.Modules)

/-- The original intermediate unit, followed by the actual direct
image and pullback composition comparisons. -/
def pullbackQuotientTransition :
    (pushforward f).obj ((pullback f).obj M) ⟶
      (pushforward k).obj ((pullback k).obj M) :=
  let A : X.Modules := (pullback f).obj M
  let B : Z.Modules := (pullback g).obj A
  let e : (pushforward (g ≫ f)).obj ((pullback (g ≫ f)).obj M) ≅
      (pushforward k).obj ((pullback k).obj M) :=
    eqToIso (congrArg (fun a : Z ⟶ Y => (pushforward a).obj ((pullback a).obj M)) h)
  (pushforward f).map ((pullbackPushforwardAdjunction g).unit.app A) ≫
    (pushforwardComp g f).hom.app B ≫
    (pushforward (g ≫ f)).map ((pullbackComp g f).hom.app M) ≫ e.hom

/-- The actual transition recovers the original quotient unit on
the smaller scheme from the original unit on the intermediate scheme. -/
theorem unit_pullbackQuotientTransition :
    (pullbackPushforwardAdjunction f).unit.app M ≫
        pullbackQuotientTransition g f k h M =
      (pullbackPushforwardAdjunction k).unit.app M := by
  subst k
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact PicTanH.pullbackComp_hom_app_app_pullbackLocalSection g f M U.unop x

/-- The transition is epimorphic when the final inclusion is closed
and the original ambient module is quasicoherent. -/
theorem epi_pullbackQuotientTransition_of_isClosedImmersion [IsClosedImmersion k]
    [M.IsQuasicoherent] : Epi (pullbackQuotientTransition g f k h M) := by
  have : Epi ((pullbackPushforwardAdjunction k).unit.app M) :=
    epi_pullbackUnit_of_isClosedImmersion k M
  exact epi_of_epi_fac (unit_pullbackQuotientTransition g f k h M)

end AlgebraicGeometry.Scheme.Modules
