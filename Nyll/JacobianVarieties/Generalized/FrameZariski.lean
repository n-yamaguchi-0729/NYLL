/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FrameRepresentability
import Nyll.JacobianVarieties.Generalized.ModulusUnitZariski

/-!
# Actual scalar frames on Zariski covers

The finite frame cover supplies reference frames locally on the parameter
scheme. On each such open, explicit modulus-unit representatives lift every
section of the fppf frame sheaf. The resulting cover of the entire frame
representer consists of opens and therefore preserves smoothness and
reducedness when constructing regular maps by geometric-point comparison.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Module Opposite
open SchemeTheory SchemeTheory.Affine.FiniteScheme

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y S : Scheme.{u}} (q : Y ⟶ S) [IsFinite q]
  {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)

include hM in
/-- Actual finite-family frame coordinates glue the Zariski existence of
raw scalar frames over the whole parameter scheme. -/
theorem scalarFrame_toSheafify_isLocallySurjective_zariski
    [Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S)
      (toSheafify (Scheme.fppfTopology.over S) (liftedModulusUnitQuotientPresheaf q))] :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S)
      (toSheafify (Scheme.fppfTopology.over S) (liftedScalarFramePresheaf q M)) := by
  apply isLocallySurjective_zariski_of_openCover _ (frameCover q hM)
  intro i
  let f := (frameCover q hM).f i
  have := toSheafify_isLocallySurjective_overMap f (liftedModulusUnitQuotientPresheaf q)
  have := toSheafify_isLocallySurjective_of_iso.{u + 1, u, u + 1}
    (Scheme.zariskiTopology.over ((frameCover q hM).X i))
    (Scheme.fppfTopology.over ((frameCover q hM).X i))
    (liftedModulusUnitPresheafBaseChangeIso q f)
  let ec : liftedModulusUnitQuotientPresheaf (pullback.snd q f) ≅
      liftedScalarFramePresheaf (pullback.snd q f)
        (((Scheme.Modules.pullback (pullback.fst q f)).obj M)) :=
    (Functor.isoWhiskerRight
      (scalarFrameCoordinatesIso (pullback.snd q f) (frameCoverPulledFrame q hM i))
      CategoryTheory.uliftFunctor.{u + 1, u}).symm
  have := toSheafify_isLocallySurjective_of_iso.{u + 1, u, u + 1}
    (Scheme.zariskiTopology.over ((frameCover q hM).X i))
    (Scheme.fppfTopology.over ((frameCover q hM).X i)) ec
  exact whisker_toSheafify_isLocallySurjective_of_iso f (liftedScalarFramePresheaf q M)
    (liftedScalarFramePresheafBaseChangeIso q f M)

variable {K : Type u} [Field K] {D : Scheme.{u}}
  (q₀ : D ⟶ Spec (CommRingCat.of K)) [IsFinite q₀]
  {n : ℕ} (b : Basis (Fin (n + 1)) K (coordinateAlgebra q₀))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
  {L : (pullback q₀ t).Modules} (hL : Scheme.Modules.IsInvertible L)

include b hL in
/-- A positive finite field modulus supplies Zariski representatives of
every actual invertible family, with no assumed reference frame. -/
theorem finiteScalarFrame_toSheafify_isLocallySurjective_zariski :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over T)
      (toScalarFrameSheaf (pullback.snd q₀ t) L) := by
  have := modulusUnitBaseChange_toSheafify_isLocallySurjective_zariski q₀ b t
  exact scalarFrame_toSheafify_isLocallySurjective_zariski (pullback.snd q₀ t) hL

include b hL in
/-- Every point of the represented frame sheaf lifts, on an actual affine
open cover, to an actual full-modulus frame of the original family. -/
theorem finiteScalarFrame_exists_affineOpenCover_frames (V : Over T)
    (x : (scalarFrameSheaf (pullback.snd q₀ t) L).obj.obj (op V)) :
    ∃ U : Scheme.AffineOpenCover.{u, u} V.left, ∀ i,
      ∃ e : (relativeFramePresheaf (pullback.snd q₀ t) L).obj
        (op (Over.mk (U.f i ≫ V.hom))),
        (toScalarFrameSheaf (pullback.snd q₀ t) L).app
            (op (Over.mk (U.f i ≫ V.hom))) (ULift.up (Quotient.mk _ e)) =
          (scalarFrameSheaf (pullback.snd q₀ t) L).obj.map
            (Over.homMk (U.f i) : Over.mk (U.f i ≫ V.hom) ⟶ V).op x := by
  have := finiteScalarFrame_toSheafify_isLocallySurjective_zariski q₀ b t hL
  obtain ⟨U, hU⟩ := exists_affineOpenCover_lifts
    (toScalarFrameSheaf (pullback.snd q₀ t) L) V x
  refine ⟨U, fun i => ?_⟩
  obtain ⟨a, ha⟩ := hU i
  obtain ⟨e, he⟩ := Quotient.exists_rep a.down
  refine ⟨e, ?_⟩
  have he' : ULift.up (Quotient.mk _ e) = a := congrArg ULift.up he
  exact (congrArg
    ((toScalarFrameSheaf (pullback.snd q₀ t) L).app (op (Over.mk (U.f i ≫ V.hom))))
    he').trans ha

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
