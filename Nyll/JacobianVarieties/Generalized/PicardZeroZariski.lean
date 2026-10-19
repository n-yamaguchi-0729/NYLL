/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FrameZariski
import Nyll.JacobianVarieties.Generalized.PointedConstruction

/-!
# Actual rigidified bundles on affine open covers of modulus Picard-zero

The explicit norm charts strengthen the Poincare frame comparison to
Zariski local surjectivity. Consequently every section of the actual
modulus Picard-zero sheaf is represented by specified rigidified bundles
on an affine open cover. In particular this applies to its universal
section on the constructed smooth generalized Jacobian.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra
open SchemeTheory SchemeTheory.WeilRestriction AlgebraicGeometry.RelPicard
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d)

include ε hd in
/-- The actual Picard-zero sheafification has raw chosen-rigidified
representatives Zariski locally, as supplied by the Poincare norm charts. -/
theorem modulusPicardZero_toSheafify_isLocallySurjective_zariski :
    Presheaf.IsLocallySurjective
      (Scheme.zariskiTopology.over (Spec (CommRingCat.of K)))
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (modulusPicardZeroPresheaf c (modulusCurveMap D))) := by
  let J := Pointed.ordinaryPicard c ε
  let h := Pointed.ordinaryRepresentation c ε
  have : IsFinite (modulusBaseMap D) := D.isFinite
  have : Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over J.P)
      (toScalarFrameSheaf (pullback.snd (modulusBaseMap D) J.toBase)
        (poincareModulusBundle D h)) :=
    finiteScalarFrame_toSheafify_isLocallySurjective_zariski
      (modulusBaseMap D) (positiveModulusBasis D hd) J.toBase
      (poincareModulusBundle_isInvertible D h)
  have : Presheaf.IsLocallySurjective
      (Scheme.zariskiTopology.over (Spec (CommRingCat.of K)))
      (poincareRawToFrameFamily D h) :=
    relativeTotalMap_isLocallySurjective.{u, u + 1} Scheme.zariskiTopology J.toBase _
  have : IsIso (poincareFrameTotalToModulusPicardZero D h) := by
    rw [← poincareFramePicardZeroIso_hom D h hd]
    infer_instance
  have hc : Presheaf.IsLocallySurjective
      (Scheme.zariskiTopology.over (Spec (CommRingCat.of K)))
      (poincareRawToFrameFamily D h ≫ poincareFrameTotalToModulusPicardZero D h) :=
    inferInstance
  rw [poincareRawToFrameFamily_comp_toModulusPicardZero D h] at hc
  have : Presheaf.IsLocallySurjective
      (Scheme.zariskiTopology.over (Spec (CommRingCat.of K)))
      (poincareRawFrameToModulusZero D h ≫
        toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
          (modulusPicardZeroPresheaf c (modulusCurveMap D))) := hc
  exact Presheaf.isLocallySurjective_of_isLocallySurjective
    (Scheme.zariskiTopology.over (Spec (CommRingCat.of K)))
    (poincareRawFrameToModulusZero D h)
    (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardZeroPresheaf c (modulusCurveMap D)))

include ε hd in
/-- Every actual zero-sheaf section admits an affine open cover with
specified rigidified bundles representing its restrictions. -/
theorem modulusPicardZero_exists_affineOpenCover_bundles
    (T : Over (Spec (CommRingCat.of K)))
    (x : (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.obj (op T)) :
    ∃ U : Scheme.AffineOpenCover.{u, u} T.left, ∀ j,
      ∃ (M : RigidifiedLineBundle
          (modulusBaseChange c (modulusCurveMap D) (U.f j ≫ T.hom)))
        (hM : RigidifiedLineBundle.classOf M ∈
          (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj
            (op (Over.mk (U.f j ≫ T.hom)))),
        (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
          (modulusPicardZeroPresheaf c (modulusCurveMap D))).app
            (op (Over.mk (U.f j ≫ T.hom))) ⟨RigidifiedLineBundle.classOf M, hM⟩ =
          (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.map
            (Over.homMk (U.f j) : Over.mk (U.f j ≫ T.hom) ⟶ T).op x := by
  have := modulusPicardZero_toSheafify_isLocallySurjective_zariski c ε D hd
  obtain ⟨U, hU⟩ := exists_affineOpenCover_lifts
    (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardZeroPresheaf c (modulusCurveMap D))) T x
  refine ⟨U, fun j => ?_⟩
  obtain ⟨⟨a, ha⟩, hx⟩ := hU j
  obtain ⟨M, rfl⟩ := Quotient.exists_rep a
  exact ⟨M, ha, hx⟩

end AlgebraicGeometry.GeneralizedJacobian
