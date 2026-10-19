/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardZeroZariski
import Nyll.JacobianVarieties.Generalized.PicardZeroFamilyDivisorClasses
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Actual supported divisors on affine charts of the modulus Picard-zero sheaf

The Zariski representatives and the normalized family construction provide
actual divisors on each affine open. Both the original sheaf section and
the equality preserving the full modulus frame are retained.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d)
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
    ((modulusComplement (modulusCurveMap D)).ι ≫ c))

include hd in
/-- Every actual noetherian zero-sheaf family has supported effective divisor
representatives after a specified basepoint twist on an actual affine open cover. -/
theorem modulusPicardZero_exists_affineOpenCover_divisors
    (T : Over (Spec (CommRingCat.of K))) [IsLocallyNoetherian T.left]
    (x : (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.obj (op T)) :
    ∃ U : Scheme.AffineOpenCover.{u, u} T.left, ∀ j,
      ∃ (n : ℕ)
        (M : RigidifiedLineBundle
          (modulusBaseChange c (modulusCurveMap D) (U.f j ≫ T.hom)))
        (hM : RigidifiedLineBundle.classOf M ∈
          (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj
            (op (Over.mk (U.f j ≫ T.hom))))
        (E : RelEffCartierDiv c n (U.f j ≫ T.hom))
        (hE : E.SupportedIn (modulusComplement (modulusCurveMap D))),
        RigidifiedLineBundle.classOf M *
            RigidifiedLineBundle.classOf (modulusCanonicalPointBundle c (modulusCurveMap D)
              (GoodReductionJacobian.schemeHomOverComp (U.f j ≫ T.hom)
                (Category.comp_id _) ε)) ^ n =
          modulusDivisorFamilyClass c (modulusCurveMap D) E hE ∧
        (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
          (modulusPicardZeroPresheaf c (modulusCurveMap D))).app
            (op (Over.mk (U.f j ≫ T.hom))) ⟨RigidifiedLineBundle.classOf M, hM⟩ =
          (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.map
            (Over.homMk (U.f j) : Over.mk (U.f j ≫ T.hom) ⟶ T).op x := by
  let εC : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c :=
    ⟨ε.1 ≫ (modulusComplement (modulusCurveMap D)).ι,
      (Category.assoc _ _ _).trans ε.2⟩
  obtain ⟨U, hU⟩ := modulusPicardZero_exists_affineOpenCover_bundles c εC D hd T x
  refine ⟨U, ?_⟩
  intro j
  obtain ⟨M, hM, hx⟩ := hU j
  have : IsLocallyNoetherian (Spec (U.X j)) :=
    isLocallyNoetherian_of_isOpenImmersion (U.f j)
  have : IsNoetherianRing (U.X j) := isLocallyNoetherian_Spec.mp inferInstance
  obtain ⟨n, hn⟩ := picardZeroFamily_eventually_divisor_class c D hd ε
    (U.X j) (U.f j ≫ T.hom) M hM
  obtain ⟨E, hE, he⟩ := hn n (le_refl n)
  exact ⟨n, M, hM, E, hE, he, hx⟩

end AlgebraicGeometry.GeneralizedJacobian
