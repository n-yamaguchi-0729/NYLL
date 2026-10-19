/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FrameCover
import Nyll.JacobianVarieties.Generalized.ModulusFramesZero
import Nyll.JacobianVarieties.Generalized.PicardZeroForgetfulGroup
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Local surjectivity of modulus forgetting without a rational basepoint

The restriction of an actual line bundle to the finite modulus is trivial over
an open cover of its parameter scheme. Those frames give actual modulus classes
lifting the ordinary relative class. No global rigidification is required.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- Every ordinary zero class has genuine modulus rigidifications on a parameter open cover. -/
theorem forgetModulusZeroGroupPresheaf_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (forgetModulusZeroGroupPresheaf c (modulusCurveMap D)) := by
  have : IsFinite (modulusBaseMap D) := D.isFinite
  constructor
  intro T x
  rcases x with ⟨x, hx⟩
  induction x using Quot.ind with
  | _ L =>
    let q := pullback.snd (modulusBaseMap D) T.hom
    let hM := L.property.pullback (modulusFamilyInclusion D T.hom)
    let V := frameCover q hM
    let U (j : V.I₀) : Over (Spec (CommRingCat.of K)) := Over.mk (V.f j ≫ T.hom)
    let f (j : V.I₀) : U j ⟶ T := Over.homMk (V.f j) rfl
    have hcover : Sieve.ofArrows U f ∈
        (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) T := by
      rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      apply Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage
      exact V.mem_grothendieckTopology
    apply (Scheme.fppfTopology.over (Spec (CommRingCat.of K))).superset_covering ?_ hcover
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro j
    let s : SchemeHomOver (U j).hom T.hom := ⟨V.f j, rfl⟩
    let N : RigidifiedLineBundle (modulusFamilyInclusion D (U j).hom) :=
      RigidifiedLineBundle.withFrame (modulusFamilyInclusion D (U j).hom)
        (L.property.pullback (baseChangeSnd c s))
        (modulusFrameTestEquiv D T.hom L.val (Over.mk (V.f j)) (frameCoverFrame q hM j))
    let y := modulusFamilyClassEquiv D (U j).hom (RigidifiedLineBundle.classOf N)
    have hy : y ∈ modulusPicardZeroSubgroup c (modulusCurveMap D) (U j) :=
      modulusFamilyClassEquiv_mem_zero D (U j).hom N
        (Unrigidified.fibrewiseZero_pullback s hx)
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    exact Quot.sound (Unrigidified.baseTwist_of_iso
      ((Scheme.Modules.pullbackId (pullback c (U j).hom)).app N.L))

/-- The actual forgetful map of fppf group sheaves is locally surjective over every field. -/
theorem forgetModulusZeroGroupSheaf_locallySurjective :
    Sheaf.IsLocallySurjective (forgetModulusZeroGroupSheaf c (modulusCurveMap D)) :=
  (Presheaf.isLocallySurjective_presheafToSheaf_map_iff
    (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    (forgetModulusZeroGroupPresheaf c (modulusCurveMap D))).mpr
      (forgetModulusZeroGroupPresheaf_isLocallySurjective D)

/-- In particular, forgetting the modulus is an epimorphism of actual fppf group sheaves. -/
theorem forgetModulusZeroGroupSheaf_epimorphism :
    Epi (forgetModulusZeroGroupSheaf c (modulusCurveMap D)) := by
  have : Sheaf.IsLocallySurjective (forgetModulusZeroGroupSheaf c (modulusCurveMap D)) :=
    forgetModulusZeroGroupSheaf_locallySurjective D
  infer_instance

end AlgebraicGeometry.GeneralizedJacobian
