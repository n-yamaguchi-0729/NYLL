/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusFramePicard

/-!
# The actual image of frames in the modulus Picard presheaf

A chosen modulus-rigidified bundle is in the image precisely when its underlying
module is isomorphic to the prescribed pulled family. The proof transports the
chosen trivialization through the actual modulus-scheme comparison.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) {L : (pullback c s).Modules}
  (hL : Scheme.Modules.IsInvertible L)

/-- The comparison hits exactly the classes with the actual prescribed underlying module. -/
theorem exists_modulusFramePicardClass_eq_iff (T : Over S)
    (N : RigidifiedLineBundle (modulusBaseChange c (modulusCurveMap D) (T.hom ≫ s))) :
    (∃ x : (scalarFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T),
        modulusFramePicardClass D s hL T x = RigidifiedLineBundle.classOf N) ↔
      Nonempty (((Scheme.Modules.pullback
        (baseChangeSnd c (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))).obj L) ≅ N.L) := by
  let M := N.pullback (𝟙 (pullback c (T.hom ≫ s)))
    (modulusFamilyDomainIso D (T.hom ≫ s)).hom
    (modulusFamilyDomainIso_square D (T.hom ≫ s))
  have hN : modulusFamilyClassEquiv D (T.hom ≫ s) (RigidifiedLineBundle.classOf M) =
      RigidifiedLineBundle.classOf N :=
    (modulusFamilyClassEquiv D (T.hom ≫ s)).apply_symm_apply (RigidifiedLineBundle.classOf N)
  constructor
  · rintro ⟨x, hx⟩
    have hx' : modulusFrameClass D s hL T x = RigidifiedLineBundle.classOf M :=
      (modulusFamilyClassEquiv D (T.hom ≫ s)).injective (hx.trans hN.symm)
    obtain ⟨a⟩ := (exists_modulusFrameClass_eq_iff D s hL T M).mp ⟨x, hx'⟩
    exact ⟨a ≪≫ (Scheme.Modules.pullbackId (pullback c (T.hom ≫ s))).app N.L⟩
  · rintro ⟨a⟩
    obtain ⟨x, hx⟩ := (exists_modulusFrameClass_eq_iff D s hL T M).mpr
      ⟨a ≪≫ ((Scheme.Modules.pullbackId (pullback c (T.hom ≫ s))).app N.L).symm⟩
    exact ⟨x, (congrArg (modulusFamilyClassEquiv D (T.hom ≫ s)) hx).trans hN⟩

end AlgebraicGeometry.GeneralizedJacobian
