/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.KernelGroup
import Nyll.JacobianVarieties.Generalized.ModulusForgetfulSurjectivity

/-! # The generalized-Jacobian exact sequence over the original field

The scalar boundary identifies the concrete norm-open group with the actual
scheme-theoretic kernel. Forgetting rigidification is locally surjective for
the fppf topology, without a rational point on the curve.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open SchemeTheory.Affine
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c] in
/-- The concrete norm-open boundary is annihilated by actual forgetting. -/
theorem modulusNormBoundarySheaf_condition :
    modulusNormBoundarySheaf D ≫ forgetModulusZeroGroupSheaf c (modulusCurveMap D) =
      modulusNormBoundarySheaf D ≫ modulusForgetfulIdentitySheaf c (modulusCurveMap D) := by
  unfold modulusNormBoundarySheaf
  rw [Category.assoc, modulusUnitBoundarySheaf_condition, ← Category.assoc]

/-- The concrete norm-open group has the actual kernel universal property in fppf group sheaves. -/
def modulusNormBoundarySheafIsKernel :
    IsLimit (Fork.ofι (modulusNormBoundarySheaf D)
      (modulusNormBoundarySheaf_condition D)) :=
  IsLimit.ofIsoLimit (modulusUnitBoundarySheafIsKernel c (modulusCurveMap D))
    (Fork.ext (modulusAlgebraUnitGroupSheafIso D).symm
      ((modulusAlgebraUnitGroupSheafIso D).inv_comp_eq.mpr rfl))

/-- The actual fppf group sheaves form a short exact sequence over an arbitrary field. -/
theorem groupSheaf_exact :
    Mono (modulusNormBoundarySheaf D) ∧
      (∀ T : Over (Spec (CommRingCat.of K)),
        Set.range ((modulusNormBoundarySheaf D).hom.app (op T)).hom =
          {x | ((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app (op T)).hom x =
            1}) ∧
      Sheaf.IsLocallySurjective (forgetModulusZeroGroupSheaf c (modulusCurveMap D)) :=
  ⟨inferInstance, modulusNormBoundarySheaf_range D,
    forgetModulusZeroGroupSheaf_locallySurjective D⟩

variable [GeometricallyIntegral c] (hd : 0 < d)

omit [GeometricallyIrreducible c] in
/-- Exactness on points of the actual group schemes, for every parameter scheme. -/
theorem modulusNormBoundary_range (T : Over (Spec (CommRingCat.of K))) :
    Set.range (fun f : T ⟶ (modulusUnitQuotient D hd).X =>
      f ≫ (modulusNormBoundary c D hd).hom.hom.hom) =
        {x | x ≫ (groupProjection c D).hom.hom.hom =
          (1 : T ⟶ (ordinaryGroupScheme c).X)} := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    change (f ≫ (modulusNormBoundary c D hd).hom.hom.hom) ≫
      (groupProjection c D).hom.hom.hom = 1
    rw [Category.assoc, modulusNormBoundary_condition, MonObj.comp_one]
  · intro hx
    have hz : ((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app (op T)).hom
        ((groupRepresentable c D).homEquiv x) = 1 := by
      exact (groupProjection_homEquiv c D x).symm.trans
        ((congrArg (ordinaryGroupRepresentable c).homEquiv hx).trans
          (SchemeTheory.RepresentedGroups.homEquiv_one _
            (ordinaryGroupRepresentable c) T))
    obtain ⟨a, ha⟩ := (Set.ext_iff.mp (modulusNormBoundarySheaf_range D T)
      ((groupRepresentable c D).homEquiv x)).mpr hz
    refine ⟨(modulusUnitQuotientRepresentable D hd).homEquiv.symm a, ?_⟩
    apply (groupRepresentable c D).homEquiv.injective
    exact (modulusNormBoundary_homEquiv c D hd _).trans
      ((congrArg ((modulusNormBoundarySheaf D).hom.app (op T)).hom
        ((modulusUnitQuotientRepresentable D hd).homEquiv.apply_symm_apply a)).trans ha)

end AlgebraicGeometry.GeneralizedJacobian
