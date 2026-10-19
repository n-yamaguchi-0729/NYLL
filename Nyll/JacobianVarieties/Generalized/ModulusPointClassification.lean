/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusClosedFieldPoints
import Nyll.JacobianVarieties.Generalized.PicardZeroLocalSums
import Nyll.JacobianVarieties.Generalized.PicardZeroChartCompatibility

/-! # The same actual point in the type-valued and group-valued classifying maps -/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- Forgetting the represented group point gives the original type-valued classifying map. -/
theorem picardZeroRepresentable_homEquiv_eq
    {T : Over (Spec (CommRingCat.of K))} (p : T ⟶ (groupScheme c D).X) :
    (picardZeroRepresentable c D).homEquiv p =
      (modulusPicardZeroGroupSheafForgetIso c (modulusCurveMap D)).hom.app (op T)
        (pointEquiv c D T p) := by
  cases d with
  | zero => rfl
  | succ n => rfl

/-- Restricting the actual universal class is the original class of the specified point. -/
theorem generalizedJacobianUniversalClass_pullback
    {T : Over (Spec (CommRingCat.of K))} (p : T ⟶ (groupScheme c D).X) :
    (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.map p.op
      (generalizedJacobianUniversalClass c D) = (picardZeroRepresentable c D).homEquiv p := by
  exact ((picardZeroRepresentable c D).homEquiv_comp p (𝟙 _)).symm.trans
    (congrArg (picardZeroRepresentable c D).homEquiv (Category.comp_id p))

/-- Every pulled chart class represents its original point, on every parameter scheme. -/
theorem generalizedJacobianDivisorAtlas_rawClass_classifies
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    (hd : 0 < d)
    (j : (generalizedJacobianDivisorAtlas c D ε hd).cover.I₀)
    {T : Over (Spec (CommRingCat.of K))}
    (z : T ⟶ Over.mk ((generalizedJacobianDivisorAtlas c D ε hd).cover.f j ≫
      (groupScheme c D).X.hom)) :
    (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardZeroGroupPresheaf c (modulusCurveMap D))).app (op T)
        ((modulusPicardZeroPresheaf c (modulusCurveMap D)).map z.op
          ((generalizedJacobianDivisorAtlas c D ε hd).rawClass j)) =
      pointEquiv c D T
        (z ≫ (Over.homMk ((generalizedJacobianDivisorAtlas c D ε hd).cover.f j) :
          Over.mk ((generalizedJacobianDivisorAtlas c D ε hd).cover.f j ≫
            (groupScheme c D).X.hom) ⟶ (groupScheme c D).X)) := by
  let atlas := generalizedJacobianDivisorAtlas c D ε hd
  let raw := (modulusPicardZeroPresheaf c (modulusCurveMap D)).map z.op (atlas.rawClass j)
  apply (ConcreteCategory.bijective_of_isIso
    ((modulusPicardZeroGroupSheafForgetIso c (modulusCurveMap D)).hom.app (op T))).injective
  have hη := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toModulusPicardZeroGroupSheaf_forgetIso c (modulusCurveMap D))
      (op T)) raw
  exact hη.trans ((atlas.rawClass_toSheafify_pullback j z).trans
    ((generalizedJacobianUniversalClass_pullback c D _).trans
      (picardZeroRepresentable_homEquiv_eq c D _)))

variable [IsAlgClosed K]

/-- The actual raw-class point has exactly its original type-valued sheafification class. -/
theorem rigidifiedZeroClassPointEquiv_toSheafify
    (z : modulusPicardZeroSubgroup c (modulusCurveMap D)
      (Over.mk (𝟙 (Spec (CommRingCat.of K))))) :
    (picardZeroRepresentable c D).homEquiv (rigidifiedZeroClassPointEquiv c D z) =
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (modulusPicardZeroPresheaf c (modulusCurveMap D))).app
          (op (Over.mk (𝟙 (Spec (CommRingCat.of K))))) z := by
  rw [picardZeroRepresentable_homEquiv_eq, rigidifiedZeroClassPointEquiv_classifies]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (toModulusPicardZeroGroupSheaf_forgetIso c (modulusCurveMap D))
      (op (Over.mk (𝟙 (Spec (CommRingCat.of K)))))) z

/-- Equality in the original sheaf identifies the very same actual field-valued point. -/
theorem rigidifiedZeroClassPointEquiv_eq_of_toSheafify
    (z : modulusPicardZeroSubgroup c (modulusCurveMap D)
      (Over.mk (𝟙 (Spec (CommRingCat.of K)))))
    (p : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme c D).X)
    (h : (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (modulusPicardZeroPresheaf c (modulusCurveMap D))).app
          (op (Over.mk (𝟙 (Spec (CommRingCat.of K))))) z =
      (picardZeroRepresentable c D).homEquiv p) :
    rigidifiedZeroClassPointEquiv c D z = p :=
  (picardZeroRepresentable c D).homEquiv.injective
    ((rigidifiedZeroClassPointEquiv_toSheafify c D z).trans h)

/-- The raw representative pulled from a chart of the actual universal atlas
classifies the original point lying over that chart. -/
theorem generalizedJacobianDivisorAtlas_rawClass_point
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    (hd : 0 < d)
    (j : (generalizedJacobianDivisorAtlas c D ε hd).cover.I₀)
    (z : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((generalizedJacobianDivisorAtlas c D ε hd).cover.f j ≫
        (groupScheme c D).X.hom)) :
    rigidifiedZeroClassPointEquiv c D
        ((modulusPicardZeroPresheaf c (modulusCurveMap D)).map z.op
          ((generalizedJacobianDivisorAtlas c D ε hd).rawClass j)) =
      z ≫ (Over.homMk ((generalizedJacobianDivisorAtlas c D ε hd).cover.f j) :
        Over.mk ((generalizedJacobianDivisorAtlas c D ε hd).cover.f j ≫
          (groupScheme c D).X.hom) ⟶ (groupScheme c D).X) := by
  apply (pointEquiv c D (Over.mk (𝟙 (Spec (CommRingCat.of K))))).injective
  exact (rigidifiedZeroClassPointEquiv_classifies c D
    ((modulusPicardZeroPresheaf c (modulusCurveMap D)).map z.op
      ((generalizedJacobianDivisorAtlas c D ε hd).rawClass j))).trans
        (generalizedJacobianDivisorAtlas_rawClass_classifies c D ε hd j z)

end AlgebraicGeometry.GeneralizedJacobian
