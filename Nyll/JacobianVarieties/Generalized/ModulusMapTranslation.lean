/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusFunctoriality
import Nyll.AlgebraicCurves.Models.Charts.OpenPointValues
import Nyll.AlgebraicCurves.Models.FunctionFields.CurveRingEquivFunctionField
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniqueness
import Nyll.JacobianVarieties.Generalized.ModulusMapCondition
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.CommGroupRelativeLaw
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorCoordinates

/-! # Translation of regular maps preserves the full modulus

The principal divisor has degree zero, so translating every value subtracts
zero from its evaluation. Values on the modulus support are irrelevant.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory MonoidalCategory NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GeneralizedJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

/-- Changing the chosen point of the target torsor translates its actual
coordinate map. This identity holds over every field. -/
theorem modulusTorsorCoordinate_changeBasepoint
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K))
    {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (P : Over (Spec (CommRingCat.of K))) [ModObj G.X P]
    [IsIso (ModObj.leftSMul G.X P)]
    (r : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ P)
    (p p' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ P) :
    let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
      Over.homMk _ (Category.comp_id _)
    r ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p' =
      (r ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p) /
        (b ≫ p' ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p) := by
  intro b
  have hrecover :
      (r ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p') • (b ≫ p') = r :=
    SchemeTheory.PointedTorsor.coordinate_smul p' r
  apply eq_div_of_mul_eq'
  simpa only [Category.assoc] using
    (SchemeTheory.PointedTorsor.coordinate_smul_eq p
      (r ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p') (b ≫ p')).symm.trans
        (congrArg (fun f => f ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p) hrecover)

end AlgebraicGeometry.GeneralizedJacobian

namespace GoodReductionJacobian

private theorem pointValue_translate
    {K : Type u} [Field K] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : SchemeHomOver t G.X.hom)
    (z : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) t) :
    let b : Over.mk t ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
      Over.homMk t (Category.comp_id t)
    commGroupPointValue G (𝟙 _)
        (NeronModelInfra.schemeHomOverComp x
          ((commGroupPointEquiv G t).symm (commGroupPointEquiv G t q / (b ≫ z)))) =
      commGroupPointValue G (𝟙 _) (NeronModelInfra.schemeHomOverComp x q) -
        Additive.ofMul z := by
  intro b
  let x' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk t := Over.homMk x.1 x.2
  have hb : x' ≫ b = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact x.2
  simp only [commGroupPointValue, commGroupPointEquiv_comp, Equiv.apply_symm_apply]
  change Additive.ofMul (x' ≫ (commGroupPointEquiv G t q / (b ≫ z))) =
    Additive.ofMul (x' ≫ commGroupPointEquiv G t q) - Additive.ofMul z
  rw [GrpObj.comp_div, ← Category.assoc x' b, hb, Category.id_comp]
  rfl

end GoodReductionJacobian

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
  (G : CommGrp (Over (Spec (CommRingCat.of K))))
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom)

/-- Translation by an actual group point preserves the full modulus condition
of the regular map, including every multiplicity. -/
theorem regularMapHasModulus_translate (hmod : M.regularMapHasModulus D G q)
    (z : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
      Over.homMk _ (Category.comp_id _)
    M.regularMapHasModulus D G
      ((commGroupPointEquiv G
        ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)).symm
          (Over.homMk q.1 q.2 / (b ≫ z))) := by
  intro b
  have hcurve : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have : HasPrincipalDivisors K F := hcurve.toHasPrincipalDivisors
  have ha := Modulus.HasModulus.sub_const hmod (Additive.ofMul z)
  apply Modulus.HasModulus.congr ha
  intro w hw
  obtain ⟨x, rfl⟩ := M.exists_modulusPlace_eq D w hw
  have hx : M.modulusPlace D x =
      M.openPointPlace (modulusComplement (modulusCurveMap D)) ⟨x.left, Over.w x⟩ := rfl
  rw [hx, M.regularMapValues_apply, M.regularMapValues_apply]
  exact (GoodReductionJacobian.pointValue_translate
    ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G q z
    ⟨x.left, Over.w x⟩).symm


/-- Translation preserves and reflects the full modulus, because translating
back by the inverse group point recovers the original regular map. -/
theorem regularMapHasModulus_translate_iff
    (z : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
      Over.homMk _ (Category.comp_id _)
    M.regularMapHasModulus D G q ↔
      M.regularMapHasModulus D G
        ((commGroupPointEquiv G
          ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)).symm
            (Over.homMk q.1 q.2 / (b ≫ z))) := by
  intro b
  refine ⟨fun h => M.regularMapHasModulus_translate D G q h z, ?_⟩
  intro h
  let e := commGroupPointEquiv G
    ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)
  let q' := e.symm (e q / (b ≫ z))
  have hback := M.regularMapHasModulus_translate D G q' h z⁻¹
  have heq : e.symm (e q' / (b ≫ z⁻¹)) = q := by
    rw [show e q' = e q / (b ≫ z) from e.apply_symm_apply _,
      GrpObj.comp_inv, div_inv_eq_mul, div_mul_cancel, Equiv.symm_apply_apply]
  exact heq ▸ hback


/-- The full modulus of a torsor-valued map does not depend on the point used
to identify its target with the acting group. -/
theorem regularMapHasModulus_torsorCoordinate_changeBasepoint
    (P : Over (Spec (CommRingCat.of K))) [ModObj G.X P]
    [IsIso (ModObj.leftSMul G.X P)]
    (r : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶ P)
    (p p' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ P) :
    let q₀ : SchemeHomOver
        ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom :=
      (commGroupPointEquiv G
        ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)).symm
          (r ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p)
    let q₁ : SchemeHomOver
        ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom :=
      (commGroupPointEquiv G
        ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)).symm
          (r ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p')
    M.regularMapHasModulus D G q₀ → M.regularMapHasModulus D G q₁ := by
  intro q₀ q₁ hmod
  change M.regularMapHasModulus D G
    ((commGroupPointEquiv G
      ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)).symm
        (r ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p'))
  rw [modulusTorsorCoordinate_changeBasepoint M.toBase D G P r p p']
  exact M.regularMapHasModulus_translate D G q₀ hmod
    (p' ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p)

end AlgebraicCurve.CurveModel
