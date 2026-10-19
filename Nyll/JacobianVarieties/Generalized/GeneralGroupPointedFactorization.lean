/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeneralGeometricModulusExistence
import Nyll.JacobianVarieties.Generalized.GeometricModulusPointedUniversalProperty

/-! # A pointed Abel factor for an actual open-curve group map

A rational point sent to the identity supplies a pointed Abel factor after
constructing a full geometric modulus over the original field. The returned
modulus has exactly the original open domain as its complement, and its
factor is unique as a group-scheme morphism.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

/-- A pointed regular map constructs its own ground-field modulus and its
unique pointed Abel factor, without a preassigned divisor or modulus condition.
The rational point itself supplies nonemptiness of the original domain. -/
theorem exists_modulus_unique_pointedGroupFactor
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (U : C.Opens)
    (ε : Over.mk (𝟙 (Spec (.of K))) ⟶ Over.mk (U.ι ≫ c))
    (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (q : Over.mk (U.ι ≫ c) ⟶ G.X) (hε : ε ≫ q = 1) :
    ∃ (d : ℕ) (D : RelEffCartierDiv c d (𝟙 (Spec (.of K))))
      (hDU : modulusComplement (modulusCurveMap D) = U),
      let j : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
          Over.mk (U.ι ≫ c) :=
        Over.homMk (V := Over.mk (U.ι ≫ c)) (C.homOfLE hDU.le)
          (by simp only [Over.mk_hom, ← Category.assoc, Scheme.homOfLE_ι])
      let jback : Over.mk (U.ι ≫ c) ⟶
          Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) :=
        Over.homMk
          (V := Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
          (C.homOfLE hDU.ge)
          (by simp only [Over.mk_hom, ← Category.assoc, Scheme.homOfLE_ι])
      let εD := ε ≫ jback
      let qD := j ≫ q
      geometricRegularMapHasModulus c D G qD ∧
        ∃! φ : groupScheme c D ⟶ G,
          modulusAbelMap c D εD ≫ φ.hom.hom.hom = qD := by
  have hU : (U : Set C).Nonempty :=
    ⟨(ε.left (IsLocalRing.closedPoint K)).1, (ε.left (IsLocalRing.closedPoint K)).2⟩
  obtain ⟨d, D, hDU, hmod⟩ := exists_group_geometricRegularMapHasModulus c U hU G q
  refine ⟨d, D, hDU, ?_⟩
  intro j jback εD qD
  refine ⟨hmod, ?_⟩
  have hj : jback ≫ j = 𝟙 (Over.mk (U.ι ≫ c)) := by
    apply Over.OverMorphism.ext
    apply (cancel_mono U.ι).mp
    change (C.homOfLE hDU.ge ≫ C.homOfLE hDU.le) ≫ U.ι = (𝟙 U.toScheme) ≫ U.ι
    rw [Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι, Category.id_comp]
  have hback : jback ≫ qD = q :=
    (Category.assoc jback j q).symm.trans
      ((congrArg (fun a : Over.mk (U.ι ≫ c) ⟶ Over.mk (U.ι ≫ c) => a ≫ q) hj).trans
        (Category.id_comp q))
  have hεD : εD ≫ qD = 1 :=
    (Category.assoc ε jback qD).trans
      ((congrArg (fun a : Over.mk (U.ι ≫ c) ⟶ G.X => ε ≫ a) hback).trans hε)
  exact existsUnique_groupHom_geometricModulus c D εD G qD hmod hεD

end AlgebraicGeometry.GeneralizedJacobian
