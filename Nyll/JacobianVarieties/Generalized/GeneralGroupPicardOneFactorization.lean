/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeneralGeometricModulusExistence
import Nyll.JacobianVarieties.Generalized.GeometricModulusUniversalProperty

/-! # An intrinsic Picard-one factor for an actual open-curve group map

Starting with the original map, the full modulus-existence theorem constructs
one relative Cartier divisor over the original field whose complement is
exactly the given domain. Its geometric modulus condition then supplies the
unique equivariant factor through the intrinsic Picard-one scheme, together
with its actual group homomorphism. No divisor, modulus hypothesis, rational
basepoint, or scalar-extension factor is required from the caller.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry
open NeronModelInfra
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

/-- An actual open-curve map to a separated commutative group locally of
finite type constructs a ground-field modulus and its unique equivariant
intrinsic Picard-one factor. The modulus has exactly the original open
complement, and its full geometric condition is retained for further use.
Uniqueness concerns the factor pair for the returned divisor. -/
theorem exists_modulus_unique_picardOneFactor
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (q : Over.mk (U.ι ≫ c) ⟶ G.X) :
    ∃ (d : ℕ) (D : RelEffCartierDiv c d (𝟙 (Spec (.of K))))
      (hDU : modulusComplement (modulusCurveMap D) = U),
      let qD : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X :=
        (Over.homMk (V := Over.mk (U.ι ≫ c)) (C.homOfLE hDU.le)
          (by simp only [Over.mk_hom, ← Category.assoc, Scheme.homOfLE_ι])) ≫ q
      geometricRegularMapHasModulus c D G qD ∧
        ∃! fg : (groupScheme c D ⟶ G) × (picardOne c D ⟶ G.X),
          abelOneMap c D ≫ fg.2 = qD ∧
            ∀ (T : Over (Spec (.of K)))
              (a : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
              (a • x) ≫ fg.2 = (a ≫ fg.1.hom.hom.hom) * (x ≫ fg.2) := by
  obtain ⟨d, D, hDU, hmod⟩ := exists_group_geometricRegularMapHasModulus c U hU G q
  refine ⟨d, D, hDU, ?_⟩
  intro qD
  refine ⟨hmod, ?_⟩
  let _ : ModObj G.X G.X := ModObj.regular G.X
  have : IsIso (ModObj.leftSMul G.X G.X) :=
    SchemeTheory.PointedTorsor.isIso_leftSMul_regular G.X
  have htorsor : geometricTorsorMapHasModulus c D G G.X qD := by
    apply (geometricTorsorMapHasModulus_iff_coordinate c D G G.X qD η[G.X]).mpr
    simpa only [SchemeTheory.PointedTorsor.coordinate_regular_unit,
      Category.comp_id] using hmod
  exact existsUnique_picardOneMapFromGeometricModulus_unpointed c D G G.X qD htorsor

end AlgebraicGeometry.GeneralizedJacobian
