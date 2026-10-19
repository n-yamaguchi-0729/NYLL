/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeneralGeometricModulusExistence
import Nyll.JacobianVarieties.Generalized.GeometricModulusProduct

/-! # A common full modulus for two actual group maps

The product-valued map constructs a single ground-field divisor with exactly
the original open complement. Its two projections have the same full geometric
modulus; neither the domain nor the ground field is enlarged.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory NeronModelInfra
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

/-- Two actual group maps on one nonempty open curve admit a common full
geometric Cartier modulus over the original field, with that same complement.
The targets need only be separated commutative groups locally of finite type. -/
theorem exists_common_group_geometricRegularMapHasModulus
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (G H : CommGrp (Over (Spec (.of K))))
    [IsSeparated G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsSeparated H.X.hom] [LocallyOfFiniteType H.X.hom]
    (q : Over.mk (U.ι ≫ c) ⟶ G.X) (r : Over.mk (U.ι ≫ c) ⟶ H.X) :
    ∃ (d : ℕ) (D : RelEffCartierDiv c d (𝟙 (Spec (.of K))))
      (hDU : modulusComplement (modulusCurveMap D) = U),
      let j : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
          Over.mk (U.ι ≫ c) :=
        Over.homMk (V := Over.mk (U.ι ≫ c)) (C.homOfLE hDU.le)
          (by simp only [Over.mk_hom, ← Category.assoc, Scheme.homOfLE_ι])
      geometricRegularMapHasModulus c D G (j ≫ q) ∧
        geometricRegularMapHasModulus c D H (j ≫ r) := by
  have : IsSeparated (GroupSchemes.product G H).X.hom := by
    change IsSeparated (pullback.fst G.X.hom H.X.hom ≫ G.X.hom)
    infer_instance
  have : LocallyOfFiniteType (GroupSchemes.product G H).X.hom := by
    change LocallyOfFiniteType (pullback.fst G.X.hom H.X.hom ≫ G.X.hom)
    infer_instance
  let qr : Over.mk (U.ι ≫ c) ⟶ (GroupSchemes.product G H).X := lift q r
  obtain ⟨d, D, hDU, hmod⟩ :=
    exists_group_geometricRegularMapHasModulus c U hU (GroupSchemes.product G H) qr
  refine ⟨d, D, hDU, ?_⟩
  intro j
  change geometricRegularMapHasModulus c D (GroupSchemes.product G H) (j ≫ qr) at hmod
  have hparts := (geometricRegularMapHasModulus_product_iff c D G H (j ≫ qr)).mp hmod
  have hf : (j ≫ qr) ≫ fst G.X H.X = j ≫ q :=
    (Category.assoc j qr (fst G.X H.X)).trans
      (congrArg (fun a : Over.mk (U.ι ≫ c) ⟶ G.X => j ≫ a) (lift_fst q r))
  have hs : (j ≫ qr) ≫ snd G.X H.X = j ≫ r :=
    (Category.assoc j qr (snd G.X H.X)).trans
      (congrArg (fun a : Over.mk (U.ι ≫ c) ⟶ H.X => j ≫ a) (lift_snd q r))
  exact ⟨Eq.mp (congrArg (geometricRegularMapHasModulus c D G) hf) hparts.1,
    Eq.mp (congrArg (geometricRegularMapHasModulus c D H) hs) hparts.2⟩

end AlgebraicGeometry.GeneralizedJacobian
