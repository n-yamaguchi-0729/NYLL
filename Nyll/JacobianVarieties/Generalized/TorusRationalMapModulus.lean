/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.SplitTorusRegularMapModulus
import Nyll.JacobianVarieties.Generalized.GeometricModulusMapReflection
import Nyll.JacobianVarieties.Generalized.ModulusOpenComplement
import Nyll.JacobianVarieties.Generalized.GeometricModulusPointedUniversalProperty
import Nyll.SchemeTheory.GroupSchemes.Torus
import Nyll.SchemeTheory.GroupSchemes.TorusSeparatedQuasiCompact

/-! # Full moduli for rational maps to tori over arbitrary fields

Every regular torus-valued map on a modulus complement has that geometric
modulus. Splitting is used only after the prescribed geometric extension;
the original torus and divisor remain over the original field. For an
arbitrary nonempty domain, its actual finite boundary supplies the divisor.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsTorus G]

/-- Any actual torus morphism on a full modulus complement has that modulus
after every algebraically closed extension, including over imperfect fields. -/
theorem geometricRegularMapHasModulus_of_isTorus
    {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X) :
    geometricRegularMapHasModulus c D G q := by
  intro L fieldL algebraL closedL cL DL algL ML qL
  let G_L := (GroupSchemes.baseChange (specMap K L)).obj G
  have : IsSplitTorus G_L := IsTorus.geometric_split L (specMap K L)
  obtain ⟨n, ⟨e⟩⟩ := IsSplitTorus.exists_split (G := G_L)
  let q₀ : SchemeHomOver
      ((modulusComplement (modulusCurveMap DL)).ι ≫ cL) G_L.X.hom :=
    ⟨qL.left, Over.w qL⟩
  apply (ML.regularMapHasModulus_comp_iff_of_injective DL G_L
    (GroupSchemes.splitTorus L n) q₀ e.hom
      (fun _ _ h => (cancel_mono e.hom.hom.hom.hom).mp h)).mp
  exact ML.splitTorus_regularMapHasModulus DL n _

/-- A rational map to an arbitrary torus admits a full relative Cartier
modulus over its original field, with exactly its original open domain. -/
theorem exists_torus_geometricRegularMapHasModulus
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (q : Over.mk (U.ι ≫ c) ⟶ G.X) :
    ∃ (d : ℕ) (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
      (hDU : modulusComplement (modulusCurveMap D) = U),
      geometricRegularMapHasModulus c D G
        ((Over.homMk (C.homOfLE hDU.le) (by
          change C.homOfLE hDU.le ≫ (U.ι ≫ c) =
            (modulusComplement (modulusCurveMap D)).ι ≫ c
          rw [← Category.assoc, Scheme.homOfLE_ι]) :
          Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
            Over.mk (U.ι ≫ c)) ≫ q) := by
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton c
  obtain ⟨d, D, hDU⟩ := exists_modulusComplement_eq c U hU
  exact ⟨d, D, hDU, geometricRegularMapHasModulus_of_isTorus c G D _⟩

/-- A torus-valued map has a unique translated generalized-Jacobian factor
without a separate modulus proof from the caller. -/
theorem existsUnique_groupHom_torus_translation
    {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X) :
    ∃! φ : groupScheme c D ⟶ G,
      modulusAbelMap c D ε ≫ φ.hom.hom.hom =
        q / (toUnit (Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) ≫ ε ≫ q) := by
  exact existsUnique_groupHom_geometricModulus_translation c D ε G q
    (geometricRegularMapHasModulus_of_isTorus c G D q)

/-- A torus-valued map sending the chosen curve point to the identity has
a unique group factor through the actual Abel map. -/
theorem existsUnique_groupHom_torus
    {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X)
    (hε : ε ≫ q = 1) :
    ∃! φ : groupScheme c D ⟶ G, modulusAbelMap c D ε ≫ φ.hom.hom.hom = q := by
  exact existsUnique_groupHom_geometricModulus c D ε G q
    (geometricRegularMapHasModulus_of_isTorus c G D q) hε

end AlgebraicGeometry.GeneralizedJacobian
