/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelUniquenessScheme
import Nyll.JacobianVarieties.Generalized.ModulusAbelGroupScalarExtension
import Nyll.SchemeTheory.GroupSchemes.GeometricPointHom

/-!
# Uniqueness of the pointed generalized Abel factorization over every field

The actual scalar-extension comparison preserves full-modulus divisor
classes and the actual Abel morphism. The proved generation over algebraically
closed extensions therefore detects every geometric point. Reducedness of
the constructed generalized Jacobian gives equality of the original group
scheme morphisms.
-/

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
  (G : CommGrp (Over (Spec (CommRingCat.of K))))
  (f g : groupScheme c D ⟶ G)
  (heq : modulusAbelMap c D ε ≫ f.hom.hom.hom =
    modulusAbelMap c D ε ≫ g.hom.hom.hom)

include heq

/-- Agreement on the original Abel morphism detects all points over any
algebraically closed extension, through the actual group comparison. -/
theorem modulusAbel_groupHom_ext_extensionPoints
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (x : (Over.map (specMap K L)).obj (Over.mk (𝟙 (Spec (CommRingCat.of L)))) ⟶
      (groupScheme c D).X) : x ≫ f.hom.hom.hom = x ≫ g.hom.hom.hom := by
  let T := Over.mk (𝟙 (Spec (CommRingCat.of L)))
  let e := groupScalarExtensionPointEquiv c D L T
  let φ := (IsMonHom.monoidHom f.hom.hom.hom ((Over.map (specMap K L)).obj T)).toAdditive
  let ψ := (IsMonHom.monoidHom g.hom.hom.hom ((Over.map (specMap K L)).obj T)).toAdditive
  have h := modulusAbel_points_addHom_ext_of_isAlgClosed (baseChange K c L)
    (D.changeBaseOfIdentity (specMap K L)) (modulusBasepointScalarExtension c D L ε)
    (φ.comp e.toAdditive.toAddMonoidHom) (ψ.comp e.toAdditive.toAddMonoidHom)
    (fun y => by
      change Additive.ofMul (e (y ≫ modulusAbelMap (baseChange K c L)
        (D.changeBaseOfIdentity (specMap K L)) (modulusBasepointScalarExtension c D L ε)) ≫
          f.hom.hom.hom) =
        Additive.ofMul (e (y ≫ modulusAbelMap (baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)) (modulusBasepointScalarExtension c D L ε)) ≫
            g.hom.hom.hom)
      rw [groupScalarExtensionPointEquiv_modulusAbelMap,
        Category.assoc, Category.assoc, heq])
  obtain ⟨z, rfl⟩ := e.surjective x
  exact congrArg Additive.toMul (DFunLike.congr_fun h (Additive.ofMul z))

/-- Over any field, an actual group morphism out of the generalized Jacobian
is uniquely determined by its composition with the pointed Abel morphism. -/
theorem modulusAbel_groupHom_ext [IsSeparated G.X.hom] : f = g := by
  apply CommGrp.hom_ext
  apply GroupSchemes.hom_ext_geometricPoints
  intro Ω _ _ a x
  let : Algebra K Ω := (Spec.preimage a).hom.toAlgebra
  have ha : specMap K Ω = a := Spec.map_preimage a
  let y : (Over.map (specMap K Ω)).obj (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) ⟶
      (groupScheme c D).X :=
    Over.homMk x.left ((Over.w x).trans ((Category.id_comp (specMap K Ω)).trans ha).symm)
  have h := modulusAbel_groupHom_ext_extensionPoints c D ε G f g heq Ω y
  have hleft := congrArg Over.Hom.left h
  apply Over.OverMorphism.ext
  exact hleft

end AlgebraicGeometry.GeneralizedJacobian
