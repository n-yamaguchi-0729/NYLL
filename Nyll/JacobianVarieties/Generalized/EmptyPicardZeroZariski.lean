/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.EmptyModulusZero
import Nyll.JacobianVarieties.Generalized.ModulusDegreeZero
import Nyll.JacobianVarieties.Generalized.OrdinaryZeroRepresentation
import Nyll.JacobianVarieties.Generalized.PointedConstruction
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Actual bundles representing the degree-zero-modulus Picard sheaf -/

noncomputable section

universe u

open CategoryTheory Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem isIso_emptyForgetZero {R : Type u} [CommRing R] {C D : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsEmpty D] :
    IsIso (forgetModulusZeroSheaf c i) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  have : Presheaf.IsLocallyInjective J (forgetModulusZeroPresheaf c i) :=
    EmptyModulus.forgetModulusZeroPresheaf_isLocallyInjective c i
  have : Presheaf.IsLocallySurjective J (forgetModulusZeroPresheaf c i) :=
    Presheaf.isLocallySurjective_of_surjective J _
      (fun T => EmptyModulus.forgetModulusZeroPresheaf_surjective c i T.unop)
  exact (J.W_iff (forgetModulusZeroPresheaf c i)).mp
    (J.W_of_isLocallyBijective (forgetModulusZeroPresheaf c i))

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  (D : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K))))

include ε in
/-- With a curve section, an empty modulus gives an actual rigidified bundle globally
on every parameter scheme, through the proved ordinary Poincare classification. -/
theorem zeroDegree_modulusPicardZero_toSheafify_surjective
    (T : Over (Spec (CommRingCat.of K))) :
    Function.Surjective ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardZeroPresheaf c (modulusCurveMap D))).app (op T)) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of K))
  let i := modulusCurveMap D
  let p := forgetModulusZeroPresheaf c i
  let etaOrd := toSheafify J (Unrigidified.zeroPresheaf c)
  let : IsEmpty D.I.subscheme := isEmpty_modulus_of_degree_zero D
  have : IsIso etaOrd := isIso_toSheafify J
    (ordinaryZeroPresheaf_isSheaf (Pointed.ordinaryRepresentation c ε))
  have : IsIso (forgetModulusZeroSheaf c i) := isIso_emptyForgetZero c i
  have : IsIso (forgetModulusZeroSheaf c i).hom := by
    change IsIso ((sheafToPresheaf J (Type (u + 1))).map (forgetModulusZeroSheaf c i))
    infer_instance
  intro x
  obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso (etaOrd.app (op T))).surjective
    ((forgetModulusZeroSheaf c i).hom.app (op T) x)
  obtain ⟨z, hz⟩ := EmptyModulus.forgetModulusZeroPresheaf_surjective c i T y
  refine ⟨z, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    ((forgetModulusZeroSheaf c i).hom.app (op T))).injective
  have hn := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality J p) (op T)) z
  exact hn.symm.trans ((congrArg (etaOrd.app (op T)) hz).trans hy)

include ε in
/-- The degree-zero-modulus sheafification is Zariski locally surjective without
postulating representatives or a sheafification-lifting property. -/
theorem zeroDegree_modulusPicardZero_toSheafify_isLocallySurjective_zariski :
    Presheaf.IsLocallySurjective
      (Scheme.zariskiTopology.over (Spec (CommRingCat.of K)))
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (modulusPicardZeroPresheaf c (modulusCurveMap D))) :=
  Presheaf.isLocallySurjective_of_surjective _ _
    (fun T => zeroDegree_modulusPicardZero_toSheafify_surjective c ε D T.unop)

include ε in
/-- In degree zero, the canonical affine open cover carries actual bundle
representatives of every section of the same modulus Picard-zero sheaf. -/
theorem zeroDegree_modulusPicardZero_exists_affineOpenCover_bundles
    (T : Over (Spec (CommRingCat.of K)))
    (x : (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.obj (op T)) :
    ∃ U : Scheme.AffineOpenCover.{u, u} T.left, ∀ j,
      ∃ (M : RigidifiedLineBundle
          (modulusBaseChange c (modulusCurveMap D) (U.f j ≫ T.hom)))
        (hM : RigidifiedLineBundle.classOf M ∈
          (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj
            (op (Over.mk (U.f j ≫ T.hom)))),
        (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
          (modulusPicardZeroPresheaf c (modulusCurveMap D))).app
            (op (Over.mk (U.f j ≫ T.hom))) ⟨RigidifiedLineBundle.classOf M, hM⟩ =
          (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.map
            (Over.homMk (U.f j) : Over.mk (U.f j ≫ T.hom) ⟶ T).op x := by
  let P := modulusPicardZeroPresheaf c (modulusCurveMap D)
  let eta := toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) P
  obtain ⟨a, ha⟩ := zeroDegree_modulusPicardZero_toSheafify_surjective c ε D T x
  refine ⟨T.left.affineOpenCover, fun j => ?_⟩
  let f : Over.mk (T.left.affineOpenCover.f j ≫ T.hom) ⟶ T :=
    Over.homMk (T.left.affineOpenCover.f j)
  let a' := P.map f.op a
  obtain ⟨M, hM⟩ := Quotient.exists_rep a'.val
  have hx : eta.app (op (Over.mk (T.left.affineOpenCover.f j ≫ T.hom))) a' =
      (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.map f.op x :=
    (eta.naturality_apply f.op a).trans
      (congrArg ((modulusPicardZeroSheaf c (modulusCurveMap D)).obj.map f.op) ha)
  have hM' : RigidifiedLineBundle.classOf M = a'.val := hM
  have hmem : RigidifiedLineBundle.classOf M ∈
      (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj
        (op (Over.mk (T.left.affineOpenCover.f j ≫ T.hom))) := by
    rw [hM']
    exact a'.property
  refine ⟨M, hmem, ?_⟩
  exact (congrArg (eta.app (op (Over.mk (T.left.affineOpenCover.f j ≫ T.hom))))
    (Subtype.ext hM')).trans hx

end AlgebraicGeometry.GeneralizedJacobian
