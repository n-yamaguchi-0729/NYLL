/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedEulerZeroComparison
import Nyll.JacobianVarieties.Generalized.ModulusAbelCanonicalPoint
import Nyll.JacobianVarieties.Generalized.RigidifiedIdealPullbackComparison
import Nyll.AlgebraicCurves.Geometry.Schemes.BaseChange.HomPullbackKerPowInvModuleIso

/-! # The actual divisor point class maps to the original Abel family -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits NeronModelInfra
open AlgebraicCurves.Geometry.Schemes.Proofs
open Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso.AlgebraicGeometry.BCKerGlue

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsSeparated c] [SmoothOfRelativeDimension 1 c]

/-- The full-modulus point ideal, with its specified frame, becomes the actual Abel bundle. -/
theorem closedModulusIdentityClassesEquiv_ofPoint
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) ((modulusComplement i).ι ≫ c))
    (ha : ∀ y : i.ker.subscheme,
      i.ker.subschemeι.base y ∉ (x.1 ≫ (modulusComplement i).ι).ker.support) :
    closedModulusIdentityClassesEquiv c i (RigidifiedLineBundle.classOf
      (RigidifiedLineBundle.ofInvertibleIdeal i.ker.subschemeι
        (x.1 ≫ (modulusComplement i).ι).ker
        (Scheme.Hom.isInvertible_ker_of_comp_eq_id _ ((Category.assoc _ _ _).trans x.2)) ha)) =
      RigidifiedLineBundle.classOf (modulusAbelBundleAt c i x) := by
  let p := x.1 ≫ (modulusComplement i).ι
  have hp : p ≫ c = 𝟙 _ := (Category.assoc _ _ _).trans x.2
  have hI : p.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp
  have hia : ∀ y : D, i.base y ∉ p.ker.support := by
    intro y
    have h := ha (i.toImage y)
    change i.ker.subschemeι (i.toImage y) ∉ p.ker.support at h
    rw [← Scheme.Hom.comp_apply, i.toImage_imageι] at h
    exact h
  let M := RigidifiedLineBundle.ofInvertibleIdeal i.ker.subschemeι p.ker hI ha
  let N := RigidifiedLineBundle.ofInvertibleIdeal i p.ker hI hia
  have hc : closedModulusClassesEquiv i (RigidifiedLineBundle.classOf M) =
      RigidifiedLineBundle.classOf N := by
    apply (RigidifiedLineBundle.classOf_eq_iff _ _).mpr
    exact ⟨RigidifiedLineBundle.ofInvertibleIdealPullbackIsoOfEq (𝟙 C) i.toImage
      (closedModulus_square i) p.ker hI ha p.ker hI hia
        (Scheme.IdealSheafData.comap_id p.ker)⟩
  let E : RelEffCartierDiv c 1 (𝟙 (Spec (CommRingCat.of K))) :=
    RelEffCartierDiv.ofPoint c p hp
  have hgraph : p.ker.comap (pullback.fst c (𝟙 _)) = E.I :=
    ker_comap_eq_ker (pullback.fst c (𝟙 _)) p (graphOver c p hp) (graphOver_fst c p hp)
  have hi : modulusIdentityBaseChangeClassesEquiv c i (RigidifiedLineBundle.classOf N) =
      RigidifiedLineBundle.classOf (modulusAbelBundleAt c i x) := by
    apply (RigidifiedLineBundle.classOf_eq_iff _ _).mpr
    exact ⟨(RigidifiedLineBundle.ofInvertibleIdealPullbackIsoOfEq
      (pullback.fst c (𝟙 _)) (pullback.fst (i ≫ c) (𝟙 _))
      (modulusIdentityBaseChange_square c i) p.ker hI hia E.I
      (RelEffCartierDiv.isInvertible_I E) (modulusPointDivisor_avoids c i x) hgraph).trans
        (modulusAbelBundleAtCanonicalIso c i x).symm⟩
  exact (congrArg (modulusIdentityBaseChangeClassesEquiv c i) hc).trans hi

end AlgebraicGeometry.GeneralizedJacobian
