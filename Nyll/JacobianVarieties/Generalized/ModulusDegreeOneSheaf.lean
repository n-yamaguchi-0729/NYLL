/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusDegreeOne
import Nyll.JacobianVarieties.Generalized.ModulusForgetfulSurjectivity
import Nyll.JacobianVarieties.Generalized.ModulusKernelPresheaf

/-! # Forgetting a rational reduced modulus is an isomorphism of fppf group sheaves -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C Y : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) (i : Y ⟶ C)

/-- If the entire modulus is the base, its scalar quotient is trivial and forgetting is
locally injective. The argument uses the actual local boundary into the forgetful kernel. -/
theorem forgetModulusZeroGroupPresheaf_locallyInjective_of_isIso [IsIso (i ≫ c)] :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (forgetModulusZeroGroupPresheaf c i) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of K))
  let b := modulusBoundaryToKernelPresheaf c i
  have : Presheaf.IsLocallySurjective J b :=
    modulusBoundaryToKernelPresheaf_isLocallySurjective c i
  constructor
  intro X x y hxy
  let k : (modulusForgetfulKernelPresheaf c i).obj X := ⟨x / y, by
    apply MonoidHom.mem_ker.mpr
    change ((forgetModulusZeroGroupPresheaf c i).app X).hom (x / y) = 1
    rw [map_div, hxy, div_self']⟩
  apply J.superset_covering ?_ (Presheaf.imageSieve_mem J b k)
  intro U f hf
  obtain ⟨a, ha⟩ := hf
  have hsub : Subsingleton (ModulusUnits (i ≫ c) U ⧸ modulusScalars (i ≫ c) U) := by
    rw [modulusScalars_eq_top_of_isIso]
    exact QuotientGroup.subsingleton_quotient_top
  have : Subsingleton ((liftedModulusUnitQuotientGroupPresheaf (i ≫ c)).obj (op U)) :=
    inferInstanceAs (Subsingleton (ULift (ModulusUnits (i ≫ c) U ⧸
      modulusScalars (i ≫ c) U)))
  have ha1 : a = 1 := Subsingleton.elim _ _
  have hk : ((modulusForgetfulKernelPresheaf c i).map f.op).hom k = 1 := by
    rw [← ha, ha1]
    exact (b.app (op U)).hom.map_one
  have h := congrArg Subtype.val hk
  change ((modulusPicardZeroGroupPresheaf c i).map f.op).hom (x / y) = 1 at h
  rw [map_div] at h
  exact div_eq_one.mp h

variable {c} (D : RelEffCartierDiv c 1 (𝟙 (Spec (CommRingCat.of K))))

/-- A degree-one modulus changes no fppf Picard-zero group classes. -/
def degreeOneForgetfulSheafIso :
    modulusPicardZeroGroupSheaf c (modulusCurveMap D) ≅ ordinaryRelativePicardZeroGroupSheaf c := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of K))
  have : IsIso (modulusCurveMap D ≫ c) := by
    rw [modulusCurveMap_toBase]
    exact modulusBaseMap_isIso_of_degree_one D
  have : Presheaf.IsLocallyInjective J
      (forgetModulusZeroGroupPresheaf c (modulusCurveMap D)) :=
    forgetModulusZeroGroupPresheaf_locallyInjective_of_isIso c (modulusCurveMap D)
  have : Presheaf.IsLocallySurjective J
      (forgetModulusZeroGroupPresheaf c (modulusCurveMap D)) :=
    forgetModulusZeroGroupPresheaf_isLocallySurjective D
  let m := forgetModulusZeroGroupSheaf c (modulusCurveMap D)
  have hm : IsIso m := (J.W_iff (forgetModulusZeroGroupPresheaf c (modulusCurveMap D))).mp
    (J.W_of_isLocallyBijective (forgetModulusZeroGroupPresheaf c (modulusCurveMap D)))
  exact ⟨m, Classical.choose hm.out, (Classical.choose_spec hm.out).1,
    (Classical.choose_spec hm.out).2⟩

end AlgebraicGeometry.GeneralizedJacobian
