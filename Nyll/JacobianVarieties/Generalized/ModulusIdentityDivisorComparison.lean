/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedEulerZeroComparison
import Nyll.JacobianVarieties.Generalized.ModulusCurveIdeal
import Nyll.JacobianVarieties.Generalized.ModulusDivisorFamily
import Nyll.JacobianVarieties.Generalized.RigidifiedIdealPullbackComparison

/-! # The full Cartier ideal and its actual identity-test divisor class -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsSeparated c] [SmoothOfRelativeDimension 1 c]

omit [IsClosedImmersion i] [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
/-- The transported original-curve Cartier ideal avoids the entire kernel modulus. -/
theorem modulusCurveIdeal_avoids {n : ℕ}
    (E : RelEffCartierDiv c n (𝟙 (Spec (CommRingCat.of K))))
    (hE : E.SupportedIn (modulusComplement i)) (y : i.ker.subscheme) :
    i.ker.subschemeι.base y ∉ (modulusCurveIdeal E).support := by
  intro hy
  rw [modulusCurveIdeal_eq_comap, Scheme.IdealSheafData.support_comap] at hy
  have hu := hE hy
  change pullback.fst c (𝟙 (Spec (CommRingCat.of K)))
    (inv (pullback.fst c (𝟙 (Spec (CommRingCat.of K)))) (i.ker.subschemeι y)) ∈
      modulusComplement i at hu
  rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id] at hu
  change i.ker.subschemeι y ∉ i.ker.support at hu
  apply hu
  change i.ker.subschemeι y ∈ (i.ker.support : Set C)
  rw [← i.ker.range_subschemeι]
  exact Set.mem_range_self y

/-- Identity base change transports the whole canonical Cartier frame, not only its module. -/
theorem closedModulusIdentityClassesEquiv_ofDivisor {n : ℕ}
    (E : RelEffCartierDiv c n (𝟙 (Spec (CommRingCat.of K))))
    (hE : E.SupportedIn (modulusComplement i)) :
    closedModulusIdentityClassesEquiv c i
        (RigidifiedLineBundle.classOf (RigidifiedLineBundle.ofInvertibleIdeal i.ker.subschemeι
          (modulusCurveIdeal E) (modulusCurveIdeal_isInvertible E)
          (modulusCurveIdeal_avoids c i E hE))) =
      modulusDivisorFamilyClass c i E hE := by
  let I := modulusCurveIdeal E
  have hI : I.IsInvertible := modulusCurveIdeal_isInvertible E
  have ha := modulusCurveIdeal_avoids c i E hE
  have hia : ∀ y : D, i.base y ∉ I.support := by
    intro y
    have h := ha (i.toImage y)
    change i.ker.subschemeι (i.toImage y) ∉ I.support at h
    rw [← Scheme.Hom.comp_apply, i.toImage_imageι] at h
    exact h
  let M := RigidifiedLineBundle.ofInvertibleIdeal i.ker.subschemeι I hI ha
  let N := RigidifiedLineBundle.ofInvertibleIdeal i I hI hia
  have hc : closedModulusClassesEquiv i (RigidifiedLineBundle.classOf M) =
      RigidifiedLineBundle.classOf N := by
    apply (RigidifiedLineBundle.classOf_eq_iff _ _).mpr
    exact ⟨RigidifiedLineBundle.ofInvertibleIdealPullbackIsoOfEq (𝟙 C) i.toImage
      (closedModulus_square i) I hI ha I hI hia (Scheme.IdealSheafData.comap_id I)⟩
  have hfull : I.comap (pullback.fst c (𝟙 (Spec (CommRingCat.of K)))) = E.I := by
    rw [show I = modulusCurveIdeal E from rfl, modulusCurveIdeal_eq_comap,
      ← Scheme.IdealSheafData.comap_comp, IsIso.hom_inv_id,
      Scheme.IdealSheafData.comap_id]
  have hi : modulusIdentityBaseChangeClassesEquiv c i (RigidifiedLineBundle.classOf N) =
      modulusDivisorFamilyClass c i E hE := by
    apply (RigidifiedLineBundle.classOf_eq_iff _ _).mpr
    exact ⟨RigidifiedLineBundle.ofInvertibleIdealPullbackIsoOfEq
      (pullback.fst c (𝟙 _)) (pullback.fst (i ≫ c) (𝟙 _))
      (modulusIdentityBaseChange_square c i) I hI hia E.I
      (RelEffCartierDiv.isInvertible_I E) (modulusDivisorFamily_avoids c i E hE) hfull⟩
  exact (congrArg (modulusIdentityBaseChangeClassesEquiv c i) hc).trans hi

end AlgebraicGeometry.GeneralizedJacobian
