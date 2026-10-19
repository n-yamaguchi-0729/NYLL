/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusDivisorFamily
import Nyll.JacobianVarieties.Generalized.ModulusComplementBaseChange
import Nyll.JacobianVarieties.Generalized.ModulusAbelRestriction
import Nyll.JacobianVarieties.Generalized.DivisorScalarExtension
import Nyll.JacobianVarieties.Generalized.ModulusIsoComparison
import Nyll.AlgebraicCurves.RelativeDivisors.BaseChange.ChangeBase

/-! # Scalar extension of the actual normalized divisor-family classes

The full divisor ideal is transported by the actual pullback associator. Its
specified normalized section is preserved, including the nonreduced modulus.
These formulas apply before sheafification, so actual equality of rigidified
families over a geometric parameter can be moved to the scalar-extended curve.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RelPicard.BaseChange AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- The actual divisor transferred to the scalar-extended curve is supported
away from the entire scalar-extended modulus. -/
theorem divisor_changeBaseEquiv_supported {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R')) {n : ℕ}
    (E : RelEffCartierDiv c n (t ≫ specMap R R'))
    (hE : E.SupportedIn (modulusComplement i)) :
    ((RelEffCartierDiv.changeBaseEquiv c (specMap R R') t n).symm E).SupportedIn
      (modulusComplement (modulusBaseChange c i (specMap R R'))) := by
  intro x hx
  change x ∈ (E.I.comap (κ c R' t).hom).support at hx
  rw [Scheme.IdealSheafData.support_comap] at hx
  rw [modulusComplement_baseChange]
  change (pullback.fst (baseChange R c R') t ≫ pullback.fst c (specMap R R')) x ∈
    modulusComplement i
  rw [← κ_hom_fst, Scheme.Hom.comp_apply]
  exact hE hx

variable [IsSeparated c] [SmoothOfRelativeDimension 1 c]

/-- The canonical divisor frame is preserved by the genuine scalar class equivalence. -/
theorem scalarExtensionClassesEquiv_divisorFamily {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R')) {n : ℕ}
    (E : RelEffCartierDiv c n (t ≫ specMap R R'))
    (hE : E.SupportedIn (modulusComplement i)) :
    scalarExtensionClassesEquiv c i R' t
      (modulusDivisorFamilyClass (baseChange R c R') (modulusBaseChange c i (specMap R R'))
        ((RelEffCartierDiv.changeBaseEquiv c (specMap R R') t n).symm E)
        (divisor_changeBaseEquiv_supported c i R' t E hE)) =
      modulusDivisorFamilyClass c i E hE := by
  apply (RigidifiedLineBundle.classOf_eq_iff _ _).mpr
  refine ⟨RigidifiedLineBundle.ofInvertibleIdealPullbackIsoOfEq
    (κ c R' t).inv (modulusScalarExtensionIso c i R' t).inv
    (RigidifiedLineBundle.inverse_square _ _ (modulusScalarExtension_square c i R' t))
    _ (RelEffCartierDiv.isInvertible_I _)
    (modulusDivisorFamily_avoids (baseChange R c R')
      (modulusBaseChange c i (specMap R R')) _
      (divisor_changeBaseEquiv_supported c i R' t E hE))
    E.I (RelEffCartierDiv.isInvertible_I E) (modulusDivisorFamily_avoids c i E hE) ?_⟩
  change (E.I.comap (κ c R' t).hom).comap (κ c R' t).inv = E.I
  rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

end AlgebraicGeometry.GeneralizedJacobian

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D D' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) {i : D ⟶ C} {i' : D' ⟶ C}
  [IsClosedImmersion i] [IsClosedImmersion i'] [IsSeparated c]
  [SmoothOfRelativeDimension 1 c] (a : D' ≅ D) (w : i' = a.hom ≫ i)

/-- An isomorphism of the whole modulus preserves the specified divisor rigidification. -/
theorem modulusIsoClassesEquiv_divisorFamily {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {n : ℕ}
    (E : RelEffCartierDiv c n t) (hE : E.SupportedIn (modulusComplement i)) :
    modulusIsoClassesEquiv c a w t (modulusDivisorFamilyClass c i E hE) =
      modulusDivisorFamilyClass c i' E
        (hE.mono (modulusComplement_le_of_restriction a.hom w)) := by
  apply (RigidifiedLineBundle.classOf_eq_iff _ _).mpr
  exact ⟨RigidifiedLineBundle.ofInvertibleIdealPullbackIsoOfEq
    (𝟙 _) (modulusIsoPullback c a w t).hom (modulusIsoPullback_square c a w t)
    E.I (RelEffCartierDiv.isInvertible_I E) (modulusDivisorFamily_avoids c i E hE)
    E.I (RelEffCartierDiv.isInvertible_I E)
    (modulusDivisorFamily_avoids c i' E
      (hE.mono (modulusComplement_le_of_restriction a.hom w)))
    (Scheme.IdealSheafData.comap_id E.I)⟩

end AlgebraicGeometry.GeneralizedJacobian
