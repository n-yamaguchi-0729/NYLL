/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusFamilyIdeal
import Nyll.JacobianVarieties.Generalized.ModulusComplementBaseChange
import Nyll.AlgebraicCurves.RelativeDivisors.Support.RelEffCartierDivSupportedIn

/-! # Normalized divisors are supported in the actual modulus complement -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))

/-- The ideal giving the whole family is exactly the kernel of its actual modulus inclusion. -/
theorem modulusFamilyIdeal_ker :
    (modulusFamilyDivisor D t).I = (modulusBaseChange c (modulusCurveMap D) t).ker := by
  have hw : (modulusFamilyDivisor D t).I.subschemeι =
      (modulusFamilyIdealIso D t).hom ≫ modulusBaseChange c (modulusCurveMap D) t :=
    (Category.comp_id _).symm.trans (modulusFamilyIdealIso_square D t)
  rw [← Scheme.IdealSheafData.ker_subschemeι (modulusFamilyDivisor D t).I,
    hw, Scheme.Hom.ker_comp_of_isIso]

/-- Avoiding the full modulus subscheme is precisely the needed support condition on the curve. -/
theorem supportedIn_of_avoids_modulusFamily [IsClosedImmersion (modulusCurveMap D)]
    {n : ℕ} (E : RelEffCartierDiv c n t)
    (ha : ∀ y : (modulusFamilyDivisor D t).I.subscheme,
      (modulusFamilyDivisor D t).I.subschemeι.base y ∉ E.I.support) :
    E.SupportedIn (modulusComplement (modulusCurveMap D)) := by
  intro z hz
  have hJ : z ∉ (modulusFamilyDivisor D t).I.support := by
    intro hzJ
    have hzrange : z ∈ Set.range (modulusFamilyDivisor D t).I.subschemeι :=
      Eq.mpr (congrArg (fun S : Set (pullback c t : Scheme.{u}) => z ∈ S)
        (modulusFamilyDivisor D t).I.range_subschemeι) hzJ
    obtain ⟨y, rfl⟩ := hzrange
    exact ha y hz
  have hU : z ∈ modulusComplement (modulusBaseChange c (modulusCurveMap D) t) := by
    change z ∉ (modulusBaseChange c (modulusCurveMap D) t).ker.support
    rw [← modulusFamilyIdeal_ker D t]
    exact hJ
  rw [modulusComplement_baseChange] at hU
  exact hU

end AlgebraicGeometry.GeneralizedJacobian
