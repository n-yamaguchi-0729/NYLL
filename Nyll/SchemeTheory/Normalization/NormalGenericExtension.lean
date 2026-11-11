/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Normalization.GenericChartPoints
public import Nyll.SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization

/-!
# Normality of the actual generic-extension normalization

The affine charts of the relative normalization are the literal integral
closures inside the chosen algebraic extension of the function field.
That extension is their fraction field, so those rings and all of their
localizations are integrally closed. The actual chart stalk isomorphisms
therefore prove normality of the original relative normalization.

Neither finiteness of the extension nor normality or Noetherianity of the
base is required.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace EtaleFundamentalGroups

universe u

variable (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L]
  [Algebra X.functionField L] [Algebra.IsAlgebraic X.functionField L]

/-- Every actual local ring of the normalization in an algebraic generic
field extension is integrally closed. -/
theorem genericExtensionNormalization_stalk_isIntegrallyClosed
    (z : (X.genericExtensionMorphism L).normalization) :
    IsIntegrallyClosed
      ((X.genericExtensionMorphism L).normalization.presheaf.stalk z) := by
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤)
    (x := (X.genericExtensionMorphism L).fromNormalization z) (by trivial)
  let : Nonempty U := ⟨⟨(X.genericExtensionMorphism L).fromNormalization z, hzU⟩⟩
  let : Algebra Γ(X, U) L := X.affineExtensionAlgebra U L
  let : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let : IsScalarTower Γ(X, U) X.functionField L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsFractionRing (integralClosure Γ(X, U) L) L :=
    integralClosure_isFractionRing_of_fractionField_algebraic
      Γ(X, U) X.functionField L
  have : IsIntegrallyClosed (integralClosure Γ(X, U) L) :=
    (IsIntegrallyClosed.integralClosure_eq_bot_iff L).mp integralClosure_idem
  have hz : z ∈ Set.range (genericNormalizationChart X L U hU) := by
    change z ∈ (genericNormalizationChart X L U hU).opensRange
    rw [genericNormalizationChart_opensRange]
    exact hzU
  obtain ⟨t, ht⟩ := hz
  have : IsIntegrallyClosed
      ((Spec (.of (integralClosure Γ(X, U) L))).presheaf.stalk t) :=
    IsNormalIntegral.stalk_isIntegrallyClosed t
  have hnormal : IsIntegrallyClosed
      ((X.genericExtensionMorphism L).normalization.presheaf.stalk
        (genericNormalizationChart X L U hU t)) :=
    IsIntegrallyClosed.of_equiv
      (asIso ((genericNormalizationChart X L U hU).stalkMap t)).symm.commRingCatIsoToRingEquiv
  exact ht ▸ hnormal

/-- The original relative normalization in any algebraic function-field
extension is a normal integral scheme. -/
theorem genericExtensionNormalization_isNormalIntegral :
    IsNormalIntegral (X.genericExtensionMorphism L).normalization :=
  IsNormalIntegral.of_stalks _
    (genericExtensionNormalization_stalk_isIntegrallyClosed X L)

end EtaleFundamentalGroups
