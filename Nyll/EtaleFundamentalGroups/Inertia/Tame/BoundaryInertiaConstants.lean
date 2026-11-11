/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspDecompositionConstants
public import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspArithmeticNormalizer
public import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildSubgroup

/-!
# Boundary inertia fixes the original constants

The original constant-residue map is injective at every normalization prime.
Thus the native inertia group fixes the constant closure even when the closed
point is not rational. Its original fundamental-group image, and hence its
native wild subgroup, lie in the original arithmetic kernel.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale SchemeTheory

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] normalizationCommAlgGaloisAction

variable (k A F κ Ω : Type u)
  [Field k] [CommRing A] [Field F] [Field κ] [Field Ω]
  [Algebra k A] [Algebra k F] [Algebra k κ] [Algebra k Ω]
  [Algebra A F] [IsFractionRing A F]
  [Algebra F Ω] [Algebra A Ω] [Algebra κ Ω]
  [IsScalarTower A F Ω] [IsScalarTower k A Ω]
  [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
  [IsGalois F Ω] [IsAlgClosure k κ]
  (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsPrime]

/-- Native inertia at any original normalization prime fixes all constants.
No rationality or residue-field identification is required. -/
theorem normalizationInertia_restrict_constants_eq_one
    (γ : Gal(Ω/F)) (hγ : γ ∈ Q.inertia Gal(Ω/F)) :
    (γ.restrictScalars k).restrictNormal κ = 1 := by
  let B := normalizationCommAlgCat A Ω
  let c : κ →+* B := arithmeticConstantNormalizationMap k A κ Ω
  let δ := (γ.restrictScalars k).restrictNormal κ
  have hc (x : κ) : c (δ x) = γ • c x := by
    apply Subtype.ext
    have haction := congrArg (fun z : B →+* Ω => z (c x))
      (normalizationCommAlg_action_comp_inclusion A F Ω γ)
    change γ (algebraMap κ Ω x) =
      (show integralClosure A Ω from γ • c x).val at haction
    exact ((γ.restrictScalars k).restrictNormal_commutes κ x).trans haction
  apply AlgEquiv.ext
  intro x
  apply (arithmeticConstantResidueMap k A κ Ω Q).injective
  change Ideal.Quotient.mk Q (c (δ x)) = Ideal.Quotient.mk Q (c x)
  rw [hc]
  have hzero := (Ideal.Quotient.eq_zero_iff_mem).mpr (hγ (c x))
  simpa only [map_sub, sub_eq_zero] using hzero

variable [IsSepClosure k κ] [IsSepClosure F Ω] [IsSepClosed Ω]
  {U : Scheme.{u}} [IsIntegral U]
  (f : U ⟶ Spec (.of k)) (jF : Spec (.of F) ⟶ U)
  (hbase : (ξ F Ω ≫ jF) ≫ f = ξ k Ω)

include hbase in
/-- The original fundamental-group image of every native inertia element
is in the kernel of the original arithmetic projection. -/
theorem normalizationInertia_fieldSource_arithmetic_eq_one
    (γ : Gal(Ω/F)) (hγ : γ ∈ Q.inertia Gal(Ω/F)) :
    arithmeticFundamentalGroupHom k κ f (ξ F Ω ≫ jF)
      (fieldSourceAbsoluteGaloisHom F Ω jF γ) = 1 := by
  obtain ⟨α, hα⟩ := exists_fieldSource_arithmetic_restriction_label
    k F κ Ω f jF hbase
  rw [hα, normalizationInertia_restrict_constants_eq_one k A F κ Ω Q γ hγ,
    mul_one, mul_inv_cancel]

variable [IsDomain A] [IsDiscreteValuationRing A] [Q.IsMaximal]

include hbase in
/-- The actual principal-unit wild subgroup has geometric image under the
same field-source map; no prime-primary quotient of the geometric group is used. -/
theorem normalizationWild_fieldSource_arithmetic_eq_one
    (σ : actualNormalizationWildSubgroup A F Ω Q) :
    arithmeticFundamentalGroupHom k κ f (ξ F Ω ≫ jF)
      (fieldSourceAbsoluteGaloisHom F Ω jF σ.val.val) = 1 :=
  normalizationInertia_fieldSource_arithmetic_eq_one k A F κ Ω Q f jF hbase
    σ.val.val σ.val.property

end EtaleFundamentalGroups.Inertia
