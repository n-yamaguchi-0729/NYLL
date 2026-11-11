/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.GenericGaloisMapComparison
public import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence

/-!
# Original decomposition images in pointed-cover subgroups

A decomposition element whose original generic Galois image lies in a
pointed-cover subgroup gives an element of the intersection with the literal
field-source decomposition image. The arithmetic label is unchanged.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale SchemeTheory

namespace EtaleFundamentalGroups.Inertia

universe u v w a

/-- Passing a native decomposition lift through the original quotient retains
both its subgroup membership and its original arithmetic label. -/
theorem exists_normalizationDecomposition_image_inf_of_generic_lift
    {U : Scheme.{u}} [IsIntegral U]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    (A : Type a) [CommRing A] [Algebra A U.functionField]
    [IsFractionRing A U.functionField] [Algebra A Ω]
    [IsScalarTower A U.functionField Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω))
    {P : Type v} {Γ : Type w} [Group P] [Group Γ]
    [TopologicalSpace P]
    (ρ : π₁ᵉᵗ(U.genericExtensionMorphism Ω) →ₜ* P) (π : P →* Γ)
    (arith : π₁ᵉᵗ(U.genericExtensionMorphism Ω) → Γ)
    (hπ : ∀ γ, π (ρ γ) = arith γ)
    (K : Subgroup π₁ᵉᵗ(U.genericExtensionMorphism Ω)) (H : Subgroup P)
    (hKH : K ≤ H.comap ρ.toMonoidHom) (g : Γ)
    (hlift : ∃ d : normalizationDecompositionGroup A U.functionField Ω Q,
      absoluteGenericGaloisToFundamentalGroup U Ω d.val ∈ K ∧
        arith (absoluteGenericGaloisToFundamentalGroup U Ω d.val) = g) :
    ∃ x : P, x ∈ ((ρ.comp (fieldSourceAbsoluteGaloisHom U.functionField Ω
      (U.fromSpecStalk (genericPoint U)))).toMonoidHom.comp
        (normalizationDecompositionInclusion A U.functionField Ω Q)).range ⊓ H ∧
      π x = g := by
  obtain ⟨d, hd, hlabel⟩ := hlift
  have hmap := DFunLike.congr_fun
    (absoluteGenericGaloisToFundamentalGroup_eq_fieldSourceAbsoluteGaloisHom U Ω) d.val
  have hmem : ρ (absoluteGenericGaloisToFundamentalGroup U Ω d.val) ∈ H := hKH hd
  refine ⟨ρ (fieldSourceAbsoluteGaloisHom U.functionField Ω
    (U.fromSpecStalk (genericPoint U)) d.val), ⟨⟨d, rfl⟩, ?_⟩, ?_⟩
  · exact Eq.mp (congrArg (fun γ => ρ γ ∈ H) hmap) hmem
  · exact (congrArg (fun γ => π (ρ γ)) hmap).symm.trans
      ((hπ (absoluteGenericGaloisToFundamentalGroup U Ω d.val)).trans hlabel)

end EtaleFundamentalGroups.Inertia
