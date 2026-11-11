/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Normalization.GenericFiber.GenericExtension
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Literal primes of generic normalizations

The standard chart of a generic normalization is an open immersion whose
image is exactly the inverse image of the chosen affine base open. Thus a
point of the actual normalization determines a prime of the literal integral
closure, with its exact contraction to the affine base ring. Closed base
points give maximal normalization primes by integrality.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace EtaleFundamentalGroups

universe u

variable (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L]
  [Algebra X.functionField L]

/-- The literal integral-closure chart is an open immersion. -/
instance genericNormalizationChart_isOpenImmersion
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsOpenImmersion (genericNormalizationChart X L U hU) := by
  let := X.affineExtensionAlgebra U L
  let := ((X.genericExtensionMorphism L).app U).hom.toAlgebra
  let c : Spec (.of (integralClosure Γ(X, U)
      Γ(Spec (.of L), X.genericExtensionMorphism L ⁻¹ᵁ U))) ⟶
      (X.genericExtensionMorphism L).normalization :=
    (X.genericExtensionMorphism L).normalizationOpenCover.f ⟨U, hU⟩
  have : IsOpenImmersion c :=
    (X.genericExtensionMorphism L).normalizationOpenCover.map_prop ⟨U, hU⟩
  let e := (X.genericExtensionSectionsAlgEquiv L U).mapIntegralClosure.toCommRingCatIso
  exact inferInstanceAs (IsOpenImmersion (Spec.map e.hom ≫ c))

/-- The chart covers exactly the points lying above the original affine open. -/
theorem genericNormalizationChart_opensRange
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (genericNormalizationChart X L U hU).opensRange =
      (X.genericExtensionMorphism L).fromNormalization ⁻¹ᵁ U := by
  let := X.affineExtensionAlgebra U L
  let := ((X.genericExtensionMorphism L).app U).hom.toAlgebra
  let c : Spec (.of (integralClosure Γ(X, U)
      Γ(Spec (.of L), X.genericExtensionMorphism L ⁻¹ᵁ U))) ⟶
      (X.genericExtensionMorphism L).normalization :=
    (X.genericExtensionMorphism L).normalizationOpenCover.f ⟨U, hU⟩
  have : IsOpenImmersion c :=
    (X.genericExtensionMorphism L).normalizationOpenCover.map_prop ⟨U, hU⟩
  let e := (X.genericExtensionSectionsAlgEquiv L U).mapIntegralClosure.toCommRingCatIso
  change (Spec.map e.hom ≫ c).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact ((X.genericExtensionMorphism L).fromNormalization_preimage ⟨U, hU⟩).symm

/-- A point of the actual normalization gives a literal integral-closure prime,
whose contraction is the prime attached to its original base point. -/
theorem exists_genericNormalizationChart_point
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (z : (X.genericExtensionMorphism L).normalization)
    (hz : (X.genericExtensionMorphism L).fromNormalization z ∈ U) :
    let := X.affineExtensionAlgebra U L
    ∃ q : PrimeSpectrum (integralClosure Γ(X, U) L),
      genericNormalizationChart X L U hU q = z ∧
      q.comap (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)) =
        hU.primeIdealOf ⟨(X.genericExtensionMorphism L).fromNormalization z, hz⟩ := by
  let := X.affineExtensionAlgebra U L
  have hz' : z ∈ (genericNormalizationChart X L U hU).opensRange := by
    rw [genericNormalizationChart_opensRange]
    exact hz
  obtain ⟨q, hq⟩ := hz'
  refine ⟨q, hq, ?_⟩
  apply hU.fromSpec.isOpenEmbedding.injective
  change (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) (integralClosure Γ(X, U) L))) ≫ hU.fromSpec) q = _
  rw [← genericNormalizationChart_base, Scheme.Hom.comp_apply, hq,
    IsAffineOpen.fromSpec_primeIdealOf]

/-- Over a closed base point, the same literal chart prime is maximal. -/
theorem exists_genericNormalizationChart_maximalPoint
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (z : (X.genericExtensionMorphism L).normalization)
    (hz : (X.genericExtensionMorphism L).fromNormalization z ∈ U)
    (hclosed : IsClosed {(X.genericExtensionMorphism L).fromNormalization z}) :
    let := X.affineExtensionAlgebra U L
    ∃ q : PrimeSpectrum (integralClosure Γ(X, U) L),
      genericNormalizationChart X L U hU q = z ∧
      q.comap (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)) =
        hU.primeIdealOf ⟨(X.genericExtensionMorphism L).fromNormalization z, hz⟩ ∧
      q.asIdeal.IsMaximal := by
  let := X.affineExtensionAlgebra U L
  obtain ⟨q, hq, hbase⟩ := exists_genericNormalizationChart_point X L U hU z hz
  refine ⟨q, hq, hbase, ?_⟩
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Γ(X, U)) q.asIdeal
  have hunder : q.asIdeal.under Γ(X, U) =
      (hU.primeIdealOf ⟨(X.genericExtensionMorphism L).fromNormalization z, hz⟩).asIdeal :=
    congrArg PrimeSpectrum.asIdeal hbase
  rw [hunder]
  exact hU.primeIdealOf_isMaximal_of_isClosed
    ⟨(X.genericExtensionMorphism L).fromNormalization z, hz⟩ hclosed

end EtaleFundamentalGroups
