/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Normalization.GenericChartPoints
public import Nyll.SchemeTheory.Normalization.SourceIso
public import Nyll.SchemeTheory.FunctionFields.AffineFunctionFieldNaturality
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Naturality of literal generic-normalization charts

An embedding of generic fields induces the actual normalization-source map.
On each affine base chart it is the spectrum of the restriction of that
embedding to the literal integral closures. The proof retains both the base
map and the dense original field source, so contractions of chart primes
compute the original scheme map.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace EtaleFundamentalGroups

universe u

variable (X : Scheme.{u}) [IsIntegral X]
  {L M : Type u} [Field L] [Field M]
  [Algebra X.functionField L] [Algebra X.functionField M]
  (φ : L →ₐ[X.functionField] M)

/-- A generic field embedding gives the original commutative square over `X`. -/
@[reassoc]
theorem genericExtensionMorphism_map :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.genericExtensionMorphism L =
      X.genericExtensionMorphism M := by
  have h : CommRingCat.ofHom (algebraMap X.functionField L) ≫
      CommRingCat.ofHom φ.toRingHom =
        CommRingCat.ofHom (algebraMap X.functionField M) :=
    CommRingCat.hom_ext φ.comp_algebraMap
  unfold Scheme.genericExtensionMorphism
  rw [← Spec.map_comp_assoc, h]

/-- The actual map of generic normalizations induced by a field embedding. -/
def genericNormalizationFieldMap :
    (X.genericExtensionMorphism M).normalization ⟶
      (X.genericExtensionMorphism L).normalization :=
  Scheme.Hom.normalizationSourceMap
    (X.genericExtensionMorphism M) (X.genericExtensionMorphism L)
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) (genericExtensionMorphism_map X φ)

/-- This map retains the original map to `X`. -/
@[reassoc]
theorem genericNormalizationFieldMap_fromNormalization :
    genericNormalizationFieldMap X φ ≫ (X.genericExtensionMorphism L).fromNormalization =
      (X.genericExtensionMorphism M).fromNormalization :=
  Scheme.Hom.normalizationSourceMap_fromNormalization _ _ _ _

/-- This map retains the original embedding of generic fields. -/
@[reassoc]
theorem toNormalization_genericNormalizationFieldMap :
    (X.genericExtensionMorphism M).toNormalization ≫ genericNormalizationFieldMap X φ =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (X.genericExtensionMorphism L).toNormalization :=
  Scheme.Hom.toNormalization_normalizationSourceMap _ _ _ _

/-- The restriction of the same field embedding to literal affine integral closures. -/
def genericNormalizationChartRingMap (U : X.Opens) [Nonempty U] :
    let := X.affineExtensionAlgebra U L
    let := X.affineExtensionAlgebra U M
    integralClosure Γ(X, U) L →+* integralClosure Γ(X, U) M := by
  let := X.affineExtensionAlgebra U L
  let := X.affineExtensionAlgebra U M
  have : IsScalarTower Γ(X, U) X.functionField L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, U) X.functionField M :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact (φ.restrictScalars Γ(X, U)).mapIntegralClosure.toRingHom

private theorem genericNormalizationChartRingMap_base (U : X.Opens) [Nonempty U] :
    let := X.affineExtensionAlgebra U L
    let := X.affineExtensionAlgebra U M
    (genericNormalizationChartRingMap X φ U).comp
        (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)) =
      algebraMap Γ(X, U) (integralClosure Γ(X, U) M) := by
  let := X.affineExtensionAlgebra U L
  let := X.affineExtensionAlgebra U M
  have : IsScalarTower Γ(X, U) X.functionField L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, U) X.functionField M :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact (φ.restrictScalars Γ(X, U)).mapIntegralClosure.comp_algebraMap

private theorem genericNormalizationChartRingMap_val (U : X.Opens) [Nonempty U] :
    let := X.affineExtensionAlgebra U L
    let := X.affineExtensionAlgebra U M
    (algebraMap (integralClosure Γ(X, U) M) M).comp
        (genericNormalizationChartRingMap X φ U) =
      φ.toRingHom.comp (algebraMap (integralClosure Γ(X, U) L) L) := by
  let := X.affineExtensionAlgebra U L
  let := X.affineExtensionAlgebra U M
  apply RingHom.ext
  intro b
  rfl

/-- On each affine chart, the actual normalization map is the spectrum of
restriction of the original field embedding to integral elements. -/
@[reassoc]
theorem genericNormalizationChart_naturality
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    let := X.affineExtensionAlgebra U L
    let := X.affineExtensionAlgebra U M
    Spec.map (CommRingCat.ofHom (genericNormalizationChartRingMap X φ U)) ≫
        genericNormalizationChart X L U hU =
      genericNormalizationChart X M U hU ≫ genericNormalizationFieldMap X φ := by
  let := X.affineExtensionAlgebra U L
  let := X.affineExtensionAlgebra U M
  let ι : Spec (.of M) ⟶ Spec (.of (integralClosure Γ(X, U) M)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (integralClosure Γ(X, U) M) M))
  have : IsDominant ι :=
    ⟨Scheme.Hom.affineSpecMap_denseRange_of_injective _ Subtype.val_injective⟩
  apply ext_of_isDominant_of_isSeparated
    (X.genericExtensionMorphism L).fromNormalization _ ι
  · change Spec.map (CommRingCat.ofHom
        (algebraMap (integralClosure Γ(X, U) M) M)) ≫
          (Spec.map (CommRingCat.ofHom (genericNormalizationChartRingMap X φ U)) ≫
            genericNormalizationChart X L U hU) = _
    rw [← Spec.map_comp_assoc]
    have h := congrArg CommRingCat.ofHom (genericNormalizationChartRingMap_val X φ U)
    change CommRingCat.ofHom (genericNormalizationChartRingMap X φ U) ≫
        CommRingCat.ofHom (algebraMap (integralClosure Γ(X, U) M) M) =
      CommRingCat.ofHom (algebraMap (integralClosure Γ(X, U) L) L) ≫
        CommRingCat.ofHom φ.toRingHom at h
    rw [h, Spec.map_comp_assoc, spec_val_genericNormalizationChart,
      ← Category.assoc, spec_val_genericNormalizationChart,
      toNormalization_genericNormalizationFieldMap]
  · rw [Category.assoc, genericNormalizationChart_base,
      Category.assoc, genericNormalizationFieldMap_fromNormalization,
      genericNormalizationChart_base, ← Spec.map_comp_assoc]
    have h := congrArg CommRingCat.ofHom (genericNormalizationChartRingMap_base X φ U)
    change CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)) ≫
        CommRingCat.ofHom (genericNormalizationChartRingMap X φ U) =
      CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) M)) at h
    rw [h]

/-- Contraction under the literal coefficient embedding computes the image
of a prime under the original normalization-source map. -/
theorem genericNormalizationChart_comap
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    let := X.affineExtensionAlgebra U L
    let := X.affineExtensionAlgebra U M
    ∀ q : PrimeSpectrum (integralClosure Γ(X, U) M),
      genericNormalizationChart X L U hU
          (q.comap (genericNormalizationChartRingMap X φ U)) =
        genericNormalizationFieldMap X φ (genericNormalizationChart X M U hU q) := by
  intro _ _ q
  exact congrArg (fun f => f q) (genericNormalizationChart_naturality X φ U hU)

end EtaleFundamentalGroups
