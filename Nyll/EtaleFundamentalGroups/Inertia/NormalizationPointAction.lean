/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationPointDecomposition
public import Nyll.SchemeTheory.Normalization.SourceIso

/-!
# The original Galois action on absolute normalization points

Inverse field automorphisms give the left action on the actual topological
points of the absolute normalization. The group laws follow from the
normalization universal property. On each original affine chart its
stabilizer is the literal native decomposition group.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry SchemeTheory

namespace EtaleFundamentalGroups.Inertia

universe u

variable {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (j : U ⟶ X) [IsOpenImmersion j] (Ω : Type u) [Field Ω]
  [Algebra U.functionField Ω]

omit [IsIntegral X] in
private theorem openGenericNormalizationEndomorphism_one :
    openGenericNormalizationEndomorphism j Ω 1 =
      𝟙 (U.genericExtensionMorphism Ω ≫ j).normalization := by
  let f := U.genericExtensionMorphism Ω ≫ j
  dsimp only [openGenericNormalizationEndomorphism]
  apply Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization
  · rw [Category.comp_id,
      Scheme.Hom.toNormalization_normalizationSourceMap]
    change Spec.map (𝟙 (CommRingCat.of Ω)) ≫ f.toNormalization = f.toNormalization
    rw [Spec.map_id, Category.id_comp]
  · exact Scheme.Hom.normalizationSourceMap_fromNormalization f f _ _
  · exact Category.id_comp _

omit [IsIntegral X] in
private theorem openGenericNormalizationEndomorphism_mul
    (σ τ : Gal(Ω/U.functionField)) :
    openGenericNormalizationEndomorphism j Ω (σ * τ) =
      openGenericNormalizationEndomorphism j Ω σ ≫
        openGenericNormalizationEndomorphism j Ω τ := by
  let f := U.genericExtensionMorphism Ω ≫ j
  have hspec : Spec.map (CommRingCat.ofHom (σ * τ).toRingHom) =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom τ.toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  dsimp only [openGenericNormalizationEndomorphism]
  apply Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization
  · rw [← Category.assoc,
      Scheme.Hom.toNormalization_normalizationSourceMap,
      Scheme.Hom.toNormalization_normalizationSourceMap,
      Category.assoc, Scheme.Hom.toNormalization_normalizationSourceMap,
      hspec, Category.assoc]
  · exact Scheme.Hom.normalizationSourceMap_fromNormalization f f _ _
  · rw [Category.assoc,
      Scheme.Hom.normalizationSourceMap_fromNormalization,
      Scheme.Hom.normalizationSourceMap_fromNormalization]

/-- The original absolute Galois group acts on the actual normalization
points. The inverse compensates for the contravariance of spectrum. -/
@[instance_reducible]
def openGenericNormalizationPointAction :
    MulAction Gal(Ω/U.functionField) (U.genericExtensionMorphism Ω ≫ j).normalization where
  smul σ z := openGenericNormalizationEndomorphism j Ω σ⁻¹ z
  one_smul z := by
    change openGenericNormalizationEndomorphism j Ω (1 : Gal(Ω/U.functionField))⁻¹ z = z
    rw [inv_one, openGenericNormalizationEndomorphism_one]
    rfl
  mul_smul σ τ z := by
    change openGenericNormalizationEndomorphism j Ω (σ * τ)⁻¹ z =
      openGenericNormalizationEndomorphism j Ω σ⁻¹
        (openGenericNormalizationEndomorphism j Ω τ⁻¹ z)
    rw [mul_inv_rev, openGenericNormalizationEndomorphism_mul]
    rfl

omit [IsIntegral X] in
/-- The original normalization action stays over the same original base point. -/
theorem openGenericNormalizationPointAction_base
    (σ : Gal(Ω/U.functionField))
    (z : (U.genericExtensionMorphism Ω ≫ j).normalization) :
    let _ := openGenericNormalizationPointAction j Ω
    (U.genericExtensionMorphism Ω ≫ j).fromNormalization (σ • z) =
      (U.genericExtensionMorphism Ω ≫ j).fromNormalization z := by
  intro action
  exact congrArg (fun h => h z)
    (Scheme.Hom.normalizationSourceMap_fromNormalization
      (U.genericExtensionMorphism Ω ≫ j) (U.genericExtensionMorphism Ω ≫ j)
      (Spec.map (CommRingCat.ofHom (σ⁻¹).toRingHom))
      (by rw [← Category.assoc, genericExtensionMorphism_specMap_algEquiv U Ω (σ⁻¹)]))

variable [Algebra.IsAlgebraic U.functionField Ω]

/-- In an original affine chart, the stabilizer of the actual normalization
point equals the image of the original native decomposition inclusion. -/
theorem openGenericNormalizationPointAction_stabilizer
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    let : Algebra Γ(X, V) U.functionField :=
      j.functionFieldAlgebraOfIsOpenImmersionAffine V
    let : IsFractionRing Γ(X, V) U.functionField :=
      j.functionField_isFractionRing_of_isOpenImmersionAffine V hV
    let : Algebra X.functionField Ω :=
      ((algebraMap U.functionField Ω).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let : Algebra Γ(X, V) Ω := X.affineExtensionAlgebra V Ω
    let : IsScalarTower Γ(X, V) U.functionField Ω :=
      j.functionField_isScalarTower_of_isOpenImmersionAffine V Ω
    let _ := openGenericNormalizationPointAction j Ω
    ∀ Q : PrimeSpectrum (normalizationCommAlgCat Γ(X, V) Ω),
      MulAction.stabilizer Gal(Ω/U.functionField)
        (openGenericNormalizationChart j Ω V hV Q) =
      (normalizationDecompositionInclusion Γ(X, V) U.functionField Ω Q.asIdeal).range := by
  intro instAF instFrac instXΩ instAΩ instTower action Q
  ext σ
  change openGenericNormalizationEndomorphism j Ω σ⁻¹
      (openGenericNormalizationChart j Ω V hV Q) =
        openGenericNormalizationChart j Ω V hV Q ↔ _
  rw [openGenericNormalizationChart_fixed_iff_decomposition,
    Subgroup.inv_mem_iff]

end EtaleFundamentalGroups.Inertia
