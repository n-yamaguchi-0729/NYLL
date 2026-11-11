/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Normalization.GenericNormalizationChartAction
public import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence
public import Nyll.SchemeTheory.FunctionFields.OpenAffineFractionField
public import Nyll.SchemeTheory.Normalization.OpenGenericExtension

/-!
# Actual normalization points and their native decomposition groups

The existing generic-chart action compares the actual global normalization
endomorphism with the restriction of the original field automorphism. Since
the chart is an open immersion, fixing its topological point is precisely
membership in the original native decomposition group at its literal prime.
The open-subscheme version keeps the original open function field throughout.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry SchemeTheory
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] normalizationCommAlgGaloisAction

private theorem normalizationPrime_comap_eq_iff_decomposition
    (A F Ω : Type u) [CommRing A] [Field F] [Field Ω]
    [Algebra A F] [IsFractionRing A F] [Algebra F Ω] [Algebra A Ω]
    [IsScalarTower A F Ω] [Algebra.IsAlgebraic F Ω]
    (Q : PrimeSpectrum (normalizationCommAlgCat A Ω)) (σ : Gal(Ω/F)) :
    PrimeSpectrum.comap (σ.restrictScalars A).mapIntegralClosure.toRingHom Q = Q ↔
      σ ∈ (normalizationDecompositionInclusion A F Ω Q.asIdeal).range := by
  let r : normalizationCommAlgCat A Ω →+* normalizationCommAlgCat A Ω :=
    (σ.restrictScalars A).mapIntegralClosure.toRingHom
  change PrimeSpectrum.comap r Q = Q ↔ _
  have hcoeff (b : normalizationCommAlgCat A Ω) :
      r b = σ • b := by
    apply Subtype.ext
    exact congrArg (fun f : normalizationCommAlgCat A Ω →+* Ω => f b)
      (normalizationCommAlg_action_comp_inclusion A F Ω σ)
  have hcomap :
      Q.asIdeal.comap r = σ⁻¹ • Q.asIdeal := by
    apply Ideal.ext
    intro b
    change r b ∈ Q.asIdeal ↔ b ∈ σ⁻¹ • Q.asIdeal
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, hcoeff]
  constructor
  · intro h
    have hideal := congrArg PrimeSpectrum.asIdeal h
    have hinv : σ⁻¹ ∈ MulAction.stabilizer Gal(Ω/F) Q.asIdeal := by
      apply MulAction.mem_stabilizer_iff.mpr
      exact hcomap.symm.trans hideal
    exact ⟨⟨σ, (Subgroup.inv_mem_iff _).mp hinv⟩, rfl⟩
  · rintro ⟨d, rfl⟩
    apply PrimeSpectrum.ext
    exact hcomap.trans ((MulAction.mem_stabilizer_iff).mp
      ((MulAction.stabilizer Gal(Ω/F) Q.asIdeal).inv_mem d.property))

section Generic

variable (X : Scheme.{u}) [IsIntegral X] (Ω : Type u) [Field Ω]
  [Algebra X.functionField Ω] [Algebra.IsAlgebraic X.functionField Ω]

/-- The actual global normalization point is fixed exactly by its original
native affine decomposition group. -/
theorem genericNormalizationChart_fixed_iff_decomposition
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    let : IsFractionRing Γ(X, V) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X V hV
    let : Algebra Γ(X, V) Ω := X.affineExtensionAlgebra V Ω
    let : IsScalarTower Γ(X, V) X.functionField Ω :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∀ (Q : PrimeSpectrum (normalizationCommAlgCat Γ(X, V) Ω))
      (σ : Gal(Ω/X.functionField)),
      Scheme.Hom.normalizationSourceMap (X.genericExtensionMorphism Ω)
          (X.genericExtensionMorphism Ω) (Spec.map (CommRingCat.ofHom σ.toRingHom))
          (genericExtensionMorphism_specMap_algEquiv X Ω σ)
          (genericNormalizationChart X Ω V hV Q) =
        genericNormalizationChart X Ω V hV Q ↔
      σ ∈ (normalizationDecompositionInclusion Γ(X, V) X.functionField Ω Q.asIdeal).range := by
  intro instFrac instAΩ instTower Q σ
  have h := congrArg
    (fun f : Spec (.of (integralClosure Γ(X, V) Ω)) ⟶
        (X.genericExtensionMorphism Ω).normalization => f Q)
    (genericNormalizationChart_endomorphism X Ω V hV σ)
  change genericNormalizationChart X Ω V hV
      (PrimeSpectrum.comap (σ.restrictScalars Γ(X, V)).mapIntegralClosure.toRingHom Q) =
    Scheme.Hom.normalizationSourceMap (X.genericExtensionMorphism Ω)
      (X.genericExtensionMorphism Ω) (Spec.map (CommRingCat.ofHom σ.toRingHom))
      (genericExtensionMorphism_specMap_algEquiv X Ω σ)
      (genericNormalizationChart X Ω V hV Q) at h
  rw [← h]
  exact (genericNormalizationChart X Ω V hV).isOpenEmbedding.injective.eq_iff.trans
    (normalizationPrime_comap_eq_iff_decomposition Γ(X, V) X.functionField Ω Q σ)

end Generic

section Open

variable {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (j : U ⟶ X) [IsOpenImmersion j] (Ω : Type u) [Field Ω]
  [Algebra U.functionField Ω]

/-- The original open-function-field automorphism induces its actual
endomorphism of the normalization over the ambient scheme. -/
def openGenericNormalizationEndomorphism (σ : Gal(Ω/U.functionField)) :
    (U.genericExtensionMorphism Ω ≫ j).normalization ⟶
      (U.genericExtensionMorphism Ω ≫ j).normalization :=
  Scheme.Hom.normalizationSourceMap (U.genericExtensionMorphism Ω ≫ j)
    (U.genericExtensionMorphism Ω ≫ j) (Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
      rw [← Category.assoc, genericExtensionMorphism_specMap_algEquiv U Ω σ])

/-- The actual open normalization chart intertwines the original field
automorphism and its original global normalization endomorphism. -/
@[reassoc]
theorem openGenericNormalizationChart_endomorphism
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    let : Algebra Γ(X, V) U.functionField :=
      j.functionFieldAlgebraOfIsOpenImmersionAffine V
    let : Algebra X.functionField Ω :=
      ((algebraMap U.functionField Ω).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let : Algebra Γ(X, V) Ω := X.affineExtensionAlgebra V Ω
    let : IsScalarTower Γ(X, V) U.functionField Ω :=
      j.functionField_isScalarTower_of_isOpenImmersionAffine V Ω
    ∀ σ : Gal(Ω/U.functionField),
      Spec.map (CommRingCat.ofHom
          (σ.restrictScalars Γ(X, V)).mapIntegralClosure.toRingHom) ≫
          openGenericNormalizationChart j Ω V hV =
        openGenericNormalizationChart j Ω V hV ≫ openGenericNormalizationEndomorphism j Ω σ := by
  intro instAF instXΩ instAΩ instTower σ
  have : IsScalarTower Γ(X, V) X.functionField Ω := IsScalarTower.of_algebraMap_eq' rfl
  let τ : Gal(Ω/X.functionField) :=
    { σ.toRingEquiv with
      commutes' := fun a => σ.commutes (j.functionFieldRingEquivOfIsOpenImmersion a) }
  let f := X.genericExtensionMorphism Ω
  let g := U.genericExtensionMorphism Ω ≫ j
  let e := genericExtensionNormalizationOpenIso j Ω
  let q := Scheme.Hom.normalizationSourceMap f f
    (Spec.map (CommRingCat.ofHom τ.toRingHom))
    (genericExtensionMorphism_specMap_algEquiv X Ω τ)
  have he : f.toNormalization ≫ e.hom = g.toNormalization :=
    toNormalization_genericExtensionNormalizationOpenIso_hom j Ω
  have hq : f.toNormalization ≫ q =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ f.toNormalization :=
    Scheme.Hom.toNormalization_normalizationSourceMap f f _ _
  have hq' : g.toNormalization ≫ openGenericNormalizationEndomorphism j Ω σ =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ g.toNormalization :=
    Scheme.Hom.toNormalization_normalizationSourceMap g g _ _
  have hnat : q ≫ e.hom = e.hom ≫ openGenericNormalizationEndomorphism j Ω σ := by
    apply Scheme.Hom.normalization.hom_ext f _ _ g.fromNormalization
    · calc
        f.toNormalization ≫ (q ≫ e.hom) = (f.toNormalization ≫ q) ≫ e.hom :=
          (Category.assoc _ _ _).symm
        _ = (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ f.toNormalization) ≫ e.hom :=
          congrArg (fun h => h ≫ e.hom) hq
        _ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ g.toNormalization := by
          rw [Category.assoc, he]
        _ = g.toNormalization ≫ openGenericNormalizationEndomorphism j Ω σ := hq'.symm
        _ = (f.toNormalization ≫ e.hom) ≫ openGenericNormalizationEndomorphism j Ω σ :=
          congrArg (fun h => h ≫ openGenericNormalizationEndomorphism j Ω σ) he.symm
        _ = f.toNormalization ≫ (e.hom ≫ openGenericNormalizationEndomorphism j Ω σ) :=
          Category.assoc _ _ _
    · dsimp only [q]
      rw [Category.assoc, genericExtensionNormalizationOpenIso_hom_fromNormalization,
        Scheme.Hom.normalizationSourceMap_fromNormalization]
    · dsimp only [openGenericNormalizationEndomorphism]
      rw [Category.assoc, Scheme.Hom.normalizationSourceMap_fromNormalization,
        genericExtensionNormalizationOpenIso_hom_fromNormalization]
  have hchart :
      Spec.map (CommRingCat.ofHom
          (σ.restrictScalars Γ(X, V)).mapIntegralClosure.toRingHom) ≫
          genericNormalizationChart X Ω V hV =
        genericNormalizationChart X Ω V hV ≫ q :=
    genericNormalizationChart_endomorphism X Ω V hV τ
  change _ ≫ (genericNormalizationChart X Ω V hV ≫ e.hom) =
    (genericNormalizationChart X Ω V hV ≫ e.hom) ≫ _
  rw [← Category.assoc, hchart, Category.assoc, hnat, ← Category.assoc]

variable [Algebra.IsAlgebraic U.functionField Ω]

/-- On the original open normalization, topological fixedness is exactly
membership in the native decomposition group of the same literal affine prime.
All coefficient structures are those used by the original geometricity predicate. -/
theorem openGenericNormalizationChart_fixed_iff_decomposition
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
    ∀ (Q : PrimeSpectrum (normalizationCommAlgCat Γ(X, V) Ω))
      (σ : Gal(Ω/U.functionField)),
      openGenericNormalizationEndomorphism j Ω σ
          (openGenericNormalizationChart j Ω V hV Q) =
        openGenericNormalizationChart j Ω V hV Q ↔
      σ ∈ (normalizationDecompositionInclusion Γ(X, V) U.functionField Ω Q.asIdeal).range := by
  intro instAF instFrac instXΩ instAΩ instTower Q σ
  have h := congrArg
    (fun f : Spec (.of (integralClosure Γ(X, V) Ω)) ⟶
        (U.genericExtensionMorphism Ω ≫ j).normalization => f Q)
    (openGenericNormalizationChart_endomorphism j Ω V hV σ)
  change openGenericNormalizationChart j Ω V hV
      (PrimeSpectrum.comap (σ.restrictScalars Γ(X, V)).mapIntegralClosure.toRingHom Q) =
    openGenericNormalizationEndomorphism j Ω σ
      (openGenericNormalizationChart j Ω V hV Q) at h
  rw [← h]
  exact (openGenericNormalizationChart j Ω V hV).isOpenEmbedding.injective.eq_iff.trans
    (normalizationPrime_comap_eq_iff_decomposition Γ(X, V) U.functionField Ω Q σ)

end Open

end EtaleFundamentalGroups.Inertia
