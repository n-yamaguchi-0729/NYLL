/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.AbsoluteCompactificationPoint
public import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedRestriction
public import Nyll.SchemeTheory.Normalization.GenericChartNaturality
public import Nyll.SchemeTheory.Normalization.OpenGenericExtension
public import Nyll.EtaleFundamentalGroups.Purity.ConnectedCoverGenericNormalizationFinite

/-!
# Literal charts of pointed connected-cover compactifications

The compactification attached to a connected finite étale cover is identified
with the ambient generic normalization using the identity on its original
function-field spectrum. Its affine charts are therefore the literal integral
closures. For a specified geometric generic point, restriction of its actual
field embedding computes the original map from the absolute normalization.
In particular, contraction computes the image of the same normalization prime.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory TopologicalSpace
open EtaleFundamentalGroups

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] connectedLeftIntegral

variable {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  [IsNormalIntegral U] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j] (W : FiniteEtale U) [IsConnected W]

/-- The actual finite-cover compactification, identified using its unchanged
original function-field spectrum. -/
def connectedCoverAmbientNormalizationIso :
    let : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let : Algebra X.functionField W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    (X.genericExtensionMorphism W.left.functionField).normalization ≅
      (connectedCoverGenericComposite W ≫ j).normalization := by
  intro _ _
  exact Scheme.Hom.normalizationSourceIso
    (X.genericExtensionMorphism W.left.functionField)
    (connectedCoverGenericComposite W ≫ j) (Iso.refl _) (by
      rw [Iso.refl_hom, Category.id_comp]
      exact (genericExtensionMorphism_eq_connectedCoverGenericComposite_comp j W).symm)

/-- The identification preserves the original structural map to the ambient scheme. -/
@[reassoc]
theorem connectedCoverAmbientNormalizationIso_hom_fromNormalization :
    let : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let : Algebra X.functionField W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    (connectedCoverAmbientNormalizationIso j W).hom ≫
        (connectedCoverGenericComposite W ≫ j).fromNormalization =
      (X.genericExtensionMorphism W.left.functionField).fromNormalization := by
  intro _ _
  exact Scheme.Hom.normalizationSourceIso_hom_fromNormalization _ _ _ _

/-- The identification preserves the literal original generic source. -/
@[reassoc]
theorem toNormalization_connectedCoverAmbientNormalizationIso_hom :
    let : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let : Algebra X.functionField W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    (X.genericExtensionMorphism W.left.functionField).toNormalization ≫
        (connectedCoverAmbientNormalizationIso j W).hom =
      (connectedCoverGenericComposite W ≫ j).toNormalization := by
  intro _ _
  exact (Scheme.Hom.toNormalization_normalizationSourceIso_hom _ _ _ _).trans
    (Category.id_comp _)

/-- A literal integral-closure chart on the original cover compactification. -/
def connectedCoverCompactificationChart (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    let : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let : Algebra X.functionField W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let := X.affineExtensionAlgebra V W.left.functionField
    Spec (.of (integralClosure Γ(X, V) W.left.functionField)) ⟶
      (connectedCoverGenericComposite W ≫ j).normalization := by
  intro _ _ _
  exact genericNormalizationChart X W.left.functionField V hV ≫
    (connectedCoverAmbientNormalizationIso j W).hom

/-- The literal finite-cover chart is an open immersion. -/
instance connectedCoverCompactificationChart_isOpenImmersion
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    IsOpenImmersion (connectedCoverCompactificationChart j W V hV) := by
  let : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
  let : Algebra X.functionField W.left.functionField :=
    ((algebraMap U.functionField W.left.functionField).comp
      j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
  exact inferInstanceAs (IsOpenImmersion
    (genericNormalizationChart X W.left.functionField V hV ≫
      (connectedCoverAmbientNormalizationIso j W).hom))

/-- The literal chart retains the original coefficient map to the affine base. -/
@[reassoc]
theorem connectedCoverCompactificationChart_base
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    let : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let : Algebra X.functionField W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let := X.affineExtensionAlgebra V W.left.functionField
    connectedCoverCompactificationChart j W V hV ≫
        (connectedCoverGenericComposite W ≫ j).fromNormalization =
      Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, V) (integralClosure Γ(X, V) W.left.functionField))) ≫
          hV.fromSpec := by
  intro _ _ _
  change (genericNormalizationChart X W.left.functionField V hV ≫
    (connectedCoverAmbientNormalizationIso j W).hom) ≫ _ = _
  rw [Category.assoc, connectedCoverAmbientNormalizationIso_hom_fromNormalization,
    genericNormalizationChart_base]

/-- The literal chart also retains the original function-field source. -/
@[reassoc]
theorem spec_val_connectedCoverCompactificationChart
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    let : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let : Algebra X.functionField W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let := X.affineExtensionAlgebra V W.left.functionField
    Spec.map (CommRingCat.ofHom
        (algebraMap (integralClosure Γ(X, V) W.left.functionField) W.left.functionField)) ≫
      connectedCoverCompactificationChart j W V hV =
        (connectedCoverGenericComposite W ≫ j).toNormalization := by
  intro _ _ _
  change _ ≫ (genericNormalizationChart X W.left.functionField V hV ≫
    (connectedCoverAmbientNormalizationIso j W).hom) = _
  rw [← Category.assoc, spec_val_genericNormalizationChart,
    toNormalization_connectedCoverAmbientNormalizationIso_hom]

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra U.functionField Ω]
  (w : (fiber (U.genericExtensionMorphism Ω)).obj W)

/-- The specified generic fiber point supplies the original field embedding,
viewed over the ambient function field through the open immersion. -/
def connectedCoverAmbientFieldEmbedding :
    let : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let : Algebra X.functionField W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let : Algebra X.functionField Ω :=
      ((algebraMap U.functionField Ω).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    W.left.functionField →ₐ[X.functionField] Ω := by
  intro _ _ _
  let β := finiteEtaleGenericHomFunctionFieldAlgHom W
    (fiberObjEquivHom (U.genericExtensionMorphism Ω) W w)
  exact
    { β.toRingHom with
      commutes' := by
        intro a
        exact β.commutes (j.functionFieldRingEquivOfIsOpenImmersion a) }

/-- The original absolute-normalization map agrees with the map of generic
normalizations induced by the specified original field embedding. -/
theorem connectedCoverAbsoluteNormalizationMap_ambient :
    let : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let : Algebra X.functionField W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let : Algebra X.functionField Ω :=
      ((algebraMap U.functionField Ω).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    genericNormalizationFieldMap X (connectedCoverAmbientFieldEmbedding j W Ω w) ≫
        (connectedCoverAmbientNormalizationIso j W).hom =
      (genericExtensionNormalizationOpenIso j Ω).hom ≫
        connectedCoverAbsoluteNormalizationMap Ω j W w := by
  intro _ _ _
  apply Scheme.Hom.normalization.hom_ext (X.genericExtensionMorphism Ω)
    _ _ (connectedCoverGenericComposite W ≫ j).fromNormalization
  · rw [← Category.assoc, toNormalization_genericNormalizationFieldMap,
      Category.assoc, toNormalization_connectedCoverAmbientNormalizationIso_hom,
      ← Category.assoc, toNormalization_genericExtensionNormalizationOpenIso_hom,
      toNormalization_connectedCoverAbsoluteNormalizationMap]
    rfl
  · rw [Category.assoc, connectedCoverAmbientNormalizationIso_hom_fromNormalization,
      genericNormalizationFieldMap_fromNormalization]
  · rw [Category.assoc, connectedCoverAbsoluteNormalizationMap_fromNormalization,
      genericExtensionNormalizationOpenIso_hom_fromNormalization]

/-- On literal affine integral closures, the original absolute-normalization
map is exactly the spectrum of restriction of the original field embedding. -/
@[reassoc]
theorem connectedCoverCompactificationChart_naturality
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    let : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let : Algebra X.functionField W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let : Algebra X.functionField Ω :=
      ((algebraMap U.functionField Ω).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let := X.affineExtensionAlgebra V W.left.functionField
    let := X.affineExtensionAlgebra V Ω
    Spec.map (CommRingCat.ofHom (genericNormalizationChartRingMap X
        (connectedCoverAmbientFieldEmbedding j W Ω w) V)) ≫
      connectedCoverCompactificationChart j W V hV =
        openGenericNormalizationChart j Ω V hV ≫
          connectedCoverAbsoluteNormalizationMap Ω j W w := by
  intro _ _ _ _ _
  change _ ≫ (genericNormalizationChart X W.left.functionField V hV ≫
      (connectedCoverAmbientNormalizationIso j W).hom) =
    (genericNormalizationChart X Ω V hV ≫
      (genericExtensionNormalizationOpenIso j Ω).hom) ≫ _
  rw [← Category.assoc, genericNormalizationChart_naturality,
    Category.assoc, connectedCoverAbsoluteNormalizationMap_ambient, ← Category.assoc]

/-- Contraction of the same absolute-normalization prime computes its image
in the original pointed finite-cover compactification. -/
theorem connectedCoverCompactificationChart_comap
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    let : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let : Algebra X.functionField W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let : Algebra X.functionField Ω :=
      ((algebraMap U.functionField Ω).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let := X.affineExtensionAlgebra V W.left.functionField
    let := X.affineExtensionAlgebra V Ω
    ∀ Q : PrimeSpectrum (integralClosure Γ(X, V) Ω),
      connectedCoverCompactificationChart j W V hV
        (Q.comap (genericNormalizationChartRingMap X
          (connectedCoverAmbientFieldEmbedding j W Ω w) V)) =
        connectedCoverAbsoluteNormalizationMap Ω j W w
          (openGenericNormalizationChart j Ω V hV Q) := by
  intro _ _ _ _ _ Q
  exact congrArg (fun f => f Q)
    (connectedCoverCompactificationChart_naturality j W Ω w V hV)

end AlgebraicGeometry.FiniteEtale
