/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Normalization.GenericChartPoints
public import Nyll.SchemeTheory.FunctionFields.OpenImmersion
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
public import Nyll.SchemeTheory.Normalization.FiniteSeparable
public import Nyll.SchemeTheory.Normalization.SourceIso

/-!
# Generic normalization through a dense open immersion

The function-field equivalence of an integral open subscheme supplies the
ambient algebra structure on every generic extension. Its generic morphism
is the literal composite through that open. The induced normalization
isomorphism preserves both the original generic source and the map to the
ambient scheme.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace EtaleFundamentalGroups

universe u

variable {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (j : U ⟶ X) [IsOpenImmersion j] (L : Type u) [Field L]
  [Algebra U.functionField L]

/-- The actual generic extension agrees with its original composite through
the open subscheme, for the induced ambient function-field algebra. -/
theorem genericExtensionMorphism_eq_comp_openImmersion :
    let : Algebra X.functionField L :=
      ((algebraMap U.functionField L).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    X.genericExtensionMorphism L = U.genericExtensionMorphism L ≫ j := by
  intro _
  have hj : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  have he : j.functionFieldRingEquivOfIsOpenImmersion.toRingHom =
      j.functionFieldMap hj := by
    apply RingHom.ext
    intro a
    exact j.functionFieldRingEquivOfIsOpenImmersion_apply a
  have hgeneric :
      Spec.map (CommRingCat.ofHom
          j.functionFieldRingEquivOfIsOpenImmersion.toRingHom) ≫
        X.fromSpecStalk (genericPoint X) =
      U.fromSpecStalk (genericPoint U) ≫ j := by
    rw [he]
    exact Spec_functionFieldMap_fromSpecStalk j hj
  have hring : CommRingCat.ofHom (algebraMap X.functionField L) =
      CommRingCat.ofHom j.functionFieldRingEquivOfIsOpenImmersion.toRingHom ≫
        CommRingCat.ofHom (algebraMap U.functionField L) := rfl
  unfold Scheme.genericExtensionMorphism
  rw [hring, Spec.map_comp, Category.assoc, hgeneric, Category.assoc]

/-- The actual normalizations are canonically identified using the identity
on their common original field spectrum. -/
def genericExtensionNormalizationOpenIso :
    let : Algebra X.functionField L :=
      ((algebraMap U.functionField L).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    (X.genericExtensionMorphism L).normalization ≅
      (U.genericExtensionMorphism L ≫ j).normalization := by
  intro extensionAlgebra
  exact Scheme.Hom.normalizationSourceIso (X.genericExtensionMorphism L)
    (U.genericExtensionMorphism L ≫ j) (Iso.refl _) (by
      rw [Iso.refl_hom, Category.id_comp]
      exact (genericExtensionMorphism_eq_comp_openImmersion j L).symm)

/-- The identification retains the original structure map to the ambient scheme. -/
@[reassoc]
theorem genericExtensionNormalizationOpenIso_hom_fromNormalization :
    let : Algebra X.functionField L :=
      ((algebraMap U.functionField L).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    (genericExtensionNormalizationOpenIso j L).hom ≫
        (U.genericExtensionMorphism L ≫ j).fromNormalization =
      (X.genericExtensionMorphism L).fromNormalization := by
  intro extensionAlgebra
  exact Scheme.Hom.normalizationSourceIso_hom_fromNormalization _ _ _ _

/-- The identification also retains the literal original field source. -/
@[reassoc]
theorem toNormalization_genericExtensionNormalizationOpenIso_hom :
    let : Algebra X.functionField L :=
      ((algebraMap U.functionField L).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    (X.genericExtensionMorphism L).toNormalization ≫
        (genericExtensionNormalizationOpenIso j L).hom =
      (U.genericExtensionMorphism L ≫ j).toNormalization := by
  intro extensionAlgebra
  exact (Scheme.Hom.toNormalization_normalizationSourceIso_hom _ _ _ _).trans
    (Category.id_comp _)

/-- The literal integral-closure chart on the original normalization of the
composite through the open subscheme. -/
def openGenericNormalizationChart
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    let : Algebra X.functionField L :=
      ((algebraMap U.functionField L).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let := X.affineExtensionAlgebra V L
    Spec (.of (integralClosure Γ(X, V) L)) ⟶
      (U.genericExtensionMorphism L ≫ j).normalization := by
  intro _ _
  exact genericNormalizationChart X L V hV ≫
    (genericExtensionNormalizationOpenIso j L).hom

/-- The actual composite-normalization chart is an open immersion. -/
instance openGenericNormalizationChart_isOpenImmersion
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    IsOpenImmersion (openGenericNormalizationChart j L V hV) := by
  let : Algebra X.functionField L :=
    ((algebraMap U.functionField L).comp
      j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
  exact inferInstanceAs (IsOpenImmersion (genericNormalizationChart X L V hV ≫
    (genericExtensionNormalizationOpenIso j L).hom))

/-- The original chart retains the affine integral-closure structure map. -/
@[reassoc]
theorem openGenericNormalizationChart_base
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    let : Algebra X.functionField L :=
      ((algebraMap U.functionField L).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let := X.affineExtensionAlgebra V L
    openGenericNormalizationChart j L V hV ≫
        (U.genericExtensionMorphism L ≫ j).fromNormalization =
      Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, V) (integralClosure Γ(X, V) L))) ≫ hV.fromSpec := by
  intro _ _
  change (genericNormalizationChart X L V hV ≫
    (genericExtensionNormalizationOpenIso j L).hom) ≫ _ = _
  rw [Category.assoc, genericExtensionNormalizationOpenIso_hom_fromNormalization,
    genericNormalizationChart_base]

/-- The same chart retains the literal original generic source. -/
@[reassoc]
theorem spec_val_openGenericNormalizationChart
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    let : Algebra X.functionField L :=
      ((algebraMap U.functionField L).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let := X.affineExtensionAlgebra V L
    Spec.map (CommRingCat.ofHom (algebraMap (integralClosure Γ(X, V) L) L)) ≫
        openGenericNormalizationChart j L V hV =
      (U.genericExtensionMorphism L ≫ j).toNormalization := by
  intro _ _
  change _ ≫ (genericNormalizationChart X L V hV ≫
    (genericExtensionNormalizationOpenIso j L).hom) = _
  rw [← Category.assoc, spec_val_genericNormalizationChart,
    toNormalization_genericExtensionNormalizationOpenIso_hom]

/-- The original affine coefficient map followed by the original affine
chart is exactly the generic extension through the given open subscheme. -/
@[reassoc]
theorem spec_algebraMap_openGenericNormalizationChart_fromSpec
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    let : Algebra X.functionField L :=
      ((algebraMap U.functionField L).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let := X.affineExtensionAlgebra V L
    Spec.algebraMap Γ(X, V) L ≫ hV.fromSpec = U.genericExtensionMorphism L ≫ j := by
  intro instXL instAL
  let B := integralClosure Γ(X, V) L
  have hcoeff : Spec.algebraMap Γ(X, V) L =
      Spec.algebraMap B L ≫ Spec.algebraMap Γ(X, V) B := by
    rw [← Spec.map_comp]
    rfl
  rw [hcoeff, Category.assoc, ← openGenericNormalizationChart_base,
    ← Category.assoc, spec_val_openGenericNormalizationChart,
    Scheme.Hom.toNormalization_fromNormalization]

/-- A point of the original composite normalization gives a prime in the
literal affine integral closure, with its exact original base contraction. -/
theorem exists_openGenericNormalizationChart_point
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V]
    (z : (U.genericExtensionMorphism L ≫ j).normalization)
    (hz : (U.genericExtensionMorphism L ≫ j).fromNormalization z ∈ V) :
    let : Algebra X.functionField L :=
      ((algebraMap U.functionField L).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let := X.affineExtensionAlgebra V L
    ∃ q : PrimeSpectrum (integralClosure Γ(X, V) L),
      openGenericNormalizationChart j L V hV q = z ∧
      q.comap (algebraMap Γ(X, V) (integralClosure Γ(X, V) L)) =
        hV.primeIdealOf ⟨(U.genericExtensionMorphism L ≫ j).fromNormalization z, hz⟩ := by
  intro _ _
  let e := genericExtensionNormalizationOpenIso j L
  have he : e.inv ≫ (X.genericExtensionMorphism L).fromNormalization =
      (U.genericExtensionMorphism L ≫ j).fromNormalization := by
    rw [← genericExtensionNormalizationOpenIso_hom_fromNormalization j L]
    exact e.inv_hom_id_assoc _
  have hz' : (X.genericExtensionMorphism L).fromNormalization (e.inv z) ∈ V := by
    have h := congrArg (fun f => f z) he
    exact h.symm ▸ hz
  obtain ⟨q, hq, -⟩ := exists_genericNormalizationChart_point X L V hV (e.inv z) hz'
  have hq' : openGenericNormalizationChart j L V hV q = z := by
    change e.hom (genericNormalizationChart X L V hV q) = z
    rw [hq]
    exact congrArg (fun f : (U.genericExtensionMorphism L ≫ j).normalization ⟶
      (U.genericExtensionMorphism L ≫ j).normalization => f z) e.inv_hom_id
  refine ⟨q, hq', ?_⟩
  apply hV.fromSpec.isOpenEmbedding.injective
  change (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, V) (integralClosure Γ(X, V) L))) ≫ hV.fromSpec) q = _
  rw [← openGenericNormalizationChart_base]
  change (U.genericExtensionMorphism L ≫ j).fromNormalization
    (openGenericNormalizationChart j L V hV q) = _
  rw [hq', IsAffineOpen.fromSpec_primeIdealOf]

/-- A closed base point gives a maximal prime in this same original chart. -/
theorem exists_openGenericNormalizationChart_maximalPoint
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V]
    (z : (U.genericExtensionMorphism L ≫ j).normalization)
    (hz : (U.genericExtensionMorphism L ≫ j).fromNormalization z ∈ V)
    (hclosed : IsClosed {(U.genericExtensionMorphism L ≫ j).fromNormalization z}) :
    let : Algebra X.functionField L :=
      ((algebraMap U.functionField L).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let := X.affineExtensionAlgebra V L
    ∃ q : PrimeSpectrum (integralClosure Γ(X, V) L),
      openGenericNormalizationChart j L V hV q = z ∧
      q.comap (algebraMap Γ(X, V) (integralClosure Γ(X, V) L)) =
        hV.primeIdealOf ⟨(U.genericExtensionMorphism L ≫ j).fromNormalization z, hz⟩ ∧
      q.asIdeal.IsMaximal := by
  intro _ _
  obtain ⟨q, hq, hbase⟩ := exists_openGenericNormalizationChart_point j L V hV z hz
  refine ⟨q, hq, hbase, ?_⟩
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Γ(X, V)) q.asIdeal
  have hunder : q.asIdeal.under Γ(X, V) =
      (hV.primeIdealOf
        ⟨(U.genericExtensionMorphism L ≫ j).fromNormalization z, hz⟩).asIdeal :=
    congrArg PrimeSpectrum.asIdeal hbase
  rw [hunder]
  exact hV.primeIdealOf_isMaximal_of_isClosed
    ⟨(U.genericExtensionMorphism L ≫ j).fromNormalization z, hz⟩ hclosed

end EtaleFundamentalGroups
