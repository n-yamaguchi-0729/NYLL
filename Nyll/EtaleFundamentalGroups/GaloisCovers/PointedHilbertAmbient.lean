/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.PointedHilbertClassField
public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange

/-!
# Pointed Hilbert containment in the original ambient field

The original embedding of a pointed abelian cover restricts to an embedding
of the base function field. Its generic point and structural coefficients
are unchanged by this restriction. The cover lies in the actual pointed
Hilbert field inside any ambient field: normality compares its original
image with an embedding through that Hilbert field.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicCurve FunctionField TopologicalSpace

namespace EtaleFundamentalGroups

/-- Restricting the actual covering-field embedding preserves its literal
generic point over the original curve. -/
theorem finiteEtaleFunctionFieldEmbedding_restrict_generic
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (Y : FiniteEtale X) [IsConnected Y]
    {Ω : Type u} [Field Ω] :
    let _ : IsIntegral Y.left := coverIntegral Y
    let _ : Algebra X.functionField Y.left.functionField := coverFieldAlgebra Y
    ∀ (i : Y.left.functionField →+* Ω),
    Spec.map (CommRingCat.ofHom
        (i.comp (algebraMap X.functionField Y.left.functionField))) ≫
        X.fromSpecStalk (genericPoint X) =
      (Spec.map (CommRingCat.ofHom i) ≫
        Y.left.fromSpecStalk (genericPoint Y.left)) ≫ Y.hom := by
  intro integralY algebraXY i
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  change Spec.map (CommRingCat.ofHom i) ≫
      Spec.map (CommRingCat.ofHom ((show Y.left ⟶ X from Y.hom).functionFieldMap
        (finiteEtale_hom_denseRange_of_isConnected Y))) ≫
      X.fromSpecStalk (genericPoint X) = _
  rw [Spec_functionFieldMap_fromSpecStalk, Category.assoc]

/-- The same restriction preserves the original constant coefficient map. -/
theorem finiteEtaleFunctionFieldEmbedding_restrict_constants
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (c : X ⟶ Spec (.of k)) (Y : FiniteEtale X) [IsConnected Y]
    {Ω : Type u} [Field Ω] :
    let _ : IsIntegral Y.left := coverIntegral Y
    let _ : Algebra X.functionField Y.left.functionField := coverFieldAlgebra Y
    ∀ (i : Y.left.functionField →+* Ω),
    (i.comp (algebraMap X.functionField Y.left.functionField)).comp
        (baseToFunctionField c) =
      i.comp (baseToFunctionField (Y.hom ≫ c)) := by
  intro integralY algebraXY i
  rw [RingHom.comp_assoc]
  exact congrArg (RingHom.comp i)
    (functionFieldMap_comp_baseToFunctionField c (show Y.left ⟶ X from Y.hom)
      (finiteEtale_hom_denseRange_of_isConnected Y))

/-- Every original image of a rationally pointed abelian finite étale
cover is contained in every image of the actual pointed Hilbert field in
the same ambient field. The finite cover and rational lift are unchanged. -/
theorem finiteEtaleFunctionFieldImage_le_hilbertImage
    (k : Type u) [Field k] [Finite k]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    ∀ [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField]
      [FunctionField k X.functionField] [HasPrincipalDivisors k X.functionField]
      (Y : FiniteEtale X) [IsGalois Y] [IsMulCommutative (Aut Y)],
    let _ : IsIntegral Y.left := coverIntegral Y
    let _ : Algebra X.functionField Y.left.functionField := coverFieldAlgebra Y
    ∀ (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
      (i : Y.left.functionField →ₐ[X.functionField] Ω)
      (x : closedPoints X) (ε : Spec (.of k) ⟶ X)
      (_ : ε ≫ c = 𝟙 _) (_ : ε (IsLocalRing.closedPoint k) = x.1)
      (s : Spec (.of k) ⟶ Y.left) (_ : s ≫ Y.hom = ε),
      let H := hilbertClassField k X.functionField
        {(CurveModel.ofSmoothProperCurve c).placeOfPoint x}
          (Finset.singleton_nonempty _)
      ∀ iH : H.val →ₐ[X.functionField] Ω, i.fieldRange ≤ iH.fieldRange := by
  intro akK aRK hkRK hfunction hprincipal Y hY hcomm integralY algebraXY
    Ω hΩ aKΩ i x ε hε hεx s hs H iH
  have hfinite : FiniteDimensional X.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  have habelian : IsAbelianGalois X.functionField Y.left.functionField :=
    isAbelianGalois_functionField_of_isGalois_finiteEtale Y
  let j : Y.left.functionField →ₐ[X.functionField] SeparableClosure X.functionField :=
    IsSepClosed.lift
  have hj : j.fieldRange ≤ H.val :=
    finiteEtaleFunctionFieldImage_le_hilbertClassField k c Y j x ε hε hεx s hs
  let jH : Y.left.functionField →ₐ[X.functionField] H.val :=
    (IntermediateField.inclusion hj).comp j.equivFieldRange.toAlgHom
  have hrange : i.fieldRange = (iH.comp jH).fieldRange :=
    ClassFieldTheory.fieldRange_eq_of_normal i (iH.comp jH)
  rw [hrange]
  rintro a ⟨b, rfl⟩
  exact ⟨jH b, rfl⟩

/-- A fixed original Hilbert image fixes the given pointed-cover image.
The base algebra in the ambient field is the restriction of the original
raw covering-field embedding, so no comparison of chosen embeddings is an
additional hypothesis. -/
theorem finiteEtaleFunctionFieldEmbedding_fixed_of_hilbertImage_fixed
    (k : Type u) [Field k] [Finite k]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    ∀ [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField]
      [FunctionField k X.functionField] [HasPrincipalDivisors k X.functionField]
      (Y : FiniteEtale X) [IsGalois Y] [IsMulCommutative (Aut Y)],
    let _ : IsIntegral Y.left := coverIntegral Y
    let _ : Algebra X.functionField Y.left.functionField := coverFieldAlgebra Y
    ∀ (Ω : Type u) [Field Ω] (i : Y.left.functionField →+* Ω)
      (x : closedPoints X) (ε : Spec (.of k) ⟶ X)
      (_ : ε ≫ c = 𝟙 _) (_ : ε (IsLocalRing.closedPoint k) = x.1)
      (s : Spec (.of k) ⟶ Y.left) (_ : s ≫ Y.hom = ε),
      let _ : Algebra X.functionField Ω :=
        (i.comp (algebraMap X.functionField Y.left.functionField)).toAlgebra
      let H := hilbertClassField k X.functionField
        {(CurveModel.ofSmoothProperCurve c).placeOfPoint x}
          (Finset.singleton_nonempty _)
      ∀ (iH : H.val →ₐ[X.functionField] Ω) (τ : Ω ≃+* Ω),
        (∀ a : H.val, τ (iH a) = iH a) →
        ∀ a : Y.left.functionField, τ (i a) = i a := by
  intro akK aRK hkRK hfunction hprincipal Y hY hcomm integralY algebraXY
    Ω hΩ i x ε hε hεx s hs aKΩ H iH τ hτ
  let iY : Y.left.functionField →ₐ[X.functionField] Ω :=
    { i with commutes' := fun _ => rfl }
  have himage := finiteEtaleFunctionFieldImage_le_hilbertImage
    k c Y Ω iY x ε hε hεx s hs iH
  intro a
  obtain ⟨b, hb⟩ := himage (show iY a ∈ iY.fieldRange from ⟨a, rfl⟩)
  change τ (iY a) = iY a
  rw [← hb]
  exact hτ b

end EtaleFundamentalGroups
