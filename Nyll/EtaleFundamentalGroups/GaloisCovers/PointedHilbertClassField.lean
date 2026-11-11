/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.EtaleHilbertClassField
public import Nyll.EtaleFundamentalGroups.GaloisCovers.AbelianFunctionField
public import Nyll.EtaleFundamentalGroups.GaloisCovers.PointedGaloisFiber
public import Nyll.SchemeTheory.FunctionFields.StructureMorphismNaturality
public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.AlgebraicCurves.Models.FunctionFields.FieldReparametrization
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension

/-!
# Hilbert class-field containment for the original finite étale cover

The covering scheme, structural morphism and original generic-field
embedding are retained. Its field-level abelianity and its curve model are
constructed from the native finite étale Galois cover. One actual rational
lift supplies complete splitting through its native deck orbit.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicCurve FunctionField TopologicalSpace

namespace EtaleFundamentalGroups

/-- Every original embedding of an actual abelian finite étale Galois cover
with a rational lift of the chosen point lands in its Hilbert class field.
No model or field-level Galois comparison is an additional input. -/
theorem finiteEtaleFunctionFieldImage_le_hilbertClassField
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
    ∀ (i : Y.left.functionField →ₐ[X.functionField] SeparableClosure X.functionField),
    let _ : Algebra k (SeparableClosure X.functionField) :=
      ((algebraMap X.functionField (SeparableClosure X.functionField)).comp
        (algebraMap k X.functionField)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure X.functionField) :=
      ((algebraMap X.functionField (SeparableClosure X.functionField)).comp
        (algebraMap (RatFunc k) X.functionField)).toAlgebra
    let _ : IsScalarTower k X.functionField (SeparableClosure X.functionField) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) X.functionField
        (SeparableClosure X.functionField) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure X.functionField) :=
      IsScalarTower.of_algebraMap_eq (fun x =>
        congrArg (algebraMap X.functionField (SeparableClosure X.functionField))
          (IsScalarTower.algebraMap_apply k (RatFunc k) X.functionField x))
    ∀ (x : closedPoints X) (ε : Spec (.of k) ⟶ X)
      (_ : ε ≫ c = 𝟙 _) (_ : ε (IsLocalRing.closedPoint k) = x.1)
      (s : Spec (.of k) ⟶ Y.left) (_ : s ≫ Y.hom = ε),
      i.fieldRange ≤ (hilbertClassField k X.functionField
        {(CurveModel.ofSmoothProperCurve c).placeOfPoint x}
          (Finset.singleton_nonempty _)).val := by
  intro akK aRK hkRK hfunction hprincipal Y hY hcomm integralY algebraXY i
    akΩ aRΩ hkKΩ hRKΩ hkRΩ x ε hε hεx s hs
  have hEtale : IsFiniteEtale (show Y.left ⟶ X from Y.hom) := Y.prop
  have hfiniteY : IsFinite Y.hom := Y.prop.toIsFinite
  have hetaleY : Etale Y.hom := Y.prop.toEtale
  let cY : Y.left ⟶ Spec (.of k) := Y.hom ≫ c
  have hproper : IsProper cY := by dsimp only [cY]; infer_instance
  have hsmooth : SmoothOfRelativeDimension 1 cY :=
    smoothOfRelativeDimension_comp 0 1 (show Y.left ⟶ X from Y.hom) c
  let akL : Algebra k Y.left.functionField := (baseToFunctionField cY).toAlgebra
  have hcoeff : IsScalarTower k X.functionField Y.left.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (DFunLike.congr_fun (functionFieldMap_comp_baseToFunctionField c
        (show Y.left ⟶ X from Y.hom)
          (finiteEtale_hom_denseRange_of_isConnected Y)) a).symm
  let E : ClassFieldTheory.FiniteAbelianLocalExtension X.functionField :=
    finiteEtaleAbelianFunctionFieldImage Y i
  let e : Y.left.functionField ≃ₐ[k] E.val :=
    i.equivFieldRange.restrictScalars k
  let M : CurveModel k X.functionField := CurveModel.ofSmoothProperCurve c
  let N₀ : CurveModel k Y.left.functionField := CurveModel.ofSmoothProperCurve cY
  let N : CurveModel k E.val := N₀.reparametrizeField e
  let p : N.C ⟶ M.C := Y.hom
  have : IsFinite p := hfiniteY
  have : Etale p := hetaleY
  have hfields : N.ffEquiv.toRingHom.comp
      ((algebraMap X.functionField E.val).comp M.ffEquiv.symm.toRingHom) =
        (show Y.left ⟶ X from Y.hom).functionFieldMap
          (finiteEtale_hom_denseRange_of_isConnected Y) := by
    ext a
    change i.equivFieldRange.symm (algebraMap X.functionField i.fieldRange a) =
      algebraMap X.functionField Y.left.functionField a
    exact i.equivFieldRange.symm.commutes a
  have hgeneric : N.C.fromSpecStalk (genericPoint N.C) ≫ Y.hom =
      Spec.map (CommRingCat.ofHom (N.ffEquiv.toRingHom.comp
        ((algebraMap X.functionField E.val).comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C) := by
    rw [hfields]
    exact (Spec_functionFieldMap_fromSpecStalk (show Y.left ⟶ X from Y.hom)
      (finiteEtale_hom_denseRange_of_isConnected Y)).symm
  apply finiteEtale_le_hilbertClassField_of_rational_fiber k X.functionField E
    M N p rfl hgeneric x ε hε hεx
  intro y hy
  exact FiniteEtale.exists_rationalPoint_lift_through_of_isGalois Y ε s hs y.1
    (hy.trans hεx.symm)

end EtaleFundamentalGroups
