/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertConstantReindex
public import Nyll.EtaleFundamentalGroups.GaloisCovers.PointedHilbertClassField

/-!
# Native pointed covers in the original-base Hilbert class field

A finite constant model is a curve over its own constants, while the norm
tower uses the original finite base throughout. The actual equality of
the two Hilbert subfields transfers the cover containment to that original
base without changing the covering scheme, generic embedding or place.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicCurve FunctionField TopologicalSpace

namespace EtaleFundamentalGroups

/-- The original embedded field of a rationally pointed abelian finite
étale cover lies in the Hilbert class field formed over the initial finite
base, even when its rational point has higher degree over that base. -/
theorem finiteEtaleFunctionFieldImage_le_hilbertClassField_forgetConstants
    (k : Type v) (C : Type u) [Field k] [Finite k] [Field C] [Finite C]
    [Algebra k C] [Algebra.IsIntegral k C]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (c : X ⟶ Spec (.of C)) [IsProper c] [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra C X.functionField := (baseToFunctionField c).toAlgebra
    ∀ [Algebra k X.functionField] [IsScalarTower k C X.functionField]
      [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField]
      [FunctionField k X.functionField] [HasPrincipalDivisors k X.functionField]
      [Algebra (RatFunc C) X.functionField]
      [IsScalarTower C (RatFunc C) X.functionField]
      [FunctionField C X.functionField] [HasPrincipalDivisors C X.functionField]
      (Y : FiniteEtale X) [IsGalois Y] [IsMulCommutative (Aut Y)],
    let _ : IsIntegral Y.left := coverIntegral Y
    let _ : Algebra X.functionField Y.left.functionField := coverFieldAlgebra Y
    ∀ (i : Y.left.functionField →ₐ[X.functionField] SeparableClosure X.functionField)
      (x : closedPoints X) (ε : Spec (.of C) ⟶ X)
      (_ : ε ≫ c = 𝟙 _) (_ : ε (IsLocalRing.closedPoint C) = x.1)
      (s : Spec (.of C) ⟶ Y.left) (_ : s ≫ Y.hom = ε),
      i.fieldRange ≤ (hilbertClassField k X.functionField
        {((CurveModel.ofSmoothProperCurve c).placeOfPoint x).forgetConstants (K := k)}
          (Finset.singleton_nonempty _)).val := by
  intro aCK akK hkCK aRkK hkRkK hfunctionk hprincipalk
    aRCK hCRCK hfunctionC hprincipalC Y hY hcomm integralY algebraXY i x ε hε hεx s hs
  rw [hilbertClassField_forgetConstants k C X.functionField]
  exact finiteEtaleFunctionFieldImage_le_hilbertClassField C c Y i x ε hε hεx s hs

end EtaleFundamentalGroups
