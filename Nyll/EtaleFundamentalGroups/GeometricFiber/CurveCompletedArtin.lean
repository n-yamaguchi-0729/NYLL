/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.CompletedArtin
public import Nyll.EtaleFundamentalGroups.GaloisCovers.CurveRayArtinKernel
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletion
public import Nyll.ProCGroups.ProC.Quotients.ClosedNormal

/-! # The same curve Artin map before and after completion

The direct map and completed reciprocity use the original generic-point Galois
map and the canonical idele-class quotient. Their equality on genuine idele
classes determines the continuous completion and identifies its pulled-back
kernel, including the original ray containment.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve
open FunctionField LocalClassFieldTheory ProCGroups.Abelian

namespace EtaleFundamentalGroups

-- Resolve the actual quotient structure before substituting a scheme stalk.
local instance curveIdeleClassCommGroup
    (k : Type v) (K : Type u) [Field k] [Field K] [Algebra k K]
    [HasPrincipalDivisors k K] : CommGroup (IdeleClassGroup k K) :=
  RayClass.powerRayIdeleClassCommGroup (k := k) (K := K)

local instance curveAbelianizationTotallyDisconnected
    (X : Scheme.{u}) [IsIntegral X] :
    TotallyDisconnectedSpace (TopologicalAbelianization
      (π₁ᵉᵗ(X.genericExtensionMorphism (AlgebraicClosure X.functionField)))) :=
  ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
    (Subgroup.closedCommutator
      (π₁ᵉᵗ(X.genericExtensionMorphism (AlgebraicClosure X.functionField))))
    (Subgroup.isClosed_closedCommutator _)

section Comparison

variable (X : Scheme.{u}) [IsIntegral X]
  (k : Type v) [Field k] [Finite k] [Algebra k X.functionField]
  [Algebra (RatFunc k) X.functionField]
  [IsScalarTower k (RatFunc k) X.functionField]
  [FunctionField k X.functionField] [HasPrincipalDivisors k X.functionField]

/-- Completed reciprocity evaluates to the original direct curve Artin map
on the same idele class. -/
theorem genericCompletedArtin_map_eq_curveArtin
    (c : IdeleClassGroup k X.functionField) :
    genericCompletedArtin X k
        (topologicalProfiniteCompletionMap (IdeleClassGroup k X.functionField) c) =
      Inertia.curveArtin (k := k) X c :=
  genericCompletedArtin_map X k c

/-- The direct map is the restriction of completed reciprocity along the
canonical completion map. -/
theorem genericCompletedArtin_comp_map_eq_curveArtin :
    (genericCompletedArtin X k).comp
        (topologicalProfiniteCompletionMap (IdeleClassGroup k X.functionField)) =
      Inertia.curveArtin (k := k) X := by
  apply ContinuousMonoidHom.ext
  intro c
  exact genericCompletedArtin_map_eq_curveArtin X k c

/-- Density identifies completed reciprocity with the canonical continuous
lift of the original curve Artin map. -/
theorem genericCompletedArtin_eq_completionLift_curveArtin :
    genericCompletedArtin X k =
      topologicalProfiniteCompletionLift
        (ProfiniteGrp.of (TopologicalAbelianization
          (π₁ᵉᵗ(X.genericExtensionMorphism (AlgebraicClosure X.functionField)))))
        (Inertia.curveArtin (k := k) X) := by
  let P := ProfiniteGrp.of (TopologicalAbelianization
    (π₁ᵉᵗ(X.genericExtensionMorphism (AlgebraicClosure X.functionField))))
  nyll_kernel_exact
    (topologicalProfiniteCompletionLift_unique P (Inertia.curveArtin (k := k) X)
      (genericCompletedArtin X k) (genericCompletedArtin_comp_map_eq_curveArtin X k))

/-- Pulling the completed kernel back to genuine idele classes gives the
kernel of the same direct map, with no additional comparison hypothesis. -/
theorem genericCompletedArtin_ker_comap_eq_curveArtin_ker :
    (genericCompletedArtin X k).toMonoidHom.ker.comap
        (topologicalProfiniteCompletionMap
          (IdeleClassGroup k X.functionField)).toMonoidHom =
      (Inertia.curveArtin (k := k) X).toMonoidHom.ker :=
  congrArg (fun f : IdeleClassGroup k X.functionField →ₜ*
      TopologicalAbelianization
        (π₁ᵉᵗ(X.genericExtensionMorphism (AlgebraicClosure X.functionField))) =>
      f.toMonoidHom.ker)
    (genericCompletedArtin_comp_map_eq_curveArtin X k)

end Comparison

/-- The completed kernel retains the original ray containment after
pullback to idele classes of the literal curve function field. -/
theorem genericCompletedArtin_ker_comap_le_rayClassSubgroup
    {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X]
    (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    ∀ [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField] [FunctionField k X.functionField]
      [HasPrincipalDivisors k X.functionField]
      (m : RayClass.Modulus k X.functionField),
      (∀ p ∈ Inertia.curveInteriorPlaces c, m p = 0) →
      (genericCompletedArtin X k).toMonoidHom.ker.comap
          (topologicalProfiniteCompletionMap
            (IdeleClassGroup k X.functionField)).toMonoidHom ≤
        RayClass.rayClassSubgroup m := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors m hm
  have h := @genericCompletedArtin_ker_comap_eq_curveArtin_ker X _ k _ _ baseAlgebra
    rationalAlgebra rationalTower functionField principalDivisors
  let R := RayClass.rayClassSubgroup m
  have hray : (Inertia.curveArtin (k := k) X).toMonoidHom.ker ≤ R := by
    nyll_kernel_exact (@Inertia.curveArtin_ker_le_rayClassSubgroup k _ _ X _ _ c _
      rationalAlgebra rationalTower functionField principalDivisors m hm)
  have hle := congrArg (fun S : Subgroup (IdeleClassGroup k X.functionField) => S ≤ R) h
  nyll_kernel_exact (Eq.mpr hle hray)

end EtaleFundamentalGroups
