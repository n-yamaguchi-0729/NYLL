/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ProfiniteReciprocity
public import Nyll.EtaleFundamentalGroups.Inertia.GenericKernelNormalGeneration
public import Nyll.ProCGroups.Abelian.TopologicalAbelianizationKernel
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteArtin
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.CompletedArtin
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.PrincipalCore

/-!
# Completed reciprocity in the original scheme fundamental group

Compose actual completed function-field reciprocity with the abelianization
of the original generic-point monodromy map. The resulting continuous map is
surjective. Its kernel is exactly the reciprocity preimage of the image of
the original normalization inertia groups, using the native generic-kernel
theorem. This supplies the arithmetic quotient before the proper-curve
Picard norm and geometric constant-tower comparisons.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open AlgebraicCurve LocalClassFieldTheory ProCGroups.Abelian

namespace EtaleFundamentalGroups

-- Fix the canonical quotient dictionaries while the field is abstract;
-- inferring them after substituting a scheme stalk unfolds its completions.
private local instance ideleClassMulOneClass
    (k : Type v) (K : Type u) [Field k] [Field K] [Algebra k K] [HasPrincipalDivisors k K] :
    MulOneClass (FunctionField.IdeleClassGroup k K) :=
  inferInstance

private local instance ideleClassGroup
    (k : Type v) (K : Type u) [Field k] [Field K] [Algebra k K] [HasPrincipalDivisors k K] :
    Group (FunctionField.IdeleClassGroup k K) :=
  inferInstance

variable (X : Scheme.{u}) [IsIntegral X]
  (k : Type v) [Field k] [Finite k] [Algebra k X.functionField]
  [Algebra (RatFunc k) X.functionField]
  [IsScalarTower k (RatFunc k) X.functionField]
  [FunctionField k X.functionField]
  [HasPrincipalDivisors k X.functionField]

/-- Actual completed function-field reciprocity followed by original
generic-point monodromy and topological abelianization. -/
def genericCompletedArtin :
    TopologicalProfiniteCompletion (FunctionField.IdeleClassGroup k X.functionField) →ₜ*
      TopologicalAbelianization
        π₁ᵉᵗ(X.genericExtensionMorphism (AlgebraicClosure X.functionField)) :=
  (TopologicalAbelianization.map (genericAbsoluteGaloisHom X)).comp
    (FunctionField.completedArtin k X.functionField)

/-- The map on a genuine idele class is its original absolute Artin value
followed by the original generic-point map. -/
theorem genericCompletedArtin_map
    (c : FunctionField.IdeleClassGroup k X.functionField) :
    genericCompletedArtin X k
        (topologicalProfiniteCompletionMap
          (FunctionField.IdeleClassGroup k X.functionField) c) =
      TopologicalAbelianization.map (genericAbsoluteGaloisHom X)
        (FunctionField.absoluteArtin k X.functionField c) :=
  congrArg (TopologicalAbelianization.map (genericAbsoluteGaloisHom X))
    (FunctionField.completedArtin_map k X.functionField c)

/-- Any original absolute Artin representative gives the same native
abelianized monodromy value. -/
theorem genericCompletedArtin_map_of_lift
    (c : FunctionField.IdeleClassGroup k X.functionField)
    (σ : Gal(SeparableClosure X.functionField/X.functionField))
    (hσ : localAbsoluteAbelianizationQuotientMap X.functionField σ =
      FunctionField.absoluteArtin k X.functionField c) :
    genericCompletedArtin X k
        (topologicalProfiniteCompletionMap
          (FunctionField.IdeleClassGroup k X.functionField) c) =
      TopologicalAbelianization.mk _ (genericAbsoluteGaloisHom X σ) := by
  exact (genericCompletedArtin_map X k c).trans
    (congrArg (TopologicalAbelianization.map (genericAbsoluteGaloisHom X)) hσ.symm)

variable [IsNormalIntegral X]

/-- The native completed reciprocity map is surjective on every normal
integral function-field model. -/
theorem genericCompletedArtin_surjective :
    Function.Surjective (genericCompletedArtin X k) :=
  (TopologicalAbelianization.surjective_map_of_surjective
    (genericAbsoluteGaloisHom X) (genericAbsoluteGaloisHom_surjective X)).comp
      (FunctionField.completedArtin_surjective k X.functionField)

/-- The exact kernel retains both original maps: actual completed
reciprocity and the original normalization inertia in the function field. -/
theorem genericCompletedArtin_ker :
    (genericCompletedArtin X k).toMonoidHom.ker =
      (((Subgroup.normalClosure
          (Inertia.affineNormalizationInertiaGenerators X)).topologicalClosure).map
        (TopologicalAbelianization.mk
          Gal(SeparableClosure X.functionField/X.functionField))).comap
            (FunctionField.completedArtin k X.functionField).toMonoidHom := by
  change (TopologicalAbelianization.map (genericAbsoluteGaloisHom X)).toMonoidHom.ker.comap
      (FunctionField.completedArtin k X.functionField).toMonoidHom = _
  rw [TopologicalAbelianization.ker_map_of_surjective
    (genericAbsoluteGaloisHom X) (genericAbsoluteGaloisHom_surjective X),
    Inertia.genericAbsoluteGaloisHom_ker_eq_normalClosure_affineNormalizationInertia]

/-- Completed reciprocity modulo its proved native kernel identifies the
original scheme abelian fundamental group as a topological group. -/
def genericCompletedArtinQuotientEquiv :
    (TopologicalProfiniteCompletion (FunctionField.IdeleClassGroup k X.functionField) ⧸
      (genericCompletedArtin X k).toMonoidHom.ker) ≃ₜ*
      TopologicalAbelianization
        π₁ᵉᵗ(X.genericExtensionMorphism (AlgebraicClosure X.functionField)) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective
    (genericCompletedArtin X k).toMonoidHom (genericCompletedArtin_surjective X k)
  apply ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2 e.toMonoidHom _ e.bijective
  exact (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (genericCompletedArtin X k).continuous

/-- The quotient comparison preserves the literal completed Artin value. -/
theorem genericCompletedArtinQuotientEquiv_mk
    (c : TopologicalProfiniteCompletion (FunctionField.IdeleClassGroup k X.functionField)) :
    genericCompletedArtinQuotientEquiv X k (QuotientGroup.mk c) =
      genericCompletedArtin X k c := rfl

end EtaleFundamentalGroups
