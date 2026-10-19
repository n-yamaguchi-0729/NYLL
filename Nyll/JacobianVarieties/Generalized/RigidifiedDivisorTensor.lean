/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleZeroSchemeIdealTensorHom
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.Cartier

/-!
# Addition of canonically rigidified effective divisors

The tensor of the canonical sections cuts out the product ideal. Its
section-preserving inverse-ideal comparison identifies tensor products with
addition of effective Cartier divisors, and preserves the chosen trivializations
on the entire modulus.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X D : Scheme.{u}} (i : D ⟶ X)

/-- Disjointness from two effective Cartier divisors gives disjointness from their sum. -/
theorem avoids_mul (I J : X.IdealSheafData)
    (hI : ∀ y : D, i.base y ∉ I.support)
    (hJ : ∀ y : D, i.base y ∉ J.support) :
    ∀ y : D, i.base y ∉ (I * J).support := by
  intro y
  change i.base y ∉ ((I * J).support : Set X)
  rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup]
  exact fun h => h.elim (hI y) (hJ y)

/-- The canonical tensor comparison is an isomorphism of actual modulus-rigidified
line bundles; the proof constructs it from the canonical divisor sections. -/
def ofInvertibleIdealMulIso (I J : X.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (hIa : ∀ y : D, i.base y ∉ I.support)
    (hJa : ∀ y : D, i.base y ∉ J.support) :
    Iso ((ofInvertibleIdeal i I hI hIa).tensor (ofInvertibleIdeal i J hJ hJa))
      (ofInvertibleIdeal i (I * J) (hI.mul hJ) (avoids_mul i I J hIa hJa)) := by
  let M := ofInvertibleIdeal i I hI hIa
  let N := ofInvertibleIdeal i J hJ hJa
  let s : 𝟙_ X.Modules ⟶ M.L ⊗ N.L :=
    (λ_ (𝟙_ X.Modules)).inv ≫ (I.invModuleSection ⊗ₘ J.invModuleSection)
  have hs : pullbackSection i s ≫ (M.tensor N).trivialization.hom =
      𝟙 (𝟙_ D.Modules) :=
    tensor_normalized_sections M N I.invModuleSection J.invModuleSection
      (ofInvertibleIdeal_section i I hI hIa) (ofInvertibleIdeal_section i J hJ hJa)
  have hzero : zeroSchemeIdeal s = I * J := by
    exact (IsInvertible.zeroSchemeIdeal_tensorHom hI.isInvertible_invModule
      hJ.isInvertible_invModule I.invModuleSection J.invModuleSection).trans
      (congrArg₂ (fun A B : X.IdealSheafData => A * B)
        hI.zeroSchemeIdeal_invModuleSection hJ.zeroSchemeIdeal_invModuleSection)
  exact zeroDivisorIso (M.tensor N) s hs (I * J) (hI.mul hJ) hzero
    (avoids_mul i I J hIa hJa)

/-- Effective divisor addition becomes multiplication of the actual compatible
isomorphism classes, with the full modulus trivializations retained. -/
theorem classOf_ofInvertibleIdeal_mul (I J : X.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (hIa : ∀ y : D, i.base y ∉ I.support)
    (hJa : ∀ y : D, i.base y ∉ J.support) :
    classOf (ofInvertibleIdeal i (I * J) (hI.mul hJ) (avoids_mul i I J hIa hJa)) =
      classOf (ofInvertibleIdeal i I hI hIa) * classOf (ofInvertibleIdeal i J hJ hJa) :=
  ((classOf_eq_iff
    ((ofInvertibleIdeal i I hI hIa).tensor (ofInvertibleIdeal i J hJ hJa))
    (ofInvertibleIdeal i (I * J) (hI.mul hJ) (avoids_mul i I J hIa hJa))).mpr
      ⟨ofInvertibleIdealMulIso i I J hI hJ hIa hJa⟩).symm

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
