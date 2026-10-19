/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenus
import Nyll.SchemeTheory.GroupSchemes.AbelianScheme
import Nyll.JacobianVarieties.Generalized.Construction
import Nyll.JacobianVarieties.Generalized.KernelGroup
import Nyll.JacobianVarieties.Generalized.EmptyOrdinaryComparison
import Nyll.JacobianVarieties.Generalized.ModulusDegreeOneComparison

/-! # Abelian varieties supplied by the actual Jacobian constructions

The ordinary Jacobian and the generalized Jacobians with modulus of degree at most
one satisfy the reusable abelian-scheme interface on their existing group objects.
No rational base point on the curve is needed.
-/

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- The zero-modulus Jacobian is an abelian variety over the original field. -/
instance zeroDegree_isAbelianScheme
    (D : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K)))) :
    IsAbelianScheme (groupScheme c D) where
  toSmooth := by
    have : SmoothOfRelativeDimension (geometricGenus K c) (groupScheme c D).X.hom :=
      (zeroDegreeGeometry c D).1
    exact SmoothOfRelativeDimension.smooth (geometricGenus K c) _
  toIsProper := (zeroDegreeGeometry c D).2.1
  toGeometricallyConnected := (zeroDegreeGeometry c D).2.2

/-- The ordinary Picard-zero group scheme is an abelian variety. -/
instance ordinary_isAbelianScheme : IsAbelianScheme (ordinaryGroupScheme c) :=
  IsAbelianScheme.of_iso (emptyModulusGroupIso c (RelEffCartierDiv.empty c (𝟙 _)))

/-- The original ordinary Jacobian group law has the same abelian-variety interface. -/
instance existingOrdinary_isAbelianScheme :
    IsAbelianScheme (JacobianVarieties.Picard.Unpointed.groupScheme K c) :=
  IsAbelianScheme.of_iso (zeroDegreeOrdinaryComparison c (RelEffCartierDiv.empty c (𝟙 _)))

/-- A degree-one modulus leaves an abelian variety with the actual tensor-product group law. -/
instance degreeOne_isAbelianScheme
    (D : RelEffCartierDiv c 1 (𝟙 (Spec (CommRingCat.of K)))) :
    IsAbelianScheme (groupScheme c D) :=
  IsAbelianScheme.of_iso (degreeOneGroupIso D).symm

/-- Both the empty modulus and a single rational reduced point give abelian varieties. -/
theorem isAbelianScheme_of_degree_le_one {d : ℕ}
    (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : d ≤ 1) :
    IsAbelianScheme (groupScheme c D) := by
  cases d with
  | zero => infer_instance
  | succ n =>
      have hn : n = 0 := by omega
      subst n
      infer_instance

end AlgebraicGeometry.GeneralizedJacobian
