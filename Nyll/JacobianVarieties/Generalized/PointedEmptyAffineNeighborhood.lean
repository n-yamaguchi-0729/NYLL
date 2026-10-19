/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PointedEmptyConstruction
import Nyll.JacobianVarieties.Generalized.PointedAffineNeighborhood

/-! # Affine neighborhoods for the degree-zero modulus representative -/

noncomputable section

universe u

open CategoryTheory NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian.Pointed

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  (D : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K))))

/-- The actual empty-modulus representative inherits the affine-neighborhood
criterion from the ordinary Picard scheme, without an additional hypothesis. -/
theorem zeroDegree_exists_isAffineOpen_forall_mem
    (S : Finset (zeroDegreeGroupScheme c ε D).X.left) :
    ∃ U : (zeroDegreeGroupScheme c ε D).X.left.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U := by
  let J := ordinaryPicard c ε
  let h := ordinaryRepresentation c ε
  have hsm : Smooth J.toBase := (exists_representsRelSubPic_of_field K c ε).choose_spec.2.1
  have hpr : IsProper J.toBase := (exists_representsRelSubPic_of_field K c ε).choose_spec.2.2.1
  have hgc : GeometricallyConnected J.toBase :=
    (exists_representsRelSubPic_of_field K c ε).choose_spec.2.2.2
  have h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : FiniteMapData c ε, m₀ ≤ 𝔉.m := by
    intro m₀
    obtain ⟨𝔉, hm, -⟩ := exists_finiteMapData_le_isUnit K c ε m₀
    exact ⟨𝔉, hm⟩
  exact exists_isAffineOpen_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
    K c ε h𝔉 J h hsm hpr hgc S

end AlgebraicGeometry.GeneralizedJacobian.Pointed
