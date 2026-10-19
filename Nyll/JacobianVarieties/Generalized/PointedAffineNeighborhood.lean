/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PointedConstruction
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapDataLeIsUnit
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.IsAffineOpenPicardRepresentabilityAlgEquivZeroCut

/-!
# Affine neighborhoods of finite sets in the actual modulus Picard scheme

The ordinary Picard scheme has affine neighborhoods of finite sets. The actual
Poincaré frame projection is affine, so their inverse images give the criterion
needed for effective finite faithfully flat descent.
-/

noncomputable section

universe u

open CategoryTheory NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian.Pointed

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d)

/-- Every finite set of points in the constructed modulus Picard scheme lies in
an affine open; no extra quasi-projectivity or descent hypothesis is required. -/
theorem exists_isAffineOpen_forall_mem (S : Finset (groupScheme c ε D hd).X.left) :
    ∃ U : (groupScheme c ε D hd).X.left.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U := by
  classical
  let J := ordinaryPicard c ε
  let h := ordinaryRepresentation c ε
  let W := poincareFrameQuotient D h hd
  have hsm : Smooth J.toBase := (exists_representsRelSubPic_of_field K c ε).choose_spec.2.1
  have hpr : IsProper J.toBase := (exists_representsRelSubPic_of_field K c ε).choose_spec.2.2.1
  have hgc : GeometricallyConnected J.toBase :=
    (exists_representsRelSubPic_of_field K c ε).choose_spec.2.2.2
  have h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : FiniteMapData c ε, m₀ ≤ 𝔉.m := by
    intro m₀
    obtain ⟨𝔉, hm, -⟩ := exists_finiteMapData_le_isUnit K c ε m₀
    exact ⟨𝔉, hm⟩
  have haff : ∀ A : Finset J.P, ∃ U : J.P.Opens, IsAffineOpen U ∧ ∀ y ∈ A, y ∈ U :=
    exists_isAffineOpen_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
      K c ε h𝔉 J h hsm hpr hgc
  have : IsAffineHom W.hom := poincareFrameQuotient_isAffineHom D h hd
  change ∃ U : W.left.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U
  obtain ⟨U, hU, hSU⟩ := haff (S.image fun x => W.hom x)
  exact ⟨W.hom ⁻¹ᵁ U, hU.preimage W.hom,
    fun x hx => hSU (W.hom x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩

end AlgebraicGeometry.GeneralizedJacobian.Pointed
