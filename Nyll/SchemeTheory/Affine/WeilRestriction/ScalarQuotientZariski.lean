/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.UnitNormSchemeRepresentation
import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientLocalBijection
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Actual Zariski lifts of the projective norm quotient

The normalized principal charts already give units representing every
projective norm point. Their pullbacks are open immersions, so a smooth
parameter scheme has smooth charts and smooth pairwise intersections.
These explicit lifts avoid choosing arbitrary fppf covers with possible
nilpotents when applying divisor-sum descent.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Module

namespace SchemeTheory.Affine.ScalarQuotientSchemePresheaf

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n : ℕ} (b : Basis (Fin (n + 1)) R A)
  {T : Over (Spec (CommRingCat.of R))}

/-- The actual normalized-chart cover is already a Zariski cover. -/
theorem chartPullbackSieve_mem_zariski (t : T ⟶ representingObject b) :
    Sieve.ofArrows (chartPullbackObject b t) (chartPullbackMap b t) ∈
      (Scheme.zariskiTopology.over (Spec (CommRingCat.of R))) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Scheme.Cover.mem_grothendieckTopology
    (P := (@IsOpenImmersion : MorphismProperty Scheme.{u}))
    ((chartCover b).openCover.pullback₁ t.left)

/-- Each actual chart inclusion is an open immersion. -/
theorem chartPullbackMap_isOpenImmersion (t : T ⟶ representingObject b)
    (j : Fin (n + 1)) : IsOpenImmersion (chartPullbackMap b t j).left := by
  have : IsOpenImmersion (chartMap b j).left := by
    rw [chartMap_left]
    exact (chartCover b).openCover.map_prop j
  change IsOpenImmersion (pullback.fst t.left (chartMap b j).left)
  infer_instance

/-- The scalar-unit quotient comparison is Zariski locally surjective. -/
theorem comparison_isLocallySurjective_zariski :
    Presheaf.IsLocallySurjective
      (Scheme.zariskiTopology.over (Spec (CommRingCat.of R))) (comparison b) := by
  constructor
  intro T s
  apply (Scheme.zariskiTopology.over (Spec (CommRingCat.of R))).superset_covering ?_
    (chartPullbackSieve_mem_zariski b s.down)
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro j
  obtain ⟨q, hq⟩ := ScalarQuotientPresheaf.quotientPoint_surjective_on_chart b
    (pointAlgHom b (chartPullbackMap b s.down j ≫ s.down)) j
    (isUnit_chartPullback_pointAlgHom b s.down j)
  refine ⟨ULift.up q, ?_⟩
  apply ULift.ext
  change affinePointEquiv (CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b))
    (chartPullbackObject b s.down j) (ScalarQuotientPresheaf.quotientPoint b q) =
      chartPullbackMap b s.down j ≫ s.down
  rw [hq]
  exact Equiv.apply_symm_apply _ _

include b in
/-- The fppf sheafification itself has actual scalar-unit representatives
on Zariski opens, by the proved represented comparison. -/
theorem toSheafify_isLocallySurjective_zariski :
    Presheaf.IsLocallySurjective
      (Scheme.zariskiTopology.over (Spec (CommRingCat.of R)))
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (liftedGroupPresheaf R A ⋙ forget CommGrpCat.{u + 1})) := by
  have := comparison_isLocallySurjective_zariski b
  have he : toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (liftedGroupPresheaf R A ⋙ forget CommGrpCat.{u + 1}) =
      comparison b ≫ (sheafifiedComparisonIso b).inv := by
    rw [← toSheafify_sheafifiedComparisonIso, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [he]
  infer_instance

/-- On every chart there is an actual morphism to the unit norm scheme
whose projective class is precisely the prescribed point. -/
theorem exists_chartPullback_unitLift (t : T ⟶ representingObject b)
    (j : Fin (n + 1)) :
    ∃ g : chartPullbackObject b t j ⟶ UnitNormPolynomial.normRepresentingObject b,
      g ≫ UnitNormPolynomial.quotientOver b = chartPullbackMap b t j ≫ t := by
  obtain ⟨q, hq⟩ := ScalarQuotientPresheaf.quotientPoint_surjective_on_chart b
    (pointAlgHom b (chartPullbackMap b t j ≫ t)) j
    (isUnit_chartPullback_pointAlgHom b t j)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  let g : chartPullbackObject b t j ⟶ UnitNormPolynomial.normRepresentingObject b :=
    (UnitNormPolynomial.normSchemeRepresentable b).homEquiv.symm a
  refine ⟨g, ?_⟩
  rw [← UnitNormPolynomial.normSchemeRepresentable_quotient]
  have ha : (UnitNormPolynomial.normSchemeRepresentable b).homEquiv g = a :=
    Equiv.apply_symm_apply _ a
  change (comparisonSmall b).app (op (chartPullbackObject b t j))
      (QuotientGroup.mk ((UnitNormPolynomial.normSchemeRepresentable b).homEquiv g)) = _
  rw [ha]
  change affinePointEquiv (CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b))
    (chartPullbackObject b t j) (ScalarQuotientPresheaf.quotientPoint b
      (QuotientGroup.mk a)) = _
  rw [hq]
  exact Equiv.apply_symm_apply _ _

/-- A smooth parameter scheme gives smooth actual representative charts. -/
theorem chartPullbackObject_smooth [Smooth T.hom]
    (t : T ⟶ representingObject b) (j : Fin (n + 1)) :
    Smooth (chartPullbackObject b t j).hom := by
  have := chartPullbackMap_isOpenImmersion b t j
  change Smooth ((chartPullbackMap b t j).left ≫ T.hom)
  infer_instance

/-- The actual pairwise chart overlap remains smooth over the coefficient base. -/
theorem chartPullback_overlap_smooth [Smooth T.hom]
    (t : T ⟶ representingObject b) (j k : Fin (n + 1)) :
    Smooth (pullback.fst (chartPullbackMap b t j).left (chartPullbackMap b t k).left ≫
      (chartPullbackObject b t j).hom) := by
  have := chartPullbackMap_isOpenImmersion b t k
  have := chartPullbackObject_smooth b t j
  infer_instance

end SchemeTheory.Affine.ScalarQuotientSchemePresheaf
