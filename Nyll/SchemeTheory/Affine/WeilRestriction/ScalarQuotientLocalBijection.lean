/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientSchemePresheaf
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# The projective norm-open is the local scalar quotient

The standard principal charts of the projective norm open pull back to
every test scheme. The adjunction between relative spectrum and global
sections carries each pulled-back chart to an algebra map under which its
chart function is invertible. Actual normalized units give local lifts,
and the scalar-orbit calculation gives local injectivity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Module

universe u

namespace SchemeTheory.Affine.ScalarQuotientSchemePresheaf

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n : ℕ} (b : Basis (Fin (n + 1)) R A)

/-- The finite principal-open cover provided by the actual chart functions. -/
def chartCover : (ProjectiveUnitOpen.carrier b).AffineOpenCover :=
  Scheme.affineOpenCoverOfSpanRangeEqTop (ProjectiveUnitCharts.chartElement b)
    (ProjectiveUnitCharts.span_chartElement b)

/-- A normalized chart, as a scheme over the original coefficient spectrum. -/
def chartObject (j : Fin (n + 1)) : Over (Spec (CommRingCat.of R)) :=
  (algSpec (CommRingCat.of R)).obj
    (op (CommAlgCat.of R (ProjectiveUnitCharts.LocalChart b j)))

/-- The chart inclusion is induced by the actual principal localization. -/
def chartMap (j : Fin (n + 1)) : chartObject b j ⟶ representingObject b :=
  (algSpec (CommRingCat.of R)).map
    (CommAlgCat.ofHom (Algebra.algHom R (ProjectiveUnitOpen.CoordinateRing b)
      (ProjectiveUnitCharts.LocalChart b j))).op

theorem chartMap_left (j : Fin (n + 1)) :
    (chartMap b j).left = (chartCover b).f j := rfl

variable {T : Over (Spec (CommRingCat.of R))}

/-- The test scheme restricted to one actual chart of its projective point. -/
def chartPullbackObject (t : T ⟶ representingObject b) (j : Fin (n + 1)) :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (pullback.fst t.left (chartMap b j).left ≫ T.hom)

/-- The members of the pulled-back cover map to the original test scheme. -/
def chartPullbackMap (t : T ⟶ representingObject b) (j : Fin (n + 1)) :
    chartPullbackObject b t j ⟶ T :=
  Over.homMk (pullback.fst t.left (chartMap b j).left)

/-- Each pulled-back cover member factors through its normalized chart. -/
def chartPullbackPoint (t : T ⟶ representingObject b) (j : Fin (n + 1)) :
    chartPullbackObject b t j ⟶ chartObject b j :=
  Over.homMk (pullback.snd t.left (chartMap b j).left) (by
    change pullback.snd t.left (chartMap b j).left ≫ (chartObject b j).hom =
      pullback.fst t.left (chartMap b j).left ≫ T.hom
    rw [← (chartMap b j).w, ← Category.assoc, ← pullback.condition,
      Category.assoc, t.w])

theorem chartPullback_condition (t : T ⟶ representingObject b) (j : Fin (n + 1)) :
    chartPullbackMap b t j ≫ t = chartPullbackPoint b t j ≫ chartMap b j := by
  apply Over.OverMorphism.ext
  exact pullback.condition

/-- The explicit chart cover is an fppf cover on the relative big site. -/
theorem chartPullbackSieve_mem (t : T ⟶ representingObject b) :
    Sieve.ofArrows (chartPullbackObject b t) (chartPullbackMap b t) ∈
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage
  exact Scheme.Cover.mem_grothendieckTopology
    (P := (@IsOpenImmersion : MorphismProperty Scheme.{u}))
    ((chartCover b).openCover.pullback₁ t.left)

/-- The algebra map of a point restricted to a chart sends that chart
function to a unit, because it factors through its actual localization. -/
theorem isUnit_chartPullback_pointAlgHom (t : T ⟶ representingObject b)
    (j : Fin (n + 1)) :
    IsUnit (pointAlgHom b (chartPullbackMap b t j ≫ t)
      (ProjectiveUnitCharts.chartElement b j)) := by
  rw [chartPullback_condition]
  change IsUnit (((affinePointEquiv
    (CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b))
    (chartPullbackObject b t j)).symm
      (chartPullbackPoint b t j ≫ chartMap b j))
        (ProjectiveUnitCharts.chartElement b j))
  have he := affinePointEquiv_symm_postcomp
    (B := CommAlgCat.of R (ProjectiveUnitOpen.CoordinateRing b))
    (B' := CommAlgCat.of R (ProjectiveUnitCharts.LocalChart b j))
    (chartPullbackPoint b t j)
    (Algebra.algHom R (ProjectiveUnitOpen.CoordinateRing b)
      (ProjectiveUnitCharts.LocalChart b j))
  have hu := (IsLocalization.Away.algebraMap_isUnit
    (S := ProjectiveUnitCharts.LocalChart b j)
    (ProjectiveUnitCharts.chartElement b j)).map
      ((affinePointEquiv (CommAlgCat.of R (ProjectiveUnitCharts.LocalChart b j))
        (chartPullbackObject b t j)).symm (chartPullbackPoint b t j))
  exact (congrArg (fun f => IsUnit (f (ProjectiveUnitCharts.chartElement b j))) he).mpr hu

/-- The actual scalar quotient locally supplies every point of the
projective norm open, on every test scheme. -/
theorem comparison_isLocallySurjective :
    Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (comparison b) := by
  constructor
  intro T s
  apply (Scheme.fppfTopology.over (Spec (CommRingCat.of R))).superset_covering ?_
    (chartPullbackSieve_mem b s.down)
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

/-- Equality of projective points locally identifies precisely scalar
orbits, including over arbitrary nonaffine test schemes. -/
theorem comparison_isLocallyInjective :
    Presheaf.IsLocallyInjective
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (comparison b) := by
  constructor
  intro T q q' hq
  let t := ((comparison b).app T q).down
  apply (Scheme.fppfTopology.over (Spec (CommRingCat.of R))).superset_covering ?_
    (chartPullbackSieve_mem b t)
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro j
  apply ULift.ext
  change ScalarQuotientPresheaf.quotientMap (sectionsMap (chartPullbackMap b t j)) q.down =
    ScalarQuotientPresheaf.quotientMap (sectionsMap (chartPullbackMap b t j)) q'.down
  apply ScalarQuotientPresheaf.quotientPoint_injective_on_chart b
    (pointAlgHom b (chartPullbackMap b t j ≫ t)) j
    (isUnit_chartPullback_pointAlgHom b t j)
  · exact (ScalarQuotientPresheaf.quotientPoint_quotientMap b
      (sectionsMap (chartPullbackMap b t j)) q.down).trans
      ((congrArg (fun f => (sectionsMap (chartPullbackMap b t j)).comp f)
        (pointAlgHom_comparison_app b T.unop q).symm).trans
          (pointAlgHom_comp b (chartPullbackMap b t j) t).symm)
  · have hpoint : ScalarQuotientPresheaf.quotientPoint b q'.down =
        pointAlgHom b t := by
      exact (pointAlgHom_comparison_app b T.unop q').symm.trans
        (congrArg (pointAlgHom b) (congrArg ULift.down hq).symm)
    exact (ScalarQuotientPresheaf.quotientPoint_quotientMap b
      (sectionsMap (chartPullbackMap b t j)) q'.down).trans
      ((congrArg (fun f => (sectionsMap (chartPullbackMap b t j)).comp f) hpoint).trans
        (pointAlgHom_comp b (chartPullbackMap b t j) t).symm)

end SchemeTheory.Affine.ScalarQuotientSchemePresheaf
