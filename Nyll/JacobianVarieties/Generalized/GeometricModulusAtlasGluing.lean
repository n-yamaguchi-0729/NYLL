/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeometricModulusMapCondition
import Nyll.JacobianVarieties.Generalized.PicardZeroLocalSums
import Nyll.JacobianVarieties.Generalized.Construction
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.CommGroupRelativeLaw
import Nyll.JacobianVarieties.Generalized.GeometricModulusFamilySumOverlap
import Nyll.JacobianVarieties.Generalized.PicardZeroChartDifference
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.ReducedSmoothOverField
import Mathlib.AlgebraicGeometry.Gluing

/-! # Gluing the actual divisor atlas over an arbitrary field

The geometric full-modulus condition identifies the corrected family sums on
the original reduced chart overlaps. The original open cover therefore glues
them directly, without requiring a reduced tensor product of extension fields.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
    ((modulusComplement (modulusCurveMap D)).ι ≫ c))
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ c) G.X.hom)
  (hmod : geometricRegularMapHasModulus c D G (Over.homMk q.1 q.2))

include hmod

/-- The corrected sums agree on the original atlas overlaps over the ground field. -/
theorem geometricModulusAtlas_localSum_compatible
    {T : Over (Spec (CommRingCat.of K))} [IsReduced T.left]
    {x : (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.obj (op T)}
    (atlas : ModulusDivisorAtlas c D ε T x) (i j : atlas.cover.I₀) :
    pullback.fst (atlas.cover.f i) (atlas.cover.f j) ≫
        (modulusFamilySum c D ε (commGroupRelativeLaw G)
          (commGroupRelativeLaw_isCommutative G) q (atlas.divisor i) (atlas.supported i)).1 =
      pullback.snd (atlas.cover.f i) (atlas.cover.f j) ≫
        (modulusFamilySum c D ε (commGroupRelativeLaw G)
          (commGroupRelativeLaw_isCommutative G) q (atlas.divisor j) (atlas.supported j)).1 := by
  let f := pullback.fst (atlas.cover.f i) (atlas.cover.f j)
  let g := pullback.snd (atlas.cover.f i) (atlas.cover.f j)
  let t := f ≫ (atlas.cover.f i ≫ T.hom)
  have hg : g ≫ (atlas.cover.f j ≫ T.hom) = t := by
    simpa only [Category.assoc] using
      (congrArg (fun u => u ≫ T.hom)
        (pullback.condition (f := atlas.cover.f i) (g := atlas.cover.f j))).symm
  have : IsReduced (pullback (atlas.cover.f i) (atlas.cover.f j)) :=
    isReduced_of_isOpenImmersion (f ≫ atlas.cover.f i)
  have : IsReduced (Over.mk t).left := by
    change IsReduced (pullback (atlas.cover.f i) (atlas.cover.f j))
    infer_instance
  obtain ⟨hz₀, hz₁, hη⟩ := atlas.overlap_zeroClasses
    i j f (show f ≫ (atlas.cover.f i ≫ T.hom) = t from rfl) g hg pullback.condition
  have hs := geometricModulusFamilySum_eq_of_zeroSheafClass c D
    (Over.homMk ε.1 ε.2) G (Over.homMk q.1 q.2) hmod (T := Over.mk t)
    ((atlas.divisor i).pullbackAlong f (show f ≫ (atlas.cover.f i ≫ T.hom) = t from rfl))
    ((atlas.supported i).pullbackAlong f rfl)
    ((atlas.divisor j).pullbackAlong g hg) ((atlas.supported j).pullbackAlong g hg)
    hz₀ hz₁ hη
  have hn₀ := modulusFamilySum_naturality c D ε (commGroupRelativeLaw G)
    (commGroupRelativeLaw_isCommutative G) q (atlas.divisor i) (atlas.supported i)
    f (show f ≫ (atlas.cover.f i ≫ T.hom) = t from rfl)
  have hn₁ := modulusFamilySum_naturality c D ε (commGroupRelativeLaw G)
    (commGroupRelativeLaw_isCommutative G) q (atlas.divisor j) (atlas.supported j) g hg
  exact (congrArg Subtype.val hn₀).trans
    ((congrArg Subtype.val hs).trans (congrArg Subtype.val hn₁).symm)

/-- The actual corrected sums glue over the original ground field. -/
def geometricModulusAtlasSum
    {T : Over (Spec (CommRingCat.of K))} [IsReduced T.left]
    {x : (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.obj (op T)}
    (atlas : ModulusDivisorAtlas c D ε T x) : SchemeHomOver T.hom G.X.hom := by
  let fs := fun j => (modulusFamilySum c D ε (commGroupRelativeLaw G)
    (commGroupRelativeLaw_isCommutative G) q (atlas.divisor j) (atlas.supported j)).1
  have hfs := geometricModulusAtlas_localSum_compatible c D ε G q hmod atlas
  refine ⟨atlas.cover.openCover.glueMorphisms fs hfs, ?_⟩
  apply atlas.cover.openCover.hom_ext
  intro j
  rw [← Category.assoc, atlas.cover.openCover.ι_glueMorphisms fs hfs j]
  exact (modulusFamilySum c D ε (commGroupRelativeLaw G)
    (commGroupRelativeLaw_isCommutative G) q (atlas.divisor j) (atlas.supported j)).2

/-- The glued map restricts to its actual corrected divisor sum on every chart. -/
theorem geometricModulusAtlasSum_restrict
    {T : Over (Spec (CommRingCat.of K))} [IsReduced T.left]
    {x : (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.obj (op T)}
    (atlas : ModulusDivisorAtlas c D ε T x) (j : atlas.cover.I₀) :
    atlas.cover.f j ≫ (geometricModulusAtlasSum c D ε G q hmod atlas).1 =
      (modulusFamilySum c D ε (commGroupRelativeLaw G)
        (commGroupRelativeLaw_isCommutative G) q (atlas.divisor j) (atlas.supported j)).1 := by
  let fs := fun j => (modulusFamilySum c D ε (commGroupRelativeLaw G)
    (commGroupRelativeLaw_isCommutative G) q (atlas.divisor j) (atlas.supported j)).1
  have hfs := geometricModulusAtlas_localSum_compatible c D ε G q hmod atlas
  change atlas.cover.f j ≫ atlas.cover.openCover.glueMorphisms fs hfs = fs j
  exact atlas.cover.openCover.ι_glueMorphisms fs hfs j

/-- On a field-valued point, the glued map is the actual pulled chart sum. -/
theorem geometricModulusAtlasSum_fieldPoint
    {T : Over (Spec (CommRingCat.of K))} [IsReduced T.left]
    {x : (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.obj (op T)}
    (atlas : ModulusDivisorAtlas c D ε T x)
    {L : Type u} [Field L] {s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)}
    (p : Over.mk s ⟶ T) :
    ∃ (j : atlas.cover.I₀)
      (z : Over.mk s ⟶ Over.mk (atlas.cover.f j ≫ T.hom)),
      z ≫ (Over.homMk (atlas.cover.f j) : Over.mk (atlas.cover.f j ≫ T.hom) ⟶ T) = p ∧
      GoodReductionJacobian.schemeHomOverComp p.left (Over.w p)
          (geometricModulusAtlasSum c D ε G q hmod atlas) =
        modulusFamilySum c D ε (commGroupRelativeLaw G)
          (commGroupRelativeLaw_isCommutative G) q
          ((atlas.divisor j).pullbackAlong z.left (Over.w z))
          ((atlas.supported j).pullbackAlong z.left (Over.w z)) := by
  obtain ⟨j, z, hz⟩ := atlas.exists_fieldPoint_lift p
  refine ⟨j, z, hz, ?_⟩
  apply Subtype.ext
  have hell : z.left ≫ atlas.cover.f j = p.left := congrArg Over.Hom.left hz
  change p.left ≫ (geometricModulusAtlasSum c D ε G q hmod atlas).1 = _
  rw [← hell, Category.assoc, geometricModulusAtlasSum_restrict c D ε G q hmod atlas j]
  exact congrArg Subtype.val (modulusFamilySum_naturality c D ε (commGroupRelativeLaw G)
    (commGroupRelativeLaw_isCommutative G) q (atlas.divisor j) (atlas.supported j)
    z.left (Over.w z))

/-- For positive modulus degree, the actual generalized Jacobian carries the
regular map constructed over the ground field from geometric full modulus. -/
def geometricModulusRegularMap (hd : 0 < d) :
    SchemeHomOver (groupScheme c D).X.hom G.X.hom := by
  have : SmoothOfRelativeDimension (SmoothProperCurve.geometricGenus K c + (d - 1))
      (groupScheme c D).X.hom := (geometry c D).1
  have : Smooth (groupScheme c D).X.hom :=
    SmoothOfRelativeDimension.smooth
      (SmoothProperCurve.geometricGenus K c + (d - 1)) _
  have : IsReduced (groupScheme c D).X.left :=
    isReduced_of_smooth_over_field (g := (groupScheme c D).X.hom) inferInstance
  exact geometricModulusAtlasSum c D ε G q hmod
    (generalizedJacobianDivisorAtlas c D ε hd)

end AlgebraicGeometry.GeneralizedJacobian
