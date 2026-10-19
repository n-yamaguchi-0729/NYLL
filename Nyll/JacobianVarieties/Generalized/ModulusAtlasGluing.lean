/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardZeroChartDifference
import Nyll.JacobianVarieties.Generalized.ModulusFamilySumOverlap
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.ReducedSmoothOverField
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing actual regular modulus sums over an algebraically closed field

The actual divisor atlas has regular corrected sums. Its original zero-sheaf
class identifies their restrictions, and full modulus invariance makes these
regular maps equal on the reduced overlaps. Hence they glue to a morphism
on the actual constructed generalized Jacobian.
-/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.GeneralizedJacobian

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  [GeometricallyIntegral M.toBase]
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
    ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))
  {B : Scheme.{u}} {b : B ⟶ Spec (CommRingCat.of K)} [IsSeparated b]
  (G : RelativeGroupLaw K b) (hc : G.IsCommutative)
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) b)
  {A : Type w} [AddCommGroup A]
  (v : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) b → A) (hv : Function.Injective v)
  (hv₁ : v (G.one (𝟙 _)) = 0)
  (hv₂ : ∀ x y, v (G.mul (𝟙 _) x y) = v x + v y)
  (a : Place K F → A)
  (ha : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase),
    a (M.pointEquivPlace
        ⟨x.1 ≫ (modulusComplement (modulusCurveMap D)).ι, (Category.assoc _ _ _).trans x.2⟩) =
      v (NeronModelInfra.schemeHomOverComp x q))
  (hmod : (M.cartierModulus (modulusCurveIdeal D)
    (modulusCurveIdeal_isInvertible D)).HasModulus a)


include hv hv₁ hv₂ ha hmod in
/-- The actual corrected local maps agree on each overlap of the specified divisor atlas. -/
theorem modulusAtlas_localSum_compatible
    {T : Over (Spec (CommRingCat.of K))} [LocallyOfFiniteType T.hom] [IsReduced T.left]
    {x : (modulusPicardZeroSheaf M.toBase (modulusCurveMap D)).obj.obj (op T)}
    (atlas : ModulusDivisorAtlas M.toBase D ε T x) (i j : atlas.cover.I₀) :
    pullback.fst (atlas.cover.f i) (atlas.cover.f j) ≫
        (modulusFamilySum M.toBase D ε G hc q (atlas.divisor i) (atlas.supported i)).1 =
      pullback.snd (atlas.cover.f i) (atlas.cover.f j) ≫
        (modulusFamilySum M.toBase D ε G hc q (atlas.divisor j) (atlas.supported j)).1 := by
  let f := pullback.fst (atlas.cover.f i) (atlas.cover.f j)
  let g := pullback.snd (atlas.cover.f i) (atlas.cover.f j)
  let t := f ≫ (atlas.cover.f i ≫ T.hom)
  have hg : g ≫ (atlas.cover.f j ≫ T.hom) = t := by
    simpa only [Category.assoc] using
      (congrArg (fun u => u ≫ T.hom)
        (pullback.condition (f := atlas.cover.f i) (g := atlas.cover.f j))).symm
  have : LocallyOfFiniteType t := inferInstance
  have : IsReduced (pullback (atlas.cover.f i) (atlas.cover.f j)) :=
    isReduced_of_isOpenImmersion (f ≫ atlas.cover.f i)
  obtain ⟨hz₀, hz₁, hη⟩ := atlas.overlap_zeroClasses
    i j f (show f ≫ (atlas.cover.f i ≫ T.hom) = t from rfl) g hg pullback.condition
  have hs := M.modulusFamilySum_eq_of_zeroSheafClass D ε G hc q v hv hv₁ hv₂ a ha hmod t
    ((atlas.divisor i).pullbackAlong f rfl) ((atlas.supported i).pullbackAlong f rfl)
    ((atlas.divisor j).pullbackAlong g hg) ((atlas.supported j).pullbackAlong g hg)
    hz₀ hz₁ hη
  have hn₀ := modulusFamilySum_naturality M.toBase D ε G hc q
    (atlas.divisor i) (atlas.supported i) f (show f ≫ (atlas.cover.f i ≫ T.hom) = t from rfl)
  have hn₁ := modulusFamilySum_naturality M.toBase D ε G hc q
    (atlas.divisor j) (atlas.supported j) g hg
  exact (congrArg Subtype.val hn₀).trans
    ((congrArg Subtype.val hs).trans (congrArg Subtype.val hn₁).symm)

/-- Gluing the actual regular sums using the proved full-modulus compatibility. -/
def modulusAtlasSum
    {T : Over (Spec (CommRingCat.of K))} [LocallyOfFiniteType T.hom] [IsReduced T.left]
    {x : (modulusPicardZeroSheaf M.toBase (modulusCurveMap D)).obj.obj (op T)}
    (atlas : ModulusDivisorAtlas M.toBase D ε T x) : SchemeHomOver T.hom b := by
  let fs := fun j => (modulusFamilySum M.toBase D ε G hc q
    (atlas.divisor j) (atlas.supported j)).1
  have hfs := M.modulusAtlas_localSum_compatible D ε G hc q v hv hv₁ hv₂ a ha hmod atlas
  refine ⟨atlas.cover.openCover.glueMorphisms fs hfs, ?_⟩
  apply atlas.cover.openCover.hom_ext
  intro j
  rw [← Category.assoc, atlas.cover.openCover.ι_glueMorphisms fs hfs j]
  exact (modulusFamilySum M.toBase D ε G hc q (atlas.divisor j) (atlas.supported j)).2

/-- The glued morphism restricts to the specified regular sum on every original chart. -/
theorem modulusAtlasSum_restrict
    {T : Over (Spec (CommRingCat.of K))} [LocallyOfFiniteType T.hom] [IsReduced T.left]
    {x : (modulusPicardZeroSheaf M.toBase (modulusCurveMap D)).obj.obj (op T)}
    (atlas : ModulusDivisorAtlas M.toBase D ε T x) (j : atlas.cover.I₀) :
    atlas.cover.f j ≫ (M.modulusAtlasSum D ε G hc q v hv hv₁ hv₂ a ha hmod atlas).1 =
      (modulusFamilySum M.toBase D ε G hc q (atlas.divisor j) (atlas.supported j)).1 := by
  let fs := fun j => (modulusFamilySum M.toBase D ε G hc q
    (atlas.divisor j) (atlas.supported j)).1
  have hfs := M.modulusAtlas_localSum_compatible D ε G hc q v hv hv₁ hv₂ a ha hmod atlas
  change atlas.cover.f j ≫ atlas.cover.openCover.glueMorphisms fs hfs = fs j
  exact atlas.cover.openCover.ι_glueMorphisms fs hfs j

/-- A field-valued point lifts to an actual affine chart, and the glued map
there evaluates the pulled supported divisor. The field may extend the ground field. -/
theorem modulusAtlasSum_fieldPoint
    {T : Over (Spec (CommRingCat.of K))} [LocallyOfFiniteType T.hom] [IsReduced T.left]
    {x : (modulusPicardZeroSheaf M.toBase (modulusCurveMap D)).obj.obj (op T)}
    (atlas : ModulusDivisorAtlas M.toBase D ε T x)
    {L : Type u} [Field L] {s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)}
    (p : Over.mk s ⟶ T) :
    ∃ (j : atlas.cover.I₀)
      (z : Over.mk s ⟶ Over.mk (atlas.cover.f j ≫ T.hom)),
      z ≫ (Over.homMk (atlas.cover.f j) : Over.mk (atlas.cover.f j ≫ T.hom) ⟶ T) = p ∧
      GoodReductionJacobian.schemeHomOverComp p.left (Over.w p)
          (M.modulusAtlasSum D ε G hc q v hv hv₁ hv₂ a ha hmod atlas) =
        modulusFamilySum M.toBase D ε G hc q
          ((atlas.divisor j).pullbackAlong z.left (Over.w z))
          ((atlas.supported j).pullbackAlong z.left (Over.w z)) := by
  obtain ⟨j, z, hz⟩ := atlas.exists_fieldPoint_lift p
  refine ⟨j, z, hz, ?_⟩
  apply Subtype.ext
  have hell : z.left ≫ atlas.cover.f j = p.left := congrArg Over.Hom.left hz
  change p.left ≫ (M.modulusAtlasSum D ε G hc q v hv hv₁ hv₂ a ha hmod atlas).1 = _
  rw [← hell, Category.assoc,
    M.modulusAtlasSum_restrict D ε G hc q v hv hv₁ hv₂ a ha hmod atlas j]
  exact congrArg Subtype.val (modulusFamilySum_naturality M.toBase D ε G hc q
    (atlas.divisor j) (atlas.supported j) z.left (Over.w z))

/-- The actual regular map on the constructed generalized Jacobian, obtained
from the full modulus condition and the concrete affine divisor atlas. -/
def modulusRegularMap (hd : 0 < d) : SchemeHomOver (groupScheme M.toBase D).X.hom b := by
  have := (geometry M.toBase D).1
  have : LocallyOfFiniteType (groupScheme M.toBase D).X.hom := (geometry M.toBase D).2.1
  have : Smooth (groupScheme M.toBase D).X.hom :=
    SmoothOfRelativeDimension.smooth
      (SmoothProperCurve.geometricGenus K M.toBase + (d - 1)) _
  have : IsReduced (groupScheme M.toBase D).X.left :=
    isReduced_of_smooth_over_field (g := (groupScheme M.toBase D).X.hom) inferInstance
  exact M.modulusAtlasSum D ε G hc q v hv hv₁ hv₂ a ha hmod
    (generalizedJacobianDivisorAtlas M.toBase D ε hd)

end AlgebraicCurve.CurveModel
