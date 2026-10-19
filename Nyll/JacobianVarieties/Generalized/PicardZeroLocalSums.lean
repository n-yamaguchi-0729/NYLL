/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardZeroDivisorCharts
import Nyll.JacobianVarieties.Generalized.Construction
import Nyll.JacobianVarieties.Albanese.OpenCurveSumChoice

/-!
# Actual regular local sums on the constructed generalized Jacobian

The affine divisor atlas below is constructed from the original zero-sheaf
section. Its local sum maps are actual morphisms defined by the proved
open-curve divisor representers. Their compatibility is a separate modulus
argument; it is not included as an assumption in the atlas construction.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra
open GoodReductionJacobian JacobianVarieties.Albanese

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
    ((modulusComplement (modulusCurveMap D)).ι ≫ c))

/-- Actual affine divisor representatives of a specified zero-sheaf section. -/
structure ModulusDivisorAtlas (T : Over (Spec (CommRingCat.of K)))
    (x : (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.obj (op T)) where
  /-- The actual affine open cover. -/
  cover : Scheme.AffineOpenCover.{u, u} T.left
  /-- The chosen divisor degree on each open. -/
  degree : cover.I₀ → ℕ
  /-- The actual rigidified line bundle on each open. -/
  bundle (j : cover.I₀) : RigidifiedLineBundle
    (modulusBaseChange c (modulusCurveMap D) (cover.f j ≫ T.hom))
  /-- Its actual Euler degree-zero membership. -/
  degree_zero (j : cover.I₀) : RigidifiedLineBundle.classOf (bundle j) ∈
    (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj
      (op (Over.mk (cover.f j ≫ T.hom)))
  /-- The supported effective divisor representing the twisted bundle. -/
  divisor (j : cover.I₀) : RelEffCartierDiv c (degree j) (cover.f j ≫ T.hom)
  /-- The divisor avoids the entire modulus. -/
  supported (j : cover.I₀) : (divisor j).SupportedIn (modulusComplement (modulusCurveMap D))
  /-- The class equality preserves the full modulus frame. -/
  class_eq (j : cover.I₀) : RigidifiedLineBundle.classOf (bundle j) *
      RigidifiedLineBundle.classOf (modulusCanonicalPointBundle c (modulusCurveMap D)
        (schemeHomOverComp (cover.f j ≫ T.hom) (Category.comp_id _) ε)) ^ degree j =
    modulusDivisorFamilyClass c (modulusCurveMap D) (divisor j) (supported j)
  /-- The actual bundle represents the restriction of the specified section. -/
  represents (j : cover.I₀) :
    (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardZeroPresheaf c (modulusCurveMap D))).app
        (op (Over.mk (cover.f j ≫ T.hom)))
        ⟨RigidifiedLineBundle.classOf (bundle j), degree_zero j⟩ =
      (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.map
        (Over.homMk (cover.f j) : Over.mk (cover.f j ≫ T.hom) ⟶ T).op x

/-- The actual divisor atlas is supplied without a local representation assumption. -/
theorem nonempty_modulusDivisorAtlas (hd : 0 < d)
    (T : Over (Spec (CommRingCat.of K))) [IsLocallyNoetherian T.left]
    (x : (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.obj (op T)) :
    Nonempty (ModulusDivisorAtlas c D ε T x) := by
  classical
  obtain ⟨U, hU⟩ := modulusPicardZero_exists_affineOpenCover_divisors c D hd ε T x
  choose n M hM E hE he hx using hU
  exact ⟨⟨U, n, M, hM, E, hE, he, hx⟩⟩

/-- A choice of actual charts, supported families and whole-modulus identifications. -/
def modulusDivisorAtlas (hd : 0 < d)
    (T : Over (Spec (CommRingCat.of K))) [IsLocallyNoetherian T.left]
    (x : (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.obj (op T)) :
    ModulusDivisorAtlas c D ε T x :=
  Classical.choice (nonempty_modulusDivisorAtlas c D ε hd T x)

/-- The universal section of the original modulus Picard-zero sheaf. -/
def generalizedJacobianUniversalClass :
    (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.obj (op (groupScheme c D).X) :=
  (picardZeroRepresentable c D).homEquiv (𝟙 (groupScheme c D).X)

/-- The constructed generalized Jacobian itself has the actual divisor atlas. -/
def generalizedJacobianDivisorAtlas (hd : 0 < d) :
    ModulusDivisorAtlas c D ε (groupScheme c D).X
      (generalizedJacobianUniversalClass c D) := by
  have : LocallyOfFiniteType (groupScheme c D).X.hom := (geometry c D).2.1
  have : IsLocallyNoetherian (groupScheme c D).X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (groupScheme c D).X.hom
  exact modulusDivisorAtlas c D ε hd (groupScheme c D).X
    (generalizedJacobianUniversalClass c D)

variable {B : Scheme.{u}} {b : B ⟶ Spec (CommRingCat.of K)} [IsSeparated b]
  (G : RelativeGroupLaw K b) (hc : G.IsCommutative)
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ c) b)

/-- The regular corrected sum of an actual supported divisor family. -/
def modulusFamilySum {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} {n : ℕ}
    (E : RelEffCartierDiv c n t) (hE : E.SupportedIn (modulusComplement (modulusCurveMap D))) :
    SchemeHomOver t b :=
  let S := chooseOpenCurveSum c (modulusComplement (modulusCurveMap D)) G q n hc ε
  correctedSupportedDivisorSum c (modulusComplement (modulusCurveMap D)) S.universal G S.sum
    (schemeHomOverComp ε.1 ε.2 q) E hE

/-- These are actual morphisms and retain pullback along every parameter map. -/
theorem modulusFamilySum_naturality {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec (CommRingCat.of K)} {n : ℕ}
    (E : RelEffCartierDiv c n t) (hE : E.SupportedIn (modulusComplement (modulusCurveMap D)))
    (f : T' ⟶ T) (hf : f ≫ t = t') :
    schemeHomOverComp f hf (modulusFamilySum c D ε G hc q E hE) =
      modulusFamilySum c D ε G hc q (E.pullbackAlong f hf) (hE.pullbackAlong f hf) :=
  correctedSupportedDivisorSum_naturality c (modulusComplement (modulusCurveMap D))
    (chooseOpenCurveSum c (modulusComplement (modulusCurveMap D)) G q n hc ε).universal G
    (chooseOpenCurveSum c (modulusComplement (modulusCurveMap D)) G q n hc ε).sum
    (schemeHomOverComp ε.1 ε.2 q) E hE f hf

/-- The specified regular corrected sum on an actual affine chart of the constructed group. -/
def generalizedJacobianLocalSum (hd : 0 < d)
    (j : (generalizedJacobianDivisorAtlas c D ε hd).cover.I₀) :
    SchemeHomOver ((generalizedJacobianDivisorAtlas c D ε hd).cover.f j ≫
      (groupScheme c D).X.hom) b :=
  modulusFamilySum c D ε G hc q
    ((generalizedJacobianDivisorAtlas c D ε hd).divisor j)
    ((generalizedJacobianDivisorAtlas c D ε hd).supported j)

end AlgebraicGeometry.GeneralizedJacobian
