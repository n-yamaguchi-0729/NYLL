/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareRawFamily
import Nyll.JacobianVarieties.Generalized.PoincareLocalClassification
import Nyll.JacobianVarieties.Generalized.ModulusFramePicardImage
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Local surjectivity onto actual modulus Picard-zero classes

Trivialize the restriction of the underlying line bundle to the chosen curve
section. On that actual open cover, ordinary Poincaré classification and the
image theorem for modulus frames supply a raw frame representing the given
modulus-rigidified class. The chosen modulus trivialization is retained.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra GoodReductionJacobian
open SchemeTheory.WeilRestriction AlgebraicGeometry.RelPicard
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)

/-- An actual underlying Poincaré isomorphism supplies a raw frame with the
given compatible modulus class, not merely the same unrigidified class. -/
theorem exists_poincareRawFrame_of_underlying_iso {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)}
    (M : RigidifiedLineBundle (modulusBaseChange c (modulusCurveMap D) t))
    (g : SchemeHomOver t J.toBase)
    (e : Nonempty ((h.poincare.pullbackAlong g).L ≅ M.L)) :
    ∃ x : (poincareRawFrameFamily D h).obj (op (Over.mk t)),
      ((poincareRawFrameToModulusZero D h).app (op (Over.mk t)) x).val =
        RigidifiedLineBundle.classOf M := by
  rcases g with ⟨g, hg⟩
  subst t
  obtain ⟨x, hx⟩ := (exists_modulusFramePicardClass_eq_iff D J.toBase
    h.poincare.isInvertible (Over.mk g) M).mpr e
  refine ⟨⟨Over.homMk g rfl, ULift.up x⟩, ?_⟩
  let p : Over.mk (g ≫ J.toBase) ⟶ Over.mk J.toBase := Over.homMk g rfl
  have hid : ((relativeTotalForgetIso J.toBase).inv.app (Over.mk p)).left = 𝟙 T := by
    change (𝟙 T) ≫ (𝟙 T) ≫ (𝟙 T) = 𝟙 T
    rw [Category.id_comp, Category.id_comp]
  have he := Functor.map_op_apply_eq_self
    (G := modulusPicardZeroPresheaf c (modulusCurveMap D))
    ((relativeTotalForgetIso J.toBase).inv.app (Over.mk p)) hid
    ((modulusFramesToPicardZero D J.toBase h.poincare.isInvertible
      (poincareUnderlying_fibrewiseZero h)).app (op (Over.mk g)) (ULift.up x))
  exact (congrArg Subtype.val he).trans hx

/-- Every modulus Picard-zero class is locally the image of an actual Poincaré
scalar frame, on the open cover trivializing its restriction to the section. -/
instance poincareRawFrameToModulusZero_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (poincareRawFrameToModulusZero D h) := by
  constructor
  intro T x
  rcases x with ⟨x, hx⟩
  induction x using Quotient.ind with
  | _ M =>
    let L : Unrigidified.LineBundle c T.hom := ⟨M.L, M.isInvertible⟩
    have hL : Unrigidified.FibrewiseZero L := hx
    let V := (Unrigidified.localRigidificationCover ε L).val
    let U (j : V.I₀) : Over (Spec (CommRingCat.of K)) := Over.mk (V.f j ≫ T.hom)
    let f (j : V.I₀) : U j ⟶ T := Over.homMk (V.f j) rfl
    have hcover : Sieve.ofArrows U f ∈
        (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) T := by
      rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      apply Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage
      exact V.mem_grothendieckTopology
    apply (Scheme.fppfTopology.over (Spec (CommRingCat.of K))).superset_covering ?_ hcover
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro j
    let s : SchemeHomOver (V.f j ≫ T.hom) T.hom := ⟨V.f j, rfl⟩
    let N := M.pullback (baseChangeSnd c s) (baseChangeSnd (modulusCurveMap D ≫ c) s)
      (modulusBaseChange_naturality c (modulusCurveMap D) s)
    obtain ⟨y, hy⟩ := exists_poincareRawFrame_of_underlying_iso D h N
      (localPoincareMap h L hL j) ⟨localPoincareIso h L hL j⟩
    refine ⟨y, Subtype.ext ?_⟩
    exact hy

end AlgebraicGeometry.GeneralizedJacobian
