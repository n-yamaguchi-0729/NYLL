/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareRawSurjectivity

/-!
# Injectivity of the actual total Poincaré frame comparison

An equality of modulus classes identifies the underlying Poincaré pullbacks.
Ordinary Poincaré uniqueness then identifies their parameter maps. The already
proved fixed-parameter frame injection identifies the remaining scalar frames.
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

/-- A modulus representative of a raw frame retains its actual Poincaré parameter. -/
theorem poincareRawFrame_underlyingIso {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} (g : SchemeHomOver t J.toBase)
    (x : (liftedScalarFramePresheaf (pullback.snd (modulusBaseMap D) J.toBase)
      (poincareModulusBundle D h)).obj (op (Over.mk g.1)))
    (M : RigidifiedLineBundle (modulusBaseChange c (modulusCurveMap D) t))
    (hx : ((poincareRawFrameToModulusZero D h).app (op (Over.mk t))
      ⟨Over.homMk g.1 g.2, x⟩).val = RigidifiedLineBundle.classOf M) :
    Nonempty ((h.poincare.pullbackAlong g).L ≅ M.L) := by
  rcases g with ⟨g, hg⟩
  subst t
  let p : Over.mk (g ≫ J.toBase) ⟶ Over.mk J.toBase := Over.homMk g rfl
  have hid : ((relativeTotalForgetIso J.toBase).inv.app (Over.mk p)).left = 𝟙 T := by
    change (𝟙 T) ≫ (𝟙 T) ≫ (𝟙 T) = 𝟙 T
    rw [Category.id_comp, Category.id_comp]
  have he := Functor.map_op_apply_eq_self
    (G := modulusPicardZeroPresheaf c (modulusCurveMap D))
    ((relativeTotalForgetIso J.toBase).inv.app (Over.mk p)) hid
    ((modulusFramesToPicardZero D J.toBase h.poincare.isInvertible
      (poincareUnderlying_fibrewiseZero h)).app (op (Over.mk g)) x)
  exact (exists_modulusFramePicardClass_eq_iff D J.toBase
    h.poincare.isInvertible (Over.mk g) M).mp
      ⟨x.down, (congrArg Subtype.val he).symm.trans hx⟩

/-- Distinct actual total scalar-frame classes remain distinct modulus zero classes. -/
theorem poincareRawFrameToModulusZero_injective (T : Over (Spec (CommRingCat.of K))) :
    Function.Injective ((poincareRawFrameToModulusZero D h).app (op T)) := by
  rintro ⟨g, x⟩ ⟨g', y⟩ hxy
  obtain ⟨M, hM⟩ := Quotient.exists_rep
    (((poincareRawFrameToModulusZero D h).app (op T) ⟨g, x⟩).val)
  have ex := poincareRawFrame_underlyingIso D h
    (⟨g.left, Over.w g⟩ : SchemeHomOver T.hom J.toBase) x M hM.symm
  have ey := poincareRawFrame_underlyingIso D h
    (⟨g'.left, Over.w g'⟩ : SchemeHomOver T.hom J.toBase) y M
    ((congrArg Subtype.val hxy).symm.trans hM.symm)
  have hg : g = g' := by
    apply Over.OverMorphism.ext
    exact congrArg Subtype.val (h.ext_of_iso T.hom
      (⟨g.left, Over.w g⟩ : SchemeHomOver T.hom J.toBase)
      (⟨g'.left, Over.w g'⟩ : SchemeHomOver T.hom J.toBase)
      ⟨ex.some ≪≫ ey.some.symm⟩)
  subst g'
  apply congrArg (fun z => (⟨g, z⟩ : (poincareRawFrameFamily D h).obj (op T)))
  let e := (relativeTotalForgetIso J.toBase).inv.app (Over.mk g)
  have hi := (CategoryTheory.mono_iff_injective
    ((modulusPicardZeroPresheaf c (modulusCurveMap D)).map e.op)).mp inferInstance
  apply ULift.ext
  apply modulusFramePicardClass_injective D J.toBase h.poincare.isInvertible
    (Over.mk g.left)
  exact congrArg Subtype.val (hi hxy)

/-- The raw total comparison is a monomorphism of actual presheaves. -/
instance poincareRawFrameToModulusZero_mono : Mono (poincareRawFrameToModulusZero D h) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro T
  exact (CategoryTheory.mono_iff_injective _).mpr
    (poincareRawFrameToModulusZero_injective D h T.unop)

end AlgebraicGeometry.GeneralizedJacobian
