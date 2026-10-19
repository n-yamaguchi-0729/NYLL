/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareRepresentability

/-!
# Compatibility of the Poincaré parameter with forgetting the modulus

The ordinary relative class of an actual frame is the class of its Poincaré
pullback. Local actual frames then give the same assertion for the total
represented family, using separation of the ordinary Picard sheaf.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)

/-- An actual scalar frame retains exactly the ordinary class of its parameter. -/
theorem poincareRawFrameToModulusZero_forget :
    poincareRawFrameToModulusZero D h ≫ forgetModulusZeroPresheaf c (modulusCurveMap D) =
      poincareRawFrameToPicard D h ≫ (Unrigidified.zeroPresheafIso ε).inv := by
  ext T x
  obtain ⟨M, hM⟩ := Quotient.exists_rep
    (((poincareRawFrameToModulusZero D h).app T x).val)
  have e := poincareRawFrame_underlyingIso D h
    (⟨x.1.left, Over.w x.1⟩ : SchemeHomOver T.unop.hom J.toBase) x.2 M hM.symm
  apply Subtype.ext
  change forgetModulusClasses c (modulusCurveMap D) T.unop.hom
      ((poincareRawFrameToModulusZero D h).app T x).val =
    Unrigidified.forget ε T.unop.hom (h.representableBy.homEquiv x.1).val
  rw [← hM]
  exact Quot.sound (Unrigidified.baseTwist_of_iso e.some.symm)

/-- The ordinary class of a total frame-family section is its actual parameter class. -/
theorem poincareFrameTotalToModulusPicardZero_forget :
    poincareFrameTotalToModulusPicardZero D h ≫
        (forgetModulusZeroSheaf c (modulusCurveMap D)).hom =
      poincareFrameTotalToPicard D h ≫ (Unrigidified.zeroPresheafIso ε).inv ≫
        toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
          (Unrigidified.zeroPresheaf c) := by
  let η : modulusPicardZeroPresheaf c (modulusCurveMap D) ⟶
      (modulusPicardZeroSheaf c (modulusCurveMap D)).obj :=
    toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardZeroPresheaf c (modulusCurveMap D))
  let ν : Unrigidified.zeroPresheaf c ⟶ (ordinaryRelativePicardZeroSheaf c).obj :=
    toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (Unrigidified.zeroPresheaf c)
  let a := poincareFrameTotalToModulusPicardZero D h ≫
    (forgetModulusZeroSheaf c (modulusCurveMap D)).hom
  let b : poincareFrameTotalFamily D h ⟶ (ordinaryRelativePicardZeroSheaf c).obj :=
    poincareFrameTotalToPicard D h ≫ (Unrigidified.zeroPresheafIso ε).inv ≫ ν
  have hab : poincareRawToFrameFamily D h ≫ a = poincareRawToFrameFamily D h ≫ b := by
    have hc : poincareRawToFrameFamily D h ≫ poincareFrameTotalToModulusPicardZero D h =
        poincareRawFrameToModulusZero D h ≫ η :=
      poincareRawToFrameFamily_comp_toModulusPicardZero D h
    have hf : η ≫
          (forgetModulusZeroSheaf c (modulusCurveMap D)).hom =
      forgetModulusZeroPresheaf c (modulusCurveMap D) ≫ ν :=
      (toSheafify_naturality (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (forgetModulusZeroPresheaf c (modulusCurveMap D))).symm
    dsimp only [a, b]
    rw [← Category.assoc, hc,
      Category.assoc, hf, ← Category.assoc,
      poincareRawFrameToModulusZero_forget, Category.assoc]
    rfl
  change a = b
  ext T x
  apply (((isSheaf_iff_isSheaf_of_type _ _).1
    (ordinaryRelativePicardZeroSheaf c).2).isSeparated _
      (Presheaf.imageSieve_mem (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (poincareRawToFrameFamily D h) x)).ext
  rintro Y f ⟨s, hs⟩
  have ha := a.naturality_apply f.op x
  have hb := b.naturality_apply f.op x
  change (ordinaryRelativePicardZeroSheaf c).obj.map f.op (a.app T x) =
    (ordinaryRelativePicardZeroSheaf c).obj.map f.op (b.app T x)
  rw [← ha, ← hb, ← hs]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app hab (op Y)) s

end AlgebraicGeometry.GeneralizedJacobian
