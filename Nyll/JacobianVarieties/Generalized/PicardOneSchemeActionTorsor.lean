/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOneSchemeAction
import Nyll.JacobianVarieties.Generalized.PicardOneSchemeTorsor

/-! # The actual canonical Picard-one action satisfies the scheme torsor identity -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.GeneralizedJacobian

private def tensorBinaryProductIso {B : Type u} [Category.{v} B]
    [CartesianMonoidalCategory B] (X Y : B) : X ⊗ Y ≅ X ⨯ Y where
  hom := Limits.prod.lift (fst X Y) (snd X Y)
  inv := lift Limits.prod.fst Limits.prod.snd
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, Limits.prod.lift_fst, Category.id_comp]
    · simp only [Category.assoc, lift_snd, Limits.prod.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply Limits.prod.hom_ext
    · simp only [Category.assoc, Limits.prod.lift_fst, lift_fst, Category.id_comp]
    · simp only [Category.assoc, Limits.prod.lift_snd, lift_snd, Category.id_comp]

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The canonical tensor action is the action component of the intrinsic scheme torsor iso. -/
theorem picardOneTensorAction_eq_productAction :
    (tensorBinaryProductIso (groupScheme c D).X (picardOne c D)).hom ≫
      picardOneAction c D = picardOneTensorAction c D := by
  let G := (groupScheme c D).X
  let P := picardOne c D
  let Z := modulusPicardZeroSheaf c (modulusCurveMap D)
  let Q := modulusPicardOneSheaf c (modulusCurveMap D)
  let q := (tensorBinaryProductIso G P).hom
  let e := tensorBinaryProductIso Z Q
  let E := (((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    (Type (u + 1))).mapIso e).app (op (G ⊗ P))).toEquiv
  let z := (picardOneActionProductRepresentable c D).homEquiv q
  let a : (Z ⊗ Q).obj.obj (op (G ⊗ P)) :=
    ((picardZeroRepresentable c D).homEquiv (fst G P),
      (picardOneRepresentable c D).homEquiv (snd G P))
  have hz' : E.symm z = a := by
    change ((Limits.prod.fst : Z ⨯ Q ⟶ Z).hom.app (op (G ⊗ P)) z,
      (Limits.prod.snd : Z ⨯ Q ⟶ Q).hom.app (op (G ⊗ P)) z) = _
    apply Prod.ext
    · exact (picardOneActionProductRepresentable_fst c D q).trans
        (congrArg (picardZeroRepresentable c D).homEquiv
          (Limits.prod.lift_fst (fst G P) (snd G P)))
    · exact (picardOneActionProductRepresentable_snd c D q).trans
        (congrArg (picardOneRepresentable c D).homEquiv
          (Limits.prod.lift_snd (fst G P) (snd G P)))
  have hz : z = E a := (E.apply_symm_apply z).symm.trans (congrArg E hz')
  have hc := picardOneTorsorIso_classifies c D q
  have ht := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun v : Z ⊗ Q ⟶ Q => v.hom)
      (modulusPicardOneTensorAction_torsor c (modulusCurveMap D))) (op (G ⊗ P))) a
  have hnew := picardOneTensorAction_classifies c D (fst G P) (snd G P)
  rw [lift_fst_snd, Category.id_comp] at hnew
  apply (picardOneRepresentable c D).homEquiv.injective
  have hfirst := picardOneSquareRepresentable_fst c D (q ≫ (picardOneTorsorIso c D).hom)
  change (picardOneRepresentable c D).homEquiv (q ≫ (picardOneTorsorIso c D).hom ≫
    Limits.prod.fst) = _
  refine (congrArg (picardOneRepresentable c D).homEquiv
    (Category.assoc q (picardOneTorsorIso c D).hom Limits.prod.fst).symm).trans ?_
  refine hfirst.symm.trans ?_
  refine (congrArg ((Limits.prod.fst : Q ⨯ Q ⟶ Q).hom.app (op (G ⊗ P))) hc).trans ?_
  change (Limits.prod.fst : Q ⨯ Q ⟶ Q).hom.app (op (G ⊗ P))
    ((modulusPicardOneSheafTorsorIso c (modulusCurveMap D)).hom.hom.app
      (op (G ⊗ P)) z) = _
  rw [hz]
  exact ht.trans hnew.symm

/-- The actual tensor-action torsor isomorphism, on Cartesian products of the same schemes. -/
def picardOneTensorTorsorIso :
    (groupScheme c D).X ⊗ picardOne c D ≅ picardOne c D ⊗ picardOne c D :=
  tensorBinaryProductIso (groupScheme c D).X (picardOne c D) ≪≫
    picardOneTorsorIso c D ≪≫ (tensorBinaryProductIso (picardOne c D) (picardOne c D)).symm

/-- Its first component is the canonical action whose unit and associativity are proved. -/
theorem picardOneTensorTorsorIso_fst :
    (picardOneTensorTorsorIso c D).hom ≫ fst _ _ = picardOneTensorAction c D := by
  change (tensorBinaryProductIso (groupScheme c D).X (picardOne c D)).hom ≫
    (picardOneTorsorIso c D).hom ≫
      lift Limits.prod.fst Limits.prod.snd ≫ fst _ _ = _
  rw [lift_fst]
  exact picardOneTensorAction_eq_productAction c D

/-- The action torsor isomorphism retains the second Picard-one point. -/
theorem picardOneTensorTorsorIso_snd :
    (picardOneTensorTorsorIso c D).hom ≫ snd _ _ =
      snd (groupScheme c D).X (picardOne c D) := by
  change (tensorBinaryProductIso (groupScheme c D).X (picardOne c D)).hom ≫
    (picardOneTorsorIso c D).hom ≫
      lift Limits.prod.fst Limits.prod.snd ≫ snd _ _ = _
  rw [lift_snd, picardOneTorsorIso_snd]
  exact Limits.prod.lift_snd (fst _ _) (snd _ _)

end AlgebraicGeometry.GeneralizedJacobian
