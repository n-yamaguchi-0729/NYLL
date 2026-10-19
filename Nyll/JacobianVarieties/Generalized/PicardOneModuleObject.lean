/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOneSchemeActionTorsor
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # The actual Picard-one torsor as a categorical module object -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The actual rigidified tensor action, with its proved categorical action laws. -/
instance picardOneModObj : ModObj (groupScheme c D).X (picardOne c D) where
  smul := picardOneTensorAction c D
  one_smul := by
    let G := (groupScheme c D).X
    let P := picardOne c D
    change η[G] ▷ P ≫ picardOneTensorAction c D = (λ_ P).hom
    have he : η[G] ▷ P = lift (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⊗ P ⟶ G)
        ((λ_ P).hom) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [whiskerRight_fst, lift_fst, CategoryTheory.Hom.one_def]
        congr 1
      · rw [whiskerRight_snd, lift_snd, leftUnitor_hom]
    rw [he]
    exact picardOneTensorAction_one c D ((λ_ P).hom)
  mul_smul := by
    let G := (groupScheme c D).X
    let P := picardOne c D
    let a := picardOneTensorAction c D
    let g : (G ⊗ G) ⊗ P ⟶ G := fst (G ⊗ G) P ≫ fst G G
    let h : (G ⊗ G) ⊗ P ⟶ G := fst (G ⊗ G) P ≫ snd G G
    let x : (G ⊗ G) ⊗ P ⟶ P := snd (G ⊗ G) P
    change μ[G] ▷ P ≫ a = (α_ G G P).hom ≫ G ◁ a ≫ a
    have hm : lift (g * h) x = μ[G] ▷ P := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst, whiskerRight_fst, CategoryTheory.Hom.mul_def]
        dsimp [g, h]
        rw [← comp_lift, lift_fst_snd, Category.comp_id]
      · exact (lift_snd (g * h) x).trans (whiskerRight_snd μ[G] P).symm
    have hi : lift h x = (α_ G G P).hom ≫ snd G (G ⊗ P) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, Category.assoc, associator_hom_snd_fst]
      · rw [lift_snd, Category.assoc, associator_hom_snd_snd]
    have hr : lift g (lift h x ≫ a) = (α_ G G P).hom ≫ G ◁ a := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, Category.assoc, whiskerLeft_fst, associator_hom_fst]
      · rw [lift_snd, Category.assoc, whiskerLeft_snd, hi, Category.assoc]
    exact (congrArg (fun f => f ≫ a) hm).symm.trans
      ((picardOneTensorAction_mul c D g h x).trans (congrArg (fun f => f ≫ a) hr))

/-- The standard categorical torsor morphism is the already constructed actual torsor iso. -/
theorem picardOne_leftSMul_eq :
    ModObj.leftSMul (groupScheme c D).X (picardOne c D) =
      (picardOneTensorTorsorIso c D).hom := by
  apply CartesianMonoidalCategory.hom_ext
  · exact ModObj.leftSMul_fst.trans (picardOneTensorTorsorIso_fst c D).symm
  · exact ModObj.leftSMul_snd.trans (picardOneTensorTorsorIso_snd c D).symm

/-- The actual tensor action is simply transitive as a scheme morphism. -/
instance picardOne_leftSMul_isIso :
    IsIso (ModObj.leftSMul (groupScheme c D).X (picardOne c D)) := by
  rw [picardOne_leftSMul_eq]
  infer_instance

/-- On every test scheme, any two degree-one points differ by a unique actual zero class. -/
theorem picardOne_existsUnique_smul (T : Over (Spec (CommRingCat.of K)))
    (x y : T ⟶ picardOne c D) :
    ∃! (g : T ⟶ (groupScheme c D).X), g • x = y :=
  (ModObj.isIso_leftSMul_iff (M := (groupScheme c D).X) (X := picardOne c D)).mp
    inferInstance T x y

/-- The constructed intrinsic torsor is an fppf cover of the base field. -/
theorem picardOne_torsor_fppf :
    Flat (picardOne c D).hom ∧ LocallyOfFinitePresentation (picardOne c D).hom ∧
      Surjective (picardOne c D).hom :=
  picardOne_fppf c D

end AlgebraicGeometry.GeneralizedJacobian
