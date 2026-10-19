/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.JacobianVarieties.Generalized.PicardOneScalarExtensionTorsor
import Nyll.JacobianVarieties.Generalized.PicardOneScalarExtensionScheme
import Nyll.JacobianVarieties.Generalized.PicardOneModuleObject
import Nyll.JacobianVarieties.Generalized.ScalarExtensionGroupScheme

/-! # Simultaneous comparisons for one scalar extension

The actual group, Picard-one scheme and complement comparisons intertwine both
native actions and preserve the Abel map and an arbitrary map from the complement.
Keeping these single-step witnesses together permits their composition before
substituting the concrete scalar-extension isomorphisms.
-/

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

/-- The canonical comparisons for one field extension simultaneously preserve
both action directions, the intrinsic Abel map and the original complement map. -/
theorem exists_singleScalarExtensionComparisons
    (Q : Over (Spec (CommRingCat.of K)))
    (r : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let F := Over.pullback (specMap K L)
    let J := groupScheme c D
    let JL := groupScheme cL DL
    let P := picardOne c D
    let PL := picardOne cL DL
    let U := Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)
    let UL := Over.mk ((modulusComplement (modulusCurveMap (c := cL) DL)).ι ≫ cL)
    let q : U ⟶ P := abelOneMap c D
    let qL : UL ⟶ PL := abelOneMap cL DL
    let rL : UL ⟶ F.obj Q := modulusMapScalarExtension c D L Q r
    let _actF : ModObj (F.obj J.X) (F.obj P) := F.modObjObj J.X P
    ∃ (b : F.mapCommGrp.obj J ≅ JL) (p : F.obj P ≅ PL) (a : UL ≅ F.obj U),
      (∀ (T : Over (Spec (CommRingCat.of L))) (g : T ⟶ JL.X) (x : T ⟶ PL),
        (g • x) ≫ p.inv =
          (g ≫ (show JL.X ⟶ F.obj J.X from b.inv.hom.hom.hom)) • (x ≫ p.inv)) ∧
      (∀ (T : Over (Spec (CommRingCat.of L)))
        (g : T ⟶ F.obj J.X) (x : T ⟶ F.obj P),
        (g • x) ≫ p.hom = (g ≫ b.hom.hom.hom.hom) • (x ≫ p.hom)) ∧
      a.hom ≫ F.map q ≫ p.hom = qL ∧ a.hom ≫ F.map r = rL := by
  intro cL DL F J JL P PL U UL q qL rL actF
  refine ⟨groupActualScalarExtensionIso c D L, picardOneScalarExtensionIso c D L,
    divisorScalarExtensionComplementIso c D L, ?_, ?_, ?_, ?_⟩
  · intro T g x
    exact picardOneScalarExtensionIso_inv_smul c D L g x
  · intro T g x
    exact picardOneScalarExtensionIso_smul c D L g x
  · exact abelOne_scalarExtension_square c D L
  · exact divisorScalarExtensionComplementIso_hom_map c D L Q r

end AlgebraicGeometry.GeneralizedJacobian
