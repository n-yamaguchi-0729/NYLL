/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.JacobianVarieties.Generalized.SingleScalarExtensionComparisons
import Nyll.SchemeTheory.CategoryTheory.ScalarTowerComparisonExistence

/-! # Simultaneous scalar-extension comparisons for the actual modulus

The group, Picard-one scheme and complement comparisons preserve the action,
the intrinsic Abel map and the original regular map.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

/-- The actual group, Picard-one and full-complement tower comparisons are
constructed together with their action and Abel/map squares. All witnesses are
formed in the abstract tower calculation from the original single-extension data. -/
theorem exists_scalarExtensionTowerComparisons
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (M : Type u) [Field M] [Algebra L M] [Algebra K M]
    (Q : Over (Spec (CommRingCat.of K)))
    (r : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q)
    (e : Over.pullback (specMap K M) ≅
      Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M)) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let cM := baseChange K c M
    let DM := D.changeBaseOfIdentity (specMap K M)
    let cLM := baseChange L cL M
    let DLM := DL.changeBaseOfIdentity (f := cL) (specMap L M)
    let F := Over.pullback (specMap K L)
    let G := Over.pullback (specMap L M)
    let H := Over.pullback (specMap K M)
    let UL := Over.mk ((modulusComplement (modulusCurveMap (c := cL) DL)).ι ≫ cL)
    let UM := Over.mk ((modulusComplement (modulusCurveMap (c := cM) DM)).ι ≫ cM)
    let ULM := Over.mk ((modulusComplement (modulusCurveMap (c := cLM) DLM)).ι ≫ cLM)
    let PM := picardOne cM DM
    let PLM := picardOne cLM DLM
    let qM : UM ⟶ PM := abelOneMap cM DM
    let qLM : ULM ⟶ PLM := abelOneMap cLM DLM
    let JLM := groupScheme cLM DLM
    let JM := groupScheme cM DM
    let tL : UL ⟶ F.obj Q := modulusMapScalarExtension c D L Q r
    let tM : UM ⟶ H.obj Q := modulusMapScalarExtension c D M Q r
    let tLM : ULM ⟶ G.obj (F.obj Q) :=
      modulusMapScalarExtension cL DL M (F.obj Q) tL
    ∃ (eJ : JLM ≅ JM) (eP : PLM ≅ PM) (eU : ULM ≅ UM),
      (∀ (T : Over (Spec (CommRingCat.of M)))
        (g : T ⟶ JLM.X) (x : T ⟶ PLM),
        (g • x) ≫ eP.hom = (g ≫ eJ.hom.hom.hom.hom) • (x ≫ eP.hom)) ∧
      eU.hom ≫ qM = qLM ≫ eP.hom ∧ eU.hom ≫ tM = tLM ≫ e.inv.app Q := by
  intro cL DL cM DM cLM DLM F G H UL UM ULM PM PLM qM qLM JLM JM tL tM tLM
  let U := Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)
  let P := picardOne c D
  let PL := picardOne cL DL
  let J := groupScheme c D
  let JL := groupScheme cL DL
  let q : U ⟶ P := abelOneMap c D
  let qL : UL ⟶ PL := abelOneMap cL DL
  exact exists_equivariantScalarTowerComparisons_of_singleSteps F G H e J JL JM JLM
    (U := U) (P := P) (Q := Q) (UL := UL) (PL := PL)
    (UM := UM) (ULM := ULM) (PM := PM) (PLM := PLM)
    q r qL qM qLM tL tM tLM
    (exists_singleScalarExtensionComparisons c D L Q r)
    (exists_singleScalarExtensionComparisons cL DL M (F.obj Q) tL)
    (exists_singleScalarExtensionComparisons c D M Q r)

end AlgebraicGeometry.GeneralizedJacobian
