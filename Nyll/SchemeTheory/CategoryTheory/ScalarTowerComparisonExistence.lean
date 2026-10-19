/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.ScalarTowerMapComparison
import Nyll.SchemeTheory.CategoryTheory.EquivariantScalarTowerComparison

/-! # Equivariant tower comparisons from actual single-step witnesses

Three single-step comparisons supply the group, acted-on object and source
comparisons for a functor tower. Their action laws and both map squares are
composed while the witnesses remain abstract.
-/

noncomputable section

universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace CategoryTheory

/-- Actual single-step group, action and source comparisons give an equivariant
tower comparison preserving both the distinguished map and a second map.
No particular formulas for the three single-step isomorphisms are required. -/
theorem exists_equivariantScalarTowerComparisons_of_singleSteps
    {A B C : Type u}
    [Category.{v} A] [CartesianMonoidalCategory A] [BraidedCategory A]
    [Category.{v} B] [CartesianMonoidalCategory B] [BraidedCategory B]
    [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
    (F : A ⥤ B) [F.Braided] (G : B ⥤ C) [G.Braided]
    (H : A ⥤ C) [H.Braided] (e : H ≅ F ⋙ G)
    (J : CommGrp A) (JL : CommGrp B) (JM JLM : CommGrp C)
    {U P Q : A} {UL PL : B} {UM ULM PM PLM : C}
    [ModObj J.X P] [ModObj JL.X PL] [ModObj JM.X PM] [ModObj JLM.X PLM]
    (q : U ⟶ P) (t : U ⟶ Q)
    (qL : UL ⟶ PL) (qM : UM ⟶ PM) (qLM : ULM ⟶ PLM)
    (tL : UL ⟶ F.obj Q) (tM : UM ⟶ H.obj Q)
    (tLM : ULM ⟶ G.obj (F.obj Q)) :
    let _actL : ModObj (F.obj J.X) (F.obj P) := F.modObjObj J.X P
    let _actLM : ModObj (G.obj JL.X) (G.obj PL) := G.modObjObj JL.X PL
    let _actM : ModObj (H.obj J.X) (H.obj P) := H.modObjObj J.X P
    (∃ (b : F.mapCommGrp.obj J ≅ JL) (p : F.obj P ≅ PL) (a : UL ≅ F.obj U),
      (∀ (T : B) (g : T ⟶ JL.X) (x : T ⟶ PL),
        (g • x) ≫ p.inv =
          (g ≫ (show JL.X ⟶ F.obj J.X from b.inv.hom.hom.hom)) • (x ≫ p.inv)) ∧
      (∀ (T : B) (g : T ⟶ F.obj J.X) (x : T ⟶ F.obj P),
        (g • x) ≫ p.hom = (g ≫ b.hom.hom.hom.hom) • (x ≫ p.hom)) ∧
      a.hom ≫ F.map q ≫ p.hom = qL ∧ a.hom ≫ F.map t = tL) →
    (∃ (b : G.mapCommGrp.obj JL ≅ JLM) (p : G.obj PL ≅ PLM)
      (a : ULM ≅ G.obj UL),
      (∀ (T : C) (g : T ⟶ JLM.X) (x : T ⟶ PLM),
        (g • x) ≫ p.inv =
          (g ≫ (show JLM.X ⟶ G.obj JL.X from b.inv.hom.hom.hom)) • (x ≫ p.inv)) ∧
      (∀ (T : C) (g : T ⟶ G.obj JL.X) (x : T ⟶ G.obj PL),
        (g • x) ≫ p.hom = (g ≫ b.hom.hom.hom.hom) • (x ≫ p.hom)) ∧
      a.hom ≫ G.map qL ≫ p.hom = qLM ∧ a.hom ≫ G.map tL = tLM) →
    (∃ (b : H.mapCommGrp.obj J ≅ JM) (p : H.obj P ≅ PM) (a : UM ≅ H.obj U),
      (∀ (T : C) (g : T ⟶ JM.X) (x : T ⟶ PM),
        (g • x) ≫ p.inv =
          (g ≫ (show JM.X ⟶ H.obj J.X from b.inv.hom.hom.hom)) • (x ≫ p.inv)) ∧
      (∀ (T : C) (g : T ⟶ H.obj J.X) (x : T ⟶ H.obj P),
        (g • x) ≫ p.hom = (g ≫ b.hom.hom.hom.hom) • (x ≫ p.hom)) ∧
      a.hom ≫ H.map q ≫ p.hom = qM ∧ a.hom ≫ H.map t = tM) →
    ∃ (eJ : JLM ≅ JM) (eP : PLM ≅ PM) (eU : ULM ≅ UM),
      (∀ (T : C) (g : T ⟶ JLM.X) (x : T ⟶ PLM),
        (g • x) ≫ eP.hom = (g ≫ eJ.hom.hom.hom.hom) • (x ≫ eP.hom)) ∧
      eU.hom ≫ qM = qLM ≫ eP.hom ∧ eU.hom ≫ tM = tLM ≫ e.inv.app Q := by
  intro actL actLM actM hL hLM hM
  obtain ⟨bL, pL, aL, hLinv, _, hqL, htL⟩ := hL
  obtain ⟨bLM, pLM, aLM, hLMinv, _, hqLM, htLM⟩ := hLM
  obtain ⟨bM, pM, aM, _, hMforward, hqM, htM⟩ := hM
  have hAction :
      let eP := scalarTowerComparisonIso H F G e pL.symm pLM.symm pM
      ∃ eJ : JLM ≅ JM, ∀ (T : C) (g : T ⟶ JLM.X) (x : T ⟶ PLM),
        (g • x) ≫ eP.hom = (g ≫ eJ.hom.hom.hom.hom) • (x ≫ eP.hom) :=
    AlgebraicGeometry.GeneralizedJacobian.exists_equivariant_commGrp_tower_comparison
      H F G e J P JL PL JLM JM PLM PM
      bL.symm pL.symm bLM.symm pLM.symm bM pM hLinv hLMinv hMforward
  exact exists_equivariantScalarTowerComparisons F G H e
    (U := U) (P := P) (Q := Q) (UL := UL) (PL := PL)
    (UM := UM) (ULM := ULM) (PM := PM) (PLM := PLM) (JLM := JLM) (JM := JM)
    q t aL aLM aM pL pM pLM qL qM qLM tL tM tLM
    hqL hqM hqLM htL htM htLM hAction

end CategoryTheory
