/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.ScalarTowerComparison
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-! # Maps and equivariant comparisons along a functor tower

The actual one-step comparison squares give the composite comparison squares.
The equivariant group comparison is retained together with the two object comparisons.
-/

open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace CategoryTheory

theorem scalarTowerComparisonIso_map
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C) (e : H ≅ F ⋙ G)
    {U V : A} (q : U ⟶ V) {UL : B} {ULM UM : C}
    (a : UL ≅ F.obj U) (b : ULM ≅ G.obj UL) (c : UM ≅ H.obj U)
    (qL : UL ⟶ F.obj V) (qM : UM ⟶ H.obj V) (qLM : ULM ⟶ G.obj (F.obj V))
    (hL : a.hom ≫ F.map q = qL) (hM : c.hom ≫ H.map q = qM)
    (hLM : b.hom ≫ G.map qL = qLM) :
    (scalarTowerComparisonIso H F G e a b c.symm).hom ≫ qM =
      qLM ≫ e.inv.app V := by
  change (b ≪≫ G.mapIso a ≪≫ (e.app U).symm ≪≫ c.symm).hom ≫ qM = _
  rw [← hM, ← hLM, ← hL]
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.app_inv]
  exact congrArg (fun f => b.hom ≫ G.map a.hom ≫ f) (e.inv.naturality q).symm

theorem scalarTowerComparisonIso_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C) (e : H ≅ F ⋙ G)
    {U P : A} {UL PL : B} {UM ULM PM PLM : C} (q : U ⟶ P)
    (a : UL ≅ F.obj U) (b : ULM ≅ G.obj UL) (c : UM ≅ H.obj U)
    (pL : F.obj P ≅ PL) (pM : H.obj P ≅ PM) (pLM : G.obj PL ≅ PLM)
    (qL : UL ⟶ PL) (qM : UM ⟶ PM) (qLM : ULM ⟶ PLM)
    (hL : a.hom ≫ F.map q ≫ pL.hom = qL)
    (hM : c.hom ≫ H.map q ≫ pM.hom = qM)
    (hLM : b.hom ≫ G.map qL ≫ pLM.hom = qLM) :
    (scalarTowerComparisonIso H F G e a b c.symm).hom ≫ qM =
      qLM ≫ (scalarTowerComparisonIso H F G e pL.symm pLM.symm pM).hom := by
  simp only [scalarTowerComparisonIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.app_inv]
  rw [← hM, ← hLM, ← hL]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (G.map pL.hom) (G.map pL.inv),
    ← G.map_comp, pL.hom_inv_id, G.map_id, Category.id_comp]
  simpa only [Category.assoc, CategoryTheory.Functor.comp_map] using
    congrArg (fun f => b.hom ≫ G.map a.hom ≫ f ≫ pM.hom) (e.inv.naturality q).symm

theorem exists_equivariantScalarTowerComparisons
    {A B C : Type*} [Category A] [Category B] [Category C]
    [CartesianMonoidalCategory C] [BraidedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C) (e : H ≅ F ⋙ G)
    {U P Q : A} {UL PL : B} {UM ULM PM PLM : C}
    {JLM JM : CommGrp C}
    [actionLM : ModObj JLM.X PLM] [actionM : ModObj JM.X PM]
    (q : U ⟶ P) (t : U ⟶ Q)
    (a : UL ≅ F.obj U) (b : ULM ≅ G.obj UL) (c : UM ≅ H.obj U)
    (pL : F.obj P ≅ PL) (pM : H.obj P ≅ PM) (pLM : G.obj PL ≅ PLM)
    (qL : UL ⟶ PL) (qM : UM ⟶ PM) (qLM : ULM ⟶ PLM)
    (tL : UL ⟶ F.obj Q) (tM : UM ⟶ H.obj Q) (tLM : ULM ⟶ G.obj (F.obj Q))
    (hqL : a.hom ≫ F.map q ≫ pL.hom = qL)
    (hqM : c.hom ≫ H.map q ≫ pM.hom = qM)
    (hqLM : b.hom ≫ G.map qL ≫ pLM.hom = qLM)
    (htL : a.hom ≫ F.map t = tL) (htM : c.hom ≫ H.map t = tM)
    (htLM : b.hom ≫ G.map tL = tLM)
    (hAction : let eP := scalarTowerComparisonIso H F G e pL.symm pLM.symm pM
      ∃ eJ : JLM ≅ JM, ∀ (T : C) (g : T ⟶ JLM.X) (x : T ⟶ PLM),
        (g • x) ≫ eP.hom = (g ≫ eJ.hom.hom.hom.hom) • (x ≫ eP.hom)) :
    ∃ (eJ : JLM ≅ JM) (eP : PLM ≅ PM) (eU : ULM ≅ UM),
      (∀ (T : C) (g : T ⟶ JLM.X) (x : T ⟶ PLM),
        (g • x) ≫ eP.hom = (g ≫ eJ.hom.hom.hom.hom) • (x ≫ eP.hom)) ∧
      eU.hom ≫ qM = qLM ≫ eP.hom ∧ eU.hom ≫ tM = tLM ≫ e.inv.app Q := by
  obtain ⟨eJ, he⟩ := hAction
  refine ⟨eJ, scalarTowerComparisonIso H F G e pL.symm pLM.symm pM,
    scalarTowerComparisonIso H F G e a b c.symm, he, ?_, ?_⟩
  · exact scalarTowerComparisonIso_transport F G H e q a b c pL pM pLM
      qL qM qLM hqL hqM hqLM
  · exact scalarTowerComparisonIso_map F G H e t a b c tL tM tLM htL htM htLM

end CategoryTheory
