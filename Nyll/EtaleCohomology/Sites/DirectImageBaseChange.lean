/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.PullbackComposition
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The canonical direct-image base-change morphism

The actual direct-image composition isomorphisms of a commuting square
have a canonical mate under the horizontal pullback/direct-image
adjunctions. The unit formula retains the literal comparison on direct
images, for use in geometric-stalk calculations. No invertibility of
base change is assumed.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

private def transposeTransformation
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : D ⥤ E} {R : E ⥤ D} (adj : L ⊣ R)
    {G : C ⥤ D} {H : C ⥤ E} (α : G ⟶ H ⋙ R) : G ⋙ L ⟶ H where
  app X := (adj.homEquiv (G.obj X) (H.obj X)).symm (α.app X)
  naturality X Y f := by
    apply (adj.homEquiv (G.obj X) (H.obj Y)).injective
    simp only [CategoryTheory.Functor.comp_map]
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact α.naturality f

private theorem transposeTransformation_unit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : D ⥤ E} {R : E ⥤ D} (adj : L ⊣ R)
    {G : C ⥤ D} {H : C ⥤ E} (α : G ⟶ H ⋙ R) (X : C) :
    α.app X = adj.unit.app (G.obj X) ≫
      R.map ((transposeTransformation adj α).app X) :=
  ((adj.homEquiv (G.obj X) (H.obj X)).apply_symm_apply (α.app X)).symm

private def directImageUnitTransformation
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {G : C ⥤ E} {H : D ⥤ F} {S : F ⥤ E}
    (α : R ⋙ G ⟶ H ⋙ S) : G ⟶ (L ⋙ H) ⋙ S where
  app X := G.map (adj.unit.app X) ≫ α.app (L.obj X)
  naturality X Y f := by
    change G.map f ≫ (G.map (adj.unit.app Y) ≫ α.app (L.obj Y)) =
      (G.map (adj.unit.app X) ≫ α.app (L.obj X)) ≫ S.map (H.map (L.map f))
    calc
      G.map f ≫ (G.map (adj.unit.app Y) ≫ α.app (L.obj Y)) =
          G.map (f ≫ adj.unit.app Y) ≫ α.app (L.obj Y) := by
        rw [G.map_comp, Category.assoc]
      _ = G.map (adj.unit.app X ≫ R.map (L.map f)) ≫ α.app (L.obj Y) :=
        congrArg (fun k => G.map k ≫ α.app (L.obj Y)) (adj.unit_naturality f).symm
      _ = (G.map (adj.unit.app X) ≫ α.app (L.obj X)) ≫ S.map (H.map (L.map f)) := by
        have hn : G.map (R.map (L.map f)) ≫ α.app (L.obj Y) =
            α.app (L.obj X) ≫ S.map (H.map (L.map f)) := α.naturality (L.map f)
        rw [G.map_comp, Category.assoc, hn, ← Category.assoc]

variable {X Y X' Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) (R : Type u) [CommRing R]

/-- The actual direct-image composition isomorphism around a commuting square. -/
def etalePushforwardSquareIso :
    etalePushforward g' R ⋙ etalePushforward f R ≅
      etalePushforward f' R ⋙ etalePushforward g R :=
  etalePushforwardCompIso g' f R ≪≫
    eqToIso (congrArg (fun q : X' ⟶ Y => etalePushforward q R) h.symm) ≪≫
    (etalePushforwardCompIso f' g R).symm

/-- Cancelling the final composition isomorphism recovers the actual
composition around the other side of the square. -/
theorem etalePushforwardSquareIso_hom_comp :
    (etalePushforwardSquareIso f g f' g' h R).hom ≫
        (etalePushforwardCompIso f' g R).hom =
      (etalePushforwardCompIso g' f R).hom ≫
        (eqToIso (congrArg (fun q : X' ⟶ Y => etalePushforward q R) h.symm)).hom := by
  simp only [etalePushforwardSquareIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The canonical base-change morphism: transpose the actual direct-image
composition map after the inverse-image unit. -/
def etaleDirectImageBaseChange :
    etalePushforward f R ⋙ etalePullback g R ⟶
      etalePullback g' R ⋙ etalePushforward f' R :=
  transposeTransformation (etalePullbackPushforwardAdjunction g R)
    (directImageUnitTransformation (etalePullbackPushforwardAdjunction g' R)
      (etalePushforwardSquareIso f g f' g' h R).hom)

/-- The literal unit identity characterizing the base-change morphism. -/
theorem etaleDirectImageBaseChange_unit
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (etalePushforward f R).map ((etalePullbackPushforwardAdjunction g' R).unit.app F) ≫
        (etalePushforwardSquareIso f g f' g' h R).hom.app ((etalePullback g' R).obj F) =
      (etalePullbackPushforwardAdjunction g R).unit.app ((etalePushforward f R).obj F) ≫
        (etalePushforward g R).map ((etaleDirectImageBaseChange f g f' g' h R).app F) :=
  transposeTransformation_unit (etalePullbackPushforwardAdjunction g R)
    (directImageUnitTransformation (etalePullbackPushforwardAdjunction g' R)
      (etalePushforwardSquareIso f g f' g' h R).hom) F

end EtaleCohomology
