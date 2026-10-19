/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Frames.ScalarFrames
import Nyll.JacobianVarieties.Generalized.RigidifiedScalars
import Nyll.JacobianVarieties.Generalized.RigidifiedPullback

/-! Pulling actual frames and their scalar relation along a commutative base square. -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y Y' S S' : Scheme.{u}} {M : Y.Modules}

/-- Pullback of an actual frame, using the canonical pullback-unit comparison. -/
def pullbackFrame (f : Y' ⟶ Y) (e : M ≅ 𝟙_ Y.Modules) :
    (Scheme.Modules.pullback f).obj M ≅ 𝟙_ Y'.Modules :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso f

/-- The ratio of the pulled frames is the pullback of their actual unit. -/
theorem frameRatio_pullbackFrame (f : Y' ⟶ Y) (e e' : M ≅ 𝟙_ Y.Modules) :
    frameRatio (pullbackFrame f e) (pullbackFrame f e') =
      Units.map f.appTop.hom.toMonoidHom (frameRatio e e') := by
  have he : ((pullbackFrame f e).symm ≪≫ pullbackFrame f e' : Aut (𝟙_ Y'.Modules)) =
      RigidifiedLineBundle.restrictUnitAut f (e.symm ≪≫ e') := by
    apply CategoryTheory.Iso.ext
    change ((Scheme.Modules.pullbackTensorUnitObjIso f).inv ≫
      (Scheme.Modules.pullback f).map e.inv) ≫
        ((Scheme.Modules.pullback f).map e'.hom ≫
          (Scheme.Modules.pullbackTensorUnitObjIso f).hom) =
      ((Scheme.Modules.pullbackTensorUnitObjIso f).inv ≫
        (Scheme.Modules.pullback f).map (e.inv ≫ e'.hom)) ≫
          (Scheme.Modules.pullbackTensorUnitObjIso f).hom
    simp only [Functor.map_comp, Category.assoc]
  exact (congrArg (unitAutEquivUnits Y') he).trans
    (RigidifiedLineBundle.unitAutEquivUnits_restrict f (e.symm ≪≫ e'))

/-- Restriction of scalar units respects the actual commutative square. -/
theorem scalarUnits_square {q : Y ⟶ S} {q' : Y' ⟶ S'}
    (f : Y' ⟶ Y) (g : S' ⟶ S) (w : f ≫ q = q' ≫ g) (a : Γ(S, ⊤)ˣ) :
    Units.map f.appTop.hom.toMonoidHom (Units.map q.appTop.hom.toMonoidHom a) =
      Units.map q'.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom a) := by
  apply Units.ext
  have hw := congrArg Scheme.Hom.appTop w
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hw
  exact congrArg (fun h : Γ(S, ⊤) ⟶ Γ(Y', ⊤) => h (a : Γ(S, ⊤))) hw

/-- The scalar relation descends along every actual base square. -/
theorem scalarFrameRel_pullback {q : Y ⟶ S} {q' : Y' ⟶ S'}
    (f : Y' ⟶ Y) (g : S' ⟶ S) (w : f ≫ q = q' ≫ g)
    {e e' : M ≅ 𝟙_ Y.Modules} (h : (scalarFrameSetoid q M).r e e') :
    (scalarFrameSetoid q' ((Scheme.Modules.pullback f).obj M)).r
      (pullbackFrame f e) (pullbackFrame f e') := by
  obtain ⟨a, ha⟩ := h
  refine ⟨Units.map g.appTop.hom.toMonoidHom a, ?_⟩
  exact (scalarUnits_square f g w a).symm.trans
    ((congrArg (Units.map f.appTop.hom.toMonoidHom) ha).trans
      (frameRatio_pullbackFrame f e e').symm)

/-- Pullback on the actual quotient of frames by base scalars. -/
def scalarFrameClassesPullback {q : Y ⟶ S} {q' : Y' ⟶ S'}
    (f : Y' ⟶ Y) (g : S' ⟶ S) (w : f ≫ q = q' ≫ g) :
    ScalarFrameClasses q M → ScalarFrameClasses q' ((Scheme.Modules.pullback f).obj M) :=
  Quotient.map (pullbackFrame f) (fun _ _ h => scalarFrameRel_pullback f g w h)

/-- Composition of pulled frames uses the canonical module pullback comparison. -/
theorem pullbackFrame_comp {Y'' : Scheme.{u}} (f : Y' ⟶ Y) (g : Y'' ⟶ Y')
    (e : M ≅ 𝟙_ Y.Modules) :
    pullbackFrame g (pullbackFrame f e) =
      (Scheme.Modules.pullbackComp g f).app M ≪≫ pullbackFrame (g ≫ f) e := by
  apply CategoryTheory.Iso.ext
  have hn := (Scheme.Modules.pullbackComp g f).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  change (Scheme.Modules.pullback g).map
      ((Scheme.Modules.pullback f).map e.hom ≫
        (Scheme.Modules.pullbackTensorUnitObjIso f).hom) ≫
      (Scheme.Modules.pullbackTensorUnitObjIso g).hom =
    (Scheme.Modules.pullbackComp g f).hom.app M ≫
      ((Scheme.Modules.pullback (g ≫ f)).map e.hom ≫
        (Scheme.Modules.pullbackTensorUnitObjIso (g ≫ f)).hom)
  rw [Functor.map_comp, Category.assoc, ← RigidifiedLineBundle.pullbackTensorUnit_comp,
    ← Category.assoc, hn, Category.assoc]

/-- Pulling back by the identity retains the canonical module identification. -/
theorem pullbackFrame_id (e : M ≅ 𝟙_ Y.Modules) :
    pullbackFrame (𝟙 Y) e = (Scheme.Modules.pullbackId Y).app M ≪≫ e := by
  apply CategoryTheory.Iso.ext
  change (Scheme.Modules.pullback (𝟙 Y)).map e.hom ≫
      (Scheme.Modules.pullbackTensorUnitObjIso (𝟙 Y)).hom =
    (Scheme.Modules.pullbackId Y).hom.app M ≫ e.hom
  rw [← RigidifiedLineBundle.pullbackId_unit]
  exact (Scheme.Modules.pullbackId Y).hom.naturality e.hom

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
