/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ScalarFramePullback
import Nyll.SchemeTheory.Modules.Functoriality.PullbackCompPullbackCongrPasteSquaresApp

/-! The presheaf of actual frames of the pullback of a fixed module. -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y : Scheme.{u}} (M : Y.Modules)

/-- The canonical comparison for the two descriptions of a pulled family. -/
def frameComparison {T T' : Over Y} (f : T' ⟶ T) :
    (Scheme.Modules.pullback f.left).obj ((Scheme.Modules.pullback T.hom).obj M) ≅
      (Scheme.Modules.pullback T'.hom).obj M :=
  (τ f.left T.hom T'.hom f.w).app M

/-- The actual frame restriction retains the pullback comparison of its source. -/
def frameMap {T T' : Over Y} (f : T' ⟶ T)
    (e : (Scheme.Modules.pullback T.hom).obj M ≅ 𝟙_ T.left.Modules) :
    (Scheme.Modules.pullback T'.hom).obj M ≅ 𝟙_ T'.left.Modules :=
  (frameComparison M f).symm ≪≫ pullbackFrame f.left e

@[reassoc] theorem frameMap_fac {T T' : Over Y} (f : T' ⟶ T)
    (e : (Scheme.Modules.pullback T.hom).obj M ≅ 𝟙_ T.left.Modules) :
    (frameComparison M f).hom ≫ (frameMap M f e).hom = (pullbackFrame f.left e).hom :=
  (frameComparison M f).hom_inv_id_assoc _

theorem frameComparison_id (T : Over Y) :
    frameComparison M (𝟙 T) =
      (Scheme.Modules.pullbackId T.left).app ((Scheme.Modules.pullback T.hom).obj M) := by
  apply CategoryTheory.Iso.ext
  have h := NatTrans.congr_app
    (Scheme.Modules.pseudofunctor_right_unitality (f := T.hom)) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at h
  change (Scheme.Modules.pullbackComp (𝟙 T.left) T.hom).inv.app M ≫
      (Scheme.Modules.pullbackId T.left).hom.app ((Scheme.Modules.pullback T.hom).obj M) =
    (Scheme.Modules.pullbackCongr (Category.id_comp T.hom)).hom.app M at h
  exact (((Scheme.Modules.pullbackComp (𝟙 T.left) T.hom).app M).inv_comp_eq.mp h).symm

theorem frameMap_id (T : Over Y)
    (e : (Scheme.Modules.pullback T.hom).obj M ≅ 𝟙_ T.left.Modules) :
    frameMap M (𝟙 T) e = e := by
  apply CategoryTheory.Iso.ext
  change (frameComparison M (𝟙 T)).inv ≫ (pullbackFrame (𝟙 T.left) e).hom = e.hom
  rw [pullbackFrame_id, frameComparison_id]
  exact ((Scheme.Modules.pullbackId T.left).app
    ((Scheme.Modules.pullback T.hom).obj M)).inv_hom_id_assoc e.hom

/-- The source comparisons obey the genuine pullback composition law. -/
theorem frameComparison_comp {T T' T'' : Over Y} (f : T' ⟶ T) (g : T'' ⟶ T') :
    (Scheme.Modules.pullback g.left).map (frameComparison M f).hom ≫
        (frameComparison M g).hom =
      (Scheme.Modules.pullbackComp g.left f.left).hom.app
        ((Scheme.Modules.pullback T.hom).obj M) ≫ (frameComparison M (g ≫ f)).hom := by
  exact (τ_paste_app g.left f.left T.hom (g.left ≫ f.left) T'.hom T''.hom
    rfl f.w (g ≫ f).w M).symm

/-- Restricting an actual frame twice agrees with restricting along the composite. -/
theorem frameMap_comp {T T' T'' : Over Y} (f : T' ⟶ T) (g : T'' ⟶ T')
    (e : (Scheme.Modules.pullback T.hom).obj M ≅ 𝟙_ T.left.Modules) :
    frameMap M g (frameMap M f e) = frameMap M (g ≫ f) e := by
  apply CategoryTheory.Iso.ext
  apply (cancel_epi ((Scheme.Modules.pullback g.left).map (frameComparison M f).hom ≫
    (frameComparison M g).hom)).mp
  calc
    _ = (Scheme.Modules.pullback g.left).map (frameComparison M f).hom ≫
        (pullbackFrame g.left (frameMap M f e)).hom := by
      rw [Category.assoc, frameMap_fac]
    _ = (pullbackFrame g.left (pullbackFrame f.left e)).hom := by
      change (Scheme.Modules.pullback g.left).map (frameComparison M f).hom ≫
        ((Scheme.Modules.pullback g.left).map (frameMap M f e).hom ≫
          (Scheme.Modules.pullbackTensorUnitObjIso g.left).hom) = _
      rw [← Functor.map_comp_assoc, frameMap_fac]
      rfl
    _ = (Scheme.Modules.pullbackComp g.left f.left).hom.app
        ((Scheme.Modules.pullback T.hom).obj M) ≫
          (pullbackFrame (g.left ≫ f.left) e).hom :=
      congrArg CategoryTheory.Iso.hom (pullbackFrame_comp f.left g.left e)
    _ = ((Scheme.Modules.pullbackComp g.left f.left).hom.app
        ((Scheme.Modules.pullback T.hom).obj M) ≫ (frameComparison M (g ≫ f)).hom) ≫
          (frameMap M (g ≫ f) e).hom := by
      rw [Category.assoc, frameMap_fac]
      rfl
    _ = _ := congrArg (fun h => h ≫ (frameMap M (g ≫ f) e).hom)
      (frameComparison_comp M f g).symm

/-- Scalar relations respect frame restriction along a square of parameter schemes. -/
theorem frameMap_scalarRel {T T' : Over Y} (f : T' ⟶ T)
    {S S' : Scheme.{u}} {q : T.left ⟶ S} {q' : T'.left ⟶ S'}
    (g : S' ⟶ S) (w : f.left ≫ q = q' ≫ g)
    {e e' : (Scheme.Modules.pullback T.hom).obj M ≅ 𝟙_ T.left.Modules}
    (h : (scalarFrameSetoid q ((Scheme.Modules.pullback T.hom).obj M)).r e e') :
    (scalarFrameSetoid q' ((Scheme.Modules.pullback T'.hom).obj M)).r
      (frameMap M f e) (frameMap M f e') := by
  have hp : frameRatio (pullbackFrame f.left e) (pullbackFrame f.left e') ∈
      (Units.map q'.appTop.hom.toMonoidHom).range :=
    scalarFrameRel_pullback f.left g w h
  change frameRatio ((frameComparison M f).symm ≪≫ pullbackFrame f.left e)
    ((frameComparison M f).symm ≪≫ pullbackFrame f.left e') ∈ _
  rw [frameRatio_precomp]
  exact hp

/-- Actual frames of a fixed module form a presheaf on all schemes over its source. -/
def framePresheaf : (Over Y)ᵒᵖ ⥤ Type u where
  obj T := (Scheme.Modules.pullback T.unop.hom).obj M ≅ 𝟙_ T.unop.left.Modules
  map f := TypeCat.ofHom (frameMap M f.unop)
  map_id T := TypeCat.homEquiv.injective (funext (frameMap_id M T.unop))
  map_comp f g := TypeCat.homEquiv.injective
    (funext fun e => (frameMap_comp M f.unop g.unop e).symm)

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
