/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FrameCoordinates

/-! Frames of a pulled-back module agree naturally with restriction of its frame functor. -/

noncomputable section

universe u v w

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y Y' : Scheme.{u}} (r : Y' ⟶ Y) (M : Y.Modules)

/-- The actual module pullback comparison identifies the two sets of frames. -/
def modulePullbackFrameEquiv (T : Over Y') :
    ((Scheme.Modules.pullback (T.hom ≫ r)).obj M ≅ 𝟙_ T.left.Modules) ≃
      ((Scheme.Modules.pullback T.hom).obj ((Scheme.Modules.pullback r).obj M) ≅
        𝟙_ T.left.Modules) :=
  frameDomainEquiv ((Scheme.Modules.pullbackComp T.hom r).app M)

theorem modulePullbackFrameComparison {T T' : Over Y'} (g : T' ⟶ T) :
    (frameComparison ((Scheme.Modules.pullback r).obj M) g).hom ≫
        (Scheme.Modules.pullbackComp T'.hom r).hom.app M =
      (Scheme.Modules.pullback g.left).map ((Scheme.Modules.pullbackComp T.hom r).hom.app M) ≫
        (frameComparison M ((Over.map r).map g)).hom := by
  have ht (U : Over Y') : (τ U.hom r (U.hom ≫ r) rfl).hom.app M =
      (Scheme.Modules.pullbackComp U.hom r).hom.app M :=
    (τ_hom_app U.hom r (U.hom ≫ r) rfl M).trans (Category.comp_id _)
  have h := τ_paste_app g.left T.hom r T'.hom (T.hom ≫ r) (T'.hom ≫ r) g.w rfl rfl M
  rw [ht T', ht T] at h
  exact h

/-- The module comparison preserves actual frame restriction maps. -/
theorem modulePullbackFrameEquiv_naturality {T T' : Over Y'} (g : T' ⟶ T)
    (e : (Scheme.Modules.pullback (T.hom ≫ r)).obj M ≅ 𝟙_ T.left.Modules) :
    frameMap ((Scheme.Modules.pullback r).obj M) g (modulePullbackFrameEquiv r M T e) =
      modulePullbackFrameEquiv r M T' (frameMap M
        (T := Over.mk (T.hom ≫ r)) (T' := Over.mk (T'.hom ≫ r))
        ((Over.map r).map g) e) := by
  apply CategoryTheory.Iso.ext
  apply (cancel_epi (frameComparison ((Scheme.Modules.pullback r).obj M) g).hom).mp
  rw [frameMap_fac]
  change (pullbackFrame g.left ((Scheme.Modules.pullbackComp T.hom r).app M ≪≫ e)).hom =
    (frameComparison ((Scheme.Modules.pullback r).obj M) g).hom ≫
      ((Scheme.Modules.pullbackComp T'.hom r).hom.app M ≫
        (frameMap M (T := Over.mk (T.hom ≫ r)) (T' := Over.mk (T'.hom ≫ r))
        ((Over.map r).map g) e).hom)
  rw [← Category.assoc, modulePullbackFrameComparison, Category.assoc, frameMap_fac]
  change (Scheme.Modules.pullback g.left).map
      ((Scheme.Modules.pullbackComp T.hom r).hom.app M ≫ e.hom) ≫
        (Scheme.Modules.pullbackTensorUnitObjIso g.left).hom =
    (Scheme.Modules.pullback g.left).map ((Scheme.Modules.pullbackComp T.hom r).hom.app M) ≫
      ((Scheme.Modules.pullback g.left).map e.hom ≫
        (Scheme.Modules.pullbackTensorUnitObjIso g.left).hom)
  rw [Functor.map_comp, Category.assoc]

/-- Pullback of the fixed module is restriction of its actual frame presheaf. -/
def framePresheafPullbackIso : (Over.map r).op ⋙ framePresheaf M ≅
    framePresheaf ((Scheme.Modules.pullback r).obj M) :=
  NatIso.ofComponents (fun T => (modulePullbackFrameEquiv r M T.unop).toIso)
    (fun g => TypeCat.homEquiv.injective
      (funext fun e => (modulePullbackFrameEquiv_naturality r M g.unop e).symm))

/-- The canonical module comparison does not change the ratio of two frames. -/
theorem frameRatio_modulePullbackFrameEquiv (T : Over Y')
    (e e' : (Scheme.Modules.pullback (T.hom ≫ r)).obj M ≅ 𝟙_ T.left.Modules) :
    frameRatio (modulePullbackFrameEquiv r M T e) (modulePullbackFrameEquiv r M T e') =
      frameRatio e e' := frameRatio_precomp _ e e'

/-- Transport a frame through a cartesian comparison and the module pullback comparison. -/
def frameTransportEquiv {T : Over Y} {U : Over Y'} (a : (Over.map r).obj U ≅ T) :
    ((Scheme.Modules.pullback T.hom).obj M ≅ 𝟙_ T.left.Modules) ≃
      ((Scheme.Modules.pullback U.hom).obj ((Scheme.Modules.pullback r).obj M) ≅
        𝟙_ U.left.Modules) :=
  ((framePresheaf M).mapIso a.op).toEquiv.trans (modulePullbackFrameEquiv r M U)

/-- Ratios of transported frames are the actual restrictions of their units. -/
theorem frameRatio_frameTransportEquiv {T : Over Y} {U : Over Y'}
    (a : (Over.map r).obj U ≅ T)
    (e e' : (Scheme.Modules.pullback T.hom).obj M ≅ 𝟙_ T.left.Modules) :
    frameRatio (frameTransportEquiv r M a e) (frameTransportEquiv r M a e') =
      Units.map a.hom.left.appTop.hom.toMonoidHom (frameRatio e e') := by
  exact (frameRatio_modulePullbackFrameEquiv r M U
    (frameMap M (T := T) (T' := (Over.map r).obj U) a.hom e)
    (frameMap M (T := T) (T' := (Over.map r).obj U) a.hom e')).trans
      (frameRatio_frameMap (M := M) (T := T) (T' := (Over.map r).obj U) a.hom e e')

/-- Transport commutes with restriction when the actual comparison square commutes. -/
theorem frameTransportEquiv_naturality {T T' : Over Y} {U U' : Over Y'}
    (a : (Over.map r).obj U ≅ T) (a' : (Over.map r).obj U' ≅ T')
    (g : T' ⟶ T) (k : U' ⟶ U)
    (w : (Over.map r).map k ≫ a.hom = a'.hom ≫ g)
    (e : (Scheme.Modules.pullback T.hom).obj M ≅ 𝟙_ T.left.Modules) :
    frameTransportEquiv r M a' (frameMap M g e) =
      frameMap ((Scheme.Modules.pullback r).obj M) k (frameTransportEquiv r M a e) := by
  have h : frameMap M (T := T') (T' := (Over.map r).obj U') a'.hom (frameMap M g e) =
      frameMap M (T := (Over.map r).obj U) (T' := (Over.map r).obj U')
        ((Over.map r).map k) (frameMap M (T := T) (T' := (Over.map r).obj U) a.hom e) := by
    rw [frameMap_comp, frameMap_comp, w]
  exact (congrArg (modulePullbackFrameEquiv r M U') h).trans
    (modulePullbackFrameEquiv_naturality r M k
      (frameMap M (T := T) (T' := (Over.map r).obj U) a.hom e)).symm

/-- A natural cartesian comparison transports the entire frame presheaf. -/
def frameTransportNatIso {I : Type v} [Category.{w} I]
    (A : I ⥤ Over Y') (B : I ⥤ Over Y) (a : A ⋙ Over.map r ≅ B) :
    B.op ⋙ framePresheaf M ≅ A.op ⋙ framePresheaf ((Scheme.Modules.pullback r).obj M) :=
  NatIso.ofComponents (fun T => (frameTransportEquiv r M (a.app T.unop)).toIso)
    (fun {T T'} g => TypeCat.homEquiv.injective (funext fun e =>
      frameTransportEquiv_naturality r M
        (T := B.obj T.unop) (T' := B.obj T'.unop)
        (U := A.obj T.unop) (U' := A.obj T'.unop)
        (a.app T.unop) (a.app T'.unop)
        (B.map g.unop) (A.map g.unop) (a.hom.naturality g.unop) e))

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
