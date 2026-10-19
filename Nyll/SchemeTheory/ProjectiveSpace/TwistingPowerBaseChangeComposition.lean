/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Frames.FrameHomExt
import Nyll.SchemeTheory.Modules.Frames.IsFrameOnPullbackLocalSection
import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerFrames
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.StandardChartsBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.CoefficientMapComposition
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPolynomialBaseChange
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Composition of the actual twisting-power coefficient comparisons

Both routes through successive coefficient extensions send each original
twice-pulled coordinate power to the corresponding coordinate power.
Those sections are actual local frames on the standard cover. Their
values therefore prove equality of the original comparison morphisms.

The equality retains the native pullback composition and congruence maps.
It will make the transition of an original thickened-level presentation
agree with the original coefficient transition of its polynomial matrix.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_pullbackLocalSection

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem pullbackCongr_hom_app_pullback_top
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : Y.Modules) (s : Γ(M, ⊤)) :
    ((pullbackCongr h).hom.app M).app ⊤ (pullbackLocalSection f s) =
      pullbackLocalSection g s := by
  cases h
  rfl

private theorem comparison_comp_on_frames
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (r : X ⟶ Z)
    (h : f ≫ g = r) (L : Z.Modules) (M : Y.Modules) (N : X.Modules)
    (eg : (Scheme.Modules.pullback g).obj L ≅ M)
    (ef : (Scheme.Modules.pullback f).obj M ≅ N)
    (er : (Scheme.Modules.pullback r).obj L ≅ N)
    {ι : Type u} (U : ι → X.Opens) (a : ι → Γ(L, ⊤))
    (b : ι → Γ(M, ⊤)) (c : ι → Γ(N, ⊤))
    (hframe : ∀ i, IsFrameOn (pullbackLocalSection f (pullbackLocalSection g (a i))) (U i))
    (hcover : ⨆ i, U i = ⊤)
    (hg : ∀ i, eg.hom.app ⊤ (pullbackLocalSection g (a i)) = b i)
    (hf : ∀ i, ef.hom.app ⊤ (pullbackLocalSection f (b i)) = c i)
    (hr : ∀ i, er.hom.app ⊤ (pullbackLocalSection r (a i)) = c i) :
    (Scheme.Modules.pullback f).map eg.hom ≫ ef.hom =
      (pullbackComp f g).hom.app L ≫ (pullbackCongr h).hom.app L ≫ er.hom := by
  apply hom_ext_of_frame_cover U
    (fun i => pullbackLocalSection f (pullbackLocalSection g (a i))) hframe hcover
  intro i
  have hp : ((Scheme.Modules.pullback f).map eg.hom ≫ ef.hom).app ⊤
      (pullbackLocalSection f (pullbackLocalSection g (a i))) = c i := by
    change ef.hom.app ⊤ (((Scheme.Modules.pullback f).map eg.hom).app ⊤
      (pullbackLocalSection f (pullbackLocalSection g (a i)))) = c i
    have hn : ((Scheme.Modules.pullback f).map eg.hom).app ⊤
        (pullbackLocalSection f (pullbackLocalSection g (a i))) =
        pullbackLocalSection f (eg.hom.app ⊤ (pullbackLocalSection g (a i))) :=
      (pullbackLocalSection_app f eg.hom (pullbackLocalSection g (a i))).symm
    exact (congrArg (ef.hom.app ⊤) hn).trans
      ((congrArg (fun y : Γ(M, ⊤) => ef.hom.app ⊤ (pullbackLocalSection f y))
        (hg i)).trans (hf i))
  have hq : ((pullbackComp f g).hom.app L ≫
      (pullbackCongr h).hom.app L ≫ er.hom).app ⊤
      (pullbackLocalSection f (pullbackLocalSection g (a i))) = c i := by
    change er.hom.app ⊤ (((pullbackCongr h).hom.app L).app ⊤
      (((pullbackComp f g).hom.app L).app ⊤
        (pullbackLocalSection f (pullbackLocalSection g (a i))))) = c i
    have hc : ((pullbackComp f g).hom.app L).app ⊤
        (pullbackLocalSection f (pullbackLocalSection g (a i))) =
        pullbackLocalSection (f ≫ g) (a i) :=
      PicTanH.pullbackComp_hom_app_app_pullbackLocalSection f g L ⊤ (a i)
    have he : ((pullbackCongr h).hom.app L).app ⊤
        (pullbackLocalSection (f ≫ g) (a i)) = pullbackLocalSection r (a i) :=
      pullbackCongr_hom_app_pullback_top h L (a i)
    exact (congrArg (fun y : Γ((Scheme.Modules.pullback (f ≫ g)).obj L, ⊤) =>
      er.hom.app ⊤ (((pullbackCongr h).hom.app L).app ⊤ y)) hc).trans
        ((congrArg (er.hom.app ⊤) he).trans (hr i))
  exact hp.trans hq.symm

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] (n d : ℕ)

/-- Successive coefficient changes of the actual twisting power agree
with the direct change through the original pullback composition map. -/
theorem twistingPowerBaseChangeIso_hom_comp
    (h : (algebraMap A B).comp (algebraMap R A) = algebraMap R B) :
    (Scheme.Modules.pullback (map A B n)).map (twistingPowerBaseChangeIso R A n d).hom ≫
        (twistingPowerBaseChangeIso A B n d).hom =
      (pullbackComp (map A B n) (map R A n)).hom.app ((twistingSheaf R n).tensorPow d) ≫
        (pullbackCongr (map_comp_of_algebraMap_comp_eq R A B n h)).hom.app
          ((twistingSheaf R n).tensorPow d) ≫ (twistingPowerBaseChangeIso R B n d).hom := by
  apply comparison_comp_on_frames (map A B n) (map R A n) (map R B n)
    (map_comp_of_algebraMap_comp_eq R A B n h)
    ((twistingSheaf R n).tensorPow d) ((twistingSheaf A n).tensorPow d)
    ((twistingSheaf B n).tensorPow d)
    (twistingPowerBaseChangeIso R A n d) (twistingPowerBaseChangeIso A B n d)
    (twistingPowerBaseChangeIso R B n d) (twistingCover B n)
    (fun j => tensorPowSection (twistingCoordinateSection R n j.down) d)
    (fun j => tensorPowSection (twistingCoordinateSection A n j.down) d)
    (fun j => tensorPowSection (twistingCoordinateSection B n j.down) d)
    ?_ (iSup_twistingCover B n)
    (fun j => twistingPowerBaseChangeIso_hom_coordinatePower R A n d j.down)
    (fun j => twistingPowerBaseChangeIso_hom_coordinatePower A B n d j.down)
    (fun j => twistingPowerBaseChangeIso_hom_coordinatePower R B n d j.down)
  intro j
  have hpower :=
    (isFrameOn_twistingCoordinateSection R n j.down).tensorPowSection_monoidalV2 d
  have hfirst := hpower.pullbackLocalSection (map R A n)
  have hframe := hfirst.pullbackLocalSection (map A B n)
  rw [map_preimage_basicOpen_X, map_preimage_basicOpen_X] at hframe
  exact hframe

end AlgebraicGeometry.ProjSpace
