/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Frames.IsFrameOnPullbackLocalSection
import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.LocallyFreeOfRank
import Nyll.SchemeTheory.Modules.Sections.FreeHomSections
import Nyll.SchemeTheory.Modules.Sections.PullbackFreeSections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Composition of the actual free-sheaf pullback comparisons

The original comparisons with a free sheaf commute with pullback
composition. Both paths carry the same twice-pulled original free
generator to the corresponding generator. The universal property
of the original free sheaf proves equality of the native morphisms.

The equality case retains the original pullback congruence, so a
commuting scheme square can be used without replacing its morphisms.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsFrameOn_pullbackLocalSection
open Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme.Modules

/-- The free-source comparison commutes with actual composition of
pullbacks, as a literal equality of native sheaf morphisms. -/
theorem pullbackFreeIso_hom_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (J : Type u) :
    (pullback f).map (pullbackFreeIso g J).hom ≫ (pullbackFreeIso f J).hom =
      (pullbackComp f g).hom.app (show Z.Modules from SheafOfModules.free J) ≫
        (pullbackFreeIso (f ≫ g) J).hom := by
  let A : Z.Modules := SheafOfModules.free J
  let B : Y.Modules := SheafOfModules.free J
  let C : X.Modules := SheafOfModules.free J
  let eg : (pullback g).obj A ≅ B := pullbackFreeIso g J
  let ef : (pullback f).obj B ≅ C := pullbackFreeIso f J
  let ec : (pullback (f ≫ g)).obj A ≅ C := pullbackFreeIso (f ≫ g) J
  let t : (pullback f).obj ((pullback g).obj A) ≅ (pullback (f ≫ g)).obj A :=
    (pullbackComp f g).app A
  let e : (pullback f).obj ((pullback g).obj A) ≅ C := (pullback f).mapIso eg ≪≫ ef
  let p : (pullback f).obj ((pullback g).obj A) ⟶ C :=
    (pullback f).map eg.hom ≫ ef.hom
  let q : (pullback f).obj ((pullback g).obj A) ⟶ C := t.hom ≫ ec.hom
  change p = q
  apply (cancel_epi e.inv).mp
  apply (freeHomTopSectionsEquiv C J).injective
  funext j
  let a : Γ(A, ⊤) := (SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val (op ⊤)
  let b : Γ((pullback g).obj A, ⊤) := pullbackLocalSection g a
  let z : Γ((pullback f).obj ((pullback g).obj A), ⊤) := pullbackLocalSection f b
  let b₀ : Γ(B, ⊤) := (SheafOfModules.freeSection (R := Y.ringCatSheaf) j).val (op ⊤)
  let c : Γ(C, ⊤) := (SheafOfModules.freeSection (R := X.ringCatSheaf) j).val (op ⊤)
  have hgb : eg.hom.app ⊤ b = b₀ :=
    pullbackFreeIso_hom_app_pullback_freeSection g J j ⊤
  have hfc : ef.hom.app ⊤ (pullbackLocalSection f b₀) = c :=
    pullbackFreeIso_hom_app_pullback_freeSection f J j ⊤
  have hnat : ((pullback f).map eg.hom).app ⊤ z =
      pullbackLocalSection f (eg.hom.app ⊤ b) :=
    (pullbackLocalSection_app f eg.hom b).symm
  have hp : p.app ⊤ z = c :=
    (congrArg (ef.hom.app ⊤) hnat).trans
      ((congrArg (fun y : Γ(B, ⊤) => ef.hom.app ⊤ (pullbackLocalSection f y)) hgb).trans hfc)
  have ht : t.hom.app ⊤ z = pullbackLocalSection (f ≫ g) a :=
    PicTanH.pullbackComp_hom_app_app_pullbackLocalSection f g A ⊤ a
  have hcc : ec.hom.app ⊤ (pullbackLocalSection (f ≫ g) a) = c :=
    pullbackFreeIso_hom_app_pullback_freeSection (f ≫ g) J j ⊤
  have hq : q.app ⊤ z = c := (congrArg (ec.hom.app ⊤) ht).trans hcc
  have hinv : e.inv.app ⊤ c = z := by
    have hz := congrArg
      (fun w : (pullback f).obj ((pullback g).obj A) ⟶
        (pullback f).obj ((pullback g).obj A) => w.app ⊤ z) e.hom_inv_id
    exact (congrArg (e.inv.app ⊤) hp.symm).trans hz
  have hp' : (e.inv ≫ p).app ⊤ c = c := (congrArg (p.app ⊤) hinv).trans hp
  have hq' : (e.inv ≫ q).app ⊤ c = c := (congrArg (q.app ⊤) hinv).trans hq
  exact hp'.trans hq'.symm

/-- Equality of scheme morphisms preserves the actual free-source
comparison through the original pullback congruence. -/
theorem pullbackFreeIso_hom_congr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (J : Type u) :
    (pullbackCongr h).hom.app (show Y.Modules from SheafOfModules.free J) ≫
        (pullbackFreeIso g J).hom = (pullbackFreeIso f J).hom := by
  cases h
  exact Category.id_comp (pullbackFreeIso f J).hom

end AlgebraicGeometry.Scheme.Modules
