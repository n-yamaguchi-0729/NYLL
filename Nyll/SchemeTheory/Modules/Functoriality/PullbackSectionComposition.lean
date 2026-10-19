/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.PullbackSections
import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.Frames.IsFrameOnPullbackLocalSection
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Actual subordinate section units and pullback composition

The original pullback composition isomorphism respects the actual
adjunction units after restriction to any subordinate opens. Consequently
a commuting square gives an actual comparison of iterated pullbacks
that retains both original restricted unit sections.

The square in the affine application is supplied by `SpecMap_appLE_fromSpec`.
No section comparison or invertibility assertion is an input here.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_pullbackLocalSection

/-- Composition of actual pullback units on arbitrary subordinate opens
is respected by the original pullback composition isomorphism. -/
theorem pullbackUnitSections_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (hVU : V ≤ g ⁻¹ᵁ U) (hWV : W ≤ f ⁻¹ᵁ V) (x : Γ(M, U)) :
    let hWU : W ≤ (f ≫ g) ⁻¹ᵁ U := hWV.trans (fun _ hz => hVU hz)
    ((pullbackComp f g).hom.app M).app W
        ((pullbackUnitSections f V W hWV).app ((pullback g).obj M)
          ((pullbackUnitSections g U V hVU).app M x)) =
      (pullbackUnitSections (f ≫ g) U W hWU).app M x := by
  intro hWU
  let N : Y.Modules := (pullback g).obj M
  let L : X.Modules := (pullback f).obj N
  let T : X.Modules := (pullback (f ≫ g)).obj M
  let i : V ⟶ g ⁻¹ᵁ U := homOfLE hVU
  let j : W ⟶ f ⁻¹ᵁ V := homOfLE hWV
  let k : f ⁻¹ᵁ V ⟶ f ⁻¹ᵁ g ⁻¹ᵁ U := (TopologicalSpace.Opens.map f.base).map i
  let t : W ⟶ (f ≫ g) ⁻¹ᵁ U := homOfLE hWU
  let e : L ≅ T := (pullbackComp f g).app M
  let v : Γ(N, g ⁻¹ᵁ U) := pullbackLocalSection g x
  let z : Γ(L, f ⁻¹ᵁ g ⁻¹ᵁ U) := pullbackLocalSection f v
  have h₁ := congrArg (fun a : Γ(L, f ⁻¹ᵁ V) => e.hom.app W (L.presheaf.map j.op a))
    (map_pullbackLocalSection f i v).symm
  have hc : L.presheaf.map k.op ≫ L.presheaf.map j.op = L.presheaf.map t.op :=
    (L.presheaf.map_comp k.op j.op).symm.trans
      (congrArg (fun a : op (f ⁻¹ᵁ g ⁻¹ᵁ U) ⟶ op W => L.presheaf.map a)
        (Subsingleton.elim (k.op ≫ j.op) t.op))
  have h₂ := congrArg (fun a : Γ(L, f ⁻¹ᵁ g ⁻¹ᵁ U) ⟶ Γ(L, W) => e.hom.app W (a z)) hc
  have h₃ := congrArg (fun a : Γ(L, (f ≫ g) ⁻¹ᵁ U) ⟶ Γ(T, W) => a z)
    (e.hom.mapPresheaf.naturality t.op)
  have h₄ := congrArg (fun a : Γ(T, (f ≫ g) ⁻¹ᵁ U) => T.presheaf.map t.op a)
    (PicTanH.pullbackComp_hom_app_app_pullbackLocalSection f g M U x)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- Transport along equality of the original scheme morphisms preserves
their original unit sections on every subordinate open. -/
theorem pullbackUnitSections_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : Y.Modules) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) (x : Γ(M, U)) :
    ((pullbackCongr h).hom.app M).app V ((pullbackUnitSections f U V hf).app M x) =
      (pullbackUnitSections g U V hg).app M x := by
  cases h
  rfl

/-- The actual comparison of iterated pullbacks for a commuting square. -/
def pullbackSquareIso {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (k : Y' ⟶ Y)
    (h : j ≫ f = g ≫ k) (M : Y.Modules) :
    (pullback j).obj ((pullback f).obj M) ≅ (pullback g).obj ((pullback k).obj M) :=
  (pullbackComp j f).app M ≪≫ (pullbackCongr h).app M ≪≫ ((pullbackComp g k).app M).symm

/-- The square comparison retains the actual unit sections after the
specified restrictions on both paths around the square. -/
theorem pullbackSquareIso_hom_unit {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (k : Y' ⟶ Y)
    (h : j ≫ f = g ≫ k) (M : Y.Modules) (U : Y.Opens)
    (V : X.Opens) (V' : Y'.Opens) (W : X'.Opens)
    (hVU : V ≤ f ⁻¹ᵁ U) (hV'U : V' ≤ k ⁻¹ᵁ U)
    (hWV : W ≤ j ⁻¹ᵁ V) (hWV' : W ≤ g ⁻¹ᵁ V') (x : Γ(M, U)) :
    (pullbackSquareIso f g j k h M).hom.app W
        ((pullbackUnitSections j V W hWV).app ((pullback f).obj M)
          ((pullbackUnitSections f U V hVU).app M x)) =
      (pullbackUnitSections g V' W hWV').app ((pullback k).obj M)
        ((pullbackUnitSections k U V' hV'U).app M x) := by
  let A : X'.Modules := (pullback j).obj ((pullback f).obj M)
  let B : X'.Modules := (pullback (j ≫ f)).obj M
  let C : X'.Modules := (pullback (g ≫ k)).obj M
  let D : X'.Modules := (pullback g).obj ((pullback k).obj M)
  let e₁ : A ≅ B := (pullbackComp j f).app M
  let e₂ : B ≅ C := (pullbackCongr h).app M
  let e₃ : D ≅ C := (pullbackComp g k).app M
  let hj : W ≤ (j ≫ f) ⁻¹ᵁ U := hWV.trans (fun _ hz => hVU hz)
  let hg : W ≤ (g ≫ k) ⁻¹ᵁ U := hWV'.trans (fun _ hz => hV'U hz)
  let y : Γ(D, W) := (pullbackUnitSections g V' W hWV').app ((pullback k).obj M)
    ((pullbackUnitSections k U V' hV'U).app M x)
  have h₁ := congrArg (fun a : Γ(B, W) => e₃.inv.app W (e₂.hom.app W a))
    (pullbackUnitSections_comp j f M U V W hVU hWV x)
  have h₂ := congrArg (fun a : Γ(C, W) => e₃.inv.app W a)
    (pullbackUnitSections_congr h M U W hj hg x)
  have h₃ := congrArg (fun a : Γ(C, W) => e₃.inv.app W a)
    (pullbackUnitSections_comp g k M U V' W hV'U hWV' x).symm
  have h₄ := congrArg (fun a : D ⟶ D => a.app W y) e₃.hom_inv_id
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end AlgebraicGeometry.Scheme.Modules
