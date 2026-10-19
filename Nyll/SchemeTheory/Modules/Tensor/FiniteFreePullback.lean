/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.Tensor.FiniteFreeSections
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Actual pullback of finite free tensor products

The native finite free tensor product is the actual finite biproduct
of copies of the module. Pullback preserves this biproduct. Combining
that universal comparison with a specified module isomorphism gives
the corresponding comparison of finite free tensor products.

Its projection and section formulas use the original coproduct and
the original adjunction unit. In particular, every original component
section is pulled back and then mapped by the specified isomorphism.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] Abelian.hasFiniteBiproducts

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (J : Type u) [Finite J]
  {L : Y.Modules} {M : X.Modules} (e : (pullback f).obj L ≅ M)

local instance : PreservesBiproduct (fun _ : J => L) (pullback f) := by
  have : PreservesColimitsOfSize.{u, u} (pullback f) :=
    (pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  exact preservesBiproduct_of_preservesCoproduct (pullback f)

/-- Pullback of the actual finite free tensor product, constructed
from its actual biproduct and a specified module comparison. -/
def finiteFreeTensorPullbackIso :
    (pullback f).obj
        (tensor (X := Y) (show Y.Modules from SheafOfModules.free J) L) ≅
      tensor (X := X) (show X.Modules from SheafOfModules.free J) M :=
  (pullback f).mapIso (finiteFreeTensorIsoBiproduct J L) ≪≫
    (pullback f).mapBiproduct (fun _ : J => L) ≪≫
    biproduct.mapIso (fun _ : J => e) ≪≫ (finiteFreeTensorIsoBiproduct J M).symm

/-- Each original coordinate projection commutes with the actual
pullback comparison. -/
theorem finiteFreeTensorPullbackIso_hom_projection (j : J) :
    (finiteFreeTensorPullbackIso f J e).hom ≫
        (finiteFreeTensorIsoBiproduct J M).hom ≫ biproduct.π (fun _ : J => M) j =
      (pullback f).map
        ((finiteFreeTensorIsoBiproduct J L).hom ≫ biproduct.π (fun _ : J => L) j) ≫
          e.hom := by
  let a : (tensor (X := Y) (show Y.Modules from SheafOfModules.free J) L) ≅
      ⨁ (fun _ : J => L) := finiteFreeTensorIsoBiproduct J L
  let b : (pullback f).obj (⨁ (fun _ : J => L)) ≅
      ⨁ (fun _ : J => (pullback f).obj L) :=
    (pullback f).mapBiproduct (fun _ : J => L)
  let c : (⨁ (fun _ : J => (pullback f).obj L)) ≅ ⨁ (fun _ : J => M) :=
    biproduct.mapIso (fun _ : J => e)
  let z : (tensor (X := X) (show X.Modules from SheafOfModules.free J) M) ≅
      ⨁ (fun _ : J => M) := finiteFreeTensorIsoBiproduct J M
  have hb : b.hom ≫ biproduct.π (fun _ : J => (pullback f).obj L) j =
      (pullback f).map (biproduct.π (fun _ : J => L) j) :=
    biproduct.lift_π (fun k : J => (pullback f).map (biproduct.π (fun _ : J => L) k)) j
  have hc : c.hom ≫ biproduct.π (fun _ : J => M) j =
      biproduct.π (fun _ : J => (pullback f).obj L) j ≫ e.hom :=
    biproduct.map_π (fun _ : J => e.hom) j
  change (((pullback f).map a.hom ≫ b.hom ≫ c.hom ≫ z.inv) ≫
      z.hom ≫ biproduct.π (fun _ : J => M) j) = _
  calc
    _ = (pullback f).map a.hom ≫
        (b.hom ≫ (c.hom ≫ biproduct.π (fun _ : J => M) j)) := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = (pullback f).map a.hom ≫
        (b.hom ≫ (biproduct.π (fun _ : J => (pullback f).obj L) j ≫ e.hom)) :=
      congrArg (fun v => (pullback f).map a.hom ≫ (b.hom ≫ v)) hc
    _ = (pullback f).map a.hom ≫
        ((pullback f).map (biproduct.π (fun _ : J => L) j) ≫ e.hom) := by
      rw [← Category.assoc b.hom, hb]
    _ = (pullback f).map
        (a.hom ≫ biproduct.π (fun _ : J => L) j) ≫ e.hom := by
      rw [Functor.map_comp, Category.assoc]

/-- Each coordinate of an original pulled-back section is the
corresponding pulled-back original coordinate. -/
theorem finiteFreeTensorPullbackIso_hom_section_coordinate (U : Y.Opens)
    (s : Γ(tensor (X := Y) (show Y.Modules from SheafOfModules.free J) L, U)) (j : J) :
    ((finiteFreeTensorIsoBiproduct J M).hom ≫ biproduct.π (fun _ : J => M) j).app
        (f ⁻¹ᵁ U) ((finiteFreeTensorPullbackIso f J e).hom.app (f ⁻¹ᵁ U)
          (pullbackLocalSection f s)) =
      e.hom.app (f ⁻¹ᵁ U) (pullbackLocalSection f
        (((finiteFreeTensorIsoBiproduct J L).hom ≫
          biproduct.π (fun _ : J => L) j).app U s)) := by
  let p : tensor (X := Y) (show Y.Modules from SheafOfModules.free J) L ⟶ L :=
    (finiteFreeTensorIsoBiproduct J L).hom ≫ biproduct.π (fun _ : J => L) j
  have h := congrArg
    (fun v : (pullback f).obj
      (tensor (X := Y) (show Y.Modules from SheafOfModules.free J) L) ⟶ M =>
        v.app (f ⁻¹ᵁ U) (pullbackLocalSection f s))
    (finiteFreeTensorPullbackIso_hom_projection f J e j)
  exact h.trans (congrArg (e.hom.app (f ⁻¹ᵁ U)) (pullbackLocalSection_app f p s).symm)

end AlgebraicGeometry.Scheme.Modules
