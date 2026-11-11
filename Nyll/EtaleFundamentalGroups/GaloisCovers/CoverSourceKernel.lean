/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ExtendedFiberGaloisAction
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# The original generic kernel fixes the actual covering source field

An element of the original generic kernel fixes every point of every
original finite étale covering fiber. At a supplied generic source of
the cover, the literal spectrum action and monomorphism of that source
force it to fix every original covering-field coefficient.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- The original field-source kernel fixes the coefficients of any
actual finite-cover generic source over the same supplied closure. -/
theorem fieldSourceKernel_fixes_coverSource
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K Ω] [Algebra L Ω] [IsSepClosure K Ω] [IsSepClosed Ω]
    {X : Scheme.{u}} [IsIntegral X]
    (W : FiniteEtale X) (p : Spec (.of K) ⟶ X)
    (q : Spec (.of L) ⟶ W.left) [IsPreimmersion q]
    (hpoint : (ξ L Ω ≫ q) ≫ W.hom = ξ K Ω ≫ p)
    (σ : Gal(Ω/K)) (hσ : fieldSourceAbsoluteGaloisHom K Ω p σ = 1)
    (a : L) : σ (algebraMap L Ω a) = algebraMap L Ω a := by
  let x := ξ K Ω ≫ p
  let y := ξ L Ω ≫ q
  let w : (fiber x).obj W := (fiberObjEquivHom x W).symm (Over.homMk y hpoint)
  have hw : fiberObjEquivHom x W w = Over.homMk y hpoint :=
    (fiberObjEquivHom x W).apply_symm_apply _
  have haction := fundamentalGroupHom_point_of_point_action p (ξ K Ω)
    (suppliedGaloisEquivFundamentalGroup K Ω σ) σ.toRingHom
    (suppliedGaloisEquivFundamentalGroup_point K Ω σ) W w
  change (fiberObjEquivHom x W
      ((fieldSourceAbsoluteGaloisHom K Ω p σ).asIso.hom.app W w)).left =
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (fiberObjEquivHom x W w).left at haction
  rw [hσ] at haction
  change (fiberObjEquivHom x W w).left =
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (fiberObjEquivHom x W w).left at haction
  rw [hw] at haction
  have hsource : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ ξ L Ω = ξ L Ω := by
    apply (cancel_mono q).mp
    exact (Category.assoc _ _ q).trans haction.symm
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) =
    Spec.map (CommRingCat.ofHom (algebraMap L Ω)) at hsource
  rw [← Spec.map_comp] at hsource
  have hcoeff := congrArg CommRingCat.Hom.hom (Spec.map_injective hsource)
  exact RingHom.congr_fun hcoeff a

end AlgebraicGeometry.FiniteEtale
