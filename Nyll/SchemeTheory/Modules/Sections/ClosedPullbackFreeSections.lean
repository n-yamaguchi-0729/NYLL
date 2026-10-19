/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.ClosedImmersionUnit
import Nyll.SchemeTheory.Modules.Functoriality.ClosedImmersionUnitKernel
import Nyll.SchemeTheory.Modules.Sections.FiniteFreeSections
import Nyll.SchemeTheory.RingTheory.AdicCompletion.QuotientFreeSequence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Ideal.Finsupp
import Mathlib.RingTheory.Ideal.Operations

/-!
# Actual free sections on a closed subscheme

The original free-section comparison followed by the original pullback
unit is surjective on affine sections. Its kernel is the defining ideal
times the original free module. Comparing this kernel with the literal
coefficient quotient constructs a linear equivalence with the free
module over the quotient ring. The equivalence retains every original
coefficient vector and its original pullback section.
-/

noncomputable section

universe u

open CategoryTheory Opposite AdicModuleSystem

namespace AlgebraicGeometry.Scheme.Modules

private theorem quotientFreeCoefficients_kernel
    {R : Type u} [CommRing R] (J : Ideal R) (K : Type u) :
    (quotientFreeCoefficients J K).ker = J • (⊤ : Submodule R (K →₀ R)) := by
  let q : R →ₗ[R] R ⧸ J := (Ideal.Quotient.mkₐ R J).toLinearMap
  have hq : q.ker = J • (⊤ : Submodule R R) := by
    apply Submodule.ext
    intro x
    change Ideal.Quotient.mk J x = 0 ↔ x ∈ J • (⊤ : Submodule R R)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.smul_eq_mul, Ideal.mul_top]
  change (Finsupp.mapRange.linearMap (α := K) q).ker = _
  rw [Finsupp.ker_mapRange, hq, Finsupp.submodule_smul, Finsupp.submodule_top]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (K : Type u) [Finite K] (U : Y.affineOpens)

/-- Apply the original free coefficient vector and then the original unit. -/
def closedFreeCoefficientMap :
    (K →₀ Γ(Y, U.1)) →ₗ[Γ(Y, U.1)]
      Γ((pushforward f).obj ((pullback f).obj
        (show Y.Modules from SheafOfModules.free K)), U.1) :=
  let P : Y.Modules := SheafOfModules.free K
  let Q : Y.Modules := (pushforward f).obj ((pullback f).obj P)
  let η : Γ(P, U.1) →ₗ[Γ(Y, U.1)] Γ(Q, U.1) :=
    (((pullbackPushforwardAdjunction f).unit.app P).val.app (op U.1)).hom
  η.comp (finiteFreeSectionsEquiv K U.1).toLinearMap

private theorem closedFreeCoefficientMap_kernel :
    (closedFreeCoefficientMap f K U).ker =
      RingHom.ker (f.app U.1).hom • (⊤ : Submodule Γ(Y, U.1) (K →₀ Γ(Y, U.1))) := by
  let P : Y.Modules := SheafOfModules.free K
  let Q : Y.Modules := (pushforward f).obj ((pullback f).obj P)
  let η : Γ(P, U.1) →ₗ[Γ(Y, U.1)] Γ(Q, U.1) :=
    (((pullbackPushforwardAdjunction f).unit.app P).val.app (op U.1)).hom
  let e : (K →₀ Γ(Y, U.1)) ≃ₗ[Γ(Y, U.1)] Γ(P, U.1) := finiteFreeSectionsEquiv K U.1
  have : P.IsQuasicoherent :=
    inferInstanceAs (SheafOfModules.free (R := Y.ringCatSheaf) K).IsQuasicoherent
  have hη : η.ker = RingHom.ker (f.app U.1).hom •
      (⊤ : Submodule Γ(Y, U.1) Γ(P, U.1)) := by
    apply Submodule.ext
    intro x
    exact pullbackUnit_app_eq_zero_iff_of_isClosedImmersion f P U.1 U.2 x
  have hrange : (⊤ : Submodule Γ(Y, U.1) Γ(P, U.1)) ≤ e.toLinearMap.range := by
    rw [LinearMap.range_eq_top.mpr e.surjective]
  have h : (η.comp e.toLinearMap).ker = RingHom.ker (f.app U.1).hom •
      (⊤ : Submodule Γ(Y, U.1) (K →₀ Γ(Y, U.1))) := by
    rw [LinearMap.ker_comp, hη, Submodule.comap_smul'' e.injective hrange,
      Submodule.comap_top]
  exact h

private theorem closedFreeCoefficientMap_surjective :
    Function.Surjective (closedFreeCoefficientMap f K U) := by
  let P : Y.Modules := SheafOfModules.free K
  have : P.IsQuasicoherent :=
    inferInstanceAs (SheafOfModules.free (R := Y.ringCatSheaf) K).IsQuasicoherent
  exact (pullbackUnit_app_surjective_of_isClosedImmersion f P U.1 U.2).comp
    (finiteFreeSectionsEquiv K U.1).surjective

/-- The actual quotient-free module identifies with the original affine
sections of the pulled-back free module on the closed subscheme. -/
def closedPullbackFreeSectionsEquiv :
    (K →₀ Γ(Y, U.1) ⧸ RingHom.ker (f.app U.1).hom) ≃ₗ[Γ(Y, U.1)]
      Γ((pushforward f).obj ((pullback f).obj
        (show Y.Modules from SheafOfModules.free K)), U.1) :=
  let q := quotientFreeCoefficients (RingHom.ker (f.app U.1).hom) K
  let b := closedFreeCoefficientMap f K U
  let e₁ := LinearMap.quotKerEquivOfSurjective q
    (quotientFreeCoefficients_surjective (RingHom.ker (f.app U.1).hom) K)
  let e₂ := Submodule.quotEquivOfEq (R := Γ(Y, U.1)) q.ker b.ker
    ((quotientFreeCoefficients_kernel (RingHom.ker (f.app U.1).hom) K).trans
      (closedFreeCoefficientMap_kernel f K U).symm)
  let e₃ := LinearMap.quotKerEquivOfSurjective b (closedFreeCoefficientMap_surjective f K U)
  e₁.symm.trans (e₂.trans e₃)

/-- The constructed equivalence preserves the original coefficient vector
and the literal original adjunction unit. -/
theorem closedPullbackFreeSectionsEquiv_coefficients (c : K →₀ Γ(Y, U.1)) :
    closedPullbackFreeSectionsEquiv f K U
        (quotientFreeCoefficients (RingHom.ker (f.app U.1).hom) K c) =
      ((pullbackPushforwardAdjunction f).unit.app
        (show Y.Modules from SheafOfModules.free K)).app U.1
          (finiteFreeSectionsEquiv K U.1 c) := by
  change (LinearMap.quotKerEquivOfSurjective (closedFreeCoefficientMap f K U)
      (closedFreeCoefficientMap_surjective f K U))
    (Submodule.quotEquivOfEq _ _ _
      ((LinearMap.quotKerEquivOfSurjective
        (quotientFreeCoefficients (RingHom.ker (f.app U.1).hom) K)
        (quotientFreeCoefficients_surjective (RingHom.ker (f.app U.1).hom) K)).symm
          (quotientFreeCoefficients (RingHom.ker (f.app U.1).hom) K c))) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

end AlgebraicGeometry.Scheme.Modules
