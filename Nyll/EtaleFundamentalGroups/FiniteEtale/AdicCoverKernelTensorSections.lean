/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverKernelRestriction
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTransitionKernels
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.SchemeTheory.Modules.Tensor.AffineTensorSections
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionMaps
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Actual transition-kernel sections with sheaf coefficients

The constructed ideal-tensor comparison for the original transition
kernel can be tensored with any quasicoherent coefficient sheaf. Actual
affine tensor sections and the tensor associator identify the result with
the ideal-power tensor of the first-stage sheaf with those coefficients.

On a pure tensor the comparison is the tensor of the original kernel
comparison with the original coefficient section. No local trivialization
of the coefficient sheaf is required.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (N : X.Modules) [N.IsQuasicoherent]

/-- Actual affine sections of the kernel with quasicoherent
coefficients are the ideal-power tensor of the original first stage with those coefficients. -/
def transitionKernelTensorWithSectionsEquiv (U : X.affineOpens) (n : ℕ) :
    (↥((sectionsIdeal f I U) ^ (n + 1)) ⊗[Γ(X, U)]
      Γ(tensor (moduleSheaf f I V 0) N, U)) ≃ₗ[Γ(X, U)]
        Γ(tensor (transitionKernelSheaf f I V n) N, U) := by
  let C : CommRingCat.{u} := Γ(X, U)
  let J : Submodule C C := (sectionsIdeal f I U) ^ (n + 1)
  have hU : IsAffineOpen (U : X.Opens) := U.2
  let e₀ : Γ(tensor (moduleSheaf f I V 0) N, U) ≃ₗ[C]
      (Γ(moduleSheaf f I V 0, U) ⊗[C] Γ(N, U)) :=
    (affineTensorSectionsEquiv (moduleSheaf f I V 0) N U hU).symm
  let eK : (↥J ⊗[C] Γ(moduleSheaf f I V 0, U)) ≃ₗ[C]
      Γ(transitionKernelSheaf f I V n, U) :=
    transitionKernelTensorSectionsEquiv f I V U n
  exact (TensorProduct.congr (LinearEquiv.refl C ↥J) e₀).trans
    ((TensorProduct.assoc C ↥J Γ(moduleSheaf f I V 0, U) Γ(N, U)).symm.trans
      ((TensorProduct.congr eK (LinearEquiv.refl C Γ(N, U))).trans
        (affineTensorSectionsEquiv (transitionKernelSheaf f I V n) N U hU)))

/-- On original pure tensor sections, the comparison is precisely
the tensor of the original kernel comparison with the given coefficient section. -/
theorem transitionKernelTensorWithSectionsEquiv_tmul_tensorSections
    (U : X.affineOpens) (n : ℕ) (a : ↥((sectionsIdeal f I U) ^ (n + 1)))
    (x : Γ(moduleSheaf f I V 0, U)) (y : Γ(N, U)) :
    transitionKernelTensorWithSectionsEquiv f I V N U n
        (a ⊗ₜ[Γ(X, U)] tensorSections x y) =
      tensorSections
        (show Γ(transitionKernelSheaf f I V n, U) from
          transitionKernelTensorSectionsEquiv f I V U n (a ⊗ₜ[Γ(X, U)] x)) y := by
  let e := affineTensorSectionsEquiv (moduleSheaf f I V 0) N U U.2
  have h₀ : e.symm (tensorSections x y) = x ⊗ₜ[Γ(X, U)] y :=
    (congrArg e.symm (affineTensorSectionsEquiv_tmul
      (moduleSheaf f I V 0) N U U.2 x y).symm).trans
      (e.symm_apply_apply (x ⊗ₜ[Γ(X, U)] y))
  simp only [transitionKernelTensorWithSectionsEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  rw [h₀, TensorProduct.assoc_symm_tmul]
  let eK : (↥((sectionsIdeal f I U) ^ (n + 1)) ⊗[Γ(X, U)]
      Γ(moduleSheaf f I V 0, U)) ≃ₗ[Γ(X, U)] Γ(transitionKernelSheaf f I V n, U) :=
    transitionKernelTensorSectionsEquiv f I V U n
  let eN : Γ(N, U) ≃ₗ[Γ(X, U)] Γ(N, U) := LinearEquiv.refl Γ(X, U) Γ(N, U)
  have ht := TensorProduct.congr_tmul eK eN (a ⊗ₜ[Γ(X, U)] x) y
  exact (congrArg (affineTensorSectionsEquiv (transitionKernelSheaf f I V n) N U U.2)
    ht).trans (affineTensorSectionsEquiv_tmul (transitionKernelSheaf f I V n) N U U.2
      (transitionKernelTensorSectionsEquiv f I V U n (a ⊗ₜ[Γ(X, U)] x)) y)

/-- The actual coefficient comparison commutes with every original
restriction between affine opens, including the coefficient-ring restriction. -/
theorem transitionKernelTensorWithSectionsEquiv_restriction
    (U W : X.affineOpens) (h : (W : X.Opens) ≤ U) (n : ℕ)
    (z : ↥((sectionsIdeal f I U) ^ (n + 1)) ⊗[Γ(X, U)]
      Γ(tensor (moduleSheaf f I V 0) N, U)) :
    (tensor (transitionKernelSheaf f I V n) N).presheaf.map (homOfLE h).op
        (transitionKernelTensorWithSectionsEquiv f I V N U n z) =
      transitionKernelTensorWithSectionsEquiv f I V N W n
        (TensorProduct.map (idealPowerRestriction f I h (n + 1))
          (show Γ(tensor (moduleSheaf f I V 0) N, U)
              →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
                Γ(tensor (moduleSheaf f I V 0) N, W) from
            (tensor (moduleSheaf f I V 0) N).val.restrictₛₗ (homOfLE h).op) z) := by
  let C : CommRingCat.{u} := Γ(X, U)
  let D : CommRingCat.{u} := Γ(X, W)
  let ρ : C →+* D := (X.presheaf.map (homOfLE h).op).hom
  let M := moduleSheaf f I V 0
  let T := transitionKernelSheaf f I V n
  let JU : Submodule C C := (sectionsIdeal f I U) ^ (n + 1)
  let JW : Submodule D D := (sectionsIdeal f I W) ^ (n + 1)
  let rM : Γ(tensor M N, U) →ₛₗ[ρ] Γ(tensor M N, W) :=
    (tensor M N).val.restrictₛₗ (homOfLE h).op
  let rT : Γ(tensor T N, U) →ₛₗ[ρ] Γ(tensor T N, W) :=
    (tensor T N).val.restrictₛₗ (homOfLE h).op
  let rI : ↥JU →ₛₗ[ρ] ↥JW := idealPowerRestriction f I h (n + 1)
  let eU := transitionKernelTensorWithSectionsEquiv f I V N U n
  let eW := transitionKernelTensorWithSectionsEquiv f I V N W n
  let a : (↥JU ⊗[C] Γ(tensor M N, U)) →ₛₗ[ρ] Γ(tensor T N, W) :=
    rT.comp eU.toLinearMap
  let b : (↥JU ⊗[C] Γ(tensor M N, U)) →ₛₗ[ρ] Γ(tensor T N, W) :=
    eW.toLinearMap.comp (TensorProduct.map rI rM)
  let pre : (↥JU ⊗[C] (Γ(M, U) ⊗[C] Γ(N, U))) ≃ₗ[C]
      (↥JU ⊗[C] Γ(tensor M N, U)) :=
    TensorProduct.congr (LinearEquiv.refl C ↥JU) (affineTensorSectionsEquiv M N U U.2)
  have hc : a.comp pre.toLinearMap = b.comp pre.toLinearMap := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro c
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change (tensor T N).presheaf.map (homOfLE h).op
        (eU (c ⊗ₜ[C] tensorSections x y)) =
      eW (rI c ⊗ₜ[D] (tensor M N).presheaf.map (homOfLE h).op (tensorSections x y))
    rw [transitionKernelTensorWithSectionsEquiv_tmul_tensorSections,
      map_tensorSections, map_tensorSections,
      transitionKernelTensorWithSectionsEquiv_tmul_tensorSections]
    have hk := transitionKernelTensorSectionsEquiv_restriction f I V U W h n
      (c ⊗ₜ[C] x)
    have ht := TensorProduct.map_tmul (idealPowerRestriction f I h (n + 1))
      (affineSectionRestriction f I V U W h 0) c
      (show affineSectionModule f I V U 0 from x)
    have hk' := hk.trans (congrArg (transitionKernelTensorSectionsEquiv f I V W n) ht)
    exact congrArg
      (fun v : Γ(T, W) => tensorSections (L := T) (M := N) (U := (W : X.Opens)) v
        (N.presheaf.map (homOfLE h).op y)) hk'
  obtain ⟨t, rfl⟩ := pre.surjective z
  exact DFunLike.congr_fun hc t

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
