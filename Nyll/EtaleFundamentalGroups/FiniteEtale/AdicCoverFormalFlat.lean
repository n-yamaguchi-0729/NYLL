/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineProjective
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverFormalModule
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FlatAssociatedGraded
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.Operations

/-!
# Flat affine sections and actual layers of the formal cover module

The constructed module is projective over the completed affine coefficient
ring. Flatness of that completion over the original Noetherian coefficient
ring, followed by the actual native section comparison, proves flatness
of the original affine sections of the inverse-limit module sheaf.

Its original ideal-power layers are therefore computed by tensoring with
the original first-stage cover sections. The comparison retains the actual
native sheaf projection and sends each pure tensor to its actual scalar
multiple before taking the original associated-graded quotient.
-/

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))

/-- The constructed completed affine module is flat also over the
original coefficient ring, with its original restricted scalar action. -/
theorem completedAffineSections_flat_original (U : X.affineOpens) :
    Module.Flat Γ(X, U) (completedAffineSections f I V U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have : Module.Flat (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
      (completedAffineSections f I V U) := completedAffineSections_flat f I V U
  exact Module.Flat.trans Γ(X, U) (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
    (completedAffineSections f I V U)

/-- The native affine sections of the actual inverse-limit sheaf are
flat over the original affine coordinate ring. -/
theorem formalAffineSectionModule_flat (U : X.affineOpens) :
    Module.Flat Γ(X, U) (formalAffineSectionModule f I V U) := by
  have : Module.Flat Γ(X, U) (completedAffineSections f I V U) :=
    completedAffineSections_flat_original f I V U
  exact Module.Flat.of_linearEquiv (formalAffineCompletionEquiv f I V U)

private def formalAffineFirstReductionEquiv (U : X.affineOpens) :
    ((formalAffineSectionModule f I V U) ⧸
      ((sectionsIdeal f I U) •
        (⊤ : Submodule Γ(X, U) (formalAffineSectionModule f I V U)))) ≃ₗ[Γ(X, U)]
      affineSectionModule f I V U 0 :=
  (Submodule.quotEquivOfEq
    ((sectionsIdeal f I U) •
      (⊤ : Submodule Γ(X, U) (formalAffineSectionModule f I V U)))
    ((sectionsIdeal f I U) ^ (0 + 1) •
      (⊤ : Submodule Γ(X, U) (formalAffineSectionModule f I V U)))
    (by rw [pow_one])).trans (formalAffineReductionEquiv f I V U 0)

private theorem formalAffineFirstReductionEquiv_mk (U : X.affineOpens)
    (x : formalAffineSectionModule f I V U) :
    formalAffineFirstReductionEquiv f I V U (Submodule.Quotient.mk x) =
      formalAffineProjection f I V U 0 x :=
  formalAffineReductionEquiv_mk f I V U 0 x

/-- The actual associated-graded layer of the native formal sections
is computed from the original first-stage cover sections. -/
def formalAffineLayerTensorEquiv (U : X.affineOpens) (n : ℕ) :
    ↥((sectionsIdeal f I U) ^ n) ⊗[Γ(X, U)] (affineSectionModule f I V U 0) ≃ₗ[Γ(X, U)]
      ((sectionsIdeal f I U).stableFiltration
        (⊤ : Submodule Γ(X, U) (formalAffineSectionModule f I V U))).gradeModule n := by
  have : Module.Flat Γ(X, U) (formalAffineSectionModule f I V U) :=
    formalAffineSectionModule_flat f I V U
  exact (TensorProduct.congr (LinearEquiv.refl Γ(X, U) ↥((sectionsIdeal f I U) ^ n))
    (formalAffineFirstReductionEquiv f I V U).symm).trans
      (AdicFlatLayers.layerTensorEquiv (formalAffineSectionModule f I V U)
        (sectionsIdeal f I U) n)

/-- The original sheaf projection and scalar multiplication compute
the layer comparison on a pure tensor, before taking the actual quotient. -/
theorem formalAffineLayerTensorEquiv_tmul_projection (U : X.affineOpens) (n : ℕ)
    (a : ↥((sectionsIdeal f I U) ^ n)) (x : formalAffineSectionModule f I V U) :
    formalAffineLayerTensorEquiv f I V U n
        (a ⊗ₜ[Γ(X, U)] formalAffineProjection f I V U 0 x) =
      Submodule.Quotient.mk
        (⟨a.val • x, Submodule.smul_mem_smul a.property
          (Submodule.mem_top : x ∈
            (⊤ : Submodule Γ(X, U) (formalAffineSectionModule f I V U)))⟩ :
          ((sectionsIdeal f I U).stableFiltration
            (⊤ : Submodule Γ(X, U) (formalAffineSectionModule f I V U))).N n) := by
  have : Module.Flat Γ(X, U) (formalAffineSectionModule f I V U) :=
    formalAffineSectionModule_flat f I V U
  have hfirst : (formalAffineFirstReductionEquiv f I V U).symm
      (formalAffineProjection f I V U 0 x) = Submodule.Quotient.mk x :=
    (LinearEquiv.symm_apply_eq _).mpr (formalAffineFirstReductionEquiv_mk f I V U x).symm
  change AdicFlatLayers.layerTensorEquiv (formalAffineSectionModule f I V U)
    (sectionsIdeal f I U) n
      ((TensorProduct.congr (LinearEquiv.refl Γ(X, U) ↥((sectionsIdeal f I U) ^ n))
        (formalAffineFirstReductionEquiv f I V U).symm)
          (a ⊗ₜ[Γ(X, U)] formalAffineProjection f I V U 0 x)) = _
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, hfirst,
    AdicFlatLayers.layerTensorEquiv_tmul_mk]

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
