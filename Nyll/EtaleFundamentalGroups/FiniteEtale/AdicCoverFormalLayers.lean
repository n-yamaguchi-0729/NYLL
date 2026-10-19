/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverFormalFlat
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverFormalModule
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.SchemeTheory.RingTheory.AdicCompletion.AssociatedGradedModule
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Operations

/-!
# Native formal layers and the original cover-transition kernels

The actual affine sheaf projection is surjective and has its proved
ideal-power kernel. Restricting it to the preceding ideal power gives a
surjective map whose kernel is precisely the next filtration member.
Its first isomorphism theorem therefore identifies each native formal
layer with the original last layer of the finite étale cover sections.

In positive degree this is the kernel of the original cover transition.
Combining with flatness of the actual formal sections computes this
kernel from the original first-stage module, including its literal scalar
and projection formula. Completeness of the original affine ring is
neither needed nor assumed.
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

/-- The original ideal-power filtration on the native formal section module. -/
abbrev formalAffineFiltration (U : X.affineOpens) :
    (sectionsIdeal f I U).Filtration (formalAffineSectionModule f I V U) :=
  (sectionsIdeal f I U).stableFiltration
    (⊤ : Submodule Γ(X, U) (formalAffineSectionModule f I V U))

/-- Restriction of the actual sheaf projection to the preceding ideal power. -/
def formalAffineLayerProjection (U : X.affineOpens) (n : ℕ) :
    (formalAffineFiltration f I V U).N n →ₗ[Γ(X, U)]
      ↥((sectionsIdeal f I U) ^ n •
        (⊤ : Submodule Γ(X, U) (affineSectionModule f I V U n))) :=
  LinearMap.codRestrict
    ((sectionsIdeal f I U) ^ n •
      (⊤ : Submodule Γ(X, U) (affineSectionModule f I V U n)))
    ((formalAffineProjection f I V U n).domRestrict
      ((formalAffineFiltration f I V U).N n))
    (fun x => Submodule.smul_top_le_comap_smul_top ((sectionsIdeal f I U) ^ n)
      (formalAffineProjection f I V U n) x.property)

omit [IsLocallyNoetherian X] in
/-- The restricted map is still the literal original sheaf projection. -/
theorem formalAffineLayerProjection_apply (U : X.affineOpens) (n : ℕ)
    (x : (formalAffineFiltration f I V U).N n) :
    (formalAffineLayerProjection f I V U n x).val =
      formalAffineProjection f I V U n x.val := rfl

/-- Every original last-layer section lifts within the preceding
ideal power of the native formal section module. -/
theorem formalAffineLayerProjection_surjective (U : X.affineOpens) (n : ℕ) :
    Function.Surjective (formalAffineLayerProjection f I V U n) := by
  have hmap :
      ((sectionsIdeal f I U) ^ n •
        (⊤ : Submodule Γ(X, U) (formalAffineSectionModule f I V U))).map
          (formalAffineProjection f I V U n) =
      (sectionsIdeal f I U) ^ n •
        (⊤ : Submodule Γ(X, U) (affineSectionModule f I V U n)) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr (formalModuleProjection_app_surjective f I V U n)]
  intro y
  have hy : y.val ∈
      ((sectionsIdeal f I U) ^ n •
        (⊤ : Submodule Γ(X, U) (formalAffineSectionModule f I V U))).map
          (formalAffineProjection f I V U n) := by
    rw [hmap]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- The restricted original projection has exactly the next native
filtration member as its kernel. -/
theorem formalAffineLayerProjection_ker (U : X.affineOpens) (n : ℕ) :
    (formalAffineLayerProjection f I V U n).ker =
      (formalAffineFiltration f I V U).gradeSubmodule n := by
  ext x
  change formalAffineLayerProjection f I V U n x = 0 ↔
    x.val ∈ (sectionsIdeal f I U) ^ (n + 1) •
      (⊤ : Submodule Γ(X, U) (formalAffineSectionModule f I V U))
  have hiff : formalAffineProjection f I V U n x.val = 0 ↔
      x.val ∈ (sectionsIdeal f I U) ^ (n + 1) •
        (⊤ : Submodule Γ(X, U) (formalAffineSectionModule f I V U)) := by
    rw [← LinearMap.mem_ker, formalModuleProjection_app_ker]
  exact ⟨fun hx => hiff.mp (congrArg Subtype.val hx),
    fun hx => Subtype.ext (hiff.mpr hx)⟩

/-- The native formal layer is the actual last ideal-power layer of
the corresponding original cover-section module. -/
def formalAffineLayerEquiv (U : X.affineOpens) (n : ℕ) :
    (formalAffineFiltration f I V U).gradeModule n ≃ₗ[Γ(X, U)]
      ↥((sectionsIdeal f I U) ^ n •
        (⊤ : Submodule Γ(X, U) (affineSectionModule f I V U n))) := by
  let e₁ := Submodule.quotEquivOfEq (R := Γ(X, U))
    (M := (formalAffineFiltration f I V U).N n)
    ((formalAffineFiltration f I V U).gradeSubmodule n)
    (formalAffineLayerProjection f I V U n).ker
    (formalAffineLayerProjection_ker f I V U n).symm
  let e₂ := LinearMap.quotKerEquivOfSurjective (R := Γ(X, U))
    (M := (formalAffineFiltration f I V U).N n)
    (M₂ := ↥((sectionsIdeal f I U) ^ n •
      (⊤ : Submodule Γ(X, U) (affineSectionModule f I V U n))))
    (formalAffineLayerProjection f I V U n)
    (formalAffineLayerProjection_surjective f I V U n)
  exact e₁.trans e₂

/-- A representative is sent to its original native sheaf projection. -/
theorem formalAffineLayerEquiv_mk (U : X.affineOpens) (n : ℕ)
    (x : (formalAffineFiltration f I V U).N n) :
    (formalAffineLayerEquiv f I V U n (Submodule.Quotient.mk x)).val =
      formalAffineProjection f I V U n x.val := by
  have h := LinearMap.quotKerEquivOfSurjective_apply_mk (R := Γ(X, U))
    (M := (formalAffineFiltration f I V U).N n)
    (M₂ := ↥((sectionsIdeal f I U) ^ n •
      (⊤ : Submodule Γ(X, U) (affineSectionModule f I V U n))))
    (f := formalAffineLayerProjection f I V U n)
    (formalAffineLayerProjection_surjective f I V U n) x
  exact (congrArg Subtype.val h).trans (formalAffineLayerProjection_apply f I V U n x)

/-- The positive native formal layer is the kernel of the actual
original affine cover transition. -/
def formalAffineTransitionKernelEquiv (U : X.affineOpens) (n : ℕ) :
    (formalAffineFiltration f I V U).gradeModule (n + 1) ≃ₗ[Γ(X, U)]
      (affineSectionTransition f I V U n).ker :=
  (formalAffineLayerEquiv f I V U (n + 1)).trans
    (LinearEquiv.ofEq
      ((sectionsIdeal f I U) ^ (n + 1) •
        (⊤ : Submodule Γ(X, U) (affineSectionModule f I V U (n + 1))))
      (affineSectionTransition f I V U n).ker
      (moduleTransition_app_ker f I V n U U.property).symm)

/-- The original next-stage projection computes the transition-kernel
comparison on each actual quotient representative. -/
theorem formalAffineTransitionKernelEquiv_mk (U : X.affineOpens) (n : ℕ)
    (x : (formalAffineFiltration f I V U).N (n + 1)) :
    (formalAffineTransitionKernelEquiv f I V U n (Submodule.Quotient.mk x)).val =
      formalAffineProjection f I V U (n + 1) x.val :=
  formalAffineLayerEquiv_mk f I V U (n + 1) x

/-- The original cover-transition kernel is computed from the original
first-stage module and the actual ideal-power coefficients. -/
def formalAffineTensorTransitionKernelEquiv (U : X.affineOpens) (n : ℕ) :
    ↥((sectionsIdeal f I U) ^ (n + 1)) ⊗[Γ(X, U)] (affineSectionModule f I V U 0) ≃ₗ[Γ(X, U)]
      (affineSectionTransition f I V U n).ker :=
  (formalAffineLayerTensorEquiv f I V U (n + 1)).trans
    (formalAffineTransitionKernelEquiv f I V U n)

/-- The kernel comparison multiplies an actual ideal coefficient by
the actual original next-stage projection of the formal section. -/
theorem formalAffineTensorTransitionKernelEquiv_tmul_projection
    (U : X.affineOpens) (n : ℕ) (a : ↥((sectionsIdeal f I U) ^ (n + 1)))
    (x : formalAffineSectionModule f I V U) :
    (formalAffineTensorTransitionKernelEquiv f I V U n
      (a ⊗ₜ[Γ(X, U)] formalAffineProjection f I V U 0 x)).val =
        a.val • formalAffineProjection f I V U (n + 1) x := by
  change (formalAffineTransitionKernelEquiv f I V U n
    (formalAffineLayerTensorEquiv f I V U (n + 1)
      (a ⊗ₜ[Γ(X, U)] formalAffineProjection f I V U 0 x))).val = _
  rw [formalAffineLayerTensorEquiv_tmul_projection]
  exact (formalAffineTransitionKernelEquiv_mk f I V U n
    ⟨a.val • x, Submodule.smul_mem_smul a.property
      (Submodule.mem_top : x ∈
        (⊤ : Submodule Γ(X, U) (formalAffineSectionModule f I V U)))⟩).trans
      ((formalAffineProjection f I V U (n + 1)).map_smul a.val x)

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
