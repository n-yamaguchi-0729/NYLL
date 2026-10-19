/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPushforward
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Nyll.SchemeTheory.Modules.Tensor.AffineTensorSections
import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
import Nyll.SchemeTheory.Modules.Tensor.PullbackTensorObjIsoHomAppPullbackLocalSection
import Nyll.SchemeTheory.Modules.Tensor.PullbackTensorSections
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionNaturality
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The actual affine projection formula for quasicoherent modules

The projection morphism is the mate of the pullback tensor comparison
followed by the original adjunction counit. Its value on a pure tensor
is the original section tensored with the original pullback unit.

For an affine morphism and quasicoherent factors, the original section
map is bijective on every affine target open: the source is computed by
the affine tensor comparison, and the target by the actual pullback
tensor comparison over the same target section ring. The affine basis
then gives an isomorphism of the native module sheaves.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) (L : Y.Modules)

/-- The mate defining the projection map for the original two module
sheaves, using the actual pullback comparison and counit. -/
def tensorProjectionMate :
    (pullback f).obj ((pushforward f).obj M ⊗ L) ⟶ M ⊗ (pullback f).obj L :=
  (pullbackTensorObjIso f ((pushforward f).obj M) L).hom ≫
    ((pullbackPushforwardAdjunction f).counit.app M ▷ (pullback f).obj L)

/-- The actual projection morphism for an arbitrary direct-image factor. -/
def tensorProjectionMorphism :
    (pushforward f).obj M ⊗ L ⟶ (pushforward f).obj (M ⊗ (pullback f).obj L) :=
  (pullbackPushforwardAdjunction f).homEquiv _ _ (tensorProjectionMate f M L)

/-- The original projection morphism sends a pure tensor to the
original section tensored with the actual pullback unit. -/
theorem tensorProjectionMorphism_app_tensorSections (U : Y.Opens)
    (x : Γ((pushforward f).obj M, U)) (y : Γ(L, U)) :
    (tensorProjectionMorphism f M L).app U (tensorSections x y) =
      tensorSections (show Γ(M, f ⁻¹ᵁ U) from x) (pullbackLocalSection f y) := by
  let B : X.Modules := (pullback f).obj L
  let C : X.Modules := (pullback f).obj ((pushforward f).obj M) ⊗ B
  let ε : (pullback f).obj ((pushforward f).obj M) ⟶ M :=
    (pullbackPushforwardAdjunction f).counit.app M
  let κ : C ⟶ M ⊗ B := ε ▷ B
  have h₁ := app_pullbackLocalSection f (tensorProjectionMate f M L)
    (tensorSections x y)
  have h₂ := pullbackTensorObjIso_hom_app_pullbackLocalSection f x y
  have h₃ := whiskerRight_app_tensorSections ε B
    (pullbackLocalSection f x) (pullbackLocalSection f y)
  have h₄ := congrArg
    (fun z : Γ(M, f ⁻¹ᵁ U) => tensorSections z (pullbackLocalSection f y))
    (counit_app_pullbackLocalSection f x)
  exact h₁.symm.trans
    ((congrArg (fun z : Γ(C, f ⁻¹ᵁ U) => κ.app (f ⁻¹ᵁ U) z) h₂).trans (h₃.trans h₄))

private def originalDirectImageSectionsEquiv (U : Y.Opens) :
    Γ((pushforward f).obj M, U) ≃ₗ[Γ(Y, U)]
      (ModuleCat.restrictScalars (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom).obj
        ((moduleSectionsFunctor (f ⁻¹ᵁ U)).obj M) where
  toFun := fun x => (show Γ(M, f ⁻¹ᵁ U) from x)
  invFun := fun x => (show Γ(M, f ⁻¹ᵁ U) from x)
  map_add' := fun _ _ => rfl
  map_smul' := by
    intro r x
    let x₀ : Γ(M, f ⁻¹ᵁ U) := x
    change (f.app U).hom r • x₀ = (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom r • x₀
    exact congrArg (fun σ : Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U) => σ.hom r • x₀)
      (f.appLE_eq_app (U := U)).symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

private theorem projection_tensor_comparison (U : Y.Opens)
    (z : Γ((pushforward f).obj M, U) ⊗[Γ(Y, U)] Γ(L, U)) :
    originalDirectImageSectionsEquiv f (M ⊗ (pullback f).obj L) U
        ((tensorProjectionMorphism f M L).app U
          (tensorSectionsMap ((pushforward f).obj M) L U z)) =
      pullbackTensorSectionsMap f U (f ⁻¹ᵁ U) le_rfl M L
        (TensorProduct.congr (originalDirectImageSectionsEquiv f M U)
          (LinearEquiv.refl Γ(Y, U) Γ(L, U)) z) := by
  let R : CommRingCat.{u} := Γ(Y, U)
  let P : ModuleCat.{u} R := (moduleSectionsFunctor U).obj ((pushforward f).obj M)
  let Q : ModuleCat.{u} R := (moduleSectionsFunctor U).obj L
  let α : P ⊗[R] Q →ₗ[R] Γ((pushforward f).obj M ⊗ L, U) :=
    tensorSectionsMap ((pushforward f).obj M) L U
  let γ : Γ((pushforward f).obj M ⊗ L, U) →ₗ[R]
      Γ((pushforward f).obj (M ⊗ (pullback f).obj L), U) :=
    ((tensorProjectionMorphism f M L).val.app (op U)).hom
  let e := originalDirectImageSectionsEquiv f (M ⊗ (pullback f).obj L) U
  let β := pullbackTensorSectionsMap f U (f ⁻¹ᵁ U) le_rfl M L
  let η := TensorProduct.congr (originalDirectImageSectionsEquiv f M U)
    (LinearEquiv.refl R Q)
  have h : e.toLinearMap.comp (γ.comp α) = β.comp η.toLinearMap := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    have h₁ := tensorProjectionMorphism_app_tensorSections f M L U x y
    have h₂ := pullbackTensorSectionsMap_tmul f U (f ⁻¹ᵁ U) le_rfl M L
      (originalDirectImageSectionsEquiv f M U x) y
    have hres : ((pullback f).obj L).presheaf.map
        (homOfLE (le_rfl : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U)).op (pullbackLocalSection f y) =
        pullbackLocalSection f y := by
      change ((pullback f).obj L).presheaf.map (𝟙 (op (f ⁻¹ᵁ U)))
        (pullbackLocalSection f y) = pullbackLocalSection f y
      rw [CategoryTheory.Functor.map_id, CategoryTheory.id_apply]
      rfl
    have h₃ := congrArg (fun v : Γ((pullback f).obj L, f ⁻¹ᵁ U) =>
      tensorSections (show Γ(M, f ⁻¹ᵁ U) from x) v) hres
    exact h₁.trans (h₂.trans h₃).symm
  exact congrArg (fun k => k z) h

/-- On an affine target open, an affine morphism and quasicoherent
factors make the actual projection map on sections bijective. -/
theorem tensorProjectionMorphism_app_bijective [IsAffineHom f]
    [M.IsQuasicoherent] [L.IsQuasicoherent] (U : Y.Opens) (hU : IsAffineOpen U) :
    Function.Bijective ((tensorProjectionMorphism f M L).app U) := by
  have hQC : ((pushforward f).obj M).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom f M
  let α := tensorSectionsMap ((pushforward f).obj M) L U
  let e := originalDirectImageSectionsEquiv f (M ⊗ (pullback f).obj L) U
  let β := pullbackTensorSectionsMap f U (f ⁻¹ᵁ U) le_rfl M L
  let η := TensorProduct.congr (originalDirectImageSectionsEquiv f M U)
    (LinearEquiv.refl Γ(Y, U) Γ(L, U))
  have hα : Function.Bijective α :=
    tensorSectionsMap_bijective ((pushforward f).obj M) L U hU
  have hβ : Function.Bijective β :=
    pullbackTensorSectionsMap_bijective f U (f ⁻¹ᵁ U) le_rfl M L hU (hU.preimage f)
  have hcomp : Function.Bijective (fun z => β (η z)) := hβ.comp η.bijective
  constructor
  · intro x y hxy
    obtain ⟨z, rfl⟩ := hα.surjective x
    obtain ⟨w, rfl⟩ := hα.surjective y
    have h := (projection_tensor_comparison f M L U z).symm.trans
      ((congrArg e hxy).trans (projection_tensor_comparison f M L U w))
    exact congrArg α (hcomp.injective h)
  · intro y
    obtain ⟨z, hz⟩ := hcomp.surjective (e y)
    exact ⟨α z, e.injective ((projection_tensor_comparison f M L U z).trans hz)⟩

private theorem isIso_of_bijective_affine_sections {A B : Y.Modules} (φ : A ⟶ B)
    (h : ∀ U : Y.Opens, IsAffineOpen U → Function.Bijective (φ.app U)) : IsIso φ := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} Y := ⟨A.presheaf, A.isSheaf⟩
  let G : TopCat.Sheaf AddCommGrpCat.{u} Y := ⟨B.presheaf, B.isSheaf⟩
  let ψ : F ⟶ G := ⟨φ.mapPresheaf⟩
  have hb : Opens.IsBasis (Set.range (fun U : Y.affineOpens => U.1)) := by
    rw [Subtype.range_coe_subtype]
    exact Y.isBasis_affineOpens
  have hψ : IsIso ψ := TopCat.Sheaf.isIso_iff_isIso_basis hb
    (fun U => (ConcreteCategory.isIso_iff_bijective (φ.app U.1)).mpr (h U.1 U.2))
  have hForget : IsIso ((TopCat.Sheaf.forget AddCommGrpCat.{u} Y).map ψ) := inferInstance
  have hPresheaf : IsIso ((toPresheaf Y).map φ) := hForget
  exact isIso_of_reflects_iso φ (toPresheaf Y)

/-- The actual projection morphism is an isomorphism for an affine
morphism and two quasicoherent module sheaves. -/
theorem isIso_tensorProjectionMorphism_of_isAffineHom [IsAffineHom f]
    [M.IsQuasicoherent] [L.IsQuasicoherent] : IsIso (tensorProjectionMorphism f M L) :=
  isIso_of_bijective_affine_sections (tensorProjectionMorphism f M L)
    (tensorProjectionMorphism_app_bijective f M L)

/-- The affine projection formula, with the original projection
morphism as its forward map. -/
def affineProjectionFormulaIso [IsAffineHom f] [M.IsQuasicoherent] [L.IsQuasicoherent] :
    (pushforward f).obj M ⊗ L ≅ (pushforward f).obj (M ⊗ (pullback f).obj L) := by
  have h : IsIso (tensorProjectionMorphism f M L) :=
    isIso_tensorProjectionMorphism_of_isAffineHom f M L
  exact asIso (tensorProjectionMorphism f M L)

/-- The affine projection formula keeps the original tensor sections
and the original pullback unit. -/
theorem affineProjectionFormulaIso_hom_tensorSections [IsAffineHom f]
    [M.IsQuasicoherent] [L.IsQuasicoherent] (U : Y.Opens)
    (x : Γ((pushforward f).obj M, U)) (y : Γ(L, U)) :
    (affineProjectionFormulaIso f M L).hom.app U (tensorSections x y) =
      tensorSections (show Γ(M, f ⁻¹ᵁ U) from x) (pullbackLocalSection f y) :=
  tensorProjectionMorphism_app_tensorSections f M L U x y

end AlgebraicGeometry.Scheme.Modules
