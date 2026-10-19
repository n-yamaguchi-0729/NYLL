/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.PullbackSections
import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.Functoriality.QuasicoherentPullbackSections
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPullback
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Nyll.SchemeTheory.Modules.Tensor.AffineTensorSections
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Tensor sections with a pulled back coefficient module

For subordinate opens, the actual pullback unit and actual sheaf tensor
operation define a map on the tensor product over the original section
ring. Its construction cancels the intervening scalar extension. On
affine opens, quasicoherence makes each of the actual comparison maps
invertible, so the resulting original section map is bijective.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (W : X.Opens)
  (hWU : W ≤ f ⁻¹ᵁ U) (L : X.Modules) (M : Y.Modules)

/-- Tensor an original section with the actual restricted pullback unit,
over the original coefficient ring of the target open. -/
def pullbackTensorSectionsMap :
    ((ModuleCat.restrictScalars (f.appLE U W hWU).hom).obj
        ((moduleSectionsFunctor W).obj L) ⊗[Γ(Y, U)] Γ(M, U)) →ₗ[Γ(Y, U)]
      (ModuleCat.restrictScalars (f.appLE U W hWU).hom).obj
        ((moduleSectionsFunctor W).obj (tensor L ((pullback f).obj M))) := by
  let C : CommRingCat.{u} := Γ(Y, U)
  let D : CommRingCat.{u} := Γ(X, W)
  let σ : C →+* D := (f.appLE U W hWU).hom
  let : Algebra C D := σ.toAlgebra
  let T : ModuleCat.{u} D := (moduleSectionsFunctor W).obj L
  let T₀ : ModuleCat.{u} C := (ModuleCat.restrictScalars σ).obj T
  let P : ModuleCat.{u} C := (moduleSectionsFunctor U).obj M
  let Q : ModuleCat.{u} D := (moduleSectionsFunctor W).obj ((pullback f).obj M)
  let H : ModuleCat.{u} D :=
    (moduleSectionsFunctor W).obj (tensor L ((pullback f).obj M))
  let H₀ : ModuleCat.{u} C := (ModuleCat.restrictScalars σ).obj H
  have : IsScalarTower C D T₀ := IsScalarTower.of_compHom C D T
  have : IsScalarTower C D H₀ := IsScalarTower.of_compHom C D H
  let e : T₀ ⊗[D] (D ⊗[C] P) ≃ₗ[D] T₀ ⊗[C] P :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange C D D T₀ P
  let β : (D ⊗[C] P) →ₗ[D] Q := (pullbackSectionsMap f U W hWU M).hom
  let t : (T₀ ⊗[D] Q) →ₗ[D] H₀ := tensorSectionsMap L ((pullback f).obj M) W
  exact (t.comp ((TensorProduct.map (LinearMap.id : T₀ →ₗ[D] T₀) β).comp
    e.symm.toLinearMap)).restrictScalars C

/-- The comparison retains the actual tensor of the given original
section and the restricted original pullback unit. -/
theorem pullbackTensorSectionsMap_tmul
    (x : (ModuleCat.restrictScalars (f.appLE U W hWU).hom).obj
      ((moduleSectionsFunctor W).obj L)) (y : Γ(M, U)) :
    pullbackTensorSectionsMap f U W hWU L M (x ⊗ₜ[Γ(Y, U)] y) =
      tensorSections (show Γ(L, W) from x)
        (((pullback f).obj M).presheaf.map (homOfLE hWU).op
          (pullbackLocalSection f y)) := by
  let C : CommRingCat.{u} := Γ(Y, U)
  let D : CommRingCat.{u} := Γ(X, W)
  let σ : C →+* D := (f.appLE U W hWU).hom
  let : Algebra C D := σ.toAlgebra
  let T : ModuleCat.{u} D := (moduleSectionsFunctor W).obj L
  let T₀ : ModuleCat.{u} C := (ModuleCat.restrictScalars σ).obj T
  let P : ModuleCat.{u} C := (moduleSectionsFunctor U).obj M
  let Q : ModuleCat.{u} D := (moduleSectionsFunctor W).obj ((pullback f).obj M)
  have : IsScalarTower C D T₀ := IsScalarTower.of_compHom C D T
  let β : (D ⊗[C] P) →ₗ[D] Q := (pullbackSectionsMap f U W hWU M).hom
  let t : (T₀ ⊗[D] Q) →ₗ[D] Γ(tensor L ((pullback f).obj M), W) :=
    tensorSectionsMap L ((pullback f).obj M) W
  have he := TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul C D D
    (M := T₀) (N := P) x y
  have h₁ := congrArg
    (fun z : T₀ ⊗[D] (D ⊗[C] P) => t (TensorProduct.map (LinearMap.id : T₀ →ₗ[D] T₀) β z))
    he
  have h₂ := congrArg t
    (TensorProduct.map_tmul (LinearMap.id : T₀ →ₗ[D] T₀) β x ((1 : D) ⊗ₜ[C] (y : P)))
  have h₃ := congrArg (fun v : Q => tensorSections (show Γ(L, W) from x) v)
    (pullbackSectionsMap_one_tmul f U W hWU M (show Γ(M, U) from y))
  exact h₁.trans (h₂.trans h₃)

/-- For quasicoherent modules and affine subordinate opens, the actual
tensor section map with pulled back coefficients is bijective. -/
theorem pullbackTensorSectionsMap_bijective [L.IsQuasicoherent] [M.IsQuasicoherent]
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) :
    Function.Bijective (pullbackTensorSectionsMap f U W hWU L M) := by
  let C : CommRingCat.{u} := Γ(Y, U)
  let D : CommRingCat.{u} := Γ(X, W)
  let σ : C →+* D := (f.appLE U W hWU).hom
  let : Algebra C D := σ.toAlgebra
  let T : ModuleCat.{u} D := (moduleSectionsFunctor W).obj L
  let T₀ : ModuleCat.{u} C := (ModuleCat.restrictScalars σ).obj T
  let P : ModuleCat.{u} C := (moduleSectionsFunctor U).obj M
  have : IsScalarTower C D T₀ := IsScalarTower.of_compHom C D T
  have : ((pullback f).obj M).IsQuasicoherent := isQuasicoherent_pullback f M
  let e : T₀ ⊗[D] (D ⊗[C] P) ≃ₗ[D] T₀ ⊗[C] P :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange C D D T₀ P
  let β := pullbackSectionsMap f U W hWU M
  have hβ : IsIso β := isIso_pullbackSectionsMap f U W hU hW hWU M
  let eβ := (asIso β).toLinearEquiv
  let eT := TensorProduct.congr (LinearEquiv.refl D T₀) eβ
  exact (tensorSectionsMap_bijective L ((pullback f).obj M) W hW).comp
    (eT.bijective.comp e.symm.bijective)

/-- Original affine tensor sections with pulled back coefficients,
linearly compared over the original target section ring. -/
def affinePullbackTensorSectionsEquiv [L.IsQuasicoherent] [M.IsQuasicoherent]
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) :
    ((ModuleCat.restrictScalars (f.appLE U W hWU).hom).obj
        ((moduleSectionsFunctor W).obj L) ⊗[Γ(Y, U)] Γ(M, U)) ≃ₗ[Γ(Y, U)]
      (ModuleCat.restrictScalars (f.appLE U W hWU).hom).obj
        ((moduleSectionsFunctor W).obj (tensor L ((pullback f).obj M))) :=
  LinearEquiv.ofBijective (pullbackTensorSectionsMap f U W hWU L M)
    (pullbackTensorSectionsMap_bijective f U W hWU L M hU hW)

/-- The affine equivalence sends the original pure tensor to its
original tensor section with the actual pullback unit. -/
theorem affinePullbackTensorSectionsEquiv_tmul [L.IsQuasicoherent] [M.IsQuasicoherent]
    (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (x : (ModuleCat.restrictScalars (f.appLE U W hWU).hom).obj
      ((moduleSectionsFunctor W).obj L)) (y : Γ(M, U)) :
    affinePullbackTensorSectionsEquiv f U W hWU L M hU hW (x ⊗ₜ[Γ(Y, U)] y) =
      tensorSections (show Γ(L, W) from x)
        (((pullback f).obj M).presheaf.map (homOfLE hWU).op
          (pullbackLocalSection f y)) :=
  pullbackTensorSectionsMap_tmul f U W hWU L M x y

end AlgebraicGeometry.Scheme.Modules
