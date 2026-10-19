/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Sections.RestrictSemilinear
import Nyll.SchemeTheory.Modules.Tensor.QuasicoherentTensorSections
import Nyll.SchemeTheory.Modules.Tensor.RestrictTensorImageSections
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionMaps
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Actual tensor sections over every affine open

The canonical linear map sends an original pure tensor of sections to
their original sheaf tensor section. On an affine open this map is
bijective for two quasicoherent modules: its comparison with the
constructed spectrum map uses the actual coefficient and section
isomorphisms of the affine chart.

The resulting equivalence has the original structure sheaf section ring
as coefficient ring. Its compatibility with sheaf morphisms and open
restrictions follows from the actual tensor-section operations.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The canonical linear map from the tensor product of original
section modules to the original tensor sheaf's section module. -/
def tensorSectionsMap (M N : X.Modules) (U : X.Opens) :
    (Γ(M, U) ⊗[Γ(X, U)] Γ(N, U)) →ₗ[Γ(X, U)] Γ(tensor M N, U) :=
  TensorProduct.lift (tensorSectionsBilin M N U)

/-- The canonical section map retains the actual pure tensor section. -/
theorem tensorSectionsMap_tmul (M N : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) :
    tensorSectionsMap M N U (x ⊗ₜ[Γ(X, U)] y) = tensorSections x y := rfl

/-- The canonical tensor-section map is natural for the given module
morphisms and their actual maps on sections. -/
theorem tensorSectionsMap_naturality {M M' N N' : X.Modules}
    (φ : M ⟶ M') (ψ : N ⟶ N') (U : X.Opens)
    (z : Γ(M, U) ⊗[Γ(X, U)] Γ(N, U)) :
    tensorSectionsMap M' N' U
        (TensorProduct.map
          (show Γ(M, U) →ₗ[Γ(X, U)] Γ(M', U) from (φ.val.app (op U)).hom)
          (show Γ(N, U) →ₗ[Γ(X, U)] Γ(N', U) from (ψ.val.app (op U)).hom) z) =
      (φ ⊗ₘ ψ).app U (tensorSectionsMap M N U z) := by
  let α : Γ(M, U) →ₗ[Γ(X, U)] Γ(M', U) := (φ.val.app (op U)).hom
  let β : Γ(N, U) →ₗ[Γ(X, U)] Γ(N', U) := (ψ.val.app (op U)).hom
  let δ : Γ(tensor M N, U) →ₗ[Γ(X, U)] Γ(tensor M' N', U) :=
    ((φ ⊗ₘ ψ).val.app (op U)).hom
  let f : (Γ(M, U) ⊗[Γ(X, U)] Γ(N, U)) →ₗ[Γ(X, U)] Γ(tensor M' N', U) :=
    (tensorSectionsMap M' N' U).comp (TensorProduct.map α β)
  let g : (Γ(M, U) ⊗[Γ(X, U)] Γ(N, U)) →ₗ[Γ(X, U)] Γ(tensor M' N', U) :=
    δ.comp (tensorSectionsMap M N U)
  have h : f = g := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact (tensorHom_app_tensorSections φ ψ x y).symm
  exact congrArg (fun k => k z) h

/-- The canonical tensor-section map commutes with the original
restriction maps, including the coefficient restriction homomorphism. -/
theorem tensorSectionsMap_restriction (M N : X.Modules) {U V : X.Opens}
    (i : V ⟶ U) (z : Γ(M, U) ⊗[Γ(X, U)] Γ(N, U)) :
    tensorSectionsMap M N V
        (TensorProduct.map
          (show Γ(M, U) →ₛₗ[(X.presheaf.map i.op).hom] Γ(M, V) from M.val.restrictₛₗ i.op)
          (show Γ(N, U) →ₛₗ[(X.presheaf.map i.op).hom] Γ(N, V) from N.val.restrictₛₗ i.op)
          z) =
      (tensor M N).presheaf.map i.op (tensorSectionsMap M N U z) := by
  let α : Γ(M, U) →ₛₗ[(X.presheaf.map i.op).hom] Γ(M, V) := M.val.restrictₛₗ i.op
  let β : Γ(N, U) →ₛₗ[(X.presheaf.map i.op).hom] Γ(N, V) := N.val.restrictₛₗ i.op
  let δ : Γ(tensor M N, U) →ₛₗ[(X.presheaf.map i.op).hom] Γ(tensor M N, V) :=
    (tensor M N).val.restrictₛₗ i.op
  let f : (Γ(M, U) ⊗[Γ(X, U)] Γ(N, U)) →ₛₗ[(X.presheaf.map i.op).hom]
      Γ(tensor M N, V) :=
    (tensorSectionsMap M N V).comp (TensorProduct.map α β)
  let g : (Γ(M, U) ⊗[Γ(X, U)] Γ(N, U)) →ₛₗ[(X.presheaf.map i.op).hom]
      Γ(tensor M N, V) :=
    δ.comp (tensorSectionsMap M N U)
  have h : f = g := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact (map_tensorSections i x y).symm
  exact congrArg (fun k => k z) h

private theorem tensorSectionsMap_bijective_image {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Bijective (tensorSectionsMap M N (j ''ᵁ ⊤)) := by
  let P : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj (M.restrict j)
  let Q : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj (N.restrict j)
  let T : ModuleCat.{u} R :=
    (moduleSpecΓFunctor (R := R)).obj (tensor (M.restrict j) (N.restrict j))
  let eR : R ≃+* Γ(X, j ''ᵁ ⊤) := specRestrictionRingEquiv j
  have _hσ : RingHomInvPair (eR : R →+* Γ(X, j ''ᵁ ⊤))
      (eR.symm : Γ(X, j ''ᵁ ⊤) →+* R) := RingHomInvPair.of_ringEquiv eR
  have _hσ' : RingHomInvPair (eR.symm : Γ(X, j ''ᵁ ⊤) →+* R)
      (eR : R →+* Γ(X, j ''ᵁ ⊤)) := RingHomInvPair.of_ringEquiv_symm eR
  let eM := specRestrictionSectionsEquiv j M
  let eN := specRestrictionSectionsEquiv j N
  let eS := TensorProduct.congr eM eN
  let e₀ : T ≃ₗ[R]
      (moduleSpecΓFunctor (R := R)).obj ((tensor M N).restrict j) :=
    ((moduleSpecΓFunctor (R := R)).mapIso (restrictTensorIso j M N).symm).toLinearEquiv
  let eT : T ≃+ Γ(tensor M N, j ''ᵁ ⊤) :=
    e₀.toAddEquiv.trans (specRestrictionSectionsEquiv j (tensor M N)).toAddEquiv
  have : (M.restrict j).IsQuasicoherent := isQuasicoherent_restrictFunctor j M
  have : (N.restrict j).IsQuasicoherent := isQuasicoherent_restrictFunctor j N
  let eΓ : (P ⊗[R] Q) ≃ₗ[R] T :=
    specTensorSectionsEquiv (M.restrict j) (N.restrict j)
  have h : ∀ z : P ⊗[R] Q,
      tensorSectionsMap M N (j ''ᵁ ⊤) (eS z) = eT (eΓ z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        have h₁ := restrictTensorIso_hom_restrictAppIso_inv_tensor j M N ⊤ (eM x) (eN y)
        have h₂ := congrArg₂
          (fun a : Γ(M.restrict j, ⊤) => fun b : Γ(N.restrict j, ⊤) => tensorSections a b)
          (eM.symm_apply_apply x) (eN.symm_apply_apply y)
        have ht : eT.symm (tensorSections (eM x) (eN y)) = tensorSections x y :=
          h₁.trans h₂
        exact (eT.apply_symm_apply (tensorSections (eM x) (eN y))).symm.trans
          (congrArg eT ht)
    | add z w hz hw =>
        rw [map_add, map_add, map_add, map_add, hz, hw]
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨x, rfl⟩ := eS.surjective a
    obtain ⟨y, rfl⟩ := eS.surjective b
    exact congrArg eS (eΓ.injective (eT.injective ((h x).symm.trans (hab.trans (h y)))))
  · intro y
    obtain ⟨t, ht⟩ := eT.surjective y
    obtain ⟨z, hz⟩ := eΓ.surjective t
    exact ⟨eS z, (h z).trans ((congrArg eT hz).trans ht)⟩

/-- The original tensor-section map is bijective on every affine
open for two quasicoherent modules. -/
theorem tensorSectionsMap_bijective (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (tensorSectionsMap M N U) := by
  have h := tensorSectionsMap_bijective_image hU.fromSpec M N
  have hImage : hU.fromSpec ''ᵁ ⊤ = U :=
    hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  exact Eq.mp
    (congrArg (fun V : X.Opens => Function.Bijective (tensorSectionsMap M N V)) hImage) h

/-- The original tensor product of section modules over an affine
open is linearly equivalent to the actual tensor sheaf's sections. -/
def affineTensorSectionsEquiv (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) :
    (Γ(M, U) ⊗[Γ(X, U)] Γ(N, U)) ≃ₗ[Γ(X, U)] Γ(tensor M N, U) :=
  LinearEquiv.ofBijective (tensorSectionsMap M N U) (tensorSectionsMap_bijective M N U hU)

/-- The affine equivalence sends the actual pure tensor to the
original tensor section on the same open. -/
theorem affineTensorSectionsEquiv_tmul (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U)
    (x : Γ(M, U)) (y : Γ(N, U)) :
    affineTensorSectionsEquiv M N U hU (x ⊗ₜ[Γ(X, U)] y) = tensorSections x y := rfl

/-- The affine equivalence commutes with the given module morphisms
on both tensor factors and their original section maps. -/
theorem affineTensorSectionsEquiv_naturality {M M' N N' : X.Modules}
    [M.IsQuasicoherent] [M'.IsQuasicoherent]
    [N.IsQuasicoherent] [N'.IsQuasicoherent]
    (φ : M ⟶ M') (ψ : N ⟶ N') (U : X.Opens) (hU : IsAffineOpen U)
    (z : Γ(M, U) ⊗[Γ(X, U)] Γ(N, U)) :
    affineTensorSectionsEquiv M' N' U hU
        (TensorProduct.map
          (show Γ(M, U) →ₗ[Γ(X, U)] Γ(M', U) from (φ.val.app (op U)).hom)
          (show Γ(N, U) →ₗ[Γ(X, U)] Γ(N', U) from (ψ.val.app (op U)).hom) z) =
      (φ ⊗ₘ ψ).app U (affineTensorSectionsEquiv M N U hU z) :=
  tensorSectionsMap_naturality φ ψ U z

/-- The affine equivalence commutes with the original restriction
maps for any inclusion of affine opens. -/
theorem affineTensorSectionsEquiv_restriction (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : V ⟶ U)
    (z : Γ(M, U) ⊗[Γ(X, U)] Γ(N, U)) :
    affineTensorSectionsEquiv M N V hV
        (TensorProduct.map
          (show Γ(M, U) →ₛₗ[(X.presheaf.map i.op).hom] Γ(M, V) from M.val.restrictₛₗ i.op)
          (show Γ(N, U) →ₛₗ[(X.presheaf.map i.op).hom] Γ(N, V) from N.val.restrictₛₗ i.op)
          z) =
      (tensor M N).presheaf.map i.op (affineTensorSectionsEquiv M N U hU z) :=
  tensorSectionsMap_restriction M N i z

end AlgebraicGeometry.Scheme.Modules
