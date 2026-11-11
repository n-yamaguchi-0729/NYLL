/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverKernelRestriction
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygies
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverNativeSyzygyRestriction
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentKernelGlobal
public import Nyll.SchemeTheory.Modules.Tensor.AffineTensorSections
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorSectionMaps
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Native syzygy layers with arbitrary quasicoherent coefficients

The affine tensor-section equivalence tensors an actual ideal/kernel
comparison with any quasicoherent coefficient sheaf. The tensor associator
identifies its source with the original ideal tensor of the first sheaf
with those coefficients. This construction preserves the original sheaf
restrictions whenever the original comparisons do.

For the native syzygy tower, the required comparisons and their
restriction compatibility are supplied by the proved native layer
theorem. No coefficient frame or flatness hypothesis is required.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

section TensorTransport

variable {X : Scheme.{u}} (F T N : X.Modules)
  [F.IsQuasicoherent] [T.IsQuasicoherent] [N.IsQuasicoherent]

/-- Tensor an actual affine ideal comparison with quasicoherent
coefficients, using the original affine tensor-section maps. -/
def tensorAffineEquiv (U : X.affineOpens) (J : Ideal Γ(X, U))
    (e : (↥J ⊗[Γ(X, U)] Γ(F, U)) ≃ₗ[Γ(X, U)] Γ(T, U)) :
    (↥J ⊗[Γ(X, U)] Γ(tensor F N, U)) ≃ₗ[Γ(X, U)] Γ(tensor T N, U) := by
  let R : CommRingCat.{u} := Γ(X, U)
  let e₀ : Γ(tensor F N, U) ≃ₗ[R] (Γ(F, U) ⊗[R] Γ(N, U)) :=
    (affineTensorSectionsEquiv F N U U.2).symm
  exact (TensorProduct.congr (LinearEquiv.refl R ↥J) e₀).trans
    ((TensorProduct.assoc R ↥J Γ(F, U) Γ(N, U)).symm.trans
      ((TensorProduct.congr e (LinearEquiv.refl R Γ(N, U))).trans
        (affineTensorSectionsEquiv T N U U.2)))

/-- On an original tensor section, tensor transport applies the given
comparison to the ideal and first factor and retains the coefficient. -/
theorem tensorAffineEquiv_tmul_tensorSections
    (U : X.affineOpens) (J : Ideal Γ(X, U))
    (e : (↥J ⊗[Γ(X, U)] Γ(F, U)) ≃ₗ[Γ(X, U)] Γ(T, U))
    (a : ↥J) (x : Γ(F, U)) (y : Γ(N, U)) :
    tensorAffineEquiv F T N U J e (a ⊗ₜ[Γ(X, U)] tensorSections x y) =
      tensorSections (e (a ⊗ₜ[Γ(X, U)] x)) y := by
  let e₀ := affineTensorSectionsEquiv F N U U.2
  have h₀ : e₀.symm (tensorSections x y) = x ⊗ₜ[Γ(X, U)] y :=
    (congrArg e₀.symm (affineTensorSectionsEquiv_tmul F N U U.2 x y).symm).trans
      (e₀.symm_apply_apply (x ⊗ₜ[Γ(X, U)] y))
  simp only [tensorAffineEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  rw [h₀, TensorProduct.assoc_symm_tmul]
  let eN : Γ(N, U) ≃ₗ[Γ(X, U)] Γ(N, U) := LinearEquiv.refl Γ(X, U) Γ(N, U)
  have ht := TensorProduct.congr_tmul e eN (a ⊗ₜ[Γ(X, U)] x) y
  exact (congrArg (affineTensorSectionsEquiv T N U U.2) ht).trans
    (affineTensorSectionsEquiv_tmul T N U U.2 (e (a ⊗ₜ[Γ(X, U)] x)) y)

/-- Tensor transport preserves a restriction square for the original
coefficient-ideal map and the original native sheaf restrictions. -/
theorem tensorAffineEquiv_restriction
    (U W : X.affineOpens) (h : (W : X.Opens) ≤ U)
    (JU : Ideal Γ(X, U)) (JW : Ideal Γ(X, W))
    (rI : ↥JU →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] ↥JW)
    (eU : (↥JU ⊗[Γ(X, U)] Γ(F, U)) ≃ₗ[Γ(X, U)] Γ(T, U))
    (eW : (↥JW ⊗[Γ(X, W)] Γ(F, W)) ≃ₗ[Γ(X, W)] Γ(T, W))
    (he : ∀ z : ↥JU ⊗[Γ(X, U)] Γ(F, U),
      T.val.restrictₛₗ (homOfLE h).op (eU z) =
        eW (TensorProduct.map rI
          (show Γ(F, U) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] Γ(F, W)
            from F.val.restrictₛₗ (homOfLE h).op) z))
    (z : ↥JU ⊗[Γ(X, U)] Γ(tensor F N, U)) :
    (tensor T N).presheaf.map (homOfLE h).op (tensorAffineEquiv F T N U JU eU z) =
      tensorAffineEquiv F T N W JW eW
        (TensorProduct.map rI
          (show Γ(tensor F N, U) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
              Γ(tensor F N, W) from
            (tensor F N).val.restrictₛₗ (homOfLE h).op) z) := by
  let R : CommRingCat.{u} := Γ(X, U)
  let S : CommRingCat.{u} := Γ(X, W)
  let ρ : R →+* S := (X.presheaf.map (homOfLE h).op).hom
  let rF : Γ(tensor F N, U) →ₛₗ[ρ] Γ(tensor F N, W) :=
    (tensor F N).val.restrictₛₗ (homOfLE h).op
  let rT : Γ(tensor T N, U) →ₛₗ[ρ] Γ(tensor T N, W) :=
    (tensor T N).val.restrictₛₗ (homOfLE h).op
  let E₁ := tensorAffineEquiv F T N U JU eU
  let E₂ := tensorAffineEquiv F T N W JW eW
  let a : (↥JU ⊗[R] Γ(tensor F N, U)) →ₛₗ[ρ] Γ(tensor T N, W) :=
    rT.comp E₁.toLinearMap
  let b : (↥JU ⊗[R] Γ(tensor F N, U)) →ₛₗ[ρ] Γ(tensor T N, W) :=
    E₂.toLinearMap.comp (TensorProduct.map rI rF)
  let pre : (↥JU ⊗[R] (Γ(F, U) ⊗[R] Γ(N, U))) ≃ₗ[R]
      (↥JU ⊗[R] Γ(tensor F N, U)) :=
    TensorProduct.congr (LinearEquiv.refl R ↥JU) (affineTensorSectionsEquiv F N U U.2)
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
        (E₁ (c ⊗ₜ[R] tensorSections x y)) =
      E₂ (rI c ⊗ₜ[S] (tensor F N).presheaf.map (homOfLE h).op (tensorSections x y))
    rw [tensorAffineEquiv_tmul_tensorSections, map_tensorSections,
      map_tensorSections, tensorAffineEquiv_tmul_tensorSections]
    have hk := he (c ⊗ₜ[R] x)
    have ht := TensorProduct.map_tmul rI
      (show Γ(F, U) →ₛₗ[ρ] Γ(F, W) from F.val.restrictₛₗ (homOfLE h).op) c x
    have hk' := hk.trans (congrArg eW ht)
    exact congrArg
      (fun v : Γ(T, W) => tensorSections (L := T) (M := N) (U := (W : X.Opens)) v
        (N.presheaf.map (homOfLE h).op y)) hk'
  obtain ⟨w, rfl⟩ := pre.surjective z
  exact DFunLike.congr_fun hc w

end TensorTransport

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (L : X.Modules) (d : ℕ) [(L.tensorPow d).IsQuasicoherent]
  (K : Type u) [Finite K]
  (α : ∀ n : ℕ, (show X.Modules from SheafOfModules.free K) ⟶
    moduleSheaf f I V n ⊗ L.tensorPow d)
  (hα : ∀ n : ℕ, α (n + 1) ≫ (moduleTransition f I V n ▷ L.tensorPow d) = α n)
  (hL : IsInvertible L) (hgen : ∀ n : ℕ, Epi (α n))
  (N : X.Modules) [N.IsQuasicoherent]

include hL hgen in
/-- The original native syzygy layers, tensored with any quasicoherent
coefficient sheaf, admit affine ideal-tensor comparisons commuting with
the actual restrictions between independently framed affine opens. -/
theorem exists_levelPresentationKernelTensorWithSectionsEquiv_restriction
    (U W : X.affineOpens) (h : (W : X.Opens) ≤ U)
    (tU : Γ(L.tensorPow d, U)) (htU : IsFrameOn tU (U : X.Opens))
    (tW : Γ(L.tensorPow d, W)) (htW : IsFrameOn tW (W : X.Opens)) (n : ℕ) :
    let M : ℕ → X.Modules := fun k => levelPresentationKernel f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) k (α k)
    let q : ∀ k : ℕ, M (k + 1) ⟶ M k := fun k =>
      levelPresentationKernelTransition f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) α hα k
    ∃ (eU : (↥((sectionsIdeal f I U) ^ (n + 1)) ⊗[Γ(X, U)]
          Γ(tensor (M 0) N, U)) ≃ₗ[Γ(X, U)] Γ(tensor (kernel (q n)) N, U))
      (eW : (↥((sectionsIdeal f I W) ^ (n + 1)) ⊗[Γ(X, W)]
          Γ(tensor (M 0) N, W)) ≃ₗ[Γ(X, W)] Γ(tensor (kernel (q n)) N, W)),
      ∀ z : ↥((sectionsIdeal f I U) ^ (n + 1)) ⊗[Γ(X, U)] Γ(tensor (M 0) N, U),
        (tensor (kernel (q n)) N).presheaf.map (homOfLE h).op (eU z) =
          eW (TensorProduct.map (idealPowerRestriction f I h (n + 1))
            (show Γ(tensor (M 0) N, U) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
                Γ(tensor (M 0) N, W) from
              (tensor (M 0) N).val.restrictₛₗ (homOfLE h).op) z) := by
  intro M q
  obtain ⟨eU, eW, _heU, _heW, he⟩ :=
    exists_levelPresentationKernelTensorEquiv_restriction
      f I V L d K α hα hL hgen U W h tU htU tW htW n
  have : (kernel (q n)).IsQuasicoherent := isQuasicoherent_kernel (q n)
  refine ⟨tensorAffineEquiv (M 0) (kernel (q n)) N U
      ((sectionsIdeal f I U) ^ (n + 1)) eU,
    tensorAffineEquiv (M 0) (kernel (q n)) N W
      ((sectionsIdeal f I W) ^ (n + 1)) eW, ?_⟩
  intro z
  exact tensorAffineEquiv_restriction (M 0) (kernel (q n)) N U W h
    ((sectionsIdeal f I U) ^ (n + 1)) ((sectionsIdeal f I W) ^ (n + 1))
    (idealPowerRestriction f I h (n + 1)) eU eW he z

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
