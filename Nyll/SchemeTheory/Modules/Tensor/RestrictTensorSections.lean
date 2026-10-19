/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Frames.IsFrameOnPullbackLocalSection
import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.Tensor.PullbackTensorObjIsoHomAppPullbackLocalSection
import Nyll.SchemeTheory.Modules.Tensor.RestrictTensor
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionMaps
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Original sections under the restriction tensor comparison

The original adjunction unit for restriction supplies the actual
restricted section. The canonical comparison with pullback maps it to
the original pullback local section. Applying this calculation to both
factors shows that the constructed restriction tensor isomorphism
retains the original tensor of restricted sections.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_pullbackLocalSection

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

private theorem restrictPullback_inv_pullbackLocalSection (M : Y.Modules)
    {U : Y.Opens} (x : Γ(M, U)) :
    ((restrictFunctorIsoPullback j).app M).inv.app (j ⁻¹ᵁ U)
        (pullbackLocalSection j x) =
      (show Γ(M.restrict j, j ⁻¹ᵁ U) from ((restrictAdjunction j).unit.app M).app U x) := by
  let e := (restrictFunctorIsoPullback j).app M
  let y : Γ(M.restrict j, j ⁻¹ᵁ U) := ((restrictAdjunction j).unit.app M).app U x
  have h := PicTanH.pullbackLocalSection_openImmersion j M U x
  have hcancel := congrArg
    (fun k : M.restrict j ⟶ M.restrict j => k.app (j ⁻¹ᵁ U) y) e.hom_inv_id
  exact (congrArg (fun z : Γ((pullback j).obj M, j ⁻¹ᵁ U) =>
    e.inv.app (j ⁻¹ᵁ U) z) h).trans hcancel

/-- The actual restriction tensor comparison sends the original
restricted pure tensor to the tensor of the two original restricted sections. -/
theorem restrictTensorIso_hom_unit_tensor (M N : Y.Modules)
    {U : Y.Opens} (x : Γ(M, U)) (y : Γ(N, U)) :
    (restrictTensorIso j M N).hom.app (j ⁻¹ᵁ U)
        (((restrictAdjunction j).unit.app (tensor M N)).app U (tensorSections x y)) =
      tensorSections (L := M.restrict j) (M := N.restrict j) (U := j ⁻¹ᵁ U)
        (show Γ(M.restrict j, j ⁻¹ᵁ U) from ((restrictAdjunction j).unit.app M).app U x)
        (show Γ(N.restrict j, j ⁻¹ᵁ U) from
          ((restrictAdjunction j).unit.app N).app U y) := by
  let W : X.Opens := j ⁻¹ᵁ U
  let eM := (restrictFunctorIsoPullback j).app M
  let eN := (restrictFunctorIsoPullback j).app N
  let e := pullbackTensorObjIso j M N
  have h₀ := (PicTanH.pullbackLocalSection_openImmersion j (tensor M N) U
    (tensorSections x y)).symm
  have h₁ := congrArg (fun z : Γ((pullback j).obj (tensor M N), W) =>
    (eM.inv ⊗ₘ eN.inv).app W (e.hom.app W z)) h₀
  have h₂ := congrArg
    (fun z : Γ(tensor ((pullback j).obj M) ((pullback j).obj N), W) =>
      (eM.inv ⊗ₘ eN.inv).app W z)
    (pullbackTensorObjIso_hom_app_pullbackLocalSection j x y)
  have h₃ := tensorHom_app_tensorSections eM.inv eN.inv
    (pullbackLocalSection j x) (pullbackLocalSection j y)
  have h₄ := congrArg₂
    (fun a : Γ(M.restrict j, W) => fun b : Γ(N.restrict j, W) => tensorSections a b)
    (restrictPullback_inv_pullbackLocalSection j M x)
    (restrictPullback_inv_pullbackLocalSection j N y)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end AlgebraicGeometry.Scheme.Modules
