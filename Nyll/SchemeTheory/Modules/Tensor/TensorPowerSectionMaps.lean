/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
import Nyll.SchemeTheory.Modules.Tensor.PullbackTensorObjIsoHomAppPullbackLocalSection
import Nyll.SchemeTheory.Modules.Tensor.PullbackTensorUnitObjIsoHomAppPullbackLocalSectionUnitSection
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerComparison
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionMaps
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionNaturality
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Actual tensor-power section formulas for comparison maps

The recursively constructed tensor-power isomorphisms carry the
original tensor-power sections to the powers of the original images.
The pullback formula uses the actual adjunction-unit section at every
stage and includes the unit section in degree zero.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual tensor-power isomorphism maps a section power to the
power of its image under the original sheaf isomorphism. -/
theorem tensorPowMapIso_hom_app_tensorPowSection
    {X : Scheme.{u}} {L M : X.Modules} (e : L ≅ M) {U : X.Opens}
    (s : Γ(L, U)) (d : ℕ) :
    (tensorPowMapIso e d).hom.app U (tensorPowSection s d) =
      tensorPowSection (e.hom.app U s) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change ((tensorPowMapIso e d).hom ⊗ₘ e.hom).app U
        (tensorSections (tensorPowSection s d) s) =
      tensorSections (tensorPowSection (e.hom.app U s) d) (e.hom.app U s)
    rw [tensorHom_app_tensorSections, ih]

/-- The canonical tensor-power pullback comparison carries the
original pulled-back section power to the power of the original
adjunction-unit pullback section. -/
theorem pullbackTensorPowIso_hom_app_pullbackLocalSection
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) {U : Y.Opens}
    (s : Γ(L, U)) (d : ℕ) :
    (pullbackTensorPowIso f L d).hom.app (f ⁻¹ᵁ U)
        (pullbackLocalSection f (tensorPowSection s d)) =
      tensorPowSection (pullbackLocalSection f s) d := by
  induction d with
  | zero =>
    exact pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection f U
  | succ d ih =>
    change ((pullbackTensorPowIso f L d).hom ▷ (Scheme.Modules.pullback f).obj L).app
        (f ⁻¹ᵁ U)
        ((pullbackTensorObjIso f (L.tensorPow d) L).hom.app (f ⁻¹ᵁ U)
          (pullbackLocalSection f (tensorSections (tensorPowSection s d) s))) =
      tensorSections (tensorPowSection (pullbackLocalSection f s) d)
        (pullbackLocalSection f s)
    rw [pullbackTensorObjIso_hom_app_pullbackLocalSection,
      whiskerRight_app_tensorSections, ih]

end AlgebraicGeometry.Scheme.Modules
