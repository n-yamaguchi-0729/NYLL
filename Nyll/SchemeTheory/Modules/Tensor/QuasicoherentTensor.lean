/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeAffineLocal
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeAffineSections
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeOfFiniteSections
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Nyll.SchemeTheory.Modules.Tensor.QuasicoherentTensorSections
import Nyll.SchemeTheory.Modules.Tensor.RestrictTensor
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Quasicoherence and finite type of the actual sheaf tensor product

Restrict the native tensor to every canonical affine spectrum. Its
constructed comparison with the tensor of the restricted sheaves and the
actual tilde tensor isomorphism give quasicoherence there. The original
affine presentations then supply global quasicoherence.

When both sheaves have finite type, the actual affine section modules
are finite. Their tensor product is finite, and the original tensor
section isomorphism gives finite type on each affine spectrum. The local
finite generating families are transported back to the original scheme.
No Noetherian, separation, flatness, or finite-presentation hypothesis
is needed.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The native tensor of two quasicoherent sheaves is quasicoherent,
by the actual affine restrictions and tilde tensor comparison. -/
theorem isQuasicoherent_tensor (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (tensor M N).IsQuasicoherent := by
  apply isQuasicoherent_of_affineSpecRestrictions (tensor M N)
  intro U hU
  let j : Spec Γ(X, U) ⟶ X := hU.fromSpec
  have : (M.restrict j).IsQuasicoherent := isQuasicoherent_restrictFunctor j M
  have : (N.restrict j).IsQuasicoherent := isQuasicoherent_restrictFunctor j N
  have h : (tensor (M.restrict j) (N.restrict j)).IsQuasicoherent :=
    isQuasicoherent_tensor_toSpec (M.restrict j) (N.restrict j)
  let e := (sheafOfModulesEquivalence (Spec Γ(X, U))).functor.mapIso
    (restrictTensorIso j M N).symm
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso e h

private theorem finite_affineSpecSections (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U)
      ((moduleSpecΓFunctor (R := Γ(X, U))).obj (M.restrict hU.fromSpec)) := by
  let j : Spec Γ(X, U) ⟶ X := hU.fromSpec
  have hImage : j ''ᵁ ⊤ = U :=
    hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  have hUFinite : Module.Finite Γ(X, U) Γ(M, U) :=
    moduleFinite_sections_of_isFiniteType M U hU
  have hImageFinite : Module.Finite Γ(X, j ''ᵁ ⊤) Γ(M, j ''ᵁ ⊤) :=
    Eq.mp (congrArg (fun W : X.Opens => Module.Finite Γ(X, W) Γ(M, W)) hImage.symm)
      hUFinite
  exact moduleFinite_moduleSpecΓ_restrict_of_finite_sections M j

/-- The native tensor of finite-type quasicoherent sheaves has finite
type, with generators supplied by their actual finite affine sections. -/
theorem isFiniteType_tensor (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType] [N.IsFiniteType] :
    (tensor M N).IsFiniteType := by
  have : (tensor M N).IsQuasicoherent := isQuasicoherent_tensor M N
  apply isFiniteType_of_affineSpecRestrictions (tensor M N)
  intro U hU
  let R : CommRingCat.{u} := Γ(X, U)
  let j : Spec R ⟶ X := hU.fromSpec
  let P : (Spec R).Modules := M.restrict j
  let Q : (Spec R).Modules := N.restrict j
  have : P.IsQuasicoherent := isQuasicoherent_restrictFunctor j M
  have : Q.IsQuasicoherent := isQuasicoherent_restrictFunctor j N
  have : ((tensor M N).restrict j).IsQuasicoherent :=
    isQuasicoherent_restrictFunctor j (tensor M N)
  let p : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj P
  let q : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj Q
  have : Module.Finite R p := finite_affineSpecSections M U hU
  have : Module.Finite R q := finite_affineSpecSections N U hU
  have : Module.Finite R (p ⊗[R] q) := inferInstance
  let e₁ : (p ⊗[R] q) ≃ₗ[R]
      (moduleSpecΓFunctor (R := R)).obj (tensor P Q) := specTensorSectionsEquiv P Q
  let e₂ := ((moduleSpecΓFunctor (R := R)).mapIso (restrictTensorIso j M N).symm).toLinearEquiv
  have : Module.Finite R
      ((moduleSpecΓFunctor (R := R)).obj ((tensor M N).restrict j)) :=
    Module.Finite.equiv (e₁.trans e₂)
  exact isFiniteType_of_finite_moduleSpecΓ ((tensor M N).restrict j)

end AlgebraicGeometry.Scheme.Modules
