/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeAffineSections
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeOfFiniteSections
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPushforward
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite type of the actual direct image under a finite morphism

On an affine target open, a finite morphism has an affine inverse image
and a finite map of the original section rings. Restricting scalars on
the actual finite module of sections therefore produces finite direct
image sections. Their actual affine local generators give native finite
type of the quasicoherent direct image.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]

/-- The original affine sections of a finite direct image form a finite
module over the original target section ring. -/
theorem moduleFinite_pushforward_sections_of_isFinite
    (U : Y.Opens) (hU : IsAffineOpen U) :
    Module.Finite Γ(Y, U) Γ((pushforward f).obj M, U) := by
  let R : CommRingCat.{u} := Γ(Y, U)
  let S : CommRingCat.{u} := Γ(X, f ⁻¹ᵁ U)
  let σ : R →+* S := (f.app U).hom
  let : Algebra R S := σ.toAlgebra
  let P : ModuleCat.{u} S := ModuleCat.of S Γ(M, f ⁻¹ᵁ U)
  let P₀ : ModuleCat.{u} R := (ModuleCat.restrictScalars σ).obj P
  have hS : Module.Finite R S := f.finite_app U hU
  have hP : Module.Finite S P :=
    moduleFinite_sections_of_isFiniteType M (f ⁻¹ᵁ U) (hU.preimage f)
  have hPS : Module.Finite S P₀ := inferInstanceAs (Module.Finite S P)
  have hTower : IsScalarTower R S P₀ := IsScalarTower.of_compHom R S P
  have hP₀ : Module.Finite R P₀ := Module.Finite.trans S P₀
  exact hP₀

/-- Finite morphisms carry finite-type quasicoherent native module
sheaves to finite-type native module sheaves. -/
theorem isFiniteType_pushforward_of_isFinite :
    ((pushforward f).obj M).IsFiniteType := by
  have hQC : ((pushforward f).obj M).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom f M
  exact isFiniteType_of_finite_affine_sections ((pushforward f).obj M)
    (moduleFinite_pushforward_sections_of_isFinite f M)

end AlgebraicGeometry.Scheme.Modules
