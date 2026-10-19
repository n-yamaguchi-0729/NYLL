/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.Functoriality.PullbackSections
import Nyll.SchemeTheory.Modules.Functoriality.QuasicoherentPullbackSections
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Nyll.SchemeTheory.Modules.Sections.NilpotentQuotientGeneration
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The actual quotient unit for a closed immersion

For a closed immersion, the pullback adjunction unit of a quasicoherent
module is surjective on every affine target open. The proof uses the
actual affine scalar-extension comparison and the actual surjective
map of structure-sheaf sections.

Every morphism into an actual direct image consequently factors
uniquely through this unit. The factor is the direct image of its
original adjoint. This supplies genuine free modules on closed
thickenings as sources of presentations, with their original quotient
maps; no descent or factorization is assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The original pullback unit for a closed immersion is surjective
on affine sections of every quasicoherent module. -/
theorem pullbackUnit_app_surjective_of_isClosedImmersion [IsClosedImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent] (U : Y.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (((pullbackPushforwardAdjunction f).unit.app M).app U) := by
  let V : X.Opens := f ⁻¹ᵁ U
  let R : CommRingCat.{u} := Γ(Y, U)
  let S : CommRingCat.{u} := Γ(X, V)
  let σ : R ⟶ S := f.appLE U V le_rfl
  let P : ModuleCat.{u} R := (moduleSectionsFunctor U).obj M
  let Q : ModuleCat.{u} S := (moduleSectionsFunctor V).obj ((pullback f).obj M)
  let _algebra : Algebra R S := σ.hom.toAlgebra
  let e : (ModuleCat.extendScalars σ.hom).obj P ≃ₗ[S] Q :=
    affinePullbackSectionsEquiv f U V hU (hU.preimage f) le_rfl M
  have hσ : Function.Surjective (algebraMap R S) := by
    change Function.Surjective (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom
    rw [Scheme.Hom.appLE_eq_app]
    exact f.app_surjective U hU
  have hmk : Function.Surjective (TensorProduct.mk R S P (1 : S)) :=
    TensorProduct.mk_surjective R P S hσ
  intro y
  obtain ⟨z, hz⟩ := e.surjective (show Q from y)
  obtain ⟨x, hx⟩ := hmk z
  refine ⟨x, ?_⟩
  have he : e ((1 : S) ⊗ₜ[R,σ.hom] x) =
      ((pullback f).obj M).presheaf.map (homOfLE (le_rfl : V ≤ V)).op
        (pullbackLocalSection f (show Γ(M, U) from x)) :=
    pullbackSectionsMap_one_tmul f U V le_rfl M x
  have hr : ((pullback f).obj M).presheaf.map (homOfLE (le_rfl : V ≤ V)).op
      (pullbackLocalSection f (show Γ(M, U) from x)) =
        pullbackLocalSection f (show Γ(M, U) from x) := by
    let N : X.Modules := (pullback f).obj M
    have hi : (homOfLE (le_rfl : V ≤ V)).op = 𝟙 (op V) := Subsingleton.elim _ _
    have hm : N.presheaf.map (homOfLE (le_rfl : V ≤ V)).op = 𝟙 (Γ(N, V)) :=
      (congrArg (fun i : op V ⟶ op V => N.presheaf.map i) hi).trans
        (N.presheaf.map_id (op V))
    exact congrArg (fun k : Γ(N, V) ⟶ Γ(N, V) => k (pullbackLocalSection f x)) hm
  exact (he.trans hr).symm.trans ((congrArg e hx).trans hz)

/-- The actual adjunction unit is an epimorphism for a closed
immersion and a quasicoherent source module. -/
theorem epi_pullbackUnit_of_isClosedImmersion [IsClosedImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent] :
    Epi ((pullbackPushforwardAdjunction f).unit.app M) :=
  Hom.epi_of_surjective_affine_app ((pullbackPushforwardAdjunction f).unit.app M)
    (pullbackUnit_app_surjective_of_isClosedImmersion f M)

variable {M : Y.Modules} {N : X.Modules} (α : M ⟶ (pushforward f).obj N)

/-- The direct image of the original adjoint, with the actual
pullback of the source as its domain. -/
def pushforwardAdjointFactor :
    (pushforward f).obj ((pullback f).obj M) ⟶ (pushforward f).obj N :=
  (pushforward f).map (((pullbackPushforwardAdjunction f).homEquiv M N).symm α)

/-- Composing the original quotient unit with the constructed
factor recovers precisely the original morphism. -/
theorem unit_pushforwardAdjointFactor :
    (pullbackPushforwardAdjunction f).unit.app M ≫ pushforwardAdjointFactor f α = α := by
  let adj : pullback f ⊣ pushforward f := pullbackPushforwardAdjunction f
  let a : (pullback f).obj M ⟶ N := (adj.homEquiv M N).symm α
  exact (adj.homEquiv_unit (f := a)).symm.trans ((adj.homEquiv M N).apply_symm_apply α)

/-- A morphism into an actual direct image factors uniquely through
the closed-immersion quotient of its quasicoherent source. -/
theorem existsUnique_factor_through_closedImmersion_unit [IsClosedImmersion f]
    [M.IsQuasicoherent] :
    ∃! β : (pushforward f).obj ((pullback f).obj M) ⟶ (pushforward f).obj N,
      (pullbackPushforwardAdjunction f).unit.app M ≫ β = α := by
  have : Epi ((pullbackPushforwardAdjunction f).unit.app M) :=
    epi_pullbackUnit_of_isClosedImmersion f M
  refine ⟨pushforwardAdjointFactor f α, unit_pushforwardAdjointFactor f α, ?_⟩
  intro β hβ
  exact (cancel_epi ((pullbackPushforwardAdjunction f).unit.app M)).mp
    (hβ.trans (unit_pushforwardAdjointFactor f α).symm)

end AlgebraicGeometry.Scheme.Modules
