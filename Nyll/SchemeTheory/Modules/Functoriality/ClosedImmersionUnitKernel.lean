/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.Functoriality.PullbackSections
import Nyll.SchemeTheory.Modules.Functoriality.QuasicoherentPullbackSections
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual affine kernel of a closed-immersion pullback unit

The original affine scalar-extension comparison carries tensoring with
one to the original adjunction unit. The first isomorphism theorem for
the actual coefficient map and right exactness of tensor products then
identify its kernel with the defining ideal times the original section
module. No quotient-module comparison is assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

private theorem one_tmul_eq_zero_iff_of_surjective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hσ : Function.Surjective (algebraMap R S))
    (P : Type u) [AddCommGroup P] [Module R P] (x : P) :
    (1 : S) ⊗ₜ[R] x = 0 ↔
      x ∈ (RingHom.ker (algebraMap R S)) • (⊤ : Submodule R P) := by
  let I : Ideal R := RingHom.ker (algebraMap R S)
  let e : (R ⧸ I) ≃ₐ[R] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hσ
  let E : (R ⧸ I) ⊗[R] P ≃ₗ[R] S ⊗[R] P :=
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R P)
  have he : E ((1 : R ⧸ I) ⊗ₜ[R] x) = (1 : S) ⊗ₜ[R] x := by
    exact (TensorProduct.congr_tmul e.toLinearEquiv (LinearEquiv.refl R P) 1 x).trans
      (congrArg (fun s : S => s ⊗ₜ[R] x) e.map_one)
  have hE : (1 : S) ⊗ₜ[R] x = 0 ↔ (1 : R ⧸ I) ⊗ₜ[R] x = 0 := by
    constructor
    · intro hx
      apply E.injective
      exact he.trans (hx.trans E.map_zero.symm)
    · intro hx
      exact he.symm.trans ((congrArg E hx).trans E.map_zero)
  have hker : (TensorProduct.mk R (R ⧸ I) P 1).ker = I • (⊤ : Submodule R P) :=
    LinearMap.ker_tensorProductMk P
  exact hE.trans (show (1 : R ⧸ I) ⊗ₜ[R] x = 0 ↔ x ∈ I • (⊤ : Submodule R P) from
    (LinearMap.mem_ker).symm.trans (Iff.of_eq (congrArg (fun K : Submodule R P => x ∈ K)
      hker)))

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- On an original affine open, the kernel of the actual adjunction
unit is exactly the defining ideal times the original section module. -/
theorem pullbackUnit_app_eq_zero_iff_of_isClosedImmersion [IsClosedImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent] (U : Y.Opens) (hU : IsAffineOpen U)
    (x : Γ(M, U)) :
    ((pullbackPushforwardAdjunction f).unit.app M).app U x = 0 ↔
      x ∈ (RingHom.ker (f.app U).hom) • (⊤ : Submodule Γ(Y, U) Γ(M, U)) := by
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
  have he₁ : e ((1 : S) ⊗ₜ[R,σ.hom] (show P from x)) =
      ((pullback f).obj M).presheaf.map (homOfLE (le_rfl : V ≤ V)).op
        (pullbackLocalSection f x) :=
    pullbackSectionsMap_one_tmul f U V le_rfl M x
  have he₂ : ((pullback f).obj M).presheaf.map (homOfLE (le_rfl : V ≤ V)).op
      (pullbackLocalSection f x) = pullbackLocalSection f x := by
    let N : X.Modules := (pullback f).obj M
    have hi : (homOfLE (le_rfl : V ≤ V)).op = 𝟙 (op V) := Subsingleton.elim _ _
    have hm : N.presheaf.map (homOfLE (le_rfl : V ≤ V)).op = 𝟙 (Γ(N, V)) :=
      (congrArg (fun k : op V ⟶ op V => N.presheaf.map k) hi).trans
        (N.presheaf.map_id (op V))
    exact congrArg (fun k : Γ(N, V) ⟶ Γ(N, V) => k (pullbackLocalSection f x)) hm
  have he : e ((1 : S) ⊗ₜ[R,σ.hom] (show P from x)) =
      pullbackLocalSection f x := he₁.trans he₂
  have hunit : ((pullbackPushforwardAdjunction f).unit.app M).app U x = 0 ↔
      (1 : S) ⊗ₜ[R,σ.hom] (show P from x) = 0 := by
    constructor
    · intro hx
      apply e.injective
      exact he.trans (hx.trans e.map_zero.symm)
    · intro hx
      exact he.symm.trans ((congrArg e hx).trans e.map_zero)
  have hσeq : algebraMap R S = (f.app U).hom := by
    change (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom = (f.app U).hom
    exact congrArg CommRingCat.Hom.hom (f.appLE_eq_app (U := U))
  have hkernel : RingHom.ker (algebraMap R S) = RingHom.ker (f.app U).hom :=
    congrArg RingHom.ker hσeq
  have hx := one_tmul_eq_zero_iff_of_surjective hσ P x
  exact hunit.trans (hx.trans (Iff.of_eq
    (congrArg (fun J : Ideal R => x ∈ J • (⊤ : Submodule R P)) hkernel)))

end AlgebraicGeometry.Scheme.Modules
