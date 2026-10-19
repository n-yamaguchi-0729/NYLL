/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.ConstantPullbackFunctoriality
import Nyll.EtaleCohomology.Frobenius.ConstantFieldAction
import Nyll.EtaleCohomology.Frobenius.ModuleArithmeticComparison

/-!
# The coefficient-linear constant-field action and Frobenius powers

The native module pullback intertwines the proved additive constant-field
action through the actual constant-coefficient comparison. Its identity and
composition laws therefore hold with the original coefficient module structure.
The existing geometric Frobenius endomorphism and all its natural powers are
the corresponding powers of inverse arithmetic Frobenius in this action.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable (R : Type u) [CommRing R]
  (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of k))]

local notation "XΩ" => pullback (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

/-- The actual coefficient-linear constant-field pullback agrees with the
actual additive action under the native constant-coefficient comparison. -/
theorem constantFieldCohomologyPullback_forget
    (M : ModuleCat.{u} R) (n : ℕ) (σ : Ω ≃ₐ[k] Ω)
    (x : etaleCohomology XΩ R
      ((constantSheaf (XΩ).smallEtaleTopology (ModuleCat.{u} R)).obj M) n) :
    etaleConstantCohomologyForgetEquiv R (X := XΩ) M n
        (etaleConstantCohomologyPullbackMap (Scheme.constantFieldTwist k Ω X σ) R M n x) =
      constantFieldAbelianCohomologyAction k Ω X
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M) n σ
        (etaleConstantCohomologyForgetEquiv R (X := XΩ) M n x) :=
  etaleConstantCohomologyPullbackMap_forget R (Scheme.constantFieldTwist k Ω X σ) M n x

/-- The actual action of constant-field automorphisms by native coefficient-linear
pullback on constant étale cohomology in every degree. -/
def constantFieldCohomologyAction (M : ModuleCat.{u} R) (n : ℕ) :
    (Ω ≃ₐ[k] Ω) →* Module.End R
      (etaleCohomology XΩ R
        ((constantSheaf (XΩ).smallEtaleTopology (ModuleCat.{u} R)).obj M) n) where
  toFun σ := etaleConstantCohomologyPullbackMap (Scheme.constantFieldTwist k Ω X σ) R M n
  map_one' := by
    apply LinearMap.ext
    intro x
    let d := etaleConstantCohomologyForgetEquiv R (X := XΩ) M n
    let a := constantFieldAbelianCohomologyAction k Ω X
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M) n
    apply d.injective
    change d (etaleConstantCohomologyPullbackMap
      (Scheme.constantFieldTwist k Ω X 1) R M n x) = d x
    exact (constantFieldCohomologyPullback_forget R k Ω X M n 1 x).trans
      (congrArg (fun z : AddMonoid.End _ => z (d x)) a.map_one)
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    let d := etaleConstantCohomologyForgetEquiv R (X := XΩ) M n
    let a := constantFieldAbelianCohomologyAction k Ω X
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M) n
    apply d.injective
    change d (etaleConstantCohomologyPullbackMap
        (Scheme.constantFieldTwist k Ω X (σ * τ)) R M n x) =
      d (etaleConstantCohomologyPullbackMap (Scheme.constantFieldTwist k Ω X σ) R M n
        (etaleConstantCohomologyPullbackMap (Scheme.constantFieldTwist k Ω X τ) R M n x))
    calc
      _ = a (σ * τ) (d x) :=
        constantFieldCohomologyPullback_forget R k Ω X M n (σ * τ) x
      _ = a σ (a τ (d x)) :=
        congrArg (fun z : AddMonoid.End _ => z (d x)) (a.map_mul σ τ)
      _ = a σ (d (etaleConstantCohomologyPullbackMap
          (Scheme.constantFieldTwist k Ω X τ) R M n x)) :=
        congrArg (a σ) (constantFieldCohomologyPullback_forget R k Ω X M n τ x).symm
      _ = _ := (constantFieldCohomologyPullback_forget R k Ω X M n σ
        (etaleConstantCohomologyPullbackMap
          (Scheme.constantFieldTwist k Ω X τ) R M n x)).symm

/-- Each constant-field automorphism gives a linear automorphism; its inverse
is pullback by the inverse constant-field automorphism. -/
def constantFieldCohomologyEquiv (M : ModuleCat.{u} R) (n : ℕ) (σ : Ω ≃ₐ[k] Ω) :
    etaleCohomology XΩ R
        ((constantSheaf (XΩ).smallEtaleTopology (ModuleCat.{u} R)).obj M) n ≃ₗ[R]
      etaleCohomology XΩ R
        ((constantSheaf (XΩ).smallEtaleTopology (ModuleCat.{u} R)).obj M) n where
  toLinearMap := constantFieldCohomologyAction R k Ω X M n σ
  invFun := constantFieldCohomologyAction R k Ω X M n σ⁻¹
  left_inv x := by
    let a := constantFieldCohomologyAction R k Ω X M n
    have h : a σ⁻¹ * a σ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    exact congrArg (fun z : Module.End R _ => z x) h
  right_inv x := by
    let a := constantFieldCohomologyAction R k Ω X M n
    have h : a σ * a σ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun z : Module.End R _ => z x) h

variable [Fintype k] [Algebra.IsAlgebraic k Ω]

/-- Geometric Frobenius on the original coefficient module is inverse
arithmetic Frobenius in the proved linear constant-field action. -/
theorem finiteFieldFrobeniusCohomology_eq_constantFieldAction
    (M : ModuleCat.{u} R) (n : ℕ) :
    finiteFieldFrobeniusCohomology R k Ω X M n =
      constantFieldCohomologyAction R k Ω X M n
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm :=
  finiteFieldFrobeniusCohomology_eq_inverseArithmetic R k Ω X M n

/-- Powers of the existing geometric Frobenius cohomology map are the
actual coefficient-linear pullbacks along the scheme Frobenius iterates. -/
theorem finiteFieldFrobeniusCohomology_pow_eq_pullback
    (M : ModuleCat.{u} R) (n m : ℕ) :
    (finiteFieldFrobeniusCohomology R k Ω X M n) ^ m =
      etaleConstantCohomologyPullbackMap
        ((CategoryTheory.End.of (Scheme.constantBaseChangeFrobenius k Ω X)) ^ m).asHom R M n :=
  etaleConstantCohomologyPullbackMap_pow R (Scheme.constantBaseChangeFrobenius k Ω X) M n m

/-- Every natural power of the actual geometric Frobenius endomorphism is
the corresponding inverse arithmetic power in the actual linear action. -/
theorem finiteFieldFrobeniusCohomology_pow_eq_constantFieldAction
    (M : ModuleCat.{u} R) (n m : ℕ) :
    (finiteFieldFrobeniusCohomology R k Ω X M n) ^ m =
      constantFieldCohomologyAction R k Ω X M n
        ((FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm ^ m) := by
  rw [finiteFieldFrobeniusCohomology_eq_constantFieldAction, map_pow]

end EtaleCohomology
