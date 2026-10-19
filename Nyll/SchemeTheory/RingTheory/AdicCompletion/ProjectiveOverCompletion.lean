/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.AdicCompletionNoetherian
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ModuleSystemOverCompletion
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveModuleSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.QuotientRingComparison
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.Basic

/-!
# Projectivity over the original affine coefficient completion

The reduction of the constructed completed-sequence module agrees with
the original stage. Every coefficient of the completed quotient has an
original-ring representative, so this comparison is semilinear for the
actual equivalence of coefficient quotient rings.

If the original stages are finite projective over their original quotient
rings, the constructed module over the coefficient completion is finite
projective, hence flat. Neither completeness of the original coefficient
ring nor flatness of the constructed module is assumed.
-/

noncomputable section

namespace AdicModuleSystem

universe u v

private def semilinearEquivOfSurjectiveAlgebraMap
    {R S T P Q : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [AddCommGroup P] [AddCommGroup Q]
    [Module R P] [Module R Q] [Module S P] [Module T Q]
    [IsScalarTower R S P] [IsScalarTower R T Q]
    (eA : S ≃ₐ[R] T) (e : P ≃ₗ[R] Q)
    (hS : Function.Surjective (algebraMap R S)) :
    let eR := eA.toRingEquiv
    let _hσ : RingHomInvPair (eR : S →+* T) (eR.symm : T →+* S) :=
      RingHomInvPair.of_ringEquiv eR
    let _hσ' : RingHomInvPair (eR.symm : T →+* S) (eR : S →+* T) :=
      RingHomInvPair.of_ringEquiv_symm eR
    LinearEquiv (σ' := (eR.symm : T →+* S)) (eR : S →+* T) P Q := by
  intro eR _hσ _hσ'
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro a x
  obtain ⟨r, rfl⟩ := hS a
  change e (algebraMap R S r • x) = eA (algebraMap R S r) • e x
  rw [IsScalarTower.algebraMap_smul, e.map_smul, eA.commutes,
    IsScalarTower.algebraMap_smul]

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (M : ℕ → Type v) [∀ k : ℕ, AddCommGroup (M k)] [∀ k : ℕ, Module R (M k)]
  (t : ∀ k : ℕ, M (k + 1) →ₗ[R] M k) (I : Ideal R)
  [∀ k : ℕ, Module.Finite R (M k)]
  [∀ k : ℕ, Module (R ⧸ I ^ (k + 1)) (M k)]
  [∀ k : ℕ, IsScalarTower R (R ⧸ I ^ (k + 1)) (M k)]
  (hpow : ∀ k : ℕ, I ^ (k + 1) • (⊤ : Submodule R (M k)) = ⊥)
  (ht : ∀ k : ℕ, Function.Surjective (t k))
  (hker : ∀ k : ℕ, (t k).ker = I ^ (k + 1) • (⊤ : Submodule R (M (k + 1))))

/-- The actual reduction comparison respects the actual equivalence
between the completed and original coefficient quotient rings. -/
def completedQuotientSemilinearEquiv (n : ℕ) :
    let S := AdicCompletion I R
    let J : Ideal S := I.map (algebraMap R S)
    let eR : (S ⧸ J ^ (n + 1)) ≃+* (R ⧸ I ^ (n + 1)) :=
      (AdicCompletion.quotientPowAlgEquiv I (IsNoetherian.noetherian I) (n + 1)).toRingEquiv
    let _hσ : RingHomInvPair
        (eR : (S ⧸ J ^ (n + 1)) →+* (R ⧸ I ^ (n + 1)))
        (eR.symm : (R ⧸ I ^ (n + 1)) →+* (S ⧸ J ^ (n + 1))) :=
      RingHomInvPair.of_ringEquiv eR
    let _hσ' : RingHomInvPair
        (eR.symm : (R ⧸ I ^ (n + 1)) →+* (S ⧸ J ^ (n + 1)))
        (eR : (S ⧸ J ^ (n + 1)) →+* (R ⧸ I ^ (n + 1))) :=
      RingHomInvPair.of_ringEquiv_symm eR
    LinearEquiv
      (σ' := (eR.symm : (R ⧸ I ^ (n + 1)) →+* (S ⧸ J ^ (n + 1))))
      (eR : (S ⧸ J ^ (n + 1)) →+* (R ⧸ I ^ (n + 1)))
      ((sections (fun k => AdicCompletion I (M k)) (fun k => AdicCompletion.map I (t k))) ⧸
      ((I.map (algebraMap R (AdicCompletion I R))) ^ (n + 1) •
        (⊤ : Submodule (AdicCompletion I R)
          (sections (fun k => AdicCompletion I (M k))
            (fun k => AdicCompletion.map I (t k)))))) (M n) := by
  intro S J eR _hσ _hσ'
  let e := completedQuotientEquiv M t I hpow ht hker n
  let eA := AdicCompletion.quotientPowAlgEquiv I (IsNoetherian.noetherian I) (n + 1)
  exact semilinearEquivOfSurjectiveAlgebraMap eA e
    (AdicCompletion.algebraMap_quotientPow_surjective I
      (IsNoetherian.noetherian I) (n + 1))

include ht hker in
/-- Semilinear comparison still sends the original quotient class to
the original, uncompleted stage value. -/
theorem completedQuotientSemilinearEquiv_mk (n : ℕ)
    (x : sections (fun k => AdicCompletion I (M k)) (fun k => AdicCompletion.map I (t k))) :
    let S := AdicCompletion I R
    let J : Ideal S := I.map (algebraMap R S)
    let eR : (S ⧸ J ^ (n + 1)) ≃+* (R ⧸ I ^ (n + 1)) :=
      (AdicCompletion.quotientPowAlgEquiv I (IsNoetherian.noetherian I) (n + 1)).toRingEquiv
    let _hσ : RingHomInvPair
        (eR : (S ⧸ J ^ (n + 1)) →+* (R ⧸ I ^ (n + 1)))
        (eR.symm : (R ⧸ I ^ (n + 1)) →+* (S ⧸ J ^ (n + 1))) :=
      RingHomInvPair.of_ringEquiv eR
    let _hσ' : RingHomInvPair
        (eR.symm : (R ⧸ I ^ (n + 1)) →+* (S ⧸ J ^ (n + 1)))
        (eR : (S ⧸ J ^ (n + 1)) →+* (R ⧸ I ^ (n + 1))) :=
      RingHomInvPair.of_ringEquiv_symm eR
    (completedQuotientSemilinearEquiv M t I hpow ht hker n).toAddEquiv
        (Submodule.Quotient.mk x) =
      ((completedSectionsEquiv M t I hpow).symm x).val n := by
  intro S J eR _hσ _hσ'
  exact completedQuotientEquiv_mk M t I hpow ht hker n x

variable [∀ k : ℕ, Module.Projective (R ⧸ I ^ (k + 1)) (M k)]

include hpow ht hker in
/-- An original finite projective adic system constructs an actual
projective module over the completed coefficient ring. -/
theorem completed_sections_projective :
    Module.Projective (AdicCompletion I R)
      (sections (fun k => AdicCompletion I (M k)) (fun k => AdicCompletion.map I (t k))) := by
  let S := AdicCompletion I R
  let J : Ideal S := I.map (algebraMap R S)
  let P : ModuleCat.{v} S := ModuleCat.of S
    (sections (fun k => AdicCompletion I (M k)) (fun k => AdicCompletion.map I (t k)))
  have : IsNoetherianRing S := AdicCompletion.isNoetherianRing_of_isNoetherianRing I
  have : IsAdicComplete J S := AdicCompletion.isAdicComplete_self I
    (IsNoetherian.noetherian I)
  have : Module.Finite S P := completed_sections_finite M t I hpow ht hker
  apply projective_of_projective_reductions J P
  intro n
  let eR : (S ⧸ J ^ (n + 1)) ≃+* (R ⧸ I ^ (n + 1)) :=
    (AdicCompletion.quotientPowAlgEquiv I (IsNoetherian.noetherian I) (n + 1)).toRingEquiv
  have _hσ : RingHomInvPair
      (eR : (S ⧸ J ^ (n + 1)) →+* (R ⧸ I ^ (n + 1)))
      (eR.symm : (R ⧸ I ^ (n + 1)) →+* (S ⧸ J ^ (n + 1))) :=
    RingHomInvPair.of_ringEquiv eR
  have _hσ' : RingHomInvPair
      (eR.symm : (R ⧸ I ^ (n + 1)) →+* (S ⧸ J ^ (n + 1)))
      (eR : (S ⧸ J ^ (n + 1)) →+* (R ⧸ I ^ (n + 1))) :=
    RingHomInvPair.of_ringEquiv_symm eR
  let e := completedQuotientSemilinearEquiv M t I hpow ht hker n
  exact Module.Projective.of_equiv (R := R ⧸ I ^ (n + 1)) (S := S ⧸ J ^ (n + 1))
    (σ := (eR.symm : (R ⧸ I ^ (n + 1)) →+* (S ⧸ J ^ (n + 1))))
    (σ' := (eR : (S ⧸ J ^ (n + 1)) →+* (R ⧸ I ^ (n + 1)))) e.symm

include hpow ht hker in
/-- Flatness follows for the same constructed module and original
completed-ring scalar action. -/
theorem completed_sections_flat :
    Module.Flat (AdicCompletion I R)
      (sections (fun k => AdicCompletion I (M k)) (fun k => AdicCompletion.map I (t k))) := by
  have : Module.Projective (AdicCompletion I R)
      (sections (fun k => AdicCompletion I (M k)) (fun k => AdicCompletion.map I (t k))) :=
    completed_sections_projective M t I hpow ht hker
  infer_instance

end AdicModuleSystem
