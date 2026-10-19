/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ModuleSheafCohomologyIso
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesImageModule
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesProjectiveSerre
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypePullback
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPullback
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
import Nyll.SchemeTheory.Modules.Tensor.QuasicoherentTensor
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerComparison
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The actual Rees image with coherent sheaf coefficients

Tensor the native Rees image with the original first-projection
pullback of a module sheaf. The proved pullback and tensor theorems give
quasicoherence and finite type of this constructed sheaf directly.
The original monoidal comparisons also identify twisting the coefficient
sheaf before this construction with twisting the resulting Rees sheaf.

For projective space over a Noetherian ring, the native Serre theorem
therefore gives one bound for every positive cohomological degree of this
actual coefficient sheaf on the original Rees cover.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS

open AlgebraicGeometry Scheme.Modules

variable {A : Type u} [CommRing A] (I : Ideal A)
  {P : Scheme.{u}} (q : P ⟶ Spec (.of A))

/-- The native Rees image tensored with the actual pullback of the
coefficient sheaf along the original first projection. -/
def imageTensorModule (M : P.Modules) : (P' I q).Modules :=
  tensor (imageModule I q) ((pullback (fst' I q)).obj M)

/-- The actual Rees coefficient sheaf is quasicoherent whenever its
original coefficient sheaf is quasicoherent. -/
theorem imageTensorModule_isQuasicoherent (M : P.Modules) [M.IsQuasicoherent] :
    (imageTensorModule I q M).IsQuasicoherent := by
  have : (imageModule I q).IsQuasicoherent := imageModule_isQuasicoherent I q
  have : ((pullback (fst' I q)).obj M).IsQuasicoherent :=
    isQuasicoherent_pullback (fst' I q) M
  exact isQuasicoherent_tensor (imageModule I q) ((pullback (fst' I q)).obj M)

/-- The actual Rees coefficient sheaf has finite type when the
original quasicoherent coefficient sheaf has finite type. -/
theorem imageTensorModule_isFiniteType (M : P.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] : (imageTensorModule I q M).IsFiniteType := by
  have : (imageModule I q).IsQuasicoherent := imageModule_isQuasicoherent I q
  have : (imageModule I q).IsFiniteType := imageModule_isFiniteType I q
  have : ((pullback (fst' I q)).obj M).IsQuasicoherent :=
    isQuasicoherent_pullback (fst' I q) M
  have : ((pullback (fst' I q)).obj M).IsFiniteType :=
    isFiniteType_pullback (fst' I q) M
  exact isFiniteType_tensor (imageModule I q) ((pullback (fst' I q)).obj M)

/-- Twisting the original coefficient sheaf is carried to twisting
the actual Rees coefficient sheaf by the original monoidal comparisons. -/
def imageTensorTwistIso (M L : P.Modules) (d : ℕ) :
    imageTensorModule I q (M ⊗ L.tensorPow d) ≅
      imageTensorModule I q M ⊗ ((pullback (fst' I q)).obj L).tensorPow d :=
  whiskerLeftIso (imageModule I q)
      (pullbackTensorObjIso (fst' I q) M (L.tensorPow d) ≪≫
        whiskerLeftIso ((pullback (fst' I q)).obj M)
          (pullbackTensorPowIso (fst' I q) L d)) ≪≫
    (α_ (imageModule I q) ((pullback (fst' I q)).obj M)
      (((pullback (fst' I q)).obj L).tensorPow d)).symm

end AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS

open AlgebraicGeometry AlgebraicGeometry.ProjSpace Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ)

local notation "X" => Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)

/-- One uniform twist bound kills every positive Čech degree of
the constructed Rees coefficient sheaf on the original ordered cover. -/
theorem exists_imageTensor_twisting_bound_subsingleton_HSucc (M : (X).Modules)
    [SheafOfModules.IsQuasicoherent (R := (X).ringCatSheaf) M]
    [SheafOfModules.IsFiniteType (R := (X).ringCatSheaf) M] :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ k : ℕ,
      Subsingleton ((toOModulePresheaf (π' I (π R n))
        (imageTensorModule I (π R n) M ⊗ ((pullback (fst' I (π R n))).obj
          (twistingSheaf R n)).tensorPow d)).HSucc
            (K' I (π R n) (stdCoverPullback (𝟙 X))) k) := by
  have : (imageTensorModule I (π R n) M).IsQuasicoherent :=
    imageTensorModule_isQuasicoherent I (π R n) M
  have : (imageTensorModule I (π R n) M).IsFiniteType :=
    imageTensorModule_isFiniteType I (π R n) M
  exact exists_rees_twisting_bound_subsingleton_HSucc R I n (imageTensorModule I (π R n) M)

/-- The same uniform bound applies with the twisting power on the
original coefficient sheaf, through the actual tensor/pullback comparison. -/
theorem exists_imageTensor_coefficient_twisting_bound_subsingleton_HSucc (M : (X).Modules)
    [SheafOfModules.IsQuasicoherent (R := (X).ringCatSheaf) M]
    [SheafOfModules.IsFiniteType (R := (X).ringCatSheaf) M] :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ k : ℕ,
      Subsingleton ((toOModulePresheaf (π' I (π R n))
        (imageTensorModule I (π R n) (M ⊗ (twistingSheaf R n).tensorPow d))).HSucc
          (K' I (π R n) (stdCoverPullback (𝟙 X))) k) := by
  obtain ⟨c, hc⟩ := exists_imageTensor_twisting_bound_subsingleton_HSucc R I n M
  refine ⟨c, ?_⟩
  intro d hd k
  have : Subsingleton ((toOModulePresheaf (π' I (π R n))
      (imageTensorModule I (π R n) M ⊗ ((pullback (fst' I (π R n))).obj
        (twistingSheaf R n)).tensorPow d)).HSucc
          (K' I (π R n) (stdCoverPullback (𝟙 X))) k) := hc d hd k
  exact subsingleton_HSucc_of_iso (π' I (π R n))
    (K' I (π R n) (stdCoverPullback (𝟙 X)))
    (imageTensorTwistIso I (π R n) M (twistingSheaf R n) d).symm k

end AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS
