/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypePullback
public import Nyll.SchemeTheory.Modules.Functoriality.ClosedImmersionCounit
public import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPullback
public import Nyll.SchemeTheory.ProjectiveSpace.AdicFreeTwistCokernel
public import Nyll.SchemeTheory.ProjectiveSpace.ClosedImmersionBaseChange
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Returning reconstructed ambient cokernels to a closed projective family

Pulling the actual reconstructed cokernel back to the closed family gives
a quasicoherent finite-type module there. At every original adic level,
the constructed comparison identifies its pullback with the cokernel of
the original presenting morphism pulled back to that same closed level.
No assertion that the ambient cokernel is supported on the closed family
is needed for this construction.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (n : ℕ) {Y : Scheme.{u}}
  (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))

/-- The actual coefficient pullback and the actual closed-family
pullback agree through the constructed base-change embedding. -/
def closedImmersionModulePullbackBaseChangeIso
    (M : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules) :
    (Scheme.Modules.pullback
      (Limits.pullback.fst (j ≫ π R n)
        (Spec.map (CommRingCat.ofHom (algebraMap R A))))).obj
      ((Scheme.Modules.pullback j).obj M) ≅
    (Scheme.Modules.pullback (closedImmersionBaseChangeMap R A n j)).obj
      ((Scheme.Modules.pullback (map R A n)).obj M) :=
  (pullbackComp
      (Limits.pullback.fst (j ≫ π R n)
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))) j).app M ≪≫
    (pullbackCongr (closedImmersionBaseChangeMap_comp_map R A n j).symm).app M ≪≫
      ((pullbackComp (closedImmersionBaseChangeMap R A n j) (map R A n)).app M).symm

/-- Pulling back a genuine ambient comparison with a closed direct image
recovers the original module through the original closed-immersion counit. -/
def closedImmersionModuleFromAmbientIso [IsClosedImmersion j]
    (M : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    (C : (Limits.pullback (j ≫ π R n)
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))).Modules)
    [C.IsQuasicoherent]
    (e : (Scheme.Modules.pullback (map R A n)).obj M ≅
      (pushforward (closedImmersionBaseChangeMap R A n j)).obj C) :
    (Scheme.Modules.pullback
      (Limits.pullback.fst (j ≫ π R n)
        (Spec.map (CommRingCat.ofHom (algebraMap R A))))).obj
      ((Scheme.Modules.pullback j).obj M) ≅ C := by
  have : IsIso
      ((pullbackPushforwardAdjunction (closedImmersionBaseChangeMap R A n j)).counit.app C) :=
    isIso_pullbackCounit_of_isClosedImmersion (closedImmersionBaseChangeMap R A n j) C
  exact closedImmersionModulePullbackBaseChangeIso R A n j M ≪≫
    (Scheme.Modules.pullback (closedImmersionBaseChangeMap R A n j)).mapIso e ≪≫
      asIso ((pullbackPushforwardAdjunction
        (closedImmersionBaseChangeMap R A n j)).counit.app C)

omit A [CommRing A] [Algebra R A]

variable (I : Ideal R) [IsAdicComplete I R]
  (J K : Type u) [Finite K] (d : ℕ)
  (φ : adicFreeTwistHomSections R I n J K d)

/-- The actual reconstructed ambient cokernel, pulled back to the
specified closed family. -/
def closedImmersionAdicFreeTwistCokernel : Y.Modules :=
  (Scheme.Modules.pullback j).obj (adicFreeTwistCokernel R n J K d I φ)

/-- The constructed module on the closed family is quasicoherent. -/
theorem closedImmersionAdicFreeTwistCokernel_isQuasicoherent :
    (closedImmersionAdicFreeTwistCokernel R n j I J K d φ).IsQuasicoherent := by
  have : (adicFreeTwistCokernel R n J K d I φ).IsQuasicoherent :=
    adicFreeTwistCokernel_isQuasicoherent R n J K d I φ
  exact isQuasicoherent_pullback j _

/-- Finite type of the actual reconstructed module survives pullback
to the closed family. -/
theorem closedImmersionAdicFreeTwistCokernel_isFiniteType :
    (closedImmersionAdicFreeTwistCokernel R n j I J K d φ).IsFiniteType := by
  have : (adicFreeTwistCokernel R n J K d I φ).IsQuasicoherent :=
    adicFreeTwistCokernel_isQuasicoherent R n J K d I φ
  have : (adicFreeTwistCokernel R n J K d I φ).IsFiniteType :=
    adicFreeTwistCokernel_isFiniteType R n J K d I φ
  exact isFiniteType_pullback j _

/-- Every actual adic reduction is the original native cokernel on
the closed level, with no separate support or algebraization assumption. -/
def closedImmersionAdicFreeTwistCokernelReductionIso (k : ℕ) :
    (Scheme.Modules.pullback
      (Limits.pullback.fst (j ≫ π R n)
        (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (k + 1))))))).obj
      (closedImmersionAdicFreeTwistCokernel R n j I J K d φ) ≅
    cokernel ((Scheme.Modules.pullback
      (closedImmersionBaseChangeMap R (R ⧸ I ^ (k + 1)) n j)).map (φ.val k)) :=
  closedImmersionModulePullbackBaseChangeIso R (R ⧸ I ^ (k + 1)) n j
      (adicFreeTwistCokernel R n J K d I φ) ≪≫
    (Scheme.Modules.pullback
      (closedImmersionBaseChangeMap R (R ⧸ I ^ (k + 1)) n j)).mapIso
      (adicFreeTwistCokernelReductionIso R n J K d I φ k) ≪≫
    PreservesCokernel.iso
      (Scheme.Modules.pullback (closedImmersionBaseChangeMap R (R ⧸ I ^ (k + 1)) n j))
      (φ.val k)

end AlgebraicGeometry.ProjSpace
