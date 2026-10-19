/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverProjectiveLevels
import Nyll.SchemeTheory.Modules.Functoriality.BaseChangeHom
import Nyll.SchemeTheory.Modules.LocallyFreeOfRank
import Nyll.SchemeTheory.Modules.Tensor.FiniteFreePullback
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.FreeTwistPolynomialMatrix
import Nyll.SchemeTheory.ProjectiveSpace.PolynomialHomPullback
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafBaseChange
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.HomCongr

/-!
# Native free twists on the projective adic levels

Pullback along the constructed level isomorphism transports the original
free source and the original finite free twist to their counterparts over
the coefficient quotient. The induced Hom equivalence uses the actual
native pullback map. The resulting polynomial matrix reconstructs that
same pulled-back sheaf morphism through the constructed source and target
comparisons.

No finite presentation or compatibility of unknown matrices is an input.
This comparison applies directly to morphisms already constructed on the
original levels of the cover tower.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules ProjSpace
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

private def pullbackHomEquivOfSchemeIso {X Y : Scheme.{u}} (e : Y ≅ X)
    (M N : X.Modules) :
    (M ⟶ N) ≃ ((Scheme.Modules.pullback e.hom).obj M ⟶
      (Scheme.Modules.pullback e.hom).obj N) := by
  have : (Scheme.Modules.pushforward e.hom).IsEquivalence :=
    (pushforwardIsoEquivalence e).isEquivalence_functor
  exact (pullbackPushforwardAdjunction e.hom).fullyFaithfulLOfIsIsoUnit.homEquiv

/-- The native morphisms on the original projective adic level, with
the twisting power pulled back from the original projective space. -/
abbrev ProjectiveLevelFreeTwistHom (R : Type u) [CommRing R] (I : Ideal R)
    (n k : ℕ) (J K : Type u) (d : ℕ) : Type u :=
  (show (level (ProjSpace.π R n) I k).Modules from SheafOfModules.free J) ⟶
    Scheme.Modules.tensor
      (show (level (ProjSpace.π R n) I k).Modules from SheafOfModules.free K)
      ((Scheme.Modules.pullback
        (Limits.pullback.fst (ProjSpace.π R n) (baseInclusion I k))).obj
          ((twistingSheaf R n).tensorPow d))

variable (R : Type u) [CommRing R] (I : Ideal R) (n k : ℕ)

local notation "Q" => R ⧸ I ^ (k + 1)
local notation "Z" => level (ProjSpace.π R n) I k
local notation "XQ" => Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Q)
local notation "i" => Limits.pullback.fst (ProjSpace.π R n) (baseInclusion I k)

/-- The actual original-level twisting power becomes the twisting
power over the literal coefficient quotient. -/
def projectiveLevelTwistingPowerIso (d : ℕ) :
    (Scheme.Modules.pullback (projectiveLevelIso R I n k).hom).obj
        ((Scheme.Modules.pullback i).obj ((twistingSheaf R n).tensorPow d)) ≅
      (twistingSheaf Q n).tensorPow d :=
  (pullbackComp (projectiveLevelIso R I n k).hom i).app
      ((twistingSheaf R n).tensorPow d) ≪≫
    (pullbackCongr (projectiveLevelIso_hom_fst R I n k)).app
      ((twistingSheaf R n).tensorPow d) ≪≫
    twistingPowerBaseChangeIso R Q n d

/-- Transport of the original finite free twisted target, using its
actual finite biproduct and the constructed twisting comparison. -/
def projectiveLevelFreeTwistIso (K : Type u) [Finite K] (d : ℕ) :
    (Scheme.Modules.pullback (projectiveLevelIso R I n k).hom).obj
        (Scheme.Modules.tensor (show (Z).Modules from SheafOfModules.free K)
          ((Scheme.Modules.pullback i).obj ((twistingSheaf R n).tensorPow d))) ≅
      Scheme.Modules.tensor (show (XQ).Modules from SheafOfModules.free K)
        ((twistingSheaf Q n).tensorPow d) :=
  finiteFreeTensorPullbackIso (projectiveLevelIso R I n k).hom K
    (projectiveLevelTwistingPowerIso R I n k d)

/-- The actual pullback along the level isomorphism is a bijection
from original-level morphisms to native coefficient-quotient morphisms. -/
def projectiveLevelFreeTwistHomEquiv (J K : Type u) [Finite K] (d : ℕ) :
    ProjectiveLevelFreeTwistHom R I n k J K d ≃ FreeTwistHom Q n J K d :=
  (pullbackHomEquivOfSchemeIso (projectiveLevelIso R I n k)
      (show (Z).Modules from SheafOfModules.free J)
      (Scheme.Modules.tensor (show (Z).Modules from SheafOfModules.free K)
        ((Scheme.Modules.pullback i).obj ((twistingSheaf R n).tensorPow d)))).trans
    (Iso.homCongr (pullbackFreeIso (projectiveLevelIso R I n k).hom J)
      (projectiveLevelFreeTwistIso R I n k K d))

/-- The forward map is the original native pullback, conjugated by
the constructed source and target comparisons. -/
theorem projectiveLevelFreeTwistHomEquiv_apply (J K : Type u) [Finite K] (d : ℕ)
    (φ : ProjectiveLevelFreeTwistHom R I n k J K d) :
    projectiveLevelFreeTwistHomEquiv R I n k J K d φ =
      (pullbackFreeIso (projectiveLevelIso R I n k).hom J).inv ≫
        (Scheme.Modules.pullback (projectiveLevelIso R I n k).hom).map φ ≫
          (projectiveLevelFreeTwistIso R I n k K d).hom := rfl

/-- The coefficient-quotient polynomial matrix reconstructs the same
original native morphism after its actual level pullback. -/
theorem projectiveLevelFreeTwistHom_polynomialMatrix (J K : Type u) [Finite K] (d : ℕ)
    (φ : ProjectiveLevelFreeTwistHom R I n k J K d) :
    (Scheme.Modules.pullback (projectiveLevelIso R I n k).hom).map φ ≫
        (projectiveLevelFreeTwistIso R I n k K d).hom =
      (pullbackFreeIso (projectiveLevelIso R I n k).hom J).hom ≫
        polynomialMatrixHom Q n J K d
          (freeTwistPolynomialMatrixEquiv Q n J K d
            (projectiveLevelFreeTwistHomEquiv R I n k J K d φ)) := by
  let p : (Scheme.Modules.pullback (projectiveLevelIso R I n k).hom).obj
      (show (Z).Modules from SheafOfModules.free J) ≅
    (show (XQ).Modules from SheafOfModules.free J) :=
    pullbackFreeIso (projectiveLevelIso R I n k).hom J
  let v : FreeTwistHom Q n J K d :=
    projectiveLevelFreeTwistHomEquiv R I n k J K d φ
  have hcancel : p.hom ≫ v =
      (Scheme.Modules.pullback (projectiveLevelIso R I n k).hom).map φ ≫
        (projectiveLevelFreeTwistIso R I n k K d).hom :=
    p.hom_inv_id_assoc
      ((Scheme.Modules.pullback (projectiveLevelIso R I n k).hom).map φ ≫
        (projectiveLevelFreeTwistIso R I n k K d).hom)
  have hmatrix := polynomialMatrixHom_of_hom Q n J K d v
  exact hcancel.symm.trans
    (congrArg (fun w : FreeTwistHom Q n J K d => p.hom ≫ w) hmatrix.symm)

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
