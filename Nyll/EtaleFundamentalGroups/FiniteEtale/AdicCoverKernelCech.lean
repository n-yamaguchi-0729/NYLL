/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverKernelTensorSections
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTransitionKernels
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorPresheaf
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Čech comparison for actual transition kernels with coefficients

The previously constructed affine tensor/kernel comparison commutes with
the original restrictions. It therefore gives inverse affine presheaf
maps between the degree `n + 1` ideal tensor of the first-stage sheaf
with coefficients and the actual transition kernel with those coefficients.

Their induced maps on the original alternating Čech complexes and on
quotient cohomology are inverse. Every comparison in this file is
constructed from the original finite étale cover, its actual infinitesimal
extensions, and the given quasicoherent coefficient sheaf.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (N : X.Modules) [N.IsQuasicoherent]

/-- The actual affine tensor/kernel comparison with both sides carrying
the same original base-ring action. -/
def transitionKernelIdealTensorSectionsEquiv (U : X.affineOpens) (n : ℕ) :
    (ReesTensor.idealTensorPresheaf f I (tensor (moduleSheaf f I V 0) N) (n + 1)).obj U
      ≃ₗ[A]
        (toOModulePresheaf f (tensor (transitionKernelSheaf f I V n) N)).obj U := by
  let e := transitionKernelTensorWithSectionsEquiv f I V N U n
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := e.map_add
      map_smul' := fun a z => e.map_smul ((f.constToPresheaf.app (op U.1)).hom a) z }

/-- The constructed kernel comparison gives an actual morphism on
affine sections from the original ideal-tensor presheaf. -/
def transitionKernelIdealTensorAffHom (n : ℕ) :
    OModulePresheaf.AffHom
      (ReesTensor.idealTensorPresheaf f I (tensor (moduleSheaf f I V 0) N) (n + 1))
      (toOModulePresheaf f (tensor (transitionKernelSheaf f I V n) N)) where
  app U := (transitionKernelIdealTensorSectionsEquiv f I V N U n).toLinearMap
  app_smul U a z := (transitionKernelTensorWithSectionsEquiv f I V N U n).map_smul a z
  naturality {U W} h := by
    apply LinearMap.ext
    intro z
    exact (transitionKernelTensorWithSectionsEquiv_restriction f I V N W U h n z).symm

/-- The actual affine section inverses form the inverse morphism of
the original tensor/kernel comparison. -/
def transitionKernelIdealTensorAffInv (n : ℕ) :
    OModulePresheaf.AffHom
      (toOModulePresheaf f (tensor (transitionKernelSheaf f I V n) N))
      (ReesTensor.idealTensorPresheaf f I (tensor (moduleSheaf f I V 0) N) (n + 1)) where
  app U := (transitionKernelIdealTensorSectionsEquiv f I V N U n).symm.toLinearMap
  app_smul U a z := (transitionKernelTensorWithSectionsEquiv f I V N U n).symm.map_smul a z
  naturality {U W} h := by
    apply LinearMap.ext
    intro z
    let eU := transitionKernelIdealTensorSectionsEquiv f I V N U n
    let eW := transitionKernelIdealTensorSectionsEquiv f I V N W n
    let F := toOModulePresheaf f (tensor (transitionKernelSheaf f I V n) N)
    apply eU.injective
    have hn := (transitionKernelIdealTensorAffHom f I V N n).naturality_apply h (eW.symm z)
    have hr := congrArg (F.res h) (eW.apply_symm_apply z)
    exact (eU.apply_symm_apply (F.res h z)).trans (hn.trans hr).symm

variable [IsSeparated f] (K : X.OrderedAffineCover)

/-- The actual affine comparison and its inverse identify the
original Čech cochains, with the same cover and degree. -/
def transitionKernelIdealTensorCochainEquiv (n k : ℕ) :
    (ReesTensor.idealTensorPresheaf f I (tensor (moduleSheaf f I V 0) N) (n + 1)).cochain K k
      ≃ₗ[A]
        (toOModulePresheaf f (tensor (transitionKernelSheaf f I V n) N)).cochain K k :=
  { (transitionKernelIdealTensorAffHom f I V N n).cochainMap K k with
    invFun := (transitionKernelIdealTensorAffInv f I V N n).cochainMap K k
    left_inv x := by
      funext s
      let e := transitionKernelIdealTensorSectionsEquiv f I V N (K.affineInter f s) n
      exact e.symm_apply_apply (x s)
    right_inv y := by
      funext s
      let e := transitionKernelIdealTensorSectionsEquiv f I V N (K.affineInter f s) n
      exact e.apply_symm_apply (y s) }

/-- The comparison on cochains retains the actual affine tensor/kernel
map on every original cover intersection. -/
theorem transitionKernelIdealTensorCochainEquiv_apply (n k : ℕ)
    (z : (ReesTensor.idealTensorPresheaf f I
      (tensor (moduleSheaf f I V 0) N) (n + 1)).cochain K k) (s : K.Idx k) :
    transitionKernelIdealTensorCochainEquiv f I V N K n k z s =
      transitionKernelIdealTensorSectionsEquiv f I V N (K.affineInter f s) n (z s) := rfl

/-- The constructed comparison identifies actual quotient Čech
cohomology of the ideal tensor with that of the original transition kernel. -/
def transitionKernelIdealTensorHSuccEquiv (n k : ℕ) :
    (ReesTensor.idealTensorPresheaf f I (tensor (moduleSheaf f I V 0) N) (n + 1)).HSucc K k
      ≃ₗ[A]
        (toOModulePresheaf f (tensor (transitionKernelSheaf f I V n) N)).HSucc K k :=
  { (transitionKernelIdealTensorAffHom f I V N n).HSuccMap K k with
    invFun := (transitionKernelIdealTensorAffInv f I V N n).HSuccMap K k
    left_inv x := by
      refine Submodule.Quotient.induction_on _ x ?_
      intro z
      refine (congrArg ((transitionKernelIdealTensorAffInv f I V N n).HSuccMap K k)
        ((transitionKernelIdealTensorAffHom f I V N n).HSuccMap_mk K k z)).trans ?_
      refine ((transitionKernelIdealTensorAffInv f I V N n).HSuccMap_mk K k
        ((transitionKernelIdealTensorAffHom f I V N n).kerMap K (k + 1) z)).trans ?_
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      let e := transitionKernelIdealTensorCochainEquiv f I V N K n (k + 1)
      exact e.symm_apply_apply z.val
    right_inv y := by
      refine Submodule.Quotient.induction_on _ y ?_
      intro z
      refine (congrArg ((transitionKernelIdealTensorAffHom f I V N n).HSuccMap K k)
        ((transitionKernelIdealTensorAffInv f I V N n).HSuccMap_mk K k z)).trans ?_
      refine ((transitionKernelIdealTensorAffHom f I V N n).HSuccMap_mk K k
        ((transitionKernelIdealTensorAffInv f I V N n).kerMap K (k + 1) z)).trans ?_
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      let e := transitionKernelIdealTensorCochainEquiv f I V N K n (k + 1)
      exact e.apply_symm_apply z.val }

/-- The cohomology comparison is the induced map of the actual
affine comparison on each original cocycle class. -/
theorem transitionKernelIdealTensorHSuccEquiv_apply_mk (n k : ℕ)
    (z : LinearMap.ker ((ReesTensor.idealTensorPresheaf f I
      (tensor (moduleSheaf f I V 0) N) (n + 1)).d K (k + 1))) :
    transitionKernelIdealTensorHSuccEquiv f I V N K n k (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        ((transitionKernelIdealTensorAffHom f I V N n).kerMap K (k + 1) z) := rfl

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
