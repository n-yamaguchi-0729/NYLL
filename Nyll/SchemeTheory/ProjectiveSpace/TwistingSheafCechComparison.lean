/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.TwistingFractionSections
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.UnitFractionEvaluation
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.SchemeTheory.Cohomology.Cech.ModulePresheafCechFiniteUnitClosedImmersionProj
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.LinearAlgebra.Pi

/-!
# The actual twisting-sheaf Čech complex and homogeneous fractions

The comparison on coordinate intersections gives a linear equivalence
in every cochain degree of the original native sheaf. The equivalence
commutes with the alternating restriction differential, including its
original integer signs. Both the section maps and the structural base
action are the ones already supplied by the actual twisting sheaf.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjSpace

open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
open ProjSpaceCech Scheme.Modules

attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra

private def restrictionAlongEquality
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
    (F : OModulePresheaf f) {U V : X.Opens} (h : U = V) :
    F.obj U ≃ₗ[R] F.obj V where
  toFun := F.res h.ge
  invFun := F.res h.le
  left_inv x := (F.res_res h.le h.ge x).trans (F.res_refl_apply U x)
  right_inv x := (F.res_res h.ge h.le x).trans (F.res_refl_apply V x)
  map_add' x y := map_add (F.res h.ge) x y
  map_smul' r x := map_smul (F.res h.ge) r x

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The actual twisting sheaf with its original structural base action,
as an input to the existing Čech complex. -/
abbrev twistingSectionPresheaf (d : ℕ) : OModulePresheaf ((𝟙 (Proj 𝒜)) ≫ π R n) :=
  toOModulePresheaf ((𝟙 (Proj 𝒜)) ≫ π R n) ((twistingSheaf R n).tensorPow d)

/-- The coordinate section equivalences, with the original cover-index
and intersection identifications, give an actual cochain equivalence. -/
def twistingCochainEquiv (d q : ℕ) :
    GradedModule.cochain (GradedModule.FD R n d) q ≃ₗ[R]
      (twistingSectionPresheaf R n d).cochain (stdCoverPullback (𝟙 (Proj 𝒜))) q :=
  (LinearEquiv.piCongrLeft' R
    (fun s : Idx n q => GradedModule.sec (GradedModule.FD R n d) (Idx.img n s))
    (ClosedImmCech.idxEquiv (𝟙 (Proj 𝒜)) q).symm).trans
    (LinearEquiv.piCongrRight (fun s =>
      (twistingFractionSectionEquiv R n d
        (Idx.img n (ClosedImmCech.idxEquiv (𝟙 (Proj 𝒜)) q s))
        (ClosedImmCech.altImg_nonempty _)).trans
        (restrictionAlongEquality (twistingSectionPresheaf R n d)
          (ClosedImmCech.altOpen_eq (𝟙 (Proj 𝒜)) q s).symm)))

theorem twistingCochainEquiv_apply (d q : ℕ)
    (c : GradedModule.cochain (GradedModule.FD R n d) q)
    (s : (stdCoverPullback (𝟙 (Proj 𝒜))).Idx q) :
    twistingCochainEquiv R n d q c s =
      (twistingSectionPresheaf R n d).res (ClosedImmCech.altOpen_eq (𝟙 (Proj 𝒜)) q s).le
        (twistingFractionSectionEquiv R n d
          (Idx.img n (ClosedImmCech.idxEquiv (𝟙 (Proj 𝒜)) q s))
          (ClosedImmCech.altImg_nonempty _)
          (c (ClosedImmCech.idxEquiv (𝟙 (Proj 𝒜)) q s))) := rfl

private theorem twistingCochainEquiv_face (d q : ℕ)
    (s : (stdCoverPullback (𝟙 (Proj 𝒜))).Idx (q + 1)) (j : Fin (q + 2))
    (z : GradedModule.sec (GradedModule.FD R n d)
      (Idx.img n (Idx.face n (ClosedImmCech.idxEquiv (𝟙 (Proj 𝒜)) (q + 1) s) j))) :
    (twistingSectionPresheaf R n d).res
        (ClosedImmCech.altOpen_eq (𝟙 (Proj 𝒜)) (q + 1) s).le
        (twistingFractionSectionEquiv R n d
          (Idx.img n (ClosedImmCech.idxEquiv (𝟙 (Proj 𝒜)) (q + 1) s))
          (ClosedImmCech.altImg_nonempty _)
          (GradedModule.secIncl _ (Idx.img_face_subset n _ j) z)) =
      (twistingSectionPresheaf R n d).res
        ((stdCoverPullback (𝟙 (Proj 𝒜))).inter_le_inter_face s j)
        ((twistingSectionPresheaf R n d).res
          (ClosedImmCech.altOpen_eq (𝟙 (Proj 𝒜)) q
            ((stdCoverPullback (𝟙 (Proj 𝒜))).face s j)).le
          (twistingFractionSectionEquiv R n d
            (Idx.img n (Idx.face n (ClosedImmCech.idxEquiv (𝟙 (Proj 𝒜)) (q + 1) s) j))
            (ClosedImmCech.altImg_nonempty _) z)) := by
  let F := twistingSectionPresheaf R n d
  let a : Idx n (q + 1) := ClosedImmCech.idxEquiv (𝟙 (Proj 𝒜)) (q + 1) s
  let v := twistingFractionSectionEquiv R n d (Idx.img n (Idx.face n a j))
    (ClosedImmCech.altImg_nonempty _) z
  have hloc : F.res (coordinateIntersection_mono R n (Idx.img_face_subset n a j)) v =
      twistingFractionSectionEquiv R n d (Idx.img n a)
        (ClosedImmCech.altImg_nonempty _)
        (GradedModule.secIncl _ (Idx.img_face_subset n a j) z) :=
    twistingFractionSectionEquiv_restrict R n d (Idx.img_face_subset n a j)
      (ClosedImmCech.altImg_nonempty _) z
  calc
    _ = F.res (ClosedImmCech.altOpen_eq (𝟙 (Proj 𝒜)) (q + 1) s).le
        (F.res (coordinateIntersection_mono R n (Idx.img_face_subset n a j)) v) :=
      congrArg (F.res (ClosedImmCech.altOpen_eq (𝟙 (Proj 𝒜)) (q + 1) s).le) hloc.symm
    _ = F.res
        ((ClosedImmCech.altOpen_eq (𝟙 (Proj 𝒜)) (q + 1) s).le.trans
          (coordinateIntersection_mono R n (Idx.img_face_subset n a j))) v := F.res_res _ _ v
    _ = _ := (F.res_res
      ((stdCoverPullback (𝟙 (Proj 𝒜))).inter_le_inter_face s j)
      (ClosedImmCech.altOpen_eq (𝟙 (Proj 𝒜)) q
        ((stdCoverPullback (𝟙 (Proj 𝒜))).face s j)).le v).symm

/-- The actual section comparison commutes with the two original
Čech differentials, rather than merely comparing their cochain modules. -/
theorem twistingCochainEquiv_d (d q : ℕ)
    (c : GradedModule.cochain (GradedModule.FD R n d) q) :
    twistingCochainEquiv R n d (q + 1) (GradedModule.d (GradedModule.FD R n d) q c) =
      (twistingSectionPresheaf R n d).d (stdCoverPullback (𝟙 (Proj 𝒜))) q
        (twistingCochainEquiv R n d q c) := by
  funext s
  let F := twistingSectionPresheaf R n d
  let a : Idx n (q + 1) := ClosedImmCech.idxEquiv (𝟙 (Proj 𝒜)) (q + 1) s
  let e : GradedModule.sec (GradedModule.FD R n d) (Idx.img n a) →ₗ[R]
      F.obj ((stdCoverPullback (𝟙 (Proj 𝒜))).inter s) :=
    (F.res (ClosedImmCech.altOpen_eq (𝟙 (Proj 𝒜)) (q + 1) s).le).comp
      (twistingFractionSectionEquiv R n d (Idx.img n a)
        (ClosedImmCech.altImg_nonempty _)).toLinearMap
  simp only [twistingCochainEquiv_apply, OModulePresheaf.d_apply]
  change e (GradedModule.d (GradedModule.FD R n d) q c a) = _
  rw [GradedModule.d_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [e.map_smul]
  rw [show (-1 : R) ^ (j : ℕ) = (((-1 : ℤ) ^ (j : ℕ) : ℤ) : R) by
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one], Int.cast_smul_eq_zsmul]
  exact congrArg (fun v => ((-1 : ℤ) ^ (j : ℕ)) • v)
    (twistingCochainEquiv_face R n d q s j
      (c (Idx.face n (ClosedImmCech.idxEquiv (𝟙 (Proj 𝒜)) (q + 1) s) j)))

end AlgebraicGeometry.ProjSpace
