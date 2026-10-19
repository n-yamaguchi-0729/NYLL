/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModuleHEquivFD
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModuleHEquivPi
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedGlobalSections
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwistGlobalSections
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwistFiniteCohomology
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Lean.Elab.Tactic.Omega

/-!
# Polynomial numerators for global sections of shifted free modules

The actual homogeneous polynomial associated to a nonnegative Laurent
monomial has denominator one on every chart. Finite linear combinations
identify the canonical graded augmentation with the previously computed
monomial map to Čech cocycles. It follows that the augmentation is
surjective for every nonnegative free twist. The product comparison then
assembles numerators for finite products of graded modules.

These are statements about the explicit graded Čech complex. No
identification with sections of an arbitrary module presheaf is assumed.
-/

noncomputable section

namespace ProjSpaceCech.GradedModule

universe u

open AlgebraicCurves.Cohomology.Cech.Proofs
open ProjSpaceCech_GradedModule_nonempty_HEquiv_FD.ProjSpaceCech.GradedModule
open ProjSpaceCech_GradedModule_nonempty_HEquiv_pi.ProjSpaceCech.GradedModule
open ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist

variable {R : Type u} [CommRing R] {n : ℕ}

private theorem mon_empty_nonneg (d : ℤ) (b : Twist.Mon n d ∅) (j : Fin (n + 1)) :
    0 ≤ b.val j := by
  apply not_lt.mp
  intro hj
  exact Finset.notMem_empty j (b.property.2 ((Twist.mem_negSupp n).mpr hj))

private def monomialNumerator (d : ℤ) (b : Twist.Mon n d ∅) : (FD R n d).grade 0 :=
  ⟨Xprod (R := R) (fun j => (b.val j).toNat), by
    change Xprod (R := R) (fun j => (b.val j).toNat) ∈ freeGrade R n (0 + d)
    rw [zero_add]
    apply Xprod_mem_freeGrade
    calc
      d = ∑ j, b.val j := b.property.1.symm
      _ = ∑ j, ((b.val j).toNat : ℤ) :=
        Finset.sum_congr rfl fun j _ => (Int.toNat_of_nonneg (mon_empty_nonneg d b j)).symm⟩

private def numeratorCombination (d : ℤ) :
    (Twist.Mon n d ∅ →₀ R) →ₗ[R] (FD R n d).grade 0 :=
  Finsupp.linearCombination R (monomialNumerator (R := R) d)

private theorem zeroSectionMap_monomialNumerator (d : ℤ)
    (I : Finset (Fin (n + 1))) (b : Twist.Mon n d ∅) :
    zeroSectionMap (FD R n d) I (monomialNumerator d b) =
      sec.mk (FD R n d) I (twistFrac d (Twist.Mon.incl n d (Finset.empty_subset I) b)) := by
  apply (sec_mk_eq (FD R n d) I).mpr
  refine ⟨0, fun _ _ => rfl, ?_⟩
  have hden : (twistFrac (R := R) d
      (Twist.Mon.incl n d (Finset.empty_subset I) b)).denExp = 0 := by
    funext j
    change (-b.val j).toNat = 0
    have hj : 0 ≤ b.val j := mon_empty_nonneg d b j
    omega
  rw [hden, zero_add, monMul_zero]
  rfl

private theorem augmentationCochain_numeratorCombination (d : ℤ) :
    (augmentationCochain (FD R n d)).comp (numeratorCombination d) =
      (cochainTwistEquiv (R := R) (n := n) d 0).toLinearMap.comp (constSec R d) := by
  apply Finsupp.lhom_ext
  intro b r
  funext s
  change zeroSectionMap (FD R n d) (Idx.img n s)
      (numeratorCombination d (Finsupp.single b r)) =
    twistToGradSec d (Idx.img n s) (constSec R d (Finsupp.single b r) s)
  rw [numeratorCombination, Finsupp.linearCombination_single, map_smul]
  change r • zeroSectionMap (FD R n d) (Idx.img n s) (monomialNumerator d b) =
    twistToGradSec d (Idx.img n s)
      (Finsupp.mapDomain (Twist.Mon.incl n d (Finset.empty_subset _)) (Finsupp.single b r))
  rw [Finsupp.mapDomain_single, twistToGradSec_single]
  exact congrArg (r • ·) (zeroSectionMap_monomialNumerator d (Idx.img n s) b)

/-- Every global Čech section of a nonnegative shifted free polynomial
module is the evaluation of an actual homogeneous numerator. -/
theorem augmentation_FD_surjective (d : ℤ) (hd : 0 ≤ d) :
    Function.Surjective (augmentation (FD R n d)) := by
  intro z
  have hz : z.val ∈ (LinearMap.ker (Twist.d R n d 0)).map
      (cochainTwistEquiv (R := R) (n := n) d 0).toLinearMap := by
    rw [cochainTwistEquiv_ker]
    exact z.property
  obtain ⟨w, hw, hwz⟩ := hz
  obtain ⟨g, hg⟩ := Twist.constSectionMap_surjective R (n := n) d hd
    (show Twist.H R n d 0 from ⟨w, hw⟩)
  refine ⟨numeratorCombination d g, ?_⟩
  apply Subtype.ext
  have hconst : constSec R d g = w := congrArg Subtype.val hg
  exact (LinearMap.congr_fun (augmentationCochain_numeratorCombination d) g).trans
    ((congrArg (cochainTwistEquiv (R := R) (n := n) d 0) hconst).trans hwz)

/-- Numerators for the components of a finite product assemble to a
numerator for its actual global Čech section. -/
theorem augmentation_pi_surjective {ι : Type} [Fintype ι]
    (D : ι → GradedModule R n) (hD : ∀ k : ι, Function.Surjective (augmentation (D k))) :
    Function.Surjective (augmentation (pi D)) := by
  intro z
  let E : H (pi D) 0 ≃ₗ[R] (∀ k : ι, H (D k) 0) := kerPiEquiv D 0
  choose m hm using fun k : ι => hD k (E z k)
  let numerator : (pi D).grade 0 :=
    ⟨fun k => (m k).val, fun k _ => (m k).property⟩
  refine ⟨numerator, E.injective ?_⟩
  funext k
  apply Subtype.ext
  funext s
  let a : LinearMap.ker (d (pi D) 0) := augmentation (pi D) numerator
  have ha := congrFun (kerPiEquiv_apply_coe D 0 a k) s
  have hprojection : cochainPiEquiv D 0 a.val k s =
      zeroSectionMap (D k) (Idx.img n s) (m k) := rfl
  exact ha.trans (hprojection.trans (congrFun (congrArg Subtype.val (hm k)) s))

end ProjSpaceCech.GradedModule
