/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Pi

/-!
# Evaluation of graded numerators as global sections

A degree-zero homogeneous numerator defines a fraction with denominator
one on every coordinate chart. These fractions agree on intersections,
so their actual Čech differential vanishes. The construction is linear
and commutes with every graded homomorphism. Applying it to a shifted
module evaluates the corresponding homogeneous degree as global sections
of that twist.

These maps retain the literal numerator. They are the maps whose eventual
surjectivity permits compatible formal global generators to be lifted
through finite graded presentations.
-/

noncomputable section

namespace ProjSpaceCech.GradedModule

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

/-- A homogeneous numerator of degree zero, viewed on one projective
coordinate chart with denominator one. -/
def zeroSectionMap (D : GradedModule R n) (I : Finset (Fin (n + 1))) :
    D.grade 0 →ₗ[R] sec D I where
  toFun m := sec.mk D I
    ⟨0, fun _ _ => rfl, m.val, by
      simpa only [Pi.zero_apply, Nat.cast_zero, Finset.sum_const_zero] using m.property⟩
  map_add' m m' := sec_mk_add D I 0 (fun _ _ => rfl)
    (by simpa only [Pi.zero_apply, Nat.cast_zero, Finset.sum_const_zero] using m.property)
    (by simpa only [Pi.zero_apply, Nat.cast_zero, Finset.sum_const_zero] using m'.property)
  map_smul' r m := (sec_mk_smul D I r
    ⟨0, fun _ _ => rfl, m.val, by
      simpa only [Pi.zero_apply, Nat.cast_zero, Finset.sum_const_zero] using m.property⟩).symm

/-- Restricting a zero-denominator fraction retains its numerator. -/
theorem secIncl_zeroSectionMap (D : GradedModule R n)
    {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) (m : D.grade 0) :
    secIncl D hIJ (zeroSectionMap D I m) = zeroSectionMap D J m := rfl

/-- The same homogeneous numerator on every coordinate chart. -/
def augmentationCochain (D : GradedModule R n) : D.grade 0 →ₗ[R] cochain D 0 :=
  LinearMap.pi fun s => zeroSectionMap D (Idx.img n s)

/-- The actual Čech cocycle equation for homogeneous numerators. -/
theorem augmentationCochain_mem_ker (D : GradedModule R n) (m : D.grade 0) :
    augmentationCochain D m ∈ LinearMap.ker (d D 0) := by
  apply LinearMap.mem_ker.mpr
  funext s
  rw [d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    augmentationCochain, LinearMap.pi_apply, faceRes, secIncl_zeroSectionMap,
    one_smul, neg_one_smul, add_neg_cancel, Pi.zero_apply]

/-- Evaluation of a degree-zero homogeneous numerator as an actual
global section in the Čech complex. -/
def augmentation (D : GradedModule R n) : D.grade 0 →ₗ[R] H D 0 :=
  (augmentationCochain D).codRestrict (LinearMap.ker (d D 0))
    (augmentationCochain_mem_ker D)

/-- On each chart, evaluation is the specified fraction with denominator
one. -/
theorem augmentation_apply (D : GradedModule R n) (m : D.grade 0) (s : Idx n 0) :
    (augmentation D m).val s = zeroSectionMap D (Idx.img n s) m := rfl

/-- A graded homomorphism restricted to a specified homogeneous degree. -/
def Hom.gradeMap {D E : GradedModule R n} (φ : Hom D E) (e : ℤ) :
    D.grade e →ₗ[R] E.grade e :=
  φ.toLinearMap.restrict (φ.mem_grade e)

/-- A graded map acts on each numerator before or after passage to the
corresponding zero-denominator fraction. -/
theorem zeroSectionMap_naturality {D E : GradedModule R n} (φ : Hom D E)
    (I : Finset (Fin (n + 1))) (m : D.grade 0) :
    Hom.secMap φ I (zeroSectionMap D I m) =
      zeroSectionMap E I (φ.gradeMap 0 m) := rfl

/-- Evaluation as a global section is natural in the graded module. -/
theorem augmentation_naturality {D E : GradedModule R n} (φ : Hom D E)
    (m : D.grade 0) :
    Hom.HMap φ 0 (augmentation D m) = augmentation E (φ.gradeMap 0 m) := by
  apply Subtype.ext
  funext s
  exact zeroSectionMap_naturality φ (Idx.img n s) m

end ProjSpaceCech.GradedModule
