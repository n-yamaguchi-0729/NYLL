/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Notation.Pi.Basic
import Lean.Elab.Tactic.NormCast

/-!
# Coordinate trivializations of shifted homogeneous fractions

Multiplication by a coordinate power is an actual graded map from a
module to its positive shift. On every coordinate intersection containing
that coordinate, the map is bijective after homogeneous localization.
The inverse appends exactly that coordinate power to the denominator.

This construction works for any graded module, without regularity of
its coordinate operators. Any additional factor needed in an equality
is retained in the witness for equality of localized fractions.
-/

noncomputable section

namespace ProjSpaceCech.GradedModule

universe u

open scoped BigOperators

variable {R : Type u} [CommRing R] {n : ℕ}

private theorem single_supported {I : Finset (Fin (n + 1))}
    {i : Fin (n + 1)} (hi : i ∈ I) (d : ℕ) :
    ∀ j ∉ I, Pi.single (M := fun _ : Fin (n + 1) => ℕ) i d j = 0 := by
  intro j hj
  exact Pi.single_eq_of_ne (M := fun _ : Fin (n + 1) => ℕ)
    (fun h : j = i => hj (h.symm ▸ hi)) d

private theorem sum_cast_add_single (a : Fin (n + 1) → ℕ)
    (i : Fin (n + 1)) (d : ℕ) :
    (∑ j, (((a + Pi.single (M := fun _ : Fin (n + 1) => ℕ) i d) j : ℕ) : ℤ)) =
      (∑ j, (a j : ℤ)) + d := by
  have hs : (∑ j : Fin (n + 1),
      ((Pi.single (M := fun _ : Fin (n + 1) => ℕ) i d j : ℕ) : ℤ)) = (d : ℤ) := by
    exact_mod_cast Fintype.sum_pi_single' i d
  simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib, hs]

/-- Multiplication by a coordinate power, as an actual map to the
corresponding shifted graded module. -/
def coordinateRaiseHom (D : GradedModule R n) (d : ℕ) (i : Fin (n + 1)) :
    Hom D (D.shift d) where
  toLinearMap := D.xMul i ^ d
  mem_grade a m hm := D.xMul_pow_mem_grade i d a m hm
  xMul_comm j := by
    change D.xMul i ^ d * D.xMul j = D.xMul j * D.xMul i ^ d
    simpa only [pow_one] using (D.xMul_pow_commute i j d 1).eq

/-- The actual fraction obtained by appending one coordinate power to
the denominator and retaining the original numerator. -/
def coordinateDenominatorFrac (D : GradedModule R n) (d : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I)
    (x : Frac (D.shift d) I) : Frac D I where
  denExp := x.denExp + Pi.single i d
  hden j hj := by
    rw [Pi.add_apply, x.hden j hj, single_supported hi d j hj, add_zero]
  num := x.num
  hnum := by
    rw [sum_cast_add_single]
    exact x.hnum

/-- Adding the coordinate denominator gives an explicit preimage under
the original coordinate multiplication map on localized sections. -/
theorem coordinateRaiseHom_secMap_coordinateDenominatorFrac
    (D : GradedModule R n) (d : ℕ) {I : Finset (Fin (n + 1))}
    (i : Fin (n + 1)) (hi : i ∈ I) (x : Frac (D.shift d) I) :
    (coordinateRaiseHom D d i).secMap I
      (sec.mk D I (coordinateDenominatorFrac D d i hi x)) = sec.mk (D.shift d) I x := by
  apply (sec_mk_eq (D.shift d) I).mpr
  refine ⟨0, fun _ _ => rfl, ?_⟩
  let m : D.M := x.num
  change monMul D (0 + x.denExp) ((D.xMul i ^ d) m) =
    monMul D (0 + (x.denExp + Pi.single i d)) m
  rw [zero_add, zero_add, ← monMul_single D i d]
  exact (monMul_add_apply D x.denExp (Pi.single i d) m).symm

/-- Coordinate multiplication is injective on each homogeneous
localization in which that coordinate is inverted. -/
theorem coordinateRaiseHom_secMap_injective
    (D : GradedModule R n) (d : ℕ) {I : Finset (Fin (n + 1))}
    (i : Fin (n + 1)) (hi : i ∈ I) :
    Function.Injective ((coordinateRaiseHom D d i).secMap I) := by
  rintro ⟨x⟩ ⟨y⟩ hxy
  obtain ⟨c, hc, h⟩ := (sec_mk_eq (D.shift d) I).mp hxy
  apply (sec_mk_eq D I).mpr
  refine ⟨c + Pi.single i d, Frac.supp_add I hc (single_supported hi d), ?_⟩
  change monMul D (c + y.denExp) ((D.xMul i ^ d) x.num) =
    monMul D (c + x.denExp) ((D.xMul i ^ d) y.num) at h
  rw [← monMul_single D i d,
    ← monMul_add_apply, ← monMul_add_apply] at h
  rw [add_right_comm c (Pi.single i d) y.denExp,
    add_right_comm c (Pi.single i d) x.denExp]
  exact h

/-- Every shifted homogeneous fraction is in the image of coordinate
multiplication, with its preimage given by appending the coordinate
power to the denominator. -/
theorem coordinateRaiseHom_secMap_surjective
    (D : GradedModule R n) (d : ℕ) {I : Finset (Fin (n + 1))}
    (i : Fin (n + 1)) (hi : i ∈ I) :
    Function.Surjective ((coordinateRaiseHom D d i).secMap I) := by
  rintro ⟨x⟩
  exact ⟨sec.mk D I (coordinateDenominatorFrac D d i hi x),
    coordinateRaiseHom_secMap_coordinateDenominatorFrac D d i hi x⟩

/-- The linear coordinate trivialization of a positive graded shift on
an intersection containing the chosen coordinate. Its inverse is the
original coordinate multiplication map. -/
def coordinateShiftEquiv (D : GradedModule R n) (d : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I) :
    sec (D.shift d) I ≃ₗ[R] sec D I :=
  (LinearEquiv.ofBijective ((coordinateRaiseHom D d i).secMap I)
    ⟨coordinateRaiseHom_secMap_injective D d i hi,
      coordinateRaiseHom_secMap_surjective D d i hi⟩).symm

theorem coordinateShiftEquiv_symm_apply (D : GradedModule R n) (d : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I) (z : sec D I) :
    (coordinateShiftEquiv D d i hi).symm z = (coordinateRaiseHom D d i).secMap I z := rfl

/-- The forward coordinate trivialization has the stated, explicit
coordinate denominator on every actual fraction representative. -/
theorem coordinateShiftEquiv_apply_mk (D : GradedModule R n) (d : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I)
    (x : Frac (D.shift d) I) :
    coordinateShiftEquiv D d i hi (sec.mk (D.shift d) I x) =
      sec.mk D I (coordinateDenominatorFrac D d i hi x) := by
  apply (coordinateShiftEquiv D d i hi).symm.injective
  rw [LinearEquiv.symm_apply_apply, coordinateShiftEquiv_symm_apply]
  exact (coordinateRaiseHom_secMap_coordinateDenominatorFrac D d i hi x).symm

/-- The coordinate trivialization commutes with further localization,
using the same original coordinate on both intersections. -/
theorem coordinateShiftEquiv_restrict (D : GradedModule R n) (d : ℕ)
    {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J)
    (i : Fin (n + 1)) (hi : i ∈ I) (z : sec (D.shift d) I) :
    coordinateShiftEquiv D d i (hIJ hi) (secIncl (D.shift d) hIJ z) =
      secIncl D hIJ (coordinateShiftEquiv D d i hi z) := by
  apply (coordinateShiftEquiv D d i (hIJ hi)).symm.injective
  rw [LinearEquiv.symm_apply_apply, coordinateShiftEquiv_symm_apply]
  have hinv : (coordinateRaiseHom D d i).secMap I
      (coordinateShiftEquiv D d i hi z) = z :=
    (coordinateShiftEquiv D d i hi).symm_apply_apply z
  calc
    secIncl (D.shift d) hIJ z = secIncl (D.shift d) hIJ
        ((coordinateRaiseHom D d i).secMap I (coordinateShiftEquiv D d i hi z)) :=
      congrArg (secIncl (D.shift d) hIJ) hinv.symm
    _ = (coordinateRaiseHom D d i).secMap J
        (secIncl D hIJ (coordinateShiftEquiv D d i hi z)) :=
      LinearMap.congr_fun ((coordinateRaiseHom D d i).secMap_incl hIJ)
        (coordinateShiftEquiv D d i hi z)

end ProjSpaceCech.GradedModule
