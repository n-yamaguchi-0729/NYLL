/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Cech.ReesTensorCech
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorPresheaf
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Homogeneous retracts of actual Rees tensor Čech cohomology

The constructed coefficient and homogeneous maps preserve the original
cocycles and boundaries. They therefore descend to the original quotient
cohomology modules, and their composite is still the identity.

Vanishing for the actual Rees tensor complex consequently implies
vanishing for every actual ideal-power tensor complex. This is a degree
extraction theorem; the geometric supply of Rees cohomology vanishing
is separate from the constructed maps proved here.
-/

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.ReesTensor

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A) (M : X.Modules) (K : X.OrderedAffineCover)

/-- Extraction of the original coefficient of an actual Rees cocycle. -/
def coefficientCocycle (n q : ℕ) :
    LinearMap.ker ((reesTensorPresheaf f I M).d K q) →ₗ[A]
      LinearMap.ker ((idealTensorPresheaf f I M n).d K q) :=
  (coefficientCochain f I M K n q).restrict fun c hc =>
    (mem_ker_iff_coefficients f I M K q c).mp hc n

/-- Homogeneous insertion of an actual ideal-power tensor cocycle. -/
def homogeneousCocycle (n q : ℕ) :
    LinearMap.ker ((idealTensorPresheaf f I M n).d K q) →ₗ[A]
      LinearMap.ker ((reesTensorPresheaf f I M).d K q) :=
  (homogeneousCochain f I M K n q).restrict fun c hc => LinearMap.mem_ker.mpr <| by
    calc
      (reesTensorPresheaf f I M).d K q (homogeneousCochain f I M K n q c) =
          homogeneousCochain f I M K n (q + 1) ((idealTensorPresheaf f I M n).d K q c) :=
        (homogeneousCochain_d f I M K n q c).symm
      _ = homogeneousCochain f I M K n (q + 1) 0 :=
        congrArg (homogeneousCochain f I M K n (q + 1)) (LinearMap.mem_ker.mp hc)
      _ = 0 := map_zero _

/-- Extraction of coefficients on the original quotient Čech cohomology module. -/
def coefficientHSucc (n q : ℕ) :
    (reesTensorPresheaf f I M).HSucc K q →ₗ[A]
      (idealTensorPresheaf f I M n).HSucc K q :=
  Submodule.mapQ _ _ (coefficientCocycle f I M K n (q + 1)) fun x hx => by
    change coefficientCochain f I M K n (q + 1) x.val ∈
      LinearMap.range ((idealTensorPresheaf f I M n).d K q)
    exact coefficientCochain_mem_range f I M K n q hx

/-- Homogeneous insertion on the original quotient Čech cohomology module. -/
def homogeneousHSucc (n q : ℕ) :
    (idealTensorPresheaf f I M n).HSucc K q →ₗ[A]
      (reesTensorPresheaf f I M).HSucc K q :=
  Submodule.mapQ _ _ (homogeneousCocycle f I M K n (q + 1)) fun x hx => by
    change homogeneousCochain f I M K n (q + 1) x.val ∈
      LinearMap.range ((reesTensorPresheaf f I M).d K q)
    exact (homogeneousCochain_mem_range_iff f I M K n q x.val).mpr hx

/-- The quotient coefficient map retains the constructed map on the original cocycle. -/
theorem coefficientHSucc_mk (n q : ℕ)
    (z : LinearMap.ker ((reesTensorPresheaf f I M).d K (q + 1))) :
    coefficientHSucc f I M K n q (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (coefficientCocycle f I M K n (q + 1) z) := rfl

/-- The quotient homogeneous map retains the constructed map on the original cocycle. -/
theorem homogeneousHSucc_mk (n q : ℕ)
    (z : LinearMap.ker ((idealTensorPresheaf f I M n).d K (q + 1))) :
    homogeneousHSucc f I M K n q (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (homogeneousCocycle f I M K n (q + 1) z) := rfl

/-- Coefficient extraction retracts homogeneous insertion on the actual quotient cohomology. -/
theorem coefficientHSucc_homogeneousHSucc (n q : ℕ)
    (x : (idealTensorPresheaf f I M n).HSucc K q) :
    coefficientHSucc f I M K n q (homogeneousHSucc f I M K n q x) = x := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro z
  rw [homogeneousHSucc_mk, coefficientHSucc_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact coefficientCochain_homogeneousCochain f I M K n (q + 1) z.val

/-- Each original ideal-power tensor cohomology module embeds by homogeneous insertion. -/
theorem homogeneousHSucc_injective (n q : ℕ) :
    Function.Injective (homogeneousHSucc f I M K n q) := by
  intro x y h
  calc
    x = coefficientHSucc f I M K n q (homogeneousHSucc f I M K n q x) :=
      (coefficientHSucc_homogeneousHSucc f I M K n q x).symm
    _ = coefficientHSucc f I M K n q (homogeneousHSucc f I M K n q y) :=
      congrArg (coefficientHSucc f I M K n q) h
    _ = y := coefficientHSucc_homogeneousHSucc f I M K n q y

/-- Every original ideal-power tensor cohomology class is an actual Rees coefficient. -/
theorem coefficientHSucc_surjective (n q : ℕ) :
    Function.Surjective (coefficientHSucc f I M K n q) := by
  intro x
  exact ⟨homogeneousHSucc f I M K n q x, coefficientHSucc_homogeneousHSucc f I M K n q x⟩

/-- Vanishing of the actual Rees cohomology implies vanishing in every original degree. -/
theorem subsingleton_idealTensorHSucc (n q : ℕ)
    [Subsingleton ((reesTensorPresheaf f I M).HSucc K q)] :
    Subsingleton ((idealTensorPresheaf f I M n).HSucc K q) :=
  ⟨fun x y => homogeneousHSucc_injective f I M K n q
    (Subsingleton.elim (homogeneousHSucc f I M K n q x)
      (homogeneousHSucc f I M K n q y))⟩

end AlgebraicGeometry.Scheme.Modules.ReesTensor
