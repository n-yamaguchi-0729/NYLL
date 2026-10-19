/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorPresheaf
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Actual Rees tensor coefficients in the original Čech complex

The sectionwise coefficient and homogeneous maps give maps of the
original ordered Čech cochains. Their restriction compatibility proves
that they commute with the original alternating differentials.

Every degree is a retract of the original Rees cochain complex. In
particular, a homogeneous cochain is an actual Rees coboundary exactly
when its original coefficient is a coboundary in the corresponding
ideal-power tensor complex. The proof constructs the preceding cochain
by extracting that coefficient; it requires no chosen comparison of
cohomology groups or boundary condition as additional input.
-/

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.ReesTensor

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A) (M : X.Modules) (K : X.OrderedAffineCover)

private def cochainMapOfHom {F G : OModulePresheaf f} (φ : OModulePresheaf.Hom F G)
    (q : ℕ) : F.cochain K q →ₗ[A] G.cochain K q :=
  LinearMap.pi fun s => (φ.app (K.inter s)).comp (LinearMap.proj s)

private theorem cochainMapOfHom_d {F G : OModulePresheaf f} (φ : OModulePresheaf.Hom F G)
    (q : ℕ) (c : F.cochain K q) :
    cochainMapOfHom f K φ (q + 1) (F.d K q c) =
      G.d K q (cochainMapOfHom f K φ q c) := by
  funext s
  simp only [cochainMapOfHom, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    OModulePresheaf.d_apply, map_sum, map_zsmul]
  exact Finset.sum_congr rfl fun j _ => congrArg _
    (φ.naturality_apply (K.inter_le_inter_face s j) (c (K.face s j)))

/-- Extraction of one actual coefficient on each original cover intersection. -/
def coefficientCochain (n q : ℕ) :
    (reesTensorPresheaf f I M).cochain K q →ₗ[A]
      (idealTensorPresheaf f I M n).cochain K q :=
  cochainMapOfHom f K (coefficient f I M n) q

/-- Insertion of one actual homogeneous coefficient on each original cover intersection. -/
def homogeneousCochain (n q : ℕ) :
    (idealTensorPresheaf f I M n).cochain K q →ₗ[A]
      (reesTensorPresheaf f I M).cochain K q :=
  cochainMapOfHom f K (homogeneous f I M n) q

/-- Coefficient extraction on cochains retains the original sectionwise coefficient. -/
theorem coefficientCochain_apply (n q : ℕ)
    (c : (reesTensorPresheaf f I M).cochain K q) (s : K.Idx q) :
    coefficientCochain f I M K n q c s = (coefficient f I M n).app (K.inter s) (c s) := rfl

/-- Homogeneous insertion on cochains retains the original sectionwise insertion. -/
theorem homogeneousCochain_apply (n q : ℕ)
    (c : (idealTensorPresheaf f I M n).cochain K q) (s : K.Idx q) :
    homogeneousCochain f I M K n q c s = (homogeneous f I M n).app (K.inter s) (c s) := rfl

/-- Actual coefficient extraction commutes with the original alternating Čech differential. -/
theorem coefficientCochain_d (n q : ℕ) (c : (reesTensorPresheaf f I M).cochain K q) :
    coefficientCochain f I M K n (q + 1) ((reesTensorPresheaf f I M).d K q c) =
      (idealTensorPresheaf f I M n).d K q (coefficientCochain f I M K n q c) :=
  cochainMapOfHom_d f K (coefficient f I M n) q c

/-- Actual homogeneous insertion commutes with the original alternating Čech differential. -/
theorem homogeneousCochain_d (n q : ℕ)
    (c : (idealTensorPresheaf f I M n).cochain K q) :
    homogeneousCochain f I M K n (q + 1) ((idealTensorPresheaf f I M n).d K q c) =
      (reesTensorPresheaf f I M).d K q (homogeneousCochain f I M K n q c) :=
  cochainMapOfHom_d f K (homogeneous f I M n) q c

/-- The coefficient cochain map retracts the actual homogeneous insertion. -/
theorem coefficientCochain_homogeneousCochain (n q : ℕ)
    (c : (idealTensorPresheaf f I M n).cochain K q) :
    coefficientCochain f I M K n q (homogeneousCochain f I M K n q c) = c := by
  funext s
  exact congrArg
    (fun φ : OModulePresheaf.Hom (idealTensorPresheaf f I M n)
      (idealTensorPresheaf f I M n) => φ.app (K.inter s) (c s))
    (coefficient_homogeneous f I M n)

/-- Every distinct coefficient of a homogeneous cochain is zero. -/
theorem coefficientCochain_homogeneousCochain_ne (n k q : ℕ) (h : k ≠ n)
    (c : (idealTensorPresheaf f I M n).cochain K q) :
    coefficientCochain f I M K k q (homogeneousCochain f I M K n q c) = 0 := by
  funext s
  exact coefficient_homogeneous_ne f I M n k h (K.inter s) (c s)

/-- The actual coefficient cochains jointly detect an original Rees cochain. -/
theorem cochain_ext_coefficients (q : ℕ)
    {c c' : (reesTensorPresheaf f I M).cochain K q}
    (h : ∀ n, coefficientCochain f I M K n q c = coefficientCochain f I M K n q c') :
    c = c' := by
  funext s
  apply ext_coefficients f I M (K.inter s)
  intro n
  exact congrFun (h n) s

/-- A Rees cochain is an original cocycle exactly when every original coefficient is a cocycle. -/
theorem mem_ker_iff_coefficients (q : ℕ) (c : (reesTensorPresheaf f I M).cochain K q) :
    c ∈ LinearMap.ker ((reesTensorPresheaf f I M).d K q) ↔
      ∀ n, coefficientCochain f I M K n q c ∈
        LinearMap.ker ((idealTensorPresheaf f I M n).d K q) := by
  constructor
  · intro hc n
    apply LinearMap.mem_ker.mpr
    calc
      (idealTensorPresheaf f I M n).d K q (coefficientCochain f I M K n q c) =
          coefficientCochain f I M K n (q + 1) ((reesTensorPresheaf f I M).d K q c) :=
        (coefficientCochain_d f I M K n q c).symm
      _ = coefficientCochain f I M K n (q + 1) 0 :=
        congrArg (coefficientCochain f I M K n (q + 1)) (LinearMap.mem_ker.mp hc)
      _ = 0 := map_zero _
  · intro hc
    apply LinearMap.mem_ker.mpr
    apply cochain_ext_coefficients f I M K (q + 1)
    intro n
    rw [coefficientCochain_d, map_zero]
    exact LinearMap.mem_ker.mp (hc n)

/-- Extracting any original coefficient of an actual Rees coboundary gives a coboundary. -/
theorem coefficientCochain_mem_range (n q : ℕ)
    {c : (reesTensorPresheaf f I M).cochain K (q + 1)}
    (hc : c ∈ LinearMap.range ((reesTensorPresheaf f I M).d K q)) :
    coefficientCochain f I M K n (q + 1) c ∈
      LinearMap.range ((idealTensorPresheaf f I M n).d K q) := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨coefficientCochain f I M K n q b, ?_⟩
  exact (coefficientCochain_d f I M K n q b).symm.trans
    (congrArg (coefficientCochain f I M K n (q + 1)) hb)

/-- A homogeneous cochain is an actual Rees coboundary if and only if its original
coefficient is a coboundary in the original ideal-power tensor complex. -/
theorem homogeneousCochain_mem_range_iff (n q : ℕ)
    (c : (idealTensorPresheaf f I M n).cochain K (q + 1)) :
    homogeneousCochain f I M K n (q + 1) c ∈
        LinearMap.range ((reesTensorPresheaf f I M).d K q) ↔
      c ∈ LinearMap.range ((idealTensorPresheaf f I M n).d K q) := by
  constructor
  · intro hc
    have h := coefficientCochain_mem_range f I M K n q hc
    rw [coefficientCochain_homogeneousCochain] at h
    exact h
  · rintro ⟨b, hb⟩
    refine ⟨homogeneousCochain f I M K n q b, ?_⟩
    exact (homogeneousCochain_d f I M K n q b).symm.trans
      (congrArg (homogeneousCochain f I M K n (q + 1)) hb)

end AlgebraicGeometry.Scheme.Modules.ReesTensor
