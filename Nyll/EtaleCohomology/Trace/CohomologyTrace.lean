/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Trace.PerfectHomology
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Cohomological bounds and coefficient extension for perfect traces

Native derived cohomological bounds restrict the trace sum independently of
the chosen projective model. In amplitude zero through two this gives the
three cohomological terms used in the curve trace formula. Extending the
coefficient field commutes with the traces of the actual cohomology maps.
-/

@[expose] public section

noncomputable section

universe u v w z

open CategoryTheory
open scoped TensorProduct

namespace EtaleCohomology

variable {k : Type u} [Field k]
variable [HasDerivedCategory.{w} (ModuleCat.{v} k)]
variable {A : DerivedCategory (ModuleCat.{v} k)}

/-- Cohomological bounds on the derived object itself give finite limits
for the alternating trace sum, independent of any chosen model bounds. -/
theorem perfectComplexTrace_eq_sum_homology_of_bounds
    (hA : IsPerfectComplex k A) (a b : ℤ) [A.IsGE a] [A.IsLE b] (f : A ⟶ A) :
    perfectComplexTrace k A hA f =
      ∑ i ∈ Finset.Icc a b, i.negOnePow •
        LinearMap.trace k ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).obj A)
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map f).hom := by
  rw [perfectComplexTrace_eq_finsum_homology]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hout
  have hz : Limits.IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).obj A) := by
    by_cases hl : i < a
    · exact DerivedCategory.isZero_of_isGE A a i hl
    · have hr : b < i := by
        simp only [Finset.mem_coe, Finset.mem_Icc] at hout
        omega
      exact DerivedCategory.isZero_of_isLE A b i hr
  have hf : (DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map f = 0 :=
    hz.eq_of_src _ _
  exact (Function.mem_support.mp hi) (by
    rw [hf, ModuleCat.hom_zero, map_zero, smul_zero])

/-- In actual derived amplitude `[0,2]`, the perfect trace is `tr H⁰ − tr H¹ + tr H²`. -/
theorem perfectComplexTrace_eq_trace_zero_sub_one_add_two
    (hA : IsPerfectComplex k A) [A.IsGE 0] [A.IsLE 2] (f : A ⟶ A) :
    perfectComplexTrace k A hA f =
      LinearMap.trace k ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0).obj A)
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0).map f).hom -
        LinearMap.trace k ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 1).obj A)
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 1).map f).hom +
        LinearMap.trace k ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 2).obj A)
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 2).map f).hom := by
  rw [perfectComplexTrace_eq_sum_homology_of_bounds hA 0 2]
  have hinterval : Finset.Icc (0 : ℤ) 2 = {0, 1, 2} := by decide
  have htwo : (2 : ℤ).negOnePow = 1 := by
    simpa only [mul_one] using Int.negOnePow_two_mul 1
  rw [hinterval]
  rw [Finset.sum_insert (by decide : (0 : ℤ) ∉ ({1, 2} : Finset ℤ)),
    Finset.sum_insert (by decide : (1 : ℤ) ∉ ({2} : Finset ℤ)), Finset.sum_singleton]
  simp only [Int.negOnePow_zero, Int.negOnePow_one, htwo, Units.neg_smul,
    one_smul, sub_eq_add_neg, add_assoc]

/-- Scalar extension of the actual cohomology endomorphisms preserves the
alternating trace. This concerns the tensor extensions of those modules;
it assumes no geometric or derived base-change comparison. -/
theorem perfectComplexTrace_eq_finsum_homology_baseChange
    (L : Type z) [Field L] [Algebra k L] (hA : IsPerfectComplex k A) (f : A ⟶ A) :
    algebraMap k L (perfectComplexTrace k A hA f) =
      ∑ᶠ i : ℤ, i.negOnePow •
        LinearMap.trace L
          (L ⊗[k] (DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).obj A)
          (((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map f).hom.baseChange L) := by
  rw [perfectComplexTrace_eq_finsum_homology]
  have hmap := (algebraMap k L).toAddMonoidHom.map_finsum_of_injective
    (algebraMap k L).injective (fun i : ℤ => i.negOnePow •
      LinearMap.trace k ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).obj A)
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map f).hom)
  change algebraMap k L _ = _ at hmap
  rw [hmap]
  apply finsum_congr
  intro i
  have : Module.Finite k
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).obj A) :=
    (Classical.choice hA).finite_homology i
  rw [LinearMap.trace_baseChange]
  simp only [Units.smul_def, map_zsmul]
  rfl

end EtaleCohomology
