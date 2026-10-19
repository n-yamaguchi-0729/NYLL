/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.LinearAlgebra.FiniteProjectiveTrace
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Data.Int.Interval

/-!
# Alternating trace on bounded complexes of finite projective modules

For a commutative coefficient ring, the actual degreewise projective traces
give an alternating trace on a bounded cochain complex. The native strict
bounds prove that the summand has finite support. The value is independent
of these bounds, is cyclic, and is invariant under actual chain homotopies
and homotopy equivalences.

The homotopy calculation is the bounded-complex part of Stacks Project,
Proposition 64.10.2 (https://stacks.math.columbia.edu/tag/03TI). Passing from
these complexes to arbitrary perfect objects in the derived category, and
the noncommutative coefficient case, are separate constructions.
-/

noncomputable section

universe u v

open CategoryTheory Limits

namespace EtaleCohomology

variable (R : Type u) [CommRing R]
variable (C : CochainComplex (ModuleCat.{v} R) ℤ)
variable [∀ i : ℤ, Module.Finite R (C.X i)]
  [∀ i : ℤ, Module.Projective R (C.X i)]

private theorem signedTrace_support_subset
    (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    (f : ∀ i : ℤ, C.X i ⟶ C.X i) :
    Function.support (fun i : ℤ =>
      i.negOnePow • LinearMap.projectiveTrace R (C.X i) (f i).hom) ⊆ Set.Icc a b := by
  intro i hi
  by_contra hout
  have hzero : IsZero (C.X i) := by
    by_cases hleft : i < a
    · exact C.isZero_of_isStrictlyGE a i hleft
    · have hright : b < i := by
        simp only [Set.mem_Icc] at hout
        omega
      exact C.isZero_of_isStrictlyLE b i hright
  have hf : f i = 0 := hzero.eq_of_src _ _
  exact (Function.mem_support.mp hi) (by
    rw [hf, ModuleCat.hom_zero, map_zero, smul_zero])

/-- The signed degreewise trace is finitely supported on any native bounding interval. -/
theorem signedTrace_hasFiniteSupport
    (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    (f : ∀ i : ℤ, C.X i ⟶ C.X i) :
    Function.HasFiniteSupport (fun i : ℤ =>
      i.negOnePow • LinearMap.projectiveTrace R (C.X i) (f i).hom) :=
  (Set.finite_Icc a b).subset (signedTrace_support_subset R C a b f)

/-- Alternating trace on the actual endomorphisms of a bounded cochain
complex whose terms are finite projective over a commutative ring. -/
def boundedComplexTrace (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b] :
    (C ⟶ C) →ₗ[R] R where
  toFun f := ∑ᶠ i : ℤ, i.negOnePow • LinearMap.projectiveTrace R (C.X i) (f.f i).hom
  map_add' f g := by
    simp only [HomologicalComplex.add_f_apply, ModuleCat.hom_add, map_add, smul_add]
    exact finsum_add_distrib (signedTrace_hasFiniteSupport R C a b f.f)
      (signedTrace_hasFiniteSupport R C a b g.f)
  map_smul' r f := by
    simp only [HomologicalComplex.smul_f_apply, ModuleCat.hom_smul, map_smul,
      RingHom.id_apply]
    rw [smul_finsum' r (signedTrace_hasFiniteSupport R C a b f.f)]
    apply finsum_congr
    intro i
    exact smul_comm _ _ _

/-- The trace is the finite alternating sum on any native bounding interval. -/
theorem boundedComplexTrace_eq_sum (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    (f : C ⟶ C) :
    boundedComplexTrace R C a b f =
      ∑ i ∈ Finset.Icc a b, i.negOnePow • LinearMap.projectiveTrace R (C.X i) (f.f i).hom := by
  apply finsum_eq_sum_of_support_subset
  simpa only [Finset.coe_Icc] using signedTrace_support_subset R C a b f.f

/-- Enlarging or changing the bounding interval does not change the trace. -/
theorem boundedComplexTrace_independent_bounds
    (a b a' b' : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    [C.IsStrictlyGE a'] [C.IsStrictlyLE b'] :
    boundedComplexTrace R C a b = boundedComplexTrace R C a' b' := by
  apply LinearMap.ext
  intro f
  rfl

/-- The alternating trace of the actual coboundary of a degree minus-one
family is zero, by cyclicity and a shift of the finite sum. -/
theorem boundedComplexTrace_nullHomotopicMap
    (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    (h : ∀ i j : ℤ, C.X i ⟶ C.X j) :
    boundedComplexTrace R C a b (Homotopy.nullHomotopicMap h) = 0 := by
  let p : ℤ → R := fun i => i.negOnePow •
    LinearMap.projectiveTrace R (C.X i) (C.d i (i + 1) ≫ h (i + 1) i).hom
  let q : ℤ → R := fun i => i.negOnePow •
    LinearMap.projectiveTrace R (C.X i) (h i (i - 1) ≫ C.d (i - 1) i).hom
  have hp : Function.HasFiniteSupport p :=
    signedTrace_hasFiniteSupport R C a b (fun i => C.d i (i + 1) ≫ h (i + 1) i)
  have hq : Function.HasFiniteSupport q :=
    signedTrace_hasFiniteSupport R C a b (fun i => h i (i - 1) ≫ C.d (i - 1) i)
  have hsum (i : ℤ) :
      i.negOnePow • LinearMap.projectiveTrace R (C.X i)
        ((Homotopy.nullHomotopicMap h).f i).hom = p i + q i := by
    have hprev : (ComplexShape.up ℤ).Rel (i - 1) i := by
      change i - 1 + 1 = i
      omega
    have hnext : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
    rw [Homotopy.nullHomotopicMap_f hprev hnext, ModuleCat.hom_add, map_add, smul_add]
  have hshift (i : ℤ) : q i = -(p (i - 1)) := by
    have hi : i - 1 + 1 = i := by omega
    have hsign : i.negOnePow = -(i - 1).negOnePow := by
      exact (congrArg Int.negOnePow hi).symm.trans (Int.negOnePow_succ (i - 1))
    dsimp only [p, q]
    rw [hi, ModuleCat.hom_comp, ModuleCat.hom_comp,
      LinearMap.projectiveTrace_comp_comm, hsign, Units.neg_smul]
  change (∑ᶠ i : ℤ, i.negOnePow • LinearMap.projectiveTrace R (C.X i)
    ((Homotopy.nullHomotopicMap h).f i).hom) = 0
  rw [finsum_congr hsum, finsum_add_distrib hp hq,
    finsum_congr hshift, finsum_neg_distrib]
  have hbij : Function.Bijective (fun i : ℤ => i - 1) := by
    constructor
    · intro i j hij
      change i - 1 = j - 1 at hij
      omega
    · intro i
      refine ⟨i + 1, ?_⟩
      change i + 1 - 1 = i
      omega
  rw [finsum_comp (fun i : ℤ => i - 1) hbij, add_neg_cancel]

/-- Homotopic endomorphisms have the same alternating trace. -/
theorem boundedComplexTrace_homotopy
    (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    {f g : C ⟶ C} (h : Homotopy f g) :
    boundedComplexTrace R C a b f = boundedComplexTrace R C a b g := by
  apply sub_eq_zero.mp
  rw [← map_sub, h.sub_eq_nullHomotopicMap]
  exact boundedComplexTrace_nullHomotopicMap R C a b h.hom

variable {C}
variable {D : CochainComplex (ModuleCat.{v} R) ℤ}
variable [∀ i : ℤ, Module.Finite R (D.X i)]
  [∀ i : ℤ, Module.Projective R (D.X i)]

/-- Cyclicity holds for maps between different bounded finite projective complexes. -/
theorem boundedComplexTrace_comp_comm
    (a b c d : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    [D.IsStrictlyGE c] [D.IsStrictlyLE d] (f : C ⟶ D) (g : D ⟶ C) :
    boundedComplexTrace R C a b (f ≫ g) = boundedComplexTrace R D c d (g ≫ f) := by
  apply finsum_congr
  intro i
  change i.negOnePow • LinearMap.projectiveTrace R (C.X i) ((g.f i).hom ∘ₗ (f.f i).hom) =
    i.negOnePow • LinearMap.projectiveTrace R (D.X i) ((f.f i).hom ∘ₗ (g.f i).hom)
  rw [LinearMap.projectiveTrace_comp_comm]

/-- Transport through an actual homotopy equivalence preserves trace. -/
theorem boundedComplexTrace_homotopyEquiv
    (a b c d : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    [D.IsStrictlyGE c] [D.IsStrictlyLE d] (e : HomotopyEquiv C D) (f : C ⟶ C) :
    boundedComplexTrace R D c d (e.inv ≫ f ≫ e.hom) = boundedComplexTrace R C a b f := by
  rw [boundedComplexTrace_comp_comm R c d a b e.inv (f ≫ e.hom), Category.assoc]
  have h : Homotopy (f ≫ (e.hom ≫ e.inv)) f := by
    simpa only [Category.comp_id] using e.homotopyHomInvId.compLeft f
  exact boundedComplexTrace_homotopy R C a b h

end EtaleCohomology
