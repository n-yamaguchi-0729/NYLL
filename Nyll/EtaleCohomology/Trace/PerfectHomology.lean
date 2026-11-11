/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Trace.Hopf
public import Nyll.EtaleCohomology.Trace.Perfect
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Perfect-complex trace and actual derived cohomology over a field

The representing isomorphism of a perfect complex and the native
localization comparison supply its homology comparison. Hopf's formula
therefore computes the intrinsic trace using the actual derived-category
homology functors, for every derived endomorphism.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace EtaleCohomology

variable {k : Type u} [Field k]
variable [HasDerivedCategory.{w} (ModuleCat.{v} k)]
variable {A : DerivedCategory (ModuleCat.{v} k)}

namespace PerfectComplexModel

/-- The actual homology of a perfect model identifies with the homology of
the represented derived object through the native localization comparison. -/
def homologyIso (P : PerfectComplexModel k A) (i : ℤ) :
    P.complex.homology i ≅ (DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).obj A :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} k) i).app P.complex).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).mapIso P.iso

/-- The cohomology modules of an actual perfect derived object over a field
are finite dimensional, as quotients of subspaces of its finite model. -/
theorem finite_homology (P : PerfectComplexModel k A) (i : ℤ) :
    Module.Finite k ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).obj A) := by
  have : Module.Finite k (P.complex.cycles i) :=
    Module.Finite.of_injective (P.complex.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have : Module.Finite k (P.complex.homology i) :=
    Module.Finite.of_surjective (P.complex.homologyπ i).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  exact Module.Finite.of_surjective (P.homologyIso i).hom.hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

private lemma homology_map_conjugate (P : PerfectComplexModel k A)
    (f : P.complex ⟶ P.complex) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map
        (P.iso.inv ≫ DerivedCategory.Q.map f ≫ P.iso.hom) =
      (P.homologyIso i).inv ≫ HomologicalComplex.homologyMap f i ≫
        (P.homologyIso i).hom := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{v} k) i
  let e := (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} k) i).app P.complex
  have hnat : H.map (DerivedCategory.Q.map f) ≫ e.hom =
      e.hom ≫ HomologicalComplex.homologyMap f i :=
    DerivedCategory.homologyFunctorFactors_hom_naturality f i
  have hmid : H.map (DerivedCategory.Q.map f) =
      e.hom ≫ HomologicalComplex.homologyMap f i ≫ e.inv := by
    exact (e.eq_comp_inv).mpr hnat
  change H.map (P.iso.inv ≫ DerivedCategory.Q.map f ≫ P.iso.hom) =
    H.map P.iso.inv ≫ e.hom ≫ HomologicalComplex.homologyMap f i ≫
      e.inv ≫ H.map P.iso.hom
  rw [Functor.map_comp, Functor.map_comp, hmid]
  rfl

private lemma trace_homology_map (P : PerfectComplexModel k A)
    (f : P.complex ⟶ P.complex) (i : ℤ) :
    LinearMap.trace k ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).obj A)
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map
          (P.iso.inv ≫ DerivedCategory.Q.map f ≫ P.iso.hom)).hom =
      LinearMap.trace k (P.complex.homology i)
        (HomologicalComplex.homologyMap f i).hom := by
  rw [homology_map_conjugate]
  change LinearMap.trace k _ ((P.homologyIso i).toLinearEquiv.conj
    (HomologicalComplex.homologyMap f i).hom) = _
  exact LinearMap.trace_conj' _ _

/-- A perfect model's trace is the alternating trace on the actual
cohomology of the derived object, for arbitrary derived endomorphisms. -/
theorem trace_eq_finsum_homology (P : PerfectComplexModel k A) (f : A ⟶ A) :
    P.trace f = ∑ᶠ i : ℤ, i.negOnePow •
      LinearMap.trace k ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).obj A)
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map f).hom := by
  obtain ⟨g, rfl⟩ := P.exists_chainMap f
  rw [P.trace_map, boundedComplexTrace_eq_finsum_homology]
  apply finsum_congr
  intro i
  rw [trace_homology_map]

/-- The same formula is a finite sum on the actual model's bounding interval. -/
theorem trace_eq_sum_homology (P : PerfectComplexModel k A) (f : A ⟶ A) :
    P.trace f = ∑ i ∈ Finset.Icc P.lower P.upper, i.negOnePow •
      LinearMap.trace k ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).obj A)
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map f).hom := by
  obtain ⟨g, rfl⟩ := P.exists_chainMap f
  rw [P.trace_map, boundedComplexTrace_eq_sum_homology]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_homology_map]

end PerfectComplexModel

/-- The intrinsic perfect-complex trace equals the alternating sum of
the actual derived cohomology traces over a field. -/
theorem perfectComplexTrace_eq_finsum_homology (hA : IsPerfectComplex k A) (f : A ⟶ A) :
    perfectComplexTrace k A hA f = ∑ᶠ i : ℤ, i.negOnePow •
      LinearMap.trace k ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).obj A)
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map f).hom :=
  (Classical.choice hA).trace_eq_finsum_homology f

end EtaleCohomology
