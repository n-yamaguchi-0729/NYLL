/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The native bounded below derived functor of an exact functor

These original constructions use inversion of quasi-isomorphisms and the
native derived unit. The single-object comparison retains the actual
single-complex and localization comparisons.
-/

@[expose] public section

noncomputable section

universe wC wD

open CategoryTheory Limits

namespace CategoryTheory.Functor

/-- Exactness makes every component of the native right-derived unit invertible. -/
theorem rightDerivedFunctorPlusUnit_isIso_of_exact
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D] [EnoughInjectives C]
    (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] :
    IsIso L.rightDerivedFunctorPlusUnit := by
  have hL : (CochainComplex.Plus.quasiIso C).IsInvertedBy
      (L.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) := by
    intro K K' a ha
    have : QuasiIso a.hom := ha
    have : QuasiIso (L.mapCochainComplexPlus.map a).hom :=
      inferInstanceAs (QuasiIso ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map a.hom))
    exact Localization.inverts (DerivedCategory.Plus.Q (C := D))
      (CochainComplex.Plus.quasiIso D) (L.mapCochainComplexPlus.map a)
      (inferInstanceAs (QuasiIso (L.mapCochainComplexPlus.map a).hom))
  exact Functor.isIso_of_isRightDerivedFunctor_of_inverts
    L.rightDerivedFunctorPlus L.rightDerivedFunctorPlusUnit hL

/-- The native right-derived functor of an exact functor sends the degree-zero
object to the degree-zero image, through its original unit. -/
def rightDerivedFunctorPlusSingleIsoOfExact
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D] [EnoughInjectives C]
    (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (A : C) :
    L.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj A) ≅
      (DerivedCategory.Plus.singleFunctor D 0).obj (L.obj A) := by
  let S : CochainComplex.Plus C :=
    ⟨(CochainComplex.singleFunctor C 0).obj A, 0, inferInstance⟩
  let T : CochainComplex.Plus D :=
    ⟨(CochainComplex.singleFunctor D 0).obj (L.obj A), 0, inferInstance⟩
  let eS : DerivedCategory.Plus.Q.obj S ≅
      (DerivedCategory.Plus.singleFunctor C 0).obj A :=
    DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.Plus.QCompιIso C).app S ≪≫
        ((DerivedCategory.Plus.singleFunctorιIso C 0).app A).symm)
  let eT : DerivedCategory.Plus.Q.obj T ≅
      (DerivedCategory.Plus.singleFunctor D 0).obj (L.obj A) :=
    DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.Plus.QCompιIso D).app T ≪≫
        ((DerivedCategory.Plus.singleFunctorιIso D 0).app (L.obj A)).symm)
  let eL : L.mapCochainComplexPlus.obj S ≅ T :=
    ObjectProperty.isoMk (CochainComplex.plus D)
      ((HomologicalComplex.singleMapHomologicalComplex L (ComplexShape.up ℤ) 0).app A)
  have : IsIso L.rightDerivedFunctorPlusUnit := L.rightDerivedFunctorPlusUnit_isIso_of_exact
  exact L.rightDerivedFunctorPlus.mapIso eS.symm ≪≫
    (asIso (L.rightDerivedFunctorPlusUnit.app S)).symm ≪≫
    DerivedCategory.Plus.Q.mapIso eL ≪≫ eT

end CategoryTheory.Functor
