/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.DerivedGlobalSections
public import Nyll.EtaleCohomology.Classical.ModulePullbackSections
public import Nyll.SchemeTheory.HomologicalAlgebra.ExactDerivedFunctorPlus
public import Nyll.EtaleCohomology.Sites.PullbackStalks
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.Single
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Whiskering

/-!
# Native derived pullback of module global sections

The original section transformation and the native right-derived units give
a comparison by the universal property of the right-derived functor. Exactness
of étale pullback makes its own derived unit invertible. Thus the comparison
also gives an actual morphism between derived global sections of a coefficient
sheaf and of its pullback. No cohomological comparison square is assumed.
-/

@[expose] public section

noncomputable section

universe u wC wD wE wX wY wR

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

section Generic

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  (L : C ⥤ D) (GY : C ⥤ E) (GX : D ⥤ E)
  [L.Additive] [GY.Additive] [GX.Additive]

/-- Apply a section transformation term by term to bounded below complexes. -/
def sectionMapOnPlus (θ : GY ⟶ L ⋙ GX) :
    GY.mapCochainComplexPlus ⟶ L.mapCochainComplexPlus ⋙ GX.mapCochainComplexPlus where
  app K := ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app K.obj)
  naturality K K' a := by
    apply (CochainComplex.Plus.ι E).map_injective
    exact (NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).naturality a.hom

variable [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  [HasDerivedCategory.{wE} E] [EnoughInjectives C] [EnoughInjectives D]

/-- Compose the section transformation with the two native derived units. -/
def sectionDerivedUnit (θ : GY ⟶ L ⋙ GX) :
    GY.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ (L.rightDerivedFunctorPlus ⋙ GX.rightDerivedFunctorPlus) :=
  Functor.whiskerRight (sectionMapOnPlus L GY GX θ) DerivedCategory.Plus.Q ≫
    (Functor.associator L.mapCochainComplexPlus GX.mapCochainComplexPlus
      DerivedCategory.Plus.Q).hom ≫
    Functor.whiskerLeft L.mapCochainComplexPlus GX.rightDerivedFunctorPlusUnit ≫
    (Functor.associator L.mapCochainComplexPlus DerivedCategory.Plus.Q
      GX.rightDerivedFunctorPlus).inv ≫
    Functor.whiskerRight L.rightDerivedFunctorPlusUnit GX.rightDerivedFunctorPlus ≫
    (Functor.associator DerivedCategory.Plus.Q L.rightDerivedFunctorPlus
      GX.rightDerivedFunctorPlus).hom

/-- The comparison induced by the universal property of the right-derived functor. -/
def sectionDerivedComparison (θ : GY ⟶ L ⋙ GX) :
    GY.rightDerivedFunctorPlus ⟶ L.rightDerivedFunctorPlus ⋙ GX.rightDerivedFunctorPlus :=
  GY.rightDerivedFunctorPlus.rightDerivedDesc GY.rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso C)
    (L.rightDerivedFunctorPlus ⋙ GX.rightDerivedFunctorPlus)
    (sectionDerivedUnit L GY GX θ)

private theorem sectionDerivedComparison_unit (θ : GY ⟶ L ⋙ GX)
    (K : CochainComplex.Plus C) :
    GY.rightDerivedFunctorPlusUnit.app K ≫
        (sectionDerivedComparison L GY GX θ).app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ((sectionMapOnPlus L GY GX θ).app K) ≫
        GX.rightDerivedFunctorPlusUnit.app (L.mapCochainComplexPlus.obj K) ≫
          GX.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlusUnit.app K) := by
  refine (GY.rightDerivedFunctorPlus.rightDerived_fac_app GY.rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso C)
    (L.rightDerivedFunctorPlus ⋙ GX.rightDerivedFunctorPlus)
    (sectionDerivedUnit L GY GX θ) K).trans ?_
  simp only [sectionDerivedUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

end Generic

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]

/-- The actual section transformation applied term by term to bounded below
complexes. Its components retain the original pullback on sections. -/
def etaleModuleGlobalSectionsPullbackComplex :
    ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} R)).obj
        (op (⊤_ Y.Etale))).mapCochainComplexPlus ⟶
      (etalePullback f R).mapCochainComplexPlus ⋙
        ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
          (op (⊤_ X.Etale))).mapCochainComplexPlus :=
  sectionMapOnPlus (etalePullback f R)
    ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ Y.Etale)))
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ X.Etale)))
    (etaleModuleGlobalSectionsPullback R f)

variable
  [HasDerivedCategory.{wY} (Sheaf Y.smallEtaleTopology (ModuleCat.{u} R))]
  [HasDerivedCategory.{wX} (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- The original section transformation induces pullback of native module
right-derived global sections by their universal property. -/
def etaleModuleDerivedGlobalSectionsPullback :
    etaleModuleDerivedGlobalSections Y R ⟶
      (etalePullback f R).rightDerivedFunctorPlus ⋙ etaleModuleDerivedGlobalSections X R :=
  sectionDerivedComparison (etalePullback f R)
    ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ Y.Etale)))
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ X.Etale)))
    (etaleModuleGlobalSectionsPullback R f)

/-- The native derived pullback retains the actual termwise section map
through both original derived units. -/
theorem etaleModuleDerivedGlobalSectionsPullback_unit
    (K : CochainComplex.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u} R))) :
    ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} R)).obj
        (op (⊤_ Y.Etale))).rightDerivedFunctorPlusUnit.app K ≫
      (etaleModuleDerivedGlobalSectionsPullback f R).app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map ((etaleModuleGlobalSectionsPullbackComplex f R).app K) ≫
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
          (op (⊤_ X.Etale))).rightDerivedFunctorPlusUnit.app
        ((etalePullback f R).mapCochainComplexPlus.obj K) ≫
          (etaleModuleDerivedGlobalSections X R).map
            ((etalePullback f R).rightDerivedFunctorPlusUnit.app K) :=
  sectionDerivedComparison_unit (etalePullback f R)
    ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ Y.Etale)))
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ X.Etale)))
    (etaleModuleGlobalSectionsPullback R f) K

/-- Exactness identifies native derived pullback of a sheaf in degree zero
with its actual étale pullback in degree zero. -/
def etaleModulePullbackDerivedSingleIso
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) :
    (etalePullback f R).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj ((etalePullback f R).obj F) :=
  (etalePullback f R).rightDerivedFunctorPlusSingleIsoOfExact F

/-- Native derived global sections of the given sheaf map to native derived
global sections of its actual pullback. -/
def etaleModuleDerivedGlobalSectionsPullbackSheaf
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) :
    (etaleModuleDerivedGlobalSections Y R).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ⟶
      (etaleModuleDerivedGlobalSections X R).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj ((etalePullback f R).obj F)) :=
  (etaleModuleDerivedGlobalSectionsPullback f R).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (etaleModuleDerivedGlobalSections X R).map (etaleModulePullbackDerivedSingleIso f R F).hom

end EtaleCohomology
