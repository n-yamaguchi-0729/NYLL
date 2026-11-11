/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.DerivedGlobalSections
public import Nyll.EtaleCohomology.Classical.ModuleLinearInjectiveResolution
public import Nyll.SchemeTheory.HomologicalAlgebra.RightDerivedFunctorPlusResolutionNaturality

/-!
# Classical module cohomology and native derived global sections

The original injective-resolution comparison computes native derived global
sections and intertwines its actual derived coefficient map.
-/

@[expose] public section

noncomputable section

universe u wS wM

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

variable
  [HasDerivedCategory.{wS} (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))]
  [HasDerivedCategory.{wM} (ModuleCat.{u} R)]

/-- Classical module cohomology and native module-derived global sections
have canonically equivalent underlying additive groups. -/
def etaleCohomologyModuleDerivedGlobalSectionsEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ) :
    etaleCohomology X R F n ≃+
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
        ((etaleModuleDerivedGlobalSections X R).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  (etaleCohomologyModuleInjectiveResolutionEquiv X R F (injectiveResolution F) n).trans
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapIso
      (etaleModuleDerivedGlobalSectionsHomologyIso X R F (injectiveResolution F) (n : ℤ)).symm
        ).addCommGroupIsoToAddEquiv

/-- The actual module-derived global-section homology and classical étale
cohomology are linearly equivalent in every nonnegative degree. -/
def etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ) :
    etaleCohomology X R F n ≃ₗ[R]
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
        ((etaleModuleDerivedGlobalSections X R).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  (etaleCohomologyModuleInjectiveResolutionLinearEquiv X R F (injectiveResolution F) n).trans
    ((etaleModuleDerivedGlobalSectionsHomologyIso X R F (injectiveResolution F)
      (n : ℤ)).symm.toLinearEquiv)

/-- The all-degree linear comparison intertwines the original classical
coefficient map with the original native derived-functor map. -/
theorem etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv_naturality
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (f : F ⟶ G)
    (n : ℕ) (x : etaleCohomology X R F n) :
    etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv X R G n
        (Classical.cohomologyMap f n x) =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        ((etaleModuleDerivedGlobalSections X R).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map f))
        (etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv X R F n x) := by
  let I := injectiveResolution F
  let J := injectiveResolution G
  let Γ := (sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ X.Etale))
  let eI := (etaleModuleDerivedGlobalSectionsHomologyIso X R F I (n : ℤ)).toLinearEquiv
  let eJ := (etaleModuleDerivedGlobalSectionsHomologyIso X R G J (n : ℤ)).toLinearEquiv
  let m := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
    ((etaleModuleDerivedGlobalSections X R).map ((DerivedCategory.Plus.singleFunctor _ 0).map f))
  let ψ := (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (HomologicalComplex.extendMap (InjectiveResolution.desc f J I) ComplexShape.embeddingUpNat)
  let l := HomologicalComplex.homologyMap ψ (n : ℤ)
  have h := InjectiveResolution.rightDerivedFunctorPlusHomologyIso_desc_naturality
    Γ f I J (n : ℤ)
  have hn : eJ (m (eI.symm
        (etaleCohomologyModuleInjectiveResolutionLinearEquiv X R F I n x))) =
      l (etaleCohomologyModuleInjectiveResolutionLinearEquiv X R F I n x) := by
    have h' := ConcreteCategory.congr_hom h
      (eI.symm (etaleCohomologyModuleInjectiveResolutionLinearEquiv X R F I n x))
    change eJ (m (eI.symm
        (etaleCohomologyModuleInjectiveResolutionLinearEquiv X R F I n x))) =
      l (eI (eI.symm (etaleCohomologyModuleInjectiveResolutionLinearEquiv X R F I n x))) at h'
    exact h'.trans (congrArg l (eI.apply_symm_apply _))
  apply eJ.injective
  change eJ (eJ.symm
      (etaleCohomologyModuleInjectiveResolutionLinearEquiv X R G J n
        (Classical.cohomologyMap f n x))) =
    eJ (m (eI.symm (etaleCohomologyModuleInjectiveResolutionLinearEquiv X R F I n x)))
  rw [LinearEquiv.apply_symm_apply]
  exact (etaleCohomologyModuleInjectiveResolutionLinearEquiv_naturality X R f I J n x).trans
    hn.symm

end EtaleCohomology
