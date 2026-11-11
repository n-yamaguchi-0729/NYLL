/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ModuleExtInjectiveResolution
public import Nyll.EtaleCohomology.Classical.ModuleExtCohomology
public import Nyll.SchemeTheory.HomologicalAlgebra.HomologicalComplexLinear
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Linearity of the original module injective-resolution comparison

The actual resolution naturality and linear global-sections functor identify
the original scalar actions and preserve the original coefficient map.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- The original resolution comparison is linear for the native scalar
structures on module Ext and on module-complex homology. -/
def etaleModuleExtInjectiveResolutionLinearEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (I : InjectiveResolution F) (n : ℕ) :
    Ext.{u} (etaleFreeIntegerModuleSheaf X R) F n ≃ₗ[R]
      ((((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
        (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) where
  toAddEquiv := etaleModuleExtInjectiveResolutionEquiv X R F I n
  map_smul' r x := by
    change etaleModuleExtInjectiveResolutionEquiv X R F I n (r • x) =
      r • etaleModuleExtInjectiveResolutionEquiv X R F I n x
    let Γ := (sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ X.Etale))
    let L := I.cocomplex.extend ComplexShape.embeddingUpNat
    have hφ : I.extendedAugmentation ≫ (r • 𝟙 L) =
        (CochainComplex.singleFunctor _ 0).map (r • 𝟙 F) ≫ I.extendedAugmentation := by
      rw [Functor.map_smul, CategoryTheory.Functor.map_id, CategoryTheory.Linear.comp_smul,
        Category.comp_id, CategoryTheory.Linear.smul_comp, Category.id_comp]
    have hx := etaleModuleExtInjectiveResolutionEquiv_naturality X R
      (r • 𝟙 F) I I (r • 𝟙 L) hφ n x
    refine (congrArg (etaleModuleExtInjectiveResolutionEquiv X R F I n)
      (Ext.smul_eq_comp_mk₀ x r)).trans (hx.trans ?_)
    let G : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) ℤ ⥤
        ModuleCat.{u} R :=
      Γ.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) (n : ℤ)
    have hsmul : G.map (r • 𝟙 L) = r • 𝟙 (G.obj L) :=
      (CategoryTheory.Functor.linear_iff R G).mp
        (inferInstance : CategoryTheory.Functor.Linear R G) L r
    exact ConcreteCategory.congr_hom hsmul
      (show G.obj L from etaleModuleExtInjectiveResolutionEquiv X R F I n x)

/-- Classical cohomology is computed linearly by the original native
module injective-resolution complex. -/
def etaleCohomologyModuleInjectiveResolutionLinearEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (I : InjectiveResolution F) (n : ℕ) :
    etaleCohomology X R F n ≃ₗ[R]
      ((((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
        (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) :=
  (etaleModuleExtCohomologyEquiv X R F n).symm.trans
    (etaleModuleExtInjectiveResolutionLinearEquiv X R F I n)

/-- The linear classical-resolution comparison preserves the original
coefficient map through its actual canonical resolution lift. -/
theorem etaleCohomologyModuleInjectiveResolutionLinearEquiv_naturality
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (n : ℕ) (x : etaleCohomology X R F n) :
    etaleCohomologyModuleInjectiveResolutionLinearEquiv X R G J n
        (Classical.cohomologyMap f n x) =
      HomologicalComplex.homologyMap
        ((((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
          (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.extendMap (InjectiveResolution.desc f J I)
              ComplexShape.embeddingUpNat)) (n : ℤ)
        (etaleCohomologyModuleInjectiveResolutionLinearEquiv X R F I n x) := by
  let eF := etaleModuleExtCohomologyEquiv X R F n
  let eG := etaleModuleExtCohomologyEquiv X R G n
  have h : eG ((eF.symm x).comp (Ext.mk₀ f) (add_zero n)) =
      Classical.cohomologyMap f n x := by
    have h' := etaleModuleExtCohomologyEquiv_naturality X R f n (eF.symm x)
    exact h'.trans (congrArg (Classical.cohomologyMap f n) (eF.apply_symm_apply x))
  change etaleModuleExtInjectiveResolutionEquiv X R G J n
    (eG.symm (Classical.cohomologyMap f n x)) = _
  rw [← h, LinearEquiv.symm_apply_apply]
  exact etaleModuleExtInjectiveResolutionEquiv_desc_naturality X R f I J n (eF.symm x)

end EtaleCohomology
