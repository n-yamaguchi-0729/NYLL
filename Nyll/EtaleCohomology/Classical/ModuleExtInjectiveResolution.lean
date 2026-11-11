/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ModuleGlobalSectionsComplex
public import Nyll.EtaleCohomology.Classical.ModuleExtCohomology
public import Nyll.SchemeTheory.HomologicalAlgebra.ExtInjectiveResolution
public import Nyll.SchemeTheory.HomologicalAlgebra.HomFromSingle
public import Nyll.SchemeTheory.HomologicalAlgebra.InjectiveResolutionExtended
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-!
# Module Ext and its additive injective-resolution comparison

The original Hom-complex comparison and its actual resolution maps compute
module Ext and the underlying additive classical cohomology.
The declarations retain their original names, values and mathematical assumptions.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- Native module Ext is computed by the original global-sections complex
of the given module injective resolution. -/
def etaleModuleExtInjectiveResolutionEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (I : InjectiveResolution F) (n : ℕ) :
    Ext.{u} (etaleFreeIntegerModuleSheaf X R) F n ≃+
      ((((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
        (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) := by
  let C := Sheaf X.smallEtaleTopology (ModuleCat.{u} R)
  let : HasDerivedCategory C := HasDerivedCategory.standard C
  let L := I.cocomplex.extend ComplexShape.embeddingUpNat
  let eHom : Ext.{u} (etaleFreeIntegerModuleSheaf X R) F n ≃+
      (CochainComplex.HomComplex
        ((CochainComplex.singleFunctor C 0).obj (etaleFreeIntegerModuleSheaf X R))
        L).homology (n : ℤ) :=
    Abelian.extResolutionHomologyEquiv (etaleFreeIntegerModuleSheaf X R) I n
  let e := (etaleModuleHomologyFromIntegerSectionsIso X R (n : ℤ)).app L
  exact eHom.trans (e.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)

/-- The resolution comparison respects an actual extended chain map
commuting with the original augmentations. -/
theorem etaleModuleExtInjectiveResolutionEquiv_naturality
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex.extend ComplexShape.embeddingUpNat ⟶
      J.cocomplex.extend ComplexShape.embeddingUpNat)
    (hφ : I.extendedAugmentation ≫ φ =
      (CochainComplex.singleFunctor _ 0).map f ≫ J.extendedAugmentation)
    (n : ℕ) (x : Ext.{u} (etaleFreeIntegerModuleSheaf X R) F n) :
    etaleModuleExtInjectiveResolutionEquiv X R G J n
        (x.comp (Ext.mk₀ f) (add_zero n)) =
      HomologicalComplex.homologyMap
        ((((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
          (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) (n : ℤ)
        (etaleModuleExtInjectiveResolutionEquiv X R F I n x) := by
  let C := Sheaf X.smallEtaleTopology (ModuleCat.{u} R)
  let : HasDerivedCategory C := HasDerivedCategory.standard C
  let A := etaleFreeIntegerModuleSheaf X R
  let e := etaleModuleHomologyFromIntegerSectionsIso X R (n : ℤ)
  have hx := Abelian.extResolutionHomologyEquiv_naturality A f I J φ hφ n x
  change ULift.down ((e.app _).hom
      (Abelian.extResolutionHomologyEquiv A J n (x.comp (Ext.mk₀ f) (add_zero n)))) = _
  rw [hx]
  exact congrArg ULift.down (ConcreteCategory.congr_hom (e.hom.naturality φ)
    (Abelian.extResolutionHomologyEquiv A I n x))

/-- Canonical resolution lifts give naturality for the original coefficient
morphism, without a supplied comparison premise. -/
theorem etaleModuleExtInjectiveResolutionEquiv_desc_naturality
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (n : ℕ) (x : Ext.{u} (etaleFreeIntegerModuleSheaf X R) F n) :
    etaleModuleExtInjectiveResolutionEquiv X R G J n
        (x.comp (Ext.mk₀ f) (add_zero n)) =
      HomologicalComplex.homologyMap
        ((((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
          (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.extendMap (InjectiveResolution.desc f J I)
              ComplexShape.embeddingUpNat)) (n : ℤ)
        (etaleModuleExtInjectiveResolutionEquiv X R F I n x) :=
  etaleModuleExtInjectiveResolutionEquiv_naturality X R f I J
    (HomologicalComplex.extendMap (InjectiveResolution.desc f J I)
      ComplexShape.embeddingUpNat)
    (InjectiveResolution.extendedAugmentation_desc f I J) n x

/-- The underlying additive group of classical module cohomology is
computed by the original native module injective resolution. -/
def etaleCohomologyModuleInjectiveResolutionEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (I : InjectiveResolution F) (n : ℕ) :
    etaleCohomology X R F n ≃+
      ((((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
        (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) :=
  (etaleModuleExtCohomologyEquiv X R F n).symm.toAddEquiv.trans
    (etaleModuleExtInjectiveResolutionEquiv X R F I n)

end EtaleCohomology
