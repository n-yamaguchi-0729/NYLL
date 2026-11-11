/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.HomologicalAlgebra.HomFromSingleSectionsMap
public import Nyll.SchemeTheory.HomologicalAlgebra.RightDerivedFunctorPlusMapResolution
public import Nyll.SchemeTheory.CategoryTheory.ModuleEndomorphismPowers
public import Nyll.EtaleCohomology.Classical.ModuleDerivedPullback
public import Nyll.EtaleCohomology.Classical.ModuleExtPullback
public import Nyll.EtaleCohomology.Classical.ModuleGlobalSectionsComplex
public import Nyll.EtaleCohomology.Classical.ModuleInjectiveResolution
public import Nyll.EtaleCohomology.Classical.ModulePullbackSections
public import Nyll.EtaleCohomology.Classical.CoefficientEndomorphism
public import Nyll.SchemeTheory.HomologicalAlgebra.ExtInjectiveResolutionMap
public import Nyll.SchemeTheory.HomologicalAlgebra.InjectiveResolutionMapExtended
public import Nyll.SchemeTheory.HomologicalAlgebra.RightDerivedFunctorPlusResolutionNaturality
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Endomorphism

public import Nyll.EtaleCohomology.Classical.DerivedGlobalSections
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Classical.ModuleExtCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Nyll.EtaleCohomology.Sites.PullbackStalks
public import Nyll.SchemeTheory.HomologicalAlgebra.HomFromSingle
public import Nyll.SchemeTheory.HomologicalAlgebra.InjectiveResolutionExtended
public import Nyll.SchemeTheory.HomologicalAlgebra.InjectiveResolutionMap
public import Nyll.SchemeTheory.HomologicalAlgebra.MapExtendUpNat
public import Nyll.SchemeTheory.HomologicalAlgebra.RightDerivedFunctorPlusResolution
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Native derived pullback computes the original cohomological pullback

The actual source morphism for module Ext acts degreewise on the original
Hom complex. Its established section formula identifies this action with
the original section transformation. Transporting an injective resolution
therefore computes the same map in every degree. The native derived units
retain that actual resolution map; no comparison square is an assumption
of the scheme-level results.
-/

@[expose] public section

noncomputable section

universe u wX wY wR

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]
  [(etalePullback f R).PreservesInjectiveObjects]

/-- Apply the actual global-section pullback to the original extended
resolution and then the canonical zero-extension comparison. -/
def etaleModulePullbackResolutionSectionsMap
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)} (I : InjectiveResolution F) :
    (((sheafSections Y.smallEtaleTopology (ModuleCat.{u} R)).obj
      (op (⊤_ Y.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (I.cocomplex.extend ComplexShape.embeddingUpNat) ⟶
    (((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((InjectiveResolution.mapExactPreservingInjectives (etalePullback f R) I).cocomplex.extend
          ComplexShape.embeddingUpNat) :=
  (NatTrans.mapHomologicalComplex (etaleModuleGlobalSectionsPullback R f)
    (ComplexShape.up ℤ)).app (I.cocomplex.extend ComplexShape.embeddingUpNat) ≫
      (((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
        (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((etalePullback f R).mapExtendUpNatIso I.cocomplex).hom

/-- The actual source morphism of module Ext and the original section map
give the same map of Hom-resolution complexes. -/
theorem etaleModuleHomFromIntegerSectionsIso_pullback_resolution
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)} (I : InjectiveResolution F) :
    homFromSingleResolutionMap (etalePullback f R) (etaleModuleFreeIntegerPullbackHom f R) I ≫
      (etaleModuleHomFromIntegerSectionsIso X R).hom.app
        ((InjectiveResolution.mapExactPreservingInjectives (etalePullback f R) I).cocomplex.extend
          ComplexShape.embeddingUpNat) =
    (etaleModuleHomFromIntegerSectionsIso Y R).hom.app
        (I.cocomplex.extend ComplexShape.embeddingUpNat) ≫
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (etaleModulePullbackResolutionSectionsMap f R I) := by
  refine CategoryTheory.homFromSingleSectionsIso_postcomp (etalePullback f R)
    ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ Y.Etale)))
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ X.Etale)))
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})
    (etaleModuleFreeIntegerPullbackHom f R)
    (etaleModuleIntegerHomSectionsIso Y R) (etaleModuleIntegerHomSectionsIso X R)
    (etaleModuleGlobalSectionsPullback R f) ?_
    (I.cocomplex.extend ComplexShape.embeddingUpNat)
    ((InjectiveResolution.mapExactPreservingInjectives (etalePullback f R) I).cocomplex.extend
      ComplexShape.embeddingUpNat)
    ((etalePullback f R).mapExtendUpNatIso I.cocomplex).hom
  intro G a
  apply ULift.ext
  exact etaleModuleIntegerHomSectionsIso_pullback R f G a

/-- The original Hom-to-sections homology comparison retains the actual
pullback of the given resolution. -/
theorem etaleModuleHomologyFromIntegerSectionsIso_pullback_resolution
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)} (I : InjectiveResolution F)
    (n : ℤ) :
    HomologicalComplex.homologyMap
        (homFromSingleResolutionMap (etalePullback f R)
          (etaleModuleFreeIntegerPullbackHom f R) I) n ≫
      (etaleModuleHomologyFromIntegerSectionsIso X R n).hom.app
        ((InjectiveResolution.mapExactPreservingInjectives (etalePullback f R) I).cocomplex.extend
          ComplexShape.embeddingUpNat) =
    (etaleModuleHomologyFromIntegerSectionsIso Y R n).hom.app
        (I.cocomplex.extend ComplexShape.embeddingUpNat) ≫
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).map
          (HomologicalComplex.homologyMap (etaleModulePullbackResolutionSectionsMap f R I) n) := by
  let V := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}
  let K := I.cocomplex.extend ComplexShape.embeddingUpNat
  let J := InjectiveResolution.mapExactPreservingInjectives (etalePullback f R) I
  let M := J.cocomplex.extend ComplexShape.embeddingUpNat
  let P := (((sheafSections Y.smallEtaleTopology (ModuleCat.{u} R)).obj
    (op (⊤_ Y.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let Q := (((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
    (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).obj M
  let eP : (homFromSingleFunctor (etaleFreeIntegerModuleSheaf Y R)).obj K ≅
      (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P :=
    (etaleModuleHomFromIntegerSectionsIso Y R).app K
  let eQ : (homFromSingleFunctor (etaleFreeIntegerModuleSheaf X R)).obj M ≅
      (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q :=
    (etaleModuleHomFromIntegerSectionsIso X R).app M
  let a := homFromSingleResolutionMap (etalePullback f R)
    (etaleModuleFreeIntegerPullbackHom f R) I
  let s := etaleModulePullbackResolutionSectionsMap f R I
  simp only [etaleModuleHomologyFromIntegerSectionsIso_hom_app]
  exact CategoryTheory.homologyMap_square_of_chain_square V a s eP eQ
    (etaleModuleHomFromIntegerSectionsIso_pullback_resolution f R I) n

/-- Mapping the original module Ext class and then comparing with the
transported resolution agrees in every degree with actual section pullback. -/
theorem etaleModuleExtInjectiveResolutionEquiv_pullback
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) (I : InjectiveResolution F)
    (n : ℕ) (x : Ext.{u} (etaleFreeIntegerModuleSheaf Y R) F n) :
    etaleModuleExtInjectiveResolutionEquiv X R ((etalePullback f R).obj F)
        (InjectiveResolution.mapExactPreservingInjectives (etalePullback f R) I) n
        ((Ext.mk₀ (etaleModuleFreeIntegerPullbackHom f R)).comp
          (x.mapExactFunctor (etalePullback f R)) (zero_add n)) =
      HomologicalComplex.homologyMap (etaleModulePullbackResolutionSectionsMap f R I) (n : ℤ)
        (etaleModuleExtInjectiveResolutionEquiv Y R F I n x) := by
  let : HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
    HasDerivedCategory.standard _
  let A := etaleFreeIntegerModuleSheaf Y R
  let B := etaleFreeIntegerModuleSheaf X R
  let J := InjectiveResolution.mapExactPreservingInjectives (etalePullback f R) I
  let z := extResolutionHomologyEquiv A I n x
  let e := etaleModuleHomologyFromIntegerSectionsIso X R (n : ℤ)
  have hx := extResolutionHomologyEquiv_mapExactFunctor (etalePullback f R)
    (etaleModuleFreeIntegerPullbackHom f R) I n x
  have hn := etaleModuleHomologyFromIntegerSectionsIso_pullback_resolution f R I (n : ℤ)
  change ULift.down ((e.app _).hom
    (extResolutionHomologyEquiv B J n
      ((Ext.mk₀ (etaleModuleFreeIntegerPullbackHom f R)).comp
        (x.mapExactFunctor (etalePullback f R)) (zero_add n)))) = _
  rw [hx]
  exact congrArg ULift.down (ConcreteCategory.congr_hom hn z)

/-- Classical pullback is computed on the original module resolution and
its actual transported injective resolution, in every degree. -/
theorem etaleCohomologyModuleInjectiveResolutionLinearEquiv_pullback
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) (I : InjectiveResolution F)
    (n : ℕ) (x : etaleCohomology Y R F n) :
    etaleCohomologyModuleInjectiveResolutionLinearEquiv X R ((etalePullback f R).obj F)
        (InjectiveResolution.mapExactPreservingInjectives (etalePullback f R) I) n
        (etaleCohomologyPullbackMap f R F n x) =
      HomologicalComplex.homologyMap (etaleModulePullbackResolutionSectionsMap f R I) (n : ℤ)
        (etaleCohomologyModuleInjectiveResolutionLinearEquiv Y R F I n x) := by
  let eY := etaleModuleExtCohomologyEquiv Y R F n
  let eX := etaleModuleExtCohomologyEquiv X R ((etalePullback f R).obj F) n
  let z := eY.symm x
  let y := (Ext.mk₀ (etaleModuleFreeIntegerPullbackHom f R)).comp
    (z.mapExactFunctor (etalePullback f R)) (zero_add n)
  have hy : eX y = etaleCohomologyPullbackMap f R F n x :=
    (etaleModuleExtCohomologyMap_pullback f R F n z).trans
      (congrArg (etaleCohomologyPullbackMap f R F n) (eY.apply_symm_apply x))
  change etaleModuleExtInjectiveResolutionEquiv X R ((etalePullback f R).obj F)
    (InjectiveResolution.mapExactPreservingInjectives (etalePullback f R) I) n
    (eX.symm (etaleCohomologyPullbackMap f R F n x)) = _
  rw [← hy, LinearEquiv.symm_apply_apply]
  exact etaleModuleExtInjectiveResolutionEquiv_pullback f R F I n z



variable
  [HasDerivedCategory.{wY} (Sheaf Y.smallEtaleTopology (ModuleCat.{u} R))]
  [HasDerivedCategory.{wX} (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- The native derived pullback retains the actual section map of the
original resolution and the actual mapped injective resolution. -/
theorem etaleModuleDerivedGlobalSectionsResolutionIso_pullback
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) (I : InjectiveResolution F) :
    DerivedCategory.Plus.ι.map (etaleModuleDerivedGlobalSectionsPullbackSheaf f R F) ≫
      (etaleModuleDerivedGlobalSectionsResolutionIso X R ((etalePullback f R).obj F)
        (InjectiveResolution.mapExactPreservingInjectives (etalePullback f R) I)).hom =
    (etaleModuleDerivedGlobalSectionsResolutionIso Y R F I).hom ≫
      DerivedCategory.Q.map (etaleModulePullbackResolutionSectionsMap f R I) :=
  CategoryTheory.Functor.rightDerivedFunctorPlusIso_mapExactPreservingInjectives (etalePullback f R)
    ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ Y.Etale)))
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ X.Etale)))
    (etaleModuleGlobalSectionsPullbackComplex f R)
    (etaleModuleDerivedGlobalSectionsPullback f R)
    (etaleModuleDerivedGlobalSectionsPullback_unit f R) I

/-- Taking actual homology of the native derived pullback gives the original
pullback of the section complexes of the given resolutions. -/
theorem etaleModuleDerivedGlobalSectionsHomologyIso_pullback
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) (I : InjectiveResolution F) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
        (etaleModuleDerivedGlobalSectionsPullbackSheaf f R F) ≫
      (etaleModuleDerivedGlobalSectionsHomologyIso X R ((etalePullback f R).obj F)
        (InjectiveResolution.mapExactPreservingInjectives (etalePullback f R) I) n).hom =
    (etaleModuleDerivedGlobalSectionsHomologyIso Y R F I n).hom ≫
      HomologicalComplex.homologyMap (etaleModulePullbackResolutionSectionsMap f R I) n := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) n
  let s := etaleModulePullbackResolutionSectionsMap f R I
  have h := congrArg H.map (etaleModuleDerivedGlobalSectionsResolutionIso_pullback f R F I)
  simp only [Functor.map_comp] at h
  have hs : CommSq
      (H.map (DerivedCategory.Plus.ι.map (etaleModuleDerivedGlobalSectionsPullbackSheaf f R F)))
      (H.map (etaleModuleDerivedGlobalSectionsResolutionIso Y R F I).hom)
      (H.map (etaleModuleDerivedGlobalSectionsResolutionIso X R ((etalePullback f R).obj F)
        (InjectiveResolution.mapExactPreservingInjectives (etalePullback f R) I)).hom)
      (H.map (DerivedCategory.Q.map s)) := ⟨h⟩
  have hn : CommSq (H.map (DerivedCategory.Q.map s))
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).hom.app _)
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).hom.app _)
      (HomologicalComplex.homologyMap s n) :=
    ⟨(DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).hom.naturality s⟩
  exact (hs.vert_comp hn).w

private theorem classicalDerived_resolution
    {Z : Scheme.{u}} [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} R))]
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R)) (I : InjectiveResolution F)
    (n : ℕ) (x : etaleCohomology Z R F n) :
    (etaleModuleDerivedGlobalSectionsHomologyIso Z R F I (n : ℤ)).hom
        (etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv Z R F n x) =
      etaleCohomologyModuleInjectiveResolutionLinearEquiv Z R F I n x := by
  let J := injectiveResolution F
  let Γ := (sheafSections Z.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ Z.Etale))
  let eJ := (etaleModuleDerivedGlobalSectionsHomologyIso Z R F J (n : ℤ)).toLinearEquiv
  let eI := (etaleModuleDerivedGlobalSectionsHomologyIso Z R F I (n : ℤ)).toLinearEquiv
  let y := etaleCohomologyModuleInjectiveResolutionLinearEquiv Z R F J n x
  let s := (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (HomologicalComplex.extendMap (InjectiveResolution.desc (𝟙 F) I J)
      ComplexShape.embeddingUpNat)
  let l := HomologicalComplex.homologyMap s (n : ℤ)
  have hn := InjectiveResolution.rightDerivedFunctorPlusHomologyIso_desc_naturality
    Γ (𝟙 F) J I (n : ℤ)
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  have hv : eI (eJ.symm y) = l y := by
    have h := ConcreteCategory.congr_hom hn (eJ.symm y)
    change eI (eJ.symm y) = l (eJ (eJ.symm y)) at h
    exact h.trans (congrArg l (eJ.apply_symm_apply y))
  have hid : Classical.cohomologyMap (𝟙 F) n x = x := by
    change Sheaf.H.map
      ((Classical.forgetCoefficients.{u + 1, u, u, u}
        (J := Z.smallEtaleTopology) (R := R)).map (𝟙 F)) n x = x
    rw [CategoryTheory.Functor.map_id]
    exact Sheaf.H.map_id_apply
      (show Sheaf.H ((Classical.forgetCoefficients.{u + 1, u, u, u}
        (J := Z.smallEtaleTopology) (R := R)).obj F) n from x)
  have hc := etaleCohomologyModuleInjectiveResolutionLinearEquiv_naturality
    Z R (𝟙 F) J I n x
  rw [hid] at hc
  exact hv.trans hc.symm

/-- The original all-degree classical pullback is the actual homology map
of native derived global sections. The only extra functorial condition is
preservation of injective objects, supplied in particular by an equivalence. -/
theorem etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv_pullback
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ)
    (x : etaleCohomology Y R F n) :
    etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv X R ((etalePullback f R).obj F) n
        (etaleCohomologyPullbackMap f R F n x) =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (etaleModuleDerivedGlobalSectionsPullbackSheaf f R F)
        (etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv Y R F n x) := by
  let I := injectiveResolution F
  let J := InjectiveResolution.mapExactPreservingInjectives (etalePullback f R) I
  let eJ := (etaleModuleDerivedGlobalSectionsHomologyIso X R
    ((etalePullback f R).obj F) J (n : ℤ)).toLinearEquiv
  let y := etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv Y R F n x
  have hn := ConcreteCategory.congr_hom
    (etaleModuleDerivedGlobalSectionsHomologyIso_pullback f R F I (n : ℤ)) y
  have hY := classicalDerived_resolution R F I n x
  have hX := classicalDerived_resolution R ((etalePullback f R).obj F) J n
    (etaleCohomologyPullbackMap f R F n x)
  have hc := etaleCohomologyModuleInjectiveResolutionLinearEquiv_pullback f R F I n x
  apply eJ.injective
  exact hX.trans (hc.trans ((congrArg
    (HomologicalComplex.homologyMap (etaleModulePullbackResolutionSectionsMap f R I) (n : ℤ))
      hY.symm).trans hn.symm))

/-- The same actual comparison includes the original coefficient morphism,
so it applies to the existing Frobenius coefficient action. -/
theorem etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv_pullback_coefficient
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (c : (etalePullback f R).obj F ⟶ G) (n : ℕ)
    (x : etaleCohomology Y R F n) :
    etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv X R G n
        (Classical.cohomologyMap c n (etaleCohomologyPullbackMap f R F n x)) =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (etaleModuleDerivedGlobalSectionsPullbackSheaf f R F ≫
          (etaleModuleDerivedGlobalSections X R).map
            ((DerivedCategory.Plus.singleFunctor _ 0).map c))
        (etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv Y R F n x) := by
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)
  let a := etaleModuleDerivedGlobalSectionsPullbackSheaf f R F
  let b := (etaleModuleDerivedGlobalSections X R).map
    ((DerivedCategory.Plus.singleFunctor _ 0).map c)
  let y := etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv Y R F n x
  have hp := etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv_pullback f R F n x
  have hc := etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv_naturality X R c n
    (etaleCohomologyPullbackMap f R F n x)
  have hm : H.map (a ≫ b) y = H.map b (H.map a y) :=
    ConcreteCategory.congr_hom (H.map_comp a b) y
  exact hc.trans ((congrArg (H.map b) hp).trans hm.symm)

section CoefficientEndomorphism

variable {W : Scheme.{u}} (g : W ⟶ W)
  [HasDerivedCategory.{wX} (Sheaf W.smallEtaleTopology (ModuleCat.{u} R))]
  (F : Sheaf W.smallEtaleTopology (ModuleCat.{u} R))
  (c : (etalePullback g R).obj F ⟶ F)

/-- The original scheme endomorphism and coefficient morphism act on native
module-derived global sections through actual derived pullback. -/
def etaleCoefficientModuleDerivedEndomorphism :
    End ((etaleModuleDerivedGlobalSections W R).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  End.of (etaleModuleDerivedGlobalSectionsPullbackSheaf g R F ≫
    (etaleModuleDerivedGlobalSections W R).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map c))

variable [(etalePullback g R).PreservesInjectiveObjects]

/-- The native coefficient endomorphism acts on actual homology as the
original classical coefficient endomorphism in every degree. -/
theorem etaleCoefficientModuleDerivedEndomorphism_cohomology
    (n : ℕ) (x : etaleCohomology W R F n) :
    etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv W R F n
        (etaleCoefficientCohomologyEndomorphism g R F c n x) =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (etaleCoefficientModuleDerivedEndomorphism (R := R) (g := g) F c).asHom
        (etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv W R F n x) :=
  etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv_pullback_coefficient
    g R F F c n x

/-- All powers retain the same native-derived and original classical
coefficient actions. -/
theorem etaleCoefficientModuleDerivedEndomorphism_cohomology_pow
    (n m : ℕ) (x : etaleCohomology W R F n) :
    etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv W R F n
        (((etaleCoefficientCohomologyEndomorphism g R F c n) ^ m) x) =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        ((etaleCoefficientModuleDerivedEndomorphism (R := R) (g := g) F c) ^ m).asHom
        (etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv W R F n x) := by
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)
  let a := etaleCoefficientCohomologyEndomorphism g R F c n
  let b := etaleCoefficientModuleDerivedEndomorphism (R := R) (g := g) F c
  let e := etaleCohomologyModuleDerivedGlobalSectionsLinearEquiv W R F n
  have hs (y : etaleCohomology W R F n) : e (a y) = H.map b.asHom (e y) :=
    etaleCoefficientModuleDerivedEndomorphism_cohomology (R := R) (g := g) F c n y
  exact CategoryTheory.Functor.moduleAction_semiconj_pow H a b (fun y => e y) hs m x

end CoefficientEndomorphism

end EtaleCohomology
