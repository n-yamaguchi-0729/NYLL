/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.HomologicalAlgebra.DerivedHomComplexMap
public import Nyll.SchemeTheory.HomologicalAlgebra.HomFromSingle
public import Nyll.SchemeTheory.HomologicalAlgebra.ExtInjectiveResolution
public import Nyll.SchemeTheory.HomologicalAlgebra.HomFromSingleMap
public import Nyll.SchemeTheory.HomologicalAlgebra.InjectiveResolutionMapExtended
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Ext-resolution comparison for an exact functor

An exact functor preserving injectives transports the given resolution.
The actual Hom-complex map applies the original functor, precomposes with
the original source map, and uses the constructed zero-extension comparison.
It computes the original `Ext.mapExactFunctor` followed by `Ext.mk₀`.
-/

@[expose] public section

noncomputable section

universe w w' v uC uD

open CategoryTheory Limits CochainComplex HomComplex

namespace CategoryTheory.Abelian

variable {C : Type uC} [Category.{v} C] [Abelian C]
  {D : Type uD} [Category.{v} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesInjectiveObjects]
  {A X : C} {B : D} (u : B ⟶ F.obj A) (I : InjectiveResolution X)

/-- The actual map of resolution Hom complexes obtained by applying the
functor and precomposing with the given source morphism. -/
def homFromSingleResolutionMap :
    (homFromSingleFunctor A).obj (I.cocomplex.extend ComplexShape.embeddingUpNat) ⟶
      (homFromSingleFunctor B).obj
        ((InjectiveResolution.mapExactPreservingInjectives F I).cocomplex.extend
          ComplexShape.embeddingUpNat) :=
  homFromSingleMap F u (I.cocomplex.extend ComplexShape.embeddingUpNat) ≫
    (homFromSingleFunctor B).map (F.mapExtendUpNatIso I.cocomplex).hom

variable [HasDerivedCategory C] [HasDerivedCategory D] [HasExt.{w} C] [HasExt.{w'} D]

/-- The original Ext map is computed on the actual transported resolution
by the Hom-complex map `a ↦ u ≫ F.map a`, with its constructed extension iso.
There is no comparison or augmentation compatibility premise. -/
theorem extResolutionHomologyEquiv_mapExactFunctor (n : ℕ) (x : Ext.{w} A X n) :
    extResolutionHomologyEquiv B (InjectiveResolution.mapExactPreservingInjectives F I) n
        ((Ext.mk₀ u).comp (x.mapExactFunctor F) (zero_add n)) =
      HomologicalComplex.homologyMap (homFromSingleResolutionMap F u I) (n : ℤ)
        (extResolutionHomologyEquiv A I n x) := by
  let K : CochainComplex C ℤ := (CochainComplex.singleFunctor C 0).obj A
  let L : CochainComplex C ℤ := I.cocomplex.extend ComplexShape.embeddingUpNat
  let J : InjectiveResolution (F.obj X) := InjectiveResolution.mapExactPreservingInjectives F I
  let M : CochainComplex D ℤ := J.cocomplex.extend ComplexShape.embeddingUpNat
  let e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L ≅ M :=
    F.mapExtendUpNatIso I.cocomplex
  let a : (CochainComplex.singleFunctor D 0).obj B ⟶
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
    (CochainComplex.singleFunctor D 0).map u ≫
      (F.mapCochainComplexSingleFunctor 0).inv.app A
  have : M.IsKInjective := inferInstance
  have : CochainComplex.IsKInjective
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
    CochainComplex.isKInjective_of_iso e.symm
  let z : (HomComplex K L).homology (n : ℤ) := extResolutionHomologyEquiv A I n x
  have ha : DerivedCategory.Q.map a ≫ F.mapDerivedCategoryFactors.inv.app K =
      (DerivedCategory.singleFunctor D 0).map u ≫
        (F.mapDerivedCategorySingleFunctor 0).inv.app A := by
    let E := F.mapDerivedCategoryFactors.app K
    have hs : (F.mapDerivedCategorySingleFunctor 0).inv.app A ≫ E.hom =
        DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app A) :=
      F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app A
    have hc : DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app A) ≫
        E.inv = (F.mapDerivedCategorySingleFunctor 0).inv.app A := by
      rw [← hs, Category.assoc, E.hom_inv_id]
      exact Category.comp_id ((F.mapDerivedCategorySingleFunctor 0).inv.app A)
    calc
      DerivedCategory.Q.map a ≫ F.mapDerivedCategoryFactors.inv.app K =
        DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map u) ≫
          (DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app A) ≫
            E.inv) := by
              change DerivedCategory.Q.map
                  ((CochainComplex.singleFunctor D 0).map u ≫
                    (F.mapCochainComplexSingleFunctor 0).inv.app A) ≫ E.inv = _
              rw [Functor.map_comp, Category.assoc]
      _ = (DerivedCategory.singleFunctor D 0).map u ≫
          (F.mapDerivedCategorySingleFunctor 0).inv.app A :=
        congrArg (fun b => DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map u) ≫ b) hc
  have htarget :
      F.mapDerivedCategory.map (DerivedCategory.Q.map I.extendedAugmentation) ≫
          F.mapDerivedCategoryFactors.hom.app L ≫ DerivedCategory.Q.map e.hom =
        (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
          DerivedCategory.Q.map J.extendedAugmentation := by
    have hs : J.extendedAugmentation =
        (F.mapCochainComplexSingleFunctor 0).inv.app X ≫
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map I.extendedAugmentation ≫
            e.hom :=
      InjectiveResolution.mapExactPreservingInjectives_extendedAugmentation F I
    have hQ := congrArg (DerivedCategory.Q (C := D)).map hs
    simp only [Functor.map_comp] at hQ
    calc
      F.mapDerivedCategory.map (DerivedCategory.Q.map I.extendedAugmentation) ≫
          F.mapDerivedCategoryFactors.hom.app L ≫ DerivedCategory.Q.map e.hom =
        F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) ≫
          DerivedCategory.Q.map
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map I.extendedAugmentation) ≫
          DerivedCategory.Q.map e.hom := by
            rw [F.mapDerivedCategoryFactors_hom_naturality_assoc]
      _ = (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
          DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app X) ≫
          DerivedCategory.Q.map
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map I.extendedAugmentation) ≫
          DerivedCategory.Q.map e.hom := by
            rw [← F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app X]
            simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
      _ = (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
          DerivedCategory.Q.map J.extendedAugmentation :=
        congrArg (fun b => (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫ b) hQ.symm
  have hpost :
      ShiftedHom.map (a := (n : ℤ))
        (x.hom ≫ (DerivedCategory.Q.map I.extendedAugmentation)⟦(n : ℤ)⟧')
          F.mapDerivedCategory =
        x.hom.map F.mapDerivedCategory ≫
          (F.mapDerivedCategory.map (DerivedCategory.Q.map I.extendedAugmentation))⟦(n : ℤ)⟧' := by
    simpa only [ShiftedHom.comp_mk₀, ShiftedHom.map_mk₀] using
      ShiftedHom.map_comp x.hom
        (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Q.map I.extendedAugmentation))
        (zero_add (n : ℤ)) F.mapDerivedCategory
  have hcross := derivedHomComplexHomologyEquiv_symm_mapPrecomp F K L
    ((CochainComplex.singleFunctor D 0).obj B) a (n : ℤ) z
  have hpostcomp := derivedHomComplexHomologyEquiv_symm_naturality B e.hom (n : ℤ)
    (HomologicalComplex.homologyMap (mapPrecomp F a) (n : ℤ) z)
  apply (derivedHomComplexHomologyEquiv ((CochainComplex.singleFunctor D 0).obj B)
    M (n : ℤ)).symm.injective
  have hH : HomologicalComplex.homologyMap (homFromSingleResolutionMap F u I) (n : ℤ) z =
      HomologicalComplex.homologyMap ((homFromSingleFunctor B).map e.hom) (n : ℤ)
        (HomologicalComplex.homologyMap (mapPrecomp F a) (n : ℤ) z) := by
    let f : HomComplex K L ⟶
        HomComplex ((CochainComplex.singleFunctor D 0).obj B)
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := mapPrecomp F a
    let g : HomComplex ((CochainComplex.singleFunctor D 0).obj B)
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ⟶
        HomComplex ((CochainComplex.singleFunctor D 0).obj B) M :=
      (homFromSingleFunctor B).map e.hom
    have h : HomologicalComplex.homologyMap (f ≫ g) (n : ℤ) =
        HomologicalComplex.homologyMap f (n : ℤ) ≫
          HomologicalComplex.homologyMap g (n : ℤ) :=
      HomologicalComplex.homologyMap_comp f g (n : ℤ)
    exact ConcreteCategory.congr_hom h z
  rw [hH, hpostcomp, hcross, extResolutionHomologyEquiv_toDerived,
    extResolutionHomologyEquiv_toDerived, hpost]
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, Ext.mapExactFunctor_hom]
  have ht := congrArg ((CategoryTheory.shiftFunctor (DerivedCategory D) (n : ℤ)).map) htarget
  simp only [Functor.map_comp] at ht
  calc
    ((DerivedCategory.singleFunctor D 0).map u ≫
        (F.mapDerivedCategorySingleFunctor 0).inv.app A ≫
          x.hom.map F.mapDerivedCategory ≫
          ((F.mapDerivedCategorySingleFunctor 0).hom.app X)⟦(n : ℤ)⟧') ≫
        (DerivedCategory.Q.map J.extendedAugmentation)⟦(n : ℤ)⟧' =
      (DerivedCategory.singleFunctor D 0).map u ≫
        (F.mapDerivedCategorySingleFunctor 0).inv.app A ≫
        x.hom.map F.mapDerivedCategory ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app X)⟦(n : ℤ)⟧' ≫
        (DerivedCategory.Q.map J.extendedAugmentation)⟦(n : ℤ)⟧' := by
          simp only [Category.assoc]
    _ = (DerivedCategory.singleFunctor D 0).map u ≫
        (F.mapDerivedCategorySingleFunctor 0).inv.app A ≫
        x.hom.map F.mapDerivedCategory ≫
        (F.mapDerivedCategory.map (DerivedCategory.Q.map I.extendedAugmentation))⟦(n : ℤ)⟧' ≫
        (F.mapDerivedCategoryFactors.hom.app L)⟦(n : ℤ)⟧' ≫
        (DerivedCategory.Q.map e.hom)⟦(n : ℤ)⟧' := by
          rw [ht]
    _ = (DerivedCategory.Q.map a ≫ F.mapDerivedCategoryFactors.inv.app K ≫
          (x.hom.map F.mapDerivedCategory ≫
            (F.mapDerivedCategory.map (DerivedCategory.Q.map I.extendedAugmentation))⟦(n : ℤ)⟧') ≫
          (F.mapDerivedCategoryFactors.hom.app L)⟦(n : ℤ)⟧') ≫
        (DerivedCategory.Q.map e.hom)⟦(n : ℤ)⟧' := by
          simp only [Category.assoc]
          rw [← Category.assoc (DerivedCategory.Q.map a), ha]
          simp only [Category.assoc]

end CategoryTheory.Abelian
