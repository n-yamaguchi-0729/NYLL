/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.HomologicalAlgebra.ExactDerivedFunctorPlus
public import Nyll.SchemeTheory.HomologicalAlgebra.InjectiveResolutionExtended
public import Nyll.SchemeTheory.HomologicalAlgebra.InjectiveResolutionMap
public import Nyll.SchemeTheory.HomologicalAlgebra.InjectiveResolutionMapExtended
public import Nyll.SchemeTheory.HomologicalAlgebra.MapExtendUpNat
public import Nyll.SchemeTheory.HomologicalAlgebra.RightDerivedFunctorPlusResolution
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Exact-functor transport of native derived resolution comparisons

The original augmentation and native derived units determine the comparison
on a transported injective resolution. Their actual naturality squares give
the resulting resolution map, without an assumed resolution comparison.
-/

@[expose] public section

noncomputable section

universe wC wD wE

open CategoryTheory Limits Abelian

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wE} E]

private def singleLocalizationIso (A : C) :
    DerivedCategory.Plus.Q.obj
      (⟨(CochainComplex.singleFunctor C 0).obj A, 0, inferInstance⟩ : CochainComplex.Plus C) ≅
        (DerivedCategory.Plus.singleFunctor C 0).obj A :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.Plus.QCompιIso C).app
        (⟨(CochainComplex.singleFunctor C 0).obj A, 0, inferInstance⟩ :
          CochainComplex.Plus C) ≪≫
      ((DerivedCategory.Plus.singleFunctorιIso C 0).app A).symm)

private def resolutionLocalizationIso {A : C} (I : InjectiveResolution A) :
    (DerivedCategory.Plus.singleFunctor C 0).obj A ≅
      DerivedCategory.Plus.Q.obj
        (⟨I.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩ :
          CochainComplex.Plus C) :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.Plus.singleFunctorιIso C 0).app A ≪≫
      asIso (DerivedCategory.Q.map I.extendedAugmentation) ≪≫
        ((DerivedCategory.Plus.QCompιIso C).app
          (⟨I.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩ :
            CochainComplex.Plus C)).symm)

private theorem resolutionLocalization_triangle {A : C} (I : InjectiveResolution A) :
    (singleLocalizationIso A).inv ≫
        DerivedCategory.Plus.Q.map (ObjectProperty.homMk I.extendedAugmentation :
          (⟨(CochainComplex.singleFunctor C 0).obj A, 0, inferInstance⟩ :
            CochainComplex.Plus C) ⟶
          ⟨I.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩) =
      (resolutionLocalizationIso I).hom := by
  let S : CochainComplex.Plus C :=
    ⟨(CochainComplex.singleFunctor C 0).obj A, 0, inferInstance⟩
  let K : CochainComplex.Plus C :=
    ⟨I.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
  let a : S ⟶ K := ObjectProperty.homMk I.extendedAugmentation
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, singleLocalizationIso, resolutionLocalizationIso,
    Functor.preimageIso_hom, Functor.preimageIso_inv, Functor.map_preimage,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, asIso_hom, Category.assoc]
  have h := (DerivedCategory.Plus.QCompιIso C).inv.naturality a
  exact congrArg (fun z => (DerivedCategory.Plus.singleFunctorιIso C 0).hom.app A ≫ z) h.symm

variable (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] [L.PreservesInjectiveObjects] [EnoughInjectives C]

private theorem derivedSingle_resolution [IsIso L.rightDerivedFunctorPlusUnit]
    {A : C} (I : InjectiveResolution A) :
    (L.rightDerivedFunctorPlusSingleIsoOfExact A).hom ≫
        (resolutionLocalizationIso (InjectiveResolution.mapExactPreservingInjectives L I)).hom =
      L.rightDerivedFunctorPlus.map (resolutionLocalizationIso I).hom ≫
        CategoryTheory.inv (L.rightDerivedFunctorPlusUnit.app
          (⟨I.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩ :
            CochainComplex.Plus C)) ≫
          DerivedCategory.Plus.Q.map
            (ObjectProperty.homMk (L.mapExtendUpNatIso I.cocomplex).hom :
              L.mapCochainComplexPlus.obj
                (⟨I.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩ :
                  CochainComplex.Plus C) ⟶
              ⟨(InjectiveResolution.mapExactPreservingInjectives L I).cocomplex.extend
                ComplexShape.embeddingUpNat, 0, inferInstance⟩) := by
  let J := InjectiveResolution.mapExactPreservingInjectives L I
  let S : CochainComplex.Plus C :=
    ⟨(CochainComplex.singleFunctor C 0).obj A, 0, inferInstance⟩
  let T : CochainComplex.Plus D :=
    ⟨(CochainComplex.singleFunctor D 0).obj (L.obj A), 0, inferInstance⟩
  let K : CochainComplex.Plus C :=
    ⟨I.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
  let M : CochainComplex.Plus D :=
    ⟨J.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
  let a : S ⟶ K := ObjectProperty.homMk I.extendedAugmentation
  let b : T ⟶ M := ObjectProperty.homMk J.extendedAugmentation
  let e0 : L.mapCochainComplexPlus.obj S ≅ T :=
    ObjectProperty.isoMk (CochainComplex.plus D)
      ((HomologicalComplex.singleMapHomologicalComplex L (ComplexShape.up ℤ) 0).app A)
  let eI : L.mapCochainComplexPlus.obj K ≅ M :=
    ObjectProperty.isoMk (CochainComplex.plus D) (L.mapExtendUpNatIso I.cocomplex)
  have hab : b = e0.inv ≫ L.mapCochainComplexPlus.map a ≫ eI.hom := by
    apply (CochainComplex.Plus.ι D).map_injective
    exact InjectiveResolution.mapExactPreservingInjectives_extendedAugmentation L I
  have hq := congrArg (DerivedCategory.Plus.Q (C := D)).map hab
  simp only [Functor.map_comp] at hq
  have hu : L.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map a) ≫
        CategoryTheory.inv (L.rightDerivedFunctorPlusUnit.app K) =
      CategoryTheory.inv (L.rightDerivedFunctorPlusUnit.app S) ≫
        DerivedCategory.Plus.Q.map (L.mapCochainComplexPlus.map a) := by
    have hn : CommSq
        (DerivedCategory.Plus.Q.map (L.mapCochainComplexPlus.map a))
        (asIso (L.rightDerivedFunctorPlusUnit.app S)).hom
        (asIso (L.rightDerivedFunctorPlusUnit.app K)).hom
        (L.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map a)) :=
      ⟨L.rightDerivedFunctorPlusUnit.naturality a⟩
    exact hn.vert_inv.w
  rw [← resolutionLocalization_triangle I, ← resolutionLocalization_triangle J]
  change (L.rightDerivedFunctorPlus.map (singleLocalizationIso A).inv ≫
      CategoryTheory.inv (L.rightDerivedFunctorPlusUnit.app S) ≫ DerivedCategory.Plus.Q.map e0.hom ≫
        (singleLocalizationIso (L.obj A)).hom) ≫
      ((singleLocalizationIso (L.obj A)).inv ≫ DerivedCategory.Plus.Q.map b) =
    L.rightDerivedFunctorPlus.map
        ((singleLocalizationIso A).inv ≫ DerivedCategory.Plus.Q.map a) ≫
      CategoryTheory.inv (L.rightDerivedFunctorPlusUnit.app K) ≫ DerivedCategory.Plus.Q.map eI.hom
  have hcancel : DerivedCategory.Plus.Q.map e0.hom ≫
      DerivedCategory.Plus.Q.map e0.inv = 𝟙 _ :=
    (DerivedCategory.Plus.Q.mapIso e0).hom_inv_id
  have hu' := congrArg (fun z => z ≫ DerivedCategory.Plus.Q.map eI.hom) hu.symm
  simp only [Category.assoc] at hu'
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [hq, ← Category.assoc (DerivedCategory.Plus.Q.map e0.hom)
    (DerivedCategory.Plus.Q.map e0.inv), hcancel, Category.id_comp, hu']

private theorem derivedComparison_algebra
    {B : Type*} [Category B]
    {X₀ X₁ Y₀ Y₁ QI QL Z ZJ QJ : B}
    (v : X₀ ⟶ X₁) (w : Y₀ ⟶ Y₁) (δ₀ : X₀ ⟶ Y₀) (δ₁ : X₁ ⟶ Y₁)
    (uI : QI ≅ X₁) (θ : QI ⟶ QL) (r : QL ⟶ Z) (uL : Z ≅ Y₁)
    (q : Z ⟶ ZJ) (e : QL ⟶ QJ) (uJ : QJ ≅ ZJ)
    (hδ : v ≫ δ₁ = δ₀ ≫ w)
    (hunit : uI.hom ≫ δ₁ = θ ≫ r ≫ uL.hom)
    (he : e ≫ uJ.hom = r ≫ q) :
    δ₀ ≫ w ≫ uL.inv ≫ q ≫ uJ.inv = v ≫ uI.inv ≫ θ ≫ e := by
  have hd : δ₁ = uI.inv ≫ θ ≫ r ≫ uL.hom := by
    calc
      δ₁ = uI.inv ≫ (uI.hom ≫ δ₁) := (uI.inv_hom_id_assoc δ₁).symm
      _ = _ := by rw [hunit]
  have hr : r ≫ q ≫ uJ.inv = e := by
    rw [← Category.assoc, ← he, Category.assoc, uJ.hom_inv_id, Category.comp_id]
  calc
    δ₀ ≫ w ≫ uL.inv ≫ q ≫ uJ.inv = v ≫ δ₁ ≫ uL.inv ≫ q ≫ uJ.inv := by
      rw [← Category.assoc δ₀ w, ← hδ]
      simp only [Category.assoc]
    _ = v ≫ uI.inv ≫ θ ≫ r ≫ q ≫ uJ.inv := by
      rw [hd]
      simp only [Category.assoc, uL.hom_inv_id_assoc]
    _ = v ≫ uI.inv ≫ θ ≫ e := by rw [hr]

variable (GY : C ⥤ E) (GX : D ⥤ E) [GY.Additive] [GX.Additive]
  [EnoughInjectives D]

/-- The native derived transformation, with its actual unit factorization,
retains the original resolution map after an exact functor preserving injectives. -/
theorem rightDerivedFunctorPlusIso_mapExactPreservingInjectives
    (θ : GY.mapCochainComplexPlus ⟶ L.mapCochainComplexPlus ⋙ GX.mapCochainComplexPlus)
    (δ : GY.rightDerivedFunctorPlus ⟶ L.rightDerivedFunctorPlus ⋙ GX.rightDerivedFunctorPlus)
    (hδ : ∀ K : CochainComplex.Plus C,
      GY.rightDerivedFunctorPlusUnit.app K ≫ δ.app (DerivedCategory.Plus.Q.obj K) =
        DerivedCategory.Plus.Q.map (θ.app K) ≫
          GX.rightDerivedFunctorPlusUnit.app (L.mapCochainComplexPlus.obj K) ≫
            GX.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlusUnit.app K))
    {A : C} (I : InjectiveResolution A) :
    DerivedCategory.Plus.ι.map
        (δ.app ((DerivedCategory.Plus.singleFunctor C 0).obj A) ≫
          GX.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlusSingleIsoOfExact A).hom) ≫
      ((InjectiveResolution.mapExactPreservingInjectives L I).rightDerivedFunctorPlusIso GX).hom =
    (I.rightDerivedFunctorPlusIso GY).hom ≫
      DerivedCategory.Q.map
        ((θ.app (⟨I.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩ :
            CochainComplex.Plus C)).hom ≫
          (GX.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (L.mapExtendUpNatIso I.cocomplex).hom) := by
  have : IsIso L.rightDerivedFunctorPlusUnit := L.rightDerivedFunctorPlusUnit_isIso_of_exact
  let J := InjectiveResolution.mapExactPreservingInjectives L I
  let K : CochainComplex.Plus C :=
    ⟨I.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
  let M : CochainComplex.Plus D :=
    ⟨J.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
  let eI : L.mapCochainComplexPlus.obj K ≅ M :=
    ObjectProperty.isoMk (CochainComplex.plus D) (L.mapExtendUpNatIso I.cocomplex)
  have : ∀ n : ℤ, Injective (K.obj.X n) := fun _ => inferInstance
  have : ∀ n : ℤ, Injective (M.obj.X n) := fun _ => inferInstance
  have : IsIso (GY.rightDerivedFunctorPlusUnit.app K) :=
    GY.rightDerivedFunctorPlusUnit_isIso_of_injective K
  have : IsIso (GX.rightDerivedFunctorPlusUnit.app M) :=
    GX.rightDerivedFunctorPlusUnit_isIso_of_injective M
  let uI := asIso (GY.rightDerivedFunctorPlusUnit.app K)
  let uJ := asIso (GX.rightDerivedFunctorPlusUnit.app M)
  let uL := GX.rightDerivedFunctorPlus.mapIso (asIso (L.rightDerivedFunctorPlusUnit.app K))
  let vI := (resolutionLocalizationIso I).hom
  let vJ := (resolutionLocalizationIso J).hom
  let sL := (L.rightDerivedFunctorPlusSingleIsoOfExact A).hom
  let ψ : GY.mapCochainComplexPlus.obj K ⟶ GX.mapCochainComplexPlus.obj M :=
    θ.app K ≫ GX.mapCochainComplexPlus.map eI.hom
  have hlambda : GX.rightDerivedFunctorPlus.map sL ≫ GX.rightDerivedFunctorPlus.map vJ =
      GX.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlus.map vI) ≫
        uL.inv ≫ GX.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map eI.hom) := by
    have h := congrArg GX.rightDerivedFunctorPlus.map (derivedSingle_resolution L I)
    change GX.rightDerivedFunctorPlus.map sL ≫ GX.rightDerivedFunctorPlus.map vJ =
      GX.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlus.map vI) ≫
        GX.rightDerivedFunctorPlus.map (CategoryTheory.inv (L.rightDerivedFunctorPlusUnit.app K)) ≫
          GX.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map eI.hom)
    change GX.rightDerivedFunctorPlus.map (sL ≫ vJ) =
      GX.rightDerivedFunctorPlus.map
        (L.rightDerivedFunctorPlus.map vI ≫
          CategoryTheory.inv (L.rightDerivedFunctorPlusUnit.app K) ≫
            DerivedCategory.Plus.Q.map eI.hom) at h
    exact (GX.rightDerivedFunctorPlus.map_comp sL vJ).symm.trans
      (h.trans ((GX.rightDerivedFunctorPlus.map_comp _ _).trans
        (congrArg (fun z => GX.rightDerivedFunctorPlus.map
          (L.rightDerivedFunctorPlus.map vI) ≫ z)
            (GX.rightDerivedFunctorPlus.map_comp _ _))))
  have hm := derivedComparison_algebra
    (GY.rightDerivedFunctorPlus.map vI)
    (GX.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlus.map vI))
    (δ.app ((DerivedCategory.Plus.singleFunctor C 0).obj A))
    (δ.app (DerivedCategory.Plus.Q.obj K))
    uI (DerivedCategory.Plus.Q.map (θ.app K))
    (GX.rightDerivedFunctorPlusUnit.app (L.mapCochainComplexPlus.obj K)) uL
    (GX.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map eI.hom))
    (DerivedCategory.Plus.Q.map (GX.mapCochainComplexPlus.map eI.hom)) uJ
    (δ.naturality vI) (hδ K) (GX.rightDerivedFunctorPlusUnit.naturality eI.hom)
  have hmiddle :
      (δ.app ((DerivedCategory.Plus.singleFunctor C 0).obj A) ≫
        GX.rightDerivedFunctorPlus.map sL) ≫
          (GX.rightDerivedFunctorPlus.map vJ ≫ uJ.inv) =
      (GY.rightDerivedFunctorPlus.map vI ≫ uI.inv) ≫ DerivedCategory.Plus.Q.map ψ := by
    rw [Category.assoc, ← Category.assoc (GX.rightDerivedFunctorPlus.map sL), hlambda]
    simpa only [ψ, Functor.map_comp, Category.assoc] using hm
  have hmiddle' := congrArg DerivedCategory.Plus.ι.map hmiddle
  simp only [Functor.map_comp] at hmiddle'
  have hq := (DerivedCategory.Plus.QCompιIso E).hom.naturality ψ
  change DerivedCategory.Plus.ι.map
      (δ.app ((DerivedCategory.Plus.singleFunctor C 0).obj A) ≫
        GX.rightDerivedFunctorPlus.map sL) ≫
      (DerivedCategory.Plus.ι.map (GX.rightDerivedFunctorPlus.map vJ ≫ uJ.inv) ≫
        (DerivedCategory.Plus.QCompιIso E).hom.app (GX.mapCochainComplexPlus.obj M)) =
    (DerivedCategory.Plus.ι.map (GY.rightDerivedFunctorPlus.map vI ≫ uI.inv) ≫
        (DerivedCategory.Plus.QCompιIso E).hom.app (GY.mapCochainComplexPlus.obj K)) ≫
      DerivedCategory.Q.map ψ.hom
  simp only [Functor.map_comp, Category.assoc] at hmiddle' ⊢
  have h1 := congrArg (fun z => z ≫
    (DerivedCategory.Plus.QCompιIso E).hom.app (GX.mapCochainComplexPlus.obj M)) hmiddle'
  have h2 := congrArg (fun z => DerivedCategory.Plus.ι.map
    (GY.rightDerivedFunctorPlus.map vI) ≫ DerivedCategory.Plus.ι.map uI.inv ≫ z) hq
  simp only [Category.assoc, Functor.comp_map] at h1 h2
  exact h1.trans h2

end CategoryTheory.Functor
