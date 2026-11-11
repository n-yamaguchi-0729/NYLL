/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.HomologicalAlgebra.InjectiveResolutionExtended
public import Nyll.SchemeTheory.HomologicalAlgebra.RightDerivedFunctorPlusResolution
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Naturality of the native derived-functor resolution comparison

The existing comparison is constructed from the original augmentation and
the native derived unit. Their actual naturality squares show that it retains
the original coefficient map and its existing lifted resolution map.
-/

@[expose] public section

noncomputable section

universe uC vC wC uD vD wD

open CategoryTheory Limits

namespace CategoryTheory.InjectiveResolution

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- The native bounded-below derived comparison commutes with the original
coefficient morphism and every compatible actual lifted resolution map. -/
theorem rightDerivedFunctorPlusIso_naturality {A B : C} (f : A ⟶ B)
    (I : InjectiveResolution A) (J : InjectiveResolution B)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι ≫ φ = (CochainComplex.single₀ C).map f ≫ J.ι) :
    DerivedCategory.Plus.ι.map
        (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f)) ≫
      (J.rightDerivedFunctorPlusIso F).hom =
    (I.rightDerivedFunctorPlusIso F).hom ≫
      DerivedCategory.Q.map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)) := by
  let LI : CochainComplex.Plus C :=
    ⟨I.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
  let LJ : CochainComplex.Plus C :=
    ⟨J.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
  let ψ : LI ⟶ LJ := ObjectProperty.homMk
    (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
  let eI : (DerivedCategory.Plus.singleFunctor C 0).obj A ≅
      DerivedCategory.Plus.Q.obj LI :=
    DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.Plus.singleFunctorιIso C 0).app A ≪≫
        asIso (DerivedCategory.Q.map I.extendedAugmentation) ≪≫
        ((DerivedCategory.Plus.QCompιIso C).app LI).symm)
  let eJ : (DerivedCategory.Plus.singleFunctor C 0).obj B ≅
      DerivedCategory.Plus.Q.obj LJ :=
    DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.Plus.singleFunctorιIso C 0).app B ≪≫
        asIso (DerivedCategory.Q.map J.extendedAugmentation) ≪≫
        ((DerivedCategory.Plus.QCompιIso C).app LJ).symm)
  have he : (DerivedCategory.Plus.singleFunctor C 0).map f ≫ eJ.hom =
      eI.hom ≫ DerivedCategory.Plus.Q.map ψ := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.map_comp, eI, eJ, Functor.preimageIso_hom,
      Functor.map_preimage, Iso.trans_hom, Iso.symm_hom, asIso_hom]
    let qφ := DerivedCategory.Q.map ((CochainComplex.Plus.ι C).map ψ)
    have hs : CommSq
        (DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.singleFunctor C 0).map f))
        ((DerivedCategory.Plus.singleFunctorιIso C 0).hom.app A)
        ((DerivedCategory.Plus.singleFunctorιIso C 0).hom.app B)
        ((DerivedCategory.singleFunctor C 0).map f) :=
      ⟨(DerivedCategory.Plus.singleFunctorιIso C 0).hom.naturality f⟩
    have ha : CommSq ((DerivedCategory.singleFunctor C 0).map f)
        (DerivedCategory.Q.map I.extendedAugmentation)
        (DerivedCategory.Q.map J.extendedAugmentation) qφ := by
      have h := congrArg DerivedCategory.Q.map
        (extendedAugmentation_naturality f I J φ hφ)
      simp only [Functor.map_comp] at h
      exact ⟨h.symm⟩
    have hq : CommSq qφ ((DerivedCategory.Plus.QCompιIso C).inv.app LI)
        ((DerivedCategory.Plus.QCompιIso C).inv.app LJ)
        (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map ψ)) :=
      ⟨(DerivedCategory.Plus.QCompιIso C).inv.naturality ψ⟩
    exact (hs.vert_comp (ha.vert_comp hq)).w
  have : ∀ n : ℤ, Injective (LI.obj.X n) := fun _ => inferInstance
  have : ∀ n : ℤ, Injective (LJ.obj.X n) := fun _ => inferInstance
  have : IsIso (F.rightDerivedFunctorPlusUnit.app LI) :=
    F.rightDerivedFunctorPlusUnit_isIso_of_injective LI
  have : IsIso (F.rightDerivedFunctorPlusUnit.app LJ) :=
    F.rightDerivedFunctorPlusUnit_isIso_of_injective LJ
  let uI := asIso (F.rightDerivedFunctorPlusUnit.app LI)
  let uJ := asIso (F.rightDerivedFunctorPlusUnit.app LJ)
  have hu : F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ) ≫ uJ.inv =
      uI.inv ≫ DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map ψ) := by
    have hn : CommSq (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map ψ))
        uI.hom uJ.hom (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) :=
      ⟨F.rightDerivedFunctorPlusUnit.naturality ψ⟩
    exact hn.vert_inv.w
  have he' := congrArg F.rightDerivedFunctorPlus.map he
  simp only [Functor.map_comp] at he'
  have hmiddle : F.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor C 0).map f) ≫
        (F.rightDerivedFunctorPlus.map eJ.hom ≫ uJ.inv) =
      (F.rightDerivedFunctorPlus.map eI.hom ≫ uI.inv) ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map ψ) := by
    rw [← Category.assoc, he', Category.assoc, hu, ← Category.assoc]
  have hmiddle' := congrArg DerivedCategory.Plus.ι.map hmiddle
  simp only [Functor.map_comp] at hmiddle'
  have hq := (DerivedCategory.Plus.QCompιIso D).hom.naturality
    (F.mapCochainComplexPlus.map ψ)
  change DerivedCategory.Plus.ι.map
      (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f)) ≫
      (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlus.map eJ.hom ≫ uJ.inv) ≫
        (DerivedCategory.Plus.QCompιIso D).hom.app (F.mapCochainComplexPlus.obj LJ)) =
    (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlus.map eI.hom ≫ uI.inv) ≫
        (DerivedCategory.Plus.QCompιIso D).hom.app (F.mapCochainComplexPlus.obj LI)) ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ.hom)
  simp only [Functor.map_comp, Category.assoc] at hmiddle' ⊢
  have h1 := congrArg (fun z => z ≫
    (DerivedCategory.Plus.QCompιIso D).hom.app (F.mapCochainComplexPlus.obj LJ)) hmiddle'
  have h2 := congrArg (fun z => DerivedCategory.Plus.ι.map
    (F.rightDerivedFunctorPlus.map eI.hom) ≫ DerivedCategory.Plus.ι.map uI.inv ≫ z) hq
  simp only [Category.assoc, Functor.comp_map] at h1 h2
  exact h1.trans h2

/-- The existing canonical resolution lift gives naturality of the native
derived comparison without requiring a supplied compatibility square. -/
theorem rightDerivedFunctorPlusIso_desc_naturality {A B : C} (f : A ⟶ B)
    (I : InjectiveResolution A) (J : InjectiveResolution B) :
    DerivedCategory.Plus.ι.map
        (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f)) ≫
      (J.rightDerivedFunctorPlusIso F).hom =
    (I.rightDerivedFunctorPlusIso F).hom ≫
      DerivedCategory.Q.map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap (desc f J I) ComplexShape.embeddingUpNat)) :=
  rightDerivedFunctorPlusIso_naturality F f I J (desc f J I) (desc_commutes f J I)

/-- The homology comparison retains the original coefficient map and the
actual lifted map between the two given resolutions. -/
theorem rightDerivedFunctorPlusHomologyIso_naturality {A B : C} (f : A ⟶ B)
    (I : InjectiveResolution A) (J : InjectiveResolution B)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι ≫ φ = (CochainComplex.single₀ C).map f ≫ J.ι) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D n).map
        (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f)) ≫
      (J.rightDerivedFunctorPlusHomologyIso F n).hom =
    (I.rightDerivedFunctorPlusHomologyIso F n).hom ≫
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)) n := by
  let ψ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
  have h := congrArg ((DerivedCategory.homologyFunctor D n).map)
    (rightDerivedFunctorPlusIso_naturality F f I J φ hφ)
  simp only [Functor.map_comp] at h
  have hs : CommSq ((DerivedCategory.homologyFunctor D n).map
      (DerivedCategory.Plus.ι.map
        (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f))))
      ((DerivedCategory.homologyFunctor D n).map (I.rightDerivedFunctorPlusIso F).hom)
      ((DerivedCategory.homologyFunctor D n).map (J.rightDerivedFunctorPlusIso F).hom)
      ((DerivedCategory.homologyFunctor D n).map (DerivedCategory.Q.map ψ)) := ⟨h⟩
  have hn : CommSq
      ((DerivedCategory.homologyFunctor D n).map (DerivedCategory.Q.map ψ))
      ((DerivedCategory.homologyFunctorFactors D n).hom.app _)
      ((DerivedCategory.homologyFunctorFactors D n).hom.app _)
      ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n).map ψ) :=
    ⟨(DerivedCategory.homologyFunctorFactors D n).hom.naturality ψ⟩
  exact (hs.vert_comp hn).w

/-- Naturality of native derived homology uses the existing canonical
resolution lift of the original coefficient morphism. -/
theorem rightDerivedFunctorPlusHomologyIso_desc_naturality {A B : C} (f : A ⟶ B)
    (I : InjectiveResolution A) (J : InjectiveResolution B) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D n).map
        (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f)) ≫
      (J.rightDerivedFunctorPlusHomologyIso F n).hom =
    (I.rightDerivedFunctorPlusHomologyIso F n).hom ≫
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap (desc f J I) ComplexShape.embeddingUpNat)) n :=
  rightDerivedFunctorPlusHomologyIso_naturality F f I J
    (desc f J I) (desc_commutes f J I) n

end CategoryTheory.InjectiveResolution
