/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.HomologicalAlgebra.InjectiveResolutionExtended
public import Nyll.SchemeTheory.HomologicalAlgebra.InjectiveResolutionMap
public import Nyll.SchemeTheory.HomologicalAlgebra.MapExtendUpNat

/-!
# Mapping the original extended augmentation

The augmentation of an injective resolution transported by an exact functor
agrees with the original mapped augmentation, through the canonical single
and zero-extension comparisons. The equality follows from the actual
degree-zero components of these maps.
-/

@[expose] public section

noncomputable section

universe uC vC uD vD

open CategoryTheory Limits

namespace CategoryTheory.InjectiveResolution

private theorem extendedAugmentation_f_zero
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {A : C} (I : InjectiveResolution A) :
    I.extendedAugmentation.f (0 : ℤ) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A).inv ≫
          I.ι.f 0 ≫ (I.cocomplex.extendXIso ComplexShape.embeddingUpNat
            embeddingUpNat_zero).inv := by
  change (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat A 0 0
      embeddingUpNat_zero).inv.f 0 ≫
    (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat).f 0 = _
  rw [HomologicalComplex.extendSingleIso_inv_f
      ComplexShape.embeddingUpNat A 0 0 embeddingUpNat_zero,
    HomologicalComplex.extendMap_f I.ι ComplexShape.embeddingUpNat embeddingUpNat_zero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (L : C ⥤ D) [L.Additive] [L.PreservesHomology] [L.PreservesInjectiveObjects]

/-- The actual mapped injective resolution has the mapped original
extended augmentation, through the canonical single and extension maps. -/
theorem mapExactPreservingInjectives_extendedAugmentation
    {A : C} (I : InjectiveResolution A) :
    (mapExactPreservingInjectives L I).extendedAugmentation =
      (HomologicalComplex.singleMapHomologicalComplex L (ComplexShape.up ℤ) 0).inv.app A ≫
        (L.mapHomologicalComplex (ComplexShape.up ℤ)).map I.extendedAugmentation ≫
          (L.mapExtendUpNatIso I.cocomplex).hom := by
  let J := mapExactPreservingInjectives L I
  let aN := HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A
  let aZ := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A
  let bN := HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.obj A)
  let bZ := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (L.obj A)
  let K : CochainComplex D ℕ :=
    (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let eI := I.cocomplex.extendXIso ComplexShape.embeddingUpNat embeddingUpNat_zero
  let eJ := K.extendXIso ComplexShape.embeddingUpNat embeddingUpNat_zero
  have hAugJ : J.extendedAugmentation.f (0 : ℤ) =
      bZ.hom ≫ bN.inv ≫ ((bN.hom ≫ L.map aN.inv) ≫ L.map (I.ι.f 0)) ≫ eJ.inv := by
    have hBase : J.extendedAugmentation.f (0 : ℤ) =
        bZ.hom ≫ bN.inv ≫ J.ι.f 0 ≫ eJ.inv := extendedAugmentation_f_zero J
    apply hBase.trans
    change bZ.hom ≫ bN.inv ≫
        (((HomologicalComplex.singleMapHomologicalComplex L
          (ComplexShape.up ℕ) 0).inv.app A).f 0 ≫ L.map (I.ι.f 0)) ≫ eJ.inv = _
    rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self L
      (ComplexShape.up ℕ) 0 A]
  have hAugI : I.extendedAugmentation.f (0 : ℤ) =
      aZ.hom ≫ aN.inv ≫ I.ι.f 0 ≫ eI.inv := extendedAugmentation_f_zero I
  have hSingle : ((HomologicalComplex.singleMapHomologicalComplex L
      (ComplexShape.up ℤ) 0).inv.app A).f 0 = bZ.hom ≫ L.map aZ.inv :=
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self L (ComplexShape.up ℤ) 0 A
  have hExtend : (L.mapExtendUpNatIso I.cocomplex).hom.f (0 : ℤ) =
      L.map eI.hom ≫ eJ.inv :=
    L.mapExtendUpNatIso_hom_f_ofNat I.cocomplex 0
  have hcancelI : L.map eI.inv ≫ L.map eI.hom ≫ eJ.inv = eJ.inv := by
    rw [← L.map_comp_assoc, eI.inv_hom_id, L.map_id, Category.id_comp]
  have hcancelZ : L.map aZ.inv ≫ L.map aZ.hom ≫
      L.map aN.inv ≫ L.map (I.ι.f 0) ≫ eJ.inv =
        L.map aN.inv ≫ L.map (I.ι.f 0) ≫ eJ.inv := by
    rw [← L.map_comp_assoc, aZ.inv_hom_id, L.map_id, Category.id_comp]
  apply HomologicalComplex.from_single_hom_ext
  change J.extendedAugmentation.f (0 : ℤ) =
    ((HomologicalComplex.singleMapHomologicalComplex L
      (ComplexShape.up ℤ) 0).inv.app A).f 0 ≫
      L.map (I.extendedAugmentation.f (0 : ℤ)) ≫
        (L.mapExtendUpNatIso I.cocomplex).hom.f (0 : ℤ)
  rw [hAugJ, hSingle, hAugI, hExtend]
  simp only [Functor.map_comp, Category.assoc, bN.inv_hom_id_assoc, hcancelI, hcancelZ]
  rfl

end CategoryTheory.InjectiveResolution
