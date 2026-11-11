/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.HomologicalAlgebra.ExtInjectiveResolution
public import Nyll.SchemeTheory.HomologicalAlgebra.HomComplexMap
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# The actual derived-Hom comparison under exact functors

The native Hom-complex map agrees with the map of derived morphisms from the
existing exact functor. The proof uses actual cocycle representatives and the
existing localization comparison, including its compatibility with shifts.
-/

@[expose] public section

noncomputable section

universe v uC uD

open CategoryTheory Limits CochainComplex HomComplex

namespace CategoryTheory.Abelian

variable {C : Type uC} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- On an actual cocycle, the original derived-Hom comparison is localization
of its actual shifted chain map. -/
theorem derivedHomComplexHomologyEquiv_symm_mk
    (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) (z : Cocycle K L n) :
    (derivedHomComplexHomologyEquiv K L n).symm
        ((homologyAddEquiv K L n).symm (CohomologyClass.mk z)) =
      ShiftedHom.map (a := n) (Cocycle.equivHomShift.symm z) DerivedCategory.Q := by
  let eK := (DerivedCategory.quotientCompQhIso C).app K
  let eL := (DerivedCategory.quotientCompQhIso C).app (L⟦n⟧)
  let t : K ⟶ L⟦n⟧ := Cocycle.equivHomShift.symm z
  change eK.inv ≫ DerivedCategory.Qh.map
      (CohomologyClass.toHom
        (homologyAddEquiv K L n ((homologyAddEquiv K L n).symm
          (CohomologyClass.mk z)))) ≫
      eL.hom ≫ ((DerivedCategory.Q (C := C)).commShiftIso n).hom.app L = _
  rw [AddEquiv.apply_symm_apply, CohomologyClass.toHom_mk]
  have h : DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map t) ≫ eL.hom =
      eK.hom ≫ DerivedCategory.Q.map t :=
    (DerivedCategory.quotientCompQhIso C).hom.naturality t
  calc
    eK.inv ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map t) ≫
        eL.hom ≫ ((DerivedCategory.Q (C := C)).commShiftIso n).hom.app L =
      eK.inv ≫ (DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map t) ≫
        eL.hom) ≫ ((DerivedCategory.Q (C := C)).commShiftIso n).hom.app L := by
          rw [Category.assoc]
    _ = eK.inv ≫ (eK.hom ≫ DerivedCategory.Q.map t) ≫
        ((DerivedCategory.Q (C := C)).commShiftIso n).hom.app L := by rw [h]
    _ = ShiftedHom.map (a := n) t DerivedCategory.Q := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc, ShiftedHom.map]

variable {D : Type uD} [Category.{v} D] [Abelian D] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The native Hom-complex map induced by an exact functor and an actual
source map agrees with the original map of derived morphisms. -/
theorem derivedHomComplexHomologyEquiv_symm_mapPrecomp
    (K L : CochainComplex C ℤ) [L.IsKInjective]
    [CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)]
    (K' : CochainComplex D ℤ)
    (a : K' ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (n : ℤ) (z : (HomComplex K L).homology n) :
    (derivedHomComplexHomologyEquiv K'
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n).symm
      (HomologicalComplex.homologyMap (mapPrecomp F a) n z) =
      DerivedCategory.Q.map a ≫ (F.mapDerivedCategoryFactors.inv.app K) ≫
        ShiftedHom.map (a := n) ((derivedHomComplexHomologyEquiv K L n).symm z)
          F.mapDerivedCategory ≫
        (F.mapDerivedCategoryFactors.hom.app L)⟦n⟧' := by
  obtain ⟨c, hc⟩ := CohomologyClass.mk_surjective (homologyAddEquiv K L n z)
  have hz : z = (homologyAddEquiv K L n).symm (CohomologyClass.mk c) :=
    (homologyAddEquiv K L n).injective (by rw [AddEquiv.apply_symm_apply, hc])
  have hmap : HomologicalComplex.homologyMap (mapPrecomp F a) n z =
      (homologyAddEquiv K' ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n).symm
        (CohomologyClass.mk ((cocycleMap F c).precomp a)) := by
    apply (homologyAddEquiv K' ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n).injective
    rw [homologyAddEquiv_mapPrecomp, ← hc, cohomologyClassMapPrecomp_mk,
      AddEquiv.apply_symm_apply]
  rw [hmap, derivedHomComplexHomologyEquiv_symm_mk, hz,
    derivedHomComplexHomologyEquiv_symm_mk, Cocycle.equivHomShift_symm_precomp,
    equivHomShift_symm_cocycleMap]
  let t : K ⟶ L⟦n⟧ := Cocycle.equivHomShift.symm c
  have h := ShiftedHom.map_naturality_1 (a := n) t F.mapDerivedCategoryFactors
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ShiftedHom.comp_map] at h
  have ha :
      ShiftedHom.map (a := n)
        (a ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map t ≫
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app L)
        DerivedCategory.Q =
      DerivedCategory.Q.map a ≫
        ShiftedHom.map (a := n)
          (ShiftedHom.map (a := n) t (F.mapHomologicalComplex (ComplexShape.up ℤ)))
          DerivedCategory.Q := by
    simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]
  apply ha.trans
  simpa only [Category.assoc] using
    (congrArg (fun b => DerivedCategory.Q.map a ≫ b) h.symm)

end CategoryTheory.Abelian
