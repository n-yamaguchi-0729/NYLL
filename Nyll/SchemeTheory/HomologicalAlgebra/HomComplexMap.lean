/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.LeftHomology

/-!
# Functorial maps of Hom complexes

An additive functor acts on cochains by the existing `Cochain.map`.
Precomposition by an actual map into the image of the source gives a chain
map. Its action on native homology is the induced map of cohomology classes.
-/

@[expose] public section

noncomputable section

universe v uC uD

open CategoryTheory Limits CochainComplex HomComplex

namespace CochainComplex.HomComplex

variable {C : Type uC} [Category.{v} C] [Preadditive C]
  {D : Type uD} [Category.{v} D] [Preadditive D]
  (F : C ⥤ D) [F.Additive]
  {K L : CochainComplex C ℤ} {K' : CochainComplex D ℤ}
  (a : K' ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

/-- Apply the original functor to a cochain and precompose with the given
actual chain map. -/
def mapPrecomp : HomComplex K L ⟶
    HomComplex K' ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) where
  f n := AddCommGrpCat.ofHom
    { toFun z := (Cochain.ofHom a).comp (z.map F) (zero_add n)
      map_zero' := by
        rw [Cochain.map_zero, Cochain.comp_zero]
      map_add' z w := by
        rw [Cochain.map_add, Cochain.comp_add] }
  comm' i j _ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change Cochain K L i at z
    change HomComplex.δ i j ((Cochain.ofHom a).comp (z.map F) (zero_add i)) =
      (Cochain.ofHom a).comp ((HomComplex.δ i j z).map F) (zero_add j)
    have hδ : HomComplex.δ i j (z.map F) = (HomComplex.δ i j z).map F :=
      HomComplex.δ_map (n := i) (m := j) (z := z) (Φ := F)
    exact (HomComplex.δ_ofHom_comp a (z.map F) j).trans
      (congrArg (fun b : Cochain
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) j =>
        (Cochain.ofHom a).comp b (zero_add j)) hδ)

/-- The actual additive-functor image of a cocycle. -/
def cocycleMap {n : ℤ} (z : Cocycle K L n) :
    Cocycle ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n :=
  Cocycle.mk (z.1.map F) (n + 1) rfl (by
    rw [HomComplex.δ_map, Cocycle.δ_eq_zero, Cochain.map_zero])

/-- Applying the functor and then precomposing on actual cocycles. -/
def cocycleMapPrecomp (n : ℤ) : Cocycle K L n →+
    Cocycle K' ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n where
  toFun z := (cocycleMap F z).precomp a
  map_zero' := by
    apply Subtype.ext
    change (Cochain.ofHom a).comp ((0 : Cochain K L n).map F) (zero_add n) = 0
    rw [Cochain.map_zero, Cochain.comp_zero]
  map_add' z w := by
    apply Subtype.ext
    change (Cochain.ofHom a).comp ((z.1 + w.1).map F) (zero_add n) =
      (Cochain.ofHom a).comp (z.1.map F) (zero_add n) +
        (Cochain.ofHom a).comp (w.1.map F) (zero_add n)
    rw [Cochain.map_add, Cochain.comp_add]

/-- The induced map on the existing quotient of cocycles by coboundaries. -/
def cohomologyClassMapPrecomp (n : ℤ) : CohomologyClass K L n →+
    CohomologyClass K' ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom _ _ n).comp (cocycleMapPrecomp F a n)) (by
      intro z hz
      change CohomologyClass.mk ((cocycleMap F z).precomp a) = 0
      apply (CohomologyClass.mk_eq_zero_iff _).mpr
      obtain ⟨m, hm, b, hb⟩ := hz
      refine ⟨m, hm, (Cochain.ofHom a).comp (b.map F) (zero_add m), ?_⟩
      rw [HomComplex.δ_ofHom_comp, HomComplex.δ_map, hb]
      rfl)

theorem cohomologyClassMapPrecomp_mk (n : ℤ) (z : Cocycle K L n) :
    cohomologyClassMapPrecomp F a n (CohomologyClass.mk z) =
      CohomologyClass.mk ((cocycleMap F z).precomp a) := rfl

/-- The cocycle-to-shifted-chain-map equivalence preserves the actual
additive-functor image and its canonical shift comparison. -/
theorem equivHomShift_symm_cocycleMap {n : ℤ} (z : Cocycle K L n) :
    Cocycle.equivHomShift.symm (cocycleMap F z) =
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Cocycle.equivHomShift.symm z) ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app L := by
  apply HomologicalComplex.hom_ext
  intro i
  change (z.1.map F).v i (i + n) rfl ≫
      (CochainComplex.shiftFunctorObjXIso
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n i (i + n) rfl).inv =
    F.map (z.1.v i (i + n) rfl ≫ (L.shiftFunctorObjXIso n i (i + n) rfl).inv) ≫
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app L).f i
  simp only [Cochain.map_v, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  exact (Category.comp_id (F.map (z.1.v i (i + n) rfl))).symm

/-- The Hom-complex class comparison preserves the actual map and
precomposition on a cocycle representative. -/
theorem cohomologyClassMapPrecomp_toHom_mk (n : ℤ) (z : Cocycle K L n) :
    CohomologyClass.toHom
        (cohomologyClassMapPrecomp F a n (CohomologyClass.mk z)) =
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        (a ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (Cocycle.equivHomShift.symm z) ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app L) := by
  rw [cohomologyClassMapPrecomp_mk, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_precomp, equivHomShift_symm_cocycleMap]

private def mapPrecompHomologyData (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n).map
        (mapPrecomp F a (L := L)))
      (leftHomologyData K L n)
      (leftHomologyData K' ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n) := by
  let SL : ShortComplex AddCommGrpCat.{v} := (HomComplex K L).sc n
  let SM : ShortComplex AddCommGrpCat.{v} :=
    (HomComplex K' ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).sc n
  let hL : SL.LeftHomologyData := leftHomologyData K L n
  let hM : SM.LeftHomologyData :=
    leftHomologyData K' ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n
  let f : SL ⟶ SM :=
    (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n).map
      (mapPrecomp F a)
  change ShortComplex.LeftHomologyMapData f hL hM
  let c : hL.K ⟶ hM.K := AddCommGrpCat.ofHom (cocycleMapPrecomp F a n)
  have hi : c ≫ hM.i = hL.i ≫ f.τ₂ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    rfl
  refine
    { φK := c
      φH := AddCommGrpCat.ofHom (cohomologyClassMapPrecomp F a n)
      commi := hi
      commf' := ?_
      commπ := ?_ }
  · let d : ShortComplex.LeftHomologyMapData f hL hM := default
    have hc : c = d.φK := (cancel_mono hM.i).mp (hi.trans d.commi.symm)
    exact (congrArg (fun t : hL.K ⟶ hM.K => hL.f' ≫ t) hc).trans d.commf'
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    exact cohomologyClassMapPrecomp_mk F a n z

/-- The original Hom-complex homology/class equivalence preserves the
native homology map of the actual additive-functor map and precomposition. -/
theorem homologyAddEquiv_mapPrecomp (n : ℤ) (z : (HomComplex K L).homology n) :
    homologyAddEquiv K' ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n
        (HomologicalComplex.homologyMap (mapPrecomp F a) n z) =
      cohomologyClassMapPrecomp F a n (homologyAddEquiv K L n z) :=
  ConcreteCategory.congr_hom (mapPrecompHomologyData F a n).homologyMap_comm z

end CochainComplex.HomComplex
