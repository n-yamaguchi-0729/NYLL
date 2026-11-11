/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.HomologicalAlgebra.HomFromSingle
public import Nyll.SchemeTheory.HomologicalAlgebra.HomComplexMap
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.Single

/-!
# The actual functorial map from a single object

Applying an additive functor to a morphism and precomposing with a given
source map extends to the Hom complex. The degreewise formula uses the
original `Cochain.fromSingleEquiv`.
-/

@[expose] public section

noncomputable section

universe v uC uD

open CategoryTheory Limits CochainComplex HomComplex

namespace CategoryTheory

variable {C : Type uC} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {D : Type uD} [Category.{v} D] [Preadditive D] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive] {A : C} {B : D} (u : B ⟶ F.obj A)

/-- The chain map whose degreewise action is the actual map
`a ↦ u ≫ F.map a`. -/
def homFromSingleMap (K : CochainComplex C ℤ) :
    (homFromSingleFunctor A).obj K ⟶
      (homFromSingleFunctor B).obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  mapPrecomp F
    ((CochainComplex.singleFunctor D 0).map u ≫
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app A)

/-- The actual map of Hom complexes has the prescribed map on literal
morphisms in every degree. -/
theorem homFromSingleMap_apply (K : CochainComplex C ℤ) (n : ℤ)
    (z : Cochain ((CochainComplex.singleFunctor C 0).obj A) K n) :
    Cochain.fromSingleEquiv (zero_add n) ((homFromSingleMap F u K).f n z) =
      u ≫ F.map (Cochain.fromSingleEquiv (zero_add n) z) := by
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).inv ≫
      ((Cochain.ofHom ((CochainComplex.singleFunctor D 0).map u ≫
        (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app A)).comp
          (z.map F) (zero_add n)).v 0 n (zero_add n) =
      u ≫ F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv ≫
        z.v 0 n (zero_add n))
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.map_v,
    HomologicalComplex.comp_f, Category.assoc]
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).inv ≫
      ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).map u).f 0 ≫
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app A).f 0 ≫
        F.map (z.v 0 n (zero_add n)) = _
  rw [HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

end CategoryTheory
