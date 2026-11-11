/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.HomologicalAlgebra.HomFromSingle
public import Nyll.SchemeTheory.HomologicalAlgebra.HomFromSingleMap
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Whiskering

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
/-!
# Actual Hom-complex maps retain a natural sections comparison

The given degreewise sections formula determines the map of Hom complexes.
Postcomposition and the exact-functor homology comparison preserve its square.
-/

@[expose] public section

noncomputable section

universe v

open CategoryTheory Limits Opposite

namespace CategoryTheory

/-- The actual map from a single object retains a given natural sections comparison. -/
theorem homFromSingleSectionsIso_map
    {C D E : Type*} [Category.{v} C] [Category.{v} D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    (L : C ⥤ D) (GY : C ⥤ E) (GX : D ⥤ E) (V : E ⥤ AddCommGrpCat.{v})
    [L.Additive] [GY.Additive] [GX.Additive] [V.Additive]
    {A : C} {B : D} (u : B ⟶ L.obj A)
    (eY : preadditiveCoyoneda.obj (op A) ≅ GY ⋙ V)
    (eX : preadditiveCoyoneda.obj (op B) ≅ GX ⋙ V)
    (θ : GY ⟶ L ⋙ GX)
    (hθ : ∀ (F : C) (a : A ⟶ F),
      eX.hom.app (L.obj F) (u ≫ L.map a) = V.map (θ.app F) (eY.hom.app F a))
    (K : CochainComplex C ℤ) :
    homFromSingleMap L u K ≫
        ((homFromSingleIso B ≪≫ NatIso.mapHomologicalComplex eX
          (ComplexShape.up ℤ)).app ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom =
      ((homFromSingleIso A ≪≫ NatIso.mapHomologicalComplex eY
        (ComplexShape.up ℤ)).app K).hom ≫
        (V.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app K) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  change eX.hom.app (L.obj (K.X n))
      (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n)
        ((homFromSingleMap L u K).f n z)) =
    V.map (θ.app (K.X n))
      (eY.hom.app (K.X n)
        (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n) z))
  have hz := homFromSingleMap_apply L u K n
    (show CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor C 0).obj A) K n from z)
  exact (congrArg (fun a : B ⟶ L.obj (K.X n) =>
    eX.hom.app (L.obj (K.X n)) a) hz).trans (hθ (K.X n) _)

/-- Postcomposition retains the same natural comparison of actual Hom complexes. -/
theorem homFromSingleSectionsIso_postcomp
    {C D E : Type*} [Category.{v} C] [Category.{v} D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    (L : C ⥤ D) (GY : C ⥤ E) (GX : D ⥤ E) (V : E ⥤ AddCommGrpCat.{v})
    [L.Additive] [GY.Additive] [GX.Additive] [V.Additive]
    {A : C} {B : D} (u : B ⟶ L.obj A)
    (eY : preadditiveCoyoneda.obj (op A) ≅ GY ⋙ V)
    (eX : preadditiveCoyoneda.obj (op B) ≅ GX ⋙ V)
    (θ : GY ⟶ L ⋙ GX)
    (hθ : ∀ (F : C) (a : A ⟶ F),
      eX.hom.app (L.obj F) (u ≫ L.map a) = V.map (θ.app F) (eY.hom.app F a))
    (K : CochainComplex C ℤ) (M : CochainComplex D ℤ)
    (e : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ M) :
    (homFromSingleMap L u K ≫ (homFromSingleFunctor B).map e) ≫
        ((homFromSingleIso B ≪≫ NatIso.mapHomologicalComplex eX
          (ComplexShape.up ℤ)).app M).hom =
      ((homFromSingleIso A ≪≫ NatIso.mapHomologicalComplex eY
        (ComplexShape.up ℤ)).app K).hom ≫
        (V.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app K ≫
            (GX.mapHomologicalComplex (ComplexShape.up ℤ)).map e) := by
  have hn : (homFromSingleFunctor B).map e ≫
        ((homFromSingleIso B ≪≫ NatIso.mapHomologicalComplex eX
          (ComplexShape.up ℤ)).app M).hom =
      ((homFromSingleIso B ≪≫ NatIso.mapHomologicalComplex eX
        (ComplexShape.up ℤ)).app
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom ≫
        (V.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((GX.mapHomologicalComplex (ComplexShape.up ℤ)).map e) :=
    (homFromSingleIso B ≪≫ NatIso.mapHomologicalComplex eX
      (ComplexShape.up ℤ)).hom.naturality e
  have hm := homFromSingleSectionsIso_map L GY GX V u eY eX θ hθ K
  rw [Category.assoc, hn, ← Category.assoc, hm,
    Category.assoc, Functor.map_comp]

/-- An actual chain square is preserved by homology and the exact-functor comparison. -/
theorem homologyMap_square_of_chain_square
    {E : Type*} [Category* E] [Abelian E]
    (V : E ⥤ AddCommGrpCat.{v}) [V.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {A B : CochainComplex AddCommGrpCat.{v} ℤ}
    {P Q : CochainComplex E ℤ} (a : A ⟶ B) (s : P ⟶ Q)
    (eP : A ≅ (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (eQ : B ≅ (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
    (h : a ≫ eQ.hom = eP.hom ≫ (V.mapHomologicalComplex (ComplexShape.up ℤ)).map s)
    (n : ℤ) :
    HomologicalComplex.homologyMap a n ≫
        (HomologicalComplex.homologyMap eQ.hom n ≫ ((Q.sc n).mapHomologyIso V).hom) =
      (HomologicalComplex.homologyMap eP.hom n ≫ ((P.sc n).mapHomologyIso V).hom) ≫
        V.map (HomologicalComplex.homologyMap s n) := by
  have hh := congrArg
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n).map) h
  simp only [Functor.map_comp] at hh
  have hs : CommSq (HomologicalComplex.homologyMap a n)
      (HomologicalComplex.homologyMap eP.hom n)
      (HomologicalComplex.homologyMap eQ.hom n)
      (HomologicalComplex.homologyMap
        ((V.mapHomologicalComplex (ComplexShape.up ℤ)).map s) n) := ⟨hh⟩
  have hn : CommSq
      (HomologicalComplex.homologyMap
        ((V.mapHomologicalComplex (ComplexShape.up ℤ)).map s) n)
      ((P.sc n).mapHomologyIso V).hom ((Q.sc n).mapHomologyIso V).hom
      (V.map (HomologicalComplex.homologyMap s n)) :=
    ⟨ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor E (ComplexShape.up ℤ) n).map s) V⟩
  exact (hs.vert_comp hn).w

end CategoryTheory
