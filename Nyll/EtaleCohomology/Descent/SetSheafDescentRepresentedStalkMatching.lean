/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.SetSheafDescentRepresentedArrows
public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberComponent
public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberProper
public import Nyll.EtaleCohomology.Descent.RepresentedOverlapFiberMatching

public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberSections
public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberSource
public import Nyll.EtaleCohomology.Descent.RepresentedFiberBaseEquality
public import Nyll.EtaleCohomology.Descent.RepresentedOverlapMatchingSections
public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Mathlib.CategoryTheory.CommSq

/-!
# The original matching stalk equation on represented geometric fibers

Both original matching arrows are compared by their actual target
isomorphism. Properness supplies the existing bijectivity of represented
geometric-fiber sections, so their original stalk equalizer equation is
exactly the original represented source matching equation.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology.SetSheafDescent

private theorem map_four_comp_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A₀ A₁ A₂ A₃ A₄ : C} {B₀ B₁ B₂ B₃ : D}
    (a : A₀ ⟶ A₄) (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂)
    (h : A₂ ⟶ A₃) (i : A₃ ⟶ A₄)
    (c₀ : F.obj A₀ ⟶ B₀) (c₁ : F.obj A₂ ⟶ B₁)
    (c₂ : F.obj A₃ ⟶ B₂) (c₃ : F.obj A₄ ⟶ B₃)
    (s : B₀ ⟶ B₁) (k : B₁ ⟶ B₂) (d : B₂ ⟶ B₃)
    (ha : a = f ≫ g ≫ h ≫ i)
    (hu : F.map (f ≫ g) ≫ c₁ = c₀ ≫ s)
    (hk : F.map h ≫ c₂ = c₁ ≫ k)
    (hd : F.map i ≫ c₃ = c₂ ≫ d) :
    F.map a ≫ c₃ = c₀ ≫ s ≫ k ≫ d := by
  have hm : F.map a = F.map (f ≫ g) ≫ (F.map h ≫ F.map i) :=
    (congrArg F.map (ha.trans (Category.assoc f g (h ≫ i)).symm)).trans
      ((F.map_comp (f ≫ g) (h ≫ i)).trans
        (congrArg (fun b => F.map (f ≫ g) ≫ b) (F.map_comp h i)))
  exact (congrArg (fun b => b ≫ c₃) hm).trans
    (((CommSq.mk hu).horiz_comp ((CommSq.mk hk).horiz_comp (CommSq.mk hd))).w)

variable {X Y : Scheme.{u}} (q : Y ⟶ X)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (CommRingCat.of Ω) ⟶ X)
  (W : Y.Etale)
  (η : (etaleBaseChange (pullback.fst q q)).obj W ≅
    (etaleBaseChange (pullback.snd q q)).obj W)

/-- The original first matching arrow becomes the actual first source
map, followed by the original coefficient map and original base equality. -/
theorem firstArrow_representedOverlapArrowTarget_fiber :
    (Scheme.pointSmallEtale t).sheafFiber.map
        (firstArrow q (Y.smallEtaleTopology.yoneda.obj W) ≫
          ((etaleSetPushforwardCompIso (pullback.fst q q) q).hom.app
      ((etaleSetPullback (pullback.fst q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
    (etaleSetPushforward (pullback.fst q q ≫ q)).map (representedOverlapIso q W η).hom ≫
      (eqToIso (congrArg (fun r => etaleSetPushforward r)
        (pullback.condition (f := q) (g := q)))).hom.app
          ((etaleSetPullback (pullback.snd q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
        (etaleSetPushforward (pullback.snd q q ≫ q)).map
          (etaleSetPullbackYonedaObjIso (pullback.snd q q) W).hom)) ≫
      etaleSetPushforwardRepresentableFiberSections
        (pullback.snd q q ≫ q) t ((etaleBaseChange (pullback.snd q q)).obj W) =
    etaleSetPushforwardRepresentableFiberSections q t W ≫
      representedSourcePullback t q (pullback.fst q q) W ≫
        TypeCat.ofHom (fun a :
          Over.mk (pullback.snd t (pullback.fst q q ≫ q)) ⟶
            (Scheme.Etale.forget (pullback q q)).obj
              ((etaleBaseChange (pullback.fst q q)).obj W) =>
          a ≫ (Scheme.Etale.forget (pullback q q)).map η.hom) ≫
        representedSectionsBaseEquality t
          (pullback.fst q q ≫ q) (pullback.snd q q ≫ q)
          (pullback.condition (f := q) (g := q))
          ((etaleBaseChange (pullback.snd q q)).obj W) := by
  exact map_four_comp_square (Scheme.pointSmallEtale t).sheafFiber
    (firstArrow q (Y.smallEtaleTopology.yoneda.obj W) ≫
      (etaleSetPushforwardCompIso (pullback.fst q q) q).hom.app
        ((etaleSetPullback (pullback.fst q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
      (etaleSetPushforward (pullback.fst q q ≫ q)).map
        (representedOverlapIso q W η).hom ≫
      (eqToIso (congrArg (fun r => etaleSetPushforward r)
        (pullback.condition (f := q) (g := q)))).hom.app
          ((etaleSetPullback (pullback.snd q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
      (etaleSetPushforward (pullback.snd q q ≫ q)).map
        (etaleSetPullbackYonedaObjIso (pullback.snd q q) W).hom)
    ((etaleSetPushforward q).map
      ((etaleSetPullbackPushforwardAdjunction (pullback.fst q q)).unit.app
        (Y.smallEtaleTopology.yoneda.obj W) ≫
      (etaleSetPushforward (pullback.fst q q)).map
        (etaleSetPullbackYonedaObjIso (pullback.fst q q) W).hom))
    ((etaleSetPushforwardCompIso (pullback.fst q q) q).hom.app
      ((pullback q q).smallEtaleTopology.yoneda.obj
        ((etaleBaseChange (pullback.fst q q)).obj W)))
    ((etaleSetPushforward (pullback.fst q q ≫ q)).map
      ((pullback q q).smallEtaleTopology.yoneda.map η.hom))
    ((eqToIso (congrArg (fun r => etaleSetPushforward r)
      (pullback.condition (f := q) (g := q)))).hom.app
        ((pullback q q).smallEtaleTopology.yoneda.obj
          ((etaleBaseChange (pullback.snd q q)).obj W)))
    (etaleSetPushforwardRepresentableFiberSections q t W)
    (etaleSetPushforwardRepresentableFiberSections (pullback.fst q q ≫ q) t
      ((etaleBaseChange (pullback.fst q q)).obj W))
    (etaleSetPushforwardRepresentableFiberSections (pullback.fst q q ≫ q) t
      ((etaleBaseChange (pullback.snd q q)).obj W))
    (etaleSetPushforwardRepresentableFiberSections (pullback.snd q q ≫ q) t
      ((etaleBaseChange (pullback.snd q q)).obj W))
    (representedSourcePullback t q (pullback.fst q q) W)
    (TypeCat.ofHom (fun a :
      Over.mk (pullback.snd t (pullback.fst q q ≫ q)) ⟶
        (Scheme.Etale.forget (pullback q q)).obj
          ((etaleBaseChange (pullback.fst q q)).obj W) =>
      a ≫ (Scheme.Etale.forget (pullback q q)).map η.hom))
    (representedSectionsBaseEquality t
      (pullback.fst q q ≫ q) (pullback.snd q q ≫ q)
      (pullback.condition (f := q) (g := q))
      ((etaleBaseChange (pullback.snd q q)).obj W))
    (firstArrow_representedOverlapArrowTarget q W η)
    (etaleSetPushforwardRepresentableFiberSections_source q (pullback.fst q q) t W)
    (etaleSetPushforwardRepresentableFiberSections_naturality (pullback.fst q q ≫ q) t
      η.hom)
    (etaleSetPushforwardRepresentableFiberSections_baseEquality t
      (pullback.fst q q ≫ q) (pullback.snd q q ≫ q)
      (pullback.condition (f := q) (g := q))
      ((etaleBaseChange (pullback.snd q q)).obj W))

/-- For a finite étale coefficient on the actual proper family, the two
original matching stalk arrows agree exactly when the represented section
satisfies the original source matching equation. -/
theorem represented_stalk_matching_iff [IsProper q] (V : FiniteEtale Y)
    (ι : (etaleBaseChange (pullback.fst q q)).obj ((finiteEtaleToEtale Y).obj V) ≅
      (etaleBaseChange (pullback.snd q q)).obj ((finiteEtaleToEtale Y).obj V))
    (a : (Scheme.pointSmallEtale t).sheafFiber.obj
      ((etaleSetPushforward q).obj ((finiteEtaleSheaf Y).obj V))) :
    (Scheme.pointSmallEtale t).sheafFiber.map
        (firstArrow q ((finiteEtaleSheaf Y).obj V)) a =
      (Scheme.pointSmallEtale t).sheafFiber.map
        (secondArrow q ((finiteEtaleSheaf Y).obj V)
          (representedOverlapIso q ((finiteEtaleToEtale Y).obj V) ι)) a ↔
    representedSectionsBaseEquality t
        (pullback.fst q q ≫ q) (pullback.snd q q ≫ q)
        (pullback.condition (f := q) (g := q))
        ((etaleBaseChange (pullback.snd q q)).obj ((finiteEtaleToEtale Y).obj V))
        (representedSourcePullback t q (pullback.fst q q)
          ((finiteEtaleToEtale Y).obj V)
          (etaleSetPushforwardRepresentableFiberSections q t
            ((finiteEtaleToEtale Y).obj V) a) ≫
            (Scheme.Etale.forget (pullback q q)).map ι.hom) =
      representedSourcePullback t q (pullback.snd q q)
        ((finiteEtaleToEtale Y).obj V)
        (etaleSetPushforwardRepresentableFiberSections q t
          ((finiteEtaleToEtale Y).obj V) a) := by
  let Φ := Scheme.pointSmallEtale t
  let W := (finiteEtaleToEtale Y).obj V
  let θ := representedOverlapIso q W ι
  let T := ((etaleSetPushforwardCompIso (pullback.fst q q) q).hom.app
      ((etaleSetPullback (pullback.fst q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
    (etaleSetPushforward (pullback.fst q q ≫ q)).map θ.hom ≫
      (eqToIso (congrArg (fun r => etaleSetPushforward r)
        (pullback.condition (f := q) (g := q)))).hom.app
          ((etaleSetPullback (pullback.snd q q)).obj (Y.smallEtaleTopology.yoneda.obj W)) ≫
        (etaleSetPushforward (pullback.snd q q ≫ q)).map
          (etaleSetPullbackYonedaObjIso (pullback.snd q q) W).hom)
  let c := etaleSetPushforwardRepresentableFiberSections
    (pullback.snd q q ≫ q) t ((etaleBaseChange (pullback.snd q q)).obj W)
  let A := firstArrow q ((finiteEtaleSheaf Y).obj V)
  let B := secondArrow q ((finiteEtaleSheaf Y).obj V) θ
  have : IsIso T := representedOverlapArrowTarget_isIso q W θ
  have hT : Function.Injective (Φ.sheafFiber.map T) :=
    (ConcreteCategory.bijective_of_isIso (Φ.sheafFiber.map T)).1
  have hc : Function.Injective c :=
    (etaleSetPushforwardRepresentableFiberSections_bijective
      (pullback.snd q q ≫ q) t ((FiniteEtale.pullback (pullback.snd q q)).obj V)).1
  have h₁ := ConcreteCategory.congr_hom
    (firstArrow_representedOverlapArrowTarget_fiber q t W ι) a
  have h₂ := ConcreteCategory.congr_hom
    (secondArrow_representedOverlapArrowTarget_fiber q t W θ) a
  have hmA : Φ.sheafFiber.map (A ≫ T) a =
      Φ.sheafFiber.map T (Φ.sheafFiber.map A a) :=
    ConcreteCategory.congr_hom (Φ.sheafFiber.map_comp A T) a
  have hmB : Φ.sheafFiber.map (B ≫ T) a =
      Φ.sheafFiber.map T (Φ.sheafFiber.map B a) :=
    ConcreteCategory.congr_hom (Φ.sheafFiber.map_comp B T) a
  constructor
  · intro h
    exact h₁.symm.trans
      ((congrArg c (hmA.trans ((congrArg (Φ.sheafFiber.map T) h).trans hmB.symm))).trans h₂)
  · intro h
    apply hT
    apply hc
    exact (congrArg c hmA.symm).trans
      (h₁.trans (h.trans (h₂.symm.trans (congrArg c hmB))))

end EtaleCohomology.SetSheafDescent
