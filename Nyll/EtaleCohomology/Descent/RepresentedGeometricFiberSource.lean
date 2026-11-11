/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberSections
public import Nyll.EtaleCohomology.Descent.SetSheafDescentSourceComposition

public import Nyll.EtaleCohomology.Sites.SetPullbackComposition
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Original source compatibility on represented geometric fibers

The actual geometric-fiber germ map over an arbitrary base respects the
original source unit. The existing pullback-pasting projection theorem
supplies the source square; no replacement of the original unit or maps
on stalks is involved.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

namespace EtaleCohomology

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (t : Spec (CommRingCat.of Ω) ⟶ S)

/-- The actual pointed-neighborhood source comparison commutes with
restriction to the original geometric fiber. -/
theorem representedGeometricFiberGerm_source_comp
    (W : X.Etale) (U : S.Etale) (v : (Scheme.pointSmallEtale t).fiber.obj U)
    (a : (etaleBaseChange f).obj U ⟶ W) :
    representedGeometricFiberGerm (g ≫ f) t ((etaleBaseChange g).obj W) U v
        ((MorphismProperty.Over.pullbackComp
          (P := show MorphismProperty Scheme from @Etale) (Q := ⊤) g f).hom.app U ≫
          (etaleBaseChange g).map a) =
      representedSourcePullback t f g W
        (representedGeometricFiberGerm f t W U v a) := by
  let n := (Over.pullback f).map v
  let mX := n.left
  let mY := ((Over.pullback (g ≫ f)).map v).left
  let b := (Scheme.Etale.forget X).map a
  let s := (pullbackLeftPullbackSndIso t f g).inv
  let e : pullback U.hom (g ≫ f) ⟶ pullback (pullback.snd U.hom f) g :=
    ((MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme from @Etale) (Q := ⊤) g f).hom.app U).left
  let p := ((Over.pullback g).map n).left
  have he₁ : e ≫ pullback.fst (pullback.snd U.hom f) g ≫ pullback.fst U.hom f =
      pullback.fst U.hom (g ≫ f) :=
    MorphismProperty.Over.pullbackComp_left_fst_fst
      (P := show MorphismProperty Scheme from @Etale) (Q := ⊤) g f U
  have he₂ : e ≫ pullback.snd (pullback.snd U.hom f) g =
      pullback.snd U.hom (g ≫ f) :=
    ((MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme from @Etale) (Q := ⊤) g f).hom.app U).w
  have hp₁ : p ≫ pullback.fst (pullback.snd U.hom f) g =
      pullback.fst (pullback.snd t f) g ≫ mX := pullback.lift_fst _ _ _
  have hp₂ : p ≫ pullback.snd (pullback.snd U.hom f) g =
      pullback.snd (pullback.snd t f) g := pullback.lift_snd _ _ _
  have hx₁ : mX ≫ pullback.fst U.hom f = pullback.fst t f ≫ v.left :=
    pullback.lift_fst _ _ _
  have hy₁ : mY ≫ pullback.fst U.hom (g ≫ f) = pullback.fst t (g ≫ f) ≫ v.left :=
    pullback.lift_fst _ _ _
  have hy₂ : mY ≫ pullback.snd U.hom (g ≫ f) = pullback.snd t (g ≫ f) :=
    ((Over.pullback (g ≫ f)).map v).w
  have hn : mY ≫ e = s ≫ p :=
    sourceComp_of_projections t U.hom f g v.left mX mY e p
      he₁ he₂ hp₁ hp₂ hx₁ hy₁ hy₂
  have hmap : ((Over.pullback g).map (n ≫ b)).left =
      p ≫ ((Over.pullback g).map b).left :=
    congrArg (fun k => k.left) ((Over.pullback g).map_comp n b)
  apply Over.OverMorphism.ext
  change mY ≫ (e ≫ ((Over.pullback g).map b).left) =
    s ≫ ((Over.pullback g).map (n ≫ b)).left
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ ((Over.pullback g).map b).left) hn).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k => s ≫ k) hmap.symm)))

/-- The original source unit commutes with the actual represented fiber
section map over an arbitrary base. -/
theorem etaleSetPushforwardRepresentableFiberSections_source (W : X.Etale) :
    (Scheme.pointSmallEtale t).sheafFiber.map
        ((etaleSetPushforward f).map
          ((etaleSetPullbackPushforwardAdjunction g).unit.app
              (X.smallEtaleTopology.yoneda.obj W) ≫
            (etaleSetPushforward g).map (etaleSetPullbackYonedaObjIso g W).hom) ≫
          (etaleSetPushforwardCompIso g f).hom.app
            (Y.smallEtaleTopology.yoneda.obj ((etaleBaseChange g).obj W))) ≫
      etaleSetPushforwardRepresentableFiberSections (g ≫ f) t ((etaleBaseChange g).obj W) =
    etaleSetPushforwardRepresentableFiberSections f t W ≫ representedSourcePullback t f g W := by
  let Φ := Scheme.pointSmallEtale t
  let Wg := (etaleBaseChange g).obj W
  let F := (etaleSetPushforward f).obj (X.smallEtaleTopology.yoneda.obj W)
  let G := (etaleSetPushforward (g ≫ f)).obj (Y.smallEtaleTopology.yoneda.obj Wg)
  let η : F ⟶ G := (etaleSetPushforward f).map
      ((etaleSetPullbackPushforwardAdjunction g).unit.app
          (X.smallEtaleTopology.yoneda.obj W) ≫
        (etaleSetPushforward g).map (etaleSetPullbackYonedaObjIso g W).hom) ≫
    (etaleSetPushforwardCompIso g f).hom.app (Y.smallEtaleTopology.yoneda.obj Wg)
  apply Φ.presheafFiber_hom_ext
  intro U v
  let sF := Φ.toPresheafFiber U v F.obj
  let sG := Φ.toPresheafFiber U v G.obj
  let k := Φ.sheafFiber.map η
  let cF := etaleSetPushforwardRepresentableFiberSections f t W
  let cG := etaleSetPushforwardRepresentableFiberSections (g ≫ f) t Wg
  let r := representedSourcePullback t f g W
  have hn : sF ≫ k = η.hom.app (op U) ≫ sG :=
    Φ.toPresheafFiber_naturality η.hom U v
  have hF : sF ≫ cF = representedGeometricFiberGerm f t W U v :=
    toPresheafFiber_etaleSetPushforwardRepresentableFiberSections f t W U v
  have hG : sG ≫ cG = representedGeometricFiberGerm (g ≫ f) t Wg U v :=
    toPresheafFiber_etaleSetPushforwardRepresentableFiberSections (g ≫ f) t Wg U v
  have hsection : η.hom.app (op U) ≫ representedGeometricFiberGerm (g ≫ f) t Wg U v =
      representedGeometricFiberGerm f t W U v ≫ r := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (congrArg (fun b => representedGeometricFiberGerm (g ≫ f) t Wg U v b)
      (etaleSetPushforward_unit_yoneda_comp_app f g W U a)).trans
        (representedGeometricFiberGerm_source_comp f g t W U v a)
  change sF ≫ (k ≫ cG) = sF ≫ (cF ≫ r)
  exact (Category.assoc sF k cG).symm.trans
    ((congrArg (fun b => b ≫ cG) hn).trans
      ((Category.assoc (η.hom.app (op U)) sG cG).trans
        ((congrArg (fun b => η.hom.app (op U) ≫ b) hG).trans
          (hsection.trans
            ((congrArg (fun b => b ≫ r) hF).symm.trans (Category.assoc sF cF r))))))

end EtaleCohomology
