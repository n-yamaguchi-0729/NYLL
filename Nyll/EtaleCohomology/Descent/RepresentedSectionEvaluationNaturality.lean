/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.RepresentedSectionPrecomposition
public import Nyll.EtaleCohomology.Descent.SetSheafDescentStalkSourceComposition

/-!
# Original evaluation and original source pullback on represented sections

Evaluation is literal precomposition on the existing represented section
sets. Its source naturality follows from the existing pullback-pasting
projection calculation, applied to the original evaluation square.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleFundamentalGroups.StrictHenselian

universe u

namespace EtaleCohomology

variable {R Ω : Type u} [CommRing R] [Field Ω]
  (φ : R →+* Ω) {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ X)

/-- Evaluation on represented sections is precomposition by the original
evaluation map of source schemes. -/
def geometricStalkEvaluationRepresentedSectionsMap (W : X.Etale) :
    (Over.mk
      (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) ⟶
        (Scheme.Etale.forget X).obj W) ⟶
    (Over.mk (pullback.snd (Spec.map (CommRingCat.ofHom φ)) f) ⟶
      (Scheme.Etale.forget X).obj W) :=
  TypeCat.ofHom (fun a => Over.homMk
    (geometricStalkEvaluationBaseChangeMap φ f ≫ a.left)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => geometricStalkEvaluationBaseChangeMap φ f ≫ k) a.w).trans
        (geometricStalkEvaluationBaseChangeMap_snd φ f))))

/-- The literal evaluation map is bijective for every finite étale
representer on the original proper family. -/
theorem geometricStalkEvaluationRepresentedSectionsMap_bijective
    [IsSepClosed Ω] [IsProper f] (W : FiniteEtale X) :
    Function.Bijective (geometricStalkEvaluationRepresentedSectionsMap φ f
      ((finiteEtaleToEtale X).obj W)) :=
  geometricStalkEvaluation_representedSections_precomp_bijective φ f W

/-- Original evaluation commutes with source base change, using the
same slice pullback and pasting maps as the original stalk formula. -/
theorem geometricStalkEvaluationRepresentedSectionsMap_source
    (W : X.Etale) :
    geometricStalkRepresentableSourcePullback φ f g W ≫
        geometricStalkEvaluationRepresentedSectionsMap φ (g ≫ f)
          ((etaleBaseChange g).obj W) =
      geometricStalkEvaluationRepresentedSectionsMap φ f W ≫
        representedSourcePullback (Spec.map (CommRingCat.ofHom φ)) f g W := by
  let h := Spec.map (CommRingCat.ofHom φ)
  let u := Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let n := Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ)))
  let mX := geometricStalkEvaluationBaseChangeMap φ f
  let mY := geometricStalkEvaluationBaseChangeMap φ (g ≫ f)
  let eX : Over.mk (pullback.snd h f) ⟶ Over.mk (pullback.snd u f) :=
    Over.homMk mX (geometricStalkEvaluationBaseChangeMap_snd φ f)
  let p := ((Over.pullback g).map eX).left
  let e := (pullbackLeftPullbackSndIso u f g).inv
  let s := (pullbackLeftPullbackSndIso h f g).inv
  have hc : mY ≫ e = s ≫ p :=
    sourceComp_of_projections h u f g n mX mY e p
      (pullbackLeftPullbackSndIso_inv_fst u f g)
      (pullbackLeftPullbackSndIso_inv_snd_snd u f g)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (geometricStalkEvaluationBaseChangeMap_fst φ f)
      (geometricStalkEvaluationBaseChangeMap_fst φ (g ≫ f))
      (geometricStalkEvaluationBaseChangeMap_snd φ (g ≫ f))
  apply ConcreteCategory.hom_ext
  intro a
  have hmap : ((Over.pullback g).map (eX ≫ a)).left =
      p ≫ ((Over.pullback g).map a).left :=
    congrArg (fun k => k.left) ((Over.pullback g).map_comp eX a)
  apply Over.OverMorphism.ext
  change mY ≫ (e ≫ ((Over.pullback g).map a).left) =
    s ≫ ((Over.pullback g).map (eX ≫ a)).left
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ ((Over.pullback g).map a).left) hc).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k => s ≫ k) hmap.symm)))

variable [IsSepClosed Ω]

/-- The original represented direct-image stalk map, followed by literal
evaluation, lands in the actual represented sections on the original
geometric fiber. -/
def etaleSetPushforwardRepresentableGeometricFiberSections (W : X.Etale) :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber.obj
      ((etaleSetPushforward f).obj (X.smallEtaleTopology.yoneda.obj W)) ⟶
    (Over.mk (pullback.snd (Spec.map (CommRingCat.ofHom φ)) f) ⟶
      (Scheme.Etale.forget X).obj W) :=
  etaleSetPushforwardRepresentableGeometricStalkSections φ f W ≫
    geometricStalkEvaluationRepresentedSectionsMap φ f W

/-- The original represented geometric-fiber section map is bijective
for every finite étale coefficient on the actual proper family. -/
theorem etaleSetPushforwardRepresentableGeometricFiberSections_bijective
    [IsProper f] (W : FiniteEtale X) :
    Function.Bijective (etaleSetPushforwardRepresentableGeometricFiberSections φ f
      ((finiteEtaleToEtale X).obj W)) :=
  (geometricStalkEvaluationRepresentedSectionsMap_bijective φ f W).comp
    (etaleSetPushforwardRepresentableGeometricStalkSections_bijective φ f
      ((finiteEtaleToEtale X).obj W))

/-- The original source unit commutes with the actual represented
geometric-fiber comparison, retaining the original stalk map, evaluation,
representable inverse-image comparison, and source-pasting maps. -/
theorem etaleSetPushforwardRepresentableGeometricFiberSections_source
    (W : X.Etale) :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber.map
        ((etaleSetPushforward f).map
          ((etaleSetPullbackPushforwardAdjunction g).unit.app
              (X.smallEtaleTopology.yoneda.obj W) ≫
            (etaleSetPushforward g).map (etaleSetPullbackYonedaObjIso g W).hom) ≫
          (etaleSetPushforwardCompIso g f).hom.app
            (Y.smallEtaleTopology.yoneda.obj ((etaleBaseChange g).obj W))) ≫
      etaleSetPushforwardRepresentableGeometricFiberSections
        φ (g ≫ f) ((etaleBaseChange g).obj W) =
    etaleSetPushforwardRepresentableGeometricFiberSections φ f W ≫
      representedSourcePullback (Spec.map (CommRingCat.ofHom φ)) f g W := by
  let Φ := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))
  let Wg := (etaleBaseChange g).obj W
  let η := (etaleSetPushforward f).map
    ((etaleSetPullbackPushforwardAdjunction g).unit.app
        (X.smallEtaleTopology.yoneda.obj W) ≫
      (etaleSetPushforward g).map (etaleSetPullbackYonedaObjIso g W).hom) ≫
    (etaleSetPushforwardCompIso g f).hom.app (Y.smallEtaleTopology.yoneda.obj Wg)
  let c₀ := etaleSetPushforwardRepresentableGeometricStalkSections φ f W
  let c₁ := etaleSetPushforwardRepresentableGeometricStalkSections φ (g ≫ f) Wg
  let e₀ := geometricStalkEvaluationRepresentedSectionsMap φ f W
  let e₁ := geometricStalkEvaluationRepresentedSectionsMap φ (g ≫ f) Wg
  let t := geometricStalkRepresentableSourcePullback φ f g W
  let t' := representedSourcePullback (Spec.map (CommRingCat.ofHom φ)) f g W
  have hs : Φ.sheafFiber.map η ≫ c₁ = c₀ ≫ t :=
    etaleSetPushforwardRepresentableGeometricStalkSections_source_comp φ f g W
  have he : t ≫ e₁ = e₀ ≫ t' :=
    geometricStalkEvaluationRepresentedSectionsMap_source φ f g W
  change Φ.sheafFiber.map η ≫ (c₁ ≫ e₁) = (c₀ ≫ e₀) ≫ t'
  exact (Category.assoc (Φ.sheafFiber.map η) c₁ e₁).symm.trans
    ((congrArg (fun k => k ≫ e₁) hs).trans
      ((Category.assoc c₀ t e₁).trans
        ((congrArg (fun k => c₀ ≫ k) he).trans (Category.assoc c₀ e₀ t').symm)))

end EtaleCohomology
