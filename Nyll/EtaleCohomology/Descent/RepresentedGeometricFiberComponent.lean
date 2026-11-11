/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleCohomology.Descent.RepresentableSheafFiberGerms
public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberSections
public import Nyll.EtaleCohomology.Descent.RepresentedFiberBaseEquality
public import Nyll.EtaleCohomology.Sites.PushforwardStalkComparison
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors

/-!
# Original stalk components and equality transport over an arbitrary base

The general represented geometric-fiber map retains the original component
at each geometric lift and the original equality transport of base maps.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology

variable {S Y : Scheme.{u}} (q : Y ⟶ S)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (t : Spec (CommRingCat.of Ω) ⟶ S)
  (s : Spec (CommRingCat.of Ω) ⟶ Y) (hs : s ≫ q = t) (W : Y.Etale)

/-- The actual direct-image component is literal restriction at the
chosen lift, through the existing represented stalk isomorphism. -/
theorem etaleSetPushforwardRepresentableFiberSections_component :
    etalePushforwardStalkComponent q t ⟨s, hs⟩ (Y.smallEtaleTopology.yoneda.obj W) ≫
      (representableSheafFiberIso (Scheme.pointSmallEtale s)).hom.app W =
    etaleSetPushforwardRepresentableFiberSections q t W ≫
      representedGeometricFiberRestriction q t s hs W := by
  let Φ := Scheme.pointSmallEtale t
  let Ψ := Scheme.pointSmallEtale s
  let c := etalePushforwardStalkComponent q t ⟨s, hs⟩ (Y.smallEtaleTopology.yoneda.obj W)
  let E := (representableSheafFiberIso Ψ).hom.app W
  let C := etaleSetPushforwardRepresentableFiberSections q t W
  let r := representedGeometricFiberRestriction q t s hs W
  apply Φ.presheafFiber_hom_ext
  intro U v
  let γ := Φ.toPresheafFiber U v
    ((etaleSetPushforward q).obj (Y.smallEtaleTopology.yoneda.obj W)).obj
  let liftPoint := etalePushforwardGeometricLift q t ⟨s, hs⟩ U v
  let k := TypeCat.ofHom (fun a : (etaleBaseChange q).obj U ⟶ W => Ψ.fiber.map a liftPoint)
  have hl : γ ≫ (c ≫ E) = k :=
    (Category.assoc γ c E).symm.trans
      ((congrArg (fun a => a ≫ E)
        (toPresheafFiber_etalePushforwardStalkComponent q t ⟨s, hs⟩
          (Y.smallEtaleTopology.yoneda.obj W) U v)).trans
        (toPresheafFiber_representableSheafFiberIso Ψ ((etaleBaseChange q).obj U) W liftPoint))
  have hr : γ ≫ (C ≫ r) = representedGeometricFiberGerm q t W U v ≫ r :=
    (Category.assoc γ C r).symm.trans
      (congrArg (fun a => a ≫ r)
        (toPresheafFiber_etaleSetPushforwardRepresentableFiberSections q t W U v))
  refine hl.trans (Eq.trans ?_ hr.symm)
  apply ConcreteCategory.hom_ext
  intro a
  let σ : Spec (CommRingCat.of Ω) ⟶ pullback t q :=
    pullback.lift (𝟙 _) s ((Category.id_comp t).trans hs.symm)
  let vq := ((Over.pullback q).map v).left
  let l := liftPoint.left
  have hv₁ : vq ≫ pullback.fst U.hom q = pullback.fst t q ≫ v.left :=
    pullback.lift_fst _ _ _
  have hv₂ : vq ≫ pullback.snd U.hom q = pullback.snd t q := pullback.lift_snd _ _ _
  have hσ₁ : σ ≫ pullback.fst t q = 𝟙 _ := pullback.lift_fst _ _ _
  have hσ₂ : σ ≫ pullback.snd t q = s := pullback.lift_snd _ _ _
  have hl₁ : l ≫ pullback.fst U.hom q = v.left := pullback.lift_fst _ _ _
  have hl₂ : l ≫ pullback.snd U.hom q = s := pullback.lift_snd _ _ _
  have hσ : σ ≫ vq = l := by
    apply pullback.hom_ext
    · exact (Category.assoc σ vq (pullback.fst U.hom q)).trans
        ((congrArg (fun d => σ ≫ d) hv₁).trans
          ((Category.assoc σ (pullback.fst t q) v.left).symm.trans
            ((congrArg (fun d => d ≫ v.left) hσ₁).trans
              ((Category.id_comp v.left).trans hl₁.symm))))
    · exact (Category.assoc σ vq (pullback.snd U.hom q)).trans
        ((congrArg (fun d => σ ≫ d) hv₂).trans (hσ₂.trans hl₂.symm))
  apply Over.OverMorphism.ext
  change l ≫ a.left = σ ≫ (vq ≫ a.left)
  exact ((Category.assoc σ vq a.left).symm.trans
    (congrArg (fun d => d ≫ a.left) hσ)).symm

/-- The original direct-image equality acts by canonical pullback
congruence on the actual sections, for an arbitrary base scheme. -/
theorem etaleSetPushforwardRepresentableFiberSections_baseEquality
    (f g : Y ⟶ S) (hfg : f = g) (V : Y.Etale) :
    (Scheme.pointSmallEtale t).sheafFiber.map
        ((eqToIso (congrArg (fun r => etaleSetPushforward r) hfg)).hom.app
          (Y.smallEtaleTopology.yoneda.obj V)) ≫
      etaleSetPushforwardRepresentableFiberSections g t V =
    etaleSetPushforwardRepresentableFiberSections f t V ≫
      representedSectionsBaseEquality t f g hfg V := by
  subst g
  let Φ := Scheme.pointSmallEtale t
  let c := etaleSetPushforwardRepresentableFiberSections f t V
  have hm :
      Φ.sheafFiber.map
          ((eqToIso (congrArg (fun r => etaleSetPushforward r) (rfl : f = f))).hom.app
            (Y.smallEtaleTopology.yoneda.obj V)) = 𝟙 _ :=
    Φ.sheafFiber.map_id _
  have hr := representedSectionsBaseEquality_refl t f V
  exact (congrArg (fun k => k ≫ c) hm).trans
    ((Category.id_comp c).trans
      ((Category.comp_id c).symm.trans (congrArg (fun k => c ≫ k) hr.symm)))

end EtaleCohomology
