/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberSections
public import Nyll.EtaleCohomology.Descent.RepresentedFiberEtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionGeometricStalks
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionRepresentedBaseChange

/-!
# Actual represented geometric sections commute with étale restriction

The existing ordinary restriction stalk isomorphism and direct-image
restriction isomorphism intertwine the original geometric-fiber maps.
The proof retains each original germ and the existing pullback-pasting
isomorphisms, so affine proper bijectivity applies over arbitrary bases.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

namespace EtaleCohomology

variable {S U Y P : Scheme.{u}} (i : U ⟶ S) [Etale i] (q : Y ⟶ S)
  (p : P ⟶ U) (g : P ⟶ Y) [Etale g] (H : IsPullback p g i q)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (r : Spec (CommRingCat.of Ω) ⟶ U) (W : Y.Etale)

/-- Actual direct-image geometric sections commute with the original
étale restriction isomorphisms and the actual fiber section equivalence. -/
theorem etaleSetPushforwardRepresentableFiberSections_restriction :
    (etaleRestrictionGeometricStalkIso i r (Type u)
      ((etaleSetPushforward q).obj (Y.smallEtaleTopology.yoneda.obj W))).hom ≫
      etaleSetPushforwardRepresentableFiberSections q (r ≫ i) W ≫
        TypeCat.ofHom (representedFiberRestrictionEquiv i q p g H r W) =
    (Scheme.pointSmallEtale r).sheafFiber.map
      (etaleRestrictionPushforwardYonedaBaseChangeIso i q p g H W).hom ≫
        etaleSetPushforwardRepresentableFiberSections p r ((etaleBaseChange g).obj W) := by
  let F := (etaleSetPushforward q).obj (Y.smallEtaleTopology.yoneda.obj W)
  let Φ := Scheme.pointSmallEtale (r ≫ i)
  let Ψ := Scheme.pointSmallEtale r
  let E := (etaleRestrictionGeometricStalkIso i r (Type u) F).hom
  let B := (etaleRestrictionPushforwardYonedaBaseChangeIso i q p g H W).hom
  let Cq := etaleSetPushforwardRepresentableFiberSections q (r ≫ i) W
  let Cp := etaleSetPushforwardRepresentableFiberSections p r ((etaleBaseChange g).obj W)
  let D := TypeCat.ofHom (representedFiberRestrictionEquiv i q p g H r W)
  apply Ψ.presheafFiber_hom_ext
  intro V v
  let V₀ := (etalePostcompose i).obj V
  let v₀ : Φ.fiber.obj V₀ := Over.homMk v.left
    ((Category.assoc v.left V.hom i).symm.trans
      (congrArg (fun z : Spec (CommRingCat.of Ω) ⟶ U => z ≫ i) v.w))
  let γ := Ψ.toPresheafFiber V v ((etaleRestriction i (Type u)).obj F).obj
  let γ₀ := Φ.toPresheafFiber V₀ v₀ F.obj
  let γ₁ := Ψ.toPresheafFiber V v
    ((etaleSetPushforward p).obj (P.smallEtaleTopology.yoneda.obj ((etaleBaseChange g).obj W))).obj
  let b₀ := representedGeometricFiberGerm q (r ≫ i) W V₀ v₀
  let b₁ := representedGeometricFiberGerm p r ((etaleBaseChange g).obj W) V v
  have hE : γ ≫ E = γ₀ :=
    toPresheafFiber_etaleRestrictionGeometricStalkIso i r (Type u) F V v
  have hB : γ ≫ Ψ.sheafFiber.map B = B.hom.app (op V) ≫ γ₁ :=
    Ψ.toPresheafFiber_naturality B.hom V v
  have hq : γ₀ ≫ Cq = b₀ :=
    toPresheafFiber_etaleSetPushforwardRepresentableFiberSections q (r ≫ i) W V₀ v₀
  have hp : γ₁ ≫ Cp = b₁ :=
    toPresheafFiber_etaleSetPushforwardRepresentableFiberSections
      p r ((etaleBaseChange g).obj W) V v
  have hl : γ ≫ (E ≫ Cq ≫ D) = b₀ ≫ D :=
    (Category.assoc γ E (Cq ≫ D)).symm.trans
      ((congrArg (fun k => k ≫ Cq ≫ D) hE).trans
        ((Category.assoc γ₀ Cq D).symm.trans (congrArg (fun k => k ≫ D) hq)))
  have hr : γ ≫ (Ψ.sheafFiber.map B ≫ Cp) = B.hom.app (op V) ≫ b₁ :=
    (Category.assoc γ (Ψ.sheafFiber.map B) Cp).symm.trans
      ((congrArg (fun k => k ≫ Cp) hB).trans
        ((Category.assoc _ _ _).trans (congrArg (fun k => B.hom.app (op V) ≫ k) hp)))
  refine hl.trans (Eq.trans ?_ hr.symm)
  apply ConcreteCategory.hom_ext
  intro a
  let e := ((IsPullback.of_hasPullback r p).paste_vert H).isoPullback.hom
  let c := ((etaleRestrictionBaseChangeSiteIsoOfIsPullback i q p g H).hom.app V).left
  let m := ((Over.pullback p).map v).left
  let n := ((Over.pullback q).map v₀).left
  let b := B.hom.app (op V) a
  have he₁ : e ≫ pullback.fst (r ≫ i) q = pullback.fst r p :=
    ((IsPullback.of_hasPullback r p).paste_vert H).isoPullback_hom_fst
  have he₂ : e ≫ pullback.snd (r ≫ i) q = pullback.snd r p ≫ g :=
    ((IsPullback.of_hasPullback r p).paste_vert H).isoPullback_hom_snd
  have hc₁ : c ≫ pullback.fst (V.hom ≫ i) q = pullback.fst V.hom p :=
    ((IsPullback.of_hasPullback V.hom p).paste_vert H).isoPullback_hom_fst
  have hc₂ : c ≫ pullback.snd (V.hom ≫ i) q = pullback.snd V.hom p ≫ g :=
    ((IsPullback.of_hasPullback V.hom p).paste_vert H).isoPullback_hom_snd
  have hm₁ : m ≫ pullback.fst V.hom p = pullback.fst r p ≫ v.left :=
    pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd V.hom p = pullback.snd r p := pullback.lift_snd _ _ _
  have hn₁ : n ≫ pullback.fst (V.hom ≫ i) q = pullback.fst (r ≫ i) q ≫ v.left :=
    pullback.lift_fst _ _ _
  have hn₂ : n ≫ pullback.snd (V.hom ≫ i) q = pullback.snd (r ≫ i) q :=
    pullback.lift_snd _ _ _
  have heq : e ≫ n = m ≫ c := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun k => e ≫ k) hn₁).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun k => k ≫ v.left) he₁).trans
              (hm₁.symm.trans
                ((congrArg (fun k => m ≫ k) hc₁.symm).trans
                  (Category.assoc _ _ _).symm)))))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun k => e ≫ k) hn₂).trans
          (he₂.trans
            ((congrArg (fun k => k ≫ g) hm₂.symm).trans
              ((Category.assoc _ _ _).trans
                ((congrArg (fun k => m ≫ k) hc₂.symm).trans
                  (Category.assoc _ _ _).symm)))))
  have hb₁ : b.left ≫ pullback.fst W.hom g = c ≫ a.left :=
    etaleRestrictionPushforwardYonedaBaseChangeIso_hom_app_fst i q p g H W V a
  have hb₂ : b.left ≫ pullback.snd W.hom g = pullback.snd V.hom p := b.w
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hD := representedFiberRestrictionEquiv_fst i q p g H r W (b₀ a)
    change (representedFiberRestrictionEquiv i q p g H r W (b₀ a)).left ≫
        pullback.fst W.hom g = (m ≫ b.left) ≫ pullback.fst W.hom g
    exact hD.trans
      ((Category.assoc e n a.left).symm.trans
        ((congrArg (fun k => k ≫ a.left) heq).trans
          ((Category.assoc m c a.left).trans
            ((congrArg (fun k => m ≫ k) hb₁.symm).trans
              (Category.assoc m b.left (pullback.fst W.hom g)).symm))))
  · have hD := representedFiberRestrictionEquiv_snd i q p g H r W (b₀ a)
    exact hD.trans
      (hm₂.symm.trans
        ((congrArg (fun k => m ≫ k) hb₂.symm).trans
          (Category.assoc m b.left (pullback.snd W.hom g)).symm))

end EtaleCohomology
