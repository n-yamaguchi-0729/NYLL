/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.Subcanonical
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Represented coefficients under actual étale base change

The existing postcomposition/base-change adjunction identifies ordinary
restriction of a representable sheaf with the actual base-changed
representer. Composing this with the existing direct-image restriction
isomorphism retains the original pullback-pasting map on every section.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Restriction of a represented sheaf is represented by actual scheme base change,
using the existing site adjunction's Yoneda isomorphism. -/
def etaleRestrictionYonedaObjIso
    {P Y : Scheme.{u}} (g : P ⟶ Y) [Etale g] (W : Y.Etale) :
    (etaleRestriction g (Type u)).obj (Y.smallEtaleTopology.yoneda.obj W) ≅
      P.smallEtaleTopology.yoneda.obj ((etaleBaseChange g).obj W) :=
  (fullyFaithfulSheafToPresheaf P.smallEtaleTopology (Type u)).preimageIso
    ((etalePostcomposeBaseChangeAdjunction g).compYonedaIso.app W).symm

/-- The represented restriction isomorphism is the literal site Hom adjunction. -/
theorem etaleRestrictionYonedaObjIso_hom_app
    {P Y : Scheme.{u}} (g : P ⟶ Y) [Etale g] (W : Y.Etale) (V : P.Etale)
    (a : (etalePostcompose g).obj V ⟶ W) :
    (etaleRestrictionYonedaObjIso g W).hom.hom.app (op V) a =
      (etalePostcomposeBaseChangeAdjunction g).homEquiv V W a := by
  let F := (etaleRestriction g (Type u)).obj (Y.smallEtaleTopology.yoneda.obj W)
  let G := P.smallEtaleTopology.yoneda.obj ((etaleBaseChange g).obj W)
  let α : F.obj ⟶ G.obj := ((etalePostcomposeBaseChangeAdjunction g).compYonedaIso.app W).inv
  have h : (etaleRestrictionYonedaObjIso g W).hom.hom = α :=
    (fullyFaithfulSheafToPresheaf P.smallEtaleTopology (Type u)).map_preimage
      (X := F) (Y := G) α
  exact congrArg (fun z : F.obj ⟶ G.obj => z.app (op V) a) h

/-- Actual direct image restricted through an étale cartesian square, with
represented coefficients kept as the original base-changed representer. -/
def etaleRestrictionPushforwardYonedaBaseChangeIso
    {S U Y P : Scheme.{u}} (i : U ⟶ S) [Etale i] (q : Y ⟶ S)
    (p : P ⟶ U) (g : P ⟶ Y) [Etale g] (H : IsPullback p g i q) (W : Y.Etale) :
    (etaleRestriction i (Type u)).obj
        ((etaleSetPushforward q).obj (Y.smallEtaleTopology.yoneda.obj W)) ≅
      (etaleSetPushforward p).obj
        (P.smallEtaleTopology.yoneda.obj ((etaleBaseChange g).obj W)) :=
  (etaleRestrictionPushforwardBaseChangeIsoOfIsPullback i q (Type u) p g H).app
      (Y.smallEtaleTopology.yoneda.obj W) ≪≫
    (etaleSetPushforward p).mapIso (etaleRestrictionYonedaObjIso g W)

/-- The original base-change isomorphism first precomposes with actual pullback
pasting and then applies the original postcomposition/base-change adjunction. -/
theorem etaleRestrictionPushforwardYonedaBaseChangeIso_hom_app
    {S U Y P : Scheme.{u}} (i : U ⟶ S) [Etale i] (q : Y ⟶ S)
    (p : P ⟶ U) (g : P ⟶ Y) [Etale g] (H : IsPullback p g i q) (W : Y.Etale)
    (V : U.Etale) (a : (etaleBaseChange q).obj ((etalePostcompose i).obj V) ⟶ W) :
    (etaleRestrictionPushforwardYonedaBaseChangeIso i q p g H W).hom.hom.app (op V) a =
      (etalePostcomposeBaseChangeAdjunction g).homEquiv ((etaleBaseChange p).obj V) W
        ((etaleRestrictionBaseChangeSiteIsoOfIsPullback i q p g H).hom.app V ≫ a) := by
  let b : (etalePostcompose g).obj ((etaleBaseChange p).obj V) ⟶ W :=
    ((etaleRestrictionPushforwardBaseChangeIsoOfIsPullback i q (Type u) p g H).app
      (Y.smallEtaleTopology.yoneda.obj W)).hom.hom.app (op V) a
  have hb : b = (etaleRestrictionBaseChangeSiteIsoOfIsPullback i q p g H).hom.app V ≫ a := rfl
  exact (etaleRestrictionYonedaObjIso_hom_app g W ((etaleBaseChange p).obj V) b).trans
    (congrArg (fun z : (etalePostcompose g).obj ((etaleBaseChange p).obj V) ⟶ W =>
      (etalePostcomposeBaseChangeAdjunction g).homEquiv ((etaleBaseChange p).obj V) W z) hb)

/-- The actual represented base-change section retains the original map to its representer. -/
theorem etaleRestrictionPushforwardYonedaBaseChangeIso_hom_app_fst
    {S U Y P : Scheme.{u}} (i : U ⟶ S) [Etale i] (q : Y ⟶ S)
    (p : P ⟶ U) (g : P ⟶ Y) [Etale g] (H : IsPullback p g i q) (W : Y.Etale)
    (V : U.Etale) (a : (etaleBaseChange q).obj ((etalePostcompose i).obj V) ⟶ W) :
    ((etaleRestrictionPushforwardYonedaBaseChangeIso i q p g H W).hom.hom.app
        (op V) a).left ≫ pullback.fst W.hom g =
      ((etaleRestrictionBaseChangeSiteIsoOfIsPullback i q p g H).hom.app V).left ≫ a.left := by
  have hb := etaleRestrictionPushforwardYonedaBaseChangeIso_hom_app i q p g H W V a
  let b := (etaleRestrictionBaseChangeSiteIsoOfIsPullback i q p g H).hom.app V ≫ a
  let adj := etalePostcomposeBaseChangeAdjunction g
  have he := (adj.homEquiv ((etaleBaseChange p).obj V) W).symm_apply_apply b
  rw [Adjunction.homEquiv_counit] at he
  exact (congrArg (fun z : (etaleBaseChange p).obj V ⟶ (etaleBaseChange g).obj W =>
    z.left ≫ pullback.fst W.hom g) hb).trans
      (congrArg (fun z : (etalePostcompose g).obj ((etaleBaseChange p).obj V) ⟶ W =>
        z.left) he)

end EtaleCohomology
