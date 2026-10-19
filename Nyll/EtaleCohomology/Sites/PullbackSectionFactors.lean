/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.PullbackSections

/-!
# Restriction through actual inverse-image section factors

Restricting an original section and then pulling it through a local factor
agrees with pulling it through the composite factor. The proof retains the
chosen inverse-image unit and the literal maps into native scheme pullbacks.
This supplies compatibility for section cocones over pointed neighborhoods.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

universe u

variable {X Y : Scheme.{u}} (q : Y ⟶ X)

/-- A local factor composed with an original-site arrow induces the
composite of the corresponding actual base-change arrows. -/
theorem etaleBaseChangeLift_comp
    {U : Y.Etale} {V W : X.Etale} (a : V ⟶ W)
    (l : U.left ⟶ V.left) (hl : l ≫ V.hom = U.hom ≫ q)
    (hla : (l ≫ a.left) ≫ W.hom = U.hom ≫ q) :
    etaleBaseChangeLift q l hl ≫ (etaleBaseChange q).map a =
      etaleBaseChangeLift q (l ≫ a.left) hla := by
  let d : U ⟶ (etaleBaseChange q).obj V := etaleBaseChangeLift q l hl
  let e : U ⟶ (etaleBaseChange q).obj W :=
    etaleBaseChangeLift q (l ≫ a.left) hla
  let m : ((etaleBaseChange q).obj V).left ⟶ ((etaleBaseChange q).obj W).left :=
    ((etaleBaseChange q).map a).left
  have hm₁ : m ≫ pullback.fst W.hom q = pullback.fst V.hom q ≫ a.left :=
    pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd W.hom q = pullback.snd V.hom q :=
    pullback.lift_snd _ _ _
  have hd₁ : d.left ≫ pullback.fst V.hom q = l := pullback.lift_fst _ _ _
  have hd₂ : d.left ≫ pullback.snd V.hom q = U.hom := pullback.lift_snd _ _ _
  have he₁ : e.left ≫ pullback.fst W.hom q = l ≫ a.left := pullback.lift_fst _ _ _
  have he₂ : e.left ≫ pullback.snd W.hom q = U.hom := pullback.lift_snd _ _ _
  apply MorphismProperty.Over.Hom.ext
  change d.left ≫ m = e.left
  apply pullback.hom_ext
  · exact (Category.assoc d.left m (pullback.fst W.hom q)).trans
      ((congrArg (fun t => d.left ≫ t) hm₁).trans
        ((Category.assoc d.left (pullback.fst V.hom q) a.left).symm.trans
          ((congrArg (fun t => t ≫ a.left) hd₁).trans he₁.symm)))
  · exact (Category.assoc d.left m (pullback.snd W.hom q)).trans
      ((congrArg (fun t => d.left ≫ t) hm₂).trans (hd₂.trans he₂.symm))

/-- Original-site restriction commutes with the actual local-factor
section map, for arbitrary module sheaves and arbitrary base morphisms. -/
theorem etalePullbackSectionMap_restriction
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {U : Y.Etale} {V W : X.Etale} (a : V ⟶ W)
    (l : U.left ⟶ V.left) (hl : l ≫ V.hom = U.hom ≫ q)
    (hla : (l ≫ a.left) ≫ W.hom = U.hom ≫ q) :
    F.obj.map a.op ≫ etalePullbackSectionMap q Λ F l hl =
      etalePullbackSectionMap q Λ F (l ≫ a.left) hla := by
  let G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) := (etalePullback q Λ).obj F
  let η : F ⟶ (etalePushforward q Λ).obj G :=
    (etalePullbackPushforwardAdjunction q Λ).unit.app F
  let d : U ⟶ (etaleBaseChange q).obj V := etaleBaseChangeLift q l hl
  let e : U ⟶ (etaleBaseChange q).obj W :=
    etaleBaseChangeLift q (l ≫ a.left) hla
  let aq : (etaleBaseChange q).obj V ⟶ (etaleBaseChange q).obj W :=
    (etaleBaseChange q).map a
  let ηV : F.obj.obj (op V) ⟶ G.obj.obj (op ((etaleBaseChange q).obj V)) :=
    η.hom.app (op V)
  let ηW : F.obj.obj (op W) ⟶ G.obj.obj (op ((etaleBaseChange q).obj W)) :=
    η.hom.app (op W)
  have hη : F.obj.map a.op ≫ ηV = ηW ≫ G.obj.map aq.op := η.hom.naturality a.op
  have he : d ≫ aq = e := etaleBaseChangeLift_comp q a l hl hla
  have hr : G.obj.map aq.op ≫ G.obj.map d.op = G.obj.map e.op :=
    (G.obj.map_comp aq.op d.op).symm.trans
      (congrArg (fun k : U ⟶ (etaleBaseChange q).obj W => G.obj.map k.op) he)
  change F.obj.map a.op ≫ (ηV ≫ G.obj.map d.op) = ηW ≫ G.obj.map e.op
  rw [← Category.assoc, hη, Category.assoc, hr]

/-- The restriction formula with a specified equal composite factor.
Keeping this congruence at the generic site level avoids unfolding a
geometric-stalk construction when building section cocones. -/
theorem etalePullbackSectionMap_restriction_of_comp_eq
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {U : Y.Etale} {V W : X.Etale} (a : V ⟶ W)
    (l : U.left ⟶ V.left) (hl : l ≫ V.hom = U.hom ≫ q)
    (m : U.left ⟶ W.left) (hm : m ≫ W.hom = U.hom ≫ q)
    (heq : l ≫ a.left = m) :
    F.obj.map a.op ≫ etalePullbackSectionMap q Λ F l hl =
      etalePullbackSectionMap q Λ F m hm := by
  subst m
  exact etalePullbackSectionMap_restriction q Λ F a l hl hm

/-- Restriction on the source site commutes with the native arrow
associated to a local factor. -/
theorem etaleBaseChangeLift_precomp
    {U V : Y.Etale} {W : X.Etale} (a : U ⟶ V)
    (l : V.left ⟶ W.left) (hl : l ≫ W.hom = V.hom ≫ q)
    (hal : (a.left ≫ l) ≫ W.hom = U.hom ≫ q) :
    a ≫ etaleBaseChangeLift q l hl =
      etaleBaseChangeLift q (a.left ≫ l) hal := by
  let d : V ⟶ (etaleBaseChange q).obj W := etaleBaseChangeLift q l hl
  let e : U ⟶ (etaleBaseChange q).obj W :=
    etaleBaseChangeLift q (a.left ≫ l) hal
  have hd₁ : d.left ≫ pullback.fst W.hom q = l := pullback.lift_fst _ _ _
  have hd₂ : d.left ≫ pullback.snd W.hom q = V.hom := pullback.lift_snd _ _ _
  have he₁ : e.left ≫ pullback.fst W.hom q = a.left ≫ l := pullback.lift_fst _ _ _
  have he₂ : e.left ≫ pullback.snd W.hom q = U.hom := pullback.lift_snd _ _ _
  apply MorphismProperty.Over.Hom.ext
  change a.left ≫ d.left = e.left
  apply pullback.hom_ext
  · exact (Category.assoc a.left d.left (pullback.fst W.hom q)).trans
      ((congrArg (fun t => a.left ≫ t) hd₁).trans he₁.symm)
  · exact (Category.assoc a.left d.left (pullback.snd W.hom q)).trans
      ((congrArg (fun t => a.left ≫ t) hd₂).trans (a.w.trans he₂.symm))

/-- Source-site restriction commutes with the actual local-factor
section map, preserving the chosen inverse-image unit. -/
theorem etalePullbackSectionMap_source_restriction
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {U V : Y.Etale} {W : X.Etale} (a : U ⟶ V)
    (l : V.left ⟶ W.left) (hl : l ≫ W.hom = V.hom ≫ q)
    (hal : (a.left ≫ l) ≫ W.hom = U.hom ≫ q) :
    etalePullbackSectionMap q Λ F l hl ≫ ((etalePullback q Λ).obj F).obj.map a.op =
      etalePullbackSectionMap q Λ F (a.left ≫ l) hal := by
  let G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) := (etalePullback q Λ).obj F
  let d : V ⟶ (etaleBaseChange q).obj W := etaleBaseChangeLift q l hl
  let e : U ⟶ (etaleBaseChange q).obj W :=
    etaleBaseChangeLift q (a.left ≫ l) hal
  let ηW : F.obj.obj (op W) ⟶ G.obj.obj (op ((etaleBaseChange q).obj W)) :=
    ((etalePullbackPushforwardAdjunction q Λ).unit.app F).hom.app (op W)
  have he : a ≫ d = e := etaleBaseChangeLift_precomp q a l hl hal
  have hr : G.obj.map d.op ≫ G.obj.map a.op = G.obj.map e.op :=
    (G.obj.map_comp d.op a.op).symm.trans
      (congrArg (fun k : U ⟶ (etaleBaseChange q).obj W => G.obj.map k.op) he)
  change (ηW ≫ G.obj.map d.op) ≫ G.obj.map a.op = ηW ≫ G.obj.map e.op
  exact (Category.assoc ηW (G.obj.map d.op) (G.obj.map a.op)).trans
    (congrArg (fun t => ηW ≫ t) hr)

/-- A commuting square of local factors gives the literal naturality
square on sections of the original sheaf and its actual inverse image. -/
theorem etalePullbackSectionMap_square
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {U₁ U₂ : Y.Etale} {V₁ V₂ : X.Etale} (a : U₁ ⟶ U₂) (b : V₁ ⟶ V₂)
    (l₁ : U₁.left ⟶ V₁.left) (hl₁ : l₁ ≫ V₁.hom = U₁.hom ≫ q)
    (l₂ : U₂.left ⟶ V₂.left) (hl₂ : l₂ ≫ V₂.hom = U₂.hom ≫ q)
    (hsquare : l₁ ≫ b.left = a.left ≫ l₂) :
    F.obj.map b.op ≫ etalePullbackSectionMap q Λ F l₁ hl₁ =
      etalePullbackSectionMap q Λ F l₂ hl₂ ≫ ((etalePullback q Λ).obj F).obj.map a.op := by
  have ha : (a.left ≫ l₂) ≫ V₂.hom = U₁.hom ≫ q :=
    (Category.assoc a.left l₂ V₂.hom).trans
      ((congrArg (fun t => a.left ≫ t) hl₂).trans
        ((Category.assoc a.left U₂.hom q).symm.trans
          (congrArg (fun t => t ≫ q) a.w)))
  exact (etalePullbackSectionMap_restriction_of_comp_eq q Λ F b l₁ hl₁
    (a.left ≫ l₂) ha hsquare).trans
      (etalePullbackSectionMap_source_restriction q Λ F a l₂ hl₂ ha).symm

end EtaleCohomology
