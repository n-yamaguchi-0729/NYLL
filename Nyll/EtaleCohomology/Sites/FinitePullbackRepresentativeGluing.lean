/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.SigmaRepresenter
import Nyll.EtaleCohomology.Sites.FinitePullbackRepresentatives
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# One affine representative cover for an inverse-image section

The finitely many affine representatives of an inverse-image section glue
on their disjoint union. The source of the resulting cover and the original
étale object are affine. The cover embeds as an actual open subscheme of
the native base change, and the glued section satisfies the original
inverse-image unit equation.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private theorem baseChangeMap_isOpenImmersion
    {X Y : Scheme.{u}} (q : Y ⟶ X) {U V : X.Etale} (g : U ⟶ V)
    [IsOpenImmersion g.left] : IsOpenImmersion ((etaleBaseChange q).map g).left :=
  MorphismProperty.pullbackLift_fst_snd
    (P := show MorphismProperty Scheme.{u} from @IsOpenImmersion) q g.w.symm
    (inferInstanceAs (IsOpenImmersion g.left))

/-- A section of actual inverse image over a quasi-compact scheme has one
affine representative on an affine surjective étale cover. The covering
domain is an open subscheme of the native base-changed representative. -/
theorem exists_affine_pullback_representative_cover
    {X Y : Scheme.{u}} (q : Y ⟶ X) [QuasiCompact (terminal.from Y)]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    let G := (etalePullback q Λ).obj F
    let η : F ⟶ (etalePushforward q Λ).obj G :=
      (etalePullbackPushforwardAdjunction q Λ).unit.app F
    ∀ b : G.obj.obj (op (Scheme.Etale.mk (𝟙 Y))),
      ∃ (U : X.Etale) (a : F.obj.obj (op U)) (V : Y.Etale)
        (d : V ⟶ (etaleBaseChange q).obj U),
        IsAffine U.left ∧ IsAffine V.left ∧ IsOpenImmersion d.left ∧
        Surjective V.hom ∧
        G.obj.map d.op (η.hom.app (op U) a) = G.obj.map
          (MorphismProperty.Over.homMk
            (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
            V.hom (Category.comp_id _) : V ⟶ Scheme.Etale.mk (𝟙 Y)).op b := by
  classical
  intro G η b
  obtain ⟨K, U, V, d, a, hU, hV, hd, hCover, heq⟩ :=
    exists_finite_affine_pullback_representatives q Λ F b
  have (i : K) : IsAffine (U i).left := hU i
  have (i : K) : IsAffine (V i).left := hV i
  have (i : K) : IsOpenImmersion (d i).left := hd i
  let U₀ : X.Etale := etaleSigma U
  let V₀ : Y.Etale := etaleSigma V
  let B : Y.Etale := (etaleBaseChange q).obj U₀
  let j (i : K) : (etaleBaseChange q).obj (U i) ⟶ B :=
    (etaleBaseChange q).map (etaleSigmaInj U i)
  have (i : K) : IsOpenImmersion (etaleSigmaInj U i).left :=
    inferInstanceAs (IsOpenImmersion (Sigma.ι (fun k : K => (U k).left) i))
  have (i : K) : IsOpenImmersion (j i).left :=
    baseChangeMap_isOpenImmersion q (etaleSigmaInj U i)
  let α (i : K) : (V i).left ⟶ B.left := (d i).left ≫ (j i).left
  have (i : K) : IsOpenImmersion (α i) := inferInstanceAs
    (IsOpenImmersion ((d i).left ≫ (j i).left))
  let π : B.left ⟶ U₀.left := pullback.fst U₀.hom q
  let β (i : K) : (V i).left ⟶ (U i).left :=
    (d i).left ≫ pullback.fst (U i).hom q
  have hjπ (i : K) : (j i).left ≫ π =
      pullback.fst (U i).hom q ≫ (etaleSigmaInj U i).left :=
    pullback.lift_fst _ _ _
  have hαπ (i : K) : α i ≫ π = β i ≫ (etaleSigmaInj U i).left :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => (d i).left ≫ k) (hjπ i)).trans (Category.assoc _ _ _).symm)
  have hdisj : Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx⟩ ⟨y, hy⟩
    have he : α i x = α j y := hx.trans hy.symm
    have hpoint (k : K) (v : (V k).left) :
        π (α k v) = (etaleSigmaInj U k).left (β k v) :=
      (Scheme.Hom.comp_apply _ _ _).symm.trans
        ((congrArg (fun l => l v) (hαπ k)).trans (Scheme.Hom.comp_apply _ _ _))
    have hs : (etaleSigmaInj U i).left (β i x) =
        (etaleSigmaInj U j).left (β j y) :=
      (hpoint i x).symm.trans ((congrArg π he).trans (hpoint j y))
    exact hij (congrArg Sigma.fst
      ((sigmaι_eq_iff (fun k : K => (U k).left) i j _ _).mp hs))
  let l : V₀.left ⟶ B.left := Sigma.desc α
  have : IsOpenImmersion l := isOpenImmersion_sigmaDesc
    (fun i : K => (V i).left) α hdisj
  have hl : l ≫ B.hom = V₀.hom := by
    apply Sigma.hom_ext
    intro i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ B.hom) (Sigma.ι_comp_desc α i)).trans
        (((d i ≫ j i).w).trans (etaleSigmaInj V i).w.symm))
  let d₀ : V₀ ⟶ B := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) l hl
  have hd₀ (i : K) : etaleSigmaInj V i ≫ d₀ = d i ≫ j i :=
    MorphismProperty.Over.Hom.ext (Sigma.ι_comp_desc α i)
  have hcover := (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mp hCover
  have hsurj : Surjective V₀.hom := Surjective.sigmaDesc_of_union_range_eq_univ
    (f := fun i : K => (V i).hom) hcover
  let FT : Sheaf X.smallEtaleTopology (Type u) :=
    (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u} Λ))).obj F
  let GT : Sheaf Y.smallEtaleTopology (Type u) :=
    (sheafCompose Y.smallEtaleTopology (forget (ModuleCat.{u} Λ))).obj G
  let a₀ : F.obj.obj (op U₀) := etaleSigmaSection U FT a
  have ha (i : K) : F.obj.map (etaleSigmaInj U i).op a₀ = a i :=
    etaleSigmaSection_restrict U FT a i
  let r : V₀ ⟶ Scheme.Etale.mk (𝟙 Y) := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    V₀.hom (Category.comp_id _)
  let ri (i : K) : V i ⟶ Scheme.Etale.mk (𝟙 Y) := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    (V i).hom (Category.comp_id _)
  have hri (i : K) : etaleSigmaInj V i ≫ r = ri i :=
    MorphismProperty.Over.Hom.ext (etaleSigmaInj V i).w
  have hsection : G.obj.map d₀.op (η.hom.app (op U₀) a₀) = G.obj.map r.op b := by
    apply etaleSigmaSection_ext V GT
    intro i
    have hn : η.hom.app (op (U i)) (F.obj.map (etaleSigmaInj U i).op a₀) =
        G.obj.map (j i).op (η.hom.app (op U₀) a₀) :=
      η.hom.naturality_apply (etaleSigmaInj U i).op a₀
    have hη : G.obj.map (j i).op (η.hom.app (op U₀) a₀) =
        η.hom.app (op (U i)) (a i) :=
      hn.symm.trans (congrArg (η.hom.app (op (U i))) (ha i))
    have hleft : G.obj.map (etaleSigmaInj V i).op
        (G.obj.map d₀.op (η.hom.app (op U₀) a₀)) =
        G.obj.map (d i).op (η.hom.app (op (U i)) (a i)) :=
      (G.obj.map_comp_apply d₀.op (etaleSigmaInj V i).op _).symm.trans
        ((congrArg (fun k => G.obj.map k.op (η.hom.app (op U₀) a₀)) (hd₀ i)).trans
          ((G.obj.map_comp_apply (j i).op (d i).op _).trans
            (congrArg (G.obj.map (d i).op) hη)))
    have hright : G.obj.map (etaleSigmaInj V i).op (G.obj.map r.op b) =
        G.obj.map (ri i).op b :=
      (G.obj.map_comp_apply r.op (etaleSigmaInj V i).op b).symm.trans
        (congrArg (fun k => G.obj.map k.op b) (hri i))
    exact hleft.trans ((heq i).trans hright.symm)
  exact ⟨U₀, a₀, V₀, d₀,
    inferInstanceAs (IsAffine (∐ fun i : K => (U i).left)),
    inferInstanceAs (IsAffine (∐ fun i : K => (V i).left)),
    inferInstanceAs (IsOpenImmersion l), hsurj, hsection⟩

end EtaleCohomology
