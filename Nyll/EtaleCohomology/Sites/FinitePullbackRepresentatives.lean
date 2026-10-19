/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.PullbackLocalRepresentatives
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.FieldTheory.SeparableClosure

/-!
# Finite affine representatives of inverse-image sections

A section of actual inverse image over a quasi-compact scheme is
represented on a finite affine étale cover by sections on affine étale
objects of the original scheme. The maps into their native base changes
are open immersions. The proof refines the actual local equality opens
and then takes a finite subcover; no continuity or descent hypothesis on
the arbitrary coefficient sheaf is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

universe u

private theorem exists_affine_pullback_representative_at_point
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    let G := (etalePullback q Λ).obj F
    let η : F ⟶ (etalePushforward q Λ).obj G :=
      (etalePullbackPushforwardAdjunction q Λ).unit.app F
    ∀ (b : G.obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) (y : Y),
      ∃ (U : X.Etale) (a : F.obj.obj (op U)) (V : Y.Etale)
        (d : V ⟶ (etaleBaseChange q).obj U),
        IsAffine U.left ∧ IsAffine V.left ∧ IsOpenImmersion d.left ∧
        y ∈ Set.range V.hom ∧
        G.obj.map d.op (η.hom.app (op U) a) = G.obj.map
          (MorphismProperty.Over.homMk
            (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
            V.hom (Category.comp_id _) : V ⟶ Scheme.Etale.mk (𝟙 Y)).op b := by
  intro G η b y
  let Ω := SeparableClosure (Y.residueField y)
  let s : Spec (CommRingCat.of Ω) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
      Y.fromSpecResidueField y
  let ξ : Spec (CommRingCat.of Ω) := default
  have hs : s ξ = y := by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply y _
  obtain ⟨U, u, hU, a, W, hzW, heqW⟩ :=
    exists_affine_pullback_local_representative q s Λ F b
  let B : Y.Etale := (etaleBaseChange q).obj U
  let z : Spec (CommRingCat.of Ω) ⟶ B.left :=
    (etalePushforwardGeometricLift q (s ≫ q) ⟨s, rfl⟩ U u).left
  have hz : z ≫ B.hom = s := pullback.lift_snd _ _ _
  change z ξ ∈ W at hzW
  obtain ⟨A, hA, hzA, hAW⟩ := exists_isAffineOpen_mem_and_subset hzW
  let V : Y.Etale := Scheme.Etale.mk (A.ι ≫ B.hom)
  let O : Y.Etale := Scheme.Etale.mk (W.ι ≫ B.hom)
  let d : V ⟶ B := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) A.ι rfl
  let j : O ⟶ B := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl
  let g : B ⟶ Scheme.Etale.mk (𝟙 Y) := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      B.hom (Category.comp_id _)
  let r : V ⟶ Scheme.Etale.mk (𝟙 Y) := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      V.hom (Category.comp_id _)
  let e : V ⟶ O := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      (B.left.homOfLE hAW) (by
        exact (Category.assoc (B.left.homOfLE hAW) W.ι B.hom).symm.trans
          (congrArg (fun t => t ≫ B.hom) (Scheme.homOfLE_ι B.left hAW)))
  have hed : e ≫ j = d := MorphismProperty.Over.Hom.ext (Scheme.homOfLE_ι B.left hAW)
  have hdg : d ≫ g = r := MorphismProperty.Over.Hom.ext rfl
  have her : e ≫ (j ≫ g) = r := by
    rw [← Category.assoc, hed, hdg]
  change G.obj.map j.op (η.hom.app (op U) a) = G.obj.map (j ≫ g).op b at heqW
  have heq : G.obj.map d.op (η.hom.app (op U) a) = G.obj.map r.op b := by
    have hleft (x : G.obj.obj (op B)) :
        G.obj.map d.op x = G.obj.map e.op (G.obj.map j.op x) :=
      (congrArg (fun t : V ⟶ B => G.obj.map t.op x) hed).symm.trans
        (G.obj.map_comp_apply j.op e.op x)
    have hright (x : G.obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) :
        G.obj.map r.op x = G.obj.map e.op (G.obj.map (j ≫ g).op x) :=
      (congrArg (fun t : V ⟶ Scheme.Etale.mk (𝟙 Y) => G.obj.map t.op x) her).symm.trans
        (G.obj.map_comp_apply (j ≫ g).op e.op x)
    exact (hleft _).trans ((congrArg (G.obj.map e.op) heqW).trans (hright b).symm)
  have hy : y ∈ Set.range V.hom := by
    refine ⟨⟨z ξ, hzA⟩, ?_⟩
    exact (Scheme.Hom.comp_apply A.ι B.hom ⟨z ξ, hzA⟩).trans
      ((Scheme.Hom.comp_apply z B.hom ξ).symm.trans
        ((congrArg (fun t : Spec (CommRingCat.of Ω) ⟶ Y => t ξ) hz).trans hs))
  exact ⟨U, a, V, d, hU, hA, inferInstanceAs (IsOpenImmersion A.ι), hy, heq⟩

/-- An arbitrary inverse-image section over a quasi-compact scheme has
finitely many affine representatives from the original étale site. Their
domains are actual open subobjects of the native base-changed objects. -/
theorem exists_finite_affine_pullback_representatives
    {X Y : Scheme.{u}} (q : Y ⟶ X) [QuasiCompact (terminal.from Y)]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    let G := (etalePullback q Λ).obj F
    let η : F ⟶ (etalePushforward q Λ).obj G :=
      (etalePullbackPushforwardAdjunction q Λ).unit.app F
    ∀ b : G.obj.obj (op (Scheme.Etale.mk (𝟙 Y))),
      ∃ (K : Finset Y) (U : K → X.Etale) (V : K → Y.Etale)
        (d : ∀ i, V i ⟶ (etaleBaseChange q).obj (U i))
        (a : ∀ i, F.obj.obj (op (U i))),
        (∀ i, IsAffine (U i).left) ∧ (∀ i, IsAffine (V i).left) ∧
        (∀ i, IsOpenImmersion (d i).left) ∧
        Sieve.ofArrows V (fun i => (MorphismProperty.Over.homMk
          (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
          (V i).hom (Category.comp_id _) : V i ⟶ Scheme.Etale.mk (𝟙 Y))) ∈
            Y.smallEtaleTopology (Scheme.Etale.mk (𝟙 Y)) ∧
        ∀ i, G.obj.map (d i).op (η.hom.app (op (U i)) (a i)) = G.obj.map
          (MorphismProperty.Over.homMk
            (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
            (V i).hom (Category.comp_id _) : V i ⟶ Scheme.Etale.mk (𝟙 Y)).op b := by
  classical
  intro G η b
  choose U a V d hU hV hd hy heq using exists_affine_pullback_representative_at_point q Λ F b
  have : CompactSpace Y := (AlgebraicGeometry.compactSpace_iff_quasiCompact Y).2 inferInstance
  obtain ⟨K, hK⟩ := (isCompact_univ : IsCompact (Set.univ : Set Y)).elim_finite_subcover
    (fun y : Y => Set.range (V y).hom)
    (fun y => (V y).hom.isOpenMap.isOpen_range)
    (by intro y _; exact Set.mem_iUnion.mpr ⟨y, hy y⟩)
  refine ⟨K, (fun i => U i.1), (fun i => V i.1), (fun i => d i.1),
    (fun i => a i.1), (fun i => hU i.1), (fun i => hV i.1), (fun i => hd i.1), ?_,
    (fun i => heq i.1)⟩
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨i, hi, hiy⟩ := Set.mem_iUnion₂.mp (hK (Set.mem_univ y))
  exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hiy⟩

end EtaleCohomology
