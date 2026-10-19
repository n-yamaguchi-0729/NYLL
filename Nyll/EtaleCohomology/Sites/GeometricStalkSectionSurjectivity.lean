/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.FinitePullbackRepresentativeGluing
import Nyll.EtaleCohomology.Sites.GeometricStalkMatchedCoverDescent
import Nyll.EtaleCohomology.Sites.GeometricStalkSectionComparison
import Nyll.EtaleCohomology.Sites.PullbackRepresentativeOverlap

/-!
# Surjectivity of the actual strict-local section comparison

A section of actual inverse image has one finite affine representative
cover. The representative's native overlap lies in the original equality
open. Descending that finite geometric matching datum gives an actual
étale neighborhood and a compatible cover on which the original sheaf
can be glued. Literal section-square identities recover the given section.

This proves the surjective half of degree-zero continuity for arbitrary
module sheaves under a quasi-compact quasi-separated morphism (Stacks
Project, Theorem 59.53.1), with the constructed strict-local ring and its
actual stalk comparison map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

universe u

private theorem pulledSection_eq_of_descended_representative
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (B C U : X.Etale) (V : Y.Etale) [Surjective V.hom]
    (p : C ⟶ B) (r : C ⟶ U)
    (v : V ⟶ Scheme.Etale.mk (𝟙 Y))
    (n : Y ⟶ B.left) (hn : n ≫ B.hom = (𝟙 Y) ≫ q)
    (h : V.left ⟶ C.left) (hh : h ≫ C.hom = V.hom ≫ q)
    (l : V.left ⟶ U.left) (hl : l ≫ U.hom = V.hom ≫ q)
    (hp : h ≫ p.left = v.left ≫ n) (hr : h ≫ r.left = l)
    (aB : F.obj.obj (op B)) (a : F.obj.obj (op U))
    (b : ((etalePullback q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))))
    (haB : F.obj.map p.op aB = F.obj.map r.op a)
    (ha : etalePullbackSectionMap q Λ F (U := V) l hl a =
      ((etalePullback q Λ).obj F).obj.map v.op b) :
    etalePullbackSectionMap q Λ F (U := Scheme.Etale.mk (𝟙 Y)) n hn aB = b := by
  let G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) := (etalePullback q Λ).obj F
  have hsquare := etalePullbackSectionMap_square q Λ F v p h hh n hn hp
  have hrestrict := etalePullbackSectionMap_restriction_of_comp_eq q Λ F r h hh l hl hr
  have hlocal : G.obj.map v.op
        (etalePullbackSectionMap q Λ F (U := Scheme.Etale.mk (𝟙 Y)) n hn aB) =
      G.obj.map v.op b :=
    (ConcreteCategory.congr_hom hsquare aB).symm.trans
      ((congrArg (etalePullbackSectionMap q Λ F (U := V) h hh) haB).trans
        ((ConcreteCategory.congr_hom hrestrict a).trans ha))
  have hv : v.left = V.hom := (Category.comp_id v.left).symm.trans v.w
  have hcover : Sieve.ofArrows (fun _ : Unit => V) (fun _ => v) ∈
      Y.smallEtaleTopology (Scheme.Etale.mk (𝟙 Y)) := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun _ : Unit => v)).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := V.hom.surjective x
    exact Set.mem_iUnion.mpr ⟨(), y, (congrArg (fun k => k y) hv).trans hy⟩
  apply G.isSeparated (Scheme.Etale.mk (𝟙 Y))
    (Sieve.ofArrows (fun _ : Unit => V) (fun _ => v)) hcover _ b
  intro T g hg
  obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff (fun _ : Unit => V)
    (fun _ => v) g).mp hg
  rw [op_comp, G.obj.map_comp_apply, G.obj.map_comp_apply]
  exact congrArg (G.obj.map k.op) hlocal

/-- Every section on the actual strictly local base change is represented
by an actual direct-image germ when the original morphism is qcqs. -/
theorem etalePushforwardGeometricStalkSections_surjective
    {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    (φ : R →+* Ω) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Function.Surjective (etalePushforwardGeometricStalkSections φ f Λ F) := by
  let s := Spec.map (CommRingCat.ofHom φ)
  let h := Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let Y := pullback h f
  let q : Y ⟶ X := pullback.snd h f
  let G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) := (etalePullback q Λ).obj F
  let η : F ⟶ (etalePushforward q Λ).obj G :=
    (etalePullbackPushforwardAdjunction q Λ).unit.app F
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (pullback.fst h f)
  have : QuasiCompact (terminal.from Y) :=
    (AlgebraicGeometry.compactSpace_iff_quasiCompact Y).1 inferInstance
  intro b
  change G.obj.obj (op (Scheme.Etale.mk (𝟙 Y))) at b
  obtain ⟨U, a, V, d, hU, hV, hd, hsurj, ha⟩ :=
    exists_affine_pullback_representative_cover q Λ F b
  have : IsAffine U.left := hU
  have : IsAffine V.left := hV
  have : IsOpenImmersion d.left := hd
  have : Surjective V.hom := hsurj
  let v : V ⟶ Scheme.Etale.mk (𝟙 Y) := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    V.hom (Category.comp_id V.hom)
  let l : V.left ⟶ U.left := d.left ≫ pullback.fst U.hom q
  have hl : l ≫ U.hom = V.hom ≫ q :=
    (Category.assoc d.left (pullback.fst U.hom q) U.hom).trans
      ((congrArg (fun k => d.left ≫ k) (pullback.condition (f := U.hom) (g := q))).trans
        ((Category.assoc d.left (pullback.snd U.hom q) q).symm.trans
          (congrArg (fun k => k ≫ q) d.w)))
  have hdLift : etaleBaseChangeLift q (U := V) (V := U) l hl = d := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans d.w.symm
  have ha' : etalePullbackSectionMap q Λ F (U := V) l hl a = G.obj.map v.op b := by
    change G.obj.map (etaleBaseChangeLift q l hl).op (η.hom.app (op U) a) = _
    exact (congrArg (fun k : V ⟶ (etaleBaseChange q).obj U =>
      G.obj.map k.op (η.hom.app (op U) a)) hdLift).trans ha
  obtain ⟨W, hWRange, hWeq⟩ :=
    exists_representative_overlap_equality_open q Λ F U V l hl v a b ha'
  obtain ⟨T, t, _, C, p, r, e, _, hpSurj, heP, heR, hOverlap⟩ :=
    geometricStalk_exists_affine_matched_cover_stage φ f U V d W hWRange
  have : Surjective p.left := hpSurj
  let B : X.Etale := (etaleBaseChange f).obj T
  obtain ⟨aB, haB⟩ := exists_section_of_representative_overlap_range
    Λ F B C U p r a W hWeq hOverlap
  let n : Y ⟶ B.left := geometricStalkNeighborhoodBaseChangeMap φ f T t
  have hn : n ≫ B.hom = (𝟙 Y) ≫ q :=
    (geometricStalkNeighborhoodBaseChangeMap_snd φ f T t).trans (Category.id_comp q).symm
  have he : e ≫ C.hom = V.hom ≫ q :=
    (congrArg (fun k => e ≫ k) r.w.symm).trans
      ((Category.assoc e r.left U.hom).symm.trans
        ((congrArg (fun k => k ≫ U.hom) heR).trans hl))
  have hrecover : geometricStalkNeighborhoodSectionMap φ f Λ F T t aB = b :=
    pulledSection_eq_of_descended_representative q Λ F B C U V p r v n hn
      e he l hl heP heR aB a b haB ha'
  refine ⟨(Scheme.pointSmallEtale s).toPresheafFiber T t
    ((etalePushforward f Λ).obj F).obj aB, ?_⟩
  exact (ConcreteCategory.congr_hom
    (toPresheafFiber_etalePushforwardGeometricStalkSections φ f Λ F T t) aB).trans hrecover

end EtaleCohomology
