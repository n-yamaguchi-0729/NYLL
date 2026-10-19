/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.GeometricStalkSectionEquality
import Nyll.EtaleCohomology.Sites.PullbackSectionFactors

/-!
# Actual overlap compatibility of inverse-image representatives

A local original section representing one global inverse-image section
agrees on the whole source overlap. The actual inverse-image unit reflects
this equality at geometric stalks, putting the overlap's image inside the
maximal equality-open of the two original restrictions. This is the finite
matching datum used when descending arbitrary sections from a strict-local
base; no continuity or descended compatibility is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

universe u

/-- The native scheme self-overlap, as an object of the same small étale site. -/
def etaleSelfOverlap {X : Scheme.{u}} (U : X.Etale) : X.Etale :=
  Scheme.Etale.mk (pullback.fst U.hom U.hom ≫ U.hom)

/-- The first native projection of the self-overlap. -/
def etaleSelfOverlapFst {X : Scheme.{u}} (U : X.Etale) : etaleSelfOverlap U ⟶ U :=
  MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    (pullback.fst U.hom U.hom) rfl

/-- The second native projection of the self-overlap. -/
def etaleSelfOverlapSnd {X : Scheme.{u}} (U : X.Etale) : etaleSelfOverlap U ⟶ U :=
  MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    (pullback.snd U.hom U.hom) pullback.condition.symm

/-- A local factor induces the literal map between native self-overlaps. -/
def etaleLocalFactorOverlapMap {X Y : Scheme.{u}} (q : Y ⟶ X)
    (U : X.Etale) (V : Y.Etale) (l : V.left ⟶ U.left)
    (hl : l ≫ U.hom = V.hom ≫ q) :
    (etaleSelfOverlap V).left ⟶ (etaleSelfOverlap U).left :=
  pullback.map V.hom V.hom U.hom U.hom l l q hl.symm hl.symm

theorem etaleLocalFactorOverlapMap_fst {X Y : Scheme.{u}} (q : Y ⟶ X)
    (U : X.Etale) (V : Y.Etale) (l : V.left ⟶ U.left)
    (hl : l ≫ U.hom = V.hom ≫ q) :
    etaleLocalFactorOverlapMap q U V l hl ≫ (etaleSelfOverlapFst U).left =
      (etaleSelfOverlapFst V).left ≫ l := pullback.lift_fst _ _ _

theorem etaleLocalFactorOverlapMap_snd {X Y : Scheme.{u}} (q : Y ⟶ X)
    (U : X.Etale) (V : Y.Etale) (l : V.left ⟶ U.left)
    (hl : l ≫ U.hom = V.hom ≫ q) :
    etaleLocalFactorOverlapMap q U V l hl ≫ (etaleSelfOverlapSnd U).left =
      (etaleSelfOverlapSnd V).left ≫ l := pullback.lift_snd _ _ _

/-- The overlap map is still a local factor over the original base morphism. -/
theorem etaleLocalFactorOverlapMap_comp {X Y : Scheme.{u}} (q : Y ⟶ X)
    (U : X.Etale) (V : Y.Etale) (l : V.left ⟶ U.left)
    (hl : l ≫ U.hom = V.hom ≫ q) :
    etaleLocalFactorOverlapMap q U V l hl ≫ (etaleSelfOverlap U).hom =
      (etaleSelfOverlap V).hom ≫ q := by
  let m := etaleLocalFactorOverlapMap q U V l hl
  let p : (etaleSelfOverlap U).left ⟶ U.left := (etaleSelfOverlapFst U).left
  let r : (etaleSelfOverlap V).left ⟶ V.left := (etaleSelfOverlapFst V).left
  change m ≫ (p ≫ U.hom) = (r ≫ V.hom) ≫ q
  exact (Category.assoc m p U.hom).symm.trans
    ((congrArg (fun t => t ≫ U.hom) (etaleLocalFactorOverlapMap_fst q U V l hl)).trans
      ((Category.assoc r l U.hom).trans
        ((congrArg (fun t => r ≫ t) hl).trans (Category.assoc r V.hom q).symm)))

/-- The native overlap of a representative of one global inverse-image
section maps into an actual equality-open of its two original restrictions. -/
theorem exists_representative_overlap_equality_open
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (U : X.Etale) (V : Y.Etale) (l : V.left ⟶ U.left)
    (hl : l ≫ U.hom = V.hom ≫ q)
    (r : V ⟶ Scheme.Etale.mk (𝟙 Y))
    (a : F.obj.obj (op U))
    (b : ((etalePullback q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))))
    (ha : etalePullbackSectionMap q Λ F (U := V) l hl a =
      ((etalePullback q Λ).obj F).obj.map r.op b) :
    ∃ W : (etaleSelfOverlap U).left.Opens,
      Set.range (etaleLocalFactorOverlapMap q U V l hl) ⊆ W.carrier ∧
      F.obj.map (MorphismProperty.Over.homMk
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl :
        (Scheme.Etale.mk (W.ι ≫ (etaleSelfOverlap U).hom) : X.Etale) ⟶
          etaleSelfOverlap U).op (F.obj.map (etaleSelfOverlapFst U).op a) =
      F.obj.map (MorphismProperty.Over.homMk
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl :
        (Scheme.Etale.mk (W.ι ≫ (etaleSelfOverlap U).hom) : X.Etale) ⟶
          etaleSelfOverlap U).op (F.obj.map (etaleSelfOverlapSnd U).op a) := by
  let G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) := (etalePullback q Λ).obj F
  let P : X.Etale := etaleSelfOverlap U
  let Q : Y.Etale := etaleSelfOverlap V
  let p₁ : P ⟶ U := etaleSelfOverlapFst U
  let p₂ : P ⟶ U := etaleSelfOverlapSnd U
  let t₁ : Q ⟶ V := etaleSelfOverlapFst V
  let t₂ : Q ⟶ V := etaleSelfOverlapSnd V
  let m : Q.left ⟶ P.left := etaleLocalFactorOverlapMap q U V l hl
  have hm : m ≫ P.hom = Q.hom ≫ q := etaleLocalFactorOverlapMap_comp q U V l hl
  have h₁ : F.obj.map p₁.op ≫ etalePullbackSectionMap q Λ F (U := Q) m hm =
      etalePullbackSectionMap q Λ F (U := V) l hl ≫ G.obj.map t₁.op :=
    etalePullbackSectionMap_square q Λ F t₁ p₁ m hm l hl
      (etaleLocalFactorOverlapMap_fst q U V l hl)
  have h₂ : F.obj.map p₂.op ≫ etalePullbackSectionMap q Λ F (U := Q) m hm =
      etalePullbackSectionMap q Λ F (U := V) l hl ≫ G.obj.map t₂.op :=
    etalePullbackSectionMap_square q Λ F t₂ p₂ m hm l hl
      (etaleLocalFactorOverlapMap_snd q U V l hl)
  have ht : t₁ ≫ r = t₂ ≫ r := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (𝟙 Y)).mp
    exact (t₁ ≫ r).w.trans (t₂ ≫ r).w.symm
  have hb : G.obj.map t₁.op (G.obj.map r.op b) = G.obj.map t₂.op (G.obj.map r.op b) :=
    (G.obj.map_comp_apply r.op t₁.op b).symm.trans
      ((congrArg (fun k : Q ⟶ Scheme.Etale.mk (𝟙 Y) => G.obj.map k.op b) ht).trans
        (G.obj.map_comp_apply r.op t₂.op b))
  have heq : etalePullbackSectionMap q Λ F (U := Q) m hm (F.obj.map p₁.op a) =
      etalePullbackSectionMap q Λ F (U := Q) m hm (F.obj.map p₂.op a) :=
    (ConcreteCategory.congr_hom h₁ a).trans
      ((congrArg (G.obj.map t₁.op) ha).trans
        (hb.trans ((congrArg (G.obj.map t₂.op) ha).symm.trans
          (ConcreteCategory.congr_hom h₂ a).symm)))
  have : X.smallEtaleTopology.HasSheafCompose (forget (ModuleCat.{u} Λ)) := by
    let : PreservesLimitsOfSize.{u, u + 1} (forget (ModuleCat.{u} Λ)) :=
      (ModuleCat.adj Λ).rightAdjoint_preservesLimits
    exact hasSheafCompose_of_preservesLimitsOfSize
      (F := forget (ModuleCat.{u} Λ)) X.smallEtaleTopology
  obtain ⟨W, hW, heqW⟩ := exists_sectionEquality_open F P
    (F.obj.map p₁.op a) (F.obj.map p₂.op a)
  exact ⟨W, range_subset_sectionEquality_open_of_local_pullback_eq q Λ F Q P m hm
    (F.obj.map p₁.op a) (F.obj.map p₂.op a) W hW heq, heqW⟩

/-- An original section descends through an actual surjective étale cover
when its native overlap map lands in an open where its two restrictions
agree. All matching equalities are proved from this literal range condition. -/
theorem exists_section_of_representative_overlap_range
    {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (B C U : X.Etale) (p : C ⟶ B) [Surjective p.left]
    (r : C ⟶ U) (a : F.obj.obj (op U))
    (W : (etaleSelfOverlap U).left.Opens)
    (hW : F.obj.map (MorphismProperty.Over.homMk
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl :
        (Scheme.Etale.mk (W.ι ≫ (etaleSelfOverlap U).hom) : X.Etale) ⟶
          etaleSelfOverlap U).op (F.obj.map (etaleSelfOverlapFst U).op a) =
      F.obj.map (MorphismProperty.Over.homMk
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl :
        (Scheme.Etale.mk (W.ι ≫ (etaleSelfOverlap U).hom) : X.Etale) ⟶
          etaleSelfOverlap U).op (F.obj.map (etaleSelfOverlapSnd U).op a))
    (hRange : Set.range (pullback.map p.left p.left U.hom U.hom r.left r.left B.hom
      (p.w.trans r.w.symm) (p.w.trans r.w.symm)) ⊆ W.carrier) :
    ∃ b : F.obj.obj (op B), F.obj.map p.op b = F.obj.map r.op a := by
  let P : X.Etale := etaleSelfOverlap U
  let u₁ : P ⟶ U := etaleSelfOverlapFst U
  let u₂ : P ⟶ U := etaleSelfOverlapSnd U
  let O : X.Etale := Scheme.Etale.mk (W.ι ≫ P.hom)
  let j : O ⟶ P := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl
  let m : pullback p.left p.left ⟶ P.left :=
    pullback.map p.left p.left U.hom U.hom r.left r.left B.hom
      (p.w.trans r.w.symm) (p.w.trans r.w.symm)
  have hm₁ : m ≫ u₁.left = pullback.fst p.left p.left ≫ r.left := pullback.lift_fst _ _ _
  have hm₂ : m ≫ u₂.left = pullback.snd p.left p.left ≫ r.left := pullback.lift_snd _ _ _
  have hcompat {T : X.Etale} (g₁ g₂ : T ⟶ C) (hg : g₁ ≫ p = g₂ ≫ p) :
      F.obj.map g₁.op (F.obj.map r.op a) = F.obj.map g₂.op (F.obj.map r.op a) := by
    have hgl : g₁.left ≫ p.left = g₂.left ≫ p.left :=
      congrArg (fun k : T ⟶ B => k.left) hg
    let t : T.left ⟶ pullback p.left p.left := pullback.lift g₁.left g₂.left hgl
    let n : T.left ⟶ P.left := t ≫ m
    have hn₁ : n ≫ u₁.left = g₁.left ≫ r.left :=
      (Category.assoc t m u₁.left).trans
        ((congrArg (fun k => t ≫ k) hm₁).trans
          ((Category.assoc t (pullback.fst p.left p.left) r.left).symm.trans
            (congrArg (fun k => k ≫ r.left) (pullback.lift_fst _ _ _))))
    have hn₂ : n ≫ u₂.left = g₂.left ≫ r.left :=
      (Category.assoc t m u₂.left).trans
        ((congrArg (fun k => t ≫ k) hm₂).trans
          ((Category.assoc t (pullback.snd p.left p.left) r.left).symm.trans
            (congrArg (fun k => k ≫ r.left) (pullback.lift_snd _ _ _))))
    have hn : n ≫ P.hom = T.hom := by
      change n ≫ (u₁.left ≫ U.hom) = T.hom
      exact (Category.assoc n u₁.left U.hom).symm.trans
        ((congrArg (fun k => k ≫ U.hom) hn₁).trans
          ((Category.assoc g₁.left r.left U.hom).trans
            ((congrArg (fun k => g₁.left ≫ k) r.w).trans g₁.w)))
    have hnRange : Set.range n ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro z ⟨x, rfl⟩
      exact hRange ⟨t x, (Scheme.Hom.comp_apply t m x).symm⟩
    let s₀ : T.left ⟶ W.toScheme := IsOpenImmersion.lift W.ι n hnRange
    have hs₀ : s₀ ≫ W.ι = n := IsOpenImmersion.lift_fac W.ι n hnRange
    let s : T ⟶ O := MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) s₀
      ((Category.assoc s₀ W.ι P.hom).symm.trans
        ((congrArg (fun k => k ≫ P.hom) hs₀).trans hn))
    have hs₁ : s ≫ j ≫ u₁ = g₁ ≫ r := by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.assoc s₀ W.ι u₁.left).symm.trans
        ((congrArg (fun k => k ≫ u₁.left) hs₀).trans hn₁)
    have hs₂ : s ≫ j ≫ u₂ = g₂ ≫ r := by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.assoc s₀ W.ι u₂.left).symm.trans
        ((congrArg (fun k => k ≫ u₂.left) hs₀).trans hn₂)
    have h₁ : F.obj.map g₁.op (F.obj.map r.op a) =
        F.obj.map s.op (F.obj.map j.op (F.obj.map u₁.op a)) :=
      (F.obj.map_comp_apply r.op g₁.op a).symm.trans
        ((congrArg (fun k : T ⟶ U => F.obj.map k.op a) hs₁.symm).trans
          ((F.obj.map_comp_apply (j ≫ u₁).op s.op a).trans
            (congrArg (F.obj.map s.op) (F.obj.map_comp_apply u₁.op j.op a))))
    have h₂ : F.obj.map g₂.op (F.obj.map r.op a) =
        F.obj.map s.op (F.obj.map j.op (F.obj.map u₂.op a)) :=
      (F.obj.map_comp_apply r.op g₂.op a).symm.trans
        ((congrArg (fun k : T ⟶ U => F.obj.map k.op a) hs₂.symm).trans
          ((F.obj.map_comp_apply (j ≫ u₂).op s.op a).trans
            (congrArg (F.obj.map s.op) (F.obj.map_comp_apply u₂.op j.op a))))
    exact h₁.trans ((congrArg (F.obj.map s.op) hW).trans h₂.symm)
  have hcover : Sieve.generate (Presieve.singleton p) ∈ X.smallEtaleTopology B := by
    have hc : Sieve.ofArrows (fun _ : Unit => C) (fun _ => p) ∈
        X.smallEtaleTopology B := by
      apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun _ : Unit => p)).mpr
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨y, hy⟩ := p.left.surjective x
      exact Set.mem_iUnion.mpr ⟨(), y, hy⟩
    apply X.smallEtaleTopology.superset_covering (R := _) ?_ hc
    intro T g hg
    obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff (fun _ : Unit => C)
      (fun _ => p) g).mp hg
    exact (Sieve.generate (Presieve.singleton p)).downward_closed
      (Sieve.le_generate _ _ _ (Presieve.singleton_self _)) k
  let FT : Sheaf X.smallEtaleTopology (Type u) :=
    (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u} Λ))).obj F
  have hSheaf : Presieve.IsSheafFor FT.obj (Presieve.singleton p) :=
    (Presieve.isSheafFor_iff_generate _).mpr
      ((isSheaf_iff_isSheaf_of_type _ _).mp FT.property _ hcover)
  obtain ⟨b, hb, _⟩ := (Presieve.isSheafFor_singleton.mp hSheaf)
    (F.obj.map r.op a) hcompat
  exact ⟨b, hb⟩

end EtaleCohomology
