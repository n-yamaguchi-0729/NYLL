/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.RepresentableGlobalSectionsPullback
public import Nyll.EtaleCohomology.Descent.RepresentablePullbackSections
public import Nyll.EtaleCohomology.Descent.GeometricStalkEvaluationSetSections

/-!
# Actual represented section precomposition at the geometric fiber

The existing original global-section pullback bijection is transported
through the existing represented-section equivalence and slice adjunction.
Its resulting map is literal precomposition by the specified scheme map.
For the native strict-local evaluation square, proper H⁰ supplies the
bijection without assuming a section-comparison theorem.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

universe u

namespace EtaleCohomology

private theorem representedSection_precomp_bijective
    {X Y : Scheme.{u}} (q : Y ⟶ X) (W : X.Etale)
    (h : Function.Bijective
      (etaleSetPullbackGlobalSectionsMap q (X.smallEtaleTopology.yoneda.obj W))) :
    Function.Bijective
      (fun a : (Scheme.Etale.mk (𝟙 X) : X.Etale) ⟶ W =>
        (Over.homMk (q ≫ a.left)
          ((Category.assoc q a.left W.hom).trans
            ((congrArg (fun k => q ≫ k) a.w).trans (Category.comp_id q))) :
            Over.mk q ⟶ (Scheme.Etale.forget X).obj W)) := by
  let E := etaleRepresentablePullbackSectionsEquiv q W
  let b := fun a : (Scheme.Etale.mk (𝟙 X) : X.Etale) ⟶ W =>
    (Over.homMk (q ≫ a.left)
      ((Category.assoc q a.left W.hom).trans
            ((congrArg (fun k => q ≫ k) a.w).trans (Category.comp_id q))) :
        Over.mk q ⟶ (Scheme.Etale.forget X).obj W)
  have he : E ∘ b = etaleSetPullbackGlobalSectionsMap q
      (X.smallEtaleTopology.yoneda.obj W) := by
    funext a
    exact (etaleSetPullbackGlobalSectionsMap_eq_representableSectionsEquiv q W a).symm
  exact (Function.Bijective.of_comp_iff' E.bijective b).mp (he.symm ▸ h)

/-- The original global-section pullback bijection on the represented
base change gives a bijection on literal morphisms to the original
representer by precomposition. -/
theorem representedSections_precomp_bijective
    {X Y Z : Scheme.{u}} (p : Y ⟶ X) (q : Z ⟶ Y)
    (r : Z ⟶ X) (hqr : q ≫ p = r) (W : X.Etale)
    (h : Function.Bijective (etaleSetPullbackGlobalSectionsMap q
      (Y.smallEtaleTopology.yoneda.obj ((etaleBaseChange p).obj W)))) :
    Function.Bijective
      (fun a : Over.mk p ⟶ (Scheme.Etale.forget X).obj W =>
        (Over.homMk (q ≫ a.left)
          ((Category.assoc q a.left W.hom).trans
            ((congrArg (fun k => q ≫ k) a.w).trans hqr)) :
            Over.mk r ⟶ (Scheme.Etale.forget X).obj W)) := by
  subst r
  let Wp := (etaleBaseChange p).obj W
  let E₀ := (etaleRepresentablePullbackSectionsEquiv p W).trans
    ((((sheafSections Y.smallEtaleTopology (Type u)).obj
      (op (Scheme.Etale.mk (𝟙 Y)))).mapIso
        (etaleSetPullbackYonedaObjIso p W)).toEquiv)
  let E₁ := (Over.mapPullbackAdj p).homEquiv (Over.mk q)
    ((Scheme.Etale.forget X).obj W)
  let b := fun a : (Scheme.Etale.mk (𝟙 Y) : Y.Etale) ⟶ Wp =>
    (Over.homMk (q ≫ a.left)
      ((Category.assoc q a.left Wp.hom).trans
        ((congrArg (fun k => q ≫ k) a.w).trans (Category.comp_id q))) :
        Over.mk q ⟶ (Scheme.Etale.forget Y).obj Wp)
  let c := fun a : Over.mk p ⟶ (Scheme.Etale.forget X).obj W =>
    (Over.homMk (q ≫ a.left)
      ((Category.assoc q a.left W.hom).trans (congrArg (fun k => q ≫ k) a.w)) :
        Over.mk (q ≫ p) ⟶ (Scheme.Etale.forget X).obj W)
  have he : E₁ ∘ c = b ∘ E₀ := by
    funext a
    have hE₀ : E₀ a = etaleBaseChangeLift p a.left
        (a.w.trans (Category.id_comp p).symm) :=
      etaleRepresentablePullbackSectionsEquiv_yoneda p W a
    apply Over.OverMorphism.ext
    change (E₁ (c a)).left = q ≫ (E₀ a).left
    rw [hE₀]
    dsimp only [E₁, c]
    simp only [Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
    change pullback.lift (q ≫ a.left) q _ = q ≫ pullback.lift a.left (𝟙 Y) _
    let ha : a.left ≫ W.hom = (𝟙 Y) ≫ p :=
      a.w.trans (Category.id_comp p).symm
    let hqa : (q ≫ a.left) ≫ W.hom = q ≫ p :=
      (Category.assoc q a.left W.hom).trans (congrArg (fun k => q ≫ k) a.w)
    let l : Z ⟶ pullback W.hom p := pullback.lift (q ≫ a.left) q hqa
    let k : Y ⟶ pullback W.hom p := pullback.lift a.left (𝟙 Y) ha
    have hl₁ : l ≫ pullback.fst W.hom p = q ≫ a.left := pullback.lift_fst _ _ _
    have hl₂ : l ≫ pullback.snd W.hom p = q := pullback.lift_snd _ _ _
    have hk₁ : k ≫ pullback.fst W.hom p = a.left := pullback.lift_fst _ _ _
    have hk₂ : k ≫ pullback.snd W.hom p = 𝟙 Y := pullback.lift_snd _ _ _
    change l = q ≫ k
    exact pullback.hom_ext
      (hl₁.trans ((Category.assoc q k (pullback.fst W.hom p)).trans
        (congrArg (fun z => q ≫ z) hk₁)).symm)
      (hl₂.trans ((Category.assoc q k (pullback.snd W.hom p)).trans
        ((congrArg (fun z => q ≫ z) hk₂).trans (Category.comp_id q))).symm)
  have hb : Function.Bijective b := representedSection_precomp_bijective q Wp h
  exact (Function.Bijective.of_comp_iff' E₁.bijective c).mp
    (he.symm ▸ hb.comp E₀.bijective)

/-- For the actual proper family and its native strict-local evaluation
square, literal restriction of represented scheme sections to the original
geometric fiber is bijective. -/
theorem geometricStalkEvaluation_representedSections_precomp_bijective
    {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    (φ : R →+* Ω) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (W : FiniteEtale X) :
    Function.Bijective
      (fun a : Over.mk
          (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) ⟶
            (FiniteEtale.forget X).obj W =>
        (Over.homMk (geometricStalkEvaluationBaseChangeMap φ f ≫ a.left)
          ((Category.assoc (geometricStalkEvaluationBaseChangeMap φ f) a.left W.hom).trans
            ((congrArg (fun k => geometricStalkEvaluationBaseChangeMap φ f ≫ k) a.w).trans
              (geometricStalkEvaluationBaseChangeMap_snd φ f))) :
            Over.mk (pullback.snd (Spec.map (CommRingCat.ofHom φ)) f) ⟶
              (FiniteEtale.forget X).obj W)) := by
  let p := pullback.snd
    (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f
  let V := (finiteEtaleToEtale X).obj W
  let Y := pullback
    (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f
  have hG : IsEtaleFiniteLocallyConstantSet
      (Y.smallEtaleTopology.yoneda.obj ((etaleBaseChange p).obj V)) :=
    ((finiteEtaleSheaf_isEtaleFiniteLocallyConstantSet W).pullback p).of_iso
      (etaleSetPullbackYonedaObjIso p V)
  exact representedSections_precomp_bijective p
    (geometricStalkEvaluationBaseChangeMap φ f)
    (pullback.snd (Spec.map (CommRingCat.ofHom φ)) f)
    (geometricStalkEvaluationBaseChangeMap_snd φ f) V
    (etaleSetGeometricStalkEvaluationGlobalSections_bijective φ f hG)

end EtaleCohomology
