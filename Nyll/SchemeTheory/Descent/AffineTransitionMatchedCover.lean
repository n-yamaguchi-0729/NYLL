/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.AffineTransitionCover
import Nyll.SchemeTheory.Descent.AffineTransitionOverlap
import Nyll.SchemeTheory.Descent.AffineTransitionRange
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Descending a covering with its full overlap condition

An affine open-immersed cover over an inverse limit descends to a covering
at a coefficient stage. If its entire self-overlap maps into an open of the
original model overlap, a later coefficient stage satisfies the same open
condition. This uses quasi-compact overlap descent and the literal native
overlap isomorphism; it does not use any continuity statement for sheaves.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineTransitionHom

variable {S T X U V : Scheme.{u}}

/-- The two maps from a cover of a coefficient model commute over the original source. -/
theorem modelCoverMap_comp_snd (h : T ⟶ S) (f : X ⟶ S) (g : U ⟶ X)
    (α : V ⟶ pullback h (g ≫ f)) :
    (α ≫ modelMap h f g) ≫ pullback.snd h f =
      (α ≫ pullback.snd h (g ≫ f)) ≫ g := by
  rw [Category.assoc, modelMap_snd, Category.assoc]

/-- The actual overlap map of a cover inside a coefficient pullback model. -/
def modelCoverOverlapMap (h : T ⟶ S) (f : X ⟶ S) (g : U ⟶ X)
    (α : V ⟶ pullback h (g ≫ f)) :
    pullback (α ≫ modelMap h f g) (α ≫ modelMap h f g) ⟶ pullback g g :=
  pullback.map _ _ g g (α ≫ pullback.snd h (g ≫ f))
    (α ≫ pullback.snd h (g ≫ f)) (pullback.snd h f)
    (modelCoverMap_comp_snd h f g α) (modelCoverMap_comp_snd h f g α)

theorem modelCoverOverlapMap_fst (h : T ⟶ S) (f : X ⟶ S) (g : U ⟶ X)
    (α : V ⟶ pullback h (g ≫ f)) :
    modelCoverOverlapMap h f g α ≫ pullback.fst g g =
      pullback.fst (α ≫ modelMap h f g) (α ≫ modelMap h f g) ≫
        α ≫ pullback.snd h (g ≫ f) := pullback.lift_fst _ _ _

theorem modelCoverOverlapMap_snd (h : T ⟶ S) (f : X ⟶ S) (g : U ⟶ X)
    (α : V ⟶ pullback h (g ≫ f)) :
    modelCoverOverlapMap h f g α ≫ pullback.snd g g =
      pullback.snd (α ≫ modelMap h f g) (α ≫ modelMap h f g) ≫
        α ≫ pullback.snd h (g ≫ f) := pullback.lift_snd _ _ _

variable {B C : Over S}

/-- A model map between two actual covers induces the expected composite
map on their original-model overlaps. -/
theorem modelCoverOverlapMap_naturality
    (t : B ⟶ C) (f : X ⟶ S) (g : U ⟶ X) {W : Scheme.{u}}
    (α : V ⟶ pullback B.hom (g ≫ f)) (β : W ⟶ pullback C.hom (g ≫ f))
    (d : V ⟶ W) (hd : d ≫ β = α ≫ ((Over.pullback (g ≫ f)).map t).left)
    (H : CommSq d (α ≫ modelMap B.hom f g) (β ≫ modelMap C.hom f g)
      ((Over.pullback f).map t).left) :
    pullback.map _ _ _ _ d d ((Over.pullback f).map t).left H.w.symm H.w.symm ≫
      modelCoverOverlapMap C.hom f g β = modelCoverOverlapMap B.hom f g α := by
  have hr : d ≫ β ≫ pullback.snd C.hom (g ≫ f) =
      α ≫ pullback.snd B.hom (g ≫ f) := by
    have ht : ((Over.pullback (g ≫ f)).map t).left ≫
        pullback.snd C.hom (g ≫ f) = pullback.snd B.hom (g ≫ f) :=
      Over.w ((Over.pullback (g ≫ f)).map t)
    rw [← Category.assoc, hd, Category.assoc, ht]
  apply pullback.hom_ext
  · rw [Category.assoc, modelCoverOverlapMap_fst, ← Category.assoc,
      pullback.lift_fst, Category.assoc, hr, modelCoverOverlapMap_fst]
  · rw [Category.assoc, modelCoverOverlapMap_snd, ← Category.assoc,
      pullback.lift_snd, Category.assoc, hr, modelCoverOverlapMap_snd]

/-- Surjectivity of a model open covering is preserved by every coefficient change. -/
theorem modelOpenCover_surjective (t : B ⟶ C) (f : X ⟶ S) (g : U ⟶ X)
    (O : (pullback C.hom (g ≫ f)).Opens)
    [Surjective (O.ι ≫ modelMap C.hom f g)] :
    Surjective ((((Over.pullback (g ≫ f)).map t).left ⁻¹ᵁ O).ι ≫
      modelMap B.hom f g) := by
  refine ⟨Set.range_eq_univ.mp ?_⟩
  rw [modelMap_range_preimage, range_eq_univ, Set.preimage_univ]

/-- Literal open recovery factors the original covering scheme through
the stage cover, without replacing the original scheme by its image. -/
def modelOpenRecovery (t : B ⟶ C) (f : X ⟶ S) (g : U ⟶ X)
    (α : V ⟶ pullback B.hom (g ≫ f)) [IsOpenImmersion α]
    (O : (pullback C.hom (g ≫ f)).Opens)
    (hO : ((Over.pullback (g ≫ f)).map t).left ⁻¹ᵁ O = α.opensRange) : V ⟶ O :=
  IsOpenImmersion.lift O.ι (α ≫ ((Over.pullback (g ≫ f)).map t).left) (by
    rintro z ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    change α v ∈ ((Over.pullback (g ≫ f)).map t).left ⁻¹ᵁ O
    rw [hO]
    exact ⟨v, rfl⟩)

theorem modelOpenRecovery_ι (t : B ⟶ C) (f : X ⟶ S) (g : U ⟶ X)
    (α : V ⟶ pullback B.hom (g ≫ f)) [IsOpenImmersion α]
    (O : (pullback C.hom (g ≫ f)).Opens)
    (hO : ((Over.pullback (g ≫ f)).map t).left ⁻¹ᵁ O = α.opensRange) :
    modelOpenRecovery t f g α O hO ≫ O.ι =
      α ≫ ((Over.pullback (g ≫ f)).map t).left := IsOpenImmersion.lift_fac _ _ _

/-- Exact inverse-image recovery supplies the actual Cartesian covering square. -/
theorem modelOpenRecovery_isPullback (t : B ⟶ C) (f : X ⟶ S) (g : U ⟶ X)
    (α : V ⟶ pullback B.hom (g ≫ f)) [IsOpenImmersion α]
    (O : (pullback C.hom (g ≫ f)).Opens)
    (hO : ((Over.pullback (g ≫ f)).map t).left ⁻¹ᵁ O = α.opensRange) :
    IsPullback (modelOpenRecovery t f g α O hO) (α ≫ modelMap B.hom f g)
      (O.ι ≫ modelMap C.hom f g) ((Over.pullback f).map t).left := by
  have H := IsOpenImmersion.isPullback (modelOpenRecovery t f g α O hO)
    α O.ι ((Over.pullback (g ≫ f)).map t).left
    (modelOpenRecovery_ι t f g α O hO).symm
    (by rw [Scheme.Opens.opensRange_ι]; exact hO)
  exact H.paste_vert (modelMap_transition_isPullback t f g)

/-- An affine open-immersed cover whose full overlap maps into a specified
original-model open descends to a stage satisfying that same overlap condition. -/
theorem exists_affine_matched_cover_stage
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    [∀ i : I, CompactSpace (D.obj i).left]
    [∀ i : I, QuasiSeparatedSpace (D.obj i).left]
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (g : U ⟶ X) [Etale g] [IsAffine U] [IsAffine V]
    (α : V ⟶ pullback c.pt.hom (g ≫ f)) [IsOpenImmersion α]
    [Surjective (α ≫ modelMap c.pt.hom f g)]
    (W : (pullback g g).Opens)
    (hW : Set.range (modelCoverOverlapMap c.pt.hom f g α) ⊆ W.carrier) :
    ∃ (i : I) (O : (pullback (D.obj i).hom (g ≫ f)).Opens),
      IsAffineOpen O ∧ (cone D c (g ≫ f)).π.app i ⁻¹ᵁ O = α.opensRange ∧
      Surjective (O.ι ≫ modelMap (D.obj i).hom f g) ∧
      Set.range (modelCoverOverlapMap (D.obj i).hom f g O.ι) ⊆ W.carrier := by
  have : IsConnected I := IsCofiltered.isConnected I
  let Z : (pullback c.pt.hom (g ≫ f)).Opens := α.opensRange
  let e : V ⟶ Z := IsOpenImmersion.lift Z.ι α
    (by rw [Scheme.Opens.range_ι]; exact Set.Subset.rfl)
  have he : e ≫ Z.ι = α := IsOpenImmersion.lift_fac _ _ _
  have hcoverZ : Surjective (Z.ι ≫ modelMap c.pt.hom f g) := by
    have hs : Surjective (e ≫ (Z.ι ≫ modelMap c.pt.hom f g)) := by
      rw [← Category.assoc, he]
      infer_instance
    exact Surjective.of_comp e _
  obtain ⟨i, O, hO, hrec, hsurj⟩ := exists_affineOpen_cover_stage
    D c hc f g Z (isAffineOpen_opensRange α) (hWsurj := hcoverZ)
  have hrec' : ((Over.pullback (g ≫ f)).map (c.π.app i)).left ⁻¹ᵁ O =
      α.opensRange := hrec
  let a : O.toScheme ⟶ pullback (D.obj i).hom f := O.ι ≫ modelMap (D.obj i).hom f g
  let b : V ⟶ pullback c.pt.hom f := α ≫ modelMap c.pt.hom f g
  let d : V ⟶ O := modelOpenRecovery (c.π.app i) f g α O hrec'
  have Hd : IsPullback d b a ((Over.pullback f).map (c.π.app i)).left :=
    modelOpenRecovery_isPullback (c.π.app i) f g α O hrec'
  let m : pullback b b ⟶ pullback a a := pullback.map b b a a d d
    ((Over.pullback f).map (c.π.app i)).left Hd.w.symm Hd.w.symm
  let r : pullback a a ⟶ (D.obj i).left :=
    pullback.snd a a ≫ a ≫ pullback.fst (D.obj i).hom f
  let o : pullback a a ⟶ pullback g g := modelCoverOverlapMap (D.obj i).hom f g O.ι
  have hmo : m ≫ o = modelCoverOverlapMap c.pt.hom f g α :=
    modelCoverOverlapMap_naturality (c.π.app i) f g α O.ι d
      (modelOpenRecovery_ι (c.π.app i) f g α O hrec') Hd.toCommSq
  have hrange : Set.range (pullback.snd (c.π.app i).left r) ⊆ (o ⁻¹ᵁ W).carrier := by
    rw [selfOverlapCoefficient_range (c.π.app i) f b a d Hd]
    rintro z ⟨v, rfl⟩
    change o (m v) ∈ W
    have hv := hW ⟨v, rfl⟩
    have hp : o (m v) = modelCoverOverlapMap c.pt.hom f g α v :=
      (Scheme.Hom.comp_apply m o v).symm.trans (congrArg (fun k => k v) hmo)
    exact hp.symm ▸ hv
  have : IsAffine O := hO
  have : QuasiCompact r := selfOverlapCoefficient_quasiCompact f a
  let D₀ := D ⋙ Over.forget S
  let c₀ := (Over.forget S).mapCone c
  have hc₀ : IsLimit c₀ := isLimitOfPreserves (Over.forget S) hc
  have : ∀ {i j : I} (a : i ⟶ j), IsAffineHom (D₀.map a) :=
    fun a => inferInstanceAs (IsAffineHom (D.map a).left)
  have : ∀ i : I, CompactSpace (D₀.obj i) :=
    fun i => inferInstanceAs (CompactSpace (D.obj i).left)
  obtain ⟨j, t, ht⟩ := exists_range_subset_later_stage D₀ c₀ hc₀ i r (o ⁻¹ᵁ W) hrange
  let O' : (pullback (D.obj j).hom (g ≫ f)).Opens :=
    ((Over.pullback (g ≫ f)).map (D.map t)).left ⁻¹ᵁ O
  have : IsAffineHom ((Over.pullback (g ≫ f)).map (D.map t)).left :=
    MorphismProperty.overPullbackMap
      (P := show MorphismProperty Scheme.{u} from @IsAffineHom)
      (g ≫ f) (D.map t) inferInstance
  have hO' : IsAffineOpen O' := hO.preimage _
  have hrecO' : (cone D c (g ≫ f)).π.app j ⁻¹ᵁ O' = α.opensRange := by
    change (cone D c (g ≫ f)).π.app j ⁻¹ᵁ
      ((diagram D (g ≫ f)).map t ⁻¹ᵁ O) = α.opensRange
    rw [← Scheme.Hom.comp_preimage, (cone D c (g ≫ f)).w t]
    exact hrec
  have hsurj' : Surjective (O'.ι ≫ modelMap (D.obj j).hom f g) := by
    have : Surjective (O.ι ≫ modelMap (D.obj i).hom f g) := hsurj
    exact modelOpenCover_surjective (D.map t) f g O
  refine ⟨j, O', hO', hrecO', hsurj', ?_⟩
  let a' : O'.toScheme ⟶ pullback (D.obj j).hom f := O'.ι ≫ modelMap (D.obj j).hom f g
  let d' : O'.toScheme ⟶ O.toScheme := ((Over.pullback (g ≫ f)).map (D.map t)).left ∣_ O
  have H' : IsPullback d' a' a ((Over.pullback f).map (D.map t)).left :=
    openCover_transition_isPullback (D.map t) f g O
  let m' : pullback a' a' ⟶ pullback a a := pullback.map a' a' a a d' d'
    ((Over.pullback f).map (D.map t)).left H'.w.symm H'.w.symm
  have hm'range : Set.range m' ⊆ (o ⁻¹ᵁ W).carrier := by
    rw [← selfOverlapCoefficient_range (D.map t) f a' a d' H']
    exact ht
  have hm'o : m' ≫ o = modelCoverOverlapMap (D.obj j).hom f g O'.ι :=
    modelCoverOverlapMap_naturality (D.map t) f g O'.ι O.ι d'
      (morphismRestrict_ι _ _) H'.toCommSq
  rintro z ⟨v, rfl⟩
  have hv := hm'range ⟨v, rfl⟩
  have hp : o (m' v) = modelCoverOverlapMap (D.obj j).hom f g O'.ι v :=
    (Scheme.Hom.comp_apply m' o v).symm.trans (congrArg (fun k => k v) hm'o)
  exact hp ▸ hv


/-- The same descent statement with named covering and original-model maps.
The two supplied projection equations are eliminated before applying the
native overlap construction. -/
theorem exists_affine_matched_cover_stage_of_maps
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    [∀ i : I, CompactSpace (D.obj i).left]
    [∀ i : I, QuasiSeparatedSpace (D.obj i).left]
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (g : U ⟶ X) [Etale g] [IsAffine U] [IsAffine V]
    (α : V ⟶ pullback c.pt.hom (g ≫ f)) [hα : IsOpenImmersion α]
    (b : V ⟶ pullback c.pt.hom f) [hSurj : Surjective b] (l : V ⟶ U)
    (hb : α ≫ modelMap c.pt.hom f g = b)
    (hl : α ≫ pullback.snd c.pt.hom (g ≫ f) = l)
    (hw : l ≫ g = b ≫ pullback.snd c.pt.hom f)
    (W : (pullback g g).Opens)
    (hW : Set.range (pullback.map b b g g l l (pullback.snd c.pt.hom f)
      hw.symm hw.symm) ⊆ W.carrier) :
    ∃ (i : I) (O : (pullback (D.obj i).hom (g ≫ f)).Opens),
      IsAffineOpen O ∧ (cone D c (g ≫ f)).π.app i ⁻¹ᵁ O = α.opensRange ∧
      Surjective (O.ι ≫ modelMap (D.obj i).hom f g) ∧
      Set.range (modelCoverOverlapMap (D.obj i).hom f g O.ι) ⊆ W.carrier := by
  subst b
  subst l
  exact exists_affine_matched_cover_stage D c hc f g α W hW

end AlgebraicGeometry.AffineTransitionHom
