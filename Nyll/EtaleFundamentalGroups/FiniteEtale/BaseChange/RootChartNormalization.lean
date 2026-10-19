/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.SmoothSchemeChart
import Nyll.SchemeTheory.LocalGeometry.AffineAwayChart
import Nyll.SchemeTheory.Normalization.SourceIso
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The original generic cover on an actual root chart

An affine chart over a DVR gives charts on both the original generic
open and the ramified root base change. Pulling the original generic
cover through those charts and then normalizing gives the restriction
of the single global normalization after the root base change.

The generic-open square comes from the literal away map. Pullback
pasting constructs the comparison of the two actual cover sources;
normalization of that source isomorphism and smooth base change of
normalization give the displayed isomorphism over the root chart.

This supplies the compatibility needed to use the local ramification
calculation on a global generic cover. No cover comparison, normalization
comparison, or extension property is assumed in the public statement.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups

universe u

private def affineAwayMap
    (A D : Type u) [CommRing A] [CommRing D] [Algebra A D] (r : A) :
    Spec (.of (Localization.Away (algebraMap A D r))) ⟶
      Spec (.of (Localization.Away r)) :=
  Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A D) r))

private theorem exists_normalizationIso_of_coverChartSquares
    {Y U X X' V V' W W' : Scheme.{u}}
    (p : Y ⟶ U) [QuasiCompact p] [QuasiSeparated p]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (ρ : X' ⟶ X) (v : V ⟶ X) (v' : V' ⟶ X') [IsOpenImmersion v']
    (a : V' ⟶ V) (i : W ⟶ V) (w : W ⟶ U)
    (i' : W' ⟶ V') [IsOpenImmersion i'] [QuasiCompact i'] (b : W' ⟶ W)
    (hChart : IsPullback i w v j) (hAway : IsPullback i' b a i)
    (hRoot : a ≫ v = v' ≫ ρ) :
    let α := pullback.fst j ρ
    let j' := pullback.snd j ρ
    let p' := pullback.snd p α
    let g := p' ≫ j'
    let q := pullback.snd (pullback.snd p w) b
    let l := q ≫ i'
    ∃ e : l.normalization ≅ pullback g.fromNormalization v',
      e.hom ≫ pullback.snd g.fromNormalization v' = l.fromNormalization := by
  intro α j' p' g q l
  have hOuter : IsPullback i' (b ≫ w) (v' ≫ ρ) j := by
    rw [← hRoot]
    exact hAway.paste_vert hChart
  have hκ : (b ≫ w) ≫ j = (i' ≫ v') ≫ ρ := by
    simpa only [Category.assoc] using hOuter.w.symm
  let κ : W' ⟶ pullback j ρ := pullback.lift (b ≫ w) (i' ≫ v') hκ
  have hκfst : κ ≫ α = b ≫ w := pullback.lift_fst _ _ _
  have hκsnd : κ ≫ j' = i' ≫ v' := pullback.lift_snd _ _ _
  have hGeneric : IsPullback i' κ v' j' := by
    have hOuter' : IsPullback i' (κ ≫ α) (v' ≫ ρ) j := by
      rw [hκfst]
      exact hOuter
    exact hOuter'.of_bot hκsnd.symm (IsPullback.of_hasPullback j ρ).flip
  let z := pullback.fst (pullback.snd p w) b ≫ pullback.fst p w
  have hLocal : IsPullback z q p (b ≫ w) :=
    (IsPullback.of_hasPullback (pullback.snd p w) b).paste_horiz
      (IsPullback.of_hasPullback p w)
  have hz : z ≫ p = (q ≫ κ) ≫ α := by
    calc
      z ≫ p = q ≫ (b ≫ w) := hLocal.w
      _ = q ≫ (κ ≫ α) := congrArg (fun h : W' ⟶ U ↦ q ≫ h) hκfst.symm
      _ = (q ≫ κ) ≫ α := (Category.assoc q κ α).symm
  let m := pullback.lift z (q ≫ κ) hz
  have hmfst : m ≫ pullback.fst p α = z := pullback.lift_fst _ _ _
  have hmsnd : m ≫ p' = q ≫ κ := pullback.lift_snd _ _ _
  have hCover : IsPullback m q p' κ :=
    (IsPullback.of_hasPullback p w).paste_twist_right
      (IsPullback.of_hasPullback p α) b κ hκfst.symm
      (pullback.fst (pullback.snd p w) b) q
      (IsPullback.of_hasPullback (pullback.snd p w) b) hmfst hmsnd
  have hWhole : IsPullback m l g v' := hCover.paste_vert hGeneric.flip
  let eSource := hWhole.isoPullback
  let eNorm := Scheme.Hom.normalizationSourceIso l (pullback.snd g v') eSource
    hWhole.isoPullback_hom_snd
  let e := eNorm ≪≫ asIso (g.normalizationPullback v')
  refine ⟨e, ?_⟩
  change (eNorm.hom ≫ g.normalizationPullback v') ≫
    pullback.snd g.fromNormalization v' = l.fromNormalization
  rw [Category.assoc, Scheme.Hom.normalizationPullback_snd]
  exact Scheme.Hom.normalizationSourceIso_hom_fromNormalization l
    (pullback.snd g v') eSource hWhole.isoPullback_hom_snd

/-- The affine normalized root cover of the original generic cover is
the actual chart restriction of its global relative normalization after
root base change. All chart maps and the source comparison are constructed
from the original smooth chart and the chosen root of the uniformizer. -/
theorem exists_uniformizerRootCoverChartNormalizationIso
    (B A : Type u)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing A] [Algebra B A] [Algebra.Smooth B A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
    (v : Spec (.of A) ⟶ X) [IsOpenImmersion v]
    (hv : v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B A)))
    (n : ℕ) (hn : 0 < n) (π : B) (hπ : Prime π) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away π)))
    let U : Scheme.{u} := pullback f η
    let j : U ⟶ X := pullback.fst f η
    let Bn := AdjoinRoot (Polynomial.X ^ n - Polynomial.C π)
    let s := Spec.map (CommRingCat.ofHom (algebraMap B Bn))
    let ρ : pullback f s ⟶ X := pullback.fst f s
    let r := algebraMap B A π
    let D := AdjoinRoot (Polynomial.X ^ n - Polynomial.C r)
    let a : Spec (.of D) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A D))
    let T := Localization.Away r
    let T' := Localization.Away (algebraMap A D r)
    let i : Spec (.of T) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A T))
    let i' : Spec (.of T') ⟶ Spec (.of D) :=
      Spec.map (CommRingCat.ofHom (algebraMap D T'))
    let b : Spec (.of T') ⟶ Spec (.of T) := affineAwayMap A D r
    ∃ v' : Spec (.of D) ⟶ pullback f s,
      IsOpenImmersion v' ∧ IsPullback a v' v ρ ∧
      ∃ w : Spec (.of T) ⟶ U,
        IsOpenImmersion w ∧ IsPullback i w v j ∧
        ∀ {Y : Scheme.{u}} (p : Y ⟶ U) [QuasiCompact p] [QuasiSeparated p],
          let g := pullback.snd p (pullback.fst j ρ) ≫ pullback.snd j ρ
          let l := pullback.snd (pullback.snd p w) b ≫ i'
          ∃ e : l.normalization ≅ pullback g.fromNormalization v',
            e.hom ≫ pullback.snd g.fromNormalization v' = l.fromNormalization := by
  intro η U j Bn s ρ r D a T T' i i' b
  obtain ⟨v', hv', hRoot, _⟩ :=
    Kummer.exists_uniformizerRootSchemeChart B A f v hv n hn π hπ
  obtain ⟨w, hw, hChart, _⟩ := SchemeTheory.exists_affineAwaySchemeChart B A f v hv π
  refine ⟨v', hv', hRoot, w, hw, hChart, ?_⟩
  intro Y p hQcP hQsP g l
  have : IsOpenImmersion v' := hv'
  have hAway : IsPullback i' b a i := SchemeTheory.isPullback_spec_algebraMap_away A D r
  exact exists_normalizationIso_of_coverChartSquares p j ρ v v' a i w i' b
    hChart hAway hRoot.w

end EtaleFundamentalGroups
