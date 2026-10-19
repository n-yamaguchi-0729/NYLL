/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.SmoothCharacteristicZeroNormalization
import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.SmoothGaloisNormalization
import Nyll.EtaleFundamentalGroups.FiniteEtale.BaseChange.RootChartNormalization
import Nyll.EtaleFundamentalGroups.GaloisCovers.SmoothGenericCharts
import Nyll.SchemeTheory.LocalGeometry.DVRFiberCover
import Nyll.SchemeTheory.LocalGeometry.SmoothGenericNormal
import Nyll.SchemeTheory.Normalization.IntegralOpen
import Nyll.SchemeTheory.Normalization.Normal
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Galois.GaloisObjects
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Extending a whole smooth generic Galois cover by normalization

Let a smooth geometrically connected scheme be given over a DVR. A
finite étale Galois cover of its actual generic open extends after one
uniformizer-root base change. In residue characteristic zero the chosen
exponent is the factorial of its Galois order. In positive residue
characteristic the order itself works when it is prime to that
characteristic.

The extension is the relative normalization of the single original
base-changed cover. Its restriction to the generic open is that same
cover. Every closed-fibre point has an actual prime-fibre smooth chart;
the restriction of the Galois cover to each such chart has the original
Galois order. The affine normalization theorem therefore uses the same
root on every chart. The actual normalization comparisons identify
these local calculations with restrictions of the global normalization,
and target Zariski locality proves that this global morphism is finite
étale. No chart extension or gluing comparison is an input.

This is the global normalized-extension step in Stacks Project 58.30.2
and 58.30.3, https://stacks.math.columbia.edu/tag/0C0Q and
https://stacks.math.columbia.edu/tag/0C0R. Properness is not required for
this extension step. Descending arbitrary geometric generic covers and
comparing them with the special fibre are subsequent steps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

universe u

/-- One uniformizer root extends the original whole generic Galois cover
of a smooth geometrically connected family by its actual normalization.
The exponent is the Galois order in positive characteristic, and its
factorial in characteristic zero. The actual generic cover is recovered. -/
theorem finiteEtale_smoothGenericGalois_normalization
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (c : ℕ) [CharP (IsLocalRing.ResidueField B) c]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
    [Smooth f] [GeometricallyConnected f] (π : B) (hπ : Prime π) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away π)))
    let U : Scheme.{u} := pullback f η
    let : IsIntegral U :=
      Smooth.isIntegral_awayBaseChange_of_geometricallyConnected f π hπ.ne_zero
    let : IsNormalIntegral U :=
      Smooth.isNormalIntegral_awayBaseChange_of_geometricallyConnected f π hπ.ne_zero
    let j : U ⟶ X := pullback.fst f η
    ∀ (Y : FiniteEtale U) [IsGalois Y],
      (c = 0 ∨ Nat.Coprime (Nat.card (Aut Y)) c) →
      let n := if c = 0 then (Nat.card (Aut Y)).factorial else Nat.card (Aut Y)
      let Bn := AdjoinRoot (Polynomial.X ^ n - Polynomial.C π)
      let s := Spec.map (CommRingCat.ofHom (algebraMap B Bn))
      let X' : Scheme.{u} := pullback f s
      let ρ : X' ⟶ X := pullback.fst f s
      let U' : Scheme.{u} := pullback j ρ
      let α : U' ⟶ U := pullback.fst j ρ
      let j' : U' ⟶ X' := pullback.snd j ρ
      let y : Y.left ⟶ U := Y.hom
      let : IsFiniteEtale y := Y.prop
      let p' : pullback y α ⟶ U' := pullback.snd y α
      let g : pullback y α ⟶ X' := p' ≫ j'
      let : QuasiCompact g := inferInstance
      let : QuasiSeparated g := inferInstance
      IsFiniteEtale g.fromNormalization ∧
        ∃ e : pullback g.fromNormalization j' ≅ pullback y α,
          e.hom ≫ p' = pullback.snd g.fromNormalization j' := by
  intro η U hIntegralU hNormalU j Y hGaloisY hdegree
    n Bn s X' ρ U' α j' y hFiniteEtaleY p' g hQcG hQsG
  have hn : 0 < n := by
    by_cases hc : c = 0
    · change 0 < if c = 0 then (Nat.card (Aut Y)).factorial else Nat.card (Aut Y)
      rw [ite_eq_left hc]
      exact Nat.factorial_pos _
    · change 0 < if c = 0 then (Nat.card (Aut Y)).factorial else Nat.card (Aut Y)
      rw [ite_eq_right hc]
      exact Nat.card_pos
  have hLocality : IsZariskiLocalAtTarget
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) :=
    ((HasAffineProperty.iff (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (Q := affineAnd RingHom.FiniteEtale)).mp inferInstance).1
  have hRespects : MorphismProperty.RespectsIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) := hLocality.toRespects
  let eOpen := Scheme.Hom.integralOpenNormalizationIso p' j'
  have hGeneric : IsFiniteEtale (pullback.snd g.fromNormalization j') := by
    have hComp : IsFiniteEtale
        (eOpen.hom ≫ pullback.snd g.fromNormalization j') := by
      rw [Scheme.Hom.integralOpenNormalizationIso_hom_snd]
      exact ⟨⟩
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) eOpen.hom
      (pullback.snd g.fromNormalization j')).mp hComp
  have hFiniteEtale : IsFiniteEtale g.fromNormalization := by
    apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
    intro x
    rcases SchemeTheory.mem_genericFiber_or_closedFiber_of_DVR B f π hπ (ρ x) with
      hxGeneric | hxClosed
    · have hx : x ∈ Set.range j' := by
        change x ∈ Set.range (pullback.snd j ρ)
        rw [Scheme.Pullback.range_snd]
        exact hxGeneric
      refine ⟨j'.opensRange, hx, ?_⟩
      exact (MorphismProperty.arrow_mk_iso_iff
        (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
        (morphismRestrictOpensRange g.fromNormalization j')).mpr hGeneric
    · obtain ⟨z, hz⟩ := hxClosed
      obtain ⟨A, hA, hr, hSmooth, v, hv, hzv, hvf, w, hw, hChart, hGalois, hCard⟩ :=
        exists_smoothGenericGaloisChart B f π hπ Y z
      have : IsDomain A := hA
      have : Algebra.Smooth B A := hSmooth
      have : IsOpenImmersion v := hv
      have : IsOpenImmersion w := hw
      let r := algebraMap B A π
      let T := Localization.Away r
      have : IsDomain T := IsLocalization.Away.isDomain T hr.ne_zero
      let P : FiniteEtale (Spec (.of T)) := (FiniteEtale.pullback w).obj Y
      have : IsGalois P := hGalois
      obtain ⟨v', hv', hRoot, w', hw', hChart', hNorm⟩ :=
        exists_uniformizerRootCoverChartNormalizationIso B A f v hvf n hn π hπ
      have hww : w' = w :=
        (cancel_mono j).mp (hChart'.w.symm.trans hChart.w)
      subst w'
      have : IsOpenImmersion v' := hv'
      let D := AdjoinRoot (Polynomial.X ^ n - Polynomial.C r)
      let T' := Localization.Away (algebraMap A D r)
      let : Algebra T T' := (Localization.awayMap (algebraMap A D) r).toAlgebra
      let b : Spec (.of T') ⟶ Spec (.of T) :=
        Spec.map (CommRingCat.ofHom (algebraMap T T'))
      let i' : Spec (.of T') ⟶ Spec (.of D) :=
        Spec.map (CommRingCat.ofHom (algebraMap D T'))
      let l := pullback.snd (pullback.snd y w) b ≫ i'
      have hLocal : IsFiniteEtale l.fromNormalization := by
        by_cases hc : c = 0
        · have hCharP : CharP (IsLocalRing.ResidueField B) 0 :=
            hc ▸ (inferInstance : CharP (IsLocalRing.ResidueField B) c)
          have : CharZero (IsLocalRing.ResidueField B) :=
            CharP.charP_to_charZero (IsLocalRing.ResidueField B)
          obtain ⟨m, hm, _, hEtale, _⟩ :=
            exists_finiteEtale_smoothPrimeFiberCharacteristicZeroCover_normalization
              B A π hπ hr P
          have hmn : m = n := by
            change m = if c = 0 then (Nat.card (Aut Y)).factorial else Nat.card (Aut Y)
            rw [ite_eq_left hc]
            exact hm.trans (congrArg Nat.factorial hCard)
          clear hm
          subst m
          exact hEtale
        · have hcPrime : c.Prime :=
            (CharP.char_is_prime_or_zero (IsLocalRing.ResidueField B) c).resolve_right hc
          have hCoprime : Nat.Coprime (Nat.card (Aut P)) c :=
            hCard.symm ▸ hdegree.resolve_left hc
          obtain ⟨m, hm, _, hEtale, _⟩ :=
            exists_finiteEtale_smoothPrimeFiberGaloisCover_normalization
              B A c hcPrime π hπ hr P hCoprime
          have hmn : m = n := by
            change m = if c = 0 then (Nat.card (Aut Y)).factorial else Nat.card (Aut Y)
            rw [ite_eq_right hc]
            exact hm.trans hCard
          clear hm
          subst m
          exact hEtale
      obtain ⟨e, he⟩ := hNorm y
      have hPullback : IsFiniteEtale (pullback.snd g.fromNormalization v') := by
        have hComp : IsFiniteEtale (e.hom ≫ pullback.snd g.fromNormalization v') := by
          rw [he]
          exact hLocal
        exact (MorphismProperty.cancel_left_of_respectsIso
          (@IsFiniteEtale : MorphismProperty Scheme.{u}) e.hom
          (pullback.snd g.fromNormalization v')).mp hComp
      have hxv : ρ x ∈ Set.range v := hz ▸ hzv
      have hRange : Set.range v' = ρ ⁻¹' Set.range v :=
        (range_eq_range_of_surjective v' (pullback.snd v ρ) hRoot.isoPullback.hom
          hRoot.isoPullback_hom_snd).trans (Scheme.Pullback.range_snd v ρ)
      have hxPreimage : x ∈ ρ ⁻¹' Set.range v := hxv
      have hx : x ∈ v'.opensRange := by
        change x ∈ Set.range v'
        rw [hRange]
        exact hxPreimage
      refine ⟨v'.opensRange, hx, ?_⟩
      exact (MorphismProperty.arrow_mk_iso_iff
        (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
        (morphismRestrictOpensRange g.fromNormalization v')).mpr hPullback
  refine ⟨hFiniteEtale, eOpen.symm, ?_⟩
  change eOpen.inv ≫ p' = pullback.snd g.fromNormalization j'
  have hOpen : eOpen.hom ≫ pullback.snd g.fromNormalization j' = p' :=
    Scheme.Hom.integralOpenNormalizationIso_hom_snd p' j'
  exact (congrArg (fun k => eOpen.inv ≫ k) hOpen).symm.trans
    (eOpen.inv_hom_id_assoc (pullback.snd g.fromNormalization j'))

end EtaleFundamentalGroups
