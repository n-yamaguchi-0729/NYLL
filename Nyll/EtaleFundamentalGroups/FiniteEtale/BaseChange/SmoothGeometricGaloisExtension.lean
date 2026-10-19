/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.BaseChange.SmoothGenericNormalization
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.FiniteFamilyModel
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.RootDVRModel
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.RingTheory.Henselian.HenselianIntegralDomainLocal
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.Algebra.Algebra.Tower
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Extending a geometric generic Galois cover over a finite DVR base

Let a smooth geometrically connected family be given over a strictly
Henselian DVR. A Galois cover over the separable closure of its fraction
field extends to a finite étale cover after an actual finite strictly
Henselian DVR base extension. In positive residue characteristic, the
Galois order is required to be prime to that characteristic.

The coefficient model and the ramification-removing uniformizer root are
constructed inside the specified separably closed field. Their generic
open cover has the original Galois order. Its whole relative
normalization supplies the finite étale extension. The cartesian square
and the recovery isomorphism retain the original geometric generic field
and the original cover.

This is the geometric-cover extension step of Stacks Project 58.30.2 and
58.30.3, https://stacks.math.columbia.edu/tag/0C0Q and
https://stacks.math.columbia.edu/tag/0C0R. Comparing the resulting proper
family with its special fibre is a subsequent step. For an arbitrary
geometric generic field, a separate constant-field comparison reduces
the cover to the separable closure used here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

open Kummer

universe u

private theorem exists_cover_recovering_normalization
    {X U W Z : Scheme.{u}} (j : W ⟶ X) (α : W ⟶ U)
    (Y : FiniteEtale U) (q : Z ⟶ X) (ν : Z ⟶ W) (hν : ν ≫ j = q)
    (V : FiniteEtale Z)
    (eV : (FiniteEtale.pullback ν).obj ((FiniteEtale.pullback α).obj Y) ≅ V)
    (g : pullback Y.hom α ⟶ X) [QuasiCompact g] [QuasiSeparated g]
    (hFinite : IsFiniteEtale g.fromNormalization)
    (e : pullback g.fromNormalization j ≅ pullback Y.hom α)
    (he : e.hom ≫ pullback.snd Y.hom α = pullback.snd g.fromNormalization j) :
    ∃ T : FiniteEtale X, Nonempty ((FiniteEtale.pullback q).obj T ≅ V) := by
  have : IsFiniteEtale g.fromNormalization := hFinite
  let T : FiniteEtale X := FiniteEtale.mk g.fromNormalization
  let eGeneric : (FiniteEtale.pullback j).obj T ≅ (FiniteEtale.pullback α).obj Y :=
    MorphismProperty.Over.isoMk e he
  exact ⟨T, ⟨(FiniteEtale.finiteEtalePullbackCompObjIso ν j q hν T).symm ≪≫
    (FiniteEtale.pullback ν).mapIso eGeneric ≪≫ eV⟩⟩

private theorem exists_smoothGeneric_cover_recovery
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (c : ℕ) [CharP (IsLocalRing.ResidueField B) c]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
    [Smooth f] [GeometricallyConnected f] (π : B) (hπ : Prime π) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away π)))
    let U : Scheme.{u} := pullback f η
    ∀ [ConnectedSpace U] (Y : FiniteEtale U) [IsGalois Y],
      (c = 0 ∨ Nat.Coprime (Nat.card (Aut Y)) c) →
      let j : U ⟶ X := pullback.fst f η
      let n := if c = 0 then (Nat.card (Aut Y)).factorial else Nat.card (Aut Y)
      let Bn := AdjoinRoot (Polynomial.X ^ n - Polynomial.C π)
      let s := Spec.map (CommRingCat.ofHom (algebraMap B Bn))
      let X' : Scheme.{u} := pullback f s
      let ρ : X' ⟶ X := pullback.fst f s
      let U' : Scheme.{u} := pullback j ρ
      let α : U' ⟶ U := pullback.fst j ρ
      let j' : U' ⟶ X' := pullback.snd j ρ
      ∀ {Z : Scheme.{u}} (q : Z ⟶ X') (ν : Z ⟶ U') (_ : ν ≫ j' = q)
        (V : FiniteEtale Z),
        ((FiniteEtale.pullback ν).obj ((FiniteEtale.pullback α).obj Y) ≅ V) →
        ∃ T : FiniteEtale X', Nonempty ((FiniteEtale.pullback q).obj T ≅ V) := by
  intro η U hU Y hY hdegree j n Bn s X' ρ U' α j' Z q ν hν V eV
  let y : Y.left ⟶ U := Y.hom
  have : IsFiniteEtale y := Y.prop
  let g : pullback y α ⟶ X' := pullback.snd y α ≫ j'
  have : QuasiCompact g := inferInstance
  have : QuasiSeparated g := inferInstance
  have hExtension := finiteEtale_smoothGenericGalois_normalization B c f π hπ Y hdegree
  obtain ⟨eOpen, heOpen⟩ := hExtension.2
  exact exists_cover_recovering_normalization
    j' α Y q ν hν V eV g hExtension.1 eOpen heOpen

private theorem finiteDVR_baseChange_square
    {B C W : Type u} [CommRing B] [CommRing C] [CommRing W]
    [Algebra B C] [Algebra C W] [Algebra B W] [IsScalarTower B C W]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) :
    let β := Spec.map (CommRingCat.ofHom (algebraMap B C))
    let s := Spec.map (CommRingCat.ofHom (algebraMap C W))
    let βW := Spec.map (CommRingCat.ofHom (algebraMap B W))
    IsPullback (pullback.fst (pullback.snd f β) s ≫ pullback.fst f β)
      (pullback.snd (pullback.snd f β) s) f βW := by
  intro β s βW
  have hBase : s ≫ β = βW := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq B C W).symm
  rw [← hBase]
  exact (IsPullback.of_hasPullback (pullback.snd f β) s).paste_horiz
    (IsPullback.of_hasPullback f β)

/-- A geometric generic Galois cover of a smooth geometrically connected
family extends over an actual finite strictly Henselian DVR extension.
The resulting family and its specified geometric fibre are cartesian
base changes, and the pullback recovers the whole original cover. -/
theorem exists_finite_strictHenselianDVR_geometricGalois_extension
    (B K Ω : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
    [Field K] [Field Ω] [IsSepClosed Ω] [Algebra B K] [IsFractionRing B K]
    [Algebra K Ω] [Algebra B Ω] [IsScalarTower B K Ω] [Algebra.IsSeparable K Ω]
    (c : ℕ) [CharP (IsLocalRing.ResidueField B) c]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of B)) [Smooth f] [GeometricallyConnected f] :
    let η := Spec.map (CommRingCat.ofHom (algebraMap B K))
    let XK : Scheme.{u} := pullback f η
    let fK : XK ⟶ Spec (.of K) := pullback.snd f η
    let φΩ := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let XΩ : Scheme.{u} := pullback φΩ fK
    let pΩ : XΩ ⟶ Spec (.of Ω) := pullback.fst φΩ fK
    let pX : XΩ ⟶ X := pullback.snd φΩ fK ≫ pullback.fst f η
    let : ConnectedSpace XΩ :=
      GeometricallyConnected.connectedSpace_of_subsingleton (f := pΩ)
    ∀ (Z : FiniteEtale XΩ) [IsGalois Z],
      (c = 0 ∨ Nat.Coprime (Nat.card (Aut Z)) c) →
      ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W)
        (_ : IsDiscreteValuationRing W) (_ : Algebra B W),
        Module.Finite B W ∧ HenselianLocalRing W ∧
          IsSepClosed (IsLocalRing.ResidueField W) ∧
          ∃ ϑ : W →ₐ[B] Ω, Function.Injective ϑ ∧
            let βW := Spec.map (CommRingCat.ofHom (algebraMap B W))
            let b := Spec.map (CommRingCat.ofHom ϑ.toRingHom)
            ∃ (X' : Scheme.{u}) (r : X' ⟶ X) (f' : X' ⟶ Spec (.of W)),
              IsPullback r f' f βW ∧
              ∃ q : XΩ ⟶ X', q ≫ r = pX ∧ IsPullback q pΩ f' b ∧
                ∃ T : FiniteEtale X',
                  Nonempty ((FiniteEtale.pullback q).obj T ≅ Z) := by
  intro η XK fK φΩ XΩ pΩ pX hXΩ Z hZ hdegree
  obtain ⟨H, _, _, hCDVR, _, _, hCharC,
    π, hπ, hU, Y, hY, hCard, hn, hWFinite, hWHenselian, hWSep,
    ϑ, hϑ, q, hqX, hq, ν, hνj, ⟨eZ⟩⟩ :=
    FiniteEtale.exists_strictHenselianRootDVR_galois_model B K Ω c X f Z hdegree
  let C : Type u := integralClosure B H
  let : IsLocalRing C := SchemeTheory.isLocalRing_of_integral_domain_henselian B C
  have : IsDiscreteValuationRing C := hCDVR
  have : CharP (IsLocalRing.ResidueField C) c := hCharC
  have : IsScalarTower B H Ω := IsScalarTower.of_algebraMap_eq fun b ↦ by
    rw [IsScalarTower.algebraMap_apply B K H,
      ← IsScalarTower.algebraMap_apply K H Ω, ← IsScalarTower.algebraMap_apply B K Ω]
  have : IsScalarTower B C Ω := IsScalarTower.subalgebra' B H Ω (integralClosure B H)
  let β := Spec.map (CommRingCat.ofHom (algebraMap B C))
  let XC : Scheme.{u} := pullback f β
  let fC : XC ⟶ Spec (.of C) := pullback.snd f β
  have : Smooth fC := inferInstanceAs (Smooth (pullback.snd f β))
  have : GeometricallyConnected fC :=
    inferInstanceAs (GeometricallyConnected (pullback.snd f β))
  let ε : Spec (.of (Localization.Away π)) ⟶ Spec (.of C) :=
    Spec.map (CommRingCat.ofHom (R := C) (S := Localization.Away π)
      (algebraMap C (Localization.Away π)))
  let U : Scheme.{u} := pullback fC ε
  let j : U ⟶ XC := pullback.fst fC ε
  have : ConnectedSpace U := hU
  have : IsGalois Y := hY
  have hDegreeY : c = 0 ∨ Nat.Coprime (Nat.card (Aut Y)) c := by
    rw [hCard]
    exact hdegree
  let n := if c = 0 then (Nat.card (Aut Y)).factorial else Nat.card (Aut Y)
  let W : Type u := AdjoinRoot (Polynomial.X ^ n - Polynomial.C π)
  have : IsDomain W := isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
  have : IsDiscreteValuationRing W :=
    isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
  let ϑB : W →ₐ[B] Ω := ϑ.restrictScalars B
  let βW := Spec.map (CommRingCat.ofHom (algebraMap B W))
  let s := Spec.map (CommRingCat.ofHom (algebraMap C W))
  let XW : Scheme.{u} := pullback fC s
  let ρ : XW ⟶ XC := pullback.fst fC s
  let fW : XW ⟶ Spec (.of W) := pullback.snd fC s
  let U' : Scheme.{u} := pullback j ρ
  let α : U' ⟶ U := pullback.fst j ρ
  let j' : U' ⟶ XW := pullback.snd j ρ
  obtain ⟨T, hRecovery⟩ := exists_smoothGeneric_cover_recovery
    C c fC π hπ Y hDegreeY q ν hνj Z eZ
  have hRootSquare : IsPullback (ρ ≫ pullback.fst f β) fW f βW :=
    finiteDVR_baseChange_square (B := B) (C := C) (W := W) f
  exact ⟨W, inferInstance, inferInstance, inferInstance, inferInstance,
    hWFinite, hWHenselian, hWSep, ϑB, hϑ, XW, ρ ≫ pullback.fst f β, fW,
    hRootSquare, q, hqX, hq, T, hRecovery⟩

end EtaleFundamentalGroups
