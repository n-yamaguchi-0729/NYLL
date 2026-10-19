/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.FiniteFamilyModel
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.GaloisDVRModel
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.StrictHenselianRootEmbedding
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.RingTheory.Henselian.HenselianIntegralDomainLocal
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.CharP.Algebra
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# A geometric generic cover after an embedded finite DVR root extension

A Galois cover over a separably closed algebraic extension of the generic
field descends to the generic open of an actual finite strictly Henselian
DVR normalization. Its automorphism order is unchanged. Adjoining the
uniformizer root of that order, or its factorial in residue characteristic
zero, gives another actual finite strictly Henselian DVR inside the same
specified geometric field.

The geometric fibre map to this root base change is constructed from the
two original coordinates. Pullback pasting proves that its square over the
root DVR is cartesian. The map factors through the pulled-back generic
open, and the pulled-back descended cover recovers the original cover.

This is the coefficient and root-base reduction for the smooth proper
specialization argument. No normalized-extension theorem is used here.
The extension across the special fibre is a subsequent step. The given
geometric field is assumed separable over the original fraction field;
in particular, it may be the chosen separable closure of that field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

open EtaleFundamentalGroups EtaleFundamentalGroups.Kummer

universe u

/-- A geometric generic Galois cover admits an actual finite strictly
Henselian DVR root model inside the specified separably closed field.
The geometric-fibre square is cartesian, and its restriction to the
generic open recovers the whole original cover. -/
theorem exists_strictHenselianRootDVR_galois_model
    (B K Ω : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
    [Field K] [Field Ω] [IsSepClosed Ω] [Algebra B K] [IsFractionRing B K]
    [Algebra K Ω] [Algebra B Ω] [IsScalarTower B K Ω] [Algebra.IsSeparable K Ω]
    (c : ℕ) [CharP (IsLocalRing.ResidueField B) c]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of B)) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap B K))
    let XK : Scheme.{u} := Limits.pullback f η
    let fK : XK ⟶ Spec (.of K) := Limits.pullback.snd f η
    let φΩ := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let XΩ : Scheme.{u} := Limits.pullback φΩ fK
    let pΩ : XΩ ⟶ Spec (.of Ω) := Limits.pullback.fst φΩ fK
    let pX : XΩ ⟶ X := Limits.pullback.snd φΩ fK ≫ Limits.pullback.fst f η
    ∀ [ConnectedSpace XΩ] (Z : FiniteEtale XΩ) [IsGalois Z],
    (c = 0 ∨ Nat.Coprime (Nat.card (Aut Z)) c) →
    ∃ H : IntermediateField K Ω, FiniteDimensional K H ∧
      let C := integralClosure B H
      let : IsLocalRing C := SchemeTheory.isLocalRing_of_integral_domain_henselian B C
      Module.Finite B C ∧ ∃ hCDVR : IsDiscreteValuationRing C,
        let : IsDiscreteValuationRing C := hCDVR
        HenselianLocalRing C ∧
        IsSepClosed (IsLocalRing.ResidueField C) ∧ CharP (IsLocalRing.ResidueField C) c ∧
        ∃ π : C, ∃ hπ : Prime π,
          let β := Spec.map (CommRingCat.ofHom (algebraMap B C))
          let XC : Scheme.{u} := Limits.pullback f β
          let fC : XC ⟶ Spec (.of C) := Limits.pullback.snd f β
          let ε := Spec.map (CommRingCat.ofHom (R := C) (S := Localization.Away π)
            (algebraMap C (Localization.Away π)))
          let U : Scheme.{u} := Limits.pullback fC ε
          let j : U ⟶ XC := Limits.pullback.fst fC ε
          ∃ hU : ConnectedSpace U,
            let : ConnectedSpace U := hU
            ∃ Y : FiniteEtale U, IsGalois Y ∧ Nat.card (Aut Y) = Nat.card (Aut Z) ∧
              let n := if c = 0 then (Nat.card (Aut Y)).factorial else Nat.card (Aut Y)
              ∃ hn : 0 < n,
                let W := AdjoinRoot (Polynomial.X ^ n - Polynomial.C π)
                let : IsDomain W := isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
                let : IsDiscreteValuationRing W :=
                  isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
                Module.Finite B W ∧ HenselianLocalRing W ∧
                  IsSepClosed (IsLocalRing.ResidueField W) ∧
                  ∃ ϑ : W →ₐ[C] Ω, Function.Injective ϑ ∧
                    let b := Spec.map (CommRingCat.ofHom ϑ.toRingHom)
                    let s := Spec.map (CommRingCat.ofHom (algebraMap C W))
                    let XW : Scheme.{u} := Limits.pullback fC s
                    let ρ : XW ⟶ XC := Limits.pullback.fst fC s
                    let fW : XW ⟶ Spec (.of W) := Limits.pullback.snd fC s
                    let U' : Scheme.{u} := Limits.pullback j ρ
                    let α : U' ⟶ U := Limits.pullback.fst j ρ
                    let j' : U' ⟶ XW := Limits.pullback.snd j ρ
                    ∃ q : XΩ ⟶ XW,
                      q ≫ ρ ≫ Limits.pullback.fst f β = pX ∧
                      IsPullback q pΩ fW b ∧
                      ∃ ν : XΩ ⟶ U', ν ≫ j' = q ∧
                        Nonempty ((pullback ν).obj ((pullback α).obj Y) ≅ Z) := by
  intro η XK fK φΩ XΩ pΩ pX hXΩ Z hZ hdegree
  obtain ⟨H, hH, hCFinite, _, hCDVR, hCHenselian, hCSep, hCLocal,
    π, hπ, e, heX, heC, hU, Y, hY, hCard, ⟨eZ⟩⟩ :=
    exists_strictHenselianDVR_galois_model B K Ω X f Z
  have : FiniteDimensional K H := hH
  let C := integralClosure B H
  let : IsLocalRing C := SchemeTheory.isLocalRing_of_integral_domain_henselian B C
  have : IsScalarTower B H Ω := IsScalarTower.of_algebraMap_eq fun b ↦ by
    rw [IsScalarTower.algebraMap_apply B K H,
      ← IsScalarTower.algebraMap_apply K H Ω, ← IsScalarTower.algebraMap_apply B K Ω]
  have : IsScalarTower B C Ω := IsScalarTower.subalgebra' B H Ω C
  have : Module.Finite B C := hCFinite
  have : IsDiscreteValuationRing C := hCDVR
  have : HenselianLocalRing C := hCHenselian
  have : IsSepClosed (IsLocalRing.ResidueField C) := hCSep
  have : IsLocalHom (algebraMap B C) := hCLocal
  have hCharC : CharP (IsLocalRing.ResidueField C) c :=
    charP_of_injective_algebraMap
      (algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField C)).injective c
  have hPrime : Prime π := hπ.prime
  let β := Spec.map (CommRingCat.ofHom (algebraMap B C))
  let XC : Scheme.{u} := Limits.pullback f β
  let fC : XC ⟶ Spec (.of C) := Limits.pullback.snd f β
  let ε : Spec (.of (Localization.Away π)) ⟶ Spec (.of C) :=
    Spec.map (CommRingCat.ofHom (R := C) (S := Localization.Away π)
      (algebraMap C (Localization.Away π)))
  let U : Scheme.{u} := Limits.pullback fC ε
  let j : U ⟶ XC := Limits.pullback.fst fC ε
  have : ConnectedSpace U := hU
  have : IsGalois Y := hY
  let n := if c = 0 then (Nat.card (Aut Y)).factorial else Nat.card (Aut Y)
  have hn : 0 < n := by
    by_cases hc : c = 0
    · change 0 < if c = 0 then (Nat.card (Aut Y)).factorial else Nat.card (Aut Y)
      rw [ite_eq_left hc]
      exact Nat.factorial_pos _
    · change 0 < if c = 0 then (Nat.card (Aut Y)).factorial else Nat.card (Aut Y)
      rw [ite_eq_right hc]
      exact Nat.card_pos
  have hnDegree : c = 0 ∨ Nat.Coprime n c := by
    by_cases hc : c = 0
    · exact Or.inl hc
    · apply Or.inr
      change Nat.Coprime (if c = 0 then _ else Nat.card (Aut Y)) c
      rw [ite_eq_right hc, hCard]
      exact hdegree.resolve_left hc
  let W := AdjoinRoot (Polynomial.X ^ n - Polynomial.C π)
  have : IsDomain W := isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hPrime
  have : IsDiscreteValuationRing W :=
    isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime hn π hPrime
  obtain ⟨hWFinite, hWHenselian, hWSep, ϑ, hϑ⟩ :=
    exists_strictHenselianUniformizerRoot_embedding C Ω c n hn hnDegree π hPrime
  have : Module.Finite C W := hWFinite
  have hWFiniteB : Module.Finite B W := Module.Finite.trans (R := B) C W
  let b := Spec.map (CommRingCat.ofHom ϑ.toRingHom)
  let s := Spec.map (CommRingCat.ofHom (algebraMap C W))
  let XW : Scheme.{u} := Limits.pullback fC s
  let ρ : XW ⟶ XC := Limits.pullback.fst fC s
  let fW : XW ⟶ Spec (.of W) := Limits.pullback.snd fC s
  let U' : Scheme.{u} := Limits.pullback j ρ
  let α : U' ⟶ U := Limits.pullback.fst j ρ
  let j' : U' ⟶ XW := Limits.pullback.snd j ρ
  let φH := Spec.map (CommRingCat.ofHom (algebraMap K H))
  let XH : Scheme.{u} := Limits.pullback φH fK
  let cH : XΩ ⟶ XH := Limits.pullback.map φΩ fK φH fK
    (Spec.map (CommRingCat.ofHom H.val.toRingHom)) (𝟙 XK) (𝟙 _)
    (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
    (by rw [Category.comp_id, Category.id_comp])
  let a : XΩ ⟶ U := cH ≫ e.inv
  let θC := Spec.map (CommRingCat.ofHom (algebraMap C Ω))
  let μ := Spec.map (CommRingCat.ofHom (algebraMap C H))
  have hcHFst : cH ≫ Limits.pullback.fst φH fK =
      pΩ ≫ Spec.map (CommRingCat.ofHom H.val.toRingHom) := by
    exact Limits.pullback.lift_fst _ _ _
  have hcHSnd : cH ≫ Limits.pullback.snd φH fK = Limits.pullback.snd φΩ fK := by
    simp only [cH, Limits.pullback.lift_snd, Category.comp_id]
  have hCoeffC : Spec.map (CommRingCat.ofHom H.val.toRingHom) ≫ μ = θC := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq C H Ω).symm
  have hRootC : b ≫ s = θC := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact ϑ.comp_algebraMap
  have haX : a ≫ j ≫ Limits.pullback.fst f β = pX := by
    calc
      _ = cH ≫ e.inv ≫ e.hom ≫
          Limits.pullback.snd φH fK ≫ Limits.pullback.fst f η := by
        rw [heX]
        exact Category.assoc _ _ _
      _ = pX := by
        rw [Iso.inv_hom_id_assoc, ← Category.assoc, hcHSnd]
  have haC : a ≫ j ≫ fC = pΩ ≫ θC := by
    calc
      _ = a ≫ Limits.pullback.snd fC ε ≫ ε := by
        rw [Limits.pullback.condition]
      _ = cH ≫ e.inv ≫ e.hom ≫ Limits.pullback.fst φH fK ≫ μ := by
        rw [heC]
        exact Category.assoc _ _ _
      _ = pΩ ≫ θC := by
        rw [Iso.inv_hom_id_assoc, ← Category.assoc, hcHFst, Category.assoc, hCoeffC]
  let q : XΩ ⟶ XW := Limits.pullback.lift (a ≫ j) (pΩ ≫ b)
    (by rw [Category.assoc, haC, Category.assoc, hRootC])
  have hqρ : q ≫ ρ = a ≫ j := Limits.pullback.lift_fst _ _ _
  have hqW : q ≫ fW = pΩ ≫ b := Limits.pullback.lift_snd _ _ _
  have hqX : q ≫ ρ ≫ Limits.pullback.fst f β = pX := by
    rw [← Category.assoc, hqρ, Category.assoc, haX]
  have hCoeffB : θC ≫ β = φΩ ≫ η := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq B C Ω).symm.trans
      (IsScalarTower.algebraMap_eq B K Ω)
  have hRootB : b ≫ s ≫ β = φΩ ≫ η := by
    rw [← Category.assoc, hRootC, hCoeffB]
  have hOuter : IsPullback (q ≫ (ρ ≫ Limits.pullback.fst f β)) pΩ f
      (b ≫ (s ≫ β)) := by
    rw [hqX, hRootB]
    exact (IsPullback.of_hasPullback φΩ fK).flip.paste_horiz
      (IsPullback.of_hasPullback f η)
  have hq : IsPullback q pΩ fW b :=
    hOuter.of_right hqW ((IsPullback.of_hasPullback fC s).paste_horiz
      (IsPullback.of_hasPullback f β))
  let ν : XΩ ⟶ U' := Limits.pullback.lift a q hqρ.symm
  have hνα : ν ≫ α = a := Limits.pullback.lift_fst _ _ _
  have hνj : ν ≫ j' = q := Limits.pullback.lift_snd _ _ _
  have hRecovery : Nonempty ((pullback ν).obj ((pullback α).obj Y) ≅ Z) :=
    ⟨finiteEtalePullbackCompObjIso ν α a hνα Y ≪≫ eZ⟩
  exact ⟨H, hH, hCFinite, hCDVR, hCHenselian, hCSep, hCharC, π, hPrime,
    hU, Y, hY, hCard, hn, hWFiniteB, hWHenselian, hWSep, ϑ, hϑ,
    q, hqX, hq, ν, hνj, hRecovery⟩

end AlgebraicGeometry.FiniteEtale
