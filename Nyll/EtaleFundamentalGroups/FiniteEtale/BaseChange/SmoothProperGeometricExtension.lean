/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.BaseChange.SmoothGeometricGaloisExtension
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.FiniteFamilyModel
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ProperGeometricGaloisModel
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Smooth proper extension for the originally specified geometric field

A Galois cover of the geometric generic fibre of a smooth proper,
geometrically connected family over a strictly Henselian DVR extends
after a finite strictly Henselian DVR base change. In positive residue
characteristic its Galois order is required to be prime to that
characteristic. The specified geometric field need not be algebraic or
separable over the original fraction field.

Proper constant-field comparison first descends the original cover to
the relative separable closure inside the given geometric field, with
the same deck-transformation group order. The finite DVR normalized
extension over this separable closure then applies. Composing the actual
field embeddings and cartesian squares returns to the original geometric
field and the original cover. Quasi-compactness and quasi-separatedness
are supplied by properness, rather than added to the hypotheses.

This supplies the cover-extension step for Stacks Project 58.30.2 and
58.30.3, https://stacks.math.columbia.edu/tag/0C0Q and
https://stacks.math.columbia.edu/tag/0C0R. The subsequent proper henselian
comparison is needed to deduce the specialization statement on
fundamental groups.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

universe u

/-- The originally specified geometric generic Galois cover of a smooth
proper family extends over an actual finite strictly Henselian DVR base
change. Both cartesian squares and the recovery isomorphism use that same
geometric field. -/
theorem exists_finite_strictHenselianDVR_smoothProperGalois_extension
    (B K Ω : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
    [Field K] [Field Ω] [IsSepClosed Ω] [Algebra B K] [IsFractionRing B K]
    [Algebra K Ω] [Algebra B Ω] [IsScalarTower B K Ω]
    (c : ℕ) [CharP (IsLocalRing.ResidueField B) c]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
    [IsProper f] [Smooth f] [GeometricallyConnected f] :
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
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : IsProper fK := inferInstanceAs (IsProper (pullback.snd f η))
  obtain ⟨hXS, q₀, hq₀X, hq₀, Y, hY, hCard, ⟨eZ⟩⟩ :=
    FiniteEtale.exists_galois_model_over_relativeSeparableClosure K Ω fK Z
  let S := separableClosure K Ω
  have : IsSepClosed S := (inferInstance : IsSepClosure K S).sep_closed
  have : IsScalarTower B S Ω := IsScalarTower.of_algebraMap_eq fun b ↦ by
    rw [IsScalarTower.algebraMap_apply B K S,
      ← IsScalarTower.algebraMap_apply K S Ω, ← IsScalarTower.algebraMap_apply B K Ω]
  let φS := Spec.map (CommRingCat.ofHom (algebraMap K S))
  let XS : Scheme.{u} := pullback φS fK
  have : ConnectedSpace XS := hXS
  have : IsGalois Y := hY
  have hDegreeY : c = 0 ∨ Nat.Coprime (Nat.card (Aut Y)) c := by
    rw [hCard]
    exact hdegree
  obtain ⟨W, hCommW, hDomainW, hDVRW, hAlgW, hFiniteW, hHenselianW, hSepW,
    ϑ₀, hϑ₀, X', r, f', hRoot, qS, hqSX, hqS, T, ⟨eY⟩⟩ :=
    exists_finite_strictHenselianDVR_geometricGalois_extension B K S c X f Y hDegreeY
  let ϑ : W →ₐ[B] Ω := (IsScalarTower.toAlgHom B S Ω).comp ϑ₀
  have hϑ : Function.Injective ϑ := (algebraMap S Ω).injective.comp hϑ₀
  let b₀ := Spec.map (CommRingCat.ofHom (algebraMap S Ω))
  let bS := Spec.map (CommRingCat.ofHom ϑ₀.toRingHom)
  let b := Spec.map (CommRingCat.ofHom ϑ.toRingHom)
  have hCoeff : b₀ ≫ bS = b := by
    rw [← Spec.map_comp]
    rfl
  let q : XΩ ⟶ X' := q₀ ≫ qS
  have hqX : q ≫ r = pX := by
    change (q₀ ≫ qS) ≫ r = pX
    rw [Category.assoc, hqSX, ← Category.assoc, hq₀X]
  have hq : IsPullback q pΩ f' b := by
    rw [← hCoeff]
    exact hq₀.paste_horiz hqS
  have hRecovery : Nonempty ((FiniteEtale.pullback q).obj T ≅ Z) :=
    ⟨(FiniteEtale.finiteEtalePullbackCompObjIso q₀ qS q rfl T).symm ≪≫
      (FiniteEtale.pullback q₀).mapIso eY ≪≫ eZ⟩
  exact ⟨W, hCommW, hDomainW, hDVRW, hAlgW, hFiniteW, hHenselianW, hSepW,
    ϑ, hϑ, X', r, f', hRoot, q, hqX, hq, T, hRecovery⟩

end EtaleFundamentalGroups
