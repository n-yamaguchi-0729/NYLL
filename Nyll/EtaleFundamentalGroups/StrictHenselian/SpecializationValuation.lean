/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.SeparablyClosedFractionHenselian
import Nyll.ValuedFieldTheory.Valuation.ResidueAlgebraicClosedness
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Valuation rings realizing the ring diagram of specialization

Given any homomorphism from a local ring `A` to a field `Ω`, choose a valuation
subring of `Ω` through which that homomorphism factors locally. The factor
map and its residue-field map retain both commutative squares on spectra.
When `Ω` is algebraically closed, the valuation ring is henselian and its
residue field is algebraically closed. These properties are proved for the
constructed valuation ring; they are not additional input data.

This is the ring construction in the proof of Stacks Project, Lemma
58.16.3, https://stacks.math.columbia.edu/tag/0C0M. The comparison of
fundamental groups of proper geometric fibres is a separate assertion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u v

section Rings

variable {A : Type u} [CommRing A] [IsLocalRing A]
  {Ω : Type v} [Field Ω] (φ : A →+* Ω)

/-- A valuation subring in the specified generic field which dominates the
image of the local source ring. The source map need not be injective. -/
def specializationValuationSubring : ValuationSubring Ω :=
  Classical.choose (IsLocalRing.exists_factor_valuationRing φ)

private theorem specializationValuation_mem (a : A) :
    φ a ∈ (specializationValuationSubring φ).toSubring :=
  Classical.choose (Classical.choose_spec (IsLocalRing.exists_factor_valuationRing φ)) a

/-- The original homomorphism with codomain restricted to the actual chosen
valuation subring. -/
def specializationValuationMap : A →+* specializationValuationSubring φ :=
  φ.codRestrict (specializationValuationSubring φ).toSubring
    (specializationValuation_mem φ)

instance specializationValuationMap_isLocalHom :
    IsLocalHom (specializationValuationMap φ) :=
  Classical.choose_spec
    (Classical.choose_spec (IsLocalRing.exists_factor_valuationRing φ))

/-- The generic-field leg of the chosen factorization is the original map. -/
theorem specializationValuationMap_comp :
    (algebraMap (specializationValuationSubring φ) Ω).comp
      (specializationValuationMap φ) = φ := by
  apply RingHom.ext
  intro a
  rfl

/-- The closed-field leg is the native map of residue fields of the local
factor map. -/
def specializationValuationResidueMap :
    IsLocalRing.ResidueField A →+*
      IsLocalRing.ResidueField (specializationValuationSubring φ) :=
  IsLocalRing.ResidueField.map (specializationValuationMap φ)

/-- The closed-field square commutes with the literal quotient maps. -/
theorem specializationValuationResidueMap_comp :
    (specializationValuationResidueMap φ).comp (IsLocalRing.residue A) =
      (IsLocalRing.residue (specializationValuationSubring φ)).comp
        (specializationValuationMap φ) :=
  IsLocalRing.ResidueField.map_comp_residue (specializationValuationMap φ)

/-- The algebraic input of the valuation reduction of specialization:
the given generic-field map factors locally through a henselian valuation
ring in that same field, with algebraically closed residue field and a
compatible residue-field map. No finiteness or normality of `A` is required. -/
theorem exists_strictlyHenselianValuationFactor [IsAlgClosed Ω] :
    ∃ (V : ValuationSubring Ω) (f : A →+* V)
      (g : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField V),
      HenselianLocalRing V ∧ IsAlgClosed (IsLocalRing.ResidueField V) ∧
      IsLocalHom f ∧ (algebraMap V Ω).comp f = φ ∧
      g.comp (IsLocalRing.residue A) = (IsLocalRing.residue V).comp f := by
  let V : ValuationSubring Ω := specializationValuationSubring φ
  have hHenselian : HenselianLocalRing V :=
    henselianLocalRing_of_isSepClosed_fractionRing V Ω
  have hResidue : IsAlgClosed (IsLocalRing.ResidueField V) :=
    ValuationSubring.isAlgClosed_residueField V
  exact ⟨V, specializationValuationMap φ, specializationValuationResidueMap φ,
    hHenselian, hResidue, specializationValuationMap_isLocalHom φ,
    specializationValuationMap_comp φ, specializationValuationResidueMap_comp φ⟩

end Rings

section Schemes

variable {A Ω : Type u} [CommRing A] [IsLocalRing A] [Field Ω]
  (φ : A →+* Ω)

/-- On spectra, the generic geometric point factors through the chosen
valuation spectrum by the actual inclusion of its fraction field. -/
theorem specializationValuation_genericTriangle :
    Spec.map (CommRingCat.ofHom (algebraMap (specializationValuationSubring φ) Ω)) ≫
      Spec.map (CommRingCat.ofHom (specializationValuationMap φ)) =
        Spec.map (CommRingCat.ofHom φ) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, specializationValuationMap_comp]

/-- The residue-field square on spectra uses precisely the same local
factor map as the generic triangle. -/
theorem specializationValuation_residueSquare :
    Spec.map (CommRingCat.ofHom
        (IsLocalRing.residue (specializationValuationSubring φ))) ≫
      Spec.map (CommRingCat.ofHom (specializationValuationMap φ)) =
        Spec.map (CommRingCat.ofHom (specializationValuationResidueMap φ)) ≫
          Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, specializationValuationResidueMap_comp]

/-- The chosen valuation ring is centered at the specified closed point of
the local source, not just at an arbitrary point of its spectrum. -/
theorem specializationValuation_closedPoint :
    Spec.map (CommRingCat.ofHom (specializationValuationMap φ))
      (IsLocalRing.closedPoint (specializationValuationSubring φ)) =
        IsLocalRing.closedPoint A := by
  change PrimeSpectrum.comap (specializationValuationMap φ)
    (IsLocalRing.closedPoint (specializationValuationSubring φ)) =
      IsLocalRing.closedPoint A
  exact IsLocalRing.comap_closedPoint (specializationValuationMap φ)

end Schemes

end EtaleFundamentalGroups.StrictHenselian
