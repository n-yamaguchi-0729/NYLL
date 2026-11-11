/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineProjective
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Étaleness of the original affine quotient coefficients

The actual coefficient map from the original affine ideal-power quotient
is the section map of the constructed finite étale cover, preceded by
the proved identification of the closed-level section ring. Its étaleness
therefore follows directly from the original cover, with no completed
algebra or effective ordinary-scheme cover assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))

/-- The original quotient coefficient map is étale by the actual cover
property and the constructed quotient comparison. -/
theorem affineSectionCoefficient_etale (U : X.affineOpens) (n : ℕ) :
    (affineSectionCoefficient f I V U n).Etale := by
  let c : (cover f I V n).left ⟶ level f I n := (cover f I V n).hom
  let p : level f I n ⟶ X := pullback.fst f (baseInclusion I n)
  have : IsFinite c := (cover f I V n).prop.1
  have : Etale c := (cover f I V n).prop.2
  have : IsClosedImmersion (baseInclusion I n) :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk (levelIdeal I n)))
      Ideal.Quotient.mk_surjective
  have : IsClosedImmersion p := inferInstance
  have hU : IsAffineOpen (p ⁻¹ᵁ U) := U.property.preimage p
  have hW : IsAffineOpen (c ⁻¹ᵁ (p ⁻¹ᵁ U)) := hU.preimage c
  have hc : (c.app (p ⁻¹ᵁ U)).hom.Etale := by
    have hc' := c.etale_appLE hU hW le_rfl
    rw [Scheme.Hom.appLE_eq_app] at hc'
    exact hc'
  apply RingHom.Etale.stableUnderComposition
  · exact RingHom.Etale.of_bijective (levelSectionsQuotientEquiv f I U n).bijective
  · exact hc

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
