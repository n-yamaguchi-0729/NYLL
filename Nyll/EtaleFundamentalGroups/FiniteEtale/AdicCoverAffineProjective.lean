/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineCompletion
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.SchemeTheory.Affine.ClosedBaseChangeSections
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveOverCompletion
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RingHom.Flat

/-!
# Projectivity of the actual completed finite étale cover sections

The actual closed base change identifies its affine section ring with the
original section ring modulo the prescribed ideal power. Composing that
ring equivalence with the actual finite étale cover map supplies the
quotient-ring action on the original native section module, with its
original scalar tower. This coefficient map is finite and flat.

On a locally Noetherian scheme, these actual stages are finite projective
over the original coefficient quotients. The completed compatible-section
module is consequently projective, hence flat, over the completed affine
coefficient ring. No flatness of this constructed module is assumed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)

private theorem levelProjection_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (pullback.fst f (baseInclusion I n)) := by
  have : IsClosedImmersion (baseInclusion I n) :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk (levelIdeal I n)))
      Ideal.Quotient.mk_surjective
  infer_instance

/-- The actual affine coefficient map at the specified closed level
has precisely the original extended ideal-power kernel. -/
theorem levelSection_ker (U : X.affineOpens) (n : ℕ) :
    RingHom.ker ((pullback.fst f (baseInclusion I n)).app U).hom =
      (sectionsIdeal f I U) ^ (n + 1) := by
  have h := Scheme.Hom.ker_app_of_closed_baseChange f
    (pullback.snd f (baseInclusion I n)) (pullback.fst f (baseInclusion I n))
    (CommRingCat.ofHom (Ideal.Quotient.mk (levelIdeal I n)))
    (IsPullback.of_hasPullback f (baseInclusion I n)) Ideal.Quotient.mk_surjective
    U U.property
  let ρ : A →+* Γ(X, U) := (f.constToPresheaf.app (op U.val)).hom
  have hk : RingHom.ker (Ideal.Quotient.mk (levelIdeal I n)) = I ^ (n + 1) :=
    (Ideal.mk_ker (I := levelIdeal I n)).trans (levelIdeal_eq_pow I n)
  have hm := congrArg (Ideal.map ρ) hk
  exact h.trans (hm.trans (Ideal.map_pow ρ I (n + 1)))

/-- Every actual coefficient at the closed level has an original
affine coefficient representative. -/
theorem levelSection_surjective (U : X.affineOpens) (n : ℕ) :
    Function.Surjective ((pullback.fst f (baseInclusion I n)).app U).hom :=
  Scheme.Hom.surjective_app_of_closed_baseChange f
    (pullback.snd f (baseInclusion I n)) (pullback.fst f (baseInclusion I n))
    (CommRingCat.ofHom (Ideal.Quotient.mk (levelIdeal I n)))
    (IsPullback.of_hasPullback f (baseInclusion I n)) Ideal.Quotient.mk_surjective
    U U.property

/-- The genuine affine section ring of the closed level is the
prescribed quotient of the original affine coefficient ring. -/
def levelSectionsQuotientEquiv (U : X.affineOpens) (n : ℕ) :
    (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) ≃+*
      Γ(level f I n, pullback.fst f (baseInclusion I n) ⁻¹ᵁ U) :=
  (Ideal.quotEquivOfEq (levelSection_ker f I U n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (levelSection_surjective f I U n))

/-- The quotient comparison retains the original scheme's section map. -/
theorem levelSectionsQuotientEquiv_mk (U : X.affineOpens) (n : ℕ) (a : Γ(X, U)) :
    levelSectionsQuotientEquiv f I U n (Ideal.Quotient.mk _ a) =
      ((pullback.fst f (baseInclusion I n)).app U).hom a := by
  let e := RingHom.quotientKerEquivOfSurjective (levelSection_surjective f I U n)
  have h₁ := Ideal.quotEquivOfEq_mk (levelSection_ker f I U n).symm a
  have h₂ := RingHom.quotientKerEquivOfSurjective_apply_mk
    (levelSection_surjective f I U n) a
  exact (congrArg e h₁).trans h₂

variable (V : MorphismProperty.Over
  ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))

/-- The actual quotient coefficient map is induced by the actual
finite étale cover of the closed level. -/
def affineSectionCoefficient (U : X.affineOpens) (n : ℕ) :
    (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) →+*
      Γ((cover f I V n).left, coverToOriginal f I V n ⁻¹ᵁ U) :=
  (((cover f I V n).hom).app (pullback.fst f (baseInclusion I n) ⁻¹ᵁ U)).hom.comp
    (levelSectionsQuotientEquiv f I U n).toRingHom

/-- On original coefficients this is precisely the original finite
direct-image algebra action. -/
theorem affineSectionCoefficient_mk (U : X.affineOpens) (n : ℕ) (a : Γ(X, U)) :
    affineSectionCoefficient f I V U n (Ideal.Quotient.mk _ a) =
      ((coverToOriginal f I V n).app U).hom a := by
  let c : (cover f I V n).left ⟶ level f I n := (cover f I V n).hom
  let p : level f I n ⟶ X := pullback.fst f (baseInclusion I n)
  let B : CommRingCat.{u} := Γ((cover f I V n).left, coverToOriginal f I V n ⁻¹ᵁ U)
  let q : Γ(level f I n, p ⁻¹ᵁ U) →+* B := (c.app (p ⁻¹ᵁ U)).hom
  have h₁ := congrArg q (levelSectionsQuotientEquiv_mk f I U n a)
  have h₂ := congrArg (fun k : Γ(X, U) ⟶ B => k.hom a) (Scheme.Hom.comp_app c p U)
  exact h₁.trans h₂.symm

/-- The actual quotient coefficient map is finite. -/
theorem affineSectionCoefficient_finite (U : X.affineOpens) (n : ℕ) :
    (affineSectionCoefficient f I V U n).Finite := by
  let c : (cover f I V n).left ⟶ level f I n := (cover f I V n).hom
  let p : level f I n ⟶ X := pullback.fst f (baseInclusion I n)
  have : IsFinite c := (cover f I V n).prop.1
  have : IsClosedImmersion p := levelProjection_isClosedImmersion f I n
  have hU : IsAffineOpen (p ⁻¹ᵁ U) := U.property.preimage p
  exact (c.finite_app (p ⁻¹ᵁ U) hU).comp (levelSectionsQuotientEquiv f I U n).finite

/-- The actual quotient coefficient map is flat by the original
finite étale cover property. -/
theorem affineSectionCoefficient_flat (U : X.affineOpens) (n : ℕ) :
    (affineSectionCoefficient f I V U n).Flat := by
  let c : (cover f I V n).left ⟶ level f I n := (cover f I V n).hom
  let p : level f I n ⟶ X := pullback.fst f (baseInclusion I n)
  have : IsFinite c := (cover f I V n).prop.1
  have : Etale c := (cover f I V n).prop.2
  have : IsClosedImmersion p := levelProjection_isClosedImmersion f I n
  have hU : IsAffineOpen (p ⁻¹ᵁ U) := U.property.preimage p
  have hW : IsAffineOpen (c ⁻¹ᵁ (p ⁻¹ᵁ U)) := hU.preimage c
  have hc : (c.app (p ⁻¹ᵁ U)).hom.Flat := by
    have hc' := c.flat_appLE hU hW le_rfl
    rw [Scheme.Hom.appLE_eq_app] at hc'
    exact hc'
  exact (RingHom.Flat.of_bijective (levelSectionsQuotientEquiv f I U n).bijective).comp hc

/-- The quotient-ring action on the original native section module,
supplied by its actual finite étale coefficient map. -/
@[instance_reducible]
def affineSectionQuotientModule (U : X.affineOpens) (n : ℕ) :
    Module (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (affineSectionModule f I V U n) := by
  let B : CommRingCat.{u} := Γ((cover f I V n).left, coverToOriginal f I V n ⁻¹ᵁ U)
  let : Algebra (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) B :=
    (affineSectionCoefficient f I V U n).toAlgebra
  exact inferInstanceAs (Module (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) B)

/-- The supplied quotient action extends the same original affine
coefficient action as the native direct-image module. -/
theorem affineSectionQuotient_isScalarTower (U : X.affineOpens) (n : ℕ) :
    let _ : Module (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
        (affineSectionModule f I V U n) := affineSectionQuotientModule f I V U n
    IsScalarTower Γ(X, U) (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (affineSectionModule f I V U n) := by
  intro _moduleQ
  apply IsScalarTower.of_algebraMap_smul
  intro a x
  let B : CommRingCat.{u} := Γ((cover f I V n).left, coverToOriginal f I V n ⁻¹ᵁ U)
  let y : B := x
  change affineSectionCoefficient f I V U n (Ideal.Quotient.mk _ a) * y =
    ((coverToOriginal f I V n).app U).hom a * y
  exact congrArg (fun b : B => b * y) (affineSectionCoefficient_mk f I V U n a)

/-- Each actual stage is projective over the prescribed quotient of
the original affine coefficient ring. -/
theorem affineSectionQuotient_projective [IsLocallyNoetherian X]
    (U : X.affineOpens) (n : ℕ) :
    let _ : Module (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
        (affineSectionModule f I V U n) := affineSectionQuotientModule f I V U n
    Module.Projective (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (affineSectionModule f I V U n) := by
  intro _moduleQ
  let Q := Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)
  let B : CommRingCat.{u} := Γ((cover f I V n).left, coverToOriginal f I V n ⁻¹ᵁ U)
  let : Algebra Q B := (affineSectionCoefficient f I V U n).toAlgebra
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have : Module.Finite Q B := affineSectionCoefficient_finite f I V U n
  have : Module.Flat Q B := affineSectionCoefficient_flat f I V U n
  have : Module.FinitePresentation Q B := Module.finitePresentation_of_finite Q B
  exact Module.Flat.projective_of_finitePresentation (R := Q) (M := B)

/-- The actual completed affine section module of the lifted finite
étale tower is projective over its completed original coefficient ring. -/
theorem completedAffineSections_projective [IsLocallyNoetherian X] (U : X.affineOpens) :
    Module.Projective (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
      (completedAffineSections f I V U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have : ∀ n : ℕ, Module.Finite Γ(X, U) (affineSectionModule f I V U n) :=
    fun n => moduleSheaf_finite_sections f I V n U U.property
  let _moduleQ : ∀ n : ℕ, Module (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (affineSectionModule f I V U n) := fun n => affineSectionQuotientModule f I V U n
  have : ∀ n : ℕ, IsScalarTower Γ(X, U) (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (affineSectionModule f I V U n) :=
    fun n => affineSectionQuotient_isScalarTower f I V U n
  have : ∀ n : ℕ, Module.Projective (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (affineSectionModule f I V U n) := fun n => affineSectionQuotient_projective f I V U n
  have h := AdicModuleSystem.completed_sections_projective
    (fun n => (affineSectionModule f I V U n))
    (fun n => affineSectionTransition f I V U n) (sectionsIdeal f I U)
    (fun n => moduleSheaf_sections_annihilated f I V n U)
    (fun n => moduleTransition_app_surjective f I V n U U.property)
    (fun n => moduleTransition_app_ker f I V n U U.property)
  exact h

/-- Flatness holds for the same constructed module with its original
completed-ring scalar action. -/
theorem completedAffineSections_flat [IsLocallyNoetherian X] (U : X.affineOpens) :
    Module.Flat (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
      (completedAffineSections f I V U) := by
  have : Module.Projective (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
      (completedAffineSections f I V U) := completedAffineSections_projective f I V U
  infer_instance

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
