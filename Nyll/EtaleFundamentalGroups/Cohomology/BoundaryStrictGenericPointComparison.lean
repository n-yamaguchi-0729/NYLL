/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionChangeField
public import Nyll.EtaleFundamentalGroups.Cohomology.BoundaryFillingAbelianization
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The original strict-local boundary source at an arbitrary residue point

Two separably closed residue points over the same local ring are compared
through a common algebraically closed field. The actual change-of-field
maps identify their strict-local generic schemes over the Cartier complement.
In particular this applies to the residue point of an original normalization
prime, without assuming any comparison of inertia subgroups.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open Yamaguchi26SolvableCoverings
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleFundamentalGroups.Cohomology

universe u

private theorem exists_fractionComplementIso_of_eq
    {X : Scheme.{u}} (D : X.EffectiveCartierDivisor) (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (φ ψ : X.presheaf.stalk x →+* Ω) [IsLocalHom φ] [IsLocalHom ψ]
    (h : φ = ψ) :
    ∃ e : Spec (.of (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))) ≅
        Spec (.of (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom ψ))))),
      e.hom ≫ geometricStalkFractionFieldToComplement D x ψ =
        geometricStalkFractionFieldToComplement D x φ := by
  subst ψ
  exact ⟨Iso.refl _, Category.id_comp _⟩

/-- An arbitrary separably closed local residue point gives the same actual
strict-local generic source over the complement as the standard boundary
residue point. -/
theorem exists_boundaryStrictGenericMorphism_iso
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    (E : Component D) {L : Type u} [Field L] [IsSepClosed L]
    (ψ : X.presheaf.stalk (componentPoint D E) →+* L) [IsLocalHom ψ] :
    let : IsDomain (X.presheaf.stalk (componentPoint D E)) :=
      isDomain_stalk_componentPoint D hreg E
    let : IsDiscreteValuationRing (X.presheaf.stalk (componentPoint D E)) :=
      isDiscreteValuationRing_stalk_componentPoint D hreg E
    let : Field (boundaryStrictFractionField D E) := boundaryStrictFractionFieldField D hreg E
    ∃ e : Spec (.of (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom ψ))))) ≅
        Spec (.of (boundaryStrictFractionField D E)),
      e.hom ≫ boundaryStrictGenericMorphism D hreg E =
        geometricStalkFractionFieldToComplement D (componentPoint D E) ψ := by
  intro hDomain hDVR hField
  let x := componentPoint D E
  let A := X.presheaf.stalk x
  let κ := X.residueField x
  let : Algebra κ L := (IsLocalRing.ResidueField.lift ψ).toAlgebra
  let : Algebra κ (AlgebraicClosure L) :=
    ((algebraMap L (AlgebraicClosure L)).comp (IsLocalRing.ResidueField.lift ψ)).toAlgebra
  let β : AlgebraicClosure κ →ₐ[κ] AlgebraicClosure L := IsAlgClosed.lift
  let φ := boundaryComponentResidueMap D E
  let ι : L →+* AlgebraicClosure L := algebraMap L (AlgebraicClosure L)
  have hpoints : β.toRingHom.comp φ = ι.comp ψ := by
    apply RingHom.ext
    intro a
    change β (algebraMap κ (AlgebraicClosure κ) (IsLocalRing.residue A a)) = ι (ψ a)
    exact (β.commutes (IsLocalRing.residue A a)).trans
      (congrArg ι (IsLocalRing.ResidueField.lift_residue_apply ψ a))
  let e₁ := Scheme.Spec.mapIso
    (geometricStalkFractionChangeFieldEquiv φ β.toRingHom).toCommRingCatIso.op
  let e₂ := Scheme.Spec.mapIso
    (geometricStalkFractionChangeFieldEquiv ψ ι).toCommRingCatIso.op
  have he₁ : e₁.hom ≫ geometricStalkFractionFieldToComplement D x φ =
      geometricStalkFractionFieldToComplement D x (β.toRingHom.comp φ) :=
    geometricStalkFractionChangeFieldEquiv_toComplement β.toRingHom D x φ
  have he₂ : e₂.hom ≫ geometricStalkFractionFieldToComplement D x ψ =
      geometricStalkFractionFieldToComplement D x (ι.comp ψ) :=
    geometricStalkFractionChangeFieldEquiv_toComplement ι D x ψ
  obtain ⟨e₃, he₃⟩ := exists_fractionComplementIso_of_eq D x
    (β.toRingHom.comp φ) (ι.comp ψ) hpoints
  refine ⟨e₂.symm ≪≫ e₃.symm ≪≫ e₁, ?_⟩
  change (e₂.inv ≫ e₃.inv ≫ e₁.hom) ≫
      geometricStalkFractionFieldToComplement D x φ =
    geometricStalkFractionFieldToComplement D x ψ
  rw [Category.assoc, Category.assoc, he₁]
  rw [(e₃.inv_comp_eq).mpr he₃.symm]
  exact (e₂.inv_comp_eq).mpr he₂.symm

end EtaleFundamentalGroups.Cohomology
