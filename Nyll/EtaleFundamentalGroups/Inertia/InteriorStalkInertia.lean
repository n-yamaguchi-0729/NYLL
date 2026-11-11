/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceStalk
public import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkGaloisRestriction
public import Nyll.EtaleFundamentalGroups.StrictHenselian.FundamentalGroup
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisNaturality

/-!
# Full original inertia at an interior point is killed

The actual strict local ring at the specified normalization prime supplies
a generic field whose absolute Galois restriction image is the full original
inertia. Its map to the original scheme factors through that same strict
local ring, whose fundamental group is trivial. Naturality of the original
field-source map therefore kills every inertia element, including wild
inertia, at every point of the original open scheme.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups.StrictHenselian

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] normalizationInertiaImageAction

/-- Full inertia at an actual stalk of the original scheme maps trivially
through the original generic field-source map. The strict-local comparison
and its factorization through the scheme are constructed internally. -/
theorem genericFieldSourceStalk_inertia_image_eq_bot
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    (K Ω : Type u) [Field K] [Field Ω]
    [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]
    (g : Spec (.of K) ⟶ U) [IsDominant g] [IsPreimmersion g] (x : U) :
    let A := U.presheaf.stalk x
    let : Algebra A K := genericFieldSourceStalkAlgebra g x
    let : IsFractionRing A K := genericFieldSourceStalk_isFractionRing g x
    let : Algebra A Ω := ((algebraMap K Ω).comp (algebraMap A K)).toAlgebra
    let : IsScalarTower A K Ω := IsScalarTower.of_algebraMap_eq' rfl
    ∀ (Q : Ideal (integralClosure A Ω)) [Q.IsMaximal],
      (Q.inertia Gal(Ω/K)).map (fieldSourceAbsoluteGaloisHom K Ω g).toMonoidHom = ⊥ := by
  intro A instAK fraction instAΩ tower Q hQ
  have : IsIntegrallyClosed A := IsNormalIntegral.stalk_isIntegrallyClosed x
  have : Algebra.IsAlgebraic A Ω :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := Ω)).mpr inferInstance
  have : FaithfulSMul A Ω :=
    (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := Ω)).mp
      (Module.IsTorsionFree.trans_faithfulSMul A K Ω)
  have : HenselianLocalRing (Localization.AtPrime Q) :=
    (integralClosure_primeLocalization_strictHenselian_of_algebraic A Ω Q).1
  have : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
    (integralClosure_primeLocalization_strictHenselian_of_algebraic A Ω Q).2
  let ψ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
    (integralClosurePrimeBaseMap A Ω Q)
  have : IsLocalHom ψ := normalizationResiduePoint_isLocalHom A Ω Q
  let S := geometricStalk (Spec.map (CommRingCat.ofHom ψ))
  let E := FractionRing S
  let : Algebra K E := (normalizationStalkFractionBaseMap A K Ω Q).toAlgebra
  let : Algebra E Ω := (geometricStalkFractionToNormalizationField A Ω Q).toAlgebra
  have : IsScalarTower K E Ω := normalizationStalkFractionField_isScalarTower A K Ω Q
  have : IsSepClosure E Ω := normalizationStalkFractionField_isSepClosure A K Ω Q
  let s : Spec (.of E) ⟶ Spec (.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S E))
  let u : Spec (.of S) ⟶ U :=
    Spec.map (CommRingCat.ofHom (geometricStalkStructureMap ψ)) ≫ U.fromSpecStalk x
  have hcoeff : (algebraMap K E).comp (algebraMap A K) =
      (algebraMap S E).comp (geometricStalkStructureMap ψ) := by
    apply RingHom.ext
    intro a
    exact normalizationStalkFractionBaseMap_algebraMap A K Ω Q a
  have hspec : ξ K E ≫ Spec.map (CommRingCat.ofHom (algebraMap A K)) =
      s ≫ Spec.map (CommRingCat.ofHom (geometricStalkStructureMap ψ)) := by
    change Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A K)) =
      Spec.map (CommRingCat.ofHom (algebraMap S E)) ≫
        Spec.map (CommRingCat.ofHom (geometricStalkStructureMap ψ))
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : A →+* E => Spec.map (CommRingCat.ofHom f)) hcoeff
  have hr : ξ K E ≫ g = s ≫ u := by
    calc
      ξ K E ≫ g = ξ K E ≫
          (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ U.fromSpecStalk x) :=
        congrArg (fun f => ξ K E ≫ f) (genericFieldSourceStalkMap_fromSpecStalk g x).symm
      _ = (ξ K E ≫ Spec.map (CommRingCat.ofHom (algebraMap A K))) ≫
          U.fromSpecStalk x := (Category.assoc _ _ _).symm
      _ = (s ≫ Spec.map (CommRingCat.ofHom (geometricStalkStructureMap ψ))) ≫
          U.fromSpecStalk x := congrArg (fun f => f ≫ U.fromSpecStalk x) hspec
      _ = s ≫ u := Category.assoc _ _ _
  have hpoint : (ξ E Ω ≫ s) ≫ u = ξ K Ω ≫ g := by
    rw [Category.assoc, ← hr, ← Category.assoc, fieldGeometricPoint_comp K E Ω]
  have : Subsingleton π₁ᵉᵗ(ξ E Ω ≫ s) :=
    subsingleton_fundamentalGroup_geometricStalk
      (Spec.map (CommRingCat.ofHom ψ)) (ξ E Ω ≫ s)
  have hrestriction : (AlgEquiv.restrictScalarsHom K : Gal(Ω/E) →* Gal(Ω/K)).range =
      Q.inertia Gal(Ω/K) := geometricStalkAbsoluteGalois_restriction_range A K Ω Q
  apply (Subgroup.eq_bot_iff_forall _).mpr
  rintro a ⟨σ, hσ, rfl⟩
  obtain ⟨τ, rfl⟩ := (show σ ∈
    (AlgEquiv.restrictScalarsHom K : Gal(Ω/E) →* Gal(Ω/K)).range from hrestriction.symm ▸ hσ)
  have h := fieldSourceAbsoluteGaloisHom_naturality K E Ω u s g hpoint τ
  have hzero : fieldSourceAbsoluteGaloisHom E Ω s τ = 1 := Subsingleton.elim _ _
  rw [hzero, map_one, map_one] at h
  exact h.symm

end EtaleFundamentalGroups.Inertia
