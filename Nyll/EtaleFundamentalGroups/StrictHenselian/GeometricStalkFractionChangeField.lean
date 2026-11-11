/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkChangeFieldIso
public import Nyll.EtaleFundamentalGroups.StrictHenselian.CartierGenericPoint
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Changing the pointing field of an actual strict-local generic morphism

The isomorphism of actual geometric stalks extends to their literal fraction
fields. Its coefficient equation proves that the original maps into a
Cartier complement commute. This permits comparing inertia defined using
the standard residue-field closure with inertia using a normalization prime.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω Ω' : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field Ω] [IsSepClosed Ω] [Field Ω'] (φ : R →+* Ω) (ι : Ω →+* Ω')

/-- The field isomorphism induced by the actual change-of-pointing-field
isomorphism of geometric stalks. -/
def geometricStalkFractionChangeFieldEquiv :
    FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ≃+*
      FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom (ι.comp φ)))) :=
  IsFractionRing.ringEquivOfRingEquiv
    (geometricStalkChangeFieldIso φ ι).commRingCatIsoToRingEquiv

omit [IsDomain R] [IsIntegrallyClosed R] in
/-- The fraction-field comparison retains the original base-ring map. -/
theorem geometricStalkFractionChangeFieldEquiv_comp_structure :
    (geometricStalkFractionChangeFieldEquiv φ ι).toRingHom.comp
        ((algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
          (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))).comp
            (geometricStalkStructureMap φ)) =
      (algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom (ι.comp φ))))
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom (ι.comp φ)))))).comp
          (geometricStalkStructureMap (ι.comp φ)) := by
  apply RingHom.ext
  intro a
  change geometricStalkFractionChangeFieldEquiv φ ι
      (algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ))) _
        (geometricStalkStructureMap φ a)) = _
  exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (geometricStalkChangeFieldIso φ ι).commRingCatIsoToRingEquiv
    (geometricStalkStructureMap φ a)).trans
    (congrArg
      (algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom (ι.comp φ))))
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom (ι.comp φ))))))
      (RingHom.congr_fun (geometricStalkChangeField_comp_structure φ ι) a))

/-- The comparison of strict-local generic fields commutes with the literal
maps into the Cartier complement. -/
theorem geometricStalkFractionChangeFieldEquiv_toComplement
    {X : Scheme.{u}} (D : X.EffectiveCartierDivisor) (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsSepClosed Ω'] (ψ : X.presheaf.stalk x →+* Ω) [IsLocalHom ψ] :
    Spec.map (CommRingCat.ofHom (geometricStalkFractionChangeFieldEquiv ψ ι).toRingHom) ≫
        geometricStalkFractionFieldToComplement D x ψ =
      geometricStalkFractionFieldToComplement D x (ι.comp ψ) := by
  let S := geometricStalk (Spec.map (CommRingCat.ofHom ψ))
  let S' := geometricStalk (Spec.map (CommRingCat.ofHom (ι.comp ψ)))
  let a : X.presheaf.stalk x →+* FractionRing S :=
    (algebraMap S (FractionRing S)).comp (geometricStalkStructureMap ψ)
  let a' : X.presheaf.stalk x →+* FractionRing S' :=
    (algebraMap S' (FractionRing S')).comp (geometricStalkStructureMap (ι.comp ψ))
  let e := geometricStalkFractionChangeFieldEquiv ψ ι
  have he : e.toRingHom.comp a = a' :=
    geometricStalkFractionChangeFieldEquiv_comp_structure ψ ι
  have hspec : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom a') :=
    (Spec.map_comp (CommRingCat.ofHom a) (CommRingCat.ofHom e.toRingHom)).symm.trans
      (congrArg (fun f : X.presheaf.stalk x →+* FractionRing S' =>
        Spec.map (CommRingCat.ofHom f)) he)
  apply (cancel_mono D.1.supportComplement.ι).mp
  rw [Category.assoc, geometricStalkFractionFieldToComplement_comp_ι,
    geometricStalkFractionFieldToComplement_comp_ι]
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom a) ≫ X.fromSpecStalk x) =
    Spec.map (CommRingCat.ofHom a') ≫ X.fromSpecStalk x
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ X.fromSpecStalk x) hspec)

end EtaleFundamentalGroups.StrictHenselian
