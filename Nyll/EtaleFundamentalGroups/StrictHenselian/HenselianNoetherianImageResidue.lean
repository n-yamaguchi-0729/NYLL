/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianImageStages
public import Nyll.SchemeTheory.Descent.NoetherianImageResidueLimit
public import Nyll.SchemeTheory.RingTheory.Ramification.NativeMaximalResidue
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Residue fields of the actual henselian Noetherian image stages

The image inclusions are local. Thus the contracted stage primes in
`SubalgebraStages.residueDiagram` are the actual maximal ideals. Their
canonical quotient-to-residue equivalences intertwine the existing
residue transitions and the local-ring residue maps.

The colimit proof is supplied by `SubalgebraStages.residueCoconeIsColimit`,
with the actual exhaustive image family. Only its vertex is transported
along the existing maximal-quotient equivalence, so the cocone has the
original local-ring residue field as its literal vertex. The original
quotient maps are retained in its base triangles.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite
open EtaleFundamentalGroups.Inertia

namespace AlgebraicGeometry.HenselianNoetherianImageStages

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [HenselianLocalRing A]

/-- The inclusion between two actual henselian image stages is local:
its composite with the target inclusion is the original local inclusion. -/
instance image_inclusion_isLocalHom {i j : FGSubalgebra R A} (h : i ≤ j) :
    IsLocalHom (Subalgebra.inclusion (image_mono R A h)).toRingHom := by
  have : IsLocalHom ((image R A j).val.toRingHom.comp
      (Subalgebra.inclusion (image_mono R A h)).toRingHom) := by
    change IsLocalHom (image R A i).val.toRingHom
    infer_instance
  exact isLocalHom_of_comp
    (Subalgebra.inclusion (image_mono R A h)).toRingHom (image R A j).val.toRingHom

/-- The prime used by the exhaustive-subalgebra residue diagram is the
actual maximal ideal of each constructed henselian image. -/
theorem image_residuePrime_eq_maximalIdeal (i : FGSubalgebra R A) :
    SubalgebraStages.residuePrime (images R A) (IsLocalRing.maximalIdeal A) i =
      IsLocalRing.maximalIdeal (image R A i) :=
  IsLocalRing.maximalIdeal_comap (image R A i).val.toRingHom

/-- The actual contracted-prime residue field is canonically the native
local-ring residue quotient of the same image stage. -/
def imageResidueFieldEquiv (i : FGSubalgebra R A) :
    (SubalgebraStages.residuePrime
      (images R A) (IsLocalRing.maximalIdeal A) i).ResidueField ≃+*
        IsLocalRing.ResidueField (image R A i) := by
  let p := SubalgebraStages.residuePrime (images R A) (IsLocalRing.maximalIdeal A) i
  have hp : p = IsLocalRing.maximalIdeal (image R A i) :=
    image_residuePrime_eq_maximalIdeal R A i
  have : p.IsMaximal :=
    hp.symm ▸ (inferInstance : (IsLocalRing.maximalIdeal (image R A i)).IsMaximal)
  exact (maximalQuotientResidueEquiv p).symm.trans (Ideal.quotEquivOfEq hp)

/-- The stage comparison preserves the original residue projection. -/
theorem imageResidueFieldEquiv_algebraMap (i : FGSubalgebra R A)
    (a : image R A i) :
    imageResidueFieldEquiv R A i
        (algebraMap (image R A i)
          (SubalgebraStages.residuePrime
            (images R A) (IsLocalRing.maximalIdeal A) i).ResidueField a) =
      IsLocalRing.residue (image R A i) a := by
  let p := SubalgebraStages.residuePrime (images R A) (IsLocalRing.maximalIdeal A) i
  have hp : p = IsLocalRing.maximalIdeal (image R A i) :=
    image_residuePrime_eq_maximalIdeal R A i
  have : p.IsMaximal :=
    hp.symm ▸ (inferInstance : (IsLocalRing.maximalIdeal (image R A i)).IsMaximal)
  let e := maximalQuotientResidueEquiv p
  have ha : e (Ideal.Quotient.mk p a) = algebraMap (image R A i) p.ResidueField a :=
    RingHom.congr_fun (maximalQuotientResidueEquiv_comp_quotient p) a
  change Ideal.quotEquivOfEq hp (e.symm (algebraMap (image R A i) p.ResidueField a)) =
    IsLocalRing.residue (image R A i) a
  rw [← ha, e.symm_apply_apply]
  exact Ideal.quotEquivOfEq_mk hp a

/-- The existing residue transition becomes the actual local-ring
residue map of the original inclusion under the canonical comparisons. -/
theorem imageResidueFieldEquiv_transition {i j : FGSubalgebra R A} (h : i ≤ j) :
    (imageResidueFieldEquiv R A j).toRingHom.comp
        (SubalgebraStages.residueTrans (images R A) (IsLocalRing.maximalIdeal A) h) =
      (@IsLocalRing.ResidueField.map (image R A i) (image R A j) _ _ _ _
        (Subalgebra.inclusion (image_mono R A h)).toRingHom
          (image_inclusion_isLocalHom R A h)).comp
          (imageResidueFieldEquiv R A i).toRingHom := by
  have : IsLocalHom (Subalgebra.inclusion (image_mono R A h)).toRingHom :=
    image_inclusion_isLocalHom R A h
  apply Ideal.ResidueField.ringHom_ext
  apply RingHom.ext
  intro a
  let ψ : IsLocalRing.ResidueField (image R A i) →+*
      IsLocalRing.ResidueField (image R A j) :=
    IsLocalRing.ResidueField.map (Subalgebra.inclusion (image_mono R A h)).toRingHom
  exact (congrArg (imageResidueFieldEquiv R A j)
    (SubalgebraStages.residueTrans_algebraMap
      (images R A) (IsLocalRing.maximalIdeal A) h a)).trans
    ((imageResidueFieldEquiv_algebraMap R A j
      (Subalgebra.inclusion (image_mono R A h) a)).trans
      ((IsLocalRing.ResidueField.map_residue
        (Subalgebra.inclusion (image_mono R A h)).toRingHom a).symm.trans
        (congrArg ψ (imageResidueFieldEquiv_algebraMap R A i a).symm)))

/-- The existing maximal-quotient equivalence with the actual cocone
vertex and native residue quotient fixed as its categorical endpoints. -/
def imageResidueVertexIso :
    (SubalgebraStages.residueCocone (images R A) (IsLocalRing.maximalIdeal A)).pt ≅
      CommRingCat.of (IsLocalRing.ResidueField A) :=
  (maximalQuotientResidueEquiv (IsLocalRing.maximalIdeal A)).symm.toCommRingCatIso

/-- The existing image-residue cocone, with vertex the literal residue
quotient of the original henselian ring. -/
def imageResidueCocone :
    Cocone (SubalgebraStages.residueDiagram (images R A) (IsLocalRing.maximalIdeal A)) :=
  (SubalgebraStages.residueCocone (images R A) (IsLocalRing.maximalIdeal A)).extend
    (imageResidueVertexIso R A).hom

/-- Exhaustivity of the actual image family supplies the existing
colimit; extension by the canonical residue isomorphism preserves it. -/
def imageResidueCoconeIsColimit : IsColimit (imageResidueCocone R A) :=
  IsColimit.extendIso
    (s := SubalgebraStages.residueCocone (images R A) (IsLocalRing.maximalIdeal A))
    (imageResidueVertexIso R A).hom
    (SubalgebraStages.residueCoconeIsColimit
      (images R A) (IsLocalRing.maximalIdeal A) (exhaustive R A))

/-- The transported cocone retains the original inclusion followed
by the native residue projection, at every actual image stage. -/
theorem imageResidueCocone_leg_comp_algebraMap (i : FGSubalgebra R A) :
    ((imageResidueCocone R A).ι.app i).hom.comp
        (algebraMap (image R A i)
          (SubalgebraStages.residuePrime
            (images R A) (IsLocalRing.maximalIdeal A) i).ResidueField) =
      (IsLocalRing.residue A).comp (image R A i).val.toRingHom := by
  apply RingHom.ext
  intro a
  change (maximalQuotientResidueEquiv (IsLocalRing.maximalIdeal A)).symm
      (SubalgebraStages.residueLeg (images R A) (IsLocalRing.maximalIdeal A) i
        (algebraMap (image R A i)
          (SubalgebraStages.residuePrime
            (images R A) (IsLocalRing.maximalIdeal A) i).ResidueField a)) =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (a : A)
  let e := maximalQuotientResidueEquiv (IsLocalRing.maximalIdeal A)
  have he : e.symm (algebraMap A (IsLocalRing.maximalIdeal A).ResidueField (a : A)) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (a : A) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (RingHom.congr_fun
      (maximalQuotientResidueEquiv_comp_quotient (IsLocalRing.maximalIdeal A)) (a : A)).symm
  exact (congrArg e.symm (SubalgebraStages.residueLeg_algebraMap
    (images R A) (IsLocalRing.maximalIdeal A) i a)).trans he

/-- The original local-ring residue point maps to the existing system
of actual contracted residue spectra. -/
def imageResidueSpecCone :
    Cone (SubalgebraStages.residueSpecDiagram (images R A) (IsLocalRing.maximalIdeal A)) :=
  Scheme.Spec.mapCone (imageResidueCocone R A).op

/-- The spectrum of the original native residue field is the limit
of the actual image-stage residue spectra. -/
def imageResidueSpecConeIsLimit : IsLimit (imageResidueSpecCone R A) :=
  isLimitOfPreserves Scheme.Spec (imageResidueCoconeIsColimit R A).op

/-- The residue-spectrum limit projections commute with the original
image inclusions and the native closed point of the original ring. -/
@[reassoc]
theorem imageResidueSpecCone_projection_base (i : (FGSubalgebra R A)ᵒᵖ) :
    (imageResidueSpecCone R A).π.app i ≫
        SubalgebraStages.residueSpecBase (images R A) (IsLocalRing.maximalIdeal A) i =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
        (SubalgebraStages.specCone (images R A)).π.app i := by
  change Spec.map ((imageResidueCocone R A).ι.app i.unop) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (image R A i.unop)
        (SubalgebraStages.residuePrime
          (images R A) (IsLocalRing.maximalIdeal A) i.unop).ResidueField)) =
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      Spec.map (CommRingCat.ofHom (image R A i.unop).val.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact imageResidueCocone_leg_comp_algebraMap R A i.unop

end AlgebraicGeometry.HenselianNoetherianImageStages
