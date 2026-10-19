/- 
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.Algebra.Category.Grp.Basic
import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
import Nyll.EtaleCohomology.Classical.AffineGenericUnitQuotient
import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
import Nyll.EtaleFundamentalGroups.Cohomology.AffineGenericPointStalkComparison
import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleGenericUnitDivisorData

/-!
# Compatibility of affine divisor and generic-unit comparisons

The objectwise divisor comparison agrees with transport to the source quotient.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open IsDedekindDomain
open EtaleFundamentalGroups.StrictHenselian
universe u
namespace EtaleCohomology

attribute [local irreducible] affineGenericPointUnitQuotientFractionRingIso
  etaleRestrictionFractionFieldUnitQuotientIso

variable {R S : Type u} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra.Etale R S]

private theorem affineObjectToSource_comparison_apply
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (s : (affineGenericPointUnitQuotient R).obj.obj (op (affineEtaleSpecObject (R := R) (S :=
      S)))) :
    let e : (affineGenericPointUnitQuotient R) ≅ (affineEtaleFractionRingUnitQuotient R) :=
      affineGenericPointUnitQuotientFractionRingIso R
    let d : (etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S))) AddCommGrpCat.{u}).obj
        (affineEtaleFractionRingUnitQuotient R) ≅ (affineEtaleFractionRingUnitQuotient S) :=
      etaleRestrictionFractionFieldUnitQuotientIso
        R S (FractionRing R) (FractionRing S)
    affineEtaleGenericUnitObjectToSourceAddEquiv (R := R) (S := S) s =
      (etaleSectionIsoAddEquiv (etaleRestrictionComparisonSectionIso
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (F := affineGenericPointUnitQuotient R)
        (G := affineEtaleFractionRingUnitQuotient R) e
        (H := affineEtaleFractionRingUnitQuotient S) d)) s := by
  intro e d
  rfl

private theorem affineObjectDivisor_top_apply
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (hR : ¬ IsField R)
    [HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) :
    affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv (R := R) (S := S) hR s =
      ((affineEtaleClosedPointDivisorToActualGenericUnitQuotientAddEquiv (R := R) (S := S)
        hR).trans (etaleSectionIsoAddEquiv (etaleRestrictionTopObjectSectionIso
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) (affineGenericPointUnitQuotient R)))) s :=
          by
  rfl

private theorem affineActualToSource_components_apply
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (s : ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S))) AddCommGrpCat.{u}).obj
      (affineGenericPointUnitQuotient R)).obj.obj
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤))) :
    let e : (affineGenericPointUnitQuotient R) ≅ (affineEtaleFractionRingUnitQuotient R) :=
      affineGenericPointUnitQuotientFractionRingIso R
    let d : (etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S))) AddCommGrpCat.{u}).obj
        (affineEtaleFractionRingUnitQuotient R) ≅ (affineEtaleFractionRingUnitQuotient S) :=
      etaleRestrictionFractionFieldUnitQuotientIso
        R S (FractionRing R) (FractionRing S)
    affineEtaleActualGenericUnitQuotientToSourceAddEquiv (R := R) (S := S) s =
      ((etaleSectionIsoAddEquiv
        (A := ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          AddCommGrpCat.{u}).obj (affineGenericPointUnitQuotient R)).obj.obj
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))
        (B := ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          AddCommGrpCat.{u}).obj (affineEtaleFractionRingUnitQuotient R)).obj.obj
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))
        (((sheafToPresheaf (Spec (CommRingCat.of S)).smallEtaleTopology
          AddCommGrpCat.{u}).mapIso
          ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
            AddCommGrpCat.{u}).mapIso e)).app
            (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))).trans
      (etaleSectionIsoAddEquiv
        (A := ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          AddCommGrpCat.{u}).obj (affineEtaleFractionRingUnitQuotient R)).obj.obj
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))
        (B := (affineEtaleFractionRingUnitQuotient S).obj.obj (op ((zariskiToEtale (Spec
          (CommRingCat.of S))).obj ⊤)))
        (((sheafToPresheaf (Spec (CommRingCat.of S)).smallEtaleTopology
          AddCommGrpCat.{u}).mapIso d).app (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj
            ⊤))))) s := by
  intro e d
  rfl

/-- The objectwise divisor comparison recovers the source comparison after
transport to the source generic-unit quotient. -/
theorem affineEtaleClosedPointDivisorGenericUnitObject_compat
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (hR : ¬ IsField R)
    [HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) :
    affineEtaleGenericUnitObjectToSourceAddEquiv (R := R) (S := S)
      (affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv
        (R := R) (S := S) hR s) =
    affineEtaleClosedPointDivisorToGenericUnitQuotientAddEquiv
      (R := R) (S := S) hR s := by
  let e : (affineGenericPointUnitQuotient R) ≅ (affineEtaleFractionRingUnitQuotient R) :=
    affineGenericPointUnitQuotientFractionRingIso R
  let d : (etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S))) AddCommGrpCat.{u}).obj
      (affineEtaleFractionRingUnitQuotient R) ≅ (affineEtaleFractionRingUnitQuotient S) :=
    etaleRestrictionFractionFieldUnitQuotientIso
      R S (FractionRing R) (FractionRing S)
  calc
    affineEtaleGenericUnitObjectToSourceAddEquiv (R := R) (S := S)
        (affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv (R := R) (S := S) hR s) =
        (etaleSectionIsoAddEquiv (etaleRestrictionComparisonSectionIso
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (F := affineGenericPointUnitQuotient R)
        (G := affineEtaleFractionRingUnitQuotient R) e
        (H := affineEtaleFractionRingUnitQuotient S) d))
          (affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv (R := R) (S := S) hR s) :=
      affineObjectToSource_comparison_apply (R := R) (S := S) _
    _ = (etaleSectionIsoAddEquiv (etaleRestrictionComparisonSectionIso
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (F := affineGenericPointUnitQuotient R)
        (G := affineEtaleFractionRingUnitQuotient R) e
        (H := affineEtaleFractionRingUnitQuotient S) d))
          (((affineEtaleClosedPointDivisorToActualGenericUnitQuotientAddEquiv (R := R) (S := S)
          hR).trans (etaleSectionIsoAddEquiv (etaleRestrictionTopObjectSectionIso
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) (affineGenericPointUnitQuotient R)))) s) :=
      congrArg (etaleSectionIsoAddEquiv (etaleRestrictionComparisonSectionIso
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (F := affineGenericPointUnitQuotient R)
        (G := affineEtaleFractionRingUnitQuotient R) e
        (H := affineEtaleFractionRingUnitQuotient S) d)) (affineObjectDivisor_top_apply (R := R)
          (S := S) hR s)
    _ = ((etaleSectionIsoAddEquiv
        (A := ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          AddCommGrpCat.{u}).obj (affineGenericPointUnitQuotient R)).obj.obj
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))
        (B := ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          AddCommGrpCat.{u}).obj (affineEtaleFractionRingUnitQuotient R)).obj.obj
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))
        (((sheafToPresheaf (Spec (CommRingCat.of S)).smallEtaleTopology
          AddCommGrpCat.{u}).mapIso
          ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
            AddCommGrpCat.{u}).mapIso e)).app
            (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))).trans
      (etaleSectionIsoAddEquiv
        (A := ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          AddCommGrpCat.{u}).obj (affineEtaleFractionRingUnitQuotient R)).obj.obj
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))
        (B := (affineEtaleFractionRingUnitQuotient S).obj.obj (op ((zariskiToEtale (Spec
          (CommRingCat.of S))).obj ⊤)))
        (((sheafToPresheaf (Spec (CommRingCat.of S)).smallEtaleTopology
          AddCommGrpCat.{u}).mapIso d).app (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj
            ⊤))))) ((affineEtaleClosedPointDivisorToActualGenericUnitQuotientAddEquiv (R := R) (S
            := S) hR) s) :=
      etaleRestrictionComparisonSectionIso_cancel
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (F := affineGenericPointUnitQuotient R)
        (G := affineEtaleFractionRingUnitQuotient R) e
        (H := affineEtaleFractionRingUnitQuotient S) d
        (affineEtaleClosedPointDivisorToActualGenericUnitQuotientAddEquiv (R := R) (S := S) hR) s
    _ = affineEtaleActualGenericUnitQuotientToSourceAddEquiv (R := R) (S := S)
        ((affineEtaleClosedPointDivisorToActualGenericUnitQuotientAddEquiv (R := R) (S := S) hR)
          s) :=
      (affineActualToSource_components_apply (R := R) (S := S) _).symm
    _ = affineEtaleClosedPointDivisorToGenericUnitQuotientAddEquiv
        (R := R) (S := S) hR s :=
      affineEtaleClosedPointDivisorToActualGenericUnitQuotient_compat
        (R := R) (S := S) hR s

end EtaleCohomology
