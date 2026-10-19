/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleCoordinateComparison
import Nyll.EtaleCohomology.Classical.KummerHigherDirectImage

/-!
# The generic Kummer higher direct image as divisors modulo n

The divisor comparison identifies the first higher direct image of roots of
unity with the cokernel of multiplication by n on the closed-point divisor
sheaf. All quotients are taken in the category of étale abelian sheaves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleCohomology

universe u

variable (R : Type u) [CommRing R] [IsDedekindDomain R] (hR : ¬ IsField R)
  [HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
    (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]

/-- Divisors modulo n agree with the quotient modulo n of the actual
fraction-field unit quotient sheaf. -/
def affineClosedPointDivisorModIso (n : ℕ) :
    cokernel (n • 𝟙 (closedPointDivisorSheaf (Spec (CommRingCat.of R)))) ≅
      cokernel (n • 𝟙 (cokernel (etaleMultiplicativeGroupToPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))))) := by
  let e := affineClosedPointDivisorGenericUnitSheafIso R hR ≪≫
    affineGenericPointUnitQuotientFractionRingIso R
  exact cokernel.mapIso _ _ e e (by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp, Category.comp_id])

/-- For an invertible positive integer n, the actual first higher direct
image from the fraction field is the closed-point divisor sheaf modulo n. -/
def affineKummerRightDerivedOneDivisorIso [CharZero R]
    {n : ℕ} (hn : 0 < n) (hnR : IsUnit (n : R)) :
    ((etaleAbelianPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).rightDerived 1).obj
        (etaleRootsOfUnitySheaf (Spec (CommRingCat.of (FractionRing R))) n) ≅
      cokernel (n • 𝟙 (closedPointDivisorSheaf (Spec (CommRingCat.of R)))) := by
  let K := FractionRing R
  let j := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hnK : IsUnit (n : Γ(Spec (CommRingCat.of K), ⊤)) := by
    have h : IsUnit (n : K) := by
      simpa only [map_natCast] using hnR.map (algebraMap R K)
    let g : K →+* Γ(Spec (CommRingCat.of K), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    exact (map_natCast g n) ▸ h.map g
  have hnX : IsUnit (n : Γ(Spec (CommRingCat.of R), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
    simpa only [map_natCast] using hnR.map e.symm.toRingHom
  exact etaleKummerRightDerivedOneUnitQuotientIso_of_field K j hn hnK hnX ≪≫
    (affineClosedPointDivisorModIso R hR n).symm

end EtaleCohomology
