/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.GenericKummerResidue
import Nyll.EtaleCohomology.Classical.KummerHigherDirectImage

/-!
# Generic Kummer first higher direct image and geometric residues

The actual right-derived comparison transports the verified generic-unit
cokernel stalk results to the first higher direct image of roots of unity.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace EtaleFundamentalGroups.StrictHenselian
universe u

/-- The actual first higher direct image at the generic point has the
generic-unit power-cokernel presentation. -/
def genericKummerRightDerivedOneIso
    (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
    {n : ℕ} (hn : 0 < n) :
    ((EtaleCohomology.etaleAbelianPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).rightDerived 1).obj
      (EtaleCohomology.etaleRootsOfUnitySheaf (Spec (.of (FractionRing R))) n) ≅
    cokernel (n • 𝟙 ((EtaleCohomology.etaleAbelianPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).obj
      (EtaleCohomology.etaleMultiplicativeGroupSheaf (Spec (.of (FractionRing R)))))) := by
  let K := FractionRing R
  let j := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let G := EtaleCohomology.etaleAbelianPushforward j
  have hnK : IsUnit (n : Γ(Spec (.of K), ⊤)) := by
    have h : IsUnit (n : K) :=
      isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
    let e := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
    have he : e.symm (n : K) = (n : Γ(Spec (.of K), ⊤)) :=
      map_natCast e.symm.toRingHom n
    rw [← he]
    exact h.map e.symm.toRingHom
  have hp : G.map (EtaleCohomology.etaleMultiplicativeGroupPower (Spec (.of K)) n) =
      n • 𝟙 (G.obj (EtaleCohomology.etaleMultiplicativeGroupSheaf (Spec (.of K)))) := by
    rw [EtaleCohomology.etaleMultiplicativeGroupPower, G.map_nsmul, G.map_id]
  exact EtaleCohomology.etaleKummerRightDerivedOneCokernelIso_of_field K j hn hnK ≪≫
    cokernelIsoOfEq hp

/-- The geometric stalk of the actual first higher direct image is actual
derived Kummer H1 of the fraction field of the geometric local ring. -/
def geometricGenericKummerRightDerivedOneStalkH1Iso
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)
    {n : ℕ} (hn : 0 < n) :
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
      (A := AddCommGrpCat.{u})).obj
      (((EtaleCohomology.etaleAbelianPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).rightDerived 1).obj
        (EtaleCohomology.etaleRootsOfUnitySheaf (Spec (.of (FractionRing R))) n)) ≅
    AddCommGrpCat.of (Sheaf.H.{u}
      (EtaleCohomology.etaleRootsOfUnitySheaf
        (Spec (.of (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))))) n) 1) := by
  let F := (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
    (A := AddCommGrpCat.{u})
  exact F.mapIso (genericKummerRightDerivedOneIso R hn) ≪≫
    geometricGenericPowerCokernelStalkH1Iso R φ hn

/-- At a non-generic geometric point of an affine Dedekind scheme, the
actual first higher direct image of roots of unity is cyclic of order n. -/
def geometricDedekindKummerRightDerivedOneStalkEquiv
    (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero R]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)
    (hφ : RingHom.ker φ ≠ ⊥) {n : ℕ} (hn : 0 < n) (hnR : IsUnit (n : R)) :
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
      (A := AddCommGrpCat.{u})).obj
      (((EtaleCohomology.etaleAbelianPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).rightDerived 1).obj
        (EtaleCohomology.etaleRootsOfUnitySheaf (Spec (.of (FractionRing R))) n)) ≃+ ZMod n := by
  let F := (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
    (A := AddCommGrpCat.{u})
  let e := F.mapIso (genericKummerRightDerivedOneIso R hn)
  exact e.addCommGroupIsoToAddEquiv.trans
    (geometricDedekindGenericPowerCokernelStalkEquiv R φ hφ hn hnR)

/-- At a generic geometric point, the actual first higher direct image
of roots of unity has zero stalk. -/
theorem geometricGenericKummerRightDerivedOneStalk_isZero_of_injective
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)
    (hφ : Function.Injective φ) {n : ℕ} (hn : 0 < n) (hnR : IsUnit (n : R)) :
    IsZero (((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
      (A := AddCommGrpCat.{u})).obj
      (((EtaleCohomology.etaleAbelianPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).rightDerived 1).obj
        (EtaleCohomology.etaleRootsOfUnitySheaf (Spec (.of (FractionRing R))) n))) := by
  let F := (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
    (A := AddCommGrpCat.{u})
  exact (geometricGenericPowerCokernelStalk_isZero_of_injective R φ hφ n hnR).of_iso
    (F.mapIso (genericKummerRightDerivedOneIso R hn))

end EtaleFundamentalGroups.StrictHenselian
