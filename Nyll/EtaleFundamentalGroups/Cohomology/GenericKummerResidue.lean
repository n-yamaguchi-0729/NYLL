/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.GenericSectionsComparison
import Nyll.EtaleFundamentalGroups.Cohomology.DVRGenericUnitQuotient
import Nyll.EtaleCohomology.Classical.FieldKummerH1Quotient
import Nyll.EtaleCohomology.Classical.StrictHenselianDVRKummer
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkDVRAtPrime
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.CharZero.AddMonoidHom
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Generic-unit power cokernels and geometric Kummer residues

The actual generic-unit quotient modulo powers has geometric stalks given
by actual field Kummer H¹ for the fraction field of the geometric local ring.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.StrictHenselian

section DomainContext

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)

/-- The actual geometric stalk of generic units modulo nth powers is
the power cokernel on the fraction field of the actual geometric local ring. -/
def geometricGenericPowerCokernelStalkIso (n : ℕ) :
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
      (A := AddCommGrpCat.{u})).obj
      (cokernel (n • 𝟙 ((EtaleCohomology.etaleAbelianPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).obj
          (EtaleCohomology.etaleMultiplicativeGroupSheaf
            (Spec (CommRingCat.of (FractionRing R))))))) ≅
      cokernel (n • 𝟙 (AddCommGrpCat.of
        (Additive (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))ˣ))) := by
  let s := Spec.map (CommRingCat.ofHom φ)
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let F := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})
  let B := (EtaleCohomology.etaleAbelianPushforward j).obj
    (EtaleCohomology.etaleMultiplicativeGroupSheaf (Spec (.of (FractionRing R))))
  let K := FractionRing (geometricStalk s)
  let G := ((Scheme.pointEtaleNeighborhoods s).presheafFiber
    (A := CommRingCat.{u})).obj (etaleBaseChangedSections j)
  let e₁ : F.obj B ≅ AddCommGrpCat.of (Additive Gˣ) :=
    (geometricMultiplicativeGroupPushforwardStalkEquiv s j).toAddCommGrpIso
  let u := Units.mapEquiv (geometricGenericSectionsStalkEquiv R φ).toMulEquiv
  let e₂ : AddCommGrpCat.of (Additive Gˣ) ≅ AddCommGrpCat.of (Additive Kˣ) :=
    u.toAdditive.toAddCommGrpIso
  let e : F.obj B ≅ AddCommGrpCat.of (Additive Kˣ) :=
    e₁ ≪≫ e₂
  have he : F.map (n • 𝟙 B) ≫ e.hom =
      e.hom ≫ (n • 𝟙 (AddCommGrpCat.of (Additive Kˣ))) := by
    rw [F.map_nsmul, F.map_id, Preadditive.nsmul_comp,
      Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]
  exact PreservesCokernel.iso F (n • 𝟙 B) ≪≫
    cokernel.mapIso (f := F.map (n • 𝟙 B))
      (n • 𝟙 (AddCommGrpCat.of (Additive Kˣ))) e e he


/-- The geometric residue sheaf defined using actual generic units has,
at each geometric point in characteristic zero, the actual derived
Kummer H1 of the fraction field of that geometric local ring. -/
def geometricGenericPowerCokernelStalkH1Iso [CharZero R]
    {n : ℕ} (hn : 0 < n) :
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
      (A := AddCommGrpCat.{u})).obj
      (cokernel (n • 𝟙 ((EtaleCohomology.etaleAbelianPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).obj
          (EtaleCohomology.etaleMultiplicativeGroupSheaf
            (Spec (CommRingCat.of (FractionRing R))))))) ≅
      AddCommGrpCat.of (Sheaf.H.{u}
        (EtaleCohomology.etaleRootsOfUnitySheaf
          (Spec (CommRingCat.of
            (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))))) n) 1) := by
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let K := FractionRing A
  have : CharZero A := CharZero.of_addMonoidHom
    (geometricStalkStructureMap φ).toAddMonoidHom
    (by
      change (geometricStalkStructureMap φ) 1 = 1
      exact map_one _)
    (geometricStalkStructureMap_injective_of_isDomain φ)
  have hnK : IsUnit (n : Γ(Spec (CommRingCat.of K), ⊤)) := by
    have h : IsUnit (n : K) :=
      isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
    let e := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
    have he : e.symm (n : K) = (n : Γ(Spec (CommRingCat.of K), ⊤)) :=
      map_natCast e.symm.toRingHom n
    rw [← he]
    exact h.map e.symm.toRingHom
  exact geometricGenericPowerCokernelStalkIso R φ n ≪≫
    EtaleCohomology.fieldKummerUnitCokernelIso K hn hnK

/-- At a geometric point above the generic point, the actual generic-unit
power cokernel has zero stalk whenever the coefficient integer is invertible. -/
theorem geometricGenericPowerCokernelStalk_isZero_of_injective
    (hφ : Function.Injective φ) (n : ℕ) (hnR : IsUnit (n : R)) :
    IsZero (((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
      (A := AddCommGrpCat.{u})).obj
      (cokernel (n • 𝟙 ((EtaleCohomology.etaleAbelianPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).obj
          (EtaleCohomology.etaleMultiplicativeGroupSheaf
            (Spec (CommRingCat.of (FractionRing R)))))))) := by
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let K := FractionRing A
  have hA : IsField A := geometricStalk_isField_of_injective φ hφ
  let e : Aˣ ≃* Kˣ :=
    Units.mapEquiv (RingEquiv.ofBijective (algebraMap A K)
      ⟨IsFractionRing.injective A K, IsFractionRing.surjective_iff_isField.mpr hA⟩).toMulEquiv
  have hnA : IsUnit (n : A) := by
    simpa only [map_natCast] using hnR.map (geometricStalkStructureMap φ)
  let p := n • 𝟙 (AddCommGrpCat.of (Additive Kˣ))
  have hp : Function.Surjective p := by
    intro a
    let a₀ : Additive Kˣ := a
    obtain ⟨b, hb⟩ := HenselianLocalRing.units_pow_surjective_of_isSepClosed
      A n hnA (e.symm a₀.toMul)
    refine ⟨Additive.ofMul (e b), ?_⟩
    change Additive.ofMul ((e b) ^ n) = a₀
    have hpow : (e b) ^ n = a₀.toMul := by
      calc
        (e b) ^ n = e (b ^ n) := (map_pow e b n).symm
        _ = e (e.symm a₀.toMul) := congrArg e hb
        _ = a₀.toMul := e.apply_symm_apply _
    exact congrArg Additive.ofMul hpow
  have : Epi p := ConcreteCategory.epi_of_surjective p hp
  exact (isZero_cokernel_of_epi p).of_iso
    (geometricGenericPowerCokernelStalkIso R φ n)

end DomainContext

section DedekindContext

universe u

variable (R : Type u) [CommRing R]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)

/-- At a non-generic geometric point of an affine Dedekind scheme in
characteristic zero, the actual generic-unit power-cokernel stalk is cyclic
of order n. Invertibility on the base supplies the required local unit roots. -/
def geometricDedekindGenericPowerCokernelStalkEquiv
    [IsDedekindDomain R] [CharZero R]
    (hφ : RingHom.ker φ ≠ ⊥) {n : ℕ} (hn : 0 < n) (hnR : IsUnit (n : R)) :
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
      (A := AddCommGrpCat.{u})).obj
      (cokernel (n • 𝟙 ((EtaleCohomology.etaleAbelianPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).obj
          (EtaleCohomology.etaleMultiplicativeGroupSheaf
            (Spec (CommRingCat.of (FractionRing R))))))) ≃+ ZMod n := by
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let K := FractionRing A
  have hP : (geometricBasePrime φ).asIdeal ≠ ⊥ := hφ
  have : IsDiscreteValuationRing (Localization.AtPrime (geometricBasePrime φ).asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP _
  have : IsDiscreteValuationRing A :=
    geometricStalk_isDiscreteValuationRing_of_baseLocalization φ
  have : CharZero A := CharZero.of_addMonoidHom
    (geometricStalkStructureMap φ).toAddMonoidHom
    (by
      change (geometricStalkStructureMap φ) 1 = 1
      exact map_one _)
    (geometricStalkStructureMap_injective_of_isDomain φ)
  have hnA : IsUnit (n : A) := by
    simpa only [map_natCast] using hnR.map (geometricStalkStructureMap φ)
  let π : A := Classical.choose (IsDiscreteValuationRing.exists_irreducible A)
  have hπ : Irreducible π :=
    Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible A)
  have hπK : algebraMap A K π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply IsFractionRing.injective A K
    exact h.trans (map_zero (algebraMap A K)).symm
  let πK : Kˣ := Units.mk0 (algebraMap A K π) hπK
  let e := (geometricGenericPowerCokernelStalkH1Iso R φ hn).addCommGroupIsoToAddEquiv
  exact e.trans
    (EtaleCohomology.fieldKummerUniformizerEquiv A K hn hnA hπ πK rfl).symm

end DedekindContext

universe u

/-- Over an affine Dedekind scheme, roots of unity extend uniquely from
the actual generic point. The comparison is induced by restriction of units. -/
def genericRootsOfUnityPushforwardIso (R : Type u) [CommRing R] [IsDedekindDomain R]
    (n : ℕ) (hn : n ≠ 0) :
    EtaleCohomology.etaleRootsOfUnitySheaf (Spec (CommRingCat.of R)) n ≅
      (EtaleCohomology.etaleAbelianPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).obj
          (EtaleCohomology.etaleRootsOfUnitySheaf
            (Spec (CommRingCat.of (FractionRing R))) n) := by
  let X := Spec (CommRingCat.of R)
  let Y := Spec (CommRingCat.of (FractionRing R))
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let G := EtaleCohomology.etaleAbelianPushforward j
  let A := EtaleCohomology.etaleMultiplicativeGroupSheaf X
  let B := G.obj (EtaleCohomology.etaleMultiplicativeGroupSheaf Y)
  let f := EtaleCohomology.etaleMultiplicativeGroupToPushforward j
  have : Mono f := EtaleCohomology.etaleMultiplicativeGroupToFractionField_mono R
  have : Mono (n • 𝟙 (cokernel f)) := genericUnitQuotient_nsmul_mono R n hn
  have hX : EtaleCohomology.etaleMultiplicativeGroupPower X n = n • 𝟙 A := by
    change n • 𝟙 A = n • 𝟙 A
    rfl
  have hp : G.map (EtaleCohomology.etaleMultiplicativeGroupPower Y n) =
      n • 𝟙 B := by
    rw [EtaleCohomology.etaleMultiplicativeGroupPower, G.map_nsmul, G.map_id]
  exact kernelIsoOfEq hX ≪≫ kernelNsmulSubobjectIso f n ≪≫
    (kernelIsoOfEq hp).symm ≪≫
      (PreservesKernel.iso G (EtaleCohomology.etaleMultiplicativeGroupPower Y n)).symm


/-- The generic-point roots-of-unity isomorphism is the actual restriction
map: its composition with the direct-image unit inclusion is restriction
of units composed with the original roots-of-unity inclusion. -/
theorem genericRootsOfUnityPushforwardIso_hom_ι
    (R : Type u) [CommRing R] [IsDedekindDomain R] (n : ℕ) (hn : n ≠ 0) :
    (genericRootsOfUnityPushforwardIso R n hn).hom ≫
      (EtaleCohomology.etaleAbelianPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).map
          (kernel.ι (EtaleCohomology.etaleMultiplicativeGroupPower
            (Spec (CommRingCat.of (FractionRing R))) n)) =
      kernel.ι (EtaleCohomology.etaleMultiplicativeGroupPower
        (Spec (CommRingCat.of R)) n) ≫
          EtaleCohomology.etaleMultiplicativeGroupToPushforward
            (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) := by
  simp only [genericRootsOfUnityPushforwardIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, PreservesKernel.iso_inv_ι, kernelIsoOfEq_inv_comp_ι,
    kernelNsmulSubobjectIso_hom_ι]
  rw [← Category.assoc, kernelIsoOfEq_hom_comp_ι]

end EtaleFundamentalGroups.StrictHenselian
