/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Polynomial coordinates of the formal difference of an affine-line map

For an actual group-valued morphism on the affine line, translation of its
parameter by the power-series variable and division by the original point
give a group-valued point over `PowerSeries (Polynomial K)`. Its constant
fibre is the identity. The kernel of the constant-coefficient map lies in the
Jacobson radical, so this point factors through every open identity
neighbourhood. An affine such neighbourhood therefore supplies actual
polynomial coefficients in all orders, with the expected unit constant term.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- An open subset of a power-series spectrum containing its entire constant
fibre contains every point. This uses all maximal ideals, not a locality
assumption on the coefficient ring. -/
theorem Scheme.powerSeries_preimage_eq_top_of_constantCoeff
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : Spec (.of (PowerSeries A)) ⟶ X) (V : X.Opens)
    (hV : Set.range (Spec.map (CommRingCat.ofHom
      (PowerSeries.constantCoeff (R := A))) ≫ f) ⊆ V) :
    f ⁻¹ᵁ V = ⊤ := by
  have hker : RingHom.ker (PowerSeries.constantCoeff (R := A)) ≤
      (⊥ : Ideal (PowerSeries A)).jacobson := by
    intro a ha
    apply Ideal.mem_jacobson_bot.mpr
    intro b
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    have ha0 : PowerSeries.constantCoeff a = 0 := ha
    rw [map_add, map_mul, ha0, zero_mul, zero_add, map_one]
    exact isUnit_one
  apply top_unique
  intro p _
  obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  have hJm : (⊥ : Ideal (PowerSeries A)).jacobson ≤ m :=
    sInf_le ⟨bot_le, hm⟩
  have hmrange : (⟨m, hm.isPrime⟩ : PrimeSpectrum (PowerSeries A)) ∈
      Set.range (PrimeSpectrum.comap (PowerSeries.constantCoeff (R := A))) := by
    rw [range_comap_of_surjective A _ PowerSeries.constantCoeff_surj]
    exact hker.trans hJm
  obtain ⟨y, hy⟩ := hmrange
  have hmy : f (⟨m, hm.isPrime⟩ : PrimeSpectrum (PowerSeries A)) ∈ V := by
    rw [← hy]
    exact hV ⟨y, rfl⟩
  exact ((PrimeSpectrum.le_iff_specializes p ⟨m, hm.isPrime⟩).mp hpm).mem_open
    (f ⁻¹ᵁ V).isOpen hmy

namespace AffineLineGroupFormalDifference

variable {K : Type u} [CommRing K]

private abbrev scalarSpec (A : Type u) [CommRing A] [Algebra K A] :
    Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))

private def scalarSpecMap {A B : Type u} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B) :
    scalarSpec (K := K) B ⟶ scalarSpec (K := K) A :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)) =
        Spec.map (CommRingCat.ofHom (algebraMap K B))
    rw [← Spec.map_comp]
    apply congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of B => Spec.map h)
    exact CommRingCat.hom_ext f.comp_algebraMap)

private theorem scalarSpecMap_comp {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    scalarSpecMap (g.comp f) = scalarSpecMap g ≫ scalarSpecMap f := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (g.comp f).toRingHom) =
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
  rw [← Spec.map_comp]
  rfl

private theorem scalarSpecMap_id (A : Type u) [CommRing A] [Algebra K A] :
    scalarSpecMap (AlgHom.id K A) = 𝟙 (scalarSpec (K := K) A) := by
  apply Over.OverMorphism.ext
  change Spec.map (𝟙 (CommRingCat.of A)) = 𝟙 _
  exact Spec.map_id _

/-- The actual formal shift of the affine-line coordinate. -/
def shift : Polynomial K →ₐ[K] PowerSeries (Polynomial K) :=
  Polynomial.aeval (PowerSeries.C Polynomial.X + PowerSeries.X)

private def constantInclusion : Polynomial K →ₐ[K] PowerSeries (Polynomial K) where
  toRingHom := PowerSeries.C
  commutes' a := (PowerSeries.algebraMap_apply (r := a)).symm

private def constantCoefficient : PowerSeries (Polynomial K) →ₐ[K] Polynomial K where
  toRingHom := PowerSeries.constantCoeff
  commutes' a := by
    change PowerSeries.constantCoeff
      (algebraMap K (PowerSeries (Polynomial K)) a) = algebraMap K (Polynomial K) a
    rw [PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C]

private theorem constantCoefficient_shift :
    (constantCoefficient (K := K)).comp shift = AlgHom.id K (Polynomial K) := by
  apply Polynomial.algHom_ext
  change PowerSeries.constantCoeff
    (Polynomial.aeval (PowerSeries.C Polynomial.X + PowerSeries.X) Polynomial.X) =
      Polynomial.X
  rw [Polynomial.aeval_X, map_add, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X, add_zero]

private theorem constantCoefficient_inclusion :
    (constantCoefficient (K := K)).comp constantInclusion = AlgHom.id K (Polynomial K) := by
  apply AlgHom.ext
  intro a
  change PowerSeries.constantCoeff (PowerSeries.C a) = a
  exact PowerSeries.constantCoeff_C a

variable {G : Over (Spec (.of K))} [GrpObj G]

/-- The actual group-valued formal difference `tau(z + T) / tau(z)`. -/
def difference (τ : Over.mk (Spec.map
      (CommRingCat.ofHom (algebraMap K (Polynomial K)))) ⟶ G) :
    Spec (.of (PowerSeries (Polynomial K))) ⟶ G.left :=
  ((scalarSpecMap shift ≫ τ) * (scalarSpecMap constantInclusion ≫ τ)⁻¹).left

/-- Restricting the full formal difference to its constant fibre gives the unit. -/
theorem difference_constant (τ : Over.mk (Spec.map
      (CommRingCat.ofHom (algebraMap K (Polynomial K)))) ⟶ G) :
    Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := Polynomial K))) ≫
      difference τ =
        (1 : Over.mk (Spec.map
          (CommRingCat.ofHom (algebraMap K (Polynomial K)))) ⟶ G).left := by
  have h : scalarSpecMap constantCoefficient ≫
      ((scalarSpecMap shift ≫ τ) * (scalarSpecMap constantInclusion ≫ τ)⁻¹) =
      (1 : scalarSpec (K := K) (Polynomial K) ⟶ G) := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
      ← scalarSpecMap_comp, ← scalarSpecMap_comp, constantCoefficient_shift,
      constantCoefficient_inclusion, scalarSpecMap_id, Category.id_comp, mul_inv_cancel]
  exact congrArg (fun a : scalarSpec (K := K) (Polynomial K) ⟶ G => a.left) h

private theorem one_left {S T : Scheme.{u}} (H : Over S) [GrpObj H]
    (t : T ⟶ S) :
    (1 : Over.mk t ⟶ H).left = t ≫ (1 : Over.mk (𝟙 S) ⟶ H).left := by
  have h := MonObj.comp_one (M := H)
    (Over.homMk t : Over.mk t ⟶ Over.mk (𝟙 S))
  exact (congrArg (fun a : Over.mk t ⟶ H => a.left) h).symm

/-- Every identity neighbourhood contains the entire formal difference over
the polynomial coefficient ring. -/
theorem difference_preimage (τ : Over.mk (Spec.map
      (CommRingCat.ofHom (algebraMap K (Polynomial K)))) ⟶ G)
    (V : G.left.Opens)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    difference τ ⁻¹ᵁ V = ⊤ := by
  apply Scheme.powerSeries_preimage_eq_top_of_constantCoeff
  rw [difference_constant, one_left]
  rintro _ ⟨y, rfl⟩
  exact hunit ⟨_, rfl⟩

/-- The constructed factor of the actual formal difference through an open
identity neighbourhood. -/
def lift (τ : Over.mk (Spec.map
      (CommRingCat.ofHom (algebraMap K (Polynomial K)))) ⟶ G)
    (V : G.left.Opens)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    Spec (.of (PowerSeries (Polynomial K))) ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι (difference τ) (by
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ difference τ ⁻¹ᵁ V := by
      rw [difference_preimage τ V hunit]
      trivial
    exact ⟨⟨difference τ y, hy⟩, rfl⟩)

/-- The open factor recovers the actual formal difference. -/
theorem lift_fac (τ : Over.mk (Spec.map
      (CommRingCat.ofHom (algebraMap K (Polynomial K)))) ⟶ G)
    (V : G.left.Opens)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    lift τ V hunit ≫ V.ι = difference τ :=
  IsOpenImmersion.lift_fac _ _ _

private def identityLift (V : G.left.Opens)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    Spec (.of K) ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left (by
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨_, hunit ⟨y, rfl⟩⟩, rfl⟩)

/-- Evaluation of an affine-neighbourhood coordinate at the actual unit section. -/
def identityCoordinates (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    Γ(G.left, V) →+* K :=
  (Spec.preimage (identityLift V hunit ≫ hV.isoSpec.hom)).hom

/-- The identity coordinate homomorphism represents the actual group unit. -/
theorem identityCoordinates_spec (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    Spec.map (CommRingCat.ofHom (identityCoordinates V hV hunit)) ≫ hV.fromSpec =
      (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left := by
  change Spec.map (Spec.preimage (identityLift V hunit ≫ hV.isoSpec.hom)) ≫
    hV.fromSpec = _
  rw [Spec.map_preimage, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]
  exact IsOpenImmersion.lift_fac _ _ _

/-- The affine identity coordinates of the actual difference are power series
whose coefficients are polynomials in the original affine-line parameter. -/
def coordinates (τ : Over.mk (Spec.map
      (CommRingCat.ofHom (algebraMap K (Polynomial K)))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    Γ(G.left, V) →+* PowerSeries (Polynomial K) :=
  (Spec.preimage (lift τ V hunit ≫ hV.isoSpec.hom)).hom

/-- The constructed polynomial-coordinate homomorphism represents the actual
formal group difference on spectra. -/
theorem coordinates_spec (τ : Over.mk (Spec.map
      (CommRingCat.ofHom (algebraMap K (Polynomial K)))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    Spec.map (CommRingCat.ofHom (coordinates τ V hV hunit)) ≫ hV.fromSpec =
      difference τ := by
  change Spec.map (Spec.preimage (lift τ V hunit ≫ hV.isoSpec.hom)) ≫
    hV.fromSpec = _
  rw [Spec.map_preimage, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]
  exact lift_fac τ V hunit

/-- The full constant-coefficient homomorphism is evaluation at the unit,
followed by the inclusion of scalar constants into the polynomial ring. -/
theorem constantCoeff_comp_coordinates (τ : Over.mk (Spec.map
      (CommRingCat.ofHom (algebraMap K (Polynomial K)))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    (PowerSeries.constantCoeff (R := Polynomial K)).comp (coordinates τ V hV hunit) =
      Polynomial.C.comp (identityCoordinates V hV hunit) := by
  have h : CommRingCat.ofHom ((PowerSeries.constantCoeff (R := Polynomial K)).comp
      (coordinates τ V hV hunit)) =
      CommRingCat.ofHom (Polynomial.C.comp (identityCoordinates V hV hunit)) := by
    apply Spec.map_injective
    apply (cancel_mono hV.fromSpec).mp
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      coordinates_spec, identityCoordinates_spec, difference_constant]
    exact one_left G (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))))
  exact congrArg (fun f : CommRingCat.of Γ(G.left, V) ⟶
    CommRingCat.of (Polynomial K) => f.hom) h

/-- Each coordinate has exactly its unit value as the constant polynomial term. -/
theorem constantCoeff_coordinates (τ : Over.mk (Spec.map
      (CommRingCat.ofHom (algebraMap K (Polynomial K)))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V)
    (a : Γ(G.left, V)) :
    PowerSeries.constantCoeff (coordinates τ V hV hunit a) =
      Polynomial.C (identityCoordinates V hV hunit a) :=
  RingHom.congr_fun (constantCoeff_comp_coordinates τ V hV hunit) a

end AffineLineGroupFormalDifference

end AlgebraicGeometry
