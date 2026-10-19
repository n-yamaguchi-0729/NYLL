/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.LocalGeometry.SmoothIntegralFiberCharts
import Nyll.SchemeTheory.RingTheory.Smooth.UniformizerPrimeFiber
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Smooth

/-!
# Smooth affine charts with a prime special-fibre parameter

Every point of the closed fibre of a smooth scheme over a DVR admits an
actual affine chart whose coordinate algebra is a smooth domain and in
which the image of the base uniformizer is prime.

The native relative global-sections functor supplies the coefficient
algebra. Its affine presentation is retained over the original base.
The geometric integral-fibre neighbourhood is compared with the actual
residue tensor by cartesian squares. Flatness and the quotient-tensor
comparison then give primality of the uniformizer image.

Thus the prime-special-fibre hypotheses in the local normalized-cover
calculation are supplied by smoothness and an actual affine shrinking.
No integral source, integral closed fibre, or prime chart parameter is
assumed in the final existence theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

private theorem affineCoordinate_properties_of_integral_closedFiber
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {X : Scheme.{u}} [IsAffine X] [IsIntegral X]
    (f : X ⟶ Spec (.of B)) [Smooth f]
    [IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))))]
    (π : B) (hπ : Prime π) :
    let A := ((algΓ (.of B)).obj (Over.mk f)).unop
    IsDomain A ∧ Algebra.Smooth B A ∧ Prime (algebraMap B A π) ∧
      ∃ e : X ≅ Spec (.of A),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B A)) = f := by
  intro A
  let e : X ≅ Spec (.of A) := X.isoSpec
  let t : Spec (.of A) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap B A))
  have hmodel : e.hom ≫ t = f := by
    change X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (.of B)).inv ≫ f.appTop) = f
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality f,
      Category.assoc, ← Scheme.isoSpec_Spec_inv, Iso.hom_inv_id, Category.comp_id]
  have ht : Smooth t := by
    have htEq : t = e.inv ≫ f := by
      rw [← hmodel, Iso.inv_hom_id_assoc]
    rw [htEq]
    infer_instance
  have hSmoothA : Algebra.Smooth B A := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp ht)
  let s := Spec.map (CommRingCat.ofHom (algebraMap B (IsLocalRing.ResidueField B)))
  have : IsIntegral (pullback f s) := by
    change IsIntegral (pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap B (IsLocalRing.ResidueField B)))))
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    infer_instance
  let p := pullback.fst t s ≫ e.inv
  have hsquare : IsPullback p (pullback.snd t s) f s := by
    apply (IsPullback.of_hasPullback t s).of_iso'
      (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    · change 𝟙 _ ≫ pullback.fst t s =
        (pullback.fst t s ≫ e.inv) ≫ e.hom
      rw [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact hmodel.trans (Category.comp_id f).symm
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  have : IsIntegral (pullback t s) := IsIntegral.of_isIso hsquare.isoPullback.inv
  have : IsIntegral (Spec (.of (A ⊗[B] IsLocalRing.ResidueField B))) :=
    IsIntegral.of_isIso (pullbackSpecIso B A (IsLocalRing.ResidueField B)).hom
  have : IsDomain (A ⊗[B] IsLocalRing.ResidueField B) :=
    (affine_isIntegral_iff (.of (A ⊗[B] IsLocalRing.ResidueField B))).mp inferInstance
  have : IsIntegral (Spec (.of A)) := IsIntegral.of_isIso e.hom
  have : IsDomain A := (affine_isIntegral_iff (.of A)).mp inferInstance
  exact ⟨inferInstance, hSmoothA,
    SchemeTheory.prime_uniformizer_image_of_isDomain_closedFiber B A π hπ,
    e, hmodel⟩

/-- Smoothness over a DVR supplies actual affine smooth domain charts
whose special fibre is defined by a prime uniformizer image. The
coordinate isomorphism preserves the original structure map to the base. -/
theorem Smooth.exists_primeUniformizer_affineChart
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) [Smooth f]
    (π : B) (hπ : Prime π) :
    let s := Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
    let Z := pullback f s
    let i : Z ⟶ X := pullback.fst f s
    ∀ z : Z, ∃ U : X.Opens, IsAffineOpen U ∧ i z ∈ U ∧
      let A := ((algΓ (.of B)).obj (Over.mk (U.ι ≫ f))).unop
      IsDomain A ∧ Algebra.Smooth B A ∧ Prime (algebraMap B A π) ∧
        ∃ e : U.toScheme ≅ Spec (.of A),
          e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B A)) = U.ι ≫ f := by
  intro s Z i z
  obtain ⟨U, hU, hizU, hIntegralU, hIntegralFibreU⟩ :=
    Smooth.exists_isAffineOpen_integral_closedFiber f z
  have : IsAffine U := hU
  have : IsIntegral U := hIntegralU
  have : IsIntegral (i ⁻¹ᵁ U) := hIntegralFibreU
  have hsquare : IsPullback (i ∣_ U)
      ((i ⁻¹ᵁ U).ι ≫ pullback.snd f s) (U.ι ≫ f) s :=
    (isPullback_morphismRestrict i U).paste_vert (IsPullback.of_hasPullback f s)
  have : IsIntegral (pullback (U.ι ≫ f) s) :=
    IsIntegral.of_isIso hsquare.isoPullback.hom
  exact ⟨U, hU, hizU, affineCoordinate_properties_of_integral_closedFiber (U.ι ≫ f) π hπ⟩

end AlgebraicGeometry
