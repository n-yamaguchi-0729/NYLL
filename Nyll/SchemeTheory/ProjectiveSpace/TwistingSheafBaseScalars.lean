/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafHomogeneousRatios
import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Defs

/-!
# The original base scalars in projective coordinate fractions

The actual structural morphism of projective space induces the expected
coefficient map on every standard chart. This is proved from the original
chart isomorphism and the composition of that chart with the structural
morphism. Homogeneous coordinate fractions therefore respect precisely
the original base scalar action.
-/

noncomputable section

universe u

open CategoryTheory HomogeneousLocalization Opposite

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The coefficient map from the actual projective structure morphism,
computed in the original homogeneous localization chart. -/
theorem projectiveChart_constToPresheaf (i : Fin (n + 1)) :
    (π R n).constToPresheaf.app (op (standardOpen R n i)) =
      CommRingCat.ofHom (algebraMap R (Away 𝒜 (MvPolynomial.X i))) ≫
        Proj.awayToSection 𝒜 (MvPolynomial.X i) := by
  let U : (Proj 𝒜).Opens := standardOpen R n i
  let e : U.toScheme ≅ Spec (.of (Away 𝒜 (MvPolynomial.X i))) :=
    Proj.basicOpenIsoSpec 𝒜 (MvPolynomial.X i) (X_mem_one R n i) one_pos
  let φ : CommRingCat.of R ⟶ CommRingCat.of (Away 𝒜 (MvPolynomial.X i)) :=
    CommRingCat.ofHom (algebraMap R (Away 𝒜 (MvPolynomial.X i)))
  have hUπ : U.ι ≫ π R n = e.hom ≫ Spec.map φ := by
    apply (cancel_epi e.inv).mp
    calc
      e.inv ≫ (U.ι ≫ π R n) = (e.inv ≫ U.ι) ≫ π R n :=
        (Category.assoc e.inv U.ι (π R n)).symm
      _ = Spec.map φ := awayι_comp_π R n i
      _ = e.inv ≫ (e.hom ≫ Spec.map φ) := (e.inv_hom_id_assoc (Spec.map φ)).symm
  have hι : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  have hcoeff : (π R n).constToPresheaf.app (op U) ≫ U.topIso.inv =
      (Scheme.ΓSpecIso (.of R)).inv ≫ (U.ι ≫ π R n).appTop := by
    let a : CommRingCat.of R ⟶ Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).inv
    let b : Γ(Spec (.of R), ⊤) ⟶ Γ(Proj 𝒜, U) := (π R n).appLE ⊤ U le_top
    have hc : b ≫ U.ι.appLE U ⊤ U.ι_preimage_self.ge = (U.ι ≫ π R n).appTop :=
      Scheme.Hom.appLE_comp_appLE U.ι (π R n) ⊤ U ⊤ le_top U.ι_preimage_self.ge
    change (a ≫ b) ≫ U.topIso.inv = a ≫ (U.ι ≫ π R n).appTop
    rw [← hι, Category.assoc, hc]
  have he : e.hom.appTop =
      (Scheme.ΓSpecIso (.of (Away 𝒜 (MvPolynomial.X i)))).hom ≫
        Proj.awayToSection 𝒜 (MvPolynomial.X i) ≫ U.topIso.inv :=
    Proj.basicOpenToSpec_app_top 𝒜 (MvPolynomial.X i)
  have hcalc : (Scheme.ΓSpecIso (.of R)).inv ≫ (U.ι ≫ π R n).appTop =
      (φ ≫ Proj.awayToSection 𝒜 (MvPolynomial.X i)) ≫ U.topIso.inv := by
    rw [hUπ, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality φ, he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (cancel_mono U.topIso.inv).mp (hcoeff.trans hcalc)

/-- Homogeneous coordinate fractions respect the scalar action induced
by the original structure morphism to the base spectrum. -/
theorem homogeneousRatioSection_smul (d : ℕ) (p : 𝒜 d)
    (i : Fin (n + 1)) (r : R) :
    homogeneousRatioSection R n d (r • p) i =
      ((π R n).constToPresheaf.app (op (standardOpen R n i))).hom r *
        homogeneousRatioSection R n d p i := by
  rw [projectiveChart_constToPresheaf]
  change homogeneousRatioSection R n d (r • p) i =
    (Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom
      (algebraMap R (Away 𝒜 (MvPolynomial.X i)) r) * homogeneousRatioSection R n d p i
  unfold homogeneousRatioSection
  rw [← map_mul]
  apply congrArg (Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, Away.val_mk, Away.val_mk, val_algebraMap,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
  apply congrArg₂ Localization.mk
  · exact MvPolynomial.smul_eq_C_mul p.val r
  · apply Subtype.ext
    exact (one_mul (MvPolynomial.X i ^ d)).symm

end AlgebraicGeometry.ProjSpace
