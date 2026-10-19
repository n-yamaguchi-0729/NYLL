/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# The coordinate algebra of an actual finite scheme

The relative Gamma functor supplies the coefficient algebra structure.
Finiteness follows from the actual finite structure morphism. Over a field,
the scheme-theoretic finite flat rank is its vector-space dimension.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace SchemeTheory.Affine.FiniteScheme

variable {R : Type u} [CommRing R] {Z : Scheme.{u}}

/-- The actual global sections, with their relative Gamma algebra structure. -/
abbrev coordinateAlgebra (q : Z ⟶ Spec (CommRingCat.of R)) : CommAlgCat.{u} R :=
  ((algΓ (CommRingCat.of R)).obj (Over.mk q)).unop

theorem coordinateAlgebra_algebraMap (q : Z ⟶ Spec (CommRingCat.of R)) :
    algebraMap R (coordinateAlgebra q) =
      q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := rfl

/-- The coordinate algebra is finite over the original coefficient ring. -/
instance coordinateAlgebra_finite (q : Z ⟶ Spec (CommRingCat.of R)) [IsFinite q] :
    Module.Finite R (coordinateAlgebra q) := by
  apply RingHom.finite_algebraMap.mp
  rw [coordinateAlgebra_algebraMap]
  exact RingHom.Finite.comp q.finite_appTop
    (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective)

/-- The affine presentation is the actual global-sections isomorphism. -/
def coordinateIso (q : Z ⟶ Spec (CommRingCat.of R)) [IsFinite q] :
    Z ≅ Spec (CommRingCat.of (coordinateAlgebra q)) := by
  let : IsAffine Z := isAffine_of_isAffineHom q
  exact Z.isoSpec

/-- The global-sections presentation preserves the given structure map. -/
@[reassoc] theorem coordinateIso_toBase
    (q : Z ⟶ Spec (CommRingCat.of R)) [IsFinite q] :
    (coordinateIso q).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (coordinateAlgebra q))) = q := by
  let : IsAffine Z := isAffine_of_isAffineHom q
  have hn := Scheme.isoSpec_hom_naturality q
  rw [Scheme.isoSpec_Spec_hom] at hn
  change Z.isoSpec.hom ≫ Spec.map
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appTop) = q
  rw [Spec.map_comp, ← Category.assoc, hn, Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.comp_id]

variable {K : Type u} [Field K]

/-- Over a field, finite flat rank equals the dimension of the actual
coordinate algebra, including for nonreduced finite schemes. -/
theorem finrank_coordinateAlgebra (q : Z ⟶ Spec (CommRingCat.of K))
    [IsFinite q] [Flat q] :
    Module.finrank K (coordinateAlgebra q) = q.finrank (IsLocalRing.closedPoint K) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K (coordinateAlgebra q)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap K (coordinateAlgebra q)))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  conv_rhs => rw [← coordinateIso_toBase q]
  rw [Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  rfl

end SchemeTheory.Affine.FiniteScheme
