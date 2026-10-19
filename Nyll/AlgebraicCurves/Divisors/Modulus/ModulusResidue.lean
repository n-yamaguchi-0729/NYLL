/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusIdeal
import Nyll.AlgebraicCurves.Places.ValuationRings.RangeStalkEq
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Residue fields of the closed points of a modulus

The structure map of the curve gives the scalar map on every stalk and
residue field. Its compatibility with the function-field embedding upgrades
the actual stalk comparison to a residue-field algebra equivalence. Thus the
closed point belonging to a place has precisely that place's residue degree.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve.Modulus

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))

/-- The structure morphism followed by the actual germ at a point. -/
def stalkBase (x : C) : K →+* C.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop ≫
    C.presheaf.germ ⊤ x trivial).hom

/-- The ground-field map into the actual residue field of a curve point. -/
def residueBase (x : C) : K →+* C.residueField x :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop ≫ C.Γevaluation x).hom

theorem residueBase_apply (x : C) (a : K) :
    residueBase c x a = IsLocalRing.residue (C.presheaf.stalk x) (stalkBase c x a) := rfl

/-- The geometric residue point is over its actual ground-field map. -/
theorem fromSpecResidueField_comp_residueBase (x : C) :
    C.fromSpecResidueField x ≫ c =
      Spec.map (CommRingCat.ofHom (residueBase c x)) := by
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  simp only [← Spec.map_comp]
  congr 1
  rw [Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of K) (c x)]
  exact congrArg (fun f => (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f)
    (Scheme.Γevaluation_naturality c x)

/-- A closed point on a curve of finite type has finite residue degree over
the original field, with the scalar map induced by the structure morphism. -/
theorem residueBase_finite [LocallyOfFiniteType c] (x : C)
    (hx : IsClosed ({x} : Set C)) : (residueBase c x).Finite := by
  have : IsClosedImmersion (C.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hfinite : IsFinite (C.fromSpecResidueField x ≫ c) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  rw [fromSpecResidueField_comp_residueBase c x] at hfinite
  exact (IsFinite.SpecMap_iff (CommRingCat.ofHom (residueBase c x))).mp hfinite

variable [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]

/-- The stalk at the closed point of a place, identified using its embedding
in the function field. -/
def stalkEquivAtPlace :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField,
      C.presheaf.stalk (pointOfPlace c v) ≃+* v.toValuationSubring := by
  intro _functionFieldAlgebra v
  exact stalkEquivOfRange (pointOfPlace c v) v (pointOfPlace_range_stalk c v)

/-- The stalk equivalence preserves the actual ground-field scalars. -/
theorem stalkEquivAtPlace_base :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ (v : Place K C.functionField) (a : K),
      stalkEquivAtPlace c v (stalkBase c (pointOfPlace c v) a) =
        algebraMap K v.toValuationSubring a := by
  intro _functionFieldAlgebra v a
  apply Subtype.ext
  rw [stalkEquivAtPlace, coe_stalkEquivOfRange, Place.coe_algebraMap]
  exact (baseToFunctionField_apply_eq_algebraMap_stalk c (pointOfPlace c v) a).symm

/-- The scheme residue field and the place residue field agree as algebras
over the field specified by the curve's structure morphism. -/
def residueEquivAtPlace :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField,
      let _ : Algebra K (C.residueField (pointOfPlace c v)) :=
        (residueBase c (pointOfPlace c v)).toAlgebra
      C.residueField (pointOfPlace c v) ≃ₐ[K] v.ResidueField := by
  intro _functionFieldAlgebra v _residueAlgebra
  refine AlgEquiv.ofRingEquiv
    (f := IsLocalRing.ResidueField.mapEquiv (stalkEquivAtPlace c v)) ?_
  intro a
  have : IsLocalHom (stalkEquivAtPlace c v).toRingHom :=
    isLocalHom_toRingHom (stalkEquivAtPlace c v)
  change IsLocalRing.ResidueField.map (stalkEquivAtPlace c v).toRingHom
    (residueBase c (pointOfPlace c v) a) = algebraMap K v.ResidueField a
  rw [residueBase_apply, IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue v.toValuationSubring)
    (stalkEquivAtPlace_base c v a)

/-- Finiteness of the place's residue field is supplied by its actual closed
point on the given curve. -/
theorem finite_residueFieldAtPlace :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField, Module.Finite K v.ResidueField := by
  intro _functionFieldAlgebra v
  let _ : Algebra K (C.residueField (pointOfPlace c v)) :=
    (residueBase c (pointOfPlace c v)).toAlgebra
  have : Module.Finite K (C.residueField (pointOfPlace c v)) :=
    residueBase_finite c (pointOfPlace c v) (pointOfPlace_closed c v)
  exact Module.Finite.equiv (residueEquivAtPlace c v).toLinearEquiv

/-- The actual closed point, presented as the spectrum of the place's residue
field with its original ground-field algebra. -/
def residuePoint :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField, Spec (CommRingCat.of v.ResidueField) ⟶ C := by
  intro _functionFieldAlgebra v
  let _ : Algebra K (C.residueField (pointOfPlace c v)) :=
    (residueBase c (pointOfPlace c v)).toAlgebra
  exact Spec.map (residueEquivAtPlace c v).toRingEquiv.toCommRingCatIso.hom ≫
    C.fromSpecResidueField (pointOfPlace c v)

/-- The residue point commutes with the specified ground-field structure map. -/
theorem residuePoint_comp :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField, residuePoint c v ≫ c =
      Spec.map (CommRingCat.ofHom (algebraMap K v.ResidueField)) := by
  intro _functionFieldAlgebra v
  let _ : Algebra K (C.residueField (pointOfPlace c v)) :=
    (residueBase c (pointOfPlace c v)).toAlgebra
  rw [residuePoint, Category.assoc, fromSpecResidueField_comp_residueBase, ← Spec.map_comp]
  congr 1
  ext a
  exact (residueEquivAtPlace c v).commutes a

theorem residuePoint_isClosedImmersion :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField, IsClosedImmersion (residuePoint c v) := by
  intro _functionFieldAlgebra v
  let _ : Algebra K (C.residueField (pointOfPlace c v)) :=
    (residueBase c (pointOfPlace c v)).toAlgebra
  have : IsClosedImmersion (C.fromSpecResidueField (pointOfPlace c v)) :=
    isClosed_singleton_iff_isClosedImmersion.mp (pointOfPlace_closed c v)
  change IsClosedImmersion
    (Spec.map (residueEquivAtPlace c v).toRingEquiv.toCommRingCatIso.hom ≫
      C.fromSpecResidueField (pointOfPlace c v))
  infer_instance

/-- The finite scheme degree of this actual residue point is its place degree. -/
theorem residuePoint_finrank :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField,
      (residuePoint c v ≫ c).finrank (IsLocalRing.closedPoint K) = v.deg := by
  intro _functionFieldAlgebra v
  have : Module.Finite K v.ResidueField := finite_residueFieldAtPlace c v
  rw [residuePoint_comp, Scheme.Hom.finrank_SpecMap_algebraMap,
    Module.rankAtStalk_eq_finrank_of_free]
  rfl

end AlgebraicCurve.Modulus
