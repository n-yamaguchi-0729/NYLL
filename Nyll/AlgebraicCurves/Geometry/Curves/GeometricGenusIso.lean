/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenus
public import Nyll.AlgebraicCurves.Geometry.AlgEquivFunctionFieldIso
public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.GenusFFEqAlgEquiv
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# Geometric genus under an actual isomorphism over the ground field

Base change of the given isomorphism identifies the actual geometric
function fields. Their original repartition genera are therefore equal.
This comparison applies in particular to the two orders of a constant
field pullback.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SmoothProperCurve

universe u

/-- An actual isomorphism over the base preserves the point-independent
geometric genus, through the induced geometric function-field equivalence. -/
theorem geometricGenus_eq_of_iso
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (cX : X ⟶ Spec (.of k)) (cY : Y ⟶ Spec (.of k))
    [GeometricallyIntegral cX] [GeometricallyIntegral cY]
    (e : X ≅ Y) (he : e.hom ≫ cY = cX) :
    geometricGenus k cX = geometricGenus k cY := by
  let Ω := AlgebraicClosure k
  let b := specMap k Ω
  let eΩ : pullback cX b ≅ pullback cY b :=
    { hom := pullback.lift (pullback.fst cX b ≫ e.hom) (pullback.snd cX b)
        (by rw [Category.assoc, he, pullback.condition])
      inv := pullback.lift (pullback.fst cY b ≫ e.inv) (pullback.snd cY b)
        (by rw [Category.assoc, ← he, e.inv_hom_id_assoc, pullback.condition])
      hom_inv_id := by
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
            e.hom_inv_id, Category.comp_id, Category.id_comp]
        · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
            e.inv_hom_id, Category.comp_id, Category.id_comp]
        · simp only [Category.assoc, pullback.lift_snd, Category.id_comp] }
  have hbase : eΩ.hom ≫ baseChange k cY Ω = baseChange k cX Ω :=
    pullback.lift_snd _ _ _
  let := (AlgebraicCurve.baseToFunctionField (baseChange k cX Ω)).toAlgebra
  let := (AlgebraicCurve.baseToFunctionField (baseChange k cY Ω)).toAlgebra
  obtain ⟨φ⟩ := AlgebraicCurve.nonempty_algEquiv_functionField_of_iso
    (baseChange k cX Ω) (baseChange k cY Ω) eΩ hbase
  exact AlgebraicCurve.genusFF_eq_of_algEquiv φ

end AlgebraicGeometry.SmoothProperCurve
