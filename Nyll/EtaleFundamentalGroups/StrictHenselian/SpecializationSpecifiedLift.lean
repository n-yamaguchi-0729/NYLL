/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkGenericIntegral
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationLift
import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Lifting the specified generic geometric point

The field base change of the actual pointed étale colimit is integral.
Faithful flatness supplies a maximal quotient of this nonzero algebra,
and that quotient is an algebraic field extension of the specified generic
field. Algebraic closedness embeds it back into that same field.

This constructs the lift used at the beginning of Stacks Project, Section
58.16, with the original generic geometric point and its morphism to the
scheme unchanged. The source scheme need not be Noetherian.

https://stacks.math.columbia.edu/tag/0BUP
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Every algebraically closed field-valued point of a local ring lifts to
the actual geometric stalk at a local field-valued point. The lift takes
values in the originally specified algebraically closed field. -/
theorem geometricStalk_exists_lift_to_isAlgClosed
    {A Ωs Ωt : Type u} [CommRing A] [IsLocalRing A]
    [Field Ωs] [Field Ωt] [IsAlgClosed Ωt]
    (s : A →+* Ωs) [IsLocalHom s] (t : A →+* Ωt) :
    ∃ l : geometricStalk (Spec.map (CommRingCat.ofHom s)) →+* Ωt,
      l.comp (geometricStalkStructureMap s) = t := by
  let H : CommRingCat.{u} := geometricStalk (Spec.map (CommRingCat.ofHom s))
  let : Algebra A H := (geometricStalkStructureMap s).toAlgebra
  have : Module.FaithfullyFlat A H := geometricStalkStructureMap_faithfullyFlat s
  let : Algebra A Ωt := t.toAlgebra
  let T : Type u := Ωt ⊗[A] H
  have : Algebra.IsIntegral Ωt T := geometricStalk_tensor_isIntegral s Ωt
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  let F : Type u := T ⧸ m
  let : Field F := Ideal.Quotient.field m
  let q : T →ₐ[Ωt] F := Ideal.Quotient.mkₐ Ωt m
  have : Algebra.IsIntegral Ωt F :=
    Algebra.IsIntegral.of_surjective q Ideal.Quotient.mk_surjective
  let z : F →ₐ[Ωt] Ωt := IsAlgClosed.lift
  let c : H →+* T := Algebra.TensorProduct.includeRight.toRingHom
  refine ⟨z.toRingHom.comp (q.toRingHom.comp c), ?_⟩
  ext a
  change z (q (c (geometricStalkStructureMap s a))) = t a
  have hcoeff := RingHom.congr_fun
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := A) (A := Ωt) (B := H)) a
  change algebraMap Ωt T (t a) = c (geometricStalkStructureMap s a) at hcoeff
  rw [← hcoeff, q.commutes, z.commutes]
  exact Algebra.algebraMap_self_apply (t a)

/-- The original generic geometric point of a specialization lifts through
the actual strict local model at the special geometric point. Both the
ring triangle and the morphism to the original scheme commute. -/
theorem exists_localGeometricStalk_specifiedSpecializationLift
    {S : Scheme.{u}} {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsAlgClosed Ωt]
    (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
    (h : t (closedPoint Ωt) ⤳ s (closedPoint Ωs)) :
    ∃ l : geometricStalk
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ωt,
      l.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
        (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom ∧
      Spec.map (CommRingCat.ofHom l) ≫ localGeometricStalkToScheme s = t := by
  obtain ⟨l, hcomp⟩ := geometricStalk_exists_lift_to_isAlgClosed
    (Scheme.stalkClosedPointTo s).hom
    (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom
  refine ⟨l, hcomp, ?_⟩
  change Spec.map (CommRingCat.ofHom l) ≫
    (Spec.map (CommRingCat.ofHom
      (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom)) ≫
        S.fromSpecStalk (s (closedPoint Ωs))) = t
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp,
    CommRingCat.ofHom_hom]
  exact Scheme.Spec_stalkSpecializationToField_fromSpecStalk (s (closedPoint Ωs)) t h

end EtaleFundamentalGroups.StrictHenselian
