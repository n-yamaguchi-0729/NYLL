/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Lifting a geometric specialization to the actual strict local model

The geometric stalk at a closed field-valued point of a local ring is
faithfully flat over that ring. Tensoring with any specified generic field
therefore gives a nontrivial ring. A maximal quotient and its algebraic
closure construct a lift of the generic point after a field extension.

For arbitrary schemes, the ordinary stalk-specialization map supplies the
map from the local ring to the original generic field. The lift then lands
in the actual geometric stalk of that local ring. Both geometric points
retain their original maps to the scheme. The existence of the lift and
the compatibility of the maps are proved, not included as input data.

This is the local-diagram construction used in Stacks Project, Section
58.16, https://stacks.math.columbia.edu/tag/0BUP.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Every field-valued point of a local base lifts to its actual geometric
stalk after an algebraically closed extension of the specified field.
Faithful flatness supplies the nonempty fiber used in the construction. -/
theorem geometricStalk_exists_genericPointLift
    {A Ωs Ωt : Type u} [CommRing A] [IsLocalRing A] [Field Ωs] [Field Ωt]
    (s : A →+* Ωs) [IsLocalHom s] (t : A →+* Ωt) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : Ωt →+* Ω)
      (l : geometricStalk (Spec.map (CommRingCat.ofHom s)) →+* Ω),
      l.comp (geometricStalkStructureMap s) = i.comp t := by
  let H : CommRingCat.{u} := geometricStalk (Spec.map (CommRingCat.ofHom s))
  let : Algebra A H := (geometricStalkStructureMap s).toAlgebra
  have : Module.FaithfullyFlat A H := geometricStalkStructureMap_faithfullyFlat s
  let : Algebra A Ωt := t.toAlgebra
  let T : Type u := H ⊗[A] Ωt
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  let F : Type u := T ⧸ m
  let : Field F := Ideal.Quotient.field m
  let Ω : Type u := AlgebraicClosure F
  let q : T →+* Ω := (algebraMap F Ω).comp (Ideal.Quotient.mk m)
  let a : H →+* T := Algebra.TensorProduct.includeLeftRingHom
  let b : Ωt →+* T := Algebra.TensorProduct.includeRight.toRingHom
  refine ⟨Ω, inferInstance, inferInstance, q.comp b, q.comp a, ?_⟩
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  exact congrArg (fun f : A →+* T => q.comp f)
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := A) (A := H) (B := Ωt))

variable {S : Scheme.{u}} {Ωs Ωt : Type u} [Field Ωs] [Field Ωt]

/-- The spectrum of the actual geometric stalk of the ordinary local ring,
with its canonical morphism to the original scheme. -/
def localGeometricStalkToScheme (s : Spec (.of Ωs) ⟶ S) :
    Spec (geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))) ⟶ S :=
  Spec.map (CommRingCat.ofHom
      (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom)) ≫
    S.fromSpecStalk (s (closedPoint Ωs))

/-- The original closed geometric point factors through the constructed
strict local model by its actual evaluation homomorphism. -/
theorem localGeometricStalkToScheme_evaluation (s : Spec (.of Ωs) ⟶ S) :
    Spec.map (CommRingCat.ofHom
        (geometricStalkEvaluation
          (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))).hom) ≫
      localGeometricStalkToScheme s = s := by
  change Spec.map (CommRingCat.ofHom
      (geometricStalkEvaluation
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))).hom) ≫
    (Spec.map (CommRingCat.ofHom
      (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom)) ≫
        S.fromSpecStalk (s (closedPoint Ωs))) = s
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    geometricStalkStructureMap_evaluation, CommRingCat.ofHom_hom]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk s

/-- A specialization of arbitrary geometric points on a scheme admits an
actual generic lift to the strict local model at its special point. The
chosen field extension and both original scheme morphisms are retained. -/
theorem exists_localGeometricStalk_specializationLift
    (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
    (h : t (closedPoint Ωt) ⤳ s (closedPoint Ωs)) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : Ωt →+* Ω)
      (l : geometricStalk
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ω),
      l.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
        i.comp (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom ∧
      Spec.map (CommRingCat.ofHom l) ≫ localGeometricStalkToScheme s =
        Spec.map (CommRingCat.ofHom i) ≫ t := by
  obtain ⟨Ω, hField, hClosed, i, l, hcomp⟩ := geometricStalk_exists_genericPointLift
    (Scheme.stalkClosedPointTo s).hom
    (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom
  refine ⟨Ω, hField, hClosed, i, l, hcomp, ?_⟩
  change Spec.map (CommRingCat.ofHom l) ≫
    (Spec.map (CommRingCat.ofHom
      (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom)) ≫
        S.fromSpecStalk (s (closedPoint Ωs))) = Spec.map (CommRingCat.ofHom i) ≫ t
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom,
    Scheme.Spec_stalkSpecializationToField_fromSpecStalk]

end EtaleFundamentalGroups.StrictHenselian
