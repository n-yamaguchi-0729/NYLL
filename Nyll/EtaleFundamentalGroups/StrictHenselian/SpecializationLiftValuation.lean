/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationLift
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationResidueField
import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationValuation
import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# A valuation diagram retaining a chosen geometric specialization

Apply the actual valuation factorization to the specified homomorphism
from the strict local model at the special point. The valuation ring is a
subring of the original algebraically closed generic field, which is its
fraction field. The generic field is therefore retained exactly.

The valuation ring is henselian and has algebraically closed residue
field. A common algebraically closed extension of this residue field and
the independently specified special geometric field gives the closed
triangle. Both triangles commute over the strict local model and the
original scheme; no Noetherian hypothesis is needed.

This is the diagram construction in Stacks Project, Lemma 58.16.3,
https://stacks.math.columbia.edu/tag/0C0M. The identification of the
fundamental-group specialization maps additionally requires the proper
closed-fiber comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- A chosen geometric specialization is realized by a henselian valuation
subring of its original algebraically closed generic field. The entire
chosen strict-local map and the independently specified special geometric
point are retained in the two actual scheme triangles. -/
theorem exists_strictlyHenselianValuation_of_specializationLift
    {S : Scheme.{u}} {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsAlgClosed Ωt]
    (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
    (h : t (closedPoint Ωt) ⤳ s (closedPoint Ωs))
    (ψ : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ωt)
    (hψ : ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
      (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom) :
    ∃ (V : ValuationSubring Ωt) (_ : HenselianLocalRing V),
      IsAlgClosed (ResidueField V) ∧
      ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
        (j : Ωs →+* k) (o : ResidueField V →+* k)
        (f : geometricStalk
          (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* V),
        IsLocalHom f ∧ (algebraMap V Ωt).comp f = ψ ∧
        (o.comp (residue V)).comp f = j.comp
          (geometricStalkEvaluation
            (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))).hom ∧
        Spec.map (CommRingCat.ofHom (algebraMap V Ωt)) ≫
            Spec.map (CommRingCat.ofHom f) ≫ localGeometricStalkToScheme s = t ∧
        Spec.map (CommRingCat.ofHom (o.comp (residue V))) ≫
            Spec.map (CommRingCat.ofHom f) ≫ localGeometricStalkToScheme s =
          Spec.map (CommRingCat.ofHom j) ≫ s := by
  let x : S := s (closedPoint Ωs)
  let R : CommRingCat.{u} := S.presheaf.stalk x
  let sr : R →+* Ωs := (Scheme.stalkClosedPointTo s).hom
  let H : CommRingCat.{u} := geometricStalk (Spec.map (CommRingCat.ofHom sr))
  obtain ⟨V, f, _, hHenselian, hResidue, hf, hgeneric, _⟩ :=
    exists_strictlyHenselianValuationFactor ψ
  obtain ⟨k, hk, hkclosed, j, o, _, _, hclosed⟩ :=
    exists_algebraicallyClosedResidueFieldSquare f
      (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom sr))).hom
  let c : R ⟶ H := CommRingCat.ofHom (geometricStalkStructureMap sr)
  let qR : Spec R ⟶ S := S.fromSpecStalk x
  let qH : Spec H ⟶ S := localGeometricStalkToScheme s
  let ψCat : H ⟶ CommRingCat.of Ωt := CommRingCat.ofHom ψ
  let tr : R ⟶ CommRingCat.of Ωt := Scheme.stalkSpecializationToField x t h
  have hψCat : c ≫ ψCat = tr := congrArg CommRingCat.ofHom hψ
  have hψScheme : Spec.map ψCat ≫ qH = t := by
    change Spec.map ψCat ≫ (Spec.map c ≫ qR) = t
    rw [← Category.assoc, ← Spec.map_comp, hψCat]
    exact Scheme.Spec_stalkSpecializationToField_fromSpecStalk x t h
  let e : H ⟶ CommRingCat.of Ωs :=
    geometricStalkEvaluation (Spec.map (CommRingCat.ofHom sr))
  have he : Spec.map e ≫ qH = s := localGeometricStalkToScheme_evaluation s
  let fCat : H ⟶ CommRingCat.of V := CommRingCat.ofHom f
  let ηCat : CommRingCat.of V ⟶ CommRingCat.of Ωt := CommRingCat.ofHom (algebraMap V Ωt)
  let oCat : CommRingCat.of V ⟶ CommRingCat.of k := CommRingCat.ofHom (o.comp (residue V))
  let jCat : CommRingCat.of Ωs ⟶ CommRingCat.of k := CommRingCat.ofHom j
  have hgCat : fCat ≫ ηCat = ψCat := congrArg CommRingCat.ofHom hgeneric
  have hoCat : fCat ≫ oCat = e ≫ jCat := congrArg CommRingCat.ofHom hclosed
  refine ⟨V, hHenselian, hResidue, k, hk, hkclosed, j, o, f, hf, hgeneric, hclosed, ?_, ?_⟩
  · change Spec.map ηCat ≫ Spec.map fCat ≫ qH = t
    rw [← Category.assoc, ← Spec.map_comp, hgCat]
    exact hψScheme
  · change Spec.map oCat ≫ Spec.map fCat ≫ qH = Spec.map jCat ≫ s
    rw [← Category.assoc, ← Spec.map_comp, hoCat, Spec.map_comp, Category.assoc, he]

end EtaleFundamentalGroups.StrictHenselian
