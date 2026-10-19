/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkNoetherian
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationLift
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationDVR
import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationResidueField
import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# A strict henselian DVR retaining a chosen geometric specialization

For a locally Noetherian scheme, the actual geometric stalk of the local
ring at the special point is Noetherian. Apply the DVR construction to the
specified homomorphism from this stalk to the generic geometric field.
The resulting local homomorphism to the DVR therefore retains that chosen
lift, including its values on the entire geometric stalk.

A common algebraically closed extension of the special geometric field
and the DVR residue field retains evaluation at the special point. Both
triangles commute already over the strict local model and hence over the
original scheme. The two field extensions and the actual fraction and
residue fields of the DVR are part of the result.

This is the diagram construction in the proof of Stacks Project, Lemma
58.16.4, https://stacks.math.columbia.edu/tag/0C0N. The identification of
fundamental-group specialization maps additionally uses proper-fiber
comparison; that categorical assertion is separate from this diagram.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Every specified lift of a geometric specialization on a locally
Noetherian scheme factors through an actual strictly henselian DVR after
field extensions. Both original geometric points and the entire chosen
strict-local-ring homomorphism are retained in the resulting diagram. -/
theorem exists_strictlyHenselianDVR_of_specializationLift
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    {Ωs Ωt : Type u} [Field Ωs] [Field Ωt]
    (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
    (h : t (closedPoint Ωt) ⤳ s (closedPoint Ωs))
    (ψ : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ωt)
    (hψ : ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
      (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
      (i : Ωt →+* K) (j : Ωs →+* k)
      (D : CommRingCat.{u}) (_ : IsDomain D) (_ : HenselianLocalRing D),
      IsDiscreteValuationRing D ∧ IsSepClosed (ResidueField D) ∧
      ∃ (f : geometricStalk
          (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* D)
        (η : FractionRing D →+* K) (o : ResidueField D →+* k),
        IsLocalHom f ∧
        η.comp ((algebraMap D (FractionRing D)).comp f) = i.comp ψ ∧
        (o.comp (residue D)).comp f = j.comp
          (geometricStalkEvaluation
            (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))).hom ∧
        Spec.map (CommRingCat.ofHom η) ≫
            Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D))) ≫
            Spec.map (CommRingCat.ofHom f) ≫ localGeometricStalkToScheme s =
          Spec.map (CommRingCat.ofHom i) ≫ t ∧
        Spec.map (CommRingCat.ofHom (o.comp (residue D))) ≫
            Spec.map (CommRingCat.ofHom f) ≫ localGeometricStalkToScheme s =
          Spec.map (CommRingCat.ofHom j) ≫ s := by
  let x : S := s (closedPoint Ωs)
  let R : CommRingCat.{u} := S.presheaf.stalk x
  let sr : R →+* Ωs := (Scheme.stalkClosedPointTo s).hom
  let H : CommRingCat.{u} := geometricStalk (Spec.map (CommRingCat.ofHom sr))
  have : IsNoetherianRing H := geometricStalk_isNoetherianRing sr
  let Ω : Type u := AlgebraicClosure Ωt
  let α : Ωt →+* Ω := algebraMap Ωt Ω
  obtain ⟨K, hK, hKclosed, a, D, hDomain, hHenselian, hDVR, hResidue,
    f, η, _, hf, hgeneric, _⟩ := exists_strictlyHenselianDVRDiagram (α.comp ψ)
  obtain ⟨k, hk, hkclosed, j, o, _, _, hclosed⟩ :=
    exists_algebraicallyClosedResidueFieldSquare f
      (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom sr))).hom
  let i : Ωt →+* K := a.comp α
  have hg : η.comp ((algebraMap D (FractionRing D)).comp f) = i.comp ψ := by
    exact hgeneric.trans (RingHom.comp_assoc ψ α a).symm
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
  let fCat : H ⟶ D := CommRingCat.ofHom f
  let dCat : D ⟶ CommRingCat.of (FractionRing D) :=
    CommRingCat.ofHom (algebraMap D (FractionRing D))
  let ηCat : CommRingCat.of (FractionRing D) ⟶ CommRingCat.of K := CommRingCat.ofHom η
  let iCat : CommRingCat.of Ωt ⟶ CommRingCat.of K := CommRingCat.ofHom i
  let oCat : D ⟶ CommRingCat.of k := CommRingCat.ofHom (o.comp (residue D))
  let jCat : CommRingCat.of Ωs ⟶ CommRingCat.of k := CommRingCat.ofHom j
  have hgCat : (fCat ≫ dCat) ≫ ηCat = ψCat ≫ iCat := congrArg CommRingCat.ofHom hg
  have hoCat : fCat ≫ oCat = e ≫ jCat := congrArg CommRingCat.ofHom hclosed
  refine ⟨K, hK, hKclosed, k, hk, hkclosed, i, j, D, hDomain, hHenselian,
    hDVR, hResidue, f, η, o, hf, hg, hclosed, ?_, ?_⟩
  · change Spec.map ηCat ≫ Spec.map dCat ≫ Spec.map fCat ≫ qH = Spec.map iCat ≫ t
    calc
      Spec.map ηCat ≫ Spec.map dCat ≫ Spec.map fCat ≫ qH =
          Spec.map ((fCat ≫ dCat) ≫ ηCat) ≫ qH := by
        rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
      _ = Spec.map (ψCat ≫ iCat) ≫ qH :=
        congrArg (fun a' : H ⟶ CommRingCat.of K => Spec.map a' ≫ qH) hgCat
      _ = Spec.map iCat ≫ t := by
        rw [Spec.map_comp, Category.assoc, hψScheme]
  · change Spec.map oCat ≫ Spec.map fCat ≫ qH = Spec.map jCat ≫ s
    rw [← Category.assoc, ← Spec.map_comp, hoCat,
      Spec.map_comp, Category.assoc, he]

end EtaleFundamentalGroups.StrictHenselian
