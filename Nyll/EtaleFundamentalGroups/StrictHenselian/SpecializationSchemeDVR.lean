/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationDVR
import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationResidueField
import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Strict henselian DVR diagrams for geometric specializations of schemes

Given two field-valued points of a locally Noetherian scheme whose underlying
points specialize, the ordinary stalk at the special point is Noetherian.
Its actual specialization map to the generic field therefore has the DVR
factorization constructed in `SpecializationDVR`. The common residue-field
construction also retains the independently specified special geometric
field. The resulting generic and special triangles commute as scheme maps.

This constructs the geometric-point diagram for the DVR reduction in
Stacks Project, Lemma 58.16.4, https://stacks.math.columbia.edu/tag/0C0N.
The comparison with a previously chosen fundamental-group specialization
map requires its additional strict-local lifting data and the proper-fiber
comparison; neither is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- A specialization of field-valued points on a locally Noetherian scheme
is realized by an actual strictly henselian DVR after algebraically closed
extensions of the two specified geometric fields. The generic map uses the
actual fraction field, and the special map uses the actual residue field. -/
theorem exists_strictlyHenselianDVR_specializationDiagram
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    {Ωs Ωt : Type u} [Field Ωs] [Field Ωt]
    (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
    (h : t (closedPoint Ωt) ⤳ s (closedPoint Ωs)) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
      (i : Ωt →+* K) (j : Ωs →+* k)
      (D : CommRingCat.{u}) (_ : IsDomain D) (_ : HenselianLocalRing D),
      IsDiscreteValuationRing D ∧ IsSepClosed (ResidueField D) ∧
      ∃ (p : Spec D ⟶ S) (η : FractionRing D →+* K) (o : ResidueField D →+* k),
        Spec.map (CommRingCat.ofHom η) ≫
            Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D))) ≫ p =
          Spec.map (CommRingCat.ofHom i) ≫ t ∧
        Spec.map (CommRingCat.ofHom (o.comp (residue D))) ≫ p =
          Spec.map (CommRingCat.ofHom j) ≫ s := by
  let x : S := s (closedPoint Ωs)
  let A : CommRingCat.{u} := S.presheaf.stalk x
  let φ : A →+* Ωt := (Scheme.stalkSpecializationToField x t h).hom
  let Ω : Type u := AlgebraicClosure Ωt
  let a : Ωt →+* Ω := algebraMap Ωt Ω
  obtain ⟨K, hK, hKclosed, i, D, hDomain, hHenselian, hDVR, hResidue,
    f, η, _, hf, hgeneric, _⟩ := exists_strictlyHenselianDVRDiagram (a.comp φ)
  obtain ⟨k, hk, hkclosed, j, o, _, _, hclosed⟩ :=
    exists_algebraicallyClosedResidueFieldSquare f (Scheme.stalkClosedPointTo s).hom
  let p : Spec D ⟶ S := Spec.map (CommRingCat.ofHom f) ≫ S.fromSpecStalk x
  have hgenericRing :
      (η.comp (algebraMap D (FractionRing D))).comp f = (i.comp a).comp φ := by
    rw [RingHom.comp_assoc, hgeneric, ← RingHom.comp_assoc]
  refine ⟨K, hK, hKclosed, k, hk, hkclosed, i.comp a, j, D, hDomain, hHenselian,
    hDVR, hResidue, p, η, o, ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom η) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D))) ≫
        (Spec.map (CommRingCat.ofHom f) ≫ S.fromSpecStalk x)) =
      Spec.map (CommRingCat.ofHom (i.comp a)) ≫ t
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      hgenericRing, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    change Spec.map (CommRingCat.ofHom (i.comp a)) ≫
        (Spec.map (Scheme.stalkSpecializationToField x t h) ≫ S.fromSpecStalk x) =
      Spec.map (CommRingCat.ofHom (i.comp a)) ≫ t
    rw [Scheme.Spec_stalkSpecializationToField_fromSpecStalk]
  · change Spec.map (CommRingCat.ofHom (o.comp (residue D))) ≫
      (Spec.map (CommRingCat.ofHom f) ≫ S.fromSpecStalk x) =
      Spec.map (CommRingCat.ofHom j) ≫ s
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hclosed,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom]
    exact congrArg (fun q : Spec (.of Ωs) ⟶ S => Spec.map (CommRingCat.ofHom j) ≫ q)
      (Scheme.Spec_stalkClosedPointTo_fromSpecStalk s)

end EtaleFundamentalGroups.StrictHenselian
