/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkChangeField
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkChangeFieldIso
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFunctoriality
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationHomExt
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationLift
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
public import Nyll.EtaleFundamentalGroups.StrictHenselian.LocalGeometricStalkNaturality
public import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationSchemeComposition
public import Nyll.SchemeTheory.LocalGeometry.PointedStalkMap
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Pointing-field extension on the actual scheme-local model

The existing field-extension isomorphism for an affine geometric stalk
also applies to the actual local model attached to a scheme point. The
ordinary stalk identification is retained by the original pointed-stalk
map. Its isomorphism and the existing functoriality of geometric stalks
give the comparison without a new construction of strict henselizations.

The inverse of this actual comparison extends any chosen generic lift.
The resulting lift restricts to the original one and retains its original
scheme triangle.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

private theorem geometricStalkMap_sameField_isIso
    {S T : Scheme.{u}} {Ω : Type u} [Field Ω]
    (f : S ⟶ T) [IsIso f]
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω) ⟶ T)
    (h : s ≫ f = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ t) :
    IsIso (geometricStalkMap f s t (RingHom.id Ω) h) := by
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id Ω)) =
      𝟙 (Spec (.of Ω)) := Spec.map_id _
  have hf : s ≫ f = t := h.trans (by rw [hid, Category.id_comp])
  have hg : t ≫ inv f = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ s := by
    rw [hid, Category.id_comp, ← hf, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  let M := geometricStalkMap f s t (RingHom.id Ω) h
  let N := geometricStalkMap (inv f) t s (RingHom.id Ω) hg
  have hNM : N ≫ M = 𝟙 _ := by
    simpa only [IsIso.hom_inv_id, RingHom.id_comp, geometricStalkMap_id] using
      geometricStalkMap_comp f s t (RingHom.id Ω) h (inv f) s (RingHom.id Ω) hg
  have hMN : M ≫ N = 𝟙 _ := by
    simpa only [IsIso.inv_hom_id, RingHom.id_comp, geometricStalkMap_id] using
      geometricStalkMap_comp (inv f) t s (RingHom.id Ω) hg f t (RingHom.id Ω) h
  exact ⟨⟨N, hMN, hNM⟩⟩

private theorem geometricStalkMap_affine_isIso
    {R A Ω Ψ : Type u} [CommRing R] [CommRing A]
    [Field Ω] [Field Ψ] [IsSepClosed Ψ]
    (f : R →+* A) [IsIso (CommRingCat.ofHom f)]
    (s : A →+* Ω) (t : R →+* Ψ) (ι : Ψ →+* Ω)
    (h : Spec.map (CommRingCat.ofHom s) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom t)) :
    IsIso (geometricStalkMap (Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom s)) (Spec.map (CommRingCat.ofHom t)) ι h) := by
  have hB : Spec.map (CommRingCat.ofHom s) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫
        Spec.map (CommRingCat.ofHom (ι.comp t)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    exact h.trans (Spec.map_comp (CommRingCat.ofHom t) (CommRingCat.ofHom ι)).symm
  let B := geometricStalkMap (Spec.map (CommRingCat.ofHom f))
    (Spec.map (CommRingCat.ofHom s)) (Spec.map (CommRingCat.ofHom (ι.comp t)))
    (RingHom.id Ω) hB
  let C := geometricStalkChangeField t ι
  have : IsIso B := geometricStalkMap_sameField_isIso
    (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom s))
    (Spec.map (CommRingCat.ofHom (ι.comp t))) hB
  have hfactor : geometricStalkMap (Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom s)) (Spec.map (CommRingCat.ofHom t)) ι h = C ≫ B := by
    apply geometricStalk_hom_ext_of_structure_evaluation t
      (Spec.map (CommRingCat.ofHom s))
    · calc
        (geometricStalkMap (Spec.map (CommRingCat.ofHom f))
            (Spec.map (CommRingCat.ofHom s)) (Spec.map (CommRingCat.ofHom t)) ι h).hom.comp
            (geometricStalkStructureMap t) =
            (geometricStalkStructureMap s).comp f :=
          geometricStalkMap_affine_comp_structure f s t ι h
        _ = (C ≫ B).hom.comp (geometricStalkStructureMap t) := by
          change (geometricStalkStructureMap s).comp f =
            B.hom.comp (C.hom.comp (geometricStalkStructureMap t))
          rw [geometricStalkChangeField_comp_structure]
          exact (geometricStalkMap_affine_comp_structure f s (ι.comp t)
            (RingHom.id Ω) hB).symm
    · rw [geometricStalkMap_evaluation, Category.assoc,
        geometricStalkMap_evaluation, CommRingCat.ofHom_id, Category.comp_id]
      exact (geometricStalkChangeField_evaluation t ι).symm
  rw [hfactor]
  infer_instance

/-- The actual scheme-local pointing-field map is an isomorphism, including
the original identification of the two ordinary stalks. -/
theorem localGeometricStalkMap_changeField_isIso
    {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω']
    (s : Spec (.of Ω) ⟶ S) (ι : Ω →+* Ω') :
    IsIso (localGeometricStalkMap (𝟙 S) (Spec.map (CommRingCat.ofHom ι) ≫ s) s ι
      (Category.comp_id _)) := by
  have : IsIso (Scheme.pointedStalkMap (𝟙 S)
      (Spec.map (CommRingCat.ofHom ι) ≫ s) s ι (Category.comp_id _)) := by
    unfold Scheme.pointedStalkMap
    infer_instance
  unfold localGeometricStalkMap
  exact geometricStalkMap_affine_isIso _ _ _ _ _

/-- Extending the special pointing field gives a specified compatible
generic lift, by the inverse of the actual local-model isomorphism. -/
def localGeometricStalkChangeFieldLift
    {S : Scheme.{u}} {Ω Ω' Ψ : Type u}
    [Field Ω] [IsSepClosed Ω] [Field Ω'] [Field Ψ]
    (s : Spec (.of Ω) ⟶ S) (ι : Ω →+* Ω')
    (ψ : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ψ) :
    geometricStalk (Spec.map (CommRingCat.ofHom
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ι) ≫ s)).hom)) →+* Ψ := by
  have := localGeometricStalkMap_changeField_isIso s ι
  exact ψ.comp (inv (localGeometricStalkMap (𝟙 S)
    (Spec.map (CommRingCat.ofHom ι) ≫ s) s ι (Category.comp_id _))).hom

/-- The constructed lift restricts to the original chosen lift. -/
theorem localGeometricStalkChangeFieldLift_comp
    {S : Scheme.{u}} {Ω Ω' Ψ : Type u}
    [Field Ω] [IsSepClosed Ω] [Field Ω'] [Field Ψ]
    (s : Spec (.of Ω) ⟶ S) (ι : Ω →+* Ω')
    (ψ : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ψ) :
    (localGeometricStalkChangeFieldLift s ι ψ).comp
      (localGeometricStalkMap (𝟙 S) (Spec.map (CommRingCat.ofHom ι) ≫ s) s ι
        (Category.comp_id _)).hom = ψ := by
  have := localGeometricStalkMap_changeField_isIso s ι
  let M := localGeometricStalkMap (𝟙 S)
    (Spec.map (CommRingCat.ofHom ι) ≫ s) s ι (Category.comp_id _)
  change (ψ.comp (inv M).hom).comp M.hom = ψ
  have he := congrArg CommRingCat.Hom.hom (IsIso.hom_inv_id M)
  change (inv M).hom.comp M.hom = RingHom.id _ at he
  rw [RingHom.comp_assoc, he, RingHom.comp_id]

/-- The constructed lift has the original generic point over the scheme. -/
theorem localGeometricStalkChangeFieldLift_toScheme
    {S : Scheme.{u}} {Ω Ω' Ψ : Type u}
    [Field Ω] [IsSepClosed Ω] [Field Ω'] [Field Ψ]
    (s : Spec (.of Ω) ⟶ S) (ι : Ω →+* Ω')
    (t : Spec (.of Ψ) ⟶ S)
    (ψ : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ψ)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ localGeometricStalkToScheme s = t) :
    Spec.map (CommRingCat.ofHom (localGeometricStalkChangeFieldLift s ι ψ)) ≫
      localGeometricStalkToScheme (Spec.map (CommRingCat.ofHom ι) ≫ s) = t := by
  let M := localGeometricStalkMap (𝟙 S)
    (Spec.map (CommRingCat.ofHom ι) ≫ s) s ι (Category.comp_id _)
  have hM : Spec.map M ≫ localGeometricStalkToScheme s =
      localGeometricStalkToScheme (Spec.map (CommRingCat.ofHom ι) ≫ s) :=
    (localGeometricStalkMap_toScheme (𝟙 S)
      (Spec.map (CommRingCat.ofHom ι) ≫ s) s ι (Category.comp_id _)).trans
      (Category.comp_id _)
  rw [← hM, ← Category.assoc, ← Spec.map_comp]
  have he : M ≫ CommRingCat.ofHom (localGeometricStalkChangeFieldLift s ι ψ) =
      CommRingCat.ofHom ψ :=
    congrArg CommRingCat.ofHom (localGeometricStalkChangeFieldLift_comp s ι ψ)
  exact (congrArg (fun a : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) ⟶ CommRingCat.of Ψ =>
        Spec.map a ≫ localGeometricStalkToScheme s) he).trans hψ

end EtaleFundamentalGroups.StrictHenselian
