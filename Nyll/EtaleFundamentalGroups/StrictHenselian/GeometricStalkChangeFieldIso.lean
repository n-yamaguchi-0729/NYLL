/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkChangeField
public import Nyll.SchemeTheory.Etale.HenselianLocalGeometricLift
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Invariance of the geometric stalk under extension of a separably closed field

A point of an étale neighborhood over an extension of a separably closed field
has a unique descent to the original field. This follows from the existing
unique étale lifting theorem for a strictly local spectrum, applied to the
spectrum of the original field. Descending the points constructs an inverse
on the actual pointed étale colimits. The enlarged field need not itself be
separably closed.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω Ω' : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω] [Field Ω']
  (s : R →+* Ω) (ι : Ω →+* Ω')

/-- Points of an étale neighborhood descend uniquely along an extension of a
separably closed pointing field. -/
theorem pointedEtaleChangeField_bijective (W : (Spec (.of R)).Etale) :
    Function.Bijective (pointedEtaleChangeField s ι W) := by
  have : IsSepClosed (IsLocalRing.ResidueField Ω) := by
    let e : Ω ≃+* IsLocalRing.ResidueField Ω :=
      RingEquiv.ofBijective (IsLocalRing.residue Ω)
        ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩
    constructor
    intro p hp
    have hsplit : (p.map e.symm.toRingHom).Splits :=
      IsSepClosed.splits_of_separable _ (hp.map (f := e.symm.toRingHom))
    simpa only [Polynomial.map_map, RingEquiv.toRingHom_eq_coe,
      RingEquiv.comp_symm, Polynomial.map_id] using hsplit.map e.toRingHom
  apply (Function.bijective_iff_existsUnique (pointedEtaleChangeField s ι W)).mpr
  intro w'
  have hpoint : w'.left ≫ W.hom =
      Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom s) :=
    w'.w.trans (Spec.map_comp (CommRingCat.ofHom s) (CommRingCat.ofHom ι))
  obtain ⟨l, hl, huniq⟩ := Etale.existsUnique_lift_of_closedFieldPoint Ω W.hom
    (Spec.map (CommRingCat.ofHom s)) (Spec.map (CommRingCat.ofHom ι))
    (Subsingleton.elim _ _) w'.left hpoint
  refine ⟨Over.homMk l hl.1, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact hl.2
  · intro v hv
    apply Over.OverMorphism.ext
    apply huniq v.left
    refine ⟨v.w, ?_⟩
    exact congrArg (fun q : (Scheme.pointEtaleNeighborhoods
      (Spec.map (CommRingCat.ofHom (ι.comp s)))).fiber.obj W => q.left) hv

/-- The equivalence of actual neighborhood points under extension of a
separably closed pointing field. Its inverse is the unique descended point. -/
def pointedEtaleChangeFieldEquiv (W : (Spec (.of R)).Etale) :
    (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom s))).fiber.obj W ≃
      (Scheme.pointEtaleNeighborhoods
        (Spec.map (CommRingCat.ofHom (ι.comp s)))).fiber.obj W :=
  Equiv.ofBijective (pointedEtaleChangeField s ι W) (pointedEtaleChangeField_bijective s ι W)

/-- The descended points respect every morphism of étale neighborhoods. -/
theorem pointedEtaleChangeFieldEquiv_symm_naturality
    {W V : (Spec (.of R)).Etale} (g : W ⟶ V)
    (w : (Scheme.pointEtaleNeighborhoods
      (Spec.map (CommRingCat.ofHom (ι.comp s)))).fiber.obj W) :
    (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom s))).fiber.map g
        ((pointedEtaleChangeFieldEquiv s ι W).symm w) =
      (pointedEtaleChangeFieldEquiv s ι V).symm
        ((Scheme.pointEtaleNeighborhoods
          (Spec.map (CommRingCat.ofHom (ι.comp s)))).fiber.map g w) := by
  apply (pointedEtaleChangeFieldEquiv s ι V).injective
  change pointedEtaleChangeField s ι V
      ((Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom s))).fiber.map g
        ((pointedEtaleChangeFieldEquiv s ι W).symm w)) =
    (pointedEtaleChangeFieldEquiv s ι V)
      ((pointedEtaleChangeFieldEquiv s ι V).symm
        ((Scheme.pointEtaleNeighborhoods
          (Spec.map (CommRingCat.ofHom (ι.comp s)))).fiber.map g w))
  rw [← pointedEtaleChangeField_naturality, Equiv.apply_symm_apply]
  change (Scheme.pointEtaleNeighborhoods
      (Spec.map (CommRingCat.ofHom (ι.comp s)))).fiber.map g
        ((pointedEtaleChangeFieldEquiv s ι W)
          ((pointedEtaleChangeFieldEquiv s ι W).symm w)) = _
  rw [Equiv.apply_symm_apply]

/-- Descending the actual neighborhood points constructs the inverse map on
geometric stalks. -/
def geometricStalkChangeFieldInv :
    geometricStalk (Spec.map (CommRingCat.ofHom (ι.comp s))) ⟶
      geometricStalk (Spec.map (CommRingCat.ofHom s)) :=
  (Scheme.pointEtaleNeighborhoods
    (Spec.map (CommRingCat.ofHom (ι.comp s)))).presheafFiberDesc
    (fun W w => geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W
      ((pointedEtaleChangeFieldEquiv s ι W).symm w)) (by
      intro W V g w
      have h := (Scheme.pointEtaleNeighborhoods
        (Spec.map (CommRingCat.ofHom s))).toPresheafFiber_w
          g ((pointedEtaleChangeFieldEquiv s ι W).symm w)
          (etaleSections (Spec (.of R)))
      rw [pointedEtaleChangeFieldEquiv_symm_naturality] at h
      exact h)

/-- The inverse map on stalks replaces the pointing field of each germ by its
unique descended point. -/
theorem geometricStalkGerm_changeFieldInv (W : (Spec (.of R)).Etale)
    (w : (Scheme.pointEtaleNeighborhoods
      (Spec.map (CommRingCat.ofHom (ι.comp s)))).fiber.obj W) :
    geometricStalkGerm (Spec.map (CommRingCat.ofHom (ι.comp s))) W w ≫
        geometricStalkChangeFieldInv s ι =
      geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W
        ((pointedEtaleChangeFieldEquiv s ι W).symm w) :=
  (Scheme.pointEtaleNeighborhoods
    (Spec.map (CommRingCat.ofHom (ι.comp s)))).toPresheafFiber_presheafFiberDesc _ _ W w

/-- The original field-change map is an isomorphism, with inverse constructed
by descending all neighborhood points. -/
def geometricStalkChangeFieldIso :
    geometricStalk (Spec.map (CommRingCat.ofHom s)) ≅
      geometricStalk (Spec.map (CommRingCat.ofHom (ι.comp s))) where
  hom := geometricStalkChangeField s ι
  inv := geometricStalkChangeFieldInv s ι
  hom_inv_id := by
    apply (Scheme.pointEtaleNeighborhoods
      (Spec.map (CommRingCat.ofHom s))).presheafFiber_hom_ext
    intro W w
    change geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫
        geometricStalkChangeField s ι ≫ geometricStalkChangeFieldInv s ι =
      geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫ 𝟙 _
    rw [← Category.assoc, geometricStalkGerm_changeField,
      geometricStalkGerm_changeFieldInv, Category.comp_id]
    exact congrArg (geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W)
      ((pointedEtaleChangeFieldEquiv s ι W).symm_apply_apply w)
  inv_hom_id := by
    apply (Scheme.pointEtaleNeighborhoods
      (Spec.map (CommRingCat.ofHom (ι.comp s)))).presheafFiber_hom_ext
    intro W w
    change geometricStalkGerm (Spec.map (CommRingCat.ofHom (ι.comp s))) W w ≫
        geometricStalkChangeFieldInv s ι ≫ geometricStalkChangeField s ι =
      geometricStalkGerm (Spec.map (CommRingCat.ofHom (ι.comp s))) W w ≫ 𝟙 _
    rw [← Category.assoc, geometricStalkGerm_changeFieldInv,
      geometricStalkGerm_changeField, Category.comp_id]
    exact congrArg (geometricStalkGerm (Spec.map (CommRingCat.ofHom (ι.comp s))) W)
      ((pointedEtaleChangeFieldEquiv s ι W).apply_symm_apply w)

/-- Extension of a separably closed pointing field induces an isomorphism on
its actual geometric stalk. -/
instance geometricStalkChangeField_isIso : IsIso (geometricStalkChangeField s ι) :=
  (geometricStalkChangeFieldIso s ι).isIso_hom

end EtaleFundamentalGroups.StrictHenselian
