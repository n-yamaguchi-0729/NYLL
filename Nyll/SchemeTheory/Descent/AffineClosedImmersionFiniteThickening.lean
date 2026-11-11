/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.FinitePresentation.FiniteSubidealSurjectivity
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Finite closed thickenings preserving an affine closed immersion

If a closed subscheme of an affine scheme maps as a closed immersion to
another affine scheme, finitely many equations already give a thickening
with the same closed-immersion property. The original source and both
ambient schemes are retained through their canonical affine comparisons.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ClosedImmersionApproximation

/-- A finite-type morphism between affine schemes that is a closed
immersion on an actual closed subscheme is a closed immersion on an
actual finitely presented closed thickening of that subscheme. -/
theorem exists_affine_finitePresentation_thickening
    {Z X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsClosedImmersion (i ≫ f)] :
    ∃ (C : Scheme.{u}) (c : C ⟶ X) (a : Z ⟶ C),
      IsClosedImmersion c ∧ LocallyOfFinitePresentation c ∧
      IsClosedImmersion (c ≫ f) ∧ a ≫ c = i := by
  have : IsAffine Z := isAffine_of_isAffineHom i
  let R := Γ(Y, ⊤)
  let S := Γ(X, ⊤)
  let α : R →+* S := f.appTop.hom
  let β : S →+* Γ(Z, ⊤) := i.appTop.hom
  let : Algebra R S := α.toAlgebra
  have : Algebra.FiniteType R S :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance
  have hβ : Function.Surjective (β.comp α) :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (i ≫ f)).2
  let I : Ideal S := RingHom.ker β
  have hquot : Function.Surjective (algebraMap R (S ⧸ I)) := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := hβ (β s)
    refine ⟨r, ?_⟩
    apply RingHom.kerLift_injective β
    exact hr
  obtain ⟨J, hJI, hJfg, hJsurj⟩ := Algebra.exists_fg_subideal_surjective_quotient I hquot
  let φ : S ⧸ J →+* Γ(Z, ⊤) :=
    Ideal.Quotient.lift J β (fun s hs => hJI hs)
  let c : Spec (CommRingCat.of (S ⧸ J)) ⟶ X :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ X.isoSpec.inv
  let a : Z ⟶ Spec (CommRingCat.of (S ⧸ J)) :=
    Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ)
  have : IsClosedImmersion c := inferInstance
  have hqfp : (Ideal.Quotient.mk J).FinitePresentation := by
    apply RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker]
    exact hJfg
  have : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr hqfp
  have : LocallyOfFinitePresentation c := inferInstance
  have hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp α) := hJsurj
  have hclosed : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp α))) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  have hcf : c ≫ f =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp α)) ≫ Y.isoSpec.inv := by
    change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ X.isoSpec.inv) ≫ f = _
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality f,
      ← Category.assoc, ← Spec.map_comp]
    rfl
  have : IsClosedImmersion (c ≫ f) :=
    hcf.symm ▸ (inferInstanceAs (IsClosedImmersion
      (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp α)) ≫ Y.isoSpec.inv)))
  have hφ : CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ CommRingCat.ofHom φ = i.appTop := by
    ext s
    rfl
  refine ⟨_, c, a, inferInstance, inferInstance, inferInstance, ?_⟩
  change (Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ)) ≫
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ X.isoSpec.inv) = i
  rw [Category.assoc, ← Spec.map_comp_assoc, hφ,
    Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.ClosedImmersionApproximation
