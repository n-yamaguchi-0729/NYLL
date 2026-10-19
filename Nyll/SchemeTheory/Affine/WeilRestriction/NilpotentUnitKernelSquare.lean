/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.NilpotentUnitScheme
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # The affine nilpotent-unit group is the actual restriction kernel -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Module
open scoped CategoryTheory.MonObj

namespace SchemeTheory.Affine.UnitNormPolynomial

open ScalarQuotientPresheaf ScalarQuotientSchemePresheaf

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  {ν κ : Type} [Fintype ν] [DecidableEq ν] [Fintype κ] [DecidableEq κ]

/-- The norm representation with its actual group-valued tensor-unit functor. -/
def normTensorUnitRepresentable (b : Basis ν R A) :
    (tensorUnitGroupPresheaf R A ⋙ forget CommGrpCat).RepresentableBy
      (normRepresentingObject b) where
  homEquiv := (normSchemeRepresentable b).homEquiv
  homEquiv_comp g p := (normSchemeRepresentable b).homEquiv_comp g p

/-- The norm open with its original multiplication of tensor-algebra units. -/
def normTensorUnitGroup (b : Basis ν R A) : CommGrp (Over (Spec (CommRingCat.of R))) :=
  RepresentedGroups.groupObject (tensorUnitGroupPresheaf R A) (normTensorUnitRepresentable b)

variable (f : A →ₐ[R] B) (bA : Basis (ν ⊕ κ) R A) (bB : Basis κ R B)

/-- The morphism of the actual represented tensor-unit groups. -/
def normTensorUnitRestriction : normTensorUnitGroup bA ⟶ normTensorUnitGroup bB :=
  RepresentedGroups.map (tensorUnitGroupPresheaf R A) (tensorUnitGroupPresheaf R B)
    (normTensorUnitRepresentable bA) (normTensorUnitRepresentable bB)
      (tensorUnitGroupRestriction f)

/-- The represented restriction retains the actual tensor-unit classification. -/
theorem normTensorUnitRestriction_homEquiv
    {T : Over (Spec (CommRingCat.of R))} (g : T ⟶ (normTensorUnitGroup bA).X) :
    (normTensorUnitRepresentable bB).homEquiv
      (g ≫ (normTensorUnitRestriction f bA bB).hom.hom.hom) =
      algebraUnitRestriction f ((normTensorUnitRepresentable bA).homEquiv g) :=
  RepresentedGroups.mapMorphism_homEquiv _ _ _ _ _ g

/-- The group morphism is the original restriction map of concrete norm opens. -/
theorem normTensorUnitRestriction_eq :
    (normTensorUnitRestriction f bA bB).hom.hom.hom = restrictionOver bA bB f := by
  apply (normTensorUnitRepresentable bB).homEquiv.injective
  have h := RepresentedGroups.mapMorphism_homEquiv
    (tensorUnitGroupPresheaf R A) (tensorUnitGroupPresheaf R B)
    (normTensorUnitRepresentable bA) (normTensorUnitRepresentable bB)
    (tensorUnitGroupRestriction f) (𝟙 (normRepresentingObject bA))
  rw [Category.id_comp] at h
  apply h.trans
  change algebraUnitRestriction f
    ((normSchemeRepresentable bA).homEquiv (𝟙 (normRepresentingObject bA))) =
      (normSchemeRepresentable bB).homEquiv (restrictionOver bA bB f)
  exact (normSchemeRepresentable_restriction bA bB f
    (𝟙 (normRepresentingObject bA))).symm.trans
      (congrArg (normSchemeRepresentable bB).homEquiv (Category.id_comp _))

variable (hleft : ∀ i, f (bA (Sum.inl i)) = 0)
  (hright : ∀ j, f (bA (Sum.inr j)) = bB j)
  (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f.toRingHom))

/-- The inclusion of the affine nilpotent-unit group into the actual norm-unit group. -/
def nilpotentUnitKernelInclusion :
    nilpotentUnitKernelGroup f bA bB hleft hright hf hnil ⟶ normTensorUnitGroup bA :=
  RepresentedGroups.map (tensorUnitKernelPresheaf f) (tensorUnitGroupPresheaf R A)
    (nilpotentUnitKernelRepresentable f bA bB hleft hright hf hnil)
    (normTensorUnitRepresentable bA) (tensorUnitKernelInclusion f)

/-- The inclusion on scheme points is literally the inclusion of the original unit kernel. -/
theorem nilpotentUnitKernelInclusion_homEquiv
    {T : Over (Spec (CommRingCat.of R))}
    (g : T ⟶ (nilpotentUnitKernelGroup f bA bB hleft hright hf hnil).X) :
    (normTensorUnitRepresentable bA).homEquiv
      (g ≫ (nilpotentUnitKernelInclusion f bA bB hleft hright hf hnil).hom.hom.hom) =
      ((nilpotentUnitKernelRepresentable f bA bB hleft hright hf hnil).homEquiv g).1 :=
  RepresentedGroups.mapMorphism_homEquiv _ _ _ _ _ g

/-- Every actual point of the affine kernel restricts to the identity. -/
theorem nilpotentUnitKernelInclusion_comp_point
    {T : Over (Spec (CommRingCat.of R))}
    (g : T ⟶ (nilpotentUnitKernelGroup f bA bB hleft hright hf hnil).X) :
    (g ≫ (nilpotentUnitKernelInclusion f bA bB hleft hright hf hnil).hom.hom.hom) ≫
      (normTensorUnitRestriction f bA bB).hom.hom.hom = 1 := by
  apply (normTensorUnitRepresentable bB).homEquiv.injective
  exact (normTensorUnitRestriction_homEquiv f bA bB
    (g ≫ (nilpotentUnitKernelInclusion f bA bB hleft hright hf hnil).hom.hom.hom)).trans
      ((congrArg (algebraUnitRestriction f)
        (nilpotentUnitKernelInclusion_homEquiv f bA bB hleft hright hf hnil g)).trans
        (((nilpotentUnitKernelRepresentable f bA bB hleft hright hf hnil).homEquiv g).property
          |>.trans (RepresentedGroups.homEquiv_one
            (tensorUnitGroupPresheaf R B) (normTensorUnitRepresentable bB) T).symm))

/-- The inclusion followed by actual restriction is the identity section. -/
theorem nilpotentUnitKernelInclusion_condition :
    (nilpotentUnitKernelInclusion f bA bB hleft hright hf hnil).hom.hom.hom ≫
      (normTensorUnitRestriction f bA bB).hom.hom.hom = 1 := by
  simpa only [Category.id_comp] using nilpotentUnitKernelInclusion_comp_point
    f bA bB hleft hright hf hnil (𝟙 _)

/-- The affine-space group satisfies the universal property of the actual identity kernel. -/
def nilpotentUnitKernelIsLimit :
    IsLimit (Fork.ofι
      (nilpotentUnitKernelInclusion f bA bB hleft hright hf hnil).hom.hom.hom
      ((nilpotentUnitKernelInclusion_condition f bA bB hleft hright hf hnil).trans
        (MonObj.comp_one
          (nilpotentUnitKernelInclusion f bA bB hleft hright hf hnil).hom.hom.hom).symm)) := by
  apply Fork.IsLimit.ofExistsUnique
  intro s
  have hs : s.ι ≫ (normTensorUnitRestriction f bA bB).hom.hom.hom = 1 :=
    s.condition.trans (MonObj.comp_one s.ι)
  have hk : algebraUnitRestriction f ((normTensorUnitRepresentable bA).homEquiv s.ι) = 1 := by
    exact (normTensorUnitRestriction_homEquiv f bA bB s.ι).symm.trans
      ((congrArg (normTensorUnitRepresentable bB).homEquiv hs).trans
        (RepresentedGroups.homEquiv_one
          (tensorUnitGroupPresheaf R B) (normTensorUnitRepresentable bB) s.pt))
  let x : (algebraUnitRestriction (S := sectionsAlgebra R s.pt) f).ker :=
    ⟨(normTensorUnitRepresentable bA).homEquiv s.ι, hk⟩
  let p : s.pt ⟶ (nilpotentUnitKernelGroup f bA bB hleft hright hf hnil).X :=
    (nilpotentUnitKernelRepresentable f bA bB hleft hright hf hnil).homEquiv.symm x
  have hp : p ≫
      (nilpotentUnitKernelInclusion f bA bB hleft hright hf hnil).hom.hom.hom = s.ι := by
    apply (normTensorUnitRepresentable bA).homEquiv.injective
    exact (nilpotentUnitKernelInclusion_homEquiv f bA bB hleft hright hf hnil p).trans
      (congrArg Subtype.val
        ((nilpotentUnitKernelRepresentable f bA bB hleft hright hf hnil).homEquiv
          |>.apply_symm_apply x))
  refine ⟨p, hp, ?_⟩
  intro q hq
  apply (nilpotentUnitKernelRepresentable f bA bB hleft hright hf hnil).homEquiv.injective
  apply Subtype.ext
  exact (nilpotentUnitKernelInclusion_homEquiv f bA bB hleft hright hf hnil q).symm.trans
    ((congrArg (normTensorUnitRepresentable bA).homEquiv (hq.trans hp.symm)).trans
      (nilpotentUnitKernelInclusion_homEquiv f bA bB hleft hright hf hnil p))

end SchemeTheory.Affine.UnitNormPolynomial
