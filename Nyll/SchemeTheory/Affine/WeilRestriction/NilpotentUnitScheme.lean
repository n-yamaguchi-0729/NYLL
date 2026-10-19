/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.NilpotentUnitCoordinates
import Nyll.SchemeTheory.Affine.WeilRestriction.UnitNormSchemeRepresentation
import Nyll.SchemeTheory.Affine.WeilRestriction.UnitGroupScheme
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIdentity
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # The affine group scheme of the actual nilpotent unit kernel -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite Module
open scoped TensorProduct

namespace SchemeTheory.Affine.UnitNormPolynomial

open ScalarQuotientPresheaf ScalarQuotientSchemePresheaf WeilRestrictionUnits

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)

/-- The literal kernel of tensor-unit restriction as a group-valued algebra functor. -/
def tensorUnitKernelFunctor : CommAlgCat.{u} R ⥤ CommGrpCat.{u} where
  obj S := CommGrpCat.of (algebraUnitRestriction (S := S) f).ker
  map g := CommGrpCat.ofHom (tensorUnitKernelMap f g.hom)
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply Units.ext
    change Algebra.TensorProduct.map (AlgHom.id R S) (AlgHom.id R A) _ = _
    rw [Algebra.TensorProduct.map_id]
    rfl
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply Units.ext
    change Algebra.TensorProduct.map (h.hom.comp g.hom) (AlgHom.id R A) _ =
      Algebra.TensorProduct.map h.hom (AlgHom.id R A)
        (Algebra.TensorProduct.map g.hom (AlgHom.id R A) _)
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
    rfl

/-- Actual tensor units with their multiplication on all test schemes. -/
def tensorUnitGroupPresheaf (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ CommGrpCat.{u} :=
  (algΓ (CommRingCat.of R)).op ⋙
    (opOpEquivalence (CommAlgCat.{u} R)).functor ⋙
      UnitGroupScheme.tensorUnitsCommGroupFunctor R A

/-- The actual unit kernel, including on nonaffine scheme tests. -/
def tensorUnitKernelPresheaf : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ CommGrpCat.{u} :=
  (algΓ (CommRingCat.of R)).op ⋙
    (opOpEquivalence (CommAlgCat.{u} R)).functor ⋙ tensorUnitKernelFunctor f

/-- The inclusion is the original inclusion into the tensor-algebra units. -/
def tensorUnitKernelInclusion : tensorUnitKernelPresheaf f ⟶ tensorUnitGroupPresheaf R A where
  app T := CommGrpCat.ofHom (algebraUnitRestriction (S := sectionsAlgebra R T.unop) f).ker.subtype
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- Restriction remains the actual tensor-algebra unit homomorphism. -/
def tensorUnitGroupRestriction : tensorUnitGroupPresheaf R A ⟶ tensorUnitGroupPresheaf R B where
  app T := CommGrpCat.ofHom (algebraUnitRestriction (S := sectionsAlgebra R T.unop) f)
  naturality _ _ g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact algebraUnitRestriction_naturality f (sectionsMap g.unop) x

variable {ι κ : Type} [Fintype ι] [Fintype κ]
  (bA : Basis (ι ⊕ κ) R A) (bB : Basis κ R B)
  (hleft : ∀ i, f (bA (Sum.inl i)) = 0)
  (hright : ∀ j, f (bA (Sum.inr j)) = bB j)
  (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f.toRingHom))

/-- The affine space carrying the nilpotent unit kernel. -/
def nilpotentUnitKernelObject : Over (Spec (CommRingCat.of R)) :=
  (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (MvPolynomial ι R)))

/-- Polynomial maps are classified by their actual variable values. -/
def polynomialCoordinatesEquiv (S : Type u) [CommRing S] [Algebra R S] :
    (MvPolynomial ι R →ₐ[R] S) ≃ (ι → S) where
  toFun p i := p (MvPolynomial.X i)
  invFun := MvPolynomial.aeval
  left_inv p := by
    apply MvPolynomial.algHom_ext
    intro i
    exact MvPolynomial.aeval_X _ i
  right_inv x := by
    funext i
    exact MvPolynomial.aeval_X x i

/-- Polynomial coordinates classify every actual unit in the kernel. -/
def nilpotentUnitKernelHomEquiv (S : Type u) [CommRing S] [Algebra R S] :
    (MvPolynomial ι R →ₐ[R] S) ≃ (algebraUnitRestriction (S := S) f).ker :=
  (polynomialCoordinatesEquiv (R := R) (ι := ι) S).trans
    (nilpotentUnitCoordinatesEquiv bA bB f hleft hright hf hnil).symm

/-- The polynomial classification commutes with every parameter-algebra map. -/
theorem nilpotentUnitKernelHomEquiv_comp {S T : Type u} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (p : MvPolynomial ι R →ₐ[R] S) (g : S →ₐ[R] T) :
    nilpotentUnitKernelHomEquiv f bA bB hleft hright hf hnil T (g.comp p) =
      tensorUnitKernelMap f g (nilpotentUnitKernelHomEquiv f bA bB hleft hright hf hnil S p) := by
  apply (nilpotentUnitCoordinatesEquiv bA bB f hleft hright hf hnil).injective
  funext i
  rw [nilpotentUnitCoordinatesEquiv_naturality]
  change (nilpotentUnitCoordinatesEquiv bA bB f hleft hright hf hnil)
    ((nilpotentUnitCoordinatesEquiv bA bB f hleft hright hf hnil).symm
      (polynomialCoordinatesEquiv T (g.comp p))) i =
    g ((nilpotentUnitCoordinatesEquiv bA bB f hleft hright hf hnil)
      ((nilpotentUnitCoordinatesEquiv bA bB f hleft hright hf hnil).symm
        (polynomialCoordinatesEquiv S p)) i)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- The actual unit kernel is represented by affine space on arbitrary scheme tests. -/
def nilpotentUnitKernelRepresentable :
    (tensorUnitKernelPresheaf f ⋙ forget CommGrpCat).RepresentableBy
      (nilpotentUnitKernelObject (R := R) (ι := ι)) where
  homEquiv {T} :=
    (affinePointEquiv (CommAlgCat.of R (MvPolynomial ι R)) T).symm.trans
      (nilpotentUnitKernelHomEquiv f bA bB hleft hright hf hnil (sectionsAlgebra R T))
  homEquiv_comp {T T'} g p :=
    (congrArg (nilpotentUnitKernelHomEquiv f bA bB hleft hright hf hnil (sectionsAlgebra R T))
      (affinePointEquiv_symm_comp (CommAlgCat.of R (MvPolynomial ι R)) g p)).trans
        (nilpotentUnitKernelHomEquiv_comp f bA bB hleft hright hf hnil
          ((affinePointEquiv (CommAlgCat.of R (MvPolynomial ι R)) T').symm p) (sectionsMap g))

/-- The affine-space carrier with the original multiplicative law of the unit kernel. -/
def nilpotentUnitKernelGroup : CommGrp (Over (Spec (CommRingCat.of R))) :=
  RepresentedGroups.groupObject (tensorUnitKernelPresheaf f)
    (nilpotentUnitKernelRepresentable f bA bB hleft hright hf hnil)

/-- The constructed group has the actual polynomial spectrum as its carrier. -/
theorem nilpotentUnitKernelGroup_carrier :
    (nilpotentUnitKernelGroup f bA bB hleft hright hf hnil).X.left =
      Spec (CommRingCat.of (MvPolynomial ι R)) := rfl

/-- In particular, this actual nilpotent unit group is affine. -/
instance nilpotentUnitKernelGroup_isAffine :
    IsAffine (nilpotentUnitKernelGroup f bA bB hleft hright hf hnil).X.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial ι R))))

end SchemeTheory.Affine.UnitNormPolynomial
