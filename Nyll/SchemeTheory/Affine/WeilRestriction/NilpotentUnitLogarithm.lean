/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.NilpotentUnitLogCoordinates
import Nyll.SchemeTheory.Affine.WeilRestriction.NilpotentIdealGroup
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIso

/-! # Finite exponential and logarithm as actual isomorphisms of group schemes -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite Module

namespace SchemeTheory.Affine.UnitNormPolynomial

open AlgebraicGeometry.GroupSchemes ScalarQuotientSchemePresheaf

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra ℚ R]
  {m : ℕ} {κ : Type} [Fintype κ]
  (bA : Basis (Fin m ⊕ κ) R A) (bB : Basis κ R B) (f : A →ₐ[R] B)
  (hleft : ∀ i, f (bA (Sum.inl i)) = 0)
  (hright : ∀ j, f (bA (Sum.inr j)) = bB j)
  (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f.toRingHom))

/-- Finite exponential is a natural isomorphism of the actual group presheaves. -/
def nilpotentUnitExponentialPresheafIso :
    vectorPresheaf R m ≅ tensorUnitKernelPresheaf f :=
  NatIso.ofComponents
    (fun T => (nilpotentUnitExpCoordinatesEquiv (S := sectionsAlgebra R T.unop)
      bA bB f hleft hright hf hnil).toCommGrpIso)
    (by
      intro T T' g
      apply ConcreteCategory.hom_ext
      intro x
      exact nilpotentUnitExpCoordinatesEquiv_naturality bA bB f hleft hright hf hnil
        (sectionsMap g.unop) x)

/-- The finite exponential is an isomorphism of actual group schemes. -/
def nilpotentUnitExponential :
    vectorGroup R m ≅ nilpotentUnitKernelGroup f bA bB hleft hright hf hnil :=
  RepresentedGroups.iso (vectorPresheaf R m) (tensorUnitKernelPresheaf f)
    (vectorRepresentable R m)
    (nilpotentUnitKernelRepresentable f bA bB hleft hright hf hnil)
    (nilpotentUnitExponentialPresheafIso bA bB f hleft hright hf hnil)

/-- On every scheme test the constructed morphism is the original finite exponential. -/
theorem nilpotentUnitExponential_homEquiv {T : Over (Spec (CommRingCat.of R))}
    (x : T ⟶ (vectorGroup R m).X) :
    (nilpotentUnitKernelRepresentable f bA bB hleft hright hf hnil).homEquiv
      (x ≫ (nilpotentUnitExponential bA bB f hleft hright hf hnil).hom.hom.hom.hom) =
      nilpotentUnitExpCoordinatesEquiv bA bB f hleft hright hf hnil
        (vectorGroupPointEquiv R m T x) :=
  RepresentedGroups.mapMorphism_homEquiv _ _ _ _ _ x

end SchemeTheory.Affine.UnitNormPolynomial

namespace SchemeTheory.Affine.UnitNormPolynomial

open AlgebraicGeometry.GroupSchemes

variable {K A : Type u} [Field K] [CharZero K] [CommRing A] [Algebra K A]
  [FiniteDimensional K A] (I : Ideal A) (hI : IsNilpotent I)

/-- In characteristic zero the actual unit group of a finite nilpotent ideal is the
vector group of the original ideal dimension. No smoothness or representation is assumed. -/
def nilpotentIdealExponential :
    vectorGroup K (Module.finrank K I) ≅ nilpotentIdealGroup (K := K) I hI :=
  nilpotentUnitExponential (idealSplitBasis (K := K) I) (Module.finBasis K (A ⧸ I))
    (Ideal.Quotient.mkₐ K I) (idealSplitBasis_left (K := K) I) (idealSplitBasis_right (K := K) I)
    (Ideal.Quotient.mkₐ_surjective K I) (idealQuotient_kernel_nilpotent (K := K) I hI)

/-- The logarithm is the inverse isomorphism of the actual group schemes. -/
def nilpotentIdealLogarithm :
    nilpotentIdealGroup (K := K) I hI ≅ vectorGroup K (Module.finrank K I) :=
  (nilpotentIdealExponential (K := K) I hI).symm

end SchemeTheory.Affine.UnitNormPolynomial
