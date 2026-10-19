/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.NilpotentIdealGroup
import Nyll.SchemeTheory.Affine.WeilRestriction.NilpotentUnitLogCoordinates
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIso

/-! # Square-zero unit kernels are actual vector groups in every characteristic -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite Module
open scoped TensorProduct

namespace SchemeTheory

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
  (hsq : RingHom.ker f ^ 2 = 0)

/-- For a square-zero ideal, subtracting one preserves the actual group law. -/
def squareZeroUnitKernelEquiv : unitKernel f ≃* Multiplicative (RingHom.ker f) where
  toEquiv := (nilpotentUnitKernelEquiv f ⟨2, hsq⟩).trans Multiplicative.ofAdd
  map_mul' u v := by
    have hn : IsNilpotent (RingHom.ker f) := ⟨2, hsq⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change (nilpotentUnitKernelEquiv f hn (u * v) : A) =
      (nilpotentUnitKernelEquiv f hn u : A) +
        (nilpotentUnitKernelEquiv f hn v : A)
    have hmul :
        (nilpotentUnitKernelEquiv f hn u : A) *
          (nilpotentUnitKernelEquiv f hn v : A) ∈ RingHom.ker f ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul
        (nilpotentUnitKernelEquiv f hn u).property
        (nilpotentUnitKernelEquiv f hn v).property
    rw [hsq] at hmul
    have hz :
        (nilpotentUnitKernelEquiv f hn u : A) *
          (nilpotentUnitKernelEquiv f hn v : A) = 0 := hmul
    apply (nilpotentUnitKernelEquiv_mul f hn u v).trans
    rw [hz, add_zero]

end SchemeTheory

namespace SchemeTheory.Affine.UnitNormPolynomial

open ScalarQuotientPresheaf ScalarQuotientSchemePresheaf AlgebraicGeometry.GroupSchemes

variable {R A B S T : Type u} [CommRing R] [CommRing A] [CommRing B]
  [CommRing S] [CommRing T] [Algebra R A] [Algebra R B] [Algebra R S] [Algebra R T]
  (f : A →ₐ[R] B) (hf : Function.Surjective f) (hsq : RingHom.ker f.toRingHom ^ 2 = 0)

include hf hsq in
/-- Square-zero kernels remain square-zero over every parameter algebra. -/
theorem tensorRestriction_ker_square_zero :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom ^ 2 = 0 := by
  have hker : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom =
      (RingHom.ker f.toRingHom).map
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom :=
    Algebra.TensorProduct.lTensor_ker f hf
  rw [hker, ← Ideal.map_pow, hsq]
  exact Ideal.map_bot

variable {m : ℕ} {κ : Type} [Fintype κ]
  (bA : Basis (Fin m ⊕ κ) R A) (bB : Basis κ R B)
  (hleft : ∀ i, f (bA (Sum.inl i)) = 0)
  (hright : ∀ j, f (bA (Sum.inr j)) = bB j)

/-- The affine coordinate classification is additive for a square-zero kernel. -/
def squareZeroUnitCoordinatesEquiv :
    (algebraUnitRestriction (S := S) f).ker ≃* Multiplicative (Fin m → S) :=
  (SchemeTheory.squareZeroUnitKernelEquiv
    (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom
    (tensorRestriction_ker_square_zero f hf hsq)).trans
      (tensorKernelCoordinatesAddEquiv bA bB f hleft hright).toMultiplicative

/-- The square-zero vector coordinates commute with coefficient restriction. -/
theorem squareZeroUnitCoordinatesEquiv_naturality (g : S →ₐ[R] T)
    (u : (algebraUnitRestriction (S := S) f).ker) :
    squareZeroUnitCoordinatesEquiv f hf hsq bA bB hleft hright (tensorUnitKernelMap f g u) =
      vectorMap m g (squareZeroUnitCoordinatesEquiv f hf hsq bA bB hleft hright u) := by
  apply Multiplicative.toAdd.injective
  funext i
  exact nilpotentUnitCoordinatesEquiv_naturality bA bB f hleft hright hf ⟨2, hsq⟩ g u i

/-- The actual square-zero kernel functor is the vector-group functor. -/
def squareZeroUnitPresheafIso : tensorUnitKernelPresheaf f ≅ vectorPresheaf R m :=
  NatIso.ofComponents
    (fun T => (squareZeroUnitCoordinatesEquiv (S := sectionsAlgebra R T.unop)
      f hf hsq bA bB hleft hright).toCommGrpIso)
    (by
      intro T T' g
      apply ConcreteCategory.hom_ext
      intro u
      exact squareZeroUnitCoordinatesEquiv_naturality f hf hsq bA bB hleft hright
        (sectionsMap g.unop) u)

/-- The actual square-zero unit group is a vector group over the original base ring. -/
def squareZeroUnitGroupIso :
    nilpotentUnitKernelGroup f bA bB hleft hright hf ⟨2, hsq⟩ ≅ vectorGroup R m :=
  RepresentedGroups.iso (tensorUnitKernelPresheaf f) (vectorPresheaf R m)
    (nilpotentUnitKernelRepresentable f bA bB hleft hright hf ⟨2, hsq⟩)
    (vectorRepresentable R m) (squareZeroUnitPresheafIso f hf hsq bA bB hleft hright)

end SchemeTheory.Affine.UnitNormPolynomial

namespace SchemeTheory.Affine.UnitNormPolynomial

open AlgebraicGeometry.GroupSchemes

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]
  (I : Ideal A) (hsq : I ^ 2 = 0)

/-- A finite square-zero ideal gives the vector group of exactly its original dimension,
in arbitrary characteristic and without a chosen splitting in the statement. -/
def squareZeroIdealGroupIso :
    nilpotentIdealGroup (K := K) I ⟨2, hsq⟩ ≅ vectorGroup K (Module.finrank K I) := by
  have hk : RingHom.ker (Ideal.Quotient.mkₐ K I).toRingHom ^ 2 = 0 := by
    change RingHom.ker (Ideal.Quotient.mk I) ^ 2 = 0
    rw [Ideal.mk_ker]
    exact hsq
  exact squareZeroUnitGroupIso (Ideal.Quotient.mkₐ K I)
    (Ideal.Quotient.mkₐ_surjective K I) hk (idealSplitBasis (K := K) I) (Module.finBasis K (A ⧸ I))
    (idealSplitBasis_left (K := K) I) (idealSplitBasis_right (K := K) I)

end SchemeTheory.Affine.UnitNormPolynomial
