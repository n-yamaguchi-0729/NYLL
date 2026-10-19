/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.NilpotentUnitCoordinates
import Nyll.SchemeTheory.GroupSchemes.VectorGroup
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # Natural exponential coordinates for the actual nilpotent unit kernel -/

noncomputable section

universe u

open Module
open scoped TensorProduct

namespace SchemeTheory

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra ℚ A]
  (f : A →+* B) (hnil : IsNilpotent (RingHom.ker f))

/-- The kernel exponential is the original finite nilpotent exponential. -/
theorem nilpotentUnitKernelExpEquiv_val (x : Multiplicative (RingHom.ker f)) :
    (((nilpotentUnitKernelExpEquiv f hnil) x).1 : A) =
      IsNilpotent.exp (Multiplicative.toAdd x).1 := rfl

end SchemeTheory

namespace SchemeTheory.Affine.UnitNormPolynomial

open ScalarQuotientPresheaf AlgebraicGeometry.GroupSchemes

variable {R A B S T : Type u} [CommRing R] [CommRing A] [CommRing B]
  [CommRing S] [CommRing T] [Algebra R A] [Algebra R B] [Algebra R S] [Algebra R T]
  {m : ℕ} {κ : Type} [Fintype κ]
  (bA : Basis (Fin m ⊕ κ) R A) (bB : Basis κ R B) (f : A →ₐ[R] B)
  (hleft : ∀ i, f (bA (Sum.inl i)) = 0)
  (hright : ∀ j, f (bA (Sum.inr j)) = bB j)

/-- The same ideal coordinates preserve the original additive group law. -/
def tensorKernelCoordinatesAddEquiv :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom ≃+ (Fin m → S) where
  toEquiv := tensorKernelCoordinatesEquiv bA bB f hleft hright
  map_add' a b := by
    funext i
    change (Algebra.TensorProduct.basis S bA).repr (a.1 + b.1) (Sum.inl i) =
      (Algebra.TensorProduct.basis S bA).repr a.1 (Sum.inl i) +
        (Algebra.TensorProduct.basis S bA).repr b.1 (Sum.inl i)
    rw [map_add]
    rfl

variable [Algebra ℚ R]

local instance parameterTensorRationalAlgebra (S : Type u) [CommRing S] [Algebra R S] :
    Algebra ℚ (S ⊗[R] A) := Algebra.compHom (S ⊗[R] A) (algebraMap ℚ R)

variable (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f.toRingHom))

/-- The finite exponential gives actual additive coordinates on every tensor-unit kernel. -/
def nilpotentUnitExpCoordinatesEquiv :
    Multiplicative (Fin m → S) ≃* (algebraUnitRestriction (S := S) f).ker :=
  (tensorKernelCoordinatesAddEquiv bA bB f hleft hright).symm.toMultiplicative.trans
    (SchemeTheory.nilpotentUnitKernelExpEquiv
      (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom
      (tensorRestriction_ker_nilpotent f hf hnil))

/-- The multiplicative coordinate map is the finite exponential in the original algebra. -/
theorem nilpotentUnitExpCoordinatesEquiv_val (x : Multiplicative (Fin m → S)) :
    ((nilpotentUnitExpCoordinatesEquiv bA bB f hleft hright hf hnil x).1 : S ⊗[R] A) =
      IsNilpotent.exp (element bA (Sum.elim (Multiplicative.toAdd x) (fun _ => 0))) := rfl

/-- Finite exponential coordinates are natural for arbitrary parameter-algebra maps. -/
theorem nilpotentUnitExpCoordinatesEquiv_naturality (g : S →ₐ[R] T)
    (x : Multiplicative (Fin m → S)) :
    nilpotentUnitExpCoordinatesEquiv bA bB f hleft hright hf hnil (vectorMap m g x) =
      tensorUnitKernelMap f g
        (nilpotentUnitExpCoordinatesEquiv bA bB f hleft hright hf hnil x) := by
  apply Subtype.ext
  apply Units.ext
  change ((nilpotentUnitExpCoordinatesEquiv bA bB f hleft hright hf hnil
      (vectorMap m g x)).1 : T ⊗[R] A) =
    Algebra.TensorProduct.map g (AlgHom.id R A)
      ((nilpotentUnitExpCoordinatesEquiv bA bB f hleft hright hf hnil x).1 : S ⊗[R] A)
  rw [nilpotentUnitExpCoordinatesEquiv_val, nilpotentUnitExpCoordinatesEquiv_val]
  have hn : IsNilpotent (element bA (Sum.elim (Multiplicative.toAdd x) (fun _ => 0))) :=
    Ideal.isNilpotent_element_of_mem (tensorRestriction_ker_nilpotent f hf hnil)
      ((tensorKernelCoordinatesEquiv bA bB f hleft hright).symm
        (Multiplicative.toAdd x)).property
  rw [IsNilpotent.map_exp hn]
  apply congrArg IsNilpotent.exp
  calc
    _ = element bA (fun j => g (Sum.elim (Multiplicative.toAdd x) (fun _ => 0) j)) := by
      apply congrArg (element bA)
      funext j
      cases j with
      | inl i => rfl
      | inr j => exact (map_zero g).symm
    _ = _ := by
      simp only [element, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

end SchemeTheory.Affine.UnitNormPolynomial
