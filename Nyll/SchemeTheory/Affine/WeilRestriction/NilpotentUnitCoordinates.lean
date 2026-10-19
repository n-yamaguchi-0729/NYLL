/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Reduced.NilpotentUnitKernel
import Nyll.SchemeTheory.Affine.WeilRestriction.UnitRestrictionGeometry
import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientRestrictionSheaf

/-! # Affine coordinates for the actual nilpotent unit kernel -/

noncomputable section

universe u

open Module
open scoped TensorProduct

namespace SchemeTheory.Affine.UnitNormPolynomial

open ScalarQuotientPresheaf

variable {R A B S T : Type u} [CommRing R] [CommRing A] [CommRing B]
  [CommRing S] [CommRing T] [Algebra R A] [Algebra R B] [Algebra R S] [Algebra R T]
  {ι κ : Type} [Fintype ι] [Fintype κ]
  (bA : Basis (ι ⊕ κ) R A) (bB : Basis κ R B) (f : A →ₐ[R] B)
  (hleft : ∀ i, f (bA (Sum.inl i)) = 0)
  (hright : ∀ j, f (bA (Sum.inr j)) = bB j)

omit [Fintype ι] [Fintype κ] in
include hleft hright in
/-- Restriction takes the target block of the actual tensor coordinates. -/
theorem restriction_coordinates [Finite ι] [Finite κ] (a : S ⊗[R] A) (j : κ) :
    coordinates bB (Algebra.TensorProduct.map (AlgHom.id R S) f a) j =
      coordinates bA a (Sum.inr j) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  calc
    _ = coordinates bB (Algebra.TensorProduct.map (AlgHom.id R S) f
        (element bA (coordinates bA a))) j :=
      congrArg (fun z => coordinates bB
        (Algebra.TensorProduct.map (AlgHom.id R S) f z) j) (element_coordinates bA a).symm
    _ = _ := by
      rw [restriction_element bA bB f hleft hright, coordinates_element]

/-- The actual tensor-algebra kernel consists exactly of the free kernel coordinates. -/
def tensorKernelCoordinatesEquiv :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom ≃ (ι → S) where
  toFun a i := coordinates bA a.1 (Sum.inl i)
  invFun x := ⟨element bA (Sum.elim x (fun _ => 0)), by
    change Algebra.TensorProduct.map (AlgHom.id R S) f
      (element bA (Sum.elim x (fun _ => 0))) = 0
    rw [restriction_element bA bB f hleft hright]
    simp only [Sum.elim_inr, element, TensorProduct.zero_tmul, Finset.sum_const_zero]⟩
  left_inv a := by
    apply Subtype.ext
    change element bA (Sum.elim (fun i => coordinates bA a.1 (Sum.inl i)) (fun _ => 0)) = a.1
    calc
      _ = element bA (coordinates bA a.1) := by
        apply congrArg (element bA)
        funext i
        cases i with
        | inl i => rfl
        | inr j =>
            have h := restriction_coordinates bA bB f hleft hright a.1 j
            have ha : Algebra.TensorProduct.map (AlgHom.id R S) f a.1 = 0 := a.property
            rw [ha] at h
            have hzero : coordinates bB (0 : S ⊗[R] B) j = 0 := by
              change (Algebra.TensorProduct.basis S bB).repr 0 j = 0
              rw [map_zero]
              rfl
            exact hzero.symm.trans h
      _ = _ := element_coordinates bA a.1
  right_inv x := by
    funext i
    exact coordinates_element bA (Sum.elim x (fun _ => 0)) (Sum.inl i)

omit [Fintype ι] [Fintype κ] in
/-- Tensor coordinates commute with changing the parameter algebra. -/
theorem coordinates_parameterMap [Finite ι] [Finite κ]
    (g : S →ₐ[R] T) (a : S ⊗[R] A) (i : ι ⊕ κ) :
    coordinates bA (Algebra.TensorProduct.map g (AlgHom.id R A) a) i =
      g (coordinates bA a i) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  have he (x : ι ⊕ κ → S) :
      Algebra.TensorProduct.map g (AlgHom.id R A) (element bA x) =
        element bA (fun j => g (x j)) := by
    simp only [element, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  calc
    _ = coordinates bA (Algebra.TensorProduct.map g (AlgHom.id R A)
        (element bA (coordinates bA a))) i :=
      congrArg (fun z => coordinates bA
        (Algebra.TensorProduct.map g (AlgHom.id R A) z) i) (element_coordinates bA a).symm
    _ = _ := by rw [he, coordinates_element]

variable (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f.toRingHom))

/-- The actual nilpotent tensor-unit kernel is the entire affine coordinate space. -/
def nilpotentUnitCoordinatesEquiv : (algebraUnitRestriction (S := S) f).ker ≃ (ι → S) :=
  (SchemeTheory.nilpotentUnitKernelEquiv
    (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom
    (tensorRestriction_ker_nilpotent f hf hnil)).trans
      (tensorKernelCoordinatesEquiv bA bB f hleft hright)

/-- Restriction on coefficients preserves the literal unit kernel as a group. -/
def tensorUnitKernelMap (g : S →ₐ[R] T) :
    (algebraUnitRestriction (S := S) f).ker →* (algebraUnitRestriction (S := T) f).ker where
  toFun u := ⟨unitMap g u.1, by
    rw [MonoidHom.mem_ker, algebraUnitRestriction_naturality, u.property, map_one]⟩
  map_one' := Subtype.ext (map_one (unitMap g))
  map_mul' u v := Subtype.ext (map_mul (unitMap g) u.1 v.1)

/-- The kernel coordinates are the original coordinates of the unit minus one. -/
theorem nilpotentUnitCoordinatesEquiv_apply
    (u : (algebraUnitRestriction (S := S) f).ker) (i : ι) :
    nilpotentUnitCoordinatesEquiv bA bB f hleft hright hf hnil u i =
      coordinates bA ((u.1 : S ⊗[R] A) - 1) (Sum.inl i) := rfl

/-- The actual affine coordinate classification is natural on every parameter algebra. -/
theorem nilpotentUnitCoordinatesEquiv_naturality (g : S →ₐ[R] T)
    (u : (algebraUnitRestriction (S := S) f).ker) (i : ι) :
    nilpotentUnitCoordinatesEquiv bA bB f hleft hright hf hnil (tensorUnitKernelMap f g u) i =
      g (nilpotentUnitCoordinatesEquiv bA bB f hleft hright hf hnil u i) := by
  change coordinates bA
      ((Algebra.TensorProduct.map g (AlgHom.id R A)) (u.1 : S ⊗[R] A) - 1) (Sum.inl i) = _
  rw [← map_one (Algebra.TensorProduct.map g (AlgHom.id R A)), ← map_sub]
  exact coordinates_parameterMap bA g ((u.1 : S ⊗[R] A) - 1) (Sum.inl i)

end SchemeTheory.Affine.UnitNormPolynomial
