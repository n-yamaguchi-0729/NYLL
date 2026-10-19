/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientPresheaf
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Coordinate ratios for an actually split scalar-unit quotient -/

noncomputable section

universe u

open scoped TensorProduct

namespace SchemeTheory.Affine.ScalarQuotientPresheaf

variable {R A S T : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing T]
  [Algebra R A] [Algebra R S] [Algebra R T] {n : ℕ}
  (e : A ≃ₐ[R] (Fin (n + 1) → R))

/-- Tensoring an actual splitting gives the product algebra over every test algebra. -/
def splitTensorEquiv : S ⊗[R] A ≃ₐ[S] (Fin (n + 1) → S) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e).trans
    (Algebra.TensorProduct.piScalarRight R S S (Fin (n + 1)))

/-- The splitting retains the actual pure-tensor coordinates. -/
theorem splitTensorEquiv_tmul (s : S) (a : A) (i : Fin (n + 1)) :
    splitTensorEquiv e (s ⊗ₜ[R] a) i = e a i • s := by
  change Algebra.TensorProduct.piScalarRight R S S (Fin (n + 1))
    (Algebra.TensorProduct.map (AlgHom.id S S) e.toAlgHom (s ⊗ₜ[R] a)) i = _
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.piScalarRight_tmul_apply]
  rfl

/-- The actual tensor-unit splitting, with componentwise multiplication. -/
def splitTensorUnits : (S ⊗[R] A)ˣ ≃* (Fin (n + 1) → Sˣ) :=
  (Units.mapEquiv (splitTensorEquiv (S := S) e).toMulEquiv).trans
    (MulEquiv.piUnits (M := fun _ : Fin (n + 1) => S))

/-- Parameter scalar units become precisely constant tuples. -/
theorem splitTensorUnits_scalar (r : Sˣ) :
    splitTensorUnits e (scalarHom (R := R) (A := A) r) = fun _ => r := by
  funext i
  apply Units.ext
  exact congrFun ((splitTensorEquiv (S := S) e).commutes (r : S)) i

/-- Ratios against coordinate zero remove exactly the common scalar factor. -/
def splitUnitRatios : (S ⊗[R] A)ˣ →* (Fin n → Sˣ) where
  toFun a i := splitTensorUnits e a i.succ / splitTensorUnits e a 0
  map_one' := by
    funext i
    simp only [map_one, Pi.one_apply, one_div, inv_one]
  map_mul' a b := by
    funext i
    simp only [map_mul, Pi.mul_apply]
    exact mul_div_mul_comm _ _ _ _

/-- Every tuple of ratios is realized by the normalized tuple with first coordinate one. -/
theorem splitUnitRatios_surjective : Function.Surjective (splitUnitRatios (S := S) e) := by
  intro v
  refine ⟨(splitTensorUnits e).symm (Fin.cons 1 v), ?_⟩
  funext i
  change splitTensorUnits e ((splitTensorUnits e).symm (Fin.cons 1 v)) i.succ /
    splitTensorUnits e ((splitTensorUnits e).symm (Fin.cons 1 v)) 0 = v i
  rw [MulEquiv.apply_symm_apply, Fin.cons_succ, Fin.cons_zero, div_one]

/-- The kernel of actual coordinate ratios is the original parameter-scalar subgroup. -/
theorem scalarSubgroup_eq_ker_splitUnitRatios :
    scalarSubgroup (R := R) (A := A) (S := S) = (splitUnitRatios (S := S) e).ker := by
  ext a
  constructor
  · rintro ⟨r, rfl⟩
    change splitUnitRatios e (scalarHom (R := R) (A := A) r) = 1
    funext i
    change splitTensorUnits e (scalarHom (R := R) (A := A) r) i.succ /
      splitTensorUnits e (scalarHom (R := R) (A := A) r) 0 = 1
    simp only [splitTensorUnits_scalar]
    exact div_self' r
  · intro h
    change splitUnitRatios e a = 1 at h
    refine ⟨splitTensorUnits e a 0, ?_⟩
    apply (splitTensorUnits e).injective
    rw [splitTensorUnits_scalar]
    funext i
    refine Fin.cases rfl (fun k => ?_) i
    exact (div_eq_one.mp (congrFun h k)).symm

/-- The literal scalar quotient of a split algebra is an actual product of unit groups. -/
def splitScalarQuotientEquiv : ScalarQuotient (R := R) (A := A) (S := S) ≃*
    (Fin n → Sˣ) :=
  (QuotientGroup.quotientMulEquivOfEq (scalarSubgroup_eq_ker_splitUnitRatios (S := S) e)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (splitUnitRatios e)
      (splitUnitRatios_surjective e))

/-- This equivalence sends the class of each actual unit to its actual coordinate ratios. -/
theorem splitScalarQuotientEquiv_mk (a : (S ⊗[R] A)ˣ) :
    splitScalarQuotientEquiv e (QuotientGroup.mk a) = splitUnitRatios e a := rfl

/-- Tensor splitting commutes with the actual map of parameter algebras. -/
theorem splitTensorEquiv_naturality (g : S →ₐ[R] T) (a : S ⊗[R] A) (i : Fin (n + 1)) :
    splitTensorEquiv e (Algebra.TensorProduct.map g (AlgHom.id R A) a) i =
      g (splitTensorEquiv e a i) := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  | tmul s a =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        splitTensorEquiv_tmul, splitTensorEquiv_tmul]
      exact (g.toLinearMap.map_smul (e a i) s).symm

/-- The tensor-unit splitting is natural on every coordinate. -/
theorem splitTensorUnits_naturality (g : S →ₐ[R] T) (a : (S ⊗[R] A)ˣ)
    (i : Fin (n + 1)) :
    splitTensorUnits e (unitMap g a) i =
      Units.map g.toRingHom.toMonoidHom (splitTensorUnits e a i) := by
  apply Units.ext
  exact splitTensorEquiv_naturality e g (a : S ⊗[R] A) i

/-- The scalar quotient classification is natural for every map of test algebras. -/
theorem splitScalarQuotientEquiv_naturality (g : S →ₐ[R] T)
    (x : ScalarQuotient (R := R) (A := A) (S := S)) (i : Fin n) :
    splitScalarQuotientEquiv e (quotientMap g x) i =
      Units.map g.toRingHom.toMonoidHom (splitScalarQuotientEquiv e x i) := by
  refine QuotientGroup.induction_on x fun a => ?_
  change splitTensorUnits e (unitMap g a) i.succ / splitTensorUnits e (unitMap g a) 0 =
    Units.map g.toRingHom.toMonoidHom (splitTensorUnits e a i.succ / splitTensorUnits e a 0)
  rw [splitTensorUnits_naturality, splitTensorUnits_naturality, map_div]

end SchemeTheory.Affine.ScalarQuotientPresheaf
