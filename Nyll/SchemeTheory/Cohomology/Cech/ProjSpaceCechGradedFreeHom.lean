/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Maps from shifted free graded modules

The commuting coordinate operators give an actual polynomial action with
values in the native endomorphism algebra. A homogeneous element therefore
defines a graded homomorphism from the corresponding shifted free module.
Finite families give a homomorphism from their finite free presentation,
and every homomorphism from such a presentation is recovered from these
actual generator images.

These constructions allow homogeneous generators at the first stage of
an adic system to be lifted before finite generation of its limit is known.
No module structure over the polynomial ring is added to the target type.
-/

noncomputable section

namespace ProjSpaceCech.GradedModule

universe u

open MvPolynomial

variable {R : Type u} [CommRing R] {n : ℕ}

/-- Monomials act by the original commuting coordinate operators. -/
def monomialAction (D : GradedModule R n) :
    Multiplicative (Fin (n + 1) →₀ ℕ) →* Module.End R D.M where
  toFun a := monMul D (fun j => a.toAdd j)
  map_one' := monMul_zero D
  map_mul' a b := monMul_add D (fun j => a.toAdd j) (fun j => b.toAdd j)

/-- The polynomial action as a map to the existing endomorphism algebra. -/
def polynomialAction (D : GradedModule R n) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] Module.End R D.M :=
  AddMonoidAlgebra.lift R (Module.End R D.M) (Fin (n + 1) →₀ ℕ) (monomialAction D)

/-- Monomials act by their prescribed exponents and coefficient. -/
theorem polynomialAction_monomial (D : GradedModule R n)
    (a : Fin (n + 1) →₀ ℕ) (r : R) :
    polynomialAction D (monomial a r) = r • monMul D (fun j => a j) :=
  AddMonoidAlgebra.lift_single (monomialAction D) a r

/-- The action of a coordinate is the originally supplied degree-one operator. -/
theorem polynomialAction_X (D : GradedModule R n) (j : Fin (n + 1)) :
    polynomialAction D (X j) = D.xMul j := by
  change polynomialAction D (monomial (Finsupp.single j 1) 1) = D.xMul j
  rw [polynomialAction_monomial, one_smul, Finsupp.single_eq_pi_single,
    monMul_single, pow_one]

/-- The linear map obtained by applying polynomials to one specified element. -/
def freeLinear (D : GradedModule R n) (v : D.M) :
    MvPolynomial (Fin (n + 1)) R →ₗ[R] D.M where
  toFun p := polynomialAction D p v
  map_add' p q := by
    rw [map_add, LinearMap.add_apply]
  map_smul' r p := by
    rw [map_smul, LinearMap.smul_apply]
    rfl

/-- Evaluation of a monomial in the constructed linear map. -/
theorem freeLinear_monomial (D : GradedModule R n) (v : D.M)
    (a : Fin (n + 1) →₀ ℕ) (r : R) :
    freeLinear D v (monomial a r) = r • monMul D (fun j => a j) v := by
  change polynomialAction D (monomial a r) v = _
  rw [polynomialAction_monomial, LinearMap.smul_apply]

/-- The constant polynomial one recovers the original element. -/
theorem freeLinear_one (D : GradedModule R n) (v : D.M) : freeLinear D v 1 = v := by
  change polynomialAction D 1 v = v
  rw [map_one, Module.End.one_apply]

/-- Multiplication by a coordinate is intertwined with its original operator. -/
theorem freeLinear_X_mul (D : GradedModule R n) (v : D.M)
    (j : Fin (n + 1)) (p : MvPolynomial (Fin (n + 1)) R) :
    freeLinear D v (X j * p) = D.xMul j (freeLinear D v p) := by
  change polynomialAction D (X j * p) v = D.xMul j (polynomialAction D p v)
  rw [map_mul, polynomialAction_X, Module.End.mul_apply]

/-- A homogeneous polynomial shifts the degree by its actual homogeneous degree. -/
theorem freeLinear_mem_grade (D : GradedModule R n) {e d : ℤ}
    (v : D.M) (hv : v ∈ D.grade e)
    (p : MvPolynomial (Fin (n + 1)) R) (hp : p ∈ freeGrade R n d) :
    freeLinear D v p ∈ D.grade (e + d) := by
  classical
  by_cases hd : 0 ≤ d
  · rw [freeGrade_of_nonneg R n hd] at hp
    rw [p.as_sum, map_sum]
    apply Submodule.sum_mem
    intro a ha
    rw [freeLinear_monomial]
    have hdeg : a.degree = d.toNat :=
      (Finsupp.degree_apply a).trans (hp.degree_eq_sum_deg_support ha).symm
    have hsum : (∑ j, (a j : ℤ)) = d := by
      rw [← Nat.cast_sum, ← Finsupp.degree_eq_sum, hdeg, Int.toNat_of_nonneg hd]
    have hm := monMul_mem_grade D (fun j => a j) e v hv
    rw [hsum] at hm
    exact Submodule.smul_mem _ (p.coeff a) hm
  · rw [freeGrade, ite_eq_right hd] at hp
    have hp0 : p = 0 := hp
    rw [hp0, map_zero]
    exact Submodule.zero_mem _

/-- A chosen homogeneous generator defines a map from its shifted free module. -/
def fromHomogeneous (D : GradedModule R n) (δ : ℤ)
    (v : D.M) (hv : v ∈ D.grade (-δ)) : Hom (FD R n δ) D where
  toLinearMap := freeLinear D v
  mem_grade d p hp := by
    have h := freeLinear_mem_grade D v hv p hp
    rw [show -δ + (d + δ) = d by omega] at h
    exact h
  xMul_comm j := by
    apply LinearMap.ext
    intro p
    exact freeLinear_X_mul D v j p

/-- Graded maps preserve the constructed polynomial evaluation. -/
theorem Hom.map_freeLinear {D E : GradedModule R n} (φ : Hom D E) (v : D.M) :
    φ.toLinearMap.comp (freeLinear D v) = freeLinear E (φ.toLinearMap v) := by
  apply MvPolynomial.linearMap_ext
  intro a
  apply LinearMap.ext
  intro r
  change φ.toLinearMap (freeLinear D v (monomial a r)) =
    freeLinear E (φ.toLinearMap v) (monomial a r)
  rw [freeLinear_monomial, map_smul, Hom.map_monMul, freeLinear_monomial]

/-- On the shifted free module, the polynomial action is ordinary multiplication. -/
theorem polynomialAction_FD (δ : ℤ) :
    polynomialAction (FD R n δ) = Algebra.lmul R (MvPolynomial (Fin (n + 1)) R) := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [polynomialAction_X]
  apply LinearMap.ext
  intro p
  rfl

/-- Evaluation at one on a shifted free source is the original polynomial. -/
theorem freeLinear_FD_one (δ : ℤ) (p : MvPolynomial (Fin (n + 1)) R) :
    freeLinear (FD R n δ) (1 : MvPolynomial (Fin (n + 1)) R) p = p := by
  change polynomialAction (FD R n δ) p (1 : MvPolynomial (Fin (n + 1)) R) = p
  rw [polynomialAction_FD]
  exact mul_one p

/-- A graded map from a shifted free module is determined by the image of one. -/
theorem Hom.fromFree_apply {D : GradedModule R n} {δ : ℤ}
    (φ : Hom (FD R n δ) D) (p : MvPolynomial (Fin (n + 1)) R) :
    φ.toLinearMap p =
      freeLinear D (φ.toLinearMap (1 : MvPolynomial (Fin (n + 1)) R)) p := by
  have h := LinearMap.congr_fun
    (φ.map_freeLinear (1 : MvPolynomial (Fin (n + 1)) R)) p
  change φ.toLinearMap
    (freeLinear (FD R n δ) (1 : MvPolynomial (Fin (n + 1)) R) p) = _ at h
  rw [freeLinear_FD_one] at h
  exact h

section Family

variable {J : Type} [Fintype J] (δ : J → ℤ)

/-- The actual inclusion of one shifted free summand into the finite source. -/
def freeSummandInclusion [DecidableEq J] (j : J) :
    Hom (FD R n (δ j)) (pi (fun k => FD R n (δ k))) where
  toLinearMap := LinearMap.single R (fun k : J => (FD R n (δ k)).M) j
  mem_grade d p hp := by
    intro k _
    change (Pi.single j p : ∀ k : J, (FD R n (δ k)).M) k ∈ (FD R n (δ k)).grade d
    by_cases h : j = k
    · subst k
      simpa only [Pi.single_eq_same] using hp
    · rw [Pi.single_eq_of_ne (Ne.symm h)]
      exact Submodule.zero_mem _
  xMul_comm i := by
    apply LinearMap.ext
    intro p
    funext k
    change (Pi.single j ((FD R n (δ j)).xMul i p) : ∀ k : J, (FD R n (δ k)).M) k =
      (FD R n (δ k)).xMul i ((Pi.single j p : ∀ k : J, (FD R n (δ k)).M) k)
    by_cases h : j = k
    · subst k
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne (Ne.symm h), map_zero]

/-- Polynomial coefficient families act on the given finite family of elements. -/
def freeFamilyLinear (D : GradedModule R n) (v : J → D.M) :
    (J → MvPolynomial (Fin (n + 1)) R) →ₗ[R] D.M where
  toFun p := ∑ j : J, freeLinear D (v j) (p j)
  map_add' p q := by
    change (∑ j : J, freeLinear D (v j) (p j + q j)) = _
    simp only [map_add, Finset.sum_add_distrib]
  map_smul' r p := by
    change (∑ j : J, freeLinear D (v j) (r • p j)) =
      r • (∑ j : J, freeLinear D (v j) (p j))
    simp only [map_smul, Finset.smul_sum]

/-- Coordinate multiplication commutes with the actual polynomial family map. -/
theorem freeFamilyLinear_X_mul (D : GradedModule R n) (v : J → D.M)
    (i : Fin (n + 1)) (p : J → MvPolynomial (Fin (n + 1)) R) :
    freeFamilyLinear D v (fun j => X i * p j) = D.xMul i (freeFamilyLinear D v p) := by
  change (∑ j : J, freeLinear D (v j) (X i * p j)) =
    D.xMul i (∑ j : J, freeLinear D (v j) (p j))
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => freeLinear_X_mul D (v j) i (p j)

/-- Finite homogeneous generators give an actual homomorphism of graded modules. -/
def fromHomogeneousFamily (D : GradedModule R n)
    (v : J → D.M) (hv : ∀ j, v j ∈ D.grade (-δ j)) :
    Hom (pi (fun j => FD R n (δ j))) D where
  toLinearMap := freeFamilyLinear D v
  mem_grade d p hp := by
    change (∑ j : J, freeLinear D (v j) (p j)) ∈ D.grade d
    apply Submodule.sum_mem
    intro j _
    exact (fromHomogeneous D (δ j) (v j) (hv j)).mem_grade d (p j)
      (hp j (Set.mem_univ j))
  xMul_comm i := by
    apply LinearMap.ext
    intro p
    exact freeFamilyLinear_X_mul D v i p

/-- The resulting homomorphism evaluates the actual polynomial coefficients
at the chosen homogeneous generators. -/
theorem fromHomogeneousFamily_apply (D : GradedModule R n)
    (v : J → D.M) (hv : ∀ j, v j ∈ D.grade (-δ j))
    (p : (pi (fun j => FD R n (δ j))).M) :
    (fromHomogeneousFamily δ D v hv).toLinearMap p =
      ∑ j : J, freeLinear D (v j) (p j) := rfl

/-- Every map from a finite shifted free source is recovered from its
actual generator images. -/
theorem Hom.fromFamily_apply [DecidableEq J] {D : GradedModule R n}
    (φ : Hom (pi (fun j => FD R n (δ j))) D)
    (p : (pi (fun j => FD R n (δ j))).M) :
    φ.toLinearMap p = ∑ j : J,
      freeLinear D (φ.toLinearMap
        (Pi.single j (1 : MvPolynomial (Fin (n + 1)) R))) (p j) := by
  have hsum : (∑ j : J, Pi.single j (p j)) = p := Finset.univ_sum_single p
  calc
    φ.toLinearMap p = φ.toLinearMap (∑ j : J, Pi.single j (p j)) :=
      congrArg φ.toLinearMap hsum.symm
    _ = ∑ j : J, φ.toLinearMap (Pi.single j (p j)) := map_sum _ _ _
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro j _
  let ι := freeSummandInclusion (R := R) (n := n) δ j
  let ψ : Hom (FD R n (δ j)) D :=
    { toLinearMap := φ.toLinearMap.comp ι.toLinearMap
      mem_grade := fun d q hq => φ.mem_grade d _ (ι.mem_grade d q hq)
      xMul_comm := fun k => by
        rw [LinearMap.comp_assoc, ι.xMul_comm, ← LinearMap.comp_assoc,
          φ.xMul_comm, LinearMap.comp_assoc] }
  exact ψ.fromFree_apply (p j)

end Family

end ProjSpaceCech.GradedModule
