/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ReesTensorCoefficients
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ReesTensorNaturality
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.ReesAlgebra

/-!
# Restrictions of the actual Rees tensors of a module sheaf

The structural morphism determines an ideal in every ring of sections.
Its naturality identifies the extension of this ideal along a restriction
map with the ideal on the smaller open. Polynomial restriction and the
original semilinear restriction of the module sheaf therefore give actual
restriction maps on the Rees tensors and on every ideal-power tensor.

These maps are functorial. The original tensor coefficient maps and
homogeneous insertions commute with them. No flatness or noetherian
hypothesis is imposed on the module or the scheme.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules.ReesTensor

private def idealPowerMapTo {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) (I : Ideal R) (J : Ideal S) (hIJ : I.map ρ = J) (n : ℕ) :
    ↥(I ^ n) →ₛₗ[ρ] ↥(J ^ n) where
  toFun a := ⟨ρ a.val, by
    rw [← hIJ, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem ρ a.property⟩
  map_add' a b := Subtype.ext (ρ.map_add a.val b.val)
  map_smul' a b := Subtype.ext (ρ.map_mul a b.val)

private def reesMapTo {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) (I : Ideal R) (J : Ideal S) (hIJ : I.map ρ = J) :
    ↥(reesAlgebra I) →ₛₗ[ρ] ↥(reesAlgebra J) where
  toFun p := ⟨Polynomial.map ρ p.val, fun n => by
    rw [Polynomial.coeff_map, ← hIJ, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem ρ (p.property n)⟩
  map_add' p q := Subtype.ext (Polynomial.map_add (p := p.val) (q := q.val) ρ)
  map_smul' a p := by
    apply Subtype.ext
    change Polynomial.map ρ (a • p.val) = ρ a • Polynomial.map ρ p.val
    rw [Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.smul_eq_C_mul]

private theorem coefficient_mapTo {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) (I : Ideal R) (J : Ideal S) (hIJ : I.map ρ = J)
    {P Q : Type u} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module S Q]
    (φ : P →ₛₗ[ρ] Q) (z : ↥(reesAlgebra I) ⊗[R] P) (n : ℕ) :
    ReesTensorCoefficients.coefficient J Q n
        (TensorProduct.map (reesMapTo ρ I J hIJ) φ z) =
      TensorProduct.map (idealPowerMapTo ρ I J hIJ n) φ
        (ReesTensorCoefficients.coefficient I P n z) := by
  subst J
  exact ReesTensorCoefficients.coefficient_tensorMap ρ I φ z n

private theorem mapTo_homogeneous {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) (I : Ideal R) (J : Ideal S) (hIJ : I.map ρ = J)
    {P Q : Type u} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module S Q]
    (φ : P →ₛₗ[ρ] Q) (n : ℕ) (z : ↥(I ^ n) ⊗[R] P) :
    TensorProduct.map (reesMapTo ρ I J hIJ) φ
        (ReesTensorCoefficients.homogeneous I P n z) =
      ReesTensorCoefficients.homogeneous J Q n
        (TensorProduct.map (idealPowerMapTo ρ I J hIJ n) φ z) := by
  subst J
  exact ReesTensorCoefficients.tensorMap_homogeneous ρ I φ n z

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)

/-- The extension of the original base ideal to the actual section ring. -/
def sectionsIdeal (U : X.Opens) : Ideal Γ(X, U) :=
  I.map (f.constToPresheaf.app (op U)).hom

/-- The original structural section homomorphisms commute with restriction. -/
theorem structuralMap_restriction {U W : X.Opens} (h : W ≤ U) :
    (X.presheaf.map (homOfLE h).op).hom.comp
        (f.constToPresheaf.app (op U)).hom =
      (f.constToPresheaf.app (op W)).hom := by
  apply RingHom.ext
  intro a
  exact (congrArg (fun k : CommRingCat.of A ⟶ Γ(X, W) => k a)
    (f.constToPresheaf.naturality (homOfLE h).op)).symm

/-- The actual section ideal extends to the actual section ideal on every smaller open. -/
theorem sectionsIdeal_map_restriction {U W : X.Opens} (h : W ≤ U) :
    (sectionsIdeal f I U).map (X.presheaf.map (homOfLE h).op).hom =
      sectionsIdeal f I W := by
  rw [sectionsIdeal, Ideal.map_map, structuralMap_restriction f h]
  rfl

/-- The restriction of the original ring homomorphism to an actual ideal power. -/
def idealPowerRestriction {U W : X.Opens} (h : W ≤ U) (n : ℕ) :
    ↥((sectionsIdeal f I U) ^ n) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
      ↥((sectionsIdeal f I W) ^ n) :=
  idealPowerMapTo (X.presheaf.map (homOfLE h).op).hom
    (sectionsIdeal f I U) (sectionsIdeal f I W) (sectionsIdeal_map_restriction f I h) n

/-- The original polynomial restriction on the actual Rees algebra. -/
def reesRestriction {U W : X.Opens} (h : W ≤ U) :
    ↥(reesAlgebra (sectionsIdeal f I U)) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
      ↥(reesAlgebra (sectionsIdeal f I W)) :=
  reesMapTo (X.presheaf.map (homOfLE h).op).hom
    (sectionsIdeal f I U) (sectionsIdeal f I W) (sectionsIdeal_map_restriction f I h)

/-- Restriction of a Rees section is coefficientwise polynomial restriction. -/
theorem reesRestriction_val {U W : X.Opens} (h : W ≤ U)
    (p : ↥(reesAlgebra (sectionsIdeal f I U))) :
    (reesRestriction f I h p).val =
      Polynomial.map (X.presheaf.map (homOfLE h).op).hom p.val := rfl

private theorem ringRestriction_refl (U : X.Opens) (a : Γ(X, U)) :
    X.presheaf.map (homOfLE (le_refl U)).op a = a := by
  change X.presheaf.map (𝟙 (op U)) a = a
  exact congrArg (fun k : Γ(X, U) ⟶ Γ(X, U) => k a) (X.presheaf.map_id (op U))

private theorem ringRestriction_comp {U V W : X.Opens} (h : U ≤ V) (h' : V ≤ W)
    (a : Γ(X, W)) :
    X.presheaf.map (homOfLE (h.trans h')).op a =
      X.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE h').op a) := by
  change X.presheaf.map ((homOfLE h').op ≫ (homOfLE h).op) a = _
  exact congrArg (fun k : Γ(X, W) ⟶ Γ(X, U) => k a)
    (X.presheaf.map_comp (homOfLE h').op (homOfLE h).op)

private theorem idealPowerRestriction_refl (U : X.Opens) (n : ℕ)
    (a : ↥((sectionsIdeal f I U) ^ n)) :
    idealPowerRestriction f I (le_refl U) n a = a :=
  Subtype.ext (ringRestriction_refl U a.val)

private theorem idealPowerRestriction_comp {U V W : X.Opens}
    (h : U ≤ V) (h' : V ≤ W) (n : ℕ) (a : ↥((sectionsIdeal f I W) ^ n)) :
    idealPowerRestriction f I (h.trans h') n a =
      idealPowerRestriction f I h n (idealPowerRestriction f I h' n a) :=
  Subtype.ext (ringRestriction_comp h h' a.val)

private theorem reesRestriction_refl (U : X.Opens)
    (p : ↥(reesAlgebra (sectionsIdeal f I U))) :
    reesRestriction f I (le_refl U) p = p := by
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  change (Polynomial.map (X.presheaf.map (homOfLE (le_refl U)).op).hom p.val).coeff n = _
  rw [Polynomial.coeff_map]
  exact ringRestriction_refl U (p.val.coeff n)

private theorem reesRestriction_comp {U V W : X.Opens} (h : U ≤ V) (h' : V ≤ W)
    (p : ↥(reesAlgebra (sectionsIdeal f I W))) :
    reesRestriction f I (h.trans h') p =
      reesRestriction f I h (reesRestriction f I h' p) := by
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  change (Polynomial.map (X.presheaf.map (homOfLE (h.trans h')).op).hom p.val).coeff n =
    (Polynomial.map (X.presheaf.map (homOfLE h).op).hom
      (Polynomial.map (X.presheaf.map (homOfLE h').op).hom p.val)).coeff n
  rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_map]
  exact ringRestriction_comp h h' (p.val.coeff n)

variable (M : X.Modules)

/-- The tensor of polynomial restriction with the original module restriction. -/
def reesTensorRestriction {U W : X.Opens} (h : W ≤ U) :
    ↥(reesAlgebra (sectionsIdeal f I U)) ⊗[Γ(X, U)] Γ(M, U)
      →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
    ↥(reesAlgebra (sectionsIdeal f I W)) ⊗[Γ(X, W)] Γ(M, W) :=
  TensorProduct.map (reesRestriction f I h) (M.val.restrictₛₗ (homOfLE h).op)

/-- The tensor of ideal-power restriction with the original module restriction. -/
def idealTensorRestriction {U W : X.Opens} (h : W ≤ U) (n : ℕ) :
    ↥((sectionsIdeal f I U) ^ n) ⊗[Γ(X, U)] Γ(M, U)
      →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
    ↥((sectionsIdeal f I W) ^ n) ⊗[Γ(X, W)] Γ(M, W) :=
  TensorProduct.map (idealPowerRestriction f I h n) (M.val.restrictₛₗ (homOfLE h).op)

private theorem moduleRestriction_refl (U : X.Opens) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE (le_refl U)).op x = x := by
  change M.presheaf.map (𝟙 (op U)) x = x
  exact congrArg (fun k : Γ(M, U) ⟶ Γ(M, U) => k x) (M.presheaf.map_id (op U))

private theorem moduleRestriction_comp {U V W : X.Opens} (h : U ≤ V) (h' : V ≤ W)
    (x : Γ(M, W)) :
    M.presheaf.map (homOfLE (h.trans h')).op x =
      M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE h').op x) := by
  change M.presheaf.map ((homOfLE h').op ≫ (homOfLE h).op) x = _
  exact congrArg (fun k : Γ(M, W) ⟶ Γ(M, U) => k x)
    (M.presheaf.map_comp (homOfLE h').op (homOfLE h).op)

/-- Rees tensor restriction along the identity inclusion is the identity. -/
theorem reesTensorRestriction_refl (U : X.Opens)
    (z : ↥(reesAlgebra (sectionsIdeal f I U)) ⊗[Γ(X, U)] Γ(M, U)) :
    reesTensorRestriction f I M (le_refl U) z = z := by
  induction z using TensorProduct.inductionOn with
  | tmul p x =>
      change reesRestriction f I (le_refl U) p ⊗ₜ[Γ(X, U)]
        M.presheaf.map (homOfLE (le_refl U)).op x = p ⊗ₜ[Γ(X, U)] x
      rw [reesRestriction_refl, moduleRestriction_refl]
  | add x y hx hy =>
      rw [map_add, hx, hy]

/-- Rees tensor restriction composes using the original restrictions of both factors. -/
theorem reesTensorRestriction_comp {U V W : X.Opens} (h : U ≤ V) (h' : V ≤ W)
    (z : ↥(reesAlgebra (sectionsIdeal f I W)) ⊗[Γ(X, W)] Γ(M, W)) :
    reesTensorRestriction f I M (h.trans h') z =
      reesTensorRestriction f I M h (reesTensorRestriction f I M h' z) := by
  induction z using TensorProduct.inductionOn with
  | tmul p x =>
      change reesRestriction f I (h.trans h') p ⊗ₜ[Γ(X, U)]
        M.presheaf.map (homOfLE (h.trans h')).op x =
        reesRestriction f I h (reesRestriction f I h' p) ⊗ₜ[Γ(X, U)]
          M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE h').op x)
      rw [reesRestriction_comp, moduleRestriction_comp]
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]

/-- Ideal-power tensor restriction along the identity inclusion is the identity. -/
theorem idealTensorRestriction_refl (U : X.Opens) (n : ℕ)
    (z : ↥((sectionsIdeal f I U) ^ n) ⊗[Γ(X, U)] Γ(M, U)) :
    idealTensorRestriction f I M (le_refl U) n z = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
      change idealPowerRestriction f I (le_refl U) n a ⊗ₜ[Γ(X, U)]
        M.presheaf.map (homOfLE (le_refl U)).op x = a ⊗ₜ[Γ(X, U)] x
      rw [idealPowerRestriction_refl, moduleRestriction_refl]
  | add x y hx hy =>
      rw [map_add, hx, hy]

/-- Ideal-power tensor restriction composes using the original restrictions of both factors. -/
theorem idealTensorRestriction_comp {U V W : X.Opens} (h : U ≤ V) (h' : V ≤ W) (n : ℕ)
    (z : ↥((sectionsIdeal f I W) ^ n) ⊗[Γ(X, W)] Γ(M, W)) :
    idealTensorRestriction f I M (h.trans h') n z =
      idealTensorRestriction f I M h n (idealTensorRestriction f I M h' n z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
      change idealPowerRestriction f I (h.trans h') n a ⊗ₜ[Γ(X, U)]
        M.presheaf.map (homOfLE (h.trans h')).op x =
        idealPowerRestriction f I h n (idealPowerRestriction f I h' n a) ⊗ₜ[Γ(X, U)]
          M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE h').op x)
      rw [idealPowerRestriction_comp, moduleRestriction_comp]
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]

/-- Every original tensor coefficient commutes with actual restriction. -/
theorem coefficient_restriction {U W : X.Opens} (h : W ≤ U) (n : ℕ)
    (z : ↥(reesAlgebra (sectionsIdeal f I U)) ⊗[Γ(X, U)] Γ(M, U)) :
    ReesTensorCoefficients.coefficient (sectionsIdeal f I W) Γ(M, W) n
        (reesTensorRestriction f I M h z) =
      idealTensorRestriction f I M h n
        (ReesTensorCoefficients.coefficient (sectionsIdeal f I U) Γ(M, U) n z) :=
  coefficient_mapTo (X.presheaf.map (homOfLE h).op).hom
    (sectionsIdeal f I U) (sectionsIdeal f I W) (sectionsIdeal_map_restriction f I h)
    (P := Γ(M, U)) (Q := Γ(M, W)) (M.val.restrictₛₗ (homOfLE h).op) z n

/-- Every homogeneous tensor insertion commutes with actual restriction. -/
theorem restriction_homogeneous {U W : X.Opens} (h : W ≤ U) (n : ℕ)
    (z : ↥((sectionsIdeal f I U) ^ n) ⊗[Γ(X, U)] Γ(M, U)) :
    reesTensorRestriction f I M h
        (ReesTensorCoefficients.homogeneous (sectionsIdeal f I U) Γ(M, U) n z) =
      ReesTensorCoefficients.homogeneous (sectionsIdeal f I W) Γ(M, W) n
        (idealTensorRestriction f I M h n z) :=
  mapTo_homogeneous (X.presheaf.map (homOfLE h).op).hom
    (sectionsIdeal f I U) (sectionsIdeal f I W) (sectionsIdeal_map_restriction f I h)
    (P := Γ(M, U)) (Q := Γ(M, W)) (M.val.restrictₛₗ (homOfLE h).op) n z

end AlgebraicGeometry.Scheme.Modules.ReesTensor
