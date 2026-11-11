/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.FieldTheory.WittCoefficientFrobenius
import Nyll.GaloisCohomology.ArtinSchreier.WittCharacters
import Nyll.SchemeTheory.Affine.SpecSectionMap
import Nyll.GaloisCohomology.FieldTheory.CoefficientFrobenius

/-!
# Arithmetic coefficient Frobenius on the original affine scheme

The automorphism of `Spec (R ⊗[k] Ω)` is induced by the identity on `R`
and arithmetic Frobenius on the algebraic closure of the finite field `k`.
Its actual map on global sections, transported by ΓSpec, is the original
coefficient Frobenius. Consequently its difference from the identity is
surjective on global sections and at every finite Witt length.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.Cohomology

universe u

variable (k Ω R : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] [CommRing R] [Algebra k R]

/-- The actual spectrum automorphism induced by a power of arithmetic
Frobenius on the coefficient field. -/
def affineCoefficientFrobenius (n : ℕ) :
    Spec (CommRingCat.of (R ⊗[k] Ω)) ≅ Spec (CommRingCat.of (R ⊗[k] Ω)) :=
  Scheme.Spec.mapIso
    (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[k] R)
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ n)).toRingEquiv.toCommRingCatIso.op

theorem affineCoefficientFrobenius_hom (n : ℕ) :
    (affineCoefficientFrobenius k Ω R n).hom =
      Spec.map (CommRingCat.ofHom
        (FiniteField.coefficientFrobenius k Ω R n).toRingHom) := rfl

/-- The ΓSpec comparison retains the original global-section pullback. -/
theorem affineCoefficientFrobenius_appTop (n : ℕ)
    (a : Γ(Spec (CommRingCat.of (R ⊗[k] Ω)), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (R ⊗[k] Ω))).hom
        ((affineCoefficientFrobenius k Ω R n).hom.appTop a) =
      FiniteField.coefficientFrobenius k Ω R n
        ((Scheme.ΓSpecIso (CommRingCat.of (R ⊗[k] Ω))).hom a) :=
  ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
      (FiniteField.coefficientFrobenius k Ω R n).toRingHom)) a

variable [IsAlgClosed Ω]

/-- Every positive arithmetic coefficient-Frobenius difference is
surjective on the actual global sections of the scalar-extended spectrum. -/
theorem affineCoefficientFrobenius_appTop_sub_id_surjective
    (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun a : Γ(Spec (CommRingCat.of (R ⊗[k] Ω)), ⊤) =>
      (affineCoefficientFrobenius k Ω R n).hom.appTop a - a) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (R ⊗[k] Ω))).commRingCatIsoToRingEquiv
  intro a
  obtain ⟨b, hb⟩ := FiniteField.coefficientFrobenius_sub_id_surjective k Ω R n hn (e a)
  change FiniteField.coefficientFrobenius k Ω R n b - b = e a at hb
  refine ⟨e.symm b, e.injective ?_⟩
  calc
    e ((affineCoefficientFrobenius k Ω R n).hom.appTop (e.symm b) - e.symm b) =
        FiniteField.coefficientFrobenius k Ω R n (e (e.symm b)) - e (e.symm b) :=
      (map_sub e _ _).trans
        (congrArg (fun z => z - e (e.symm b))
          (affineCoefficientFrobenius_appTop k Ω R n (e.symm b)))
    _ = e a := by simpa only [e.apply_symm_apply] using hb

/-- Surjectivity holds for the actual induced endomorphism of finite Witt
vectors of global sections, at every length and every positive power. -/
theorem affineCoefficientFrobenius_witt_sub_id_surjective
    (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n ≠ 0) (m : ℕ) :
    Function.Surjective
      (fun a : TruncatedWittVector p m Γ(Spec (CommRingCat.of (R ⊗[k] Ω)), ⊤) =>
        TruncatedWittVector.map (affineCoefficientFrobenius k Ω R n).hom.appTop.hom a -
          a) := by
  intro a
  obtain ⟨b, hb⟩ := WittVector.truncate_map_sub_id_surjective
    (p := p) (affineCoefficientFrobenius k Ω R n).hom.appTop.hom
    (affineCoefficientFrobenius_appTop_sub_id_surjective k Ω R n hn) m a
  refine ⟨WittVector.truncate m b, ?_⟩
  change TruncatedWittVector.map (affineCoefficientFrobenius k Ω R n).hom.appTop.hom
      (WittVector.truncate m b) - WittVector.truncate m b = a
  rw [TruncatedWittVector.map_wittVector_truncate, ← map_sub]
  exact hb

end EtaleFundamentalGroups.Cohomology
