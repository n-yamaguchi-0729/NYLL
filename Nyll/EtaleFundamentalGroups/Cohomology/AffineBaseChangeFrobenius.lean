/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.CoefficientBaseChangeIso
public import Nyll.SchemeTheory.Affine.SpecFlatBaseChangeSections
public import Nyll.GaloisCohomology.FieldTheory.WittCoefficientFrobenius
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacters
public import Nyll.GaloisCohomology.FieldTheory.CoefficientFrobenius

/-!
# Coefficient Frobenius on the original geometric base change

The existing flat base-change comparison and the literal pullback symmetry
identify sections of `Spec Ω ×[Spec k] X` with `Γ(X) ⊗[k] Ω`. Both original
projections are retained. Under this comparison the actual coefficient
automorphism acts on the second tensor factor. Positive Frobenius differences
are therefore surjective on these sections and on all finite Witt lengths.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.FiniteEtale
open scoped TensorProduct

namespace EtaleFundamentalGroups.Cohomology

universe u

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [QuasiCompact f] [QuasiSeparated f]

/-- The original base-change section equivalence in the order used by the
native coefficient action, with the source section algebra explicitly fixed. -/
def coefficientBaseChangeSectionsTensorEquiv :
    let _ : Algebra k Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom.toAlgebra
    Γ(X, ⊤) ⊗[k] Ω ≃+*
      Γ(pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f, ⊤) := by
  intro hX
  let b := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let _ : Algebra Ω Γ(pullback f b, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ (pullback.snd f b).appTop).hom.toAlgebra
  exact (Algebra.TensorProduct.comm k Γ(X, ⊤) Ω).toRingEquiv.trans
    ((specPullbackSectionsTensorEquiv (A := Ω) f).toRingEquiv.trans
      (Scheme.Γ.mapIso (pullbackSymmetry b f).op).commRingCatIsoToRingEquiv)

/-- A pure tensor maps to the product of the original coefficient and
scheme section pullbacks. -/
theorem coefficientBaseChangeSectionsTensorEquiv_tmul
    (r : Γ(X, ⊤)) (a : Ω) :
    let _ : Algebra k Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom.toAlgebra
    coefficientBaseChangeSectionsTensorEquiv k Ω f (r ⊗ₜ[k] a) =
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv a) *
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f).appTop r := by
  intro hX
  let b := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let _ : Algebra Ω Γ(pullback f b, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ (pullback.snd f b).appTop).hom.toAlgebra
  let E := specPullbackSectionsTensorEquiv (A := Ω) f
  let s := pullbackSymmetry b f
  have hleft : E (a ⊗ₜ[k] (1 : Γ(X, ⊤))) =
      (pullback.snd f b).appTop ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv a) :=
    E.commutes a
  have hright : E ((1 : Ω) ⊗ₜ[k] r) = (pullback.fst f b).appTop r :=
    specPullbackSectionsTensorEquiv_one_tmul (A := Ω) f r
  have hfst : s.hom.appTop ((pullback.fst f b).appTop r) =
      (pullback.snd b f).appTop r :=
    (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop s.hom (pullback.fst f b)) r).symm.trans
      (congrArg (fun g : pullback b f ⟶ X => g.appTop r)
        (pullbackSymmetry_hom_comp_fst b f))
  have hsnd : s.hom.appTop
      ((pullback.snd f b).appTop ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv a)) =
        (pullback.fst b f).appTop ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv a) :=
    (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop s.hom (pullback.snd f b))
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv a)).symm.trans
        (congrArg (fun g : pullback b f ⟶ Spec (CommRingCat.of Ω) =>
          g.appTop ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv a))
            (pullbackSymmetry_hom_comp_snd b f))
  change s.hom.appTop (E (a ⊗ₜ[k] r)) = _
  rw [show a ⊗ₜ[k] r = (a ⊗ₜ[k] (1 : Γ(X, ⊤))) * ((1 : Ω) ⊗ₜ[k] r) by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
  rw [map_mul, hleft, hright, map_mul, hsnd, hfst]

/-- The actual coefficient automorphism acts on the original coefficient
factor of the global-section tensor comparison. -/
theorem coefficientBaseChangeSectionsTensorEquiv_action (σ : Ω ≃ₐ[k] Ω) :
    let _ : Algebra k Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom.toAlgebra
    ∀ z : Γ(X, ⊤) ⊗[k] Ω,
      (coefficientBaseChangeIso k Ω f σ).hom.appTop
          (coefficientBaseChangeSectionsTensorEquiv k Ω f z) =
        coefficientBaseChangeSectionsTensorEquiv k Ω f
          (Algebra.TensorProduct.map (AlgHom.id k Γ(X, ⊤)) σ.toAlgHom z) := by
  intro hX z
  let b := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let θ := coefficientBaseChangeIso k Ω f σ
  let E := coefficientBaseChangeSectionsTensorEquiv k Ω f
  have hscheme (r : Γ(X, ⊤)) : θ.hom.appTop ((pullback.snd b f).appTop r) =
      (pullback.snd b f).appTop r :=
    (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop θ.hom (pullback.snd b f)) r).symm.trans
      (congrArg (fun g : pullback b f ⟶ X => g.appTop r)
        (coefficientBaseChangeIso_hom_snd k Ω f σ))
  have hcoeff (a : Ω) : θ.hom.appTop
      ((pullback.fst b f).appTop ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv a)) =
        (pullback.fst b f).appTop ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv (σ a)) := by
    have hs := (ConcreteCategory.congr_hom
      (Scheme.Hom.comp_appTop θ.hom (pullback.fst b f))
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv a)).symm
    have ht := congrArg (fun g : pullback b f ⟶ Spec (CommRingCat.of Ω) =>
      g.appTop ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv a))
        (coefficientBaseChangeIso_hom_fst k Ω f σ)
    have hu := ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop
      (pullback.fst b f) (Spec.map (CommRingCat.ofHom σ.toRingHom)))
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv a)
    exact (hs.trans (ht.trans hu)).trans
      (congrArg (pullback.fst b f).appTop
        (ConcreteCategory.congr_hom
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ.toRingHom)) a).symm)
  have htmul (r : Γ(X, ⊤)) (a : Ω) : E (r ⊗ₜ[k] a) =
      (pullback.fst b f).appTop ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv a) *
        (pullback.snd b f).appTop r :=
    coefficientBaseChangeSectionsTensorEquiv_tmul k Ω f r a
  change θ.hom.appTop (E z) = E (Algebra.TensorProduct.map (AlgHom.id k Γ(X, ⊤)) σ.toAlgHom z)
  induction z using TensorProduct.inductionOn with
  | tmul r a =>
      change θ.hom.appTop (E (r ⊗ₜ[k] a)) = E (r ⊗ₜ[k] σ a)
      rw [htmul, htmul, map_mul, hcoeff, hscheme]
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Fintype k] [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]

/-- Positive arithmetic Frobenius differences are surjective on sections
of the literal geometric base change used by the native fundamental group. -/
theorem coefficientBaseChangeFrobenius_appTop_sub_id_surjective
    (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective
      (fun a : Γ(pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f, ⊤) =>
        (coefficientBaseChangeIso k Ω f
          (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ n)).hom.appTop a - a) := by
  let _ : Algebra k Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom.toAlgebra
  let E := coefficientBaseChangeSectionsTensorEquiv k Ω f
  intro a
  obtain ⟨b, hb⟩ := FiniteField.coefficientFrobenius_sub_id_surjective
    k Ω Γ(X, ⊤) n hn (E.symm a)
  change FiniteField.coefficientFrobenius k Ω Γ(X, ⊤) n b - b = E.symm a at hb
  refine ⟨E b, ?_⟩
  have he := coefficientBaseChangeSectionsTensorEquiv_action k Ω f
    (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ n) b
  change (coefficientBaseChangeIso k Ω f
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ n)).hom.appTop (E b) =
    E (FiniteField.coefficientFrobenius k Ω Γ(X, ⊤) n b) at he
  change (coefficientBaseChangeIso k Ω f
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ n)).hom.appTop (E b) - E b = a
  rw [he, ← map_sub, hb, E.apply_symm_apply]

/-- The original coefficient-Frobenius pullback minus the identity is
surjective at every finite Witt length on the actual geometric base change. -/
theorem coefficientBaseChangeFrobenius_witt_sub_id_surjective
    (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n ≠ 0) (m : ℕ) :
    Function.Surjective
      (fun a : TruncatedWittVector p m
          Γ(pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f, ⊤) =>
        TruncatedWittVector.map (coefficientBaseChangeIso k Ω f
          (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ n)).hom.appTop.hom a - a) := by
  intro a
  obtain ⟨b, hb⟩ := WittVector.truncate_map_sub_id_surjective (p := p)
    (coefficientBaseChangeIso k Ω f
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ n)).hom.appTop.hom
    (coefficientBaseChangeFrobenius_appTop_sub_id_surjective k Ω f n hn) m a
  refine ⟨WittVector.truncate m b, ?_⟩
  change TruncatedWittVector.map (coefficientBaseChangeIso k Ω f
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ n)).hom.appTop.hom
        (WittVector.truncate m b) - WittVector.truncate m b = a
  rw [TruncatedWittVector.map_wittVector_truncate, ← map_sub]
  exact hb

end EtaleFundamentalGroups.Cohomology
