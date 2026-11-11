/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceClosureComparison
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence
public import Mathlib.FieldTheory.IsSepClosed

/-!
# The original native absolute abelian map at a supplied generic point

An actual separable-closure equivalence identifies native absolute Galois
automorphisms with the supplied field-source automorphisms. Its induced
abelian map agrees with the actual comparison of the two scheme fibers.
Changing the closure equivalence changes the original group map by an
inner conjugation, which disappears in this original abelian target.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry ProCGroups.Abelian

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
  [IsSepClosure F Ω] [IsSepClosed Ω]
  {X : Scheme.{u}} [IsIntegral X] (p : Spec (.of F) ⟶ X)
  (e : SeparableClosure F ≃ₐ[F] Ω)

/-- The original native absolute Galois map into the supplied geometric
fiber, through the specified actual closure equivalence. -/
def nativeSourceGaloisHomOfClosure :
    Gal(SeparableClosure F/F) →ₜ* π₁ᵉᵗ(ξ F Ω ≫ p) :=
  (fieldSourceAbsoluteGaloisHom F Ω p).comp
    { toMonoidHom := (AlgEquiv.autCongr e).toMonoidHom
      continuous_toFun :=
        RamificationTheory.Field.absoluteGaloisGroup.algEquiv_autCongr_continuous e }

omit [IsIntegral X] in
/-- The native map keeps the literal conjugation of original field automorphisms. -/
theorem nativeSourceGaloisHomOfClosure_apply (σ : Gal(SeparableClosure F/F)) :
    nativeSourceGaloisHomOfClosure p e σ =
      fieldSourceAbsoluteGaloisHom F Ω p (AlgEquiv.autCongr e σ) := rfl

/-- Surjectivity follows from the actual generic-point map and the actual
equivalence of its closure groups. -/
theorem nativeSourceGaloisHomOfClosure_surjective
    [IsNormalIntegral X] [IsDominant p] [IsPreimmersion p] [QuasiCompact p] :
    Function.Surjective (nativeSourceGaloisHomOfClosure p e) :=
  (fieldSourceAbsoluteGaloisHom_surjective F Ω p).comp (AlgEquiv.autCongr e).surjective

/-- The original abelian map from native absolute Galois to the supplied
scheme fiber, induced by the literal original group map. -/
def nativeSourceAbelianHomOfClosure :
    TopologicalAbelianization Gal(SeparableClosure F/F) →ₜ*
      TopologicalAbelianization π₁ᵉᵗ(ξ F Ω ≫ p) :=
  TopologicalAbelianization.map (nativeSourceGaloisHomOfClosure p e)

omit [IsIntegral X] in
/-- Native Galois representatives keep their original image. -/
theorem nativeSourceAbelianHomOfClosure_mk (σ : Gal(SeparableClosure F/F)) :
    nativeSourceAbelianHomOfClosure p e
        (TopologicalAbelianization.mk Gal(SeparableClosure F/F) σ) =
      TopologicalAbelianization.mk π₁ᵉᵗ(ξ F Ω ≫ p)
        (fieldSourceAbsoluteGaloisHom F Ω p (AlgEquiv.autCongr e σ)) := rfl

/-- Every original abelian class of the supplied generic fiber comes from
an original native absolute-abelian class. -/
theorem nativeSourceAbelianHomOfClosure_surjective
    [IsNormalIntegral X] [IsDominant p] [IsPreimmersion p] [QuasiCompact p] :
    Function.Surjective (nativeSourceAbelianHomOfClosure p e) := by
  intro a
  obtain ⟨g, rfl⟩ := TopologicalAbelianization.surjective_mk π₁ᵉᵗ(ξ F Ω ≫ p) a
  obtain ⟨σ, rfl⟩ := nativeSourceGaloisHomOfClosure_surjective p e g
  exact ⟨TopologicalAbelianization.mk Gal(SeparableClosure F/F) σ, rfl⟩

/-- The native absolute abelian map is the original native field-source
map followed by the actual scheme-fiber comparison. -/
theorem nativeSourceAbelianHomOfClosure_comparison
    (a : TopologicalAbelianization Gal(SeparableClosure F/F)) :
    nativeSourceAbelianHomOfClosure p e a =
      TopologicalAbelianization.congr (fieldSourceClosureGroupEquiv p e)
        (TopologicalAbelianization.map
          (fieldSourceAbsoluteGaloisHom F (SeparableClosure F) p) a) := by
  obtain ⟨σ, rfl⟩ := TopologicalAbelianization.surjective_mk Gal(SeparableClosure F/F) a
  rw [nativeSourceAbelianHomOfClosure_mk,
    TopologicalAbelianization.map_apply_mk, TopologicalAbelianization.congr_apply_mk,
    fieldSourceClosureGroupEquiv_galois]

omit [IsIntegral X] in
/-- The original abelian source map is independent of the chosen actual
separable-closure equivalence: the discrepancy is an original inner conjugation. -/
theorem nativeSourceAbelianHomOfClosure_eq
    (e' : SeparableClosure F ≃ₐ[F] Ω) :
    nativeSourceAbelianHomOfClosure p e = nativeSourceAbelianHomOfClosure p e' := by
  apply ContinuousMonoidHom.ext
  intro a
  obtain ⟨σ, rfl⟩ := TopologicalAbelianization.surjective_mk Gal(SeparableClosure F/F) a
  let δ : Gal(Ω/F) := e.symm.trans e'
  have hconj : AlgEquiv.autCongr e' σ = δ * AlgEquiv.autCongr e σ * δ⁻¹ := by
    apply AlgEquiv.ext
    intro x
    change e' (σ (e'.symm x)) =
      e' (e.symm (e (σ (e.symm (e (e'.symm x))))))
    rw [e.symm_apply_apply, e.symm_apply_apply]
  let χ : Gal(Ω/F) →* TopologicalAbelianization π₁ᵉᵗ(ξ F Ω ≫ p) :=
    (TopologicalAbelianization.mk π₁ᵉᵗ(ξ F Ω ≫ p)).comp
      (fieldSourceAbsoluteGaloisHom F Ω p).toMonoidHom
  change χ (AlgEquiv.autCongr e σ) = χ (AlgEquiv.autCongr e' σ)
  rw [hconj, map_mul, map_mul, map_inv,
    mul_comm (χ δ) (χ (AlgEquiv.autCongr e σ)), mul_assoc, mul_inv_cancel, mul_one]

end AlgebraicGeometry.FiniteEtale
