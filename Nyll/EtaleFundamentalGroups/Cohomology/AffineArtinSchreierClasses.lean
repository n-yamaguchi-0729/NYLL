/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.AffineArtinSchreierMonodromy
import Nyll.EtaleFundamentalGroups.GeometricFiber.FixedPointSections
import Nyll.GaloisCohomology.ArtinSchreier.RootCharacter

/-!
# Triviality of the native affine Artin–Schreier character

A trivial original monodromy character gives a fixed geometric point of
the actual root cover. The established finite-cover section theorem
descends that point to a section, hence to a root in the original base
ring. No domain or normality hypothesis is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open CategoryTheory.PreGaloisCategory
open ValuationTheory.DiscreteValuationField

namespace EtaleFundamentalGroups.Cohomology

universe u

variable (R : Type u) [CommRing R] [Nontrivial R]
  (p : ℕ) [Fact p.Prime] [CharP R p] (a : R)

/-- Sections of the original Artin–Schreier cover are precisely roots
over its original affine base. -/
theorem artinSchreierCover_section_iff :
    (∃ s : Spec (CommRingCat.of R) ⟶ (artinSchreierCover R p a).left,
      s ≫ (artinSchreierCover R p a).hom = 𝟙 _) ↔
      ∃ b : R, b ^ p - b = a := by
  have hid : Spec.algebraMap R R = 𝟙 (Spec (CommRingCat.of R)) :=
    Scheme.Spec.map_id _
  constructor
  · rintro ⟨s, hs⟩
    let f : ArtinSchreierAlgebra R p a →ₐ[R] R :=
      Spec.homEquivAlgHom ⟨s, hs.trans hid.symm⟩
    refine ⟨f (AdjoinRoot.root _), ?_⟩
    simpa only [map_sub, map_pow, f.commutes, Algebra.algebraMap_self_apply] using
      congrArg f (artinSchreierAlgebra_root R p a)
  · rintro ⟨b, hb⟩
    let f : ArtinSchreierAlgebra R p a →ₐ[R] R :=
      AdjoinRoot.liftAlgHom _ (AlgHom.id R R) b (by
        change (X ^ p - X - C a : Polynomial R).eval₂ (RingHom.id R) b = 0
        rw [eval₂_sub, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
        change b ^ p - b - a = 0
        exact sub_eq_zero.mpr hb)
    let s := (Spec.homEquivAlgHom (R := R)).symm f
    exact ⟨s.1, s.2.trans hid⟩

variable [ConnectedSpace (Spec (CommRingCat.of R))]
  {Ω : Type u} [Field Ω] [Algebra R Ω] [CharP Ω p] [IsSepClosed Ω]

/-- The native character vanishes exactly on actual Artin–Schreier
coboundaries in the original affine coordinate ring. -/
theorem affineArtinSchreierCharacter_eq_one_iff :
    affineArtinSchreierCharacter R p a (Ω := Ω) = 1 ↔
      ∃ b : R, b ^ p - b = a := by
  refine Iff.trans ?_
    ((FiniteEtale.exists_section_iff_exists_fiber_fixed
      (Spec.algebraMap R Ω) (artinSchreierCover R p a)).symm.trans
        (artinSchreierCover_section_iff R p a))
  constructor
  · intro hχ
    have : Nonempty ((FiniteEtale.fiber (Spec.algebraMap R Ω)).obj
        (artinSchreierCover R p a)) := by
      obtain ⟨β, hβ⟩ := ArtinSchreierTheory.exists_root p Ω (algebraMap R Ω a)
      exact ⟨(artinSchreierFiberEquivRoots R p a).symm ⟨β, hβ⟩⟩
    refine ⟨Classical.choice inferInstance, fun γ => ?_⟩
    apply (artinSchreierFiberEquivRoots R p a).injective
    apply Subtype.ext
    apply sub_eq_zero.mp
    have h := affineArtinSchreierCharacter_cast R p a (Classical.choice inferInstance) γ
    have hzero : (affineArtinSchreierCharacter R p a (Ω := Ω) γ).toAdd = 0 :=
      congrArg (fun χ : Aut (FiniteEtale.fiber (Spec.algebraMap R Ω)) →ₜ*
        Multiplicative (ZMod p) => (χ γ).toAdd) hχ
    exact h.symm.trans ((congrArg (ZMod.castHom (dvd_refl p) Ω) hzero).trans (map_zero _))
  · rintro ⟨x, hx⟩
    apply ContinuousMonoidHom.ext
    intro γ
    change (affineArtinSchreierCharacter R p a (Ω := Ω) γ).toAdd = 0
    apply (ZMod.castHom (dvd_refl p) Ω).injective
    rw [affineArtinSchreierCharacter_cast R p a x γ, hx γ, sub_self, map_zero]

end EtaleFundamentalGroups.Cohomology
