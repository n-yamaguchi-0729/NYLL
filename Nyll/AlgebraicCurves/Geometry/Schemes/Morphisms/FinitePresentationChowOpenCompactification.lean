/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.FgSubalgebraProperFlatPullback
public import Nyll.SchemeTheory.Descent.IsProperFgSubalgebraProperPullbackSnd
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Chow open compactifications of separated finitely presented schemes

The existing separated finite-presentation descent produces a Noetherian
coefficient model. Its existing Chow open compactification is pulled back
using the existing comparison square. The result is an actual proper
surjective cover of the original scheme with an open immersion into a
proper finitely presented ambient scheme, over the original base ring.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits
open AlgebraicCurves.Geometry.Schemes.Proofs
open IsProper_exists_fg_subalgebra_of_isProper_pullback_snd

namespace AlgebraicGeometry

/-- A separated finitely presented scheme over an arbitrary algebra over a
Noetherian coefficient ring has an actual Chow open compactification over
its original base. -/
theorem exists_proper_surjective_open_compactification_of_finitePresentation
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [QuasiCompact f] [LocallyOfFinitePresentation f] :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P)
      (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧
        LocallyOfFinitePresentation q ∧ j ≫ q = π ≫ f := by
  obtain ⟨B, hB, -, X₀, f₀, a, hf₀sep, hf₀qc, hf₀fp, sq⟩ :=
    SeparatedFinitePresentationDescent (A₀ := R) f ∅
  have : Algebra.FiniteType R B := (Subalgebra.fg_iff_finiteType B).mp hB
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have : IsSeparated f₀ := hf₀sep
  have : QuasiCompact f₀ := hf₀qc
  have : LocallyOfFinitePresentation f₀ := hf₀fp
  obtain ⟨X₀', P₀, π₀, j₀, q₀, hπ₀, hπ₀surj, hj₀, hq₀, hw₀⟩ :=
    exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated f₀
  have : IsProper π₀ := hπ₀
  have : Surjective π₀ := hπ₀surj
  have : IsOpenImmersion j₀ := hj₀
  have : IsProper q₀ := hq₀
  have : LocallyOfFinitePresentation q₀ := inferInstance
  let α : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap B A))
  let e : X ≅ pullback f₀ α := sq.isoPullback
  let π := ProperDesc.ρ f₀ π₀ j₀ q₀ hw₀ α ≫ e.inv
  have : IsProper (ProperDesc.ρ f₀ π₀ j₀ q₀ hw₀ α) :=
    ProperDesc.isProper_ρ f₀ π₀ j₀ q₀ hw₀ α
  have : Surjective (ProperDesc.ρ f₀ π₀ j₀ q₀ hw₀ α) :=
    ProperDesc.surjective_ρ f₀ π₀ j₀ q₀ hw₀ α
  have he : e.inv ≫ f = pullback.snd f₀ α := by
    rw [← sq.isoPullback_hom_snd, Iso.inv_hom_id_assoc]
  refine ⟨_, _, π, ProperDesc.jY j₀ q₀ α, pullback.snd q₀ α,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  change ProperDesc.jY j₀ q₀ α ≫ pullback.snd q₀ α =
    (ProperDesc.ρ f₀ π₀ j₀ q₀ hw₀ α ≫ e.inv) ≫ f
  rw [Category.assoc, he, ProperDesc.ρ_snd]

end AlgebraicGeometry
