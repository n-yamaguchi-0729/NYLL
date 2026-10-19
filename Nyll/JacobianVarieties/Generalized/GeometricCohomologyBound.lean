/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RelativeNormalizedSection
import Nyll.JacobianVarieties.Generalized.ModulusUniformVanishing
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # A uniform bound for actual geometric first cohomology -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicCurves.Cohomology.Sheaves.Proofs
open Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq.Ws31ChiA
open scoped TensorProduct

namespace AlgebraicGeometry.GeneralizedJacobian

/-- A finite set of module generators bounds every field fibre, uniformly. -/
theorem exists_uniform_tensor_finrank_bound
    {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ∃ n : ℕ, ∀ (k : Type u) [Field k] [Algebra R k],
      Module.finrank k (k ⊗[R] M) ≤ n := by
  classical
  obtain ⟨s, hs⟩ : (⊤ : Submodule R M).FG := Module.Finite.fg_top
  refine ⟨s.card, ?_⟩
  intro k _ _
  let v : ↥s → k ⊗[R] M := fun z => 1 ⊗ₜ[R] z.val
  have hv : Set.range v = TensorProduct.mk R k M 1 '' (s : Set M) := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hspan : Submodule.span k (Set.range v) = ⊤ := by
    rw [hv, ← Submodule.baseChange_span, hs, Submodule.baseChange_top]
  have hb := finrank_le_of_span_eq_top hspan
  simpa only [Fintype.card_coe] using hb

/-- Proper cohomological finiteness supplies a bound on all geometric genera of the family. -/
theorem exists_uniform_geometric_H1_bound
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of R)) [IsProper c] (𝒱 : X.TwoAffineOpenCover) :
    ∃ g : ℕ, ∀ (k : Type u) [Field k] [Algebra R k],
      Module.finrank k ((𝒱.pullback c k).sectionsOf
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))
          (𝟙_ (pullback c (Scheme.TwoAffineOpenCover.specMap R k)).Modules)).H1 ≤ g := by
  let F : X.Modules := 𝟙_ X.Modules
  have hF : IsInvertible F := isInvertible_unit _
  have hfin := (OModulePresheaf.cechFinite_toOrderedAffineCover_iff
    (OModulePresheaf.ofModules c F) 𝒱).mp
      (OModulePresheaf.cechFinite_ofModules_of_locallyTrivial c F
        hF.exists_trivialization 𝒱.toOrderedAffineCover)
  have : Module.Finite R (𝒱.sectionsOf c F).H1 := hfin.2
  obtain ⟨g, hg⟩ := exists_uniform_tensor_finrank_bound (R := R) (𝒱.sectionsOf c F).H1
  refine ⟨g, ?_⟩
  intro k _ _
  let f := pullback.fst c (Scheme.TwoAffineOpenCover.specMap R k)
  let π := pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k)
  let 𝒲 := 𝒱.pullback c k
  obtain ⟨⟨eb⟩, _, _⟩ :=
    Scheme.TwoAffineOpenCover.exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
      𝒱 c F hF.exists_trivialization k
  obtain ⟨_, ⟨eu⟩⟩ := nonempty_linearEquiv_of_iso π 𝒲
    (Scheme.Modules.pullbackTensorUnitObjIso f)
  calc
    Module.finrank k (𝒲.sectionsOf π (𝟙_ _)).H1 =
        Module.finrank k (𝒲.sectionsOf π ((Scheme.Modules.pullback f).obj F)).H1 :=
      eu.finrank_eq.symm
    _ = Module.finrank k (k ⊗[R] (𝒱.sectionsOf c F).H1) := eb.finrank_eq
    _ ≤ g := hg k

end AlgebraicGeometry.GeneralizedJacobian
