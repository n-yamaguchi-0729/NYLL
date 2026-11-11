/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAlgebraizedReductionFlat
public import Nyll.SchemeTheory.Cohomology.Sheaves.ModulePresheafLerayQuasicoherentRelHPresheafChow
public import Nyll.SchemeTheory.Etale.FiniteNeighborhoodSection
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteFreeAffineSections
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeAffineSections
public import Nyll.SchemeTheory.RingTheory.Flat.FiniteFlatAdicLocalization
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Local freeness of an actual algebraized finite étale cover module

At a closed-fiber point, its original affine section module has flat
reductions, identified by the actual closed-level pullback maps with
the finite étale cover sections. The local adic criterion gives freeness
at that prime. Finite presentation spreads this basis to an actual open
neighborhood. The original universally closed structural map then makes
the finite free locus cover the whole scheme over the local base.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules
open AlgebraicCurves.Cohomology.Sheaves.Proofs
open OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow.AlgebraicGeometry.OModulePresheaf.Leray

variable {A : Type u} [CommRing A] [IsLocalRing A]
  {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (.of A))
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
      (level f (IsLocalRing.maximalIdeal A) 0))
  (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
  (s : ∀ n : ℕ, M ⟶ moduleSheaf f (IsLocalRing.maximalIdeal A) V n)
  (hs : ∀ n : ℕ, IsIso
    ((Scheme.Modules.pullback
      (Limits.pullback.fst f (baseInclusion (IsLocalRing.maximalIdeal A) n))).map (s n)))

include V s hs

/-- Every point of the original closed fiber has a finite local basis,
supplied by the actual finite étale reductions of the original module. -/
theorem closedFiber_mem_finiteFreeLocus_of_adicCoverPullback_isIso
    (x : X) (hx : f x = IsLocalRing.closedPoint A) :
    x ∈ finiteFreeLocus M := by
  obtain ⟨U, hU, hxU, _hUtop⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := hU.range_fromSpec ▸ hxU
  have : p.asIdeal.IsPrime := p.isPrime
  have hmap : Spec.map (f.constToPresheaf.app (op U)) = hU.fromSpec ≫ f :=
    specMap_algebraMap_eq_fromSpec_comp f hU
  have hp : PrimeSpectrum.comap (f.constToPresheaf.app (op U)).hom p =
      IsLocalRing.closedPoint A := by
    change Spec.map (f.constToPresheaf.app (op U)) p = IsLocalRing.closedPoint A
    rw [hmap, Scheme.Hom.comp_apply]
    exact hx
  have hIp : sectionsIdeal f (IsLocalRing.maximalIdeal A) U ≤ p.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    exact (congrArg PrimeSpectrum.asIdeal hp).ge
  have : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.Finite Γ(X, U) Γ(M, U) :=
    moduleFinite_sections_of_isFiniteType M U hU
  have (n : ℕ) : IsIso
      ((Scheme.Modules.pullback
        (Limits.pullback.fst f (baseInclusion (IsLocalRing.maximalIdeal A) n))).map (s n)) :=
    hs n
  have : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl Γ(M, U)) :=
    Module.free_localizedModule_of_flat_adic_reductions
      Γ(M, U) (sectionsIdeal f (IsLocalRing.maximalIdeal A) U) p.asIdeal hIp
      (fun n => affineReduction_flat_of_levelPullback_isIso
        f (IsLocalRing.maximalIdeal A) V M n (s n) ⟨U, hU⟩)
  exact mem_finiteFreeLocus_of_free_localized_affineSections M hU p

/-- Over a local base, an actual finite quasicoherent algebraization
of the finite étale cover modules is finite locally free everywhere
when the original structural map is universally closed. -/
theorem finiteFreeLocus_eq_top_of_adicCoverPullback_isIso [UniversallyClosed f] :
    finiteFreeLocus M = ⊤ := by
  obtain ⟨W, hW, hWM⟩ := f.exists_preimage_le_of_fiber_subset
    (IsLocalRing.closedPoint A) (finiteFreeLocus M)
      (closedFiber_mem_finiteFreeLocus_of_adicCoverPullback_isIso f V M s hs)
  have hWtop : W = ⊤ := (IsLocalRing.closedPoint_mem_iff W).mp hW
  apply top_unique
  intro x _hx
  apply hWM
  change f x ∈ W
  rw [hWtop]
  trivial

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
