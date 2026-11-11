/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.FiniteType.FiniteFreeLocus
public import Nyll.SchemeTheory.Modules.Sections.InverseLimit

/-!
# Transport of actual finite local bases

Native module isomorphisms and open restriction transport the original
compatible section bases. In particular local freeness of a restriction
identifies an actual part of the original finite locally free locus.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- An actual module-sheaf isomorphism transports compatible finite bases. -/
theorem IsFiniteFreeOn.of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) {U : X.Opens} (hU : IsFiniteFreeOn M U) :
    IsFiniteFreeOn N U := by
  obtain ⟨n, s, hs⟩ := hU
  refine ⟨n, fun i => e.hom.app U (s i), ?_⟩
  intro V hVU
  obtain ⟨b, hb⟩ := hs V hVU
  let l : Γ(M, V) ≃ₗ[Γ(X, V)] Γ(N, V) :=
    ((moduleSectionsFunctor V).mapIso e).toLinearEquiv
  refine ⟨b.map l, ?_⟩
  intro i
  rw [Module.Basis.map_apply, hb]
  exact (congrArg (fun k : Γ(M, U) ⟶ Γ(N, V) => k (s i))
    (e.hom.mapPresheaf.naturality (homOfLE hVU).op))

/-- The finite locally free locus is invariant under actual isomorphism. -/
theorem finiteFreeLocus_eq_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    finiteFreeLocus M = finiteFreeLocus N := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_finiteFreeLocus_iff M x).mp hx
    exact (mem_finiteFreeLocus_iff N x).mpr ⟨U, hxU, hU.of_iso e⟩
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_finiteFreeLocus_iff N x).mp hx
    exact (mem_finiteFreeLocus_iff M x).mpr ⟨U, hxU, hU.of_iso e.symm⟩

/-- A basis on the restriction supplies the original basis on its image open. -/
theorem IsFiniteFreeOn.of_restrict {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) {W : X.Opens}
    (hW : IsFiniteFreeOn (M.restrict j) W) : IsFiniteFreeOn M (j ''ᵁ W) := by
  obtain ⟨n, s, hs⟩ := hW
  refine ⟨n, fun i => (M.restrictAppIso j W).hom (s i), ?_⟩
  intro V hV
  have hpre : j ⁻¹ᵁ V ≤ W := by
    have h := j.preimage_mono hV
    rwa [j.preimage_image_eq] at h
  have himage : j ''ᵁ (j ⁻¹ᵁ V) = V := by
    rw [j.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.mpr (hV.trans (j.image_le_opensRange W))
  obtain ⟨Z, hZW, rfl⟩ : ∃ Z : X.Opens, Z ≤ W ∧ j ''ᵁ Z = V :=
    ⟨j ⁻¹ᵁ V, hpre, himage⟩
  obtain ⟨b, hb⟩ := hs Z hZW
  let e := (j.appIso Z).symm.commRingCatIsoToRingEquiv
  let : Module Γ(Y, j ''ᵁ Z) Γ(M.restrict j, Z) :=
    inferInstanceAs (Module Γ(Y, j ''ᵁ Z) Γ(M, j ''ᵁ Z))
  let b' : Module.Basis (Fin n) Γ(Y, j ''ᵁ Z) Γ(M, j ''ᵁ Z) :=
    b.mapCoeffs e (fun c x => rfl)
  refine ⟨b', ?_⟩
  intro i
  have hb' : b' i = (M.restrictAppIso j Z).hom (b i) :=
    b.mapCoeffs_apply e (fun c x => rfl) i
  exact hb'.trans ((congrArg (M.restrictAppIso j Z).hom (hb i)).trans
    (congrArg (fun k : Γ(M.restrict j, W) ⟶ Γ(M, j ''ᵁ Z) => k (s i))
      (M.map_restrictAppIso_hom j (homOfLE hZW).op)))

/-- A finite locally free restriction lies in the original module's
finite locally free locus. -/
theorem le_finiteFreeLocus_of_restrict_eq_top {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (hU : finiteFreeLocus (M.restrict U.ι) = ⊤) :
    U ≤ finiteFreeLocus M := by
  intro x hx
  let y : U := ⟨x, hx⟩
  have hy : y ∈ finiteFreeLocus (M.restrict U.ι) := by
    rw [hU]
    trivial
  obtain ⟨W, hyW, hW⟩ := (mem_finiteFreeLocus_iff (M.restrict U.ι) y).mp hy
  exact (mem_finiteFreeLocus_iff M x).mpr
    ⟨U.ι ''ᵁ W, ⟨y, hyW, rfl⟩, hW.of_restrict U.ι M⟩

end AlgebraicGeometry.Scheme.Modules
