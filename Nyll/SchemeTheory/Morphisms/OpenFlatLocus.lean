/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Naganori Yamaguchi (assisted by OpenAI Codex)

The affine stalk comparison adapts `formallySmooth_stalkMap_iff` from
Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean to flatness.
-/

module

public import Nyll.SchemeTheory.RingTheory.Flat.OpenLocus
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Flat.Localization

/-!
# The open flat locus of a locally finite type scheme morphism

Over a locally Noetherian target, flatness of the original stalk map is
an open condition on the source. The affine stalk-localization comparison
identifies it with the ring-theoretic flat locus. Affine chart maps then
transport this open set back to the original scheme.

In particular, flatness at a supplied point constructs an actual open
neighborhood on which the original morphism is flat.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- On actual affine charts, flatness of the original stalk map is flatness
of the source prime localization over the target section ring. -/
lemma flat_stalkMap_iff {f : X ⟶ Y} {x : X}
    (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    let _ : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.Flat ↔
      Module.Flat Γ(Y, U) (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  intro sectionAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨(congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx)).symm⟩
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  change (f.stalkMap x).hom.Flat ↔ Module.Flat Γ(Y, U) (Localization.AtPrime q)
  trans Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← RingHom.flat_algebraMap_iff]
    exact RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · exact Module.flat_iff_of_isLocalization
      (Localization.AtPrime p) p.primeCompl (Localization.AtPrime q)

/-- The flat locus is open for a locally finite type morphism to a locally
Noetherian scheme. Its defining condition uses the original stalk maps. -/
lemma Scheme.Hom.isOpen_flatLocus (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    IsOpen {x : X | (f.stalkMap x).hom.Flat} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  change IsAffineOpen U at hU
  change IsAffineOpen V at hV
  change V ≤ f ⁻¹ᵁ U at hVU
  let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Algebra.FiniteType Γ(Y, U) Γ(X, V) := f.finiteType_appLE hU hV hVU
  let Z : Set (PrimeSpectrum Γ(X, V)) :=
    {q | Module.Flat Γ(Y, U) (Localization.AtPrime q.asIdeal)}
  have hZ : IsOpen Z := Module.Flat.isOpen_setOf_flat_localization_atPrime
  refine ⟨hV.fromSpec '' Z, ?_, hV.fromSpec.isOpenEmbedding.isOpenMap Z hZ, ?_⟩
  · rintro y ⟨q, hq, rfl⟩
    have hyV : hV.fromSpec q ∈ V := by
      change hV.fromSpec q ∈ (V : Set X)
      rw [← hV.range_fromSpec]
      exact ⟨q, rfl⟩
    apply (flat_stalkMap_iff U hU V hV hVU hyV).mpr
    have heq : hV.primeIdealOf ⟨hV.fromSpec q, hyV⟩ = q :=
      hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf _)
    rw [heq]
    exact hq
  · exact ⟨hV.primeIdealOf ⟨x, hxV⟩,
      (flat_stalkMap_iff U hU V hV hVU hxV).mp hx, hV.fromSpec_primeIdealOf _⟩

/-- The open subscheme where the original stalk maps are flat. -/
def Scheme.Hom.flatLocus (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] : X.Opens :=
  ⟨{x : X | (f.stalkMap x).hom.Flat}, f.isOpen_flatLocus⟩

lemma Scheme.Hom.mem_flatLocus {f : X ⟶ Y}
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] {x : X} :
    x ∈ f.flatLocus ↔ (f.stalkMap x).hom.Flat := Iff.rfl

/-- Restriction of the original morphism to its constructed flat locus is flat. -/
theorem Scheme.Hom.flat_flatLocus (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] : Flat (f.flatLocus.ι ≫ f) := by
  apply Flat.of_stalkMap
  intro x
  have heq : ((f.flatLocus.ι ≫ f).stalkMap x).hom =
      (f.flatLocus.ι.stalkMap x).hom.comp (f.stalkMap (f.flatLocus.ι x)).hom :=
    congrArg (fun a : Y.presheaf.stalk (f (f.flatLocus.ι x)) ⟶
      f.flatLocus.toScheme.presheaf.stalk x => a.hom)
        (Scheme.Hom.stalkMap_comp f.flatLocus.ι f x)
  exact heq.symm ▸ (show (f.stalkMap (f.flatLocus.ι x)).hom.Flat from x.property).comp
    (Flat.stalkMap f.flatLocus.ι x)

/-- A flat original stalk map supplies an actual flat open neighborhood. -/
theorem exists_flat_open_of_flat_stalkMap (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    (x : X) (hx : (f.stalkMap x).hom.Flat) :
    ∃ W : X.Opens, x ∈ W ∧ Flat (W.ι ≫ f) :=
  ⟨f.flatLocus, hx, f.flat_flatLocus⟩

/-- Flatness of the original stalk is equivalent to existence of a flat
open neighborhood, under the same finite type hypotheses. -/
theorem exists_flat_open_iff_flat_stalkMap (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] (x : X) :
    (∃ W : X.Opens, x ∈ W ∧ Flat (W.ι ≫ f)) ↔ (f.stalkMap x).hom.Flat := by
  constructor
  · rintro ⟨W, hx, hW⟩
    let w : W.toScheme := ⟨x, hx⟩
    have heq : ((W.ι ≫ f).stalkMap w).hom =
        (W.ι.stalkMap w).hom.comp (f.stalkMap (W.ι w)).hom :=
      congrArg (fun a : Y.presheaf.stalk (f (W.ι w)) ⟶
        W.toScheme.presheaf.stalk w => a.hom) (Scheme.Hom.stalkMap_comp W.ι f w)
    have hc : ((W.ι.stalkMap w).hom.comp (f.stalkMap (W.ι w)).hom).Flat :=
      heq ▸ Flat.stalkMap (W.ι ≫ f) w
    have : IsIso (W.ι.stalkMap w) := inferInstance
    exact (RingHom.Flat.respectsIso.cancel_right_isIso
      (f.stalkMap (W.ι w)) (W.ι.stalkMap w)).mp hc
  · exact exists_flat_open_of_flat_stalkMap f x

end AlgebraicGeometry
