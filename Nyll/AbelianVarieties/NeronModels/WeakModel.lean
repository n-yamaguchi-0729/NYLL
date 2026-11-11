/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Nyll.AbelianVarieties.NeronModels.Basic

/-!
# Models that catch points over index-one extensions

A family consists of actual schemes over the valuation ring with open generic-fibre charts.
Its point-catching condition records the extension property used in the construction of a
Néron model. Existence of such families is proved separately.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from:
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_NeronModelInfra_WeakNeronModel.lean
Upstream NOTICE:
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION:
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra

/-- A local extension of ramification index one with formally smooth residue-field extension. -/
structure IsIndexOneExtension (R R' : Type u) [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] : Prop where
  /-- The base maximal ideal generates the maximal ideal upstairs. -/
  map_maximalIdeal :
    Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R'
  /-- The induced residue-field extension is formally smooth. -/
  formallySmooth_residueField :
    Algebra.FormallySmooth (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R')

/-- The identity extension has index one. -/
theorem IsIndexOneExtension.refl (R : Type u) [CommRing R] [IsLocalRing R] :
    IsIndexOneExtension R R where
  map_maximalIdeal := by
    rw [Algebra.algebraMap_self, Ideal.map_id]
  formallySmooth_residueField := by
    have e : (IsLocalRing.ResidueField.instAlgebra :
        Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)) =
        Algebra.id (IsLocalRing.ResidueField R) := by
      apply Algebra.algebra_ext
      intro x
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      rfl
    have h : @Algebra.FormallySmooth (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)
        _ _ (Algebra.id (IsLocalRing.ResidueField R)) := inferInstance
    rw [e]
    exact h

section PointGenericFibre

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {K' : Type u} [CommRing K'] [Algebra R' K'] [Algebra R K']
  [IsScalarTower R R' K'] [Algebra K K'] [IsScalarTower R K K']

/-- The two scalar towers induce the same morphism between their spectra. -/
theorem specMap_algebraMap_comp_specMap_algebraMap
    (R K R' K' : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing R'] [Algebra R R'] [CommRing K'] [Algebra R' K'] [Algebra R K']
    [IsScalarTower R R' K'] [Algebra K K'] [IsScalarTower R K K'] :
    Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) =
      Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- Restrict a point of a model to its actual generic fibre. -/
def pointGenericFibre
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K')))
      (pullback.snd f (specGenericFibreInclusion R K)) :=
  ⟨pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ x.1)
      (Spec.map (CommRingCat.ofHom (algebraMap K K')))
      (by rw [Category.assoc, x.2, specGenericFibreInclusion_eq,
        specMap_algebraMap_comp_specMap_algebraMap R K R' K']),
    pullback.lift_snd _ _ _⟩

@[simp]
theorem pointGenericFibre_coe_comp_fst
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f) :
    (pointGenericFibre (K := K) (K' := K') x).1 ≫
        pullback.fst f (specGenericFibreInclusion R K) =
      Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ x.1 :=
  pullback.lift_fst _ _ _

@[simp]
theorem pointGenericFibre_coe_comp_snd
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f) :
    (pointGenericFibre (K := K) (K' := K') x).1 ≫
        pullback.snd f (specGenericFibreInclusion R K) =
      Spec.map (CommRingCat.ofHom (algebraMap K K')) :=
  pullback.lift_snd _ _ _

end PointGenericFibre

/-- Schemes over the base equipped with open charts on a fixed generic fibre. -/
structure ModelFamily (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    {AK : Scheme.{u}} (gK : AK ⟶ Spec (CommRingCat.of K)) where
  /-- The indexing type of the family. -/
  ι : Type u
  /-- The actual schemes in the family. -/
  X : ι → Scheme.{u}
  /-- Their structure maps to the base. -/
  str : ∀ i, X i ⟶ Spec (CommRingCat.of R)
  /-- The generic-fibre charts. -/
  chart : ∀ i, SchemeHomOver (pullback.snd (str i) (specGenericFibreInclusion R K)) gK
  /-- Each chart is an open immersion. -/
  isOpenImmersion_chart : ∀ i, IsOpenImmersion (chart i).1

attribute [instance] ModelFamily.isOpenImmersion_chart

/-- Every point over an index-one extension lifts to a member of the family. -/
def ModelFamily.CatchesIndexOnePoints
    {R K : Type u} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    {AK : Scheme.{u}} {gK : AK ⟶ Spec (CommRingCat.of K)} (M : ModelFamily R K gK) : Prop :=
  ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')]
    (K' : Type u) [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    [Algebra R K'] [IsScalarTower R R' K'] [Algebra K K'] [IsScalarTower R K K'],
    IsIndexOneExtension R R' →
    ∀ a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K'))) gK,
      ∃ (i : M.ι) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (M.str i)),
        schemeHomOverComp (pointGenericFibre x) (M.chart i) = a

end NeronModelInfra

end
end
