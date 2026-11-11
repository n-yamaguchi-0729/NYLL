/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_PolarDifferentials.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Nyll.AlgebraicCurves.Differentials.Regular.Regular
public import Nyll.AlgebraicCurves.Differentials.Local.Uniformizer
public import Nyll.AlgebraicCurves.Places.Evaluation.Value

/-!
# Polar
-/

@[expose] public section

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

/-- Regularity of a differential expressed using an integral coefficient in a local coordinate. -/
def IsRegularAt (ω : Ω[F⁄K]) : Prop :=
  ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord

/-- The condition that a differential has at most a simple pole at the place. -/
def HasSimplePoleAt (ω : Ω[F⁄K]) : Prop :=
  ∃ f : F, v.uniformizer * f ∈ v.toValuationSubring ∧ ω = f • v.dCoord

/-- The condition that a differential has the specified simple residue in the chosen local
coordinate. -/
def HasSimpleResidue (ω : Ω[F⁄K]) (a : K) : Prop :=
  ∃ f : F, ω = f • v.dCoord ∧ v.HasValue (v.uniformizer * f) a

variable {v}

variable (v) in
theorem uniformizer_mem_toValuationSubring : v.uniformizer ∈ v.toValuationSubring :=
  SetLike.coe_mem (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose

variable (v) in
theorem irreducible_mk_uniformizer :
    Irreducible (⟨v.uniformizer, v.uniformizer_mem_toValuationSubring⟩ : v.toValuationSubring) := by
  have h := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  exact h

theorem IsRegularAt.hasSimplePoleAt {ω : Ω[F⁄K]} (h : v.IsRegularAt ω) : v.HasSimplePoleAt ω := by
  obtain ⟨f, hf, rfl⟩ := h
  exact ⟨f, mul_mem v.uniformizer_mem_toValuationSubring hf, rfl⟩

theorem HasSimpleResidue.hasSimplePoleAt {ω : Ω[F⁄K]} {a : K} (h : v.HasSimpleResidue ω a) :
    v.HasSimplePoleAt ω := by
  obtain ⟨f, rfl, hval⟩ := h
  exact ⟨f, hval.mem, rfl⟩

variable (v) in
theorem isRegularAt_zero : v.IsRegularAt (0 : Ω[F⁄K]) :=
  ⟨0, zero_mem _, by rw [zero_smul]⟩

theorem IsRegularAt.add {ω η : Ω[F⁄K]} (hω : v.IsRegularAt ω) (hη : v.IsRegularAt η) :
    v.IsRegularAt (ω + η) := by
  obtain ⟨f, hf, rfl⟩ := hω
  obtain ⟨g, hg, rfl⟩ := hη
  exact ⟨f + g, add_mem hf hg, by rw [add_smul]⟩

theorem IsRegularAt.smul (c : K) {ω : Ω[F⁄K]} (hω : v.IsRegularAt ω) : v.IsRegularAt (c • ω) := by
  obtain ⟨f, hf, rfl⟩ := hω
  refine ⟨algebraMap K F c * f, mul_mem (v.algebraMap_mem' c) hf, ?_⟩
  rw [mul_smul, algebraMap_smul]

variable (v) in
theorem hasSimplePoleAt_zero : v.HasSimplePoleAt (0 : Ω[F⁄K]) :=
  ⟨0, by rw [mul_zero]; exact zero_mem _, by rw [zero_smul]⟩

theorem HasSimplePoleAt.add {ω η : Ω[F⁄K]} (hω : v.HasSimplePoleAt ω) (hη : v.HasSimplePoleAt η) :
    v.HasSimplePoleAt (ω + η) := by
  obtain ⟨f, hf, rfl⟩ := hω
  obtain ⟨g, hg, rfl⟩ := hη
  exact ⟨f + g, by rw [mul_add]; exact add_mem hf hg, by rw [add_smul]⟩

theorem HasSimplePoleAt.smul (c : K) {ω : Ω[F⁄K]} (hω : v.HasSimplePoleAt ω) :
    v.HasSimplePoleAt (c • ω) := by
  obtain ⟨f, hf, rfl⟩ := hω
  refine ⟨algebraMap K F c * f, ?_, by rw [mul_smul, algebraMap_smul]⟩
  rw [mul_left_comm]
  exact mul_mem (v.algebraMap_mem' c) hf

theorem hasSimpleResidue_zero_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasSimpleResidue (f • v.dCoord) 0 := by
  refine ⟨f, rfl, mul_mem v.uniformizer_mem_toValuationSubring hf, ?_⟩
  rw [map_zero, IsLocalRing.residue_eq_zero_iff]
  have hx : (⟨v.uniformizer * f, mul_mem v.uniformizer_mem_toValuationSubring hf⟩ :
    v.toValuationSubring) =
      ⟨v.uniformizer, v.uniformizer_mem_toValuationSubring⟩ * ⟨f, hf⟩ := rfl
  rw [hx]
  exact Ideal.mul_mem_right _ _
    ((IsLocalRing.mem_maximalIdeal _).mpr v.irreducible_mk_uniformizer.not_isUnit)

/-- Differentials with at most a simple pole form a submodule at every place. -/
def simplePoleDifferentials (v : Place K F) : Submodule K Ω[F⁄K] where
  carrier := {ω | v.HasSimplePoleAt ω}
  zero_mem' := v.hasSimplePoleAt_zero
  add_mem' hω hη := hω.add hη
  smul_mem' c _ hω := hω.smul c

/-- Multiplying the actual differential coefficient by the uniformizer gives an
integral coefficient. The nonzero coordinate makes the coefficient unique. -/
def simplePoleIntegralCoefficient (v : Place K F) (hcoord : v.dCoord ≠ 0) :
    simplePoleDifferentials v →ₗ[K] v.toValuationSubring where
  toFun ω := ⟨v.uniformizer * v.differentialCoeff ω, by
    obtain ⟨f, hf, hω⟩ := ω.property
    rw [v.differentialCoeff_unique_of_ne_zero hcoord hω]
    exact hf⟩
  map_add' x y := by
    obtain ⟨f, _hf, hx⟩ := x.property
    obtain ⟨g, _hg, hy⟩ := y.property
    apply Subtype.ext
    change v.uniformizer * v.differentialCoeff ((x : Ω[F⁄K]) + y) =
      v.uniformizer * v.differentialCoeff x + v.uniformizer * v.differentialCoeff y
    have hxy : (x : Ω[F⁄K]) + y = (f + g) • v.dCoord := by
      rw [add_smul, ← hx, ← hy]
    rw [v.differentialCoeff_unique_of_ne_zero hcoord hxy,
      v.differentialCoeff_unique_of_ne_zero hcoord hx,
      v.differentialCoeff_unique_of_ne_zero hcoord hy, mul_add]
  map_smul' c x := by
    obtain ⟨f, _hf, hx⟩ := x.property
    apply Subtype.ext
    change v.uniformizer * v.differentialCoeff (c • (x : Ω[F⁄K])) =
      algebraMap K F c * (v.uniformizer * v.differentialCoeff x)
    have hcx : c • (x : Ω[F⁄K]) = (algebraMap K F c * f) • v.dCoord := by
      rw [mul_smul, algebraMap_smul, ← hx]
    rw [v.differentialCoeff_unique_of_ne_zero hcoord hcx,
      v.differentialCoeff_unique_of_ne_zero hcoord hx, mul_left_comm]

/-- The actual simple-pole residue takes values in the residue field of the place. -/
def simplePoleResidue (v : Place K F) (hcoord : v.dCoord ≠ 0) :
    simplePoleDifferentials v →ₗ[K] v.ResidueField :=
  ((IsScalarTower.toAlgHom K v.toValuationSubring v.ResidueField).toLinearMap).comp
    (simplePoleIntegralCoefficient v hcoord)

/-- The residue is the reduction of the uniformizer times the actual coefficient. -/
theorem simplePoleResidue_eq (v : Place K F) (hcoord : v.dCoord ≠ 0)
    (ω : simplePoleDifferentials v) {f : F}
    (hω : (ω : Ω[F⁄K]) = f • v.dCoord) (hf : v.uniformizer * f ∈ v.toValuationSubring) :
    simplePoleResidue v hcoord ω =
      IsLocalRing.residue v.toValuationSubring ⟨v.uniformizer * f, hf⟩ := by
  change algebraMap v.toValuationSubring v.ResidueField
    (simplePoleIntegralCoefficient v hcoord ω) = _
  rw [IsLocalRing.ResidueField.algebraMap_eq]
  apply congrArg (IsLocalRing.residue v.toValuationSubring)
  apply Subtype.ext
  change v.uniformizer * v.differentialCoeff ω = v.uniformizer * f
  rw [v.differentialCoeff_unique_of_ne_zero hcoord hω]

/-- The existing base-field residue predicate is precisely the base-field part of
the actual residue-field-valued map. -/
theorem simplePoleResidue_eq_algebraMap_iff (v : Place K F) (hcoord : v.dCoord ≠ 0)
    (ω : simplePoleDifferentials v) (a : K) :
    simplePoleResidue v hcoord ω = algebraMap K v.ResidueField a ↔
      v.HasSimpleResidue ω a := by
  constructor
  · intro h
    obtain ⟨f, hf, hω⟩ := ω.property
    exact ⟨f, hω, hf, (simplePoleResidue_eq v hcoord ω hω hf).symm.trans h⟩
  · rintro ⟨f, hω, hf, hr⟩
    exact (simplePoleResidue_eq v hcoord ω hω hf).trans hr


end Place

section Polar

variable (K F)

/-- The space of differentials regular off the selected places and with at most simple poles
there. -/
def polarDifferentials (S : Set (Place K F)) : Submodule K Ω[F⁄K] where
  carrier := {ω | ∀ v : Place K F, (v ∉ S → v.IsRegularAt ω) ∧ (v ∈ S → v.HasSimplePoleAt ω)}
  zero_mem' v := ⟨fun _ => v.isRegularAt_zero, fun _ => v.hasSimplePoleAt_zero⟩
  add_mem' hω hη v :=
    ⟨fun hv => ((hω v).1 hv).add ((hη v).1 hv), fun hv => ((hω v).2 hv).add ((hη v).2 hv)⟩
  smul_mem' c _ hω v := ⟨fun hv => ((hω v).1 hv).smul c, fun hv => ((hω v).2 hv).smul c⟩

variable {K F}

theorem mem_polarDifferentials_iff {S : Set (Place K F)} {ω : Ω[F⁄K]} :
    ω ∈ polarDifferentials K F S ↔
      ∀ v : Place K F, (v ∉ S → v.IsRegularAt ω) ∧ (v ∈ S → v.HasSimplePoleAt ω) :=
  Iff.rfl

theorem hasSimplePoleAt_of_mem_polarDifferentials {S : Set (Place K F)} {ω : Ω[F⁄K]}
    (h : ω ∈ polarDifferentials K F S) (v : Place K F) : v.HasSimplePoleAt ω := by
  by_cases hv : v ∈ S
  · exact (h v).2 hv
  · exact ((h v).1 hv).hasSimplePoleAt

theorem regularDifferentials_le_polarDifferentials (S : Set (Place K F)) :
    regularDifferentials K F ≤ polarDifferentials K F S := fun ω hω v =>
  ⟨fun _ => hω v, fun _ => (show v.IsRegularAt ω from hω v).hasSimplePoleAt⟩

theorem polarDifferentials_mono {S T : Set (Place K F)} (h : S ⊆ T) :
    polarDifferentials K F S ≤ polarDifferentials K F T := fun _ hω v =>
  ⟨fun hv => (hω v).1 fun hs => hv (h hs), fun _ => hasSimplePoleAt_of_mem_polarDifferentials hω v⟩

theorem polarDifferentials_empty : polarDifferentials K F ∅ = regularDifferentials K F := by
  refine le_antisymm (fun ω hω v => (hω v).1 (Set.notMem_empty v)) ?_
  exact regularDifferentials_le_polarDifferentials ∅

end Polar

section Glued

variable (K F)

/-- The residue-field-valued residue of a polar differential at a specified place. -/
def polarSimpleResidue (S : Set (Place K F)) (v : Place K F) (hcoord : v.dCoord ≠ 0) :
    polarDifferentials K F S →ₗ[K] v.ResidueField :=
  (Place.simplePoleResidue v hcoord).comp
    (Submodule.inclusion
      (show polarDifferentials K F S ≤ Place.simplePoleDifferentials v from
        fun _ hω => hasSimplePoleAt_of_mem_polarDifferentials hω v))

/-- A gluing identifies the residue fields of its two branches. The chosen local
coordinates must have nonzero differential so that the actual residues are well defined. -/
structure PolarGluingData (S : Set (Place K F × Place K F)) where
  /-- The residue-field identification at each pair of branches, fixing the base field. -/
  residueEquiv : ∀ s : S, s.val.1.ResidueField ≃ₐ[K] s.val.2.ResidueField
  /-- The first chosen local coordinate has nonzero differential. -/
  fst_dCoord_ne_zero : ∀ s : S, s.val.1.dCoord ≠ 0
  /-- The second chosen local coordinate has nonzero differential. -/
  snd_dCoord_ne_zero : ∀ s : S, s.val.2.dCoord ≠ 0

/-- There is no residue comparison to choose for an empty gluing. -/
def PolarGluingData.empty : PolarGluingData K F ∅ where
  residueEquiv s := False.elim s.property
  fst_dCoord_ne_zero s := False.elim s.property
  snd_dCoord_ne_zero s := False.elim s.property

/-- The sum of the two actual residues, in the second branch's residue field at each pair. -/
def polarPairResidueSum (S : Set (Place K F × Place K F)) (glue : PolarGluingData K F S) :
    (polarDifferentials K F (Prod.fst '' S) × polarDifferentials K F (Prod.snd '' S)) →ₗ[K]
      (∀ s : S, s.val.2.ResidueField) :=
  LinearMap.pi fun s =>
    ((glue.residueEquiv s).toLinearMap.comp
      ((polarSimpleResidue K F _ s.val.1 (glue.fst_dCoord_ne_zero s)).comp
        (LinearMap.fst K _ _))) +
      ((polarSimpleResidue K F _ s.val.2 (glue.snd_dCoord_ne_zero s)).comp
        (LinearMap.snd K _ _))

/-- A polar pair is glued exactly when its actual residue-field-valued sums vanish. -/
def IsGluedPolarPair (S : Set (Place K F × Place K F)) (glue : PolarGluingData K F S)
    (ω : Ω[F⁄K] × Ω[F⁄K]) : Prop :=
  ∃ (h₁ : ω.1 ∈ polarDifferentials K F (Prod.fst '' S))
    (h₂ : ω.2 ∈ polarDifferentials K F (Prod.snd '' S)),
    polarPairResidueSum K F S glue (⟨ω.1, h₁⟩, ⟨ω.2, h₂⟩) = 0

/-- The actual kernel of the residue-sum map, embedded in the ambient pair of
differential spaces. Every element satisfies the gluing condition. -/
def gluedPolarDifferentials (S : Set (Place K F × Place K F))
    (glue : PolarGluingData K F S) : Submodule K (Ω[F⁄K] × Ω[F⁄K]) :=
  (LinearMap.ker (polarPairResidueSum K F S glue)).map
    ((polarDifferentials K F (Prod.fst '' S)).subtype.prodMap
      (polarDifferentials K F (Prod.snd '' S)).subtype)

variable {K F}

/-- Membership in the glued space is the residue condition itself. -/
theorem mem_gluedPolarDifferentials_iff {S : Set (Place K F × Place K F)}
    (glue : PolarGluingData K F S) {ω : Ω[F⁄K] × Ω[F⁄K]} :
    ω ∈ gluedPolarDifferentials K F S glue ↔ IsGluedPolarPair K F S glue ω := by
  rw [gluedPolarDifferentials, Submodule.mem_map]
  constructor
  · rintro ⟨⟨x, y⟩, h, rfl⟩
    exact ⟨x.property, y.property, h⟩
  · rintro ⟨h₁, h₂, h⟩
    exact ⟨(⟨ω.1, h₁⟩, ⟨ω.2, h₂⟩), h, rfl⟩

theorem mem_gluedPolarDifferentials_of_isGluedPolarPair {S : Set (Place K F × Place K F)}
    {glue : PolarGluingData K F S} {ω : Ω[F⁄K] × Ω[F⁄K]}
    (h : IsGluedPolarPair K F S glue ω) : ω ∈ gluedPolarDifferentials K F S glue :=
  (mem_gluedPolarDifferentials_iff glue).mpr h

/-- Taking the span does not add any pairs violating the residue condition. -/
theorem gluedPolarDifferentials_eq_span (S : Set (Place K F × Place K F))
    (glue : PolarGluingData K F S) :
    gluedPolarDifferentials K F S glue =
      Submodule.span K {ω | IsGluedPolarPair K F S glue ω} := by
  apply le_antisymm
  · intro ω h
    exact Submodule.subset_span ((mem_gluedPolarDifferentials_iff glue).mp h)
  · exact Submodule.span_le.mpr fun _ h =>
      mem_gluedPolarDifferentials_of_isGluedPolarPair h

theorem gluedPolarDifferentials_le_prod (S : Set (Place K F × Place K F))
    (glue : PolarGluingData K F S) :
    gluedPolarDifferentials K F S glue ≤
      (polarDifferentials K F (Prod.fst '' S)).prod (polarDifferentials K F (Prod.snd '' S)) := by
  intro ω h
  obtain ⟨h₁, h₂, _⟩ := (mem_gluedPolarDifferentials_iff glue).mp h
  exact ⟨h₁, h₂⟩

/-- The actual residue condition implies the original base-field-valued residue equation
whenever both residues lie in the base field. It also constrains nonrational residues. -/
theorem IsGluedPolarPair.base_residue_add_eq_zero
    {S : Set (Place K F × Place K F)} {glue : PolarGluingData K F S}
    {ω : Ω[F⁄K] × Ω[F⁄K]} (h : IsGluedPolarPair K F S glue ω) (s : S)
    (a b : K) (ha : s.val.1.HasSimpleResidue ω.1 a)
    (hb : s.val.2.HasSimpleResidue ω.2 b) : a + b = 0 := by
  obtain ⟨h₁, h₂, hz⟩ := h
  have heq := congrFun hz s
  change glue.residueEquiv s
      (polarSimpleResidue K F _ s.val.1 (glue.fst_dCoord_ne_zero s) ⟨ω.1, h₁⟩) +
    polarSimpleResidue K F _ s.val.2 (glue.snd_dCoord_ne_zero s) ⟨ω.2, h₂⟩ = 0 at heq
  have hleft : polarSimpleResidue K F _ s.val.1
      (glue.fst_dCoord_ne_zero s) ⟨ω.1, h₁⟩ = algebraMap K s.val.1.ResidueField a :=
    (Place.simplePoleResidue_eq_algebraMap_iff s.val.1
      (glue.fst_dCoord_ne_zero s)
      ⟨ω.1, hasSimplePoleAt_of_mem_polarDifferentials h₁ s.val.1⟩ a).mpr ha
  have hright : polarSimpleResidue K F _ s.val.2
      (glue.snd_dCoord_ne_zero s) ⟨ω.2, h₂⟩ = algebraMap K s.val.2.ResidueField b :=
    (Place.simplePoleResidue_eq_algebraMap_iff s.val.2
      (glue.snd_dCoord_ne_zero s)
      ⟨ω.2, hasSimplePoleAt_of_mem_polarDifferentials h₂ s.val.2⟩ b).mpr hb
  rw [hleft, hright, (glue.residueEquiv s).commutes a, ← map_add] at heq
  exact (algebraMap K s.val.2.ResidueField).injective
    (heq.trans (map_zero (algebraMap K s.val.2.ResidueField)).symm)

variable (K F) in
/-- Projection of a glued polar differential pair onto its first polar differential. -/
def gluedPolarDifferentials.fst (S : Set (Place K F × Place K F))
    (glue : PolarGluingData K F S) :
    gluedPolarDifferentials K F S glue →ₗ[K] polarDifferentials K F (Prod.fst '' S) :=
  ((LinearMap.fst K Ω[F⁄K] Ω[F⁄K]).domRestrict _).codRestrict _ fun ω =>
    (gluedPolarDifferentials_le_prod S glue ω.property).1

variable (K F) in
/-- Projection of a glued polar differential pair onto its second polar differential. -/
def gluedPolarDifferentials.snd (S : Set (Place K F × Place K F))
    (glue : PolarGluingData K F S) :
    gluedPolarDifferentials K F S glue →ₗ[K] polarDifferentials K F (Prod.snd '' S) :=
  ((LinearMap.snd K Ω[F⁄K] Ω[F⁄K]).domRestrict _).codRestrict _ fun ω =>
    (gluedPolarDifferentials_le_prod S glue ω.property).2

@[simp]
theorem gluedPolarDifferentials.coe_fst_apply (S : Set (Place K F × Place K F))
    (glue : PolarGluingData K F S) (ω : gluedPolarDifferentials K F S glue) :
    (gluedPolarDifferentials.fst K F S glue ω : Ω[F⁄K]) = (ω : Ω[F⁄K] × Ω[F⁄K]).1 := rfl

@[simp]
theorem gluedPolarDifferentials.coe_snd_apply (S : Set (Place K F × Place K F))
    (glue : PolarGluingData K F S) (ω : gluedPolarDifferentials K F S glue) :
    (gluedPolarDifferentials.snd K F S glue ω : Ω[F⁄K]) = (ω : Ω[F⁄K] × Ω[F⁄K]).2 := rfl

theorem prod_regularDifferentials_le_gluedPolarDifferentials_empty :
    (regularDifferentials K F).prod (regularDifferentials K F) ≤
      gluedPolarDifferentials K F ∅ (PolarGluingData.empty K F) := by
  rintro ω ⟨h₁, h₂⟩
  apply mem_gluedPolarDifferentials_of_isGluedPolarPair
  have hfst : ω.1 ∈ polarDifferentials K F (Prod.fst '' (∅ : Set (Place K F × Place K F))) := by
    rw [Set.image_empty, polarDifferentials_empty]
    exact h₁
  have hsnd : ω.2 ∈ polarDifferentials K F (Prod.snd '' (∅ : Set (Place K F × Place K F))) := by
    rw [Set.image_empty, polarDifferentials_empty]
    exact h₂
  refine ⟨hfst, hsnd, ?_⟩
  exact funext fun s => False.elim s.property

end Glued

end AlgebraicCurve

end
