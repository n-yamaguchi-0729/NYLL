/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuativeExtension
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# The actual inertia fixed field of a finite local Galois extension

The fixed field of the kernel of the residue action is unramified over the
base. The remaining extension has degree and ramification index equal to the
original ramification index. The upper field keeps its given valuation and
topology; only the intermediate field receives the existing spectral structure.
-/

@[expose] public section

noncomputable section

namespace LocalFieldTheory

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

universe u v

variable (K : Type u) (L : Type v)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- The fixed field of the actual kernel of the residue-field action. -/
def inertiaSubfield : IntermediateField K L :=
  IntermediateField.fixedField (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker

/-- The upper degree is the cardinality of actual inertia, hence the original
ramification index. -/
theorem finrank_inertiaSubfield :
    Module.finrank (inertiaSubfield K L) L =
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] := by
  rw [inertiaSubfield, IntermediateField.finrank_fixedField_eq_card]
  exact galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_ramificationIdx K L

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [FiniteDimensional K L] in
/-- Normality of the residue kernel makes its fixed field Galois over the base. -/
theorem inertiaSubfield_isGalois : IsGalois K (inertiaSubfield K L) := by
  unfold inertiaSubfield
  infer_instance

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [IsGalois K L] in
/-- The upper extension is Galois by the fixed-field theorem. -/
theorem inertiaSubfield_top_isGalois : IsGalois (inertiaSubfield K L) L := by
  unfold inertiaSubfield
  exact IsGalois.of_fixed_field L (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker

attribute [local instance] inertiaSubfield_isGalois inertiaSubfield_top_isGalois

/-- The existing spectral norm on the actual inertia fixed field. -/
@[reducible]
def inertiaSubfieldNormedField : NontriviallyNormedField (inertiaSubfield K L) :=
  finiteExtensionSpectralNormedField K (inertiaSubfield K L)

attribute [local instance] inertiaSubfieldNormedField

/-- The uniform structure of the same spectral norm, fixed explicitly because
the intermediate field also has an inherited subtype structure. -/
@[reducible]
def inertiaSubfieldUniformSpace : UniformSpace (inertiaSubfield K L) :=
  (inertiaSubfieldNormedField K L).toUniformSpace

attribute [local instance] inertiaSubfieldUniformSpace

/-- The topology of the specified spectral uniform structure. -/
@[reducible]
def inertiaSubfieldTopologicalSpace : TopologicalSpace (inertiaSubfield K L) :=
  (inertiaSubfieldUniformSpace K L).toTopologicalSpace

attribute [local instance] inertiaSubfieldTopologicalSpace

/-- The valuative relation of that same spectral norm. -/
@[reducible]
def inertiaSubfieldValuativeRel : ValuativeRel (inertiaSubfield K L) :=
  finiteExtensionSpectralValuativeRel K (inertiaSubfield K L)

attribute [local instance] inertiaSubfieldValuativeRel

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] [IsGalois K L] in
/-- The inertia fixed field is a local field for the specified spectral structure. -/
theorem inertiaSubfieldIsNonarchimedeanLocalField :
    IsNonarchimedeanLocalField (inertiaSubfield K L) :=
  finiteExtensionSpectralIsNonarchimedeanLocalField K (inertiaSubfield K L)

attribute [local instance] inertiaSubfieldIsNonarchimedeanLocalField

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] [IsGalois K L] in
/-- The lower spectral valuation extends the given base valuation. -/
theorem inertiaSubfield_base_hasExtension :
    (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation (inertiaSubfield K L)) :=
  finiteExtensionSpectralValuation_hasExtension K (inertiaSubfield K L)

attribute [local instance] inertiaSubfield_base_hasExtension

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- The lower integer ring is the actual integral closure of the base integers. -/
theorem inertiaSubfield_base_isIntegralClosure :
    IsIntegralClosure 𝒪[inertiaSubfield K L] 𝒪[K] (inertiaSubfield K L) :=
  localCompleteDVF_integerRing_isIntegralClosure K (inertiaSubfield K L)

attribute [local instance] inertiaSubfield_base_isIntegralClosure

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- The upper given valuation extends the spectral valuation of the inertia field. -/
theorem inertiaSubfield_top_hasExtension :
    (ValuativeRel.valuation (inertiaSubfield K L)).HasExtension (ValuativeRel.valuation L) :=
  valuation_hasExtension_of_integralClosure_tower K (inertiaSubfield K L) L

attribute [local instance] inertiaSubfield_top_hasExtension

/-- The upper integer ring is the actual integral closure over the inertia field. -/
theorem inertiaSubfield_top_isIntegralClosure :
    IsIntegralClosure 𝒪[L] 𝒪[inertiaSubfield K L] L :=
  localCompleteDVF_integerRing_isIntegralClosure (inertiaSubfield K L) L

attribute [local instance] inertiaSubfield_top_isIntegralClosure

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- The lower integer ring is finite over the base integers. -/
theorem inertiaSubfield_base_moduleFinite : Module.Finite 𝒪[K] 𝒪[inertiaSubfield K L] :=
  localCompleteDVF_integerRing_moduleFinite K (inertiaSubfield K L)

attribute [local instance] inertiaSubfield_base_moduleFinite

/-- Every automorphism over the inertia fixed field acts trivially on the
original upper residue field. -/
theorem inertiaSubfield_top_residue_ker :
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure (inertiaSubfield K L) L).ker = ⊤ := by
  let I := (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker
  apply top_unique
  intro σ _
  apply (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal
    (inertiaSubfield K L) L σ).2
  intro x
  let τ : I := (IntermediateField.subgroupEquivAlgEquiv I).symm σ
  have hx :=
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal
      K L τ.1).1 τ.2 x
  have hvalue :
      galoisGroupIntegerRingEquivOfIsIntegralClosure (inertiaSubfield K L) L σ x =
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L τ.1 x := by
    apply Subtype.ext
    rfl
  rw [hvalue]
  exact hx

/-- The upper extension has full ramification: its index equals its degree. -/
theorem inertiaSubfield_top_ramificationIdx_eq_finrank :
    (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[inertiaSubfield K L] =
      Module.finrank (inertiaSubfield K L) L := by
  rw [← galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_ramificationIdx
    (inertiaSubfield K L) L, inertiaSubfield_top_residue_ker]
  exact (Nat.card_congr (Subgroup.topEquiv :
    (⊤ : Subgroup Gal(L/inertiaSubfield K L)) ≃* Gal(L/inertiaSubfield K L)).toEquiv).trans
      (IsGalois.card_aut_eq_finrank (inertiaSubfield K L) L)

/-- The upper ramification index equals the original index. -/
theorem inertiaSubfield_top_ramificationIdx :
    (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[inertiaSubfield K L] =
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] :=
  (inertiaSubfield_top_ramificationIdx_eq_finrank K L).trans (finrank_inertiaSubfield K L)

/-- The lower extension is unramified at its actual valuation integer rings. -/
theorem inertiaSubfield_base_ramificationIdx :
    (𝓂[inertiaSubfield K L] : Ideal 𝒪[inertiaSubfield K L]).ramificationIdx 𝒪[K] = 1 := by
  let : Module.Finite 𝒪[inertiaSubfield K L] 𝒪[L] :=
    localCompleteDVF_integerRing_moduleFinite (inertiaSubfield K L) L
  let : Module.Finite 𝒪[K] 𝒪[L] := localCompleteDVF_integerRing_moduleFinite K L
  let : IsScalarTower 𝒪[K] 𝒪[inertiaSubfield K L] 𝒪[L] :=
    IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  have htower := Ideal.ramificationIdx_tower (R := 𝒪[K])
    (𝓂[inertiaSubfield K L] : Ideal 𝒪[inertiaSubfield K L]) (𝓂[L] : Ideal 𝒪[L])
  rw [inertiaSubfield_top_ramificationIdx K L] at htower
  apply Nat.eq_of_mul_eq_mul_right ((𝓂[L] : Ideal 𝒪[L]).ramificationIdx_pos 𝒪[K])
  rw [one_mul]
  exact htower.symm

/-- The proved lower index-one property supplies the existing unramified owner. -/
theorem inertiaSubfield_isUnramified : IsUnramifiedValuedExtension K (inertiaSubfield K L) :=
  ⟨inertiaSubfield_base_ramificationIdx K L⟩

end LocalFieldTheory
