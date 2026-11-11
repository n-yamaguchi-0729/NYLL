/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Nyll.AbelianVarieties.Geometry.Torsion.Degree
public import Nyll.AbelianVarieties.Reduction.Inertia
public import Nyll.ValuedFieldTheory.Ramification.InertiaLifting
public import Nyll.SchemeTheory.RingTheory.Ramification.UnramifiedDVR
public import Nyll.SchemeTheory.Morphisms.SectionRigidity
public import Nyll.AbelianVarieties.Basic
public import Nyll.AbelianVarieties.NeronModels.Basic
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.AbelianVarieties.Geometry.AbelianSchemeBaseChange
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawEtaleSchemeNsmul
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFiniteFlatSchemeNsmul
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFormallyUnramifiedSchemeNsmulIsUnit
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Torsion descent and injective specialization

Construct a finite Galois field of torsion coordinates. Use unramifiedness and the Néron
mapping property to specialize torsion injectively, with the expected torsion cardinality.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace AbelianVarieties.NOSProofs.TorsionSplittingField

namespace TorsionFieldDescent

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs in
open RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing in
theorem nsmul_coe (G : RelativeGroupLaw K f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n :=
  GoodReductionJacobian.RelativeGroupLaw.nsmul_coe_eq_comp_schemeNsmul G n x

theorem one_coe (G : RelativeGroupLaw K f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) :
    (G.one t).1 = t ≫ (G.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  have h := G.one_natural (𝟙 (Spec (CommRingCat.of K))) t t (Category.comp_id t)
  rw [← h]
  rfl

theorem isTorsionPoint_iff_comp (G : RelativeGroupLaw K f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : SchemeHomOver t f) :
    G.IsTorsionPoint t n x ↔
      x.1 ≫ G.schemeNsmul n = t ≫ (G.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  rw [RelativeGroupLaw.isTorsionPoint_def, Subtype.ext_iff, nsmul_coe, one_coe]

theorem mono_unit (G : RelativeGroupLaw K f) :
    Mono (G.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  have : Mono ((G.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f) := by
    rw [(G.one (𝟙 (Spec (CommRingCat.of K)))).2]
    infer_instance
  exact mono_of_mono _ f

theorem kerFst_comp (G : RelativeGroupLaw K f) (n : ℕ) :
    pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f =
      G.schemeKerStr n := by
  calc pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f
      = pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫
          (G.schemeNsmul n ≫ f) := by rw [G.schemeNsmul_over n]
    _ = (pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫
          (G.one (𝟙 (Spec (CommRingCat.of K)))).1) ≫ f := by
        rw [← Category.assoc, pullback.condition]
    _ = G.schemeKerStr n := by
        rw [Category.assoc, (G.one (𝟙 (Spec (CommRingCat.of K)))).2, Category.comp_id]

theorem isTorsionPoint_of_ker (G : RelativeGroupLaw K f) (n : ℕ) {T : Scheme.{u}}
    (y : T ⟶ G.schemeKer n) (t : T ⟶ Spec (CommRingCat.of K)) (ht : y ≫ G.schemeKerStr n = t) :
    ∃ h : (y ≫ pullback.fst _ _) ≫ f = t,
      G.IsTorsionPoint t n ⟨y ≫ pullback.fst _ _, h⟩ := by
  refine ⟨by rw [Category.assoc, kerFst_comp, ht], ?_⟩
  rw [isTorsionPoint_iff_comp]
  change (y ≫ pullback.fst _ _) ≫ G.schemeNsmul n = t ≫ _
  rw [Category.assoc, pullback.condition, ← Category.assoc, ht]

section Kernel

variable (G : RelativeGroupLaw K f) (n : ℕ) [IsAffine (G.schemeKer n)]

/-- The base algebra map on the affine torsion kernel. -/
noncomputable def kerAlgMap : CommRingCat.of K ⟶ Γ(G.schemeKer n, ⊤) :=
  Spec.preimage ((G.schemeKer n).isoSpec.inv ≫ G.schemeKerStr n)

theorem spec_kerAlgMap :
    Spec.map (kerAlgMap G n) = (G.schemeKer n).isoSpec.inv ≫ G.schemeKerStr n :=
  Spec.map_preimage _

variable {T : Type u} [CommRing T] [Algebra K T]

/-- Convert a coordinate algebra homomorphism to a torsion-kernel point. -/
noncomputable def homToPt (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of T)
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K T)) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) f :=
  ⟨Spec.map φ ≫ (G.schemeKer n).isoSpec.inv ≫
      pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1, by
    rw [Category.assoc, Category.assoc, kerFst_comp, ← hφ, Spec.map_comp, spec_kerAlgMap]⟩

@[scoped simp]
theorem homToPt_coe (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of T)
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K T)) :
    (homToPt G n φ hφ).1 = Spec.map φ ≫ (G.schemeKer n).isoSpec.inv ≫
      pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1 :=
  rfl

theorem isTorsionPoint_homToPt (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of T)
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K T)) :
    G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K T))) n (homToPt G n φ hφ) := by
  have hy : (Spec.map φ ≫ (G.schemeKer n).isoSpec.inv) ≫ G.schemeKerStr n =
      Spec.map (CommRingCat.ofHom (algebraMap K T)) := by
    rw [Category.assoc, ← spec_kerAlgMap, ← Spec.map_comp, hφ]
  obtain ⟨h, ht⟩ := isTorsionPoint_of_ker G n _ _ hy
  have he : homToPt G n φ hφ = ⟨_, h⟩ := Subtype.ext (by simp only [homToPt_coe, Category.assoc])
  rw [he]
  exact ht

theorem homToPt_comp_coe (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of T)
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K T))
    {T' : Type u} [CommRing T'] [Algebra K T'] (j : CommRingCat.of T ⟶ CommRingCat.of T')
    (hj : kerAlgMap G n ≫ (φ ≫ j) = CommRingCat.ofHom (algebraMap K T')) :
    (homToPt G n (φ ≫ j) hj).1 = Spec.map j ≫ (homToPt G n φ hφ).1 := by
  simp only [homToPt_coe, Spec.map_comp, Category.assoc]

theorem eq_of_homToPt_coe_eq {φ φ' : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of T}
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K T))
    (hφ' : kerAlgMap G n ≫ φ' = CommRingCat.ofHom (algebraMap K T))
    (h : (homToPt G n φ hφ).1 = (homToPt G n φ' hφ').1) : φ = φ' := by
  have : Mono (G.one (𝟙 (Spec (CommRingCat.of K)))).1 := mono_unit G
  have : Mono ((G.schemeKer n).isoSpec.inv ≫
      pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1) := inferInstance
  rw [homToPt_coe, homToPt_coe] at h
  exact Spec.map_injective ((cancel_mono _).mp h)

theorem exists_homToPt_eq (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) f)
    (hx : G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K T))) n x) :
    ∃ (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of T)
      (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K T)), homToPt G n φ hφ = x := by
  rw [isTorsionPoint_iff_comp] at hx
  refine ⟨Spec.preimage (pullback.lift x.1 _ hx ≫ (G.schemeKer n).isoSpec.hom), ?_, ?_⟩
  · apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, spec_kerAlgMap, Category.assoc, Iso.hom_inv_id_assoc,
      pullback.lift_snd]
  · apply Subtype.ext
    simp only [homToPt_coe, Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc,
      pullback.lift_fst]

end Kernel

section Structure

variable (G : RelativeGroupLaw K f)
  (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
    G.mul t x y = G.mul t y x)
  (hA : AbelianSchemePropertyBundle K f) (n : ℕ) (hn : IsUnit (n : K))

include hcomm hA hn in
theorem isFinite_schemeKerStr : IsFinite (G.schemeKerStr n) := by
  have : IsFinite (G.schemeNsmul n) :=
    (GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_schemeNsmul_of_isUnit
    G hA hcomm n hn).1
  infer_instance

include hcomm hA hn in
theorem isAffine_schemeKer : IsAffine (G.schemeKer n) := by
  have : IsFinite (G.schemeKerStr n) := isFinite_schemeKerStr G hcomm hA n hn
  exact isAffine_of_isAffineHom (G.schemeKerStr n)

include hcomm hn in
theorem formallyUnramified_schemeKerStr (d : ℕ) [SmoothOfRelativeDimension d f] :
    FormallyUnramified (G.schemeKerStr n) := by
  have : Etale (G.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
    G hcomm d n hn
  infer_instance

theorem finite_kerAlgMap [IsAffine (G.schemeKer n)] (hfin : IsFinite (G.schemeKerStr n)) :
    (kerAlgMap G n).hom.Finite := by
  rw [← IsFinite.SpecMap_iff, spec_kerAlgMap]
  infer_instance

theorem formallyUnramified_kerAlgMap [IsAffine (G.schemeKer n)]
    (h : FormallyUnramified (G.schemeKerStr n)) : (kerAlgMap G n).hom.FormallyUnramified := by
  rw [← HasRingHomProperty.Spec_iff (P := @FormallyUnramified), spec_kerAlgMap]
  have : MorphismProperty.RespectsIso (@FormallyUnramified.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := @FormallyUnramified.{u})
  exact MorphismProperty.RespectsIso.precomp (P := @FormallyUnramified.{u}) _ _ h

end Structure

section Field

variable (G : RelativeGroupLaw K f) (n : ℕ) [IsAffine (G.schemeKer n)]
  (Ω : Type u) [Field Ω] [Algebra K Ω]

/-- All coordinates of torsion points over the ambient field. -/
def torsionCoords : Set Ω :=
  {y | ∃ (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of Ω),
    kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K Ω) ∧ ∃ a, φ.hom a = y}

/-- The intermediate field generated by torsion coordinates. -/
noncomputable def torsionField : IntermediateField K Ω :=
  IntermediateField.adjoin K (torsionCoords G n Ω)

theorem image_torsionCoords_subset (σ : Ω ≃ₐ[K] Ω) :
    σ '' torsionCoords G n Ω ⊆ torsionCoords G n Ω := by
  rintro _ ⟨y, ⟨φ, hφ, a, rfl⟩, rfl⟩
  refine ⟨φ ≫ CommRingCat.ofHom (σ : Ω →+* Ω), ?_, a, rfl⟩
  rw [← Category.assoc, hφ, ← CommRingCat.ofHom_comp]
  congr 1
  exact σ.toAlgHom.comp_algebraMap

theorem normal_torsionField [Normal K Ω] : Normal K (torsionField G n Ω) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro σ
  rw [torsionField, IntermediateField.adjoin_map]
  exact IntermediateField.adjoin.mono K _ _ (image_torsionCoords_subset G n Ω σ)

/-- Restrict torsion-point coordinates to their generated field. -/
noncomputable def restrictHom (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of Ω)
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K Ω)) :
    Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of (torsionField G n Ω) :=
  CommRingCat.ofHom (φ.hom.codRestrict (torsionField G n Ω)
    (fun a => IntermediateField.subset_adjoin K _ ⟨φ, hφ, a, rfl⟩))

theorem restrictHom_comp (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of Ω)
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K Ω)) :
    restrictHom G n Ω φ hφ ≫ CommRingCat.ofHom (algebraMap (torsionField G n Ω) Ω) = φ := by
  ext a
  rfl

theorem kerAlgMap_comp_restrictHom (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of Ω)
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K Ω)) :
    kerAlgMap G n ≫ restrictHom G n Ω φ hφ =
      CommRingCat.ofHom (algebraMap K (torsionField G n Ω)) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply Subtype.ext
  change φ.hom ((kerAlgMap G n).hom r) = ((algebraMap K (torsionField G n Ω) r : _) : Ω)
  have := congrArg (fun ψ : CommRingCat.of K ⟶ CommRingCat.of Ω => ψ.hom r) hφ
  exact this

theorem exists_descent (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f)
    (hx : G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) n x) :
    ∃ z : SchemeHomOver
        (Spec.map (CommRingCat.ofHom (algebraMap K (torsionField G n Ω)))) f,
      G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K (torsionField G n Ω)))) n z ∧
      Spec.map (CommRingCat.ofHom (algebraMap (torsionField G n Ω) Ω)) ≫ z.1 = x.1 := by
  obtain ⟨φ, hφ, rfl⟩ := exists_homToPt_eq G n x hx
  refine ⟨homToPt G n (restrictHom G n Ω φ hφ) (kerAlgMap_comp_restrictHom G n Ω φ hφ),
    isTorsionPoint_homToPt G n _ _, ?_⟩
  have hj : kerAlgMap G n ≫ (restrictHom G n Ω φ hφ ≫
      CommRingCat.ofHom (algebraMap (torsionField G n Ω) Ω)) =
      CommRingCat.ofHom (algebraMap K Ω) := by rw [restrictHom_comp, hφ]
  rw [← homToPt_comp_coe G n _ (kerAlgMap_comp_restrictHom G n Ω φ hφ) _ hj]
  simp only [homToPt_coe, restrictHom_comp]

theorem eq_one_of_forall_comp_eq [Normal K Ω] (τ : torsionField G n Ω ≃ₐ[K] torsionField G n Ω)
    (hτ : ∀ z : SchemeHomOver
        (Spec.map (CommRingCat.ofHom (algebraMap K (torsionField G n Ω)))) f,
      G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K (torsionField G n Ω)))) n z →
      Spec.map (CommRingCat.ofHom (τ : torsionField G n Ω →+* torsionField G n Ω)) ≫ z.1 = z.1) :
    τ = 1 := by
  have hfix : ∀ y ∈ torsionCoords G n Ω, τ.liftNormal Ω y = y := by
    rintro _ ⟨φ, hφ, a, rfl⟩
    have hj : kerAlgMap G n ≫ (restrictHom G n Ω φ hφ ≫
        CommRingCat.ofHom (τ : torsionField G n Ω →+* torsionField G n Ω)) =
        CommRingCat.ofHom (algebraMap K (torsionField G n Ω)) := by
      rw [← Category.assoc, kerAlgMap_comp_restrictHom, ← CommRingCat.ofHom_comp]
      congr 1
      exact τ.toAlgHom.comp_algebraMap
    have h1 := hτ _ (isTorsionPoint_homToPt G n _ (kerAlgMap_comp_restrictHom G n Ω φ hφ))
    rw [← homToPt_comp_coe G n _ (kerAlgMap_comp_restrictHom G n Ω φ hφ) _ hj] at h1
    have h2 := eq_of_homToPt_coe_eq G n hj (kerAlgMap_comp_restrictHom G n Ω φ hφ) h1
    have h3 := congrArg (fun ψ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of (torsionField G n Ω) =>
      algebraMap (torsionField G n Ω) Ω (ψ.hom a)) h2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at h3
    rw [RingHom.coe_coe, ← AlgEquiv.liftNormal_commutes τ Ω] at h3
    exact h3
  have hfixL : ∀ y ∈ torsionField G n Ω, τ.liftNormal Ω y = y := by
    intro y hy
    induction hy using IntermediateField.adjoin_induction with
    | mem y hy => exact hfix y hy
    | algebraMap r => exact (τ.liftNormal Ω).commutes r
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  apply AlgEquiv.ext
  intro w
  apply Subtype.ext
  rw [AlgEquiv.one_apply]
  calc ((τ w : torsionField G n Ω) : Ω) = τ.liftNormal Ω (w : Ω) :=
        (AlgEquiv.liftNormal_commutes τ Ω w).symm
    _ = w := hfixL _ w.2

end Field

end TorsionFieldDescent
end AbelianVarieties.NOSProofs.TorsionSplittingField

open AbelianVarieties.NOSProofs.TorsionSplittingField.TorsionFieldDescent

namespace GoodReductionJacobian.RelativeGroupLaw

theorem exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one (K : Type u)
    [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (G : RelativeGroupLaw K f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (hA : AbelianSchemePropertyBundle K f) (d : ℕ) [SmoothOfRelativeDimension d f]
    (n : ℕ) (hn : (n : K) ≠ 0)
    (Ω : Type u) [Field Ω] [Algebra K Ω] [Normal K Ω] :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧
      (∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f,
        G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) n x →
        ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) f,
          G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z ∧
          Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ z.1 = x.1) ∧
      (∀ τ : L ≃ₐ[K] L,
        (∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) f,
          G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z →
          Spec.map (CommRingCat.ofHom (τ : L →+* L)) ≫ z.1 = z.1) → τ = 1) := by
  have hnU : IsUnit (n : K) := isUnit_iff_ne_zero.mpr hn
  have : IsAffine (G.schemeKer n) := isAffine_schemeKer G hcomm hA n hnU
  let : Algebra K Γ(G.schemeKer n, ⊤) := (kerAlgMap G n).hom.toAlgebra
  have : Module.Finite K Γ(G.schemeKer n, ⊤) :=
    finite_kerAlgMap G n (isFinite_schemeKerStr G hcomm hA n hnU)
  have : Algebra.FormallyUnramified K Γ(G.schemeKer n, ⊤) :=
    formallyUnramified_kerAlgMap G n (formallyUnramified_schemeKerStr G hcomm n hnU d)
  obtain ⟨L₁, hfd₁, hgal₁, hL₁⟩ :=
    Algebra.FormallyUnramified.exists_isGalois_forall_algHom_apply_mem K Γ(G.schemeKer n, ⊤) Ω
  have hle : torsionField G n Ω ≤ L₁ := by
    rw [torsionField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨φ, hφ, a, rfl⟩
    let φa : Γ(G.schemeKer n, ⊤) →ₐ[K] Ω :=
      { φ.hom with
        commutes' := fun r => congrArg (fun ψ : CommRingCat.of K ⟶ CommRingCat.of Ω => ψ.hom r) hφ }
    exact hL₁ φa a
  have : FiniteDimensional K L₁ := hfd₁
  have : IsGalois K L₁ := hgal₁
  have : FiniteDimensional K (torsionField G n Ω) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  have : Algebra.IsSeparable K (torsionField G n Ω) :=
    Algebra.IsSeparable.of_algHom K _ (IntermediateField.inclusion hle)
  have : Normal K (torsionField G n Ω) := normal_torsionField G n Ω
  have : IsGalois K (torsionField G n Ω) := IsGalois.mk
  exact ⟨torsionField G n Ω, inferInstance, inferInstance, fun x hx => exists_descent G n Ω x hx,
    fun τ hτ => eq_one_of_forall_comp_eq G n Ω τ hτ⟩

end GoodReductionJacobian.RelativeGroupLaw

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_eq_of_isTorsionPoint_of_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace AbelianVarieties.NOSProofs.TorsionSectionRigidity

namespace TorsionRigidity

theorem preconnectedSpace_of_forall_specializes {α : Type*} [TopologicalSpace α] (c : α)
    (hc : ∀ x : α, x ⤳ c) : PreconnectedSpace α := by
  refine ⟨fun U V hU hV hUV hxU' hyV' => ?_⟩
  obtain ⟨x, -, hxU⟩ := hxU'
  obtain ⟨y, -, hyV⟩ := hyV'
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hxV : x ∉ V := fun hxV => by
    have : x ∈ Set.univ ∩ (U ∩ V) := ⟨Set.mem_univ x, hxU, hxV⟩
    rw [h] at this; exact this
  have hyU : y ∉ U := fun hyU => by
    have : y ∈ Set.univ ∩ (U ∩ V) := ⟨Set.mem_univ y, hyU, hyV⟩
    rw [h] at this; exact this
  have hcV : c ∈ Vᶜ := (hc x).mem_closed hV.isClosed_compl hxV
  have hcU : c ∈ Uᶜ := (hc y).mem_closed hU.isClosed_compl hyU
  rcases hUV (Set.mem_univ c) with hcU' | hcV'
  · exact hcU hcU'
  · exact hcV hcV'

scoped instance preconnectedSpace_spec_of_isLocalRing (O : Type u) [CommRing O] [IsLocalRing O] :
    PreconnectedSpace (Spec (CommRingCat.of O)) :=
  preconnectedSpace_of_forall_specializes (IsLocalRing.closedPoint O)
    (fun x => IsLocalRing.specializes_closedPoint x)

scoped instance connectedSpace_spec_of_isLocalRing (O : Type u) [CommRing O] [IsLocalRing O] :
    ConnectedSpace (Spec (CommRingCat.of O)) where
  toNonempty := ⟨IsLocalRing.closedPoint O⟩

section Torsion

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs in
open RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing in
theorem coe_nsmul_eq_comp_schemeNsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n :=
  GoodReductionJacobian.RelativeGroupLaw.nsmul_coe_eq_comp_schemeNsmul G n x

theorem coe_comp_schemeNsmul_of_isTorsionPoint (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) {x : SchemeHomOver t f}
    (hx : G.IsTorsionPoint t n x) :
    x.1 ≫ G.schemeNsmul n = (G.one t).1 := by
  rw [← coe_nsmul_eq_comp_schemeNsmul, hx]

variable [IsLocalRing R]

theorem eq_of_isTorsionPoint_of_comp_eq [IsSeparated f] [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R))
    {T : Scheme.{u}} [PreconnectedSpace T] (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) (hx : G.IsTorsionPoint t n x) (hy : G.IsTorsionPoint t n y)
    {Z : Scheme.{u}} [Nonempty Z] (p : Z ⟶ T) (hp : p ≫ x.1 = p ≫ y.1) :
    x = y := by
  have : FormallyUnramified (G.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
      G hcomm n hn
  have : LocallyOfFiniteType (G.schemeNsmul n ≫ f) := by
    rw [G.schemeNsmul_over n]; infer_instance
  have : LocallyOfFiniteType (G.schemeNsmul n) := locallyOfFiniteType_of_comp _ f
  have : IsSeparated (G.schemeNsmul n ≫ f) := by
    rw [G.schemeNsmul_over n]; infer_instance
  have : IsSeparated (G.schemeNsmul n) := IsSeparated.of_comp _ f
  apply Subtype.ext
  refine AlgebraicGeometry.eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace
    (G.schemeNsmul n) x.1 y.1 ?_ p hp
  rw [coe_comp_schemeNsmul_of_isTorsionPoint G t n hx,
    coe_comp_schemeNsmul_of_isTorsionPoint G t n hy]

theorem eq_of_isTorsionPoint_of_residue_comp_eq [IsSeparated f] [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R))
    (O : Type u) [CommRing O] [IsLocalRing O]
    (t : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) (hx : G.IsTorsionPoint t n x) (hy : G.IsTorsionPoint t n y)
    (hres : Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ x.1 =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ y.1) :
    x = y :=
  eq_of_isTorsionPoint_of_comp_eq G hcomm n hn t x y hx hy
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) hres

end Torsion

end TorsionRigidity
end AbelianVarieties.NOSProofs.TorsionSectionRigidity

open AbelianVarieties.NOSProofs.TorsionSectionRigidity

namespace GoodReductionJacobian.RelativeGroupLaw

theorem eq_of_isTorsionPoint_of_comp_eq
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R))
    {T : Scheme.{u}} [PreconnectedSpace T] (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) (hx : G.IsTorsionPoint t n x) (hy : G.IsTorsionPoint t n y)
    {Z : Scheme.{u}} [Nonempty Z] (p : Z ⟶ T) (hp : p ≫ x.1 = p ≫ y.1) :
    x = y :=
  TorsionRigidity.eq_of_isTorsionPoint_of_comp_eq G hcomm n hn t x y hx hy p hp

end GoodReductionJacobian.RelativeGroupLaw

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_smooth.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open scoped TensorProduct nonZeroDivisors

universe u

namespace AbelianVarieties.NOSProofs.SmoothTorsionSpecialization

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
namespace RelativeGroupLaw
open _root_.GoodReductionJacobian.RelativeGroupLaw
namespace TorsionSpecialization
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

section GenericFibreOfBase

variable (R : Type u) [CommRing R]
  (K : Type u) [Field K] [Algebra R K]
  (R' : Type u) [CommRing R'] [Algebra R R']
  (L : Type u) [Field L] [Algebra R' L] [Algebra K L] [Algebra R L]
  [IsScalarTower R R' L] [IsScalarTower R K L]

local notation "P" => R' ⊗[R] K
local notation "tR'" => Spec.map (CommRingCat.ofHom (algebraMap R R'))
local notation "ιK" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The tensor-product map induced by the two compatible embeddings into the fraction field. -/
noncomputable def β : P →ₐ[R] L :=
  Algebra.TensorProduct.lift ((Algebra.ofId R' L).restrictScalars R) ((Algebra.ofId K
    L).restrictScalars R)
    (fun _ _ => Commute.all _ _)

theorem β_tmul (r' : R') (k : K) : β R K R' L (r' ⊗ₜ k) = algebraMap R' L r' * algebraMap K L k :=
  Algebra.TensorProduct.lift_tmul _ _ _ r' k

theorem β_comp_includeLeft :
    (β R K R' L).toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = algebraMap R' L := by
  ext r'
  change β R K R' L (r' ⊗ₜ 1) = _
  rw [β_tmul, map_one, _root_.mul_one]

theorem β_comp_includeRight :
    (β R K R' L).toRingHom.comp
      ((Algebra.TensorProduct.includeRight : K →ₐ[R] P) : K →+* P) = algebraMap K L := by
  ext k
  change β R K R' L (1 ⊗ₜ k) = _
  rw [β_tmul, map_one, _root_.one_mul]

variable [IsDomain R] [IsFractionRing R K]

theorem isUnit_includeLeft (m : Algebra.algebraMapSubmonoid R' R⁰) :
    IsUnit (Algebra.TensorProduct.includeLeftRingHom (R := R) (B := K) (m : R')) := by
  obtain ⟨_, ⟨r, hr, rfl⟩⟩ := m
  change IsUnit ((algebraMap R R' r) ⊗ₜ[R] (1 : K))
  have h : (algebraMap R R' r) ⊗ₜ[R] (1 : K) = (1 : R') ⊗ₜ[R] (algebraMap R K r) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [h]
  have hu : IsUnit (algebraMap R K r) := by
    refine isUnit_iff_ne_zero.mpr ?_
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr
  exact hu.map (Algebra.TensorProduct.includeRight : K →ₐ[R] P)

variable [IsLocalization (Algebra.algebraMapSubmonoid R' R⁰) L]

/-- The inverse map obtained from the localization universal property. -/
noncomputable def α : L →+* P :=
  IsLocalization.lift (M := Algebra.algebraMapSubmonoid R' R⁰)
    (g := (Algebra.TensorProduct.includeLeftRingHom : R' →+* P)) (isUnit_includeLeft R K R')

omit [Algebra K L] [Algebra R L] [IsScalarTower R R' L] [IsScalarTower R K L] in
theorem α_algebraMap (r' : R') : α R K R' L (algebraMap R' L r') = r' ⊗ₜ 1 :=
  IsLocalization.lift_eq _ r'

theorem β_comp_α : (β R K R' L).toRingHom.comp (α R K R' L) = RingHom.id L := by
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R' R⁰)
  ext r'
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [α_algebraMap]
  change β R K R' L (r' ⊗ₜ 1) = _
  rw [β_tmul, map_one, _root_.mul_one]

theorem α_comp_algebraMap :
    (α R K R' L).comp (algebraMap K L) =
      ((Algebra.TensorProduct.includeRight : K →ₐ[R] P) : K →+* P) := by
  apply IsLocalization.ringHom_ext R⁰ (S := K)
  ext r
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R' L, α_algebraMap]
  change (algebraMap R R' r) ⊗ₜ[R] (1 : K) = (1 : R') ⊗ₜ[R] (algebraMap R K r)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/-- The generic base-change morphism into the spectrum of the common fraction field. -/
noncomputable def e : pullback tR' ιK ⟶ Spec (CommRingCat.of L) :=
  (pullbackSpecIso R R' K).hom ≫ Spec.map (CommRingCat.ofHom (α R K R' L))

/-- The comparison morphism from the common fraction field to the generic base change. -/
noncomputable def j : Spec (CommRingCat.of L) ⟶ pullback tR' ιK :=
  Spec.map (CommRingCat.ofHom (β R K R' L).toRingHom) ≫ (pullbackSpecIso R R' K).inv

theorem j_e : j R K R' L ≫ e R K R' L = 𝟙 _ := by
  rw [j, e, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    β_comp_α, CommRingCat.ofHom_id]
  exact Spec.map_id _

omit [IsDomain R] [IsFractionRing R K]
  [IsLocalization (Algebra.algebraMapSubmonoid R' R⁰) L] in
theorem j_fst : j R K R' L ≫ pullback.fst tR' ιK = Spec.map (CommRingCat.ofHom (algebraMap R' L)) :=
    by
  rw [j, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    β_comp_includeLeft]

theorem e_snd : e R K R' L ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = pullback.snd tR' ιK :=
    by
  rw [e, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, α_comp_algebraMap,
    pullbackSpecIso_hom_snd]

end GenericFibreOfBase

section Restrict

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}

theorem baseChangePointToBase_genericFibreRestrict {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t g) :
    baseChangePointToBase (specGenericFibreInclusion R K) (genericFibreRestrict R K g t a) =
      GoodReductionJacobian.schemeHomOverComp (pullback.fst t (specGenericFibreInclusion R K))
        pullback.condition a :=
  Subtype.ext (genericFibreRestrict_coe_comp_fst R K g t a)

theorem genericFibreRestrict_mul (LB : RelativeGroupLaw R g) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t g) :
    genericFibreRestrict R K g t (LB.mul t a b) =
      (LB.genericFibre K).mul (pullback.snd t (specGenericFibreInclusion R K))
        (genericFibreRestrict R K g t a) (genericFibreRestrict R K g t b) := by
  apply (baseChangePointEquiv (specGenericFibreInclusion R K) (f := g) _).injective
  change baseChangePointToBase _ _ = baseChangePointToBase _ _
  rw [baseChangePointToBase_mul, baseChangePointToBase_genericFibreRestrict,
    baseChangePointToBase_genericFibreRestrict, baseChangePointToBase_genericFibreRestrict,
    LB.mul_natural]

theorem genericFibreRestrict_one (LB : RelativeGroupLaw R g) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    genericFibreRestrict R K g t (LB.one t) =
      (LB.genericFibre K).one (pullback.snd t (specGenericFibreInclusion R K)) := by
  apply (baseChangePointEquiv (specGenericFibreInclusion R K) (f := g) _).injective
  change baseChangePointToBase _ _ = baseChangePointToBase _ _
  rw [baseChangePointToBase_one, baseChangePointToBase_genericFibreRestrict, LB.one_natural]

theorem genericFibreRestrict_nsmul (LB : RelativeGroupLaw R g) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (a : SchemeHomOver t g) :
    genericFibreRestrict R K g t (LB.nsmul t n a) =
      (LB.genericFibre K).nsmul (pullback.snd t (specGenericFibreInclusion R K)) n
        (genericFibreRestrict R K g t a) := by
  induction n with
  | zero => exact genericFibreRestrict_one K LB t
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, genericFibreRestrict_mul, ih]

theorem isTorsionPoint_of_genericFibreRestrict (LB : RelativeGroupLaw R g) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (hinj : Function.Injective (genericFibreRestrict R K g t))
    (n : ℕ) (a : SchemeHomOver t g)
    (ha : (LB.genericFibre K).IsTorsionPoint (pullback.snd t (specGenericFibreInclusion R K)) n
      (genericFibreRestrict R K g t a)) :
    LB.IsTorsionPoint t n a := by
  apply hinj
  rw [genericFibreRestrict_nsmul, genericFibreRestrict_one]
  exact ha

end Restrict

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}

theorem preconnectedSpace_spec (S : Type u) [CommRing S] [IsDomain S] :
    PreconnectedSpace (Spec (CommRingCat.of S) : Scheme.{u}) := by
  have : IrreducibleSpace (PrimeSpectrum S) := inferInstance
  have : IrreducibleSpace (Spec (CommRingCat.of S) : Scheme.{u}) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum S))
  infer_instance

theorem nonempty_spec (S : Type u) [CommRing S] [Nontrivial S] :
    Nonempty (Spec (CommRingCat.of S) : Scheme.{u}) :=
  inferInstanceAs (Nonempty (PrimeSpectrum S))

theorem main (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (n : ℕ) (hn : IsUnit (n : R))
    (R' : Type u) [CommRing R'] [IsDomain R'] [Algebra R R']
    (hsm : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (L : Type u) [Field L] [Algebra R' L] [Algebra K L] [Algebra R L]
    [IsScalarTower R R' L] [IsScalarTower R K L]
    [IsLocalization (Algebra.algebraMapSubmonoid R' R⁰) L]
    (k' : Type u) [Field k'] [Algebra R k'] (ψ : R' →ₐ[R] k') :
    ∃ r : {z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L)))
              (pullback.snd g (specGenericFibreInclusion R K)) //
            (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z}
          → {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
            LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) n y},
      Function.Injective r ∧
      ∀ z, ∃ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g,
        LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R R'))) n x ∧
        Spec.map (CommRingCat.ofHom (algebraMap R' L)) ≫ x.1 =
          z.1.1 ≫ pullback.fst g (specGenericFibreInclusion R K) ∧
        (r z).1.1 = Spec.map (CommRingCat.ofHom (ψ : R' →+* k')) ≫ x.1 := by
  let ι := specGenericFibreInclusion R K
  have hι : ι = Spec.map (CommRingCat.ofHom (algebraMap R K)) := rfl
  let T : Scheme.{u} := Spec (CommRingCat.of R')
  let t : T ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R R'))
  let sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let ee : pullback t ι ⟶ Spec (CommRingCat.of L) := e R K R' L
  let jj : Spec (CommRingCat.of L) ⟶ pullback t ι := j R K R' L
  have hje : jj ≫ ee = 𝟙 _ := j_e R K R' L
  have hjfst : jj ≫ pullback.fst t ι = Spec.map (CommRingCat.ofHom (algebraMap R' L)) :=
    j_fst R K R' L
  have hesnd : ee ≫ sL = pullback.snd t ι := e_snd R K R' L
  have hbij := hN.neronMapping T t hsm
  let p : Spec (CommRingCat.of k') ⟶ T := Spec.map (CommRingCat.ofHom (ψ : R' →+* k'))
  have hp : p ≫ t = Spec.map (CommRingCat.ofHom (algebraMap R k')) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap
  have ext : ∀ z : {z : SchemeHomOver sL (pullback.snd g ι) //
      (LB.genericFibre K).IsTorsionPoint sL n z},
      ∃ x : SchemeHomOver t g, LB.IsTorsionPoint t n x ∧
        genericFibreRestrict R K g t x = GoodReductionJacobian.schemeHomOverComp ee hesnd z.1 := by
    intro z
    obtain ⟨x, hx⟩ := hbij.2 (GoodReductionJacobian.schemeHomOverComp ee hesnd z.1)
    refine ⟨x, ?_, hx⟩
    apply isTorsionPoint_of_genericFibreRestrict K LB t hbij.1 n x
    rw [hx]
    exact (LB.genericFibre K).isTorsionPoint_schemeHomOverComp sL _ ee hesnd n z.2
  choose xOf hxTors hxRes using ext
  have hxi : ∀ z, Spec.map (CommRingCat.ofHom (algebraMap R' L)) ≫ (xOf z).1 =
      z.1.1 ≫ pullback.fst g ι := by
    intro z
    have h := congrArg Subtype.val (hxRes z)
    have h' := genericFibreRestrict_coe_comp_fst R K g t (xOf z)
    rw [h] at h'
    rw [← hjfst, Category.assoc, ← h', GoodReductionJacobian.schemeHomOverComp_coe]
    simp only [Category.assoc]
    rw [← Category.assoc, hje, Category.id_comp]
  let r : {z : SchemeHomOver sL (pullback.snd g ι) // (LB.genericFibre K).IsTorsionPoint sL n z} →
      {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
        LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) n y} :=
    fun z => ⟨GoodReductionJacobian.schemeHomOverComp p hp (xOf z),
      LB.isTorsionPoint_schemeHomOverComp t _ p hp n (hxTors z)⟩
  refine ⟨r, ?_, fun z => ⟨xOf z, hxTors z, hxi z, rfl⟩⟩
  intro z₁ z₂ h
  have h1 : p ≫ (xOf z₁).1 = p ≫ (xOf z₂).1 :=
    congrArg (fun w : {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
        LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) n y} => w.1.1) h
  have : IsSeparated g := hN.separated
  have : LocallyOfFiniteType g := hN.locallyOfFiniteType
  have : PreconnectedSpace T := preconnectedSpace_spec R'
  have : Nonempty (Spec (CommRingCat.of k') : Scheme.{u}) := nonempty_spec k'
  have hx12 : xOf z₁ = xOf z₂ :=
    GoodReductionJacobian.RelativeGroupLaw.eq_of_isTorsionPoint_of_comp_eq LB hcomm n hn t
      (xOf z₁) (xOf z₂) (hxTors z₁) (hxTors z₂) p h1
  apply Subtype.ext
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [← hxi z₁, ← hxi z₂, hx12]
  · rw [z₁.1.2, z₂.1.2]

end Main

end GoodReductionJacobian.RelativeGroupLaw.TorsionSpecialization
end AbelianVarieties.NOSProofs.SmoothTorsionSpecialization

open AbelianVarieties.NOSProofs.SmoothTorsionSpecialization.GoodReductionJacobian
open RelativeGroupLaw.TorsionSpecialization (main)

namespace GoodReductionJacobian.RelativeGroupLaw

theorem exists_injective_specialize_isTorsionPoint_of_smooth
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (n : ℕ) (hn : IsUnit (n : R))
    (R' : Type u) [CommRing R'] [IsDomain R'] [Algebra R R']
    (hsm : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (L : Type u) [Field L] [Algebra R' L] [Algebra K L] [Algebra R L]
    [IsScalarTower R R' L] [IsScalarTower R K L]
    [IsLocalization (Algebra.algebraMapSubmonoid R' R⁰) L]
    (k' : Type u) [Field k'] [Algebra R k'] (ψ : R' →ₐ[R] k') :
    ∃ r : {z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L)))
              (pullback.snd g (specGenericFibreInclusion R K)) //
            (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z}
          → {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
            LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) n y},
      Function.Injective r ∧
      ∀ z, ∃ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g,
        LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R R'))) n x ∧
        Spec.map (CommRingCat.ofHom (algebraMap R' L)) ≫ x.1 =
          z.1.1 ≫ pullback.fst g (specGenericFibreInclusion R K) ∧
        (r z).1.1 = Spec.map (CommRingCat.ofHom (ψ : R' →+* k')) ≫ x.1 :=
  main K LB hcomm hN n hn R' hsm L k' ψ

end GoodReductionJacobian.RelativeGroupLaw

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_isUnramifiedAt.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open scoped nonZeroDivisors

universe u

namespace AbelianVarieties.NOSProofs.UnramifiedTorsionSpecialization

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
namespace RelativeGroupLaw
open _root_.GoodReductionJacobian.RelativeGroupLaw
namespace TorsionSpecializationDedekind
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

section EtaleNbhd

variable (R : Type u) [CommRing R]
  (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S]
  (P : Ideal S) [P.IsPrime] [Algebra.IsUnramifiedAt R P]

theorem exists_formallyUnramified_away :
    ∃ f : S, f ∉ P ∧ Algebra.FormallyUnramified R (Localization.Away f) := by
  have hmem : (⟨P, inferInstance⟩ : PrimeSpectrum S) ∈ Algebra.unramifiedLocus R S := by
    change Algebra.IsUnramifiedAt R P
    infer_instance
  obtain ⟨v, ⟨f, rfl⟩, hfv, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem
      Algebra.isOpen_unramifiedLocus
  refine ⟨f, ?_, Algebra.basicOpen_subset_unramifiedLocus_iff.mp hsub⟩
  exact hfv

variable [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [FaithfulSMul R S] (f : S)

theorem smooth_specMap_away [Algebra.FormallyUnramified R (Localization.Away f)] :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) := by
  have : Module.Flat R (Localization.Away f) := Module.Flat.trans R S (Localization.Away f)
  have : Algebra.FiniteType R (Localization.Away f) :=
    Algebra.FiniteType.trans (S := S) inferInstance inferInstance
  have : Algebra.FinitePresentation R (Localization.Away f) :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  have : Algebra.Etale R (Localization.Away f) := Algebra.Etale.of_formallyUnramified_of_flat
  have : Algebra.Smooth R (Localization.Away f) := inferInstance
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap R (Localization.Away f)).Smooth
  rw [RingHom.smooth_algebraMap]
  infer_instance

end EtaleNbhd

section GenericFibre

variable (R : Type u) [CommRing R] [IsDomain R]
  (S : Type u) [CommRing S] [IsDomain S] [Algebra R S]
  (L : Type u) [Field L] [Algebra S L] [Algebra R L]
  [IsScalarTower R S L] [IsFractionRing S L] [IsIntegralClosure S R L]
  (f : S) (hf : f ≠ 0)

/-- Embed a principal localization into the fraction field. -/
noncomputable def awayToField : Localization.Away f →+* L :=
  IsLocalization.Away.lift f (g := algebraMap S L)
    (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective S L)).mpr hf))

omit [IsDomain S] in
theorem awayToField_comp : (awayToField S L f hf).comp (algebraMap S (Localization.Away f)) =
    algebraMap S L :=
  IsLocalization.Away.lift_comp f _

omit [IsDomain S] in
theorem awayToField_injective : Function.Injective (awayToField S L f hf) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) x
  have h := IsLocalization.mk'_spec (Localization.Away f) s m
  have h' := congrArg (awayToField S L f hf) h
  rw [map_mul, hx, zero_mul, ← RingHom.comp_apply, awayToField_comp] at h'
  have hs : s = 0 := (map_eq_zero_iff _ (IsFractionRing.injective S L)).mp h'.symm
  subst hs
  change IsLocalization.mk' (Localization.Away f) 0 m = 0
  exact IsLocalization.mk'_zero _

omit [IsDomain S] in
theorem isLocalization_away (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [IsScalarTower R K L] [Algebra.IsAlgebraic K L] :
    let : Algebra (Localization.Away f) L := (awayToField S L f hf).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away f) R⁰) L := by
  intro awayAlgebra
  have halg : ∀ x, algebraMap (Localization.Away f) L x = awayToField S L f hf x := fun _ => rfl
  have hSL : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L :=
    IsIntegralClosure.isLocalization R K L S
  have htower : ∀ s : S, algebraMap (Localization.Away f) L (algebraMap S _ s) = algebraMap S L s :=
    by
    intro s; rw [halg, ← RingHom.comp_apply, awayToField_comp]
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, r, hr, rfl⟩
    change IsUnit (algebraMap (Localization.Away f) L (algebraMap R (Localization.Away f) r))
    rw [IsScalarTower.algebraMap_apply R S (Localization.Away f), htower]
    exact IsLocalization.map_units L (M := Algebra.algebraMapSubmonoid S R⁰)
      ⟨algebraMap R S r, r, hr, rfl⟩
  · intro y
    obtain ⟨⟨s, ⟨_, r, hr, rfl⟩⟩, h⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid S R⁰) y
    refine ⟨⟨algebraMap S _ s, ⟨algebraMap R _ r, r, hr, rfl⟩⟩, ?_⟩
    change y * algebraMap (Localization.Away f) L (algebraMap R (Localization.Away f) r) =
      algebraMap (Localization.Away f) L (algebraMap S _ s)
    rw [IsScalarTower.algebraMap_apply R S (Localization.Away f), htower, htower]
    exact h
  · intro x₁ x₂ h
    rw [halg, halg] at h
    exact ⟨1, by rw [awayToField_injective S L f hf h]⟩

end GenericFibre

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}

theorem main (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (n : ℕ) (hn : IsUnit (n : R))
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (L : Type u) [Field L] [Algebra S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] [IsFractionRing S L]
    [IsIntegralClosure S R L] [Algebra.IsAlgebraic K L]
    (P : Ideal S) [P.IsPrime] [Algebra.IsUnramifiedAt R P]
    (k' : Type u) [Field k'] [Algebra R k'] (ψ : S →ₐ[R] k')
    (hψ : ∀ s : S, ψ s = 0 → s ∈ P) :
    ∃ r : {z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L)))
              (pullback.snd g (specGenericFibreInclusion R K)) //
            (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z}
          → {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
            LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) n y},
      Function.Injective r := by
  have : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective R S]
    intro a b h
    have h' := congrArg (algebraMap S L) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K L] at h'
    exact (IsFractionRing.injective R K) ((algebraMap K L).injective h')
  obtain ⟨f, hfP, hunr⟩ := exists_formallyUnramified_away R S P
  have : Algebra.FormallyUnramified R (Localization.Away f) := hunr
  have hf0 : f ≠ 0 := fun h => hfP (h ▸ P.zero_mem)
  let R' := Localization.Away f
  have : IsDomain R' :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) R'
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
  have hsm : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := smooth_specMap_away R S f
  let : Algebra R' L := (awayToField S L f hf0).toAlgebra
  have halg : ∀ x, algebraMap R' L x = awayToField S L f hf0 x := fun _ => rfl
  have : IsScalarTower S R' L := IsScalarTower.of_algebraMap_eq (fun s => by
    rw [halg, ← RingHom.comp_apply, awayToField_comp])
  have : IsScalarTower R R' L := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply R S R', ← IsScalarTower.algebraMap_apply S R' L,
      ← IsScalarTower.algebraMap_apply R S L])
  have : IsLocalization (Algebra.algebraMapSubmonoid R' R⁰) L := isLocalization_away R S L f hf0 K
  have hψf : IsUnit ((ψ : S →+* k') f) := isUnit_iff_ne_zero.mpr (fun h => hfP (hψ f h))
  let ψ₀ : R' →+* k' := IsLocalization.Away.lift f hψf
  have hψ₀ : ψ₀.comp (algebraMap S R') = (ψ : S →+* k') := IsLocalization.Away.lift_comp f hψf
  let ψ' : R' →ₐ[R] k' :=
    { ψ₀ with
      commutes' := fun r => by
        change ψ₀ (algebraMap R R' r) = algebraMap R k' r
        rw [IsScalarTower.algebraMap_apply R S R', ← RingHom.comp_apply, hψ₀]
        exact ψ.commutes r }
  obtain ⟨r, hr, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_injective_specialize_isTorsionPoint_of_smooth
      K LB hcomm hN n hn R' hsm L k' ψ'
  exact ⟨r, hr⟩

end Main

end GoodReductionJacobian.RelativeGroupLaw.TorsionSpecializationDedekind
end AbelianVarieties.NOSProofs.UnramifiedTorsionSpecialization

open AbelianVarieties.NOSProofs.UnramifiedTorsionSpecialization.GoodReductionJacobian
open RelativeGroupLaw.TorsionSpecializationDedekind (main)

namespace GoodReductionJacobian.RelativeGroupLaw

theorem exists_injective_specialize_isTorsionPoint_of_isUnramifiedAt
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (n : ℕ) (hn : IsUnit (n : R))
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (L : Type u) [Field L] [Algebra S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] [IsFractionRing S L]
    [IsIntegralClosure S R L] [Algebra.IsAlgebraic K L]
    (P : Ideal S) [P.IsPrime] [Algebra.IsUnramifiedAt R P]
    (k' : Type u) [Field k'] [Algebra R k'] (ψ : S →ₐ[R] k')
    (hψ : ∀ s : S, ψ s = 0 → s ∈ P) :
    ∃ r : {z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L)))
              (pullback.snd g (specGenericFibreInclusion R K)) //
            (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z}
          → {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
            LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) n y},
      Function.Injective r :=
  main K LB hcomm hN n hn S L P k' ψ hψ

end GoodReductionJacobian.RelativeGroupLaw

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Pointwise

universe u

namespace AbelianVarieties.NOSProofs.TorsionSpecializationInjection

namespace TorsionInjection

open AbelianVarieties.NOSProofs.TorsionInertia.GoodReductionJacobian.RelativeGroupLaw
open InertiaOnTorsion (baseChangePointToBase_nsmul)

section Transport

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

/-- Transport torsion points along an equality of structure morphisms. -/
def torsionEquivOfEq (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) (n : ℕ) :
    {x : SchemeHomOver t₁ f // G.IsTorsionPoint t₁ n x} ≃
      {x : SchemeHomOver t₂ f // G.IsTorsionPoint t₂ n x} := by
  subst h
  exact Equiv.refl _

variable {R' : Type u} [CommRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))

theorem isTorsionPoint_baseChange_iff (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ)
    (x : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f)) :
    (G.baseChange ι).IsTorsionPoint t' n x ↔
      G.IsTorsionPoint (t' ≫ ι) n (RelativeGroupLaw.baseChangePointToBase ι x) := by
  rw [RelativeGroupLaw.isTorsionPoint_def, RelativeGroupLaw.isTorsionPoint_def,
    ← baseChangePointToBase_nsmul, ← RelativeGroupLaw.baseChangePointToBase_one ι G t']
  constructor
  · intro h; rw [h]
  · intro h
    exact (RelativeGroupLaw.baseChangePointEquiv ι t').injective h

/-- Identify torsion points before and after base change. -/
noncomputable def torsionEquivBaseChange (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ) :
    {x : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f) //
        (G.baseChange ι).IsTorsionPoint t' n x} ≃
      {y : SchemeHomOver (t' ≫ ι) f // G.IsTorsionPoint (t' ≫ ι) n y} :=
  (RelativeGroupLaw.baseChangePointEquiv ι t').subtypeEquiv
    (fun x => isTorsionPoint_baseChange_iff ι G t' n x)

end Transport

section Count

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem finite_and_natCard_torsion (G : RelativeGroupLaw K f) (hc : G.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f) (d : ℕ) [SmoothOfRelativeDimension d f]
    (n : ℕ) (hn : (n : K) ≠ 0) (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] :
    Finite {x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f //
        G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) n x} ∧
      Nat.card {x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f //
        G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) n x} = n ^ (2 * d) := by
  set ι : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω)) with hι
  have hAΩ : AbelianSchemePropertyBundle Ω (pullback.snd f ι) := hA.baseChange_of_field ι
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (g : X ⟶ Y) => SmoothOfRelativeDimension d g) :=
    smoothOfRelativeDimension_isStableUnderBaseChange d
  have : SmoothOfRelativeDimension d (pullback.snd f ι) :=
    hbc.of_isPullback (IsPullback.of_hasPullback f ι) ‹SmoothOfRelativeDimension d f›
  have hcΩ : (G.baseChange ι).IsCommutative := RelativeGroupLaw.IsCommutative.baseChange ι hc
  have hnΩ : (n : Ω) ≠ 0 := by
    intro h
    apply hn
    apply (algebraMap K Ω).injective
    rw [map_natCast, h, map_zero]
  have hcard :=
    GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
      Ω (pullback.snd f ι) (G.baseChange ι) hcΩ hAΩ d n hnΩ
  let e := (torsionEquivBaseChange ι G (𝟙 _) n).trans (torsionEquivOfEq G (Category.id_comp ι) n)
  rw [Nat.card_congr e] at hcard
  refine ⟨?_, hcard⟩
  have hpos : n ^ (2 * d) ≠ 0 := by
    apply pow_ne_zero
    rintro rfl
    exact hn (Nat.cast_zero)
  exact Nat.finite_of_card_ne_zero (hcard ▸ hpos)

end Count

theorem epi_specMap_of_field {L Ω : Type u} [Field L] [Field Ω] (φ : L →+* Ω) :
    Epi (Spec.map (CommRingCat.ofHom φ)) := by
  have : Flat (Spec.map (CommRingCat.ofHom φ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let : Algebra L Ω := φ.toAlgebra
    change Module.Flat L Ω
    infer_instance
  have : Surjective (Spec.map (CommRingCat.ofHom φ)) := by
    refine ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

section ValuationInertia

variable {S L : Type u} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L]

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem mem_valuationSubringAtPrime_iff (v : HeightOneSpectrum S) (x : L) :
    x ∈ valuationSubringAtPrime L v ↔ v.valuation L x ≤ 1 := by
  rw [valuationSubringAtPrime_eq_valuationSubring, Valuation.mem_valuationSubring_iff]

theorem mem_nonunits_valuationSubringAtPrime_iff (v : HeightOneSpectrum S) (x : L) :
    x ∈ (valuationSubringAtPrime L v).nonunits ↔ v.valuation L x < 1 := by
  rw [ValuationSubring.mem_nonunits_iff_or, mem_valuationSubringAtPrime_iff, map_inv₀]
  by_cases hx : x = 0
  · subst hx
    simp only [map_zero, zero_lt_one, true_or]
  · have hpos : 0 < v.valuation L x := (Valuation.pos_iff _).mpr hx
    rw [or_iff_right hx, not_le, one_lt_inv₀ hpos]

theorem algebraMap_mem_valuationSubringAtPrime (v : HeightOneSpectrum S) (b : S) :
    algebraMap S L b ∈ valuationSubringAtPrime L v :=
  (mem_valuationSubringAtPrime_iff v _).mpr (v.valuation_le_one b)

theorem algebraMap_mem_nonunits_iff (v : HeightOneSpectrum S) (b : S) :
    algebraMap S L b ∈ (valuationSubringAtPrime L v).nonunits ↔ b ∈ v.asIdeal := by
  rw [mem_nonunits_valuationSubringAtPrime_iff, valuation_lt_one_iff_mem]

theorem mul_mem_nonunits {F : Type*} [Field F] (P : ValuationSubring F) {x y : F} (hx : x ∈ P)
    (hy : y ∈ P.nonunits) : x * y ∈ P.nonunits := by
  have hy' : y ∈ P := P.nonunits_subset hy
  have h := (ValuationSubring.coe_mem_nonunits_iff (a := (⟨x, hx⟩ : P) * ⟨y, hy'⟩)).mpr
    (Ideal.mul_mem_left _ _ (ValuationSubring.coe_mem_nonunits_iff.mp hy))
  exact h

theorem eq_valuationSubringAtPrime_of_centre (v : HeightOneSpectrum S) (P' : ValuationSubring L)
    (h1 : ∀ b : S, algebraMap S L b ∈ P')
    (h2 : ∀ b : S, algebraMap S L b ∈ P'.nonunits ↔ b ∈ v.asIdeal) :
    P' = valuationSubringAtPrime L v := by
  have hle : valuationSubringAtPrime L v ≤ P' := by
    rintro x ⟨a, s, hs, rfl⟩
    refine mul_mem (h1 a) ?_
    have hsn : algebraMap S L s ∉ P'.nonunits := fun h => hs ((h2 s).mp h)
    rw [ValuationSubring.mem_nonunits_iff_or, not_or] at hsn
    exact not_not.mp hsn.2
  have hne : P' ≠ ⊤ := by
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    have hbn : algebraMap S L b ∈ P'.nonunits := (h2 b).mpr hb
    rintro rfl
    rw [ValuationSubring.mem_nonunits_iff_or] at hbn
    rcases hbn with h | h
    · exact hb0 ((IsFractionRing.injective S L) (by rw [h, map_zero]))
    · exact h (ValuationSubring.mem_top _)
  exact (ValuationSubring.eq_of_le_of_ne_top _ hle hne).symm

theorem exists_sub_algebraMap_mem_nonunits (v : HeightOneSpectrum S) [v.asIdeal.IsMaximal]
    (e : valuationSubringAtPrime L v) :
    ∃ b : S, (e : L) - algebraMap S L b ∈ (valuationSubringAtPrime L v).nonunits := by
  obtain ⟨a, s, hs, he⟩ := e.2
  obtain ⟨t, i, hi, hti⟩ := Ideal.IsMaximal.exists_inv ‹v.asIdeal.IsMaximal› hs
  refine ⟨a * t, ?_⟩
  have hs0 : algebraMap S L s ≠ 0 := fun h =>
    (show s ∉ v.asIdeal from hs) (by
      rw [(IsFractionRing.injective S L) (by rw [h, map_zero] : algebraMap S L s = algebraMap S L
        0)]
      exact v.asIdeal.zero_mem)
  have key : (e : L) - algebraMap S L (a * t) =
      (algebraMap S L a * (algebraMap S L s)⁻¹) * algebraMap S L i := by
    have hi' : algebraMap S L i = 1 - algebraMap S L t * algebraMap S L s := by
      rw [← map_mul, ← map_one (algebraMap S L), ← map_sub, ← hti]; ring_nf
    rw [he, hi', map_mul]
    field_simp
  rw [key]
  exact mul_mem_nonunits _ ⟨a, s, hs, rfl⟩ ((algebraMap_mem_nonunits_iff v i).mpr hi)

end ValuationInertia

section IntegralClosure

variable {R : Type u} [CommRing R] [IsDomain R]
  {K : Type u} [Field K] [Algebra R K]
  {L : Type u} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

scoped instance smulCommClass_gal : SMulCommClass (L ≃ₐ[K] L) R L where
  smul_comm g r x := by
    rw [Algebra.smul_def, Algebra.smul_def, AlgEquiv.smul_def, AlgEquiv.smul_def, map_mul,
      IsScalarTower.algebraMap_apply R K L, AlgEquiv.commutes]

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (K L) in
theorem isFractionRing_integralClosure [IsFractionRing R K] [FiniteDimensional K L] :
    IsFractionRing (integralClosure R L) L :=
  integralClosure.isFractionRing_of_finite_extension K L

variable (K L) in
theorem module_finite_integralClosure [IsDiscreteValuationRing R] [IsFractionRing R K]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Module.Finite R (integralClosure R L) :=
  IsIntegralClosure.finite R K L (integralClosure R L)

variable (K L) in
theorem isDedekindDomain_integralClosure [IsDiscreteValuationRing R] [IsFractionRing R K]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsDedekindDomain (integralClosure R L) :=
  integralClosure.isDedekindDomain R K L

omit [Algebra R K] in
theorem isTorsionFree_integralClosure (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type u) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] :
    Module.IsTorsionFree R (integralClosure R L) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
  rw [Algebra.smul_def, mul_eq_zero] at h
  rcases h with h | h
  · left
    have h' : algebraMap R L r = 0 := by
      have := congrArg (algebraMap (integralClosure R L) L) h
      rwa [map_zero, ← IsScalarTower.algebraMap_apply] at this
    rw [IsScalarTower.algebraMap_apply R K L, map_eq_zero] at h'
    exact (IsFractionRing.injective R K) (by rw [h', map_zero])
  · exact Or.inr h

variable (K L) in
theorem isGaloisGroup_integralClosure [IsDiscreteValuationRing R] [IsFractionRing R K] [IsGalois K
    L]
    [IsFractionRing (integralClosure R L) L] :
    IsGaloisGroup (L ≃ₐ[K] L) R (integralClosure R L) :=
  IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) R (integralClosure R L) K L

omit [IsDomain R] in
theorem mem_inertiaSubgroupIn_of_mem_inertia [IsDedekindDomain (integralClosure R L)]
    [IsFractionRing (integralClosure R L) L]
    (v : HeightOneSpectrum (integralClosure R L)) [v.asIdeal.IsMaximal]
    (τ : L ≃ₐ[K] L) (hτ : τ ∈ v.asIdeal.inertia (L ≃ₐ[K] L)) :
    τ ∈ (valuationSubringAtPrime L v).inertiaSubgroupIn K := by
  set A₀ := valuationSubringAtPrime L v with hA₀
  have hρ : ∀ (g : L ≃ₐ[K] L) (b : integralClosure R L),
      g • algebraMap (integralClosure R L) L b = algebraMap (integralClosure R L) L (g • b) :=
    fun g b => rfl
  have h := (Ideal.mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits
    (G := L ≃ₐ[K] L) (algebraMap (integralClosure R L) L : integralClosure R L →+* L) hρ
    v.asIdeal A₀ (algebraMap_mem_valuationSubringAtPrime v) (algebraMap_mem_nonunits_iff v)
    (fun P' h1 h2 => eq_valuationSubringAtPrime_of_centre v P' h1 h2)
    (exists_sub_algebraMap_mem_nonunits v) τ).mp hτ
  obtain ⟨hstab, hres⟩ := h
  refine Subgroup.mem_map.mpr ⟨⟨τ, hstab⟩, ?_, rfl⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  ext r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  simp only [MulSemiringAction.toRingAut_apply, RingAut.one_apply]
  change (⟨τ, hstab⟩ : A₀.decompositionSubgroup K) • IsLocalRing.residue A₀ a = _
  rw [← IsLocalRing.ResidueField.residue_smul]
  exact Ideal.Quotient.eq.mpr ((ValuationSubring.coe_mem_nonunits_iff (A := A₀)).mp (hres a))

theorem isUnramifiedAt_of_inertia_eq_bot [IsDiscreteValuationRing R] [IsFractionRing R K]
    [FiniteDimensional K L] [IsGalois K L]
    [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L]
    [Module.Finite R (integralClosure R L)]
    (P : Ideal (integralClosure R L)) [P.IsMaximal] [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (h : P.inertia (L ≃ₐ[K] L) = ⊥) :
    Algebra.IsUnramifiedAt R P := by
  have : Module.IsTorsionFree R (integralClosure R L) :=
    isTorsionFree_integralClosure K L (R := R)
  have : IsGaloisGroup (L ≃ₐ[K] L) R (integralClosure R L) :=
    isGaloisGroup_integralClosure K L (R := R)
  have hm : IsLocalRing.maximalIdeal R ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    apply hm
    rw [Ideal.LiesOver.over (P := (⊥ : Ideal (integralClosure R L)))
      (p := IsLocalRing.maximalIdeal R), Ideal.under_def, Ideal.comap_bot_of_injective]
    intro a b hab
    apply IsFractionRing.injective R K
    have := congrArg (algebraMap (integralClosure R L) L) hab
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K L,
      (algebraMap K L).injective.eq_iff] at this
  obtain ⟨he, hsep⟩ :=
    (Ideal.inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable (L ≃ₐ[K] L) hm P).mp h
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (IsLocalRing.maximalIdeal R) P (L ≃ₐ[K] L),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal R) P hm] at he
  have : Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R L ⧸ P) := hsep
  exact Algebra.isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable
    (IsLocalRing.maximalIdeal R) P hP0 he

end IntegralClosure

section Point

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {S : Type u} [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]

theorem exists_ideal_algHom_of_isAlgClosed (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra R k']
    (hk' : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R k' r = 0)
    (hker : RingHom.ker (algebraMap R S) ≠ ⊤) :
    ∃ (P : Ideal S) (_ : P.IsMaximal) (_ : P.LiesOver (IsLocalRing.maximalIdeal R))
      (ψ : S →ₐ[R] k'), ∀ s : S, ψ s = 0 → s ∈ P := by
  obtain ⟨P, hPmax, hPover⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S)
    (IsLocalRing.maximalIdeal R) (IsLocalRing.le_maximalIdeal hker)
  have : P.IsMaximal := hPmax
  have hover : P.LiesOver (IsLocalRing.maximalIdeal R) := ⟨hPover.symm⟩
  set k₀ := IsLocalRing.ResidueField R with hk₀
  let : Algebra k₀ k' :=
    (Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (algebraMap R k') hk').toAlgebra
  have : IsScalarTower R k₀ k' := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R k' r =
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (algebraMap R k') hk'
        (Ideal.Quotient.mk _ r)
    rw [Ideal.Quotient.lift_mk])
  let : Field (S ⧸ P) := Ideal.Quotient.field P
  have : Algebra.IsIntegral k₀ (S ⧸ P) := Algebra.IsIntegral.tower_top R
  have : Algebra.IsAlgebraic k₀ (S ⧸ P) := Algebra.IsIntegral.isAlgebraic
  have : Module.IsTorsionFree k₀ (S ⧸ P) :=
    Module.IsTorsionFree.of_smul_eq_zero (fun r m h => smul_eq_zero.mp h)
  have : Module.IsTorsionFree k₀ k' :=
    Module.IsTorsionFree.of_smul_eq_zero (fun r m h => smul_eq_zero.mp h)
  let φ₀ : (S ⧸ P) →ₐ[k₀] k' := IsAlgClosed.lift
  let ψ : S →ₐ[R] k' :=
    { (φ₀ : (S ⧸ P) →+* k').comp (Ideal.Quotient.mk P) with
      commutes' := fun r => by
        change φ₀ (Ideal.Quotient.mk P (algebraMap R S r)) = algebraMap R k' r
        rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
          IsScalarTower.algebraMap_apply R k₀ (S ⧸ P), φ₀.commutes,
          ← IsScalarTower.algebraMap_apply] }
  refine ⟨P, hPmax, hover, ψ, fun s hs => ?_⟩
  change φ₀ (Ideal.Quotient.mk P s) = 0 at hs
  rw [map_eq_zero] at hs
  exact Ideal.Quotient.eq_zero_iff_mem.mp hs

end Point

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {L : Type u} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

include K in
theorem ne_bot_of_liesOver_maximalIdeal (P : Ideal (integralClosure R L))
    [P.LiesOver (IsLocalRing.maximalIdeal R)] : P ≠ ⊥ := by
  rintro rfl
  apply IsDiscreteValuationRing.not_a_field R
  rw [Ideal.LiesOver.over (P := (⊥ : Ideal (integralClosure R L)))
    (p := IsLocalRing.maximalIdeal R), Ideal.under_def, Ideal.comap_bot_of_injective]
  intro a b hab
  apply IsFractionRing.injective R K
  have := congrArg (algebraMap (integralClosure R L) L) hab
  rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K L,
    (algebraMap K L).injective.eq_iff] at this

end Main

end TorsionInjection
end AbelianVarieties.NOSProofs.TorsionSpecializationInjection

open AbelianVarieties.NOSProofs.TorsionSpecializationInjection.TorsionInjection

namespace GoodReductionJacobian.RelativeGroupLaw

theorem exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (hBK : AbelianSchemePropertyBundle K (pullback.snd g (specGenericFibreInclusion R K)))
    (d : ℕ) [SmoothOfRelativeDimension d (pullback.snd g (specGenericFibreInclusion R K))]
    (ℓ : ℕ) (hℓu : IsUnit (ℓ : R))
    (hunr : ∀ (A : ValuationSubring (AlgebraicClosure K)),
      (∀ r : R, algebraMap R (AlgebraicClosure K) r ∈ A) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ ∈ A.inertiaSubgroupIn K →
      ∀ (v : ℕ) (x : SchemeHomOver
          (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
          (pullback.snd g (specGenericFibreInclusion R K))),
        (LB.genericFibre K).IsTorsionPoint
            (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (ℓ ^ v) x →
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ x.1 =
            x.1)
    (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra R k']
    (hk' : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R k' r = 0) (v : ℕ) :
    ∃ r : Fin (ℓ ^ (2 * d * v)) →
        {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
          LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) (ℓ ^ v) y},
      Function.Injective r := by
  classical
  have hnR : IsUnit ((ℓ ^ v : ℕ) : R) := by rw [Nat.cast_pow]; exact hℓu.pow v
  have hnK : ((ℓ ^ v : ℕ) : K) ≠ 0 := by
    have h := hnR.map (algebraMap R K)
    rw [map_natCast] at h
    exact h.ne_zero
  have hcK : (LB.genericFibre K).IsCommutative :=
    RelativeGroupLaw.IsCommutative.baseChange _ (fun t x y => hcomm t x y)
  obtain ⟨hfin, hcard⟩ := finite_and_natCard_torsion (LB.genericFibre K) hcK hBK d (ℓ ^ v) hnK
    (AlgebraicClosure K)
  obtain ⟨L, hfd, hgal, hdesc, hfaith⟩ :=
    exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one
      K (LB.genericFibre K) (fun t x y => hcK t x y) hBK d (ℓ ^ v) hnK (AlgebraicClosure K)
  have : FiniteDimensional K L := hfd
  have : IsGalois K L := hgal
  have : IsFractionRing (integralClosure R L) L :=
    isFractionRing_integralClosure K L (R := R)
  have : IsDedekindDomain (integralClosure R L) :=
    isDedekindDomain_integralClosure K L (R := R)
  have : Module.Finite R (integralClosure R L) :=
    module_finite_integralClosure K L (R := R)
  obtain ⟨P, hPmax, hPover, ψ, hψ⟩ := exists_ideal_algHom_of_isAlgClosed
    (S := integralClosure R L) k' hk' (RingHom.ker_ne_top _)
  have hP0 : P ≠ ⊥ := ne_bot_of_liesOver_maximalIdeal (K := K) P
  have hinert : P.inertia (L ≃ₐ[K] L) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun τ hτ => hfaith τ fun z hz => ?_
    let vP : IsDedekindDomain.HeightOneSpectrum (integralClosure R L) := ⟨P, hPmax.isPrime, hP0⟩
    have : vP.asIdeal.IsMaximal := hPmax
    have hτv := mem_inertiaSubgroupIn_of_mem_inertia vP τ hτ
    obtain ⟨A, σ, hA, hσ, hστ⟩ :=
      ValuationSubring.exists_mem_inertiaSubgroupIn_and_forall_apply_algebraMap_eq K
        (Ω := AlgebraicClosure K) _ τ hτv
    have hRA : ∀ r : R, algebraMap R (AlgebraicClosure K) r ∈ A := by
      intro r
      have h1 : algebraMap R (AlgebraicClosure K) r =
          algebraMap L (AlgebraicClosure K) (algebraMap R L r) := by
        rw [IsScalarTower.algebraMap_apply R K (AlgebraicClosure K),
          IsScalarTower.algebraMap_apply R K L, ← IsScalarTower.algebraMap_apply K L]
      rw [h1, ← ValuationSubring.mem_comap, hA, IsScalarTower.algebraMap_apply R (integralClosure R
        L) L]
      exact algebraMap_mem_valuationSubringAtPrime vP _
    have hcomp : Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
        Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    have hx := (LB.genericFibre K).isTorsionPoint_schemeHomOverComp _ _ _ hcomp (ℓ ^ v) hz
    have hfix := hunr A hRA σ hσ v _ hx
    rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp] at hfix
    have hring : (σ : AlgebraicClosure K →+* AlgebraicClosure K).comp
        (algebraMap L (AlgebraicClosure K)) =
        (algebraMap L (AlgebraicClosure K)).comp (τ : L →+* L) :=
      RingHom.ext fun x => hστ x
    rw [hring, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] at hfix
    have : Epi (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure K)))) :=
      epi_specMap_of_field (algebraMap L (AlgebraicClosure K))
    exact (cancel_epi _).mp hfix
  have : Algebra.IsUnramifiedAt R P := isUnramifiedAt_of_inertia_eq_bot (K := K) P hinert
  have : P.IsPrime := hPmax.isPrime
  obtain ⟨r₁, hr₁⟩ :=
    exists_injective_specialize_isTorsionPoint_of_isUnramifiedAt
      K LB hcomm hN (ℓ ^ v) hnR (integralClosure R L) L P k' ψ hψ
  let δ : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
        (pullback.snd g (specGenericFibreInclusion R K)) //
      (LB.genericFibre K).IsTorsionPoint
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (ℓ ^ v) x} →
      {z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (pullback.snd g (specGenericFibreInclusion R K)) //
      (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (ℓ ^ v) z} :=
    fun x => ⟨(hdesc x.1 x.2).choose, (hdesc x.1 x.2).choose_spec.1⟩
  have hδ : Function.Injective δ := by
    intro x x' h
    apply Subtype.ext
    apply Subtype.ext
    rw [← (hdesc x.1 x.2).choose_spec.2, ← (hdesc x'.1 x'.2).choose_spec.2]
    exact congrArg (fun z => Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure K))) ≫
      z.1.1) h
  have : Finite {x : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
      (pullback.snd g (specGenericFibreInclusion R K)) //
      (LB.genericFibre K).IsTorsionPoint
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (ℓ ^ v) x} := hfin
  have hcard' : Nat.card {x : SchemeHomOver
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
        (pullback.snd g (specGenericFibreInclusion R K)) //
      (LB.genericFibre K).IsTorsionPoint
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (ℓ ^ v) x} =
      ℓ ^ (2 * d * v) := by
    rw [hcard, ← pow_mul]; congr 1; ring
  let e := Finite.equivFinOfCardEq hcard'
  exact ⟨fun i => r₁ (δ (e.symm i)), hr₁.comp (hδ.comp e.symm.injective)⟩

end GoodReductionJacobian.RelativeGroupLaw

end
