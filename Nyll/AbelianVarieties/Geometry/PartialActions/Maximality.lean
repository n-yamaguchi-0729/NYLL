/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Nyll.AbelianVarieties.Geometry.PartialActions.Basic
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.SchemeTheory.LocalGeometry.Normality
public import Nyll.AbelianVarieties.Geometry.GroupLaw
public import Nyll.AlgebraicCurves.Geometry.Schemes.FunctionFields.PartialMapMemDomainToRationalMap
public import Nyll.SchemeTheory.LocalGeometry.SmoothDVRStalk
public import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Maximal compatible partial actions

Extend multiplication from an open model to a maximal partial action, prove its unit and
associativity laws, and control the boundary using properness and specialization.
-/

@[expose] public section

/-- The unique point of the spectrum of a field. -/
def fieldPoint (k : Type*) [Field k] :
    ↥(AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  IsLocalRing.closedPoint k

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CategoryTheory.Limits hiding pair
open Topology

universe u

namespace AbelianVarieties.NOSProofs.TranslationSpecialization

namespace Specialization

variable {R : Type u} [CommRing R]
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)

/-- Right translation by a point after base change. -/
noncomputable def rightMul {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) : pullback g t₀ ⟶ B :=
  (LB.mul (pullback.snd g t₀ ≫ t₀) ⟨pullback.fst g t₀, pullback.condition⟩
      (schemeHomOverComp (pullback.snd g t₀) rfl σ)).1

theorem rightMul_comp {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) : rightMul LB t₀ σ ≫ g = pullback.snd g t₀ ≫ t₀ :=
  (LB.mul _ _ _).2

/-- The same translation as an endomorphism of the base-changed scheme. -/
noncomputable def rightTrans {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) : pullback g t₀ ⟶ pullback g t₀ :=
  pullback.lift (rightMul LB t₀ σ) (pullback.snd g t₀) (rightMul_comp LB t₀ σ)

@[scoped simp]
theorem rightTrans_fst {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) : rightTrans LB t₀ σ ≫ pullback.fst g t₀ = rightMul LB t₀ σ :=
  pullback.lift_fst _ _ _

@[scoped simp]
theorem rightTrans_snd {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) : rightTrans LB t₀ σ ≫ pullback.snd g t₀ = pullback.snd g t₀ :=
  pullback.lift_snd _ _ _

theorem comp_rightMul {T₀ T : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) (ψ : T ⟶ pullback g t₀) (t' : T ⟶ Spec (CommRingCat.of R))
    (hψ : ψ ≫ (pullback.snd g t₀ ≫ t₀) = t') :
    ψ ≫ rightMul LB t₀ σ =
      (LB.mul t' ⟨ψ ≫ pullback.fst g t₀, by rw [Category.assoc, pullback.condition, ←
        Category.assoc, ← hψ, Category.assoc]⟩
        ⟨ψ ≫ pullback.snd g t₀ ≫ σ.1, by rw [Category.assoc, Category.assoc, σ.2, ← Category.assoc,
          ← hψ, Category.assoc]⟩).1 := by
  have h := LB.mul_natural (pullback.snd g t₀ ≫ t₀) t' ψ hψ
    ⟨pullback.fst g t₀, pullback.condition⟩ (schemeHomOverComp (pullback.snd g t₀) rfl σ)
  have h1 := congrArg Subtype.val h
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at h1
  unfold rightMul
  rw [h1]
  congr 2

theorem rightTrans_comp_rightTrans_inv {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) :
    rightTrans LB t₀ σ ≫ rightTrans LB t₀ (LB.inv t₀ σ) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, rightTrans_fst, Category.id_comp,
      comp_rightMul LB t₀ (LB.inv t₀ σ) (rightTrans LB t₀ σ) (pullback.snd g t₀ ≫ t₀)
        (by rw [← Category.assoc, rightTrans_snd])]
    have e1 : (⟨rightTrans LB t₀ σ ≫ pullback.fst g t₀, by
          rw [Category.assoc, pullback.condition, ← Category.assoc, rightTrans_snd]⟩ :
          SchemeHomOver (pullback.snd g t₀ ≫ t₀) g) =
        LB.mul (pullback.snd g t₀ ≫ t₀) ⟨pullback.fst g t₀, pullback.condition⟩
          (schemeHomOverComp (pullback.snd g t₀) rfl σ) := by
      apply Subtype.ext; simp only [rightTrans_fst]; rfl
    have e2 : (⟨rightTrans LB t₀ σ ≫ pullback.snd g t₀ ≫ (LB.inv t₀ σ).1, by
          rw [Category.assoc, Category.assoc, (LB.inv t₀ σ).2, ← Category.assoc, rightTrans_snd]⟩ :
          SchemeHomOver (pullback.snd g t₀ ≫ t₀) g) =
        LB.inv (pullback.snd g t₀ ≫ t₀) (schemeHomOverComp (pullback.snd g t₀) rfl σ) := by
      rw [← LB.inv_natural t₀ (pullback.snd g t₀ ≫ t₀) (pullback.snd g t₀) rfl σ]
      apply Subtype.ext; simp only [GoodReductionJacobian.schemeHomOverComp_coe]; rw [←
        Category.assoc, rightTrans_snd]
    rw [e1, e2, LB.mul_assoc, LB.mul_inv_cancel, LB.mul_one]
  · rw [Category.assoc, rightTrans_snd, rightTrans_snd, Category.id_comp]

theorem isIso_rightTrans {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) : IsIso (rightTrans LB t₀ σ) := by
  refine ⟨⟨rightTrans LB t₀ (LB.inv t₀ σ), rightTrans_comp_rightTrans_inv LB t₀ σ, ?_⟩⟩
  have h := rightTrans_comp_rightTrans_inv LB t₀ (LB.inv t₀ σ)
  have hii : LB.inv t₀ (LB.inv t₀ σ) = σ := by
    let : Group (SchemeHomOver t₀ g) := LB.pointGroup t₀
    exact inv_inv σ
  rwa [hii] at h

section Top

theorem base_fst_eq (s₀ : B) (x : ↑(pullback g (B.fromSpecResidueField s₀ ≫ g))) :
    g.base ((pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base x) = g.base s₀ := by
  change (pullback.fst g (B.fromSpecResidueField s₀ ≫ g) ≫ g) x = g.base s₀
  rw [pullback.condition, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply]

theorem exists_specializes_fst_eq (s₀ : B) (_hs₀ : ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀)
    (e : ↑(pullback g (B.fromSpecResidueField s₀ ≫ g))) (y : B) (hy : g.base y = g.base s₀)
    (hye : y ⤳ (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base e) :
    ∃ w : ↑(pullback g (B.fromSpecResidueField s₀ ≫ g)),
      w ⤳ e ∧ (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base w = y := by
  let t : ↑(Spec (CommRingCat.of R)) := g.base s₀
  let ιt := (Spec (CommRingCat.of R)).fromSpecResidueField t
  let σb : Spec (B.residueField s₀) ⟶ Spec ((Spec (CommRingCat.of R)).residueField t) :=
    Spec.map (g.residueFieldMap s₀)
  have hστ : σb ≫ ιt = B.fromSpecResidueField s₀ ≫ g :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g s₀
  let fT := pullback.snd g ιt
  let fι := pullback.fst g ιt
  let p' := pullback.fst fT σb
  let E : pullback fT σb ≅ pullback g (B.fromSpecResidueField s₀ ≫ g) :=
    pullbackLeftPullbackSndIso g ιt σb ≪≫ pullback.congrHom rfl hστ
  have hE : E.hom ≫ pullback.fst g (B.fromSpecResidueField s₀ ≫ g) = p' ≫ fι := by
    simp only [E, Iso.trans_hom, Category.assoc, pullback.congrHom, asIso_hom, pullback.lift_fst,
      Category.comp_id]
    exact pullbackLeftPullbackSndIso_hom_fst g ιt σb
  have : Flat σb := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField _) _
  have : Flat p' := inferInstance
  have hgen : GeneralizingMap p'.base := Flat.generalizingMap p'
  set e' := E.inv.base e with he'
  have hEe : E.hom.base e' = e := by
    rw [he', ← TopCat.comp_app, ← Scheme.Hom.comp_base, Iso.inv_hom_id]; rfl
  have hpe : (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base e = fι.base (p'.base e') := by
    rw [← hEe, ← TopCat.comp_app, ← Scheme.Hom.comp_base, hE, Scheme.Hom.comp_base, TopCat.comp_app]
  obtain ⟨yF, hyF⟩ : y ∈ Set.range (g.fiberι t) := by
    rw [Scheme.Hom.range_fiberι]; exact hy
  have hyF' : yF ⤳ p'.base e' := by
    rw [hpe, ← hyF] at hye
    exact (g.fiberι t).isEmbedding.isInducing.specializes_iff.mp hye
  obtain ⟨w', hw'e', hpw'⟩ := hgen hyF'
  refine ⟨E.hom.base w', ?_, ?_⟩
  · rw [← hEe]; exact hw'e'.map E.hom.continuous
  · rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, hE, Scheme.Hom.comp_base, TopCat.comp_app, hpw']
    exact hyF

variable [IsDomain R] [IsDiscreteValuationRing R] [Smooth g] [IsSeparated g] [QuasiCompact g]

omit LB in
theorem eq_of_ne_closedPoint (a b : ↑(Spec (CommRingCat.of R)))
    (ha : a ≠ IsLocalRing.closedPoint R) (hb : b ≠ IsLocalRing.closedPoint R) : a = b := by
  have key : ∀ c : ↑(Spec (CommRingCat.of R)), c ≠ IsLocalRing.closedPoint R → c.asIdeal = ⊥ := by
    intro c hc
    by_contra h
    apply hc
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal (hpi := c.2) h)
  exact PrimeSpectrum.ext ((key a ha).trans (key b hb).symm)

omit LB [Smooth g] [IsSeparated g] [QuasiCompact g] in
theorem locallyOfFiniteType_fromSpecResidueField (s₀ : B)
    (hs₀ : ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀) :
    LocallyOfFiniteType (B.fromSpecResidueField s₀) := by
  by_cases ht : g.base s₀ = IsLocalRing.closedPoint R
  · have hcl : IsClosed ({s₀} : Set B) := by
      rw [← closure_eq_iff_isClosed]
      apply Set.Subset.antisymm _ subset_closure
      intro y hy
      have hsy : s₀ ⤳ y := specializes_iff_mem_closure.mpr hy
      have : g.base y = g.base s₀ := by
        have h1 : g.base s₀ ⤳ g.base y := hsy.map g.continuous
        rw [ht] at h1 ⊢
        have := h1.mem_closed (IsLocalRing.isClosed_singleton_closedPoint R) rfl
        exact this
      exact hs₀ y hsy this
    have := isClosed_singleton_iff_isClosedImmersion.mp hcl
    infer_instance
  · let V : B.Opens := g ⁻¹ᵁ ⟨{IsLocalRing.closedPoint R}ᶜ,
      (IsLocalRing.isClosed_singleton_closedPoint R).isOpen_compl⟩
    have hs₀V : s₀ ∈ V := ht
    let x : ↑(V : Scheme.{u}) := ⟨s₀, hs₀V⟩
    have hcl : IsClosed ({x} : Set ↑(V : Scheme.{u})) := by
      rw [← closure_eq_iff_isClosed]
      apply Set.Subset.antisymm _ subset_closure
      intro y hy
      have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
      have hsy : s₀ ⤳ y.1 := hxy.map continuous_subtype_val
      have hyV : g.base y.1 ≠ IsLocalRing.closedPoint R := y.2
      have : g.base y.1 = g.base s₀ := eq_of_ne_closedPoint (R := R) _ _ hyV ht
      have := hs₀ y.1 hsy this
      exact Set.mem_singleton_iff.mpr (Subtype.ext this)
    have hci := isClosed_singleton_iff_isClosedImmersion.mp hcl
    have heq : Spec.map (V.ι.residueFieldMap x) ≫ B.fromSpecResidueField s₀ =
        (V : Scheme.{u}).fromSpecResidueField x ≫ V.ι :=
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField V.ι x
    have hlft : LocallyOfFiniteType ((V : Scheme.{u}).fromSpecResidueField x ≫ V.ι) := inferInstance
    rw [← heq] at hlft
    have : MorphismProperty.RespectsIso (@LocallyOfFiniteType.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.cancel_left_of_respectsIso (@LocallyOfFiniteType.{u})
      (Spec.map (V.ι.residueFieldMap x)) (B.fromSpecResidueField s₀)).mp hlft

omit [IsSeparated g] [QuasiCompact g] in
theorem eq_of_specializes_of_fst_eq (s₀ : B) (hs₀ : ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀)
    (w e : ↑(pullback g (B.fromSpecResidueField s₀ ≫ g))) (hwe : w ⤳ e)
    (hp : (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base w =
      (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base e) : w = e := by
  have : LocallyOfFiniteType (B.fromSpecResidueField s₀) :=
    locallyOfFiniteType_fromSpecResidueField (g := g) s₀ hs₀
  have : LocallyOfFiniteType (B.fromSpecResidueField s₀ ≫ g) := inferInstance
  have : LocallyQuasiFinite (B.fromSpecResidueField s₀ ≫ g) :=
    .of_injective (fun a b _ => Subsingleton.elim a b)
  have : LocallyQuasiFinite (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)) := inferInstance
  let π : pullback g (B.fromSpecResidueField s₀ ≫ g) ⟶ B :=
    pullback.fst g (B.fromSpecResidueField s₀ ≫ g)
  have hdisc := π.isDiscrete_preimage_singleton (π.base e)
  rw [isDiscrete_iff_discreteTopology] at hdisc
  have : DiscreteTopology
      {z : ↥(pullback g (B.fromSpecResidueField s₀ ≫ g)) // π.base z = π.base e} := hdisc
  let w' : {z : ↥(pullback g (B.fromSpecResidueField s₀ ≫ g)) // π.base z = π.base e} := ⟨w, hp⟩
  let e' : {z : ↥(pullback g (B.fromSpecResidueField s₀ ≫ g)) // π.base z = π.base e} := ⟨e, rfl⟩
  have hwe' : w' ⤳ e' := (Topology.IsInducing.subtypeVal.specializes_iff (x := w') (y := e')).mp hwe
  have : w' = e' := (specializes_iff_eq.mp hwe')
  exact congrArg Subtype.val this

omit [IsDomain R] [IsDiscreteValuationRing R] [IsSeparated g] in
theorem exists_mem_specializes_of_mem_closure_image (s₀ : B)
    (E : Set ↑(pullback g (B.fromSpecResidueField s₀ ≫ g))) (hE : IsClosed E) (η : B)
    (hη : η ∈ closure ((pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base '' E)) :
    ∃ e ∈ E, (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base e ⤳ η := by
  let p := pullback.fst g (B.fromSpecResidueField s₀ ≫ g)
  have : IsNoetherian ↑(pullback g (B.fromSpecResidueField s₀ ≫ g)) :=
    (isNoetherian_iff _).mpr ⟨inferInstance, inferInstance⟩
  have : TopologicalSpace.NoetherianSpace ↑(pullback g (B.fromSpecResidueField s₀ ≫ g)) :=
    inferInstance
  obtain ⟨S, hSfin, hScl, hSirr, hSE⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hE
  let γ : ↑S → ↑(pullback g (B.fromSpecResidueField s₀ ≫ g)) := fun t => (hSirr t.1
    t.2).genericPoint
  have hγ : ∀ t : ↑S, IsGenericPoint (γ t) (t.1 : Set _) := fun t =>
    (hSirr t.1 t.2).isGenericPoint_genericPoint (hScl t.1 t.2)
  have : Finite ↑S := hSfin.to_subtype
  have hsub : p.base '' E ⊆ ⋃ t : ↑S, closure {p.base (γ t)} := by
    rintro b ⟨e, he, rfl⟩
    rw [hSE] at he
    obtain ⟨t, htS, het⟩ := Set.mem_sUnion.mp he
    refine Set.mem_iUnion.mpr ⟨⟨t, htS⟩, ?_⟩
    have hsp : γ ⟨t, htS⟩ ⤳ e := (hγ ⟨t, htS⟩).specializes het
    exact specializes_iff_mem_closure.mp (hsp.map p.continuous)
  have hcl : IsClosed (⋃ t : ↑S, closure {p.base (γ t)}) :=
    isClosed_iUnion_of_finite fun _ => isClosed_closure
  have hη' := (closure_minimal hsub hcl) hη
  obtain ⟨t, hηt⟩ := Set.mem_iUnion.mp hη'
  refine ⟨γ t, ?_, specializes_iff_mem_closure.mpr hηt⟩
  rw [hSE]
  exact Set.mem_sUnion.mpr ⟨t.1, t.2, (hγ t).mem⟩

omit LB [IsSeparated g] [QuasiCompact g] in
theorem forall_specializes_eq_of_specializes_of_ne (η : B) (hηk : g.base η = IsLocalRing.closedPoint
    R)
    (hηmax : ∀ y : B, y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η)
    (d : B) (hd : d ⤳ η) (hdk : g.base d ≠ IsLocalRing.closedPoint R) :
    ∀ y : B, y ⤳ d → y = d := by
  classical
  obtain ⟨_, hdvr⟩ := AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R
    g η hηk hηmax
  have hrange : Set.range (B.fromSpecStalk η) = {y | y ⤳ η} := Scheme.range_fromSpecStalk
  have hprime : ∀ 𝔭 : PrimeSpectrum (B.presheaf.stalk η),
      𝔭.asIdeal = ⊥ ∨ 𝔭 = IsLocalRing.closedPoint (B.presheaf.stalk η) := by
    intro 𝔭
    by_cases h : 𝔭.asIdeal = ⊥
    · exact Or.inl h
    · right
      apply PrimeSpectrum.ext
      exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal (hpi := 𝔭.2) h)
  have hclosed : (B.fromSpecStalk η).base (IsLocalRing.closedPoint (B.presheaf.stalk η)) = η :=
    Scheme.fromSpecStalk_closedPoint
  have hdη : d ≠ η := fun h => hdk (h ▸ hηk)
  obtain ⟨𝔭, h𝔭⟩ : d ∈ Set.range (B.fromSpecStalk η) := by rw [hrange]; exact hd
  intro y hy
  obtain ⟨𝔮, h𝔮⟩ : y ∈ Set.range (B.fromSpecStalk η) := by rw [hrange]; exact hy.trans hd
  have hyη : y ≠ η := by
    intro hyη
    apply hdη
    rw [hyη] at hy
    exact (hd.antisymm hy).eq
  have h𝔭gen : 𝔭.asIdeal = ⊥ := by
    rcases hprime 𝔭 with h | h
    · exact h
    · exact absurd (h𝔭.symm.trans (by rw [h]; exact hclosed)) hdη
  have h𝔮gen : 𝔮.asIdeal = ⊥ := by
    rcases hprime 𝔮 with h | h
    · exact h
    · exact absurd (h𝔮.symm.trans (by rw [h]; exact hclosed)) hyη
  have : 𝔮 = 𝔭 := PrimeSpectrum.ext (h𝔮gen.trans h𝔭gen.symm)
  rw [← h𝔮, ← h𝔭, this]

omit [IsSeparated g] in
theorem main (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (s₀ : B) (hs₀ : ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀)
    (η : B) (hηk : g.base η = IsLocalRing.closedPoint R)
    (hηmax : ∀ y : B, y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η) :
    η ∉ closure ((pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base ''
      ((rightMul LB (B.fromSpecResidueField s₀ ≫ g) ⟨B.fromSpecResidueField s₀, rfl⟩).base ⁻¹' ((U :
        Set B)ᶜ))) := by
  classical
  set t₀ := B.fromSpecResidueField s₀ ≫ g with ht₀
  set σ : SchemeHomOver t₀ g := ⟨B.fromSpecResidueField s₀, rfl⟩ with hσ
  set p := pullback.fst g t₀ with hp
  set ρ := rightMul LB t₀ σ with hρ
  intro hη
  have hE : IsClosed (ρ.base ⁻¹' ((U : Set B)ᶜ)) := U.isOpen.isClosed_compl.preimage ρ.continuous
  obtain ⟨e, heE, hde⟩ := exists_mem_specializes_of_mem_closure_image (g := g) s₀ _ hE η hη
  have hdmax : ∀ y : B, y ⤳ p.base e → g.base y = g.base (p.base e) → y = p.base e := by
    by_cases hdk : g.base (p.base e) = IsLocalRing.closedPoint R
    · have hde' : p.base e = η := hηmax _ hde hdk
      intro y hy hyk
      rw [hde'] at hy hyk ⊢
      exact hηmax y hy (hyk.trans hηk)
    · intro y hy _
      exact forall_specializes_eq_of_specializes_of_ne (g := g) η hηk hηmax (p.base e) hde hdk y hy
  have hiso := isIso_rightTrans LB t₀ σ
  set T := rightTrans LB t₀ σ with hT
  have hTfst : T ≫ p = ρ := rightTrans_fst LB t₀ σ
  have hρe : ρ.base e = p.base (T.base e) := by
    rw [← hTfst, Scheme.Hom.comp_base, TopCat.comp_app]
  have hρmax : ∀ y : B, y ⤳ ρ.base e → g.base y = g.base (ρ.base e) → y = ρ.base e := by
    intro y hy hyk
    rw [hρe] at hy hyk ⊢
    have hy' : g.base y = g.base s₀ := by rw [hyk, base_fst_eq]
    obtain ⟨w, hwe', hpw⟩ := exists_specializes_fst_eq (g := g) s₀ hs₀ (T.base e) y hy' hy
    let Tinv := inv T
    have h1 : Tinv.base (T.base e) = e := by
      rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, IsIso.hom_inv_id]; rfl
    have hw₀e : Tinv.base w ⤳ e := by rw [← h1]; exact hwe'.map Tinv.continuous
    have hpw₀ : p.base (Tinv.base w) ⤳ p.base e := hw₀e.map p.continuous
    have hfib : g.base (p.base (Tinv.base w)) = g.base (p.base e) := by
      rw [base_fst_eq, base_fst_eq]
    have hw₀ : p.base (Tinv.base w) = p.base e := hdmax _ hpw₀ hfib
    have : Tinv.base w = e := eq_of_specializes_of_fst_eq (g := g) s₀ hs₀ _ _ hw₀e hw₀
    have : w = T.base e := by
      rw [← this, ← TopCat.comp_app, ← Scheme.Hom.comp_base, IsIso.inv_hom_id]; rfl
    rw [← hpw, this]
  have hρU : ρ.base e ∈ (U : Set B) := hU _ hρmax
  exact heE hρU

end Top

end Specialization
end AbelianVarieties.NOSProofs.TranslationSpecialization

open AbelianVarieties.NOSProofs.TranslationSpecialization.Specialization

namespace GoodReductionJacobian.RelativeGroupLaw

theorem not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (s₀ : B) (hs₀ : ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀)
    (η : B) (hηk : g.base η = IsLocalRing.closedPoint R)
    (hηmax : ∀ y : B, y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η) :
    η ∉ closure ((pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base ''
      ((LB.mul (pullback.snd g (B.fromSpecResidueField s₀ ≫ g) ≫ (B.fromSpecResidueField s₀ ≫ g))
          ⟨pullback.fst g (B.fromSpecResidueField s₀ ≫ g), pullback.condition⟩
          (schemeHomOverComp (pullback.snd g (B.fromSpecResidueField s₀ ≫ g)) rfl
            (⟨B.fromSpecResidueField s₀, rfl⟩ :
              SchemeHomOver (B.fromSpecResidueField s₀ ≫ g) g))).1.base ⁻¹' ((U : Set B)ᶜ))) :=
  main LB U hU s₀ hs₀ η hηk hηmax

end GoodReductionJacobian.RelativeGroupLaw

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

universe u

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits hiding pair
open NeronModelInfra (SchemeHomOver)

namespace AbelianVarieties.NOSProofs.PartialActionLaws

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian

namespace PartialAction
open _root_.GoodReductionJacobian.PartialAction

namespace ActionLaws

open
  AbelianVarieties.NOSProofs.PartialActionTransport.GoodReductionJacobian.PartialAction.OpTransport
  (geometricallyIrreducible)

section Points

variable {B T'' T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {t'' : T'' ⟶ B} {g : A ⟶ B}

theorem comp_comp (ψ' : T'' ⟶ T') (hψ' : ψ' ≫ t' = t'') (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t g) :
    schemeHomOverComp ψ' hψ' (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp (ψ' ≫ ψ) (by rw [Category.assoc, hψ, hψ']) x :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem comp_id' (h : 𝟙 T ≫ t = t) (x : SchemeHomOver t g) :
    schemeHomOverComp (𝟙 T) h x = x :=
  Subtype.ext (Category.id_comp _)

theorem comp_congr {ψ₁ ψ₂ : T' ⟶ T} (e : ψ₁ = ψ₂) (h₁ : ψ₁ ≫ t = t') (h₂ : ψ₂ ≫ t = t')
    (x : SchemeHomOver t g) :
    schemeHomOverComp ψ₁ h₁ x = schemeHomOverComp ψ₂ h₂ x := by
  subst e; rfl

end Points

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}

section Calculus

variable (a : PartialAction k f p)

theorem pair_comp {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) :
    pair (schemeHomOverComp ψ hψ γ) (schemeHomOverComp ψ hψ x) = ψ ≫ pair γ x := by
  apply pullback.hom_ext <;>
    simp only [pair, GoodReductionJacobian.schemeHomOverComp_coe, pullback.lift_fst,
      pullback.lift_snd, Category.assoc]

theorem defined_comp {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    a.Defined (schemeHomOverComp ψ hψ γ) (schemeHomOverComp ψ hψ x) := by
  rintro _ ⟨τ, rfl⟩
  rw [pair_comp, Scheme.Hom.comp_apply]
  exact hd ⟨_, rfl⟩

theorem liftDom_eq {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x)
    (φ : T ⟶ (a.dom : Scheme.{u})) (h : φ ≫ a.dom.ι = pair γ x) : a.liftDom γ x hd = φ := by
  rw [← cancel_mono a.dom.ι, liftDom_ι, h]

theorem liftDom_comp {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x)
    (hd' : a.Defined (schemeHomOverComp ψ hψ γ) (schemeHomOverComp ψ hψ x)) :
    a.liftDom _ _ hd' = ψ ≫ a.liftDom γ x hd :=
  liftDom_eq a _ _ hd' _ (by rw [Category.assoc, liftDom_ι, pair_comp])

theorem act_comp {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x)
    (hd' : a.Defined (schemeHomOverComp ψ hψ γ) (schemeHomOverComp ψ hψ x)) :
    a.act _ _ hd' = schemeHomOverComp ψ hψ (a.act γ x hd) :=
  Subtype.ext (by simp only [act_coe, GoodReductionJacobian.schemeHomOverComp_coe, liftDom_comp a ψ
    hψ γ x hd hd',
    Category.assoc])

theorem act_coe_congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {γ γ' : SchemeHomOver t f} {x x' : SchemeHomOver t p} (eγ : γ = γ') (ex : x = x')
    (hd : a.Defined γ x) (hd' : a.Defined γ' x') : (a.act γ x hd).1 = (a.act γ' x' hd').1 := by
  subst eγ ex; rfl

theorem act_congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {γ γ' : SchemeHomOver t f} {x x' : SchemeHomOver t p} (eγ : γ = γ') (ex : x = x')
    (hd : a.Defined γ x) (hd' : a.Defined γ' x') : a.act γ x hd = a.act γ' x' hd' := by
  subst eγ ex; rfl

/-- The structure morphism of the group-model product. -/
abbrev q (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k)) :
    pullback f p ⟶ Spec (CommRingCat.of k) :=
  pullback.fst f p ≫ f

/-- The group-coordinate point of the action product. -/
def wGP (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k)) :
    SchemeHomOver (q f p) f :=
  ⟨pullback.fst f p, rfl⟩

/-- The model-coordinate point of the action product. -/
def zGP (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k)) :
    SchemeHomOver (q f p) p :=
  ⟨pullback.snd f p, pullback.condition.symm⟩

@[scoped simp]
theorem wGP_coe : (wGP f p).1 = pullback.fst f p := rfl
@[scoped simp]
theorem zGP_coe : (zGP f p).1 = pullback.snd f p := rfl

theorem pair_wGP_zGP : pair (wGP f p) (zGP f p) = 𝟙 _ := by
  apply pullback.hom_ext <;>
    simp only [pair, wGP_coe, zGP_coe, pullback.lift_fst, pullback.lift_snd, Category.id_comp]

/-- The structure morphism of the partial-action domain. -/
abbrev tD : (a.dom : Scheme.{u}) ⟶ Spec (CommRingCat.of k) := a.dom.ι ≫ q f p

/-- Restrict the group-coordinate point to the action domain. -/
def wD : SchemeHomOver (tD a) f := schemeHomOverComp a.dom.ι rfl (wGP f p)

/-- Restrict the model-coordinate point to the action domain. -/
def zD : SchemeHomOver (tD a) p := schemeHomOverComp a.dom.ι rfl (zGP f p)

@[scoped simp]
theorem wD_coe : (wD a).1 = a.dom.ι ≫ pullback.fst f p := rfl
@[scoped simp]
theorem zD_coe : (zD a).1 = a.dom.ι ≫ pullback.snd f p := rfl

theorem pair_wD_zD : pair (wD a) (zD a) = a.dom.ι := by
  rw [wD, zD, pair_comp, pair_wGP_zGP, Category.comp_id]

theorem defined_wD_zD : a.Defined (wD a) (zD a) := by
  rw [Defined, pair_wD_zD, Scheme.Opens.range_ι]

theorem liftDom_wD_zD : a.liftDom (wD a) (zD a) (defined_wD_zD a) = 𝟙 _ :=
  liftDom_eq a _ _ _ _ (by rw [Category.id_comp, pair_wD_zD])

/-- The value of the partial action on its domain. -/
def yD : SchemeHomOver (tD a) p := a.act (wD a) (zD a) (defined_wD_zD a)

@[scoped simp]
theorem yD_coe : (yD a).1 = a.hom := by
  simp only [yD, act_coe, liftDom_wD_zD, Category.id_comp]

theorem liftDom_tD {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    a.liftDom γ x hd ≫ tD a = t := by
  rw [← Category.assoc, liftDom_ι, pair, pullback.lift_fst_assoc]
  exact γ.2

theorem eq_comp_liftDom {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    γ = schemeHomOverComp (a.liftDom γ x hd) (liftDom_tD a γ x hd) (wD a) ∧
      x = schemeHomOverComp (a.liftDom γ x hd) (liftDom_tD a γ x hd) (zD a) := by
  refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, wD_coe, ← Category.assoc, liftDom_ι,
    pair,
      pullback.lift_fst]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, zD_coe, ← Category.assoc, liftDom_ι,
    pair,
      pullback.lift_snd]

theorem act_eq_comp_yD {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    a.act γ x hd = schemeHomOverComp (a.liftDom γ x hd) (liftDom_tD a γ x hd) (yD a) :=
  Subtype.ext (by simp only [act_coe, GoodReductionJacobian.schemeHomOverComp_coe, yD_coe])

end Calculus

section Unit

variable (L : RelativeGroupLaw k f) (a : PartialAction k f p)

/-- Insert the unit section into the action product. -/
def unitSlice (L : RelativeGroupLaw k f) (p : P ⟶ Spec (CommRingCat.of k)) : P ⟶ pullback f p :=
  pair (L.one p) (⟨𝟙 P, Category.id_comp p⟩ : SchemeHomOver p p)

@[reassoc (attr := simp)]
theorem unitSlice_snd : unitSlice L p ≫ pullback.snd f p = 𝟙 P := by
  simp only [unitSlice, pair, pullback.lift_snd]

theorem pair_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t p) :
    pair (L.one t) x = x.1 ≫ unitSlice L p := by
  apply pullback.hom_ext
  · simp only [pair, unitSlice, pullback.lift_fst, Category.assoc]
    exact congrArg Subtype.val (L.one_natural p t x.1 x.2).symm
  · simp only [pair, unitSlice, pullback.lift_snd, Category.assoc, Category.comp_id]

/-- The model points where the unit section acts. -/
def unitOpen : P.Opens := unitSlice L p ⁻¹ᵁ a.dom

/-- Lift the unit section into the action domain. -/
def unitLift : ((unitOpen L a : P.Opens) : Scheme.{u}) ⟶ (a.dom : Scheme.{u}) :=
  IsOpenImmersion.lift a.dom.ι ((unitOpen L a).ι ≫ unitSlice L p) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact y.2)

@[reassoc (attr := simp)]
theorem unitLift_ι : unitLift L a ≫ a.dom.ι = (unitOpen L a).ι ≫ unitSlice L p :=
  IsOpenImmersion.lift_fac _ _ _

variable [IsIntegral P] [IsSeparated p] (V : G.Opens) [Nonempty (V : Scheme.{u})]
  (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι] (hι : ι ≫ p = V.ι ≫ f)

/-- The identity point of the chosen open model. -/
def idV (V : G.Opens) : SchemeHomOver (V.ι ≫ f) (V.ι ≫ f) := ⟨𝟙 _, Category.id_comp _⟩

include hι in
theorem unitLift_hom (hc : a.Compatible L V ι hι) :
    unitLift L a ≫ a.hom = (unitOpen L a).ι := by
  obtain ⟨hdV, hactV⟩ := hc (V.ι ≫ f) (L.one _) (idV V) (idV V) (by rw [L.one_mul])
  have hrange : Set.range ι ⊆ ((unitOpen L a : P.Opens) : Set P) := by
    rintro _ ⟨v, rfl⟩
    have := hdV ⟨v, rfl⟩
    rw [pair_one, modelPoint_coe, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
    exact this
  let ιe : (V : Scheme.{u}) ⟶ (unitOpen L a : P.Opens) :=
    IsOpenImmersion.lift (unitOpen L a).ι ι (by rwa [Scheme.Opens.range_ι])
  have hιe : ιe ≫ (unitOpen L a).ι = ι := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion ιe := IsOpenImmersion.of_comp ιe (unitOpen L a).ι
  have : Nonempty ((unitOpen L a : P.Opens) : Scheme.{u}) := Nonempty.map ιe inferInstance
  have : IrreducibleSpace ((unitOpen L a : P.Opens) : Scheme.{u}) :=
    (unitOpen L a).ι.isOpenEmbedding.irreducibleSpace
  have : IsDominant ιe :=
    ⟨ιe.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _⟩
  have : IsReduced ((unitOpen L a : P.Opens) : Scheme.{u}) := isReduced_of_isOpenImmersion (unitOpen
    L a).ι
  refine ext_of_isDominant_of_isSeparated p ?_ ιe ?_
  · rw [Category.assoc, a.hom_comp, unitLift_ι_assoc, unitSlice_snd_assoc]
  · have hlift : a.liftDom (L.one _) (modelPoint ι hι (idV V)) hdV = ιe ≫ unitLift L a :=
      liftDom_eq a _ _ _ _ (by
        rw [Category.assoc, unitLift_ι, ← Category.assoc, hιe, pair_one, modelPoint_coe, idV,
          Category.id_comp])
    have := congrArg Subtype.val hactV
    rw [act_coe, hlift, modelPoint_coe, Category.assoc] at this
    rw [this, hιe, idV, Category.id_comp]

include hι in
theorem unitActs (hc : a.Compatible L V ι hι) : a.UnitActs L := by
  intro T t x hd
  have hrange : Set.range x.1 ⊆ ((unitOpen L a : P.Opens) : Set P) := by
    rintro _ ⟨τ, rfl⟩
    have := hd ⟨τ, rfl⟩
    rw [pair_one, Scheme.Hom.comp_apply] at this
    exact this
  let x' : T ⟶ (unitOpen L a : P.Opens) :=
    IsOpenImmersion.lift (unitOpen L a).ι x.1 (by rwa [Scheme.Opens.range_ι])
  have hx' : x' ≫ (unitOpen L a).ι = x.1 := IsOpenImmersion.lift_fac _ _ _
  have hlift : a.liftDom (L.one t) x hd = x' ≫ unitLift L a :=
    liftDom_eq a _ _ _ _ (by rw [Category.assoc, unitLift_ι, ← Category.assoc, hx', pair_one])
  apply Subtype.ext
  rw [act_coe, hlift, Category.assoc, unitLift_hom L a V ι hι hc, hx']

end Unit

section MoreCalculus

variable (L : RelativeGroupLaw k f) (a : PartialAction k f p)

theorem comp_mul {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x y : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.mul t x y) =
      L.mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y) :=
  L.mul_natural t t' ψ hψ x y

theorem comp_one {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    schemeHomOverComp ψ hψ (L.one t) = L.one t' :=
  L.one_natural t t' ψ hψ

theorem comp_nmi {T' T : Scheme.{u}} {B C : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} {g' : B ⟶ Spec (CommRingCat.of k)}
    {g : C ⟶ Spec (CommRingCat.of k)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t g') (φ : SchemeHomOver g' g) :
    schemeHomOverComp ψ hψ (NeronModelInfra.schemeHomOverComp x φ) =
      NeronModelInfra.schemeHomOverComp (schemeHomOverComp ψ hψ x) φ :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem comp_modelPoint {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f)
    {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (v : SchemeHomOver t (V.ι ≫ f)) :
    schemeHomOverComp ψ hψ (modelPoint ι hι v) = modelPoint ι hι (schemeHomOverComp ψ hψ v) :=
  Subtype.ext (Category.assoc _ _ _).symm

/-- Pull a base point back to a test scheme. -/
def const {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of k)} {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    SchemeHomOver t g :=
  schemeHomOverComp t (Category.comp_id t) x

@[scoped simp]
theorem const_coe {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of k)} {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    (const t x).1 = t ≫ x.1 := rfl

theorem comp_const {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of k)} {T' T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    schemeHomOverComp ψ hψ (const t x) = const t' x :=
  Subtype.ext (by simp only [GoodReductionJacobian.schemeHomOverComp_coe, const_coe, ←
    Category.assoc, hψ])

theorem const_id {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of k)}
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    const (𝟙 _) x = x :=
  Subtype.ext (Category.id_comp _)

theorem comp_kpt_eq {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of k)} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (τ : Spec (CommRingCat.of k) ⟶ T) (hτ : τ ≫ t = 𝟙 _)
    (x : SchemeHomOver t g) : (schemeHomOverComp τ hτ x).1 = τ ≫ x.1 := rfl

end MoreCalculus

section Structure

variable (L : RelativeGroupLaw k f)

theorem exists_kPoint [IsAlgClosed k] {X : Scheme.{u}} (tX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType tX] {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tX,
      x.1 (fieldPoint k) ∈ Z := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace tX
  obtain ⟨x, hxZ, hxc⟩ := nonempty_inter_closedPoints hne hZ
  have hxclosed : IsClosed ({x} : Set X) := hxc
  refine ⟨⟨pointOfClosedPoint tX x hxclosed, pointOfClosedPoint_comp _ _ _⟩, ?_⟩
  change (pointOfClosedPoint tX x hxclosed).base (fieldPoint k) ∈ Z
  rw [pointOfClosedPoint_apply]
  exact hxZ

theorem range_kPoint {X : Scheme.{u}} (x : Spec (CommRingCat.of k) ⟶ X) :
    Set.range x = {x (fieldPoint k)} := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    obtain rfl : s = fieldPoint k := Subsingleton.elim _ _
    rfl
  · rintro rfl; exact ⟨_, rfl⟩

/-- Lift a field-valued point into an open subscheme containing its image. -/
def kLift {X : Scheme.{u}} (U : X.Opens) (x : Spec (CommRingCat.of k) ⟶ X)
    (hx : x (fieldPoint k) ∈ U) : Spec (CommRingCat.of k) ⟶ (U : Scheme.{u}) :=
  IsOpenImmersion.lift U.ι x (by
    rw [Scheme.Opens.range_ι, range_kPoint, Set.singleton_subset_iff]; exact hx)

@[reassoc (attr := simp)]
theorem kLift_ι {X : Scheme.{u}} (U : X.Opens) (x : Spec (CommRingCat.of k) ⟶ X)
    (hx : x (fieldPoint k) ∈ U) : kLift U x hx ≫ U.ι = x :=
  IsOpenImmersion.lift_fac _ _ _

theorem irreducibleSpace_G [GeometricallyIrreducible f] : IrreducibleSpace G :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton f

theorem isReduced_pullback [Smooth f] {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k))
    [IsReduced Y] [IsLocallyNoetherian Y] : IsReduced (pullback f g) :=
  AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.snd f g)

/-- Left translation on the group scheme. -/
def ltrans (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : G ⟶ G :=
  (L.mul f (const f g) ⟨𝟙 G, Category.id_comp f⟩).1

theorem kpt_ltrans (g x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    x.1 ≫ ltrans L g = (L.mul (𝟙 _) g x).1 := by
  have h : schemeHomOverComp x.1 x.2 (L.mul f (const f g) ⟨𝟙 G, Category.id_comp f⟩) =
      L.mul (𝟙 _) g x := by
    rw [comp_mul, comp_const, const_id]
    congr 1
  exact congrArg Subtype.val h

/-- Translate the group coordinate of the action product. -/
def transl (p : P ⟶ Spec (CommRingCat.of k)) (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    pullback f p ⟶ pullback f p :=
  pair (L.mul (q f p) (const (q f p) g) (wGP f p)) (zGP f p)

theorem transl_q (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    transl L p g ≫ q f p = q f p := by
  simp only [transl, pair, q, pullback.lift_fst_assoc]
  exact (L.mul (q f p) (const (q f p) g) (wGP f p)).2

theorem comp_transl_wGP (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    schemeHomOverComp (transl L p g) (transl_q L g) (wGP f p) =
      L.mul (q f p) (const (q f p) g) (wGP f p) :=
  Subtype.ext (by simp only [GoodReductionJacobian.schemeHomOverComp_coe, transl, pair, wGP_coe,
    pullback.lift_fst])

theorem comp_transl_zGP (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    schemeHomOverComp (transl L p g) (transl_q L g) (zGP f p) = zGP f p :=
  Subtype.ext (by simp only [GoodReductionJacobian.schemeHomOverComp_coe, transl, pair, zGP_coe,
    pullback.lift_snd])

theorem transl_comp (g h : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    transl L p g ≫ transl L p h = transl L p (L.mul (𝟙 _) h g) := by
  rw [show transl L p h = pair (L.mul (q f p) (const (q f p) h) (wGP f p)) (zGP f p) from rfl,
    ← pair_comp (transl L p g) (transl_q L g), comp_mul, comp_const, comp_transl_wGP,
    comp_transl_zGP, ← L.mul_assoc, transl]
  congr 2
  rw [const, const, const, ← comp_mul]

theorem transl_one : transl L p (L.one _) = 𝟙 _ := by
  rw [transl, const, comp_one, L.one_mul, pair_wGP_zGP]

scoped instance isIso_transl (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    IsIso (transl L p g) :=
  ⟨⟨transl L p (L.inv _ g), by rw [transl_comp, L.inv_mul_cancel, transl_one],
    by rw [transl_comp, L.mul_inv_cancel, transl_one]⟩⟩

end Structure

section Triple

variable (L : RelativeGroupLaw k f) (a : PartialAction k f p)

/-- The product parametrizing a group point and a defined action pair. -/
abbrev Ω₁ : Scheme.{u} := pullback f (tD a)

/-- The structure morphism of the iterated action product. -/
abbrev t₁ : Ω₁ a ⟶ Spec (CommRingCat.of k) := pullback.fst f (tD a) ≫ f

theorem snd_tD : pullback.snd f (tD a) ≫ tD a = t₁ a := pullback.condition.symm

/-- The first group point of the iterated action product. -/
def u₁ : SchemeHomOver (t₁ a) f := ⟨pullback.fst f (tD a), rfl⟩

/-- The second group point of the iterated action product. -/
def w₁ : SchemeHomOver (t₁ a) f := schemeHomOverComp (pullback.snd f (tD a)) (snd_tD a) (wD a)

/-- The model point of the iterated action product. -/
def z₁ : SchemeHomOver (t₁ a) p := schemeHomOverComp (pullback.snd f (tD a)) (snd_tD a) (zD a)

/-- The inner action value on the iterated product. -/
def y₁ : SchemeHomOver (t₁ a) p := schemeHomOverComp (pullback.snd f (tD a)) (snd_tD a) (yD a)

theorem defined_w₁_z₁ : a.Defined (w₁ a) (z₁ a) := defined_comp a _ _ _ _ (defined_wD_zD a)

theorem act_w₁_z₁ : a.act (w₁ a) (z₁ a) (defined_w₁_z₁ a) = y₁ a :=
  act_comp a _ _ _ _ (defined_wD_zD a) _

/-- The pair defining the outer partial action. -/
def c₁ : Ω₁ a ⟶ pullback f p := pair (u₁ a) (y₁ a)

/-- The open domain where the outer action is defined. -/
def Ω' : (Ω₁ a).Opens := c₁ a ⁻¹ᵁ a.dom

/-- The open subset where the successive action is defined. -/
abbrev O : Scheme.{u} := (Ω' a : (Ω₁ a).Opens)

/-- The structure morphism of the successive-action domain. -/
abbrev tO : O a ⟶ Spec (CommRingCat.of k) := (Ω' a).ι ≫ t₁ a

/-- Restrict the first group point to the outer action domain. -/
def uO : SchemeHomOver (tO a) f := schemeHomOverComp (Ω' a).ι rfl (u₁ a)

/-- Restrict the second group point to the outer action domain. -/
def wO : SchemeHomOver (tO a) f := schemeHomOverComp (Ω' a).ι rfl (w₁ a)

/-- Restrict the model point to the outer action domain. -/
def zO : SchemeHomOver (tO a) p := schemeHomOverComp (Ω' a).ι rfl (z₁ a)

/-- Restrict the inner action value to the outer domain. -/
def yO : SchemeHomOver (tO a) p := schemeHomOverComp (Ω' a).ι rfl (y₁ a)

theorem defined_wO_zO : a.Defined (wO a) (zO a) := defined_comp a _ _ _ _ (defined_w₁_z₁ a)

theorem act_wO_zO : a.act (wO a) (zO a) (defined_wO_zO a) = yO a := by
  rw [yO, ← act_w₁_z₁]; exact act_comp a _ _ _ _ _ _

theorem defined_uO_yO : a.Defined (uO a) (yO a) := by
  rintro _ ⟨ω, rfl⟩
  rw [uO, yO, pair_comp, Scheme.Hom.comp_apply]
  exact ω.2

/-- The iterated action on its natural domain. -/
def φO : SchemeHomOver (tO a) p := a.act (uO a) (yO a) (defined_uO_yO a)

/-- The product of the two acting group points. -/
def μO : SchemeHomOver (tO a) f := L.mul (tO a) (uO a) (wO a)

theorem assoc_of_universal (hA : a.Defined (μO L a) (zO a))
    (hB : a.act (μO L a) (zO a) hA = φO a) : a.Assoc L := by
  intro T t γ δ x hd₁ hd₂
  obtain ⟨τD, hτD⟩ : ∃ τD, a.liftDom δ x hd₁ = τD := ⟨_, rfl⟩
  have hτDt : τD ≫ tD a = t := by rw [← hτD]; exact liftDom_tD a δ x hd₁
  have eδ : schemeHomOverComp τD hτDt (wD a) = δ := by
    subst hτD; exact ((eq_comp_liftDom a δ x hd₁).1).symm
  have ex : schemeHomOverComp τD hτDt (zD a) = x := by
    subst hτD; exact ((eq_comp_liftDom a δ x hd₁).2).symm
  have ey : schemeHomOverComp τD hτDt (yD a) = a.act δ x hd₁ := by
    subst hτD; exact (act_eq_comp_yD a δ x hd₁).symm
  obtain ⟨τ₁, hτ₁f, hτ₁s⟩ : ∃ τ₁ : T ⟶ Ω₁ a, τ₁ ≫ pullback.fst f (tD a) = γ.1 ∧
      τ₁ ≫ pullback.snd f (tD a) = τD :=
    ⟨pullback.lift γ.1 τD (by rw [γ.2, hτDt]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hτ₁t : τ₁ ≫ t₁ a = t := by rw [t₁, ← Category.assoc, hτ₁f]; exact γ.2
  have eu₁ : schemeHomOverComp τ₁ hτ₁t (u₁ a) = γ := Subtype.ext hτ₁f
  have ew₁ : schemeHomOverComp τ₁ hτ₁t (w₁ a) = δ := by
    rw [w₁, comp_comp, comp_congr hτ₁s _ hτDt, eδ]
  have ez₁ : schemeHomOverComp τ₁ hτ₁t (z₁ a) = x := by
    rw [z₁, comp_comp, comp_congr hτ₁s _ hτDt, ex]
  have ey₁ : schemeHomOverComp τ₁ hτ₁t (y₁ a) = a.act δ x hd₁ := by
    rw [y₁, comp_comp, comp_congr hτ₁s _ hτDt, ey]
  have hc₁ : τ₁ ≫ c₁ a = pair γ (a.act δ x hd₁) := by
    rw [c₁, ← pair_comp τ₁ hτ₁t, eu₁, ey₁]
  have hrange : Set.range τ₁ ⊆ ((Ω' a : (Ω₁ a).Opens) : Set (Ω₁ a)) := by
    rintro _ ⟨s, rfl⟩
    change (c₁ a) (τ₁ s) ∈ a.dom
    rw [← Scheme.Hom.comp_apply, hc₁]
    exact hd₂ ⟨s, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : T ⟶ O a, τ ≫ (Ω' a).ι = τ₁ :=
    ⟨IsOpenImmersion.lift (Ω' a).ι τ₁ (by rwa [Scheme.Opens.range_ι]),
      IsOpenImmersion.lift_fac _ _ _⟩
  have hτt : τ ≫ tO a = t := by rw [tO, ← Category.assoc, hτ, hτ₁t]
  have euO : schemeHomOverComp τ hτt (uO a) = γ := by
    rw [uO, comp_comp, comp_congr hτ _ hτ₁t, eu₁]
  have ewO : schemeHomOverComp τ hτt (wO a) = δ := by
    rw [wO, comp_comp, comp_congr hτ _ hτ₁t, ew₁]
  have ezO : schemeHomOverComp τ hτt (zO a) = x := by
    rw [zO, comp_comp, comp_congr hτ _ hτ₁t, ez₁]
  have eyO : schemeHomOverComp τ hτt (yO a) = a.act δ x hd₁ := by
    rw [yO, comp_comp, comp_congr hτ _ hτ₁t, ey₁]
  have eμ : schemeHomOverComp τ hτt (μO L a) = L.mul t γ δ := by
    rw [μO, comp_mul, euO, ewO]
  have hd₃' := defined_comp a τ hτt _ _ hA
  have hd₃ : a.Defined (L.mul t γ δ) x := by rwa [eμ, ezO] at hd₃'
  refine ⟨hd₃, Subtype.ext ?_⟩
  calc (a.act γ (a.act δ x hd₁) hd₂).1
      = (a.act _ _ (defined_comp a τ hτt _ _ (defined_uO_yO a))).1 :=
        act_coe_congr a euO.symm eyO.symm _ _
    _ = τ ≫ (φO a).1 := by rw [act_comp a τ hτt _ _ (defined_uO_yO a)]; rfl
    _ = τ ≫ (a.act (μO L a) (zO a) hA).1 := by rw [hB]
    _ = (a.act _ _ hd₃').1 := by rw [act_comp a τ hτt _ _ hA]; rfl
    _ = (a.act (L.mul t γ δ) x hd₃).1 := act_coe_congr a eμ ezO _ _

end Triple

section Equality

variable (L : RelativeGroupLaw k f) (a : PartialAction k f p)

/-- The comparison domain where the product action is defined. -/
def Dset : (O a).Opens := pair (μO L a) (zO a) ⁻¹ᵁ a.dom

/-- The open subset where both sides of associativity are defined. -/
abbrev OD : Scheme.{u} := (Dset L a : (O a).Opens)

/-- The structure morphism of the associativity comparison domain. -/
abbrev tOD : OD L a ⟶ Spec (CommRingCat.of k) := (Dset L a).ι ≫ tO a

/-- Restrict the first group point to the comparison domain. -/
def uOD : SchemeHomOver (tOD L a) f := schemeHomOverComp (Dset L a).ι rfl (uO a)

/-- Restrict the second group point to the comparison domain. -/
def wOD : SchemeHomOver (tOD L a) f := schemeHomOverComp (Dset L a).ι rfl (wO a)

/-- Restrict the model point to the comparison domain. -/
def zOD : SchemeHomOver (tOD L a) p := schemeHomOverComp (Dset L a).ι rfl (zO a)

/-- Restrict the inner action value to the comparison domain. -/
def yOD : SchemeHomOver (tOD L a) p := schemeHomOverComp (Dset L a).ι rfl (yO a)

/-- The iterated action on the comparison domain. -/
def φOD : SchemeHomOver (tOD L a) p := schemeHomOverComp (Dset L a).ι rfl (φO a)

/-- The product group point on the comparison domain. -/
def μOD : SchemeHomOver (tOD L a) f := L.mul (tOD L a) (uOD L a) (wOD L a)

theorem comp_μO : schemeHomOverComp (Dset L a).ι rfl (μO L a) = μOD L a := by
  rw [μO, comp_mul]; rfl

theorem defined_wOD_zOD : a.Defined (wOD L a) (zOD L a) :=
  defined_comp a _ _ _ _ (defined_wO_zO a)

theorem act_wOD_zOD : a.act (wOD L a) (zOD L a) (defined_wOD_zOD L a) = yOD L a := by
  rw [yOD, ← act_wO_zO]; exact act_comp a _ _ _ _ _ _

theorem defined_uOD_yOD : a.Defined (uOD L a) (yOD L a) :=
  defined_comp a _ _ _ _ (defined_uO_yO a)

theorem act_uOD_yOD : a.act (uOD L a) (yOD L a) (defined_uOD_yOD L a) = φOD L a :=
  act_comp a _ _ _ _ _ _

theorem defined_μOD_zOD : a.Defined (μOD L a) (zOD L a) := by
  rintro _ ⟨ω, rfl⟩
  rw [← comp_μO, zOD, pair_comp, Scheme.Hom.comp_apply]
  exact ω.2

/-- The product action on the comparison domain. -/
def ψOD : SchemeHomOver (tOD L a) p := a.act (μOD L a) (zOD L a) (defined_μOD_zOD L a)

theorem isReduced_OD [Smooth f] [IsIntegral P] [LocallyOfFiniteType p] : IsReduced (OD L a) := by
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsReduced (pullback f p) := isReduced_pullback p
  have : IsReduced (a.dom : Scheme.{u}) := isReduced_of_isOpenImmersion a.dom.ι
  have : IsReduced (Ω₁ a) := isReduced_pullback (tD a)
  have : IsReduced (O a) := isReduced_of_isOpenImmersion (Ω' a).ι
  exact isReduced_of_isOpenImmersion (Dset L a).ι

theorem irreducibleSpace_OD [GeometricallyIrreducible f] [UniversallyOpen f] [IsIntegral P]
    [Nonempty (OD L a)] : IrreducibleSpace (OD L a) := by
  have : Nonempty (O a) := Nonempty.map (Dset L a).ι inferInstance
  have : Nonempty (Ω₁ a) := Nonempty.map (Ω' a).ι inferInstance
  have : Nonempty (a.dom : Scheme.{u}) := Nonempty.map (pullback.snd f (tD a)) inferInstance
  have : IrreducibleSpace (a.dom : Scheme.{u}) := a.dom.ι.isOpenEmbedding.irreducibleSpace
  have : IrreducibleSpace (O a) := (Ω' a).ι.isOpenEmbedding.irreducibleSpace
  exact (Dset L a).ι.isOpenEmbedding.irreducibleSpace

theorem nonempty_kPoint_V [IsAlgClosed k] [LocallyOfFiniteType f] (V : G.Opens)
    [Nonempty (V : Scheme.{u})] :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (V.ι ≫ f)) := by
  have hne : (V : Set G).Nonempty :=
    ⟨(Classical.arbitrary V).1, (Classical.arbitrary V).2⟩
  obtain ⟨g, hg⟩ := exists_kPoint f V.2.isLocallyClosed hne
  exact ⟨⟨kLift V g.1 hg, by rw [← Category.assoc, kLift_ι]; exact g.2⟩⟩

variable {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f)

include hι in
theorem exists_kPoint_OD (hc : a.Compatible L V ι hι)
    (v₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (V.ι ≫ f)) :
    ∃ (o : Spec (CommRingCat.of k) ⟶ OD L a) (ho : o ≫ tOD L a = 𝟙 _),
      schemeHomOverComp o ho (uOD L a) = L.one _ ∧
      schemeHomOverComp o ho (wOD L a) = L.one _ ∧
      schemeHomOverComp o ho (zOD L a) = modelPoint ι hι v₀ := by
  obtain ⟨hde, eact⟩ := hc (𝟙 _) (L.one _) v₀ v₀ (by rw [L.one_mul])
  obtain ⟨d, hd⟩ : ∃ d, a.liftDom (L.one _) (modelPoint ι hι v₀) hde = d := ⟨_, rfl⟩
  have hdt : d ≫ tD a = 𝟙 _ := by rw [← hd]; exact liftDom_tD a _ _ hde
  have edw : schemeHomOverComp d hdt (wD a) = L.one _ := by
    subst hd; exact ((eq_comp_liftDom a _ _ hde).1).symm
  have edz : schemeHomOverComp d hdt (zD a) = modelPoint ι hι v₀ := by
    subst hd; exact ((eq_comp_liftDom a _ _ hde).2).symm
  have edy : schemeHomOverComp d hdt (yD a) = modelPoint ι hι v₀ := by
    subst hd; rw [← act_eq_comp_yD a _ _ hde, eact]
  obtain ⟨o₁, ho₁f, ho₁s⟩ : ∃ o₁ : Spec (CommRingCat.of k) ⟶ Ω₁ a,
      o₁ ≫ pullback.fst f (tD a) = (L.one (𝟙 _)).1 ∧ o₁ ≫ pullback.snd f (tD a) = d :=
    ⟨pullback.lift (L.one (𝟙 _)).1 d (by rw [(L.one _).2, hdt]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have ho₁t : o₁ ≫ t₁ a = 𝟙 _ := by rw [t₁, ← Category.assoc, ho₁f]; exact (L.one _).2
  have eu₁ : schemeHomOverComp o₁ ho₁t (u₁ a) = L.one _ := Subtype.ext ho₁f
  have ew₁ : schemeHomOverComp o₁ ho₁t (w₁ a) = L.one _ := by
    rw [w₁, comp_comp, comp_congr ho₁s _ hdt, edw]
  have ez₁ : schemeHomOverComp o₁ ho₁t (z₁ a) = modelPoint ι hι v₀ := by
    rw [z₁, comp_comp, comp_congr ho₁s _ hdt, edz]
  have ey₁ : schemeHomOverComp o₁ ho₁t (y₁ a) = modelPoint ι hι v₀ := by
    rw [y₁, comp_comp, comp_congr ho₁s _ hdt, edy]
  have hc₁ : o₁ ≫ c₁ a = pair (L.one _) (modelPoint ι hι v₀) := by
    rw [c₁, ← pair_comp o₁ ho₁t, eu₁, ey₁]
  have hoΩ' : o₁ (fieldPoint k) ∈ Ω' a := by
    change c₁ a (o₁ _) ∈ a.dom
    rw [← Scheme.Hom.comp_apply, hc₁]
    exact hde ⟨_, rfl⟩
  let oO := kLift (Ω' a) o₁ hoΩ'
  have hoO : oO ≫ (Ω' a).ι = o₁ := kLift_ι _ _ _
  have hoOt : oO ≫ tO a = 𝟙 _ := by rw [tO, ← Category.assoc, hoO, ho₁t]
  have euO : schemeHomOverComp oO hoOt (uO a) = L.one _ := by
    rw [uO, comp_comp, comp_congr hoO _ ho₁t, eu₁]
  have ewO : schemeHomOverComp oO hoOt (wO a) = L.one _ := by
    rw [wO, comp_comp, comp_congr hoO _ ho₁t, ew₁]
  have ezO : schemeHomOverComp oO hoOt (zO a) = modelPoint ι hι v₀ := by
    rw [zO, comp_comp, comp_congr hoO _ ho₁t, ez₁]
  have eμO : schemeHomOverComp oO hoOt (μO L a) = L.one _ := by
    rw [μO, comp_mul, euO, ewO, L.one_mul]
  have hoD : oO (fieldPoint k) ∈ Dset L a := by
    change pair (μO L a) (zO a) (oO _) ∈ a.dom
    rw [← Scheme.Hom.comp_apply, ← pair_comp oO hoOt, eμO, ezO]
    exact hde ⟨_, rfl⟩
  refine ⟨kLift (Dset L a) oO hoD, by rw [tOD, kLift_ι_assoc, hoOt], ?_, ?_, ?_⟩
  · rw [uOD, comp_comp, comp_congr (kLift_ι _ _ _) _ hoOt, euO]
  · rw [wOD, comp_comp, comp_congr (kLift_ι _ _ _) _ hoOt, ewO]
  · rw [zOD, comp_comp, comp_congr (kLift_ι _ _ _) _ hoOt, ezO]

include hι in
theorem ψOD_eq_φOD [IsAlgClosed k] [GeometricallyIrreducible f] [UniversallyOpen f] [Smooth f]
    [IsIntegral P] [LocallyOfFiniteType p] [IsSeparated p]
    [Nonempty (V : Scheme.{u})] [IsOpenImmersion ι] (hc : a.Compatible L V ι hι) :
    ψOD L a = φOD L a := by
  let W₁ : (OD L a).Opens := (zOD L a).1 ⁻¹ᵁ (Scheme.Hom.opensRange ι)
  let tW₁ : (W₁ : Scheme.{u}) ⟶ Spec (CommRingCat.of k) := W₁.ι ≫ tOD L a
  let u' : SchemeHomOver tW₁ f := schemeHomOverComp W₁.ι rfl (uOD L a)
  let w' : SchemeHomOver tW₁ f := schemeHomOverComp W₁.ι rfl (wOD L a)
  let z' : SchemeHomOver tW₁ p := schemeHomOverComp W₁.ι rfl (zOD L a)
  have hxrange : Set.range z'.1.base ⊆ Set.range ι.base := by
    rintro _ ⟨ω, rfl⟩
    exact ω.2
  let xLift : (W₁ : Scheme.{u}) ⟶ (V : Scheme.{u}) :=
    IsOpenImmersion.lift ι z'.1 hxrange
  have hxLift : xLift ≫ ι = z'.1 := IsOpenImmersion.lift_fac _ _ _
  let x' : SchemeHomOver tW₁ (V.ι ≫ f) :=
    ⟨xLift, by rw [← hι, ← Category.assoc, hxLift]; exact z'.2⟩
  have hxz : modelPoint ι hι x' = z' := Subtype.ext hxLift
  let VG : SchemeHomOver (V.ι ≫ f) f := ⟨V.ι, rfl⟩
  let vx : SchemeHomOver tW₁ f := L.mul tW₁ w' (NeronModelInfra.schemeHomOverComp x' VG)
  let uvx : SchemeHomOver tW₁ f := L.mul tW₁ u' vx
  let W₂ : (W₁ : Scheme.{u}).Opens := vx.1 ⁻¹ᵁ V ⊓ uvx.1 ⁻¹ᵁ V
  let jW : (W₂ : Scheme.{u}) ⟶ OD L a := W₂.ι ≫ W₁.ι
  have hjt : jW ≫ tOD L a = W₂.ι ≫ tW₁ := Category.assoc _ _ _
  let t₂ := W₂.ι ≫ tW₁
  let u₂ : SchemeHomOver t₂ f := schemeHomOverComp jW hjt (uOD L a)
  let w₂ : SchemeHomOver t₂ f := schemeHomOverComp jW hjt (wOD L a)
  let x₂ : SchemeHomOver t₂ (V.ι ≫ f) := schemeHomOverComp W₂.ι rfl x'
  have eu₂ : schemeHomOverComp W₂.ι rfl u' = u₂ := comp_comp _ _ _ _ _
  have ew₂ : schemeHomOverComp W₂.ι rfl w' = w₂ := comp_comp _ _ _ _ _
  have ez₂ : schemeHomOverComp jW hjt (zOD L a) = modelPoint ι hι x₂ := by
    rw [show modelPoint ι hι x₂ = schemeHomOverComp W₂.ι rfl (modelPoint ι hι x') from
      (comp_modelPoint ι hι _ _ _).symm, hxz]
    exact (comp_comp _ _ _ _ _).symm
  have evx : schemeHomOverComp W₂.ι rfl vx =
      L.mul t₂ w₂ (NeronModelInfra.schemeHomOverComp x₂ VG) := by
    rw [comp_mul, comp_nmi, ew₂]
  have euvx : schemeHomOverComp W₂.ι rfl uvx =
      L.mul t₂ u₂ (L.mul t₂ w₂ (NeronModelInfra.schemeHomOverComp x₂ VG)) := by
    rw [comp_mul, evx, eu₂]
  let vxV : SchemeHomOver t₂ (V.ι ≫ f) :=
    ⟨IsOpenImmersion.lift V.ι (schemeHomOverComp W₂.ι rfl vx).1
      (by rw [Scheme.Opens.range_ι]; rintro _ ⟨ω, rfl⟩; exact ω.2.1), by
      rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact (schemeHomOverComp W₂.ι rfl vx).2⟩
  have hvxV : NeronModelInfra.schemeHomOverComp vxV VG =
      L.mul t₂ w₂ (NeronModelInfra.schemeHomOverComp x₂ VG) := by
    rw [← evx]; exact Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  let uvxV : SchemeHomOver t₂ (V.ι ≫ f) :=
    ⟨IsOpenImmersion.lift V.ι (schemeHomOverComp W₂.ι rfl uvx).1
      (by rw [Scheme.Opens.range_ι]; rintro _ ⟨ω, rfl⟩; exact ω.2.2), by
      rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact (schemeHomOverComp W₂.ι rfl uvx).2⟩
  have huvxV : NeronModelInfra.schemeHomOverComp uvxV VG =
      L.mul t₂ u₂ (NeronModelInfra.schemeHomOverComp vxV VG) := by
    rw [hvxV, ← euvx]; exact Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  obtain ⟨hd1, e1⟩ := hc t₂ w₂ x₂ vxV hvxV
  obtain ⟨hd2, e2⟩ := hc t₂ u₂ vxV uvxV huvxV
  obtain ⟨hd3, e3⟩ := hc t₂ (L.mul t₂ u₂ w₂) x₂ uvxV (by rw [huvxV, hvxV, L.mul_assoc])
  have ey₂ : schemeHomOverComp jW hjt (yOD L a) = modelPoint ι hι vxV := by
    rw [← e1, ← act_wOD_zOD, ← act_comp a jW hjt _ _ (defined_wOD_zOD L a)
      (defined_comp a jW hjt _ _ (defined_wOD_zOD L a))]
    exact act_congr a rfl ez₂ _ _
  have hagree : jW ≫ (ψOD L a).1 = jW ≫ (φOD L a).1 := by
    have lhs : schemeHomOverComp jW hjt (ψOD L a) = modelPoint ι hι uvxV := by
      rw [← e3, ψOD, ← act_comp a jW hjt _ _ (defined_μOD_zOD L a)
        (defined_comp a jW hjt _ _ (defined_μOD_zOD L a))]
      exact act_congr a (by rw [μOD, comp_mul]) ez₂ _ _
    have rhs : schemeHomOverComp jW hjt (φOD L a) = modelPoint ι hι uvxV := by
      rw [← e2, ← act_uOD_yOD, ← act_comp a jW hjt _ _ (defined_uOD_yOD L a)
        (defined_comp a jW hjt _ _ (defined_uOD_yOD L a))]
      exact act_congr a rfl ey₂ _ _
    exact (congrArg Subtype.val lhs).trans (congrArg Subtype.val rhs).symm
  have : LocallyOfFiniteType f := inferInstance
  obtain ⟨v₀⟩ := nonempty_kPoint_V (f := f) V
  obtain ⟨o, ho, eou, eow, eoz⟩ := exists_kPoint_OD L a ι hι hc v₀
  have hoW₁ : o (fieldPoint k) ∈ W₁ := by
    change (zOD L a).1 (o _) ∈ Scheme.Hom.opensRange ι
    rw [← Scheme.Hom.comp_apply, ← comp_kpt_eq o ho, eoz, modelPoint_coe, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let oW := kLift W₁ o hoW₁
  have hoWt : oW ≫ tW₁ = 𝟙 _ := by rw [kLift_ι_assoc, ho]
  have eox : schemeHomOverComp oW hoWt x' = v₀ := by
    apply Subtype.ext
    rw [← cancel_mono ι, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc,
      hxLift, ← modelPoint_coe ι hι, ← eoz]
    change oW ≫ W₁.ι ≫ (zOD L a).1 = _
    rw [kLift_ι_assoc]; rfl
  have eow' : schemeHomOverComp oW hoWt w' = L.one _ := by
    rw [comp_comp, comp_congr (kLift_ι _ _ _) _ ho, eow]
  have eou' : schemeHomOverComp oW hoWt u' = L.one _ := by
    rw [comp_comp, comp_congr (kLift_ι _ _ _) _ ho, eou]
  have eovx : schemeHomOverComp oW hoWt vx = NeronModelInfra.schemeHomOverComp v₀ VG := by
    rw [comp_mul, comp_nmi, eow', eox, L.one_mul]
  have eouvx : schemeHomOverComp oW hoWt uvx = NeronModelInfra.schemeHomOverComp v₀ VG := by
    rw [comp_mul, eovx, eou', L.one_mul]
  have hv₀V : (NeronModelInfra.schemeHomOverComp v₀ VG).1 (fieldPoint k) ∈ V := by
    rw [NeronModelInfra.schemeHomOverComp_coe, Scheme.Hom.comp_apply]
    exact (v₀.1 _).2
  have : Nonempty (W₂ : Scheme.{u}) := ⟨⟨oW (fieldPoint k), by
    constructor
    · change vx.1 (oW _) ∈ V
      rw [← Scheme.Hom.comp_apply, ← comp_kpt_eq oW hoWt, eovx]; exact hv₀V
    · change uvx.1 (oW _) ∈ V
      rw [← Scheme.Hom.comp_apply, ← comp_kpt_eq oW hoWt, eouvx]; exact hv₀V⟩⟩
  have : Nonempty (OD L a) := Nonempty.map jW inferInstance
  have : IsReduced (OD L a) := isReduced_OD L a
  have : IrreducibleSpace (OD L a) := irreducibleSpace_OD L a
  have : IsDominant jW := ⟨jW.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _⟩
  apply Subtype.ext
  exact ext_of_isDominant_of_isSeparated p (by rw [(ψOD L a).2, (φOD L a).2]) jW hagree

end Equality

section Definedness

variable (L : RelativeGroupLaw k f) (a : PartialAction k f p)

theorem act_comp_μO {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f)
    [IsAlgClosed k] [GeometricallyIrreducible f] [UniversallyOpen f] [Smooth f]
    [IsIntegral P] [LocallyOfFiniteType p] [IsSeparated p]
    [Nonempty (V : Scheme.{u})] [IsOpenImmersion ι] (hc : a.Compatible L V ι hι)
    {T : Scheme.{u}} (τ : T ⟶ O a) {t : T ⟶ Spec (CommRingCat.of k)} (hτ : τ ≫ tO a = t)
    (hdef : a.Defined (schemeHomOverComp τ hτ (μO L a)) (schemeHomOverComp τ hτ (zO a))) :
    a.act _ _ hdef = schemeHomOverComp τ hτ (φO a) := by
  have hr : Set.range τ ⊆ ((Dset L a : (O a).Opens) : Set (O a)) := by
    rintro _ ⟨s, rfl⟩
    change pair (μO L a) (zO a) (τ s) ∈ a.dom
    rw [← Scheme.Hom.comp_apply, ← pair_comp τ hτ]
    exact hdef ⟨s, rfl⟩
  obtain ⟨τ', hτ'⟩ : ∃ τ' : T ⟶ OD L a, τ' ≫ (Dset L a).ι = τ :=
    ⟨IsOpenImmersion.lift (Dset L a).ι τ (by rwa [Scheme.Opens.range_ι]),
      IsOpenImmersion.lift_fac _ _ _⟩
  have hτ't : τ' ≫ tOD L a = t := by rw [tOD, ← Category.assoc, hτ', hτ]
  have e1 : schemeHomOverComp τ hτ (μO L a) = schemeHomOverComp τ' hτ't (μOD L a) := by
    rw [← comp_μO, comp_comp]; exact comp_congr hτ'.symm _ _ _
  have e2 : schemeHomOverComp τ hτ (zO a) = schemeHomOverComp τ' hτ't (zOD L a) := by
    rw [zOD, comp_comp]; exact comp_congr hτ'.symm _ _ _
  have e3 : schemeHomOverComp τ hτ (φO a) = schemeHomOverComp τ' hτ't (φOD L a) := by
    rw [φOD, comp_comp]; exact comp_congr hτ'.symm _ _ _
  rw [act_congr a e1 e2 hdef (defined_comp a τ' hτ't _ _ (defined_μOD_zOD L a)),
    act_comp a τ' hτ't _ _ (defined_μOD_zOD L a), e3, ← ψOD_eq_φOD L a ι hι hc]
  rfl

/-- The rational partial map underlying the given partial action. -/
def toPartialMap : (pullback f p).PartialMap P := ⟨a.dom, a.dense_dom, a.hom⟩

theorem le_dom_of_equiv [IsReduced (pullback f p)] [P.IsSeparated] (hm : a.Maximal)
    (π' : (pullback f p).PartialMap P) (h : π'.equiv (toPartialMap a)) : π'.domain ≤ a.dom := by
  have h1 : π'.toRationalMap = (toPartialMap a).toRationalMap :=
    Scheme.PartialMap.toRationalMap_eq_iff.mpr h
  have h2 : (toPartialMap a).toRationalMap.domain = a.dom := by
    refine hm (toPartialMap a).toRationalMap.domain (toPartialMap a).toRationalMap.toPartialMap.hom
      (toPartialMap a).le_domain_toRationalMap ?_
    exact (toPartialMap a).toPartialMap_toRationalMap_restrict
  calc π'.domain ≤ π'.toRationalMap.domain := π'.le_domain_toRationalMap
    _ = a.dom := by rw [h1, h2]

variable (u₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)

/-- Insert a fixed group point into the iterated action product. -/
def slice : (a.dom : Scheme.{u}) ⟶ Ω₁ a :=
  pullback.lift (tD a ≫ u₀.1) (𝟙 _) (by rw [Category.assoc, u₀.2, Category.comp_id,
    Category.id_comp])

@[reassoc (attr := simp)]
theorem slice_fst : slice a u₀ ≫ pullback.fst f (tD a) = tD a ≫ u₀.1 := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem slice_snd : slice a u₀ ≫ pullback.snd f (tD a) = 𝟙 _ := pullback.lift_snd _ _ _

theorem slice_t₁ : slice a u₀ ≫ t₁ a = tD a := by
  rw [t₁, slice_fst_assoc, u₀.2, Category.comp_id]

theorem comp_slice_u₁ : schemeHomOverComp (slice a u₀) (slice_t₁ a u₀) (u₁ a) = const (tD a) u₀ :=
  Subtype.ext (slice_fst a u₀)

theorem comp_slice_w₁ : schemeHomOverComp (slice a u₀) (slice_t₁ a u₀) (w₁ a) = wD a := by
  rw [w₁, comp_comp, comp_congr (slice_snd a u₀) _ (Category.id_comp _), comp_id']

theorem comp_slice_z₁ : schemeHomOverComp (slice a u₀) (slice_t₁ a u₀) (z₁ a) = zD a := by
  rw [z₁, comp_comp, comp_congr (slice_snd a u₀) _ (Category.id_comp _), comp_id']

theorem comp_slice_y₁ : schemeHomOverComp (slice a u₀) (slice_t₁ a u₀) (y₁ a) = yD a := by
  rw [y₁, comp_comp, comp_congr (slice_snd a u₀) _ (Category.id_comp _), comp_id']

/-- The slice domain where the iterated action is defined. -/
def E : (a.dom : Scheme.{u}).Opens := slice a u₀ ⁻¹ᵁ Ω' a

/-- The structure morphism of the fixed-translation domain. -/
abbrev tE : ((E a u₀ : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of k) :=
  (E a u₀).ι ≫ tD a

/-- Lift the slice to the outer action domain. -/
def sliceE : ((E a u₀ : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) ⟶ O a :=
  IsOpenImmersion.lift (Ω' a).ι ((E a u₀).ι ≫ slice a u₀) (by
    rintro _ ⟨e, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact e.2)

@[reassoc (attr := simp)]
theorem sliceE_ι : sliceE a u₀ ≫ (Ω' a).ι = (E a u₀).ι ≫ slice a u₀ := IsOpenImmersion.lift_fac _ _
    _

theorem sliceE_tO : sliceE a u₀ ≫ tO a = tE a u₀ := by
  rw [tO, sliceE_ι_assoc, slice_t₁]

theorem comp_sliceE_uO :
    schemeHomOverComp (sliceE a u₀) (sliceE_tO a u₀) (uO a) = const (tE a u₀) u₀ := by
  rw [uO, comp_comp, comp_congr (sliceE_ι a u₀) _ (by rw [Category.assoc, slice_t₁]),
    ← comp_comp _ rfl _ (slice_t₁ a u₀), comp_slice_u₁, comp_const]

theorem comp_sliceE_wO : schemeHomOverComp (sliceE a u₀) (sliceE_tO a u₀) (wO a) =
    schemeHomOverComp (E a u₀).ι rfl (wD a) := by
  rw [wO, comp_comp, comp_congr (sliceE_ι a u₀) _ (by rw [Category.assoc, slice_t₁]),
    ← comp_comp _ rfl _ (slice_t₁ a u₀), comp_slice_w₁]

theorem comp_sliceE_zO : schemeHomOverComp (sliceE a u₀) (sliceE_tO a u₀) (zO a) =
    schemeHomOverComp (E a u₀).ι rfl (zD a) := by
  rw [zO, comp_comp, comp_congr (sliceE_ι a u₀) _ (by rw [Category.assoc, slice_t₁]),
    ← comp_comp _ rfl _ (slice_t₁ a u₀), comp_slice_z₁]

/-- The translated pair used to extend the action domain. -/
def ε : ((E a u₀ : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) ⟶ pullback f p :=
  (E a u₀).ι ≫ a.dom.ι ≫ transl L p u₀

scoped instance : IsOpenImmersion (ε L a u₀) := by
  unfold ε; infer_instance

theorem ε_eq : ε L a u₀ = sliceE a u₀ ≫ pair (μO L a) (zO a) := by
  rw [← pair_comp (sliceE a u₀) (sliceE_tO a u₀), μO, comp_mul, comp_sliceE_uO, comp_sliceE_wO,
    comp_sliceE_zO, ε, transl, ← pair_comp (a.dom.ι) rfl, comp_mul, comp_const, ← wD, ← zD,
    ← pair_comp (E a u₀).ι rfl, comp_mul, comp_const]

theorem defined_μO_zO {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f)
    [IsAlgClosed k] [GeometricallyIrreducible f] [UniversallyOpen f] [Smooth f]
    [LocallyOfFiniteType f] [IsIntegral P] [LocallyOfFiniteType p] [IsSeparated p]
    [Nonempty (V : Scheme.{u})] [IsOpenImmersion ι] (hc : a.Compatible L V ι hι)
    (hm : a.Maximal) : a.Defined (μO L a) (zO a) := by
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsReduced (pullback f p) := isReduced_pullback p
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have : IrreducibleSpace G := irreducibleSpace_G (f := f)
  suffices h : ∀ ω : O a, ω ∈ Dset L a by rintro _ ⟨ω, rfl⟩; exact h ω
  intro ω
  by_contra hω
  obtain ⟨ωk, hωk⟩ := exists_kPoint (tO a) (Dset L a).2.isClosed_compl.isLocallyClosed ⟨ω, hω⟩
  let u₀ : SchemeHomOver (𝟙 _) f := schemeHomOverComp ωk.1 ωk.2 (uO a)
  let d₀ : Spec (CommRingCat.of k) ⟶ (a.dom : Scheme.{u}) :=
    ωk.1 ≫ (Ω' a).ι ≫ pullback.snd f (tD a)
  have hd₀t : d₀ ≫ tD a = 𝟙 _ := by
    change (ωk.1 ≫ (Ω' a).ι ≫ pullback.snd f (tD a)) ≫ tD a = 𝟙 _
    rw [Category.assoc, Category.assoc, snd_tD]; exact ωk.2
  have hd₀ : d₀ ≫ slice a u₀ = ωk.1 ≫ (Ω' a).ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, slice_fst, ← Category.assoc, hd₀t, Category.id_comp]; rfl
    · change (ωk.1 ≫ (Ω' a).ι ≫ pullback.snd f (tD a)) ≫ slice a u₀ ≫ pullback.snd f (tD a) = _
      rw [slice_snd, Category.comp_id, Category.assoc]
  have hd₀E : d₀ (fieldPoint k) ∈ E a u₀ := by
    change slice a u₀ (d₀ _) ∈ Ω' a
    rw [← Scheme.Hom.comp_apply, hd₀, Scheme.Hom.comp_apply]
    exact (ωk.1 _).2
  obtain ⟨v₀⟩ := nonempty_kPoint_V (f := f) V
  let VG : SchemeHomOver (V.ι ≫ f) f := ⟨V.ι, rfl⟩
  have hopen : IsOpen ((ltrans L u₀) ⁻¹' (V : Set G)) := V.2.preimage (ltrans L u₀).continuous
  have hne : ((ltrans L u₀) ⁻¹' (V : Set G)).Nonempty := by
    refine ⟨(L.mul (𝟙 _) (L.inv _ u₀) (NeronModelInfra.schemeHomOverComp v₀ VG)).1
      (fieldPoint k), ?_⟩
    change ltrans L u₀ _ ∈ V
    rw [← Scheme.Hom.comp_apply, kpt_ltrans, ← L.mul_assoc, L.mul_inv_cancel, L.one_mul,
      NeronModelInfra.schemeHomOverComp_coe, Scheme.Hom.comp_apply]
    exact (v₀.1 _).2
  obtain ⟨g₁, hg₁V, hg₁⟩ := exists_kPoint f (V.2.inter hopen).isLocallyClosed
    (nonempty_preirreducible_inter V.2 hopen ⟨_, (Classical.arbitrary V).2⟩ hne)
  have hug₁ : (L.mul (𝟙 _) u₀ g₁).1 (fieldPoint k) ∈ V := by
    rw [← kpt_ltrans, Scheme.Hom.comp_apply]; exact hg₁
  let g₁V : SchemeHomOver (𝟙 _) (V.ι ≫ f) :=
    ⟨kLift V g₁.1 hg₁V, by rw [← Category.assoc, kLift_ι]; exact g₁.2⟩
  let ug₁V : SchemeHomOver (𝟙 _) (V.ι ≫ f) :=
    ⟨kLift V (L.mul (𝟙 _) u₀ g₁).1 hug₁, by rw [← Category.assoc, kLift_ι]; exact (L.mul _ u₀ g₁).2⟩
  have hg₁G : NeronModelInfra.schemeHomOverComp g₁V VG = g₁ := Subtype.ext (kLift_ι V g₁.1 hg₁V)
  have hug₁G : NeronModelInfra.schemeHomOverComp ug₁V VG =
      L.mul (𝟙 _) u₀ (NeronModelInfra.schemeHomOverComp g₁V VG) := by
    rw [hg₁G]; exact Subtype.ext (kLift_ι V _ hug₁)
  obtain ⟨hde, eact⟩ := hc (𝟙 _) (L.one _) g₁V g₁V (by rw [L.one_mul])
  obtain ⟨hdu, -⟩ := hc (𝟙 _) u₀ g₁V ug₁V hug₁G
  obtain ⟨d₁, hd₁⟩ : ∃ d₁, a.liftDom (L.one _) (modelPoint ι hι g₁V) hde = d₁ := ⟨_, rfl⟩
  have hd₁t : d₁ ≫ tD a = 𝟙 _ := by rw [← hd₁]; exact liftDom_tD a _ _ hde
  have ed₁w : schemeHomOverComp d₁ hd₁t (wD a) = L.one _ := by
    subst hd₁; exact ((eq_comp_liftDom a _ _ hde).1).symm
  have ed₁z : schemeHomOverComp d₁ hd₁t (zD a) = modelPoint ι hι g₁V := by
    subst hd₁; exact ((eq_comp_liftDom a _ _ hde).2).symm
  have ed₁y : schemeHomOverComp d₁ hd₁t (yD a) = modelPoint ι hι g₁V := by
    subst hd₁; rw [← act_eq_comp_yD a _ _ hde, eact]
  have hd₁s : (d₁ ≫ slice a u₀) ≫ t₁ a = 𝟙 _ := by rw [Category.assoc, slice_t₁, hd₁t]
  have hd₁E : d₁ (fieldPoint k) ∈ E a u₀ := by
    change c₁ a (slice a u₀ (d₁ _)) ∈ a.dom
    have : d₁ ≫ slice a u₀ ≫ c₁ a = pair u₀ (modelPoint ι hι g₁V) := by
      rw [← Category.assoc, c₁, ← pair_comp _ hd₁s, ← comp_comp d₁ hd₁t _ (slice_t₁ a u₀),
        ← comp_comp d₁ hd₁t _ (slice_t₁ a u₀), comp_slice_u₁, comp_slice_y₁, comp_const,
        const_id, ed₁y]
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, this]
    exact hdu ⟨_, rfl⟩
  obtain ⟨d₁E, hd₁Eι⟩ : ∃ d₁E : Spec (CommRingCat.of k) ⟶ (E a u₀ : (a.dom : Scheme.{u}).Opens),
      d₁E ≫ (E a u₀).ι = d₁ := ⟨kLift (E a u₀) d₁ hd₁E, kLift_ι _ _ hd₁E⟩
  have hd₁Et : d₁E ≫ tE a u₀ = 𝟙 _ := by rw [tE, ← Category.assoc, hd₁Eι, hd₁t]
  have hεd₁ : d₁E ≫ ε L a u₀ = pair u₀ (modelPoint ι hι g₁V) := by
    rw [ε_eq, ← Category.assoc, ← pair_comp _ (by rw [Category.assoc, sliceE_tO, hd₁Et]),
      ← comp_comp d₁E hd₁Et _ (sliceE_tO a u₀), ← comp_comp d₁E hd₁Et _ (sliceE_tO a u₀),
      μO, comp_mul, comp_sliceE_uO, comp_sliceE_wO, comp_sliceE_zO, comp_mul,
      comp_const, const_id, comp_comp, comp_comp, comp_congr hd₁Eι _ hd₁t,
      comp_congr hd₁Eι _ hd₁t, ed₁w, ed₁z, L.mul_one]
  let E₃ : ((E a u₀ : (a.dom : Scheme.{u}).Opens) : Scheme.{u}).Opens := sliceE a u₀ ⁻¹ᵁ Dset L a
  have hd₁E₃ : d₁E (fieldPoint k) ∈ E₃ := by
    change pair (μO L a) (zO a) (sliceE a u₀ (d₁E _)) ∈ a.dom
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← ε_eq, hεd₁]
    exact hdu ⟨_, rfl⟩
  have hE₃ : E₃ ≤ ε L a u₀ ⁻¹ᵁ a.dom := by
    intro e he
    change ε L a u₀ e ∈ a.dom
    rw [ε_eq, Scheme.Hom.comp_apply]
    exact he
  let W : (pullback f p).Opens := ε L a u₀ ''ᵁ E₃
  have hWr : W ≤ Scheme.Hom.opensRange (ε L a u₀) := Scheme.Hom.image_le_opensRange _ _
  have hWd : W ≤ a.dom := by
    rintro _ ⟨e, he, rfl⟩; exact hE₃ he
  have hWdense : Dense (W : Set ↥(pullback f p)) :=
    W.2.dense ⟨_, ⟨_, hd₁E₃, rfl⟩⟩
  let π' : (pullback f p).PartialMap P :=
    ⟨Scheme.Hom.opensRange (ε L a u₀),
      (Scheme.Hom.opensRange (ε L a u₀)).2.dense ⟨_, ⟨d₁E (fieldPoint k), rfl⟩⟩,
      (Scheme.Hom.isoOpensRange (ε L a u₀)).inv ≫ sliceE a u₀ ≫ (φO a).1⟩
  have hequiv : π'.equiv (toPartialMap a) := by
    refine ⟨W, hWdense, hWr, hWd, ?_⟩
    change (pullback f p).homOfLE hWr ≫ (Scheme.Hom.isoOpensRange (ε L a u₀)).inv ≫ sliceE a u₀ ≫
        (φO a).1 = (pullback f p).homOfLE hWd ≫ a.hom
    have hiso : (Scheme.Hom.isoImage (ε L a u₀) E₃).hom ≫ (pullback f p).homOfLE hWr ≫
        (Scheme.Hom.isoOpensRange (ε L a u₀)).inv = E₃.ι := by
      rw [← cancel_mono (ε L a u₀), Category.assoc, Category.assoc,
        Scheme.Hom.isoOpensRange_inv_comp, Scheme.homOfLE_ι, Scheme.Hom.isoImage_hom_ι]
    have hτ : (E₃.ι ≫ sliceE a u₀) ≫ tO a = E₃.ι ≫ tE a u₀ := by rw [Category.assoc, sliceE_tO]
    have hdef : a.Defined (schemeHomOverComp (E₃.ι ≫ sliceE a u₀) hτ (μO L a))
        (schemeHomOverComp (E₃.ι ≫ sliceE a u₀) hτ (zO a)) := by
      rintro _ ⟨e, rfl⟩
      rw [pair_comp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact e.2
    have hlift : a.liftDom _ _ hdef = (Scheme.Hom.isoImage (ε L a u₀) E₃).hom ≫
        (pullback f p).homOfLE hWd :=
      liftDom_eq a _ _ hdef _ (by
        rw [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoImage_hom_ι, pair_comp, ε_eq,
          Category.assoc])
    have key := congrArg Subtype.val (act_comp_μO L a ι hι hc (E₃.ι ≫ sliceE a u₀) hτ hdef)
    rw [act_coe, hlift, GoodReductionJacobian.schemeHomOverComp_coe] at key
    simp only [Category.assoc] at key
    rw [← cancel_epi (Scheme.Hom.isoImage (ε L a u₀) E₃).hom, reassoc_of% hiso]
    exact key.symm
  have hle := le_dom_of_equiv a hm π' hequiv
  obtain ⟨d₀E, hd₀Eι⟩ : ∃ d₀E : Spec (CommRingCat.of k) ⟶ (E a u₀ : (a.dom : Scheme.{u}).Opens),
      d₀E ≫ (E a u₀).ι = d₀ := ⟨kLift (E a u₀) d₀ hd₀E, kLift_ι _ _ hd₀E⟩
  have hd₀ε : ε L a u₀ (d₀E (fieldPoint k)) ∈ a.dom :=
    hle ⟨_, rfl⟩
  have hsl : d₀E ≫ sliceE a u₀ = ωk.1 := by
    rw [← cancel_mono (Ω' a).ι, Category.assoc, sliceE_ι, ← Category.assoc, hd₀Eι, hd₀]
  apply hωk
  change pair (μO L a) (zO a) (ωk.1 _) ∈ a.dom
  rw [← hsl, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (sliceE a u₀), ← ε_eq]
  exact hd₀ε

end Definedness

section Assembly

theorem unitActs_and_assoc (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    [Smooth f] (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hc : a.Compatible L V ι hι) (hm : a.Maximal) :
    a.UnitActs L ∧ a.Assoc L := by
  have : GeometricallyIrreducible f := geometricallyIrreducible L
  have hA : a.Defined (μO L a) (zO a) := defined_μO_zO L a ι hι hc hm
  suffices hB : a.act (μO L a) (zO a) hA = φO a from
    ⟨fun {T} => unitActs L a V ι hι hc (T := T), fun {T} => assoc_of_universal L a hA hB (T := T)⟩
  have h1 : schemeHomOverComp (𝟙 (O a)) (Category.id_comp _) (μO L a) = μO L a := comp_id' _ _
  have h2 : schemeHomOverComp (𝟙 (O a)) (Category.id_comp _) (zO a) = zO a := comp_id' _ _
  have h3 : schemeHomOverComp (𝟙 (O a)) (Category.id_comp _) (φO a) = φO a := comp_id' _ _
  have hdef : a.Defined (schemeHomOverComp (𝟙 (O a)) (Category.id_comp _) (μO L a))
      (schemeHomOverComp (𝟙 (O a)) (Category.id_comp _) (zO a)) := by rwa [h1, h2]
  rw [← act_congr a h1 h2 hdef hA, act_comp_μO L a ι hι hc (𝟙 (O a)) (Category.id_comp _) hdef, h3]

end Assembly

end ActionLaws

end PartialAction

end GoodReductionJacobian
end AbelianVarieties.NOSProofs.PartialActionLaws

end

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits hiding pair
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AbelianVarieties.NOSProofs.PartialActionLaws.GoodReductionJacobian

open AbelianVarieties.NOSProofs.PartialActionLaws.GoodReductionJacobian.PartialAction.ActionLaws
  (unitActs_and_assoc)

namespace GoodReductionJacobian.PartialAction

theorem unitActs_and_assoc_of_compatible_of_maximal
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hc : a.Compatible L V ι hι) (hm : a.Maximal) :
    a.UnitActs L ∧ a.Assoc L :=
  unitActs_and_assoc k f L p V ι hι a hc hm

end GoodReductionJacobian.PartialAction

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits hiding pair
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

universe u

noncomputable section

namespace AbelianVarieties.NOSProofs.PartialActionBoundary

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
namespace PartialAction
open _root_.GoodReductionJacobian.PartialAction
namespace BoundaryStability

open
  AbelianVarieties.NOSProofs.PartialActionTransport.GoodReductionJacobian.PartialAction.OpTransport
  (mul_val_congr inv_val_congr inv_natural geometricallyIrreducible)
open AbelianVarieties.NOSProofs.PartialActionTransport.GoodReductionJacobian.PartialAction

section Main

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f)
  {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
  (D : P.Opens) (τ : (D : Scheme.{u}) ⟶ G) (hτ : τ ≫ f = D.ι ≫ p)
  {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u}))
  [IsOpenImmersion ι] (hτι : ι ≫ τ = V.ι)
  (a : PartialAction k f p)

omit [IsOpenImmersion ι] in
include hτ hτι in
theorem j_comp : (ι ≫ D.ι) ≫ p = V.ι ≫ f := by
  rw [Category.assoc, ← hτ, ← Category.assoc, hτι]

/-- The action product restricted to the open model. -/
abbrev GV : Scheme.{u} := pullback (pullback.snd f p) (ι ≫ D.ι)

/-- The structure morphism of the restricted action product. -/
abbrev tGV : GV f p D ι ⟶ Spec (CommRingCat.of k) :=
  (pullback.fst (pullback.snd f p) (ι ≫ D.ι) ≫ pullback.fst f p) ≫ f

/-- The acting group point on the pulled-back model chart. -/
def γ₀ : SchemeHomOver (tGV f p D ι) f :=
  ⟨pullback.fst (pullback.snd f p) (ι ≫ D.ι) ≫ pullback.fst f p, rfl⟩

omit [IsOpenImmersion ι] in
include hτ hτι in
theorem vG₀_over : (pullback.snd (pullback.snd f p) (ι ≫ D.ι) ≫ V.ι) ≫ f = tGV f p D ι := by
  have h1 : pullback.snd (pullback.snd f p) (ι ≫ D.ι) ≫ (ι ≫ D.ι) =
      pullback.fst (pullback.snd f p) (ι ≫ D.ι) ≫ pullback.snd f p := pullback.condition.symm
  calc (pullback.snd (pullback.snd f p) (ι ≫ D.ι) ≫ V.ι) ≫ f
      = pullback.snd (pullback.snd f p) (ι ≫ D.ι) ≫ (V.ι ≫ f) := Category.assoc _ _ _
    _ = pullback.snd (pullback.snd f p) (ι ≫ D.ι) ≫ ((ι ≫ D.ι) ≫ p) := by rw [j_comp f p D τ hτ ι
      hτι]
    _ = (pullback.snd (pullback.snd f p) (ι ≫ D.ι) ≫ (ι ≫ D.ι)) ≫ p := (Category.assoc _ _ _).symm
    _ = (pullback.fst (pullback.snd f p) (ι ≫ D.ι) ≫ pullback.snd f p) ≫ p := by rw [h1]
    _ = pullback.fst (pullback.snd f p) (ι ≫ D.ι) ≫ (pullback.fst f p ≫ f) := by
        rw [Category.assoc, ← pullback.condition]
    _ = tGV f p D ι := (Category.assoc _ _ _).symm

/-- The chosen open-model point regarded as a group point. -/
def vG₀ : SchemeHomOver (tGV f p D ι) f :=
  ⟨pullback.snd (pullback.snd f p) (ι ≫ D.ι) ≫ V.ι, vG₀_over f p D τ hτ ι hτι⟩

/-- The chosen point of the open model. -/
def v₀ : SchemeHomOver (tGV f p D ι) (V.ι ≫ f) :=
  ⟨pullback.snd (pullback.snd f p) (ι ≫ D.ι), by
    rw [← Category.assoc]
    exact vG₀_over f p D τ hτ ι hτι⟩

/-- Multiply the group point with the open-model point. -/
def m₀ : SchemeHomOver (tGV f p D ι) f := L.mul _ (γ₀ f p D ι) (vG₀ f p D τ hτ ι hτι)

/-- The open locus where multiplication stays in the chosen model. -/
abbrev W : (GV f p D ι).Opens := (m₀ f L p D τ hτ ι hτι).1 ⁻¹ᵁ V

/-- The structure morphism of the chart multiplication domain. -/
abbrev tW : ((W f L p D τ hτ ι hτι : (GV f p D ι).Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of k) :=
  (W f L p D τ hτ ι hτι).ι ≫ tGV f p D ι

/-- Restrict the acting group point to the chart multiplication domain. -/
def γW : SchemeHomOver (tW f L p D τ hτ ι hτι) f := schemeHomOverComp (W f L p D τ hτ ι hτι).ι rfl
    (γ₀ f p D ι)
/-- Restrict the open-model point to the chart multiplication domain. -/
def vW : SchemeHomOver (tW f L p D τ hτ ι hτι) (V.ι ≫ f) := schemeHomOverComp (W f L p D τ hτ ι
    hτι).ι rfl (v₀ f p D τ hτ ι hτι)
/-- The restricted open-model point regarded as a group point. -/
def vGW : SchemeHomOver (tW f L p D τ hτ ι hτι) f := schemeHomOverComp (W f L p D τ hτ ι hτι).ι rfl
    (vG₀ f p D τ hτ ι hτι)

omit [IsOpenImmersion ι] in
theorem range_Wι_m₀ : Set.range ((W f L p D τ hτ ι hτι).ι ≫ (m₀ f L p D τ hτ ι hτι).1) ⊆ Set.range
    V.ι := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact w.2

/-- Lift the product point back to the open model. -/
def wW : SchemeHomOver (tW f L p D τ hτ ι hτι) (V.ι ≫ f) :=
  ⟨IsOpenImmersion.lift V.ι _ (range_Wι_m₀ f L p D τ hτ ι hτι), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, (m₀ f L p D τ hτ ι hτι).2]⟩

omit [IsOpenImmersion ι] in
theorem wW_ι : (wW f L p D τ hτ ι hτι).1 ≫ V.ι = (W f L p D τ hτ ι hτι).ι ≫ (m₀ f L p D τ hτ ι
    hτι).1 :=
  IsOpenImmersion.lift_fac _ _ _

omit [IsOpenImmersion ι] in
theorem compat_hyp :
    NeronModelInfra.schemeHomOverComp (wW f L p D τ hτ ι hτι) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f)
      f) =
      L.mul _ (γW f L p D τ hτ ι hτι)
        (NeronModelInfra.schemeHomOverComp (vW f L p D τ hτ ι hτι) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι
          ≫ f) f)) := by
  have e : NeronModelInfra.schemeHomOverComp (vW f L p D τ hτ ι hτι) (⟨V.ι, rfl⟩ : SchemeHomOver
    (V.ι ≫ f) f) =
      vGW f L p D τ hτ ι hτι :=
    Subtype.ext (by
      simp only [vW, vGW, v₀, vG₀, GoodReductionJacobian.schemeHomOverComp_coe,
        NeronModelInfra.schemeHomOverComp_coe, Category.assoc])
  rw [e]
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, wW_ι]
  change _ = (L.mul _ (schemeHomOverComp _ rfl (γ₀ f p D ι)) (schemeHomOverComp _ rfl (vG₀ f p D τ
    hτ ι hτι))).1
  rw [← L.mul_natural]
  rfl

variable (hc : a.Compatible L V (ι ≫ D.ι) (j_comp f p D τ hτ ι hτι))

include hc in
omit [IsOpenImmersion ι] in
theorem definedW : a.Defined (γW f L p D τ hτ ι hτι) (modelPoint (ι ≫ D.ι) (j_comp f p D τ hτ ι hτι)
    (vW f L p D τ hτ ι hτι)) :=
  (hc _ _ _ _ (compat_hyp f L p D τ hτ ι hτι)).choose

include hc in
omit [IsOpenImmersion ι] in
theorem actW : a.act _ _ (definedW f L p D τ hτ ι hτι a hc) =
    modelPoint (ι ≫ D.ι) (j_comp f p D τ hτ ι hτι) (wW f L p D τ hτ ι hτι) :=
  (hc _ _ _ _ (compat_hyp f L p D τ hτ ι hτι)).choose_spec

/-- Map the compatible chart into the partial-action domain. -/
def θd : ((W f L p D τ hτ ι hτι : (GV f p D ι).Opens) : Scheme.{u}) ⟶ (a.dom : Scheme.{u}) :=
  a.liftDom _ _ (definedW f L p D τ hτ ι hτι a hc)

omit [IsOpenImmersion ι] in
theorem θd_ι : θd f L p D τ hτ ι hτι a hc ≫ a.dom.ι = (W f L p D τ hτ ι hτι).ι ≫ pullback.fst _ _ :=
    by
  change a.liftDom _ _ (definedW f L p D τ hτ ι hτι a hc) ≫ a.dom.ι = _
  rw [liftDom_ι]
  apply pullback.hom_ext
  · erw [pullback.lift_fst]
    simp only [γW, γ₀, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]
  · erw [pullback.lift_snd]
    simp only [modelPoint_coe, vW, v₀, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]
    rw [pullback.condition]

omit [IsOpenImmersion ι] in
theorem θd_hom : θd f L p D τ hτ ι hτι a hc ≫ a.hom = (wW f L p D τ hτ ι hτι).1 ≫ ι ≫ D.ι := by
  have := congrArg Subtype.val (actW f L p D τ hτ ι hτι a hc)
  simp only [act_coe, modelPoint_coe] at this
  exact this

scoped instance : IsOpenImmersion (θd f L p D τ hτ ι hτι a hc) := by
  have : IsOpenImmersion (θd f L p D τ hτ ι hτι a hc ≫ a.dom.ι) := by
    rw [θd_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ a.dom.ι

/-- The preimage of the proper boundary chart under the partial action. -/
abbrev U : (a.dom : Scheme.{u}).Opens := a.hom ⁻¹ᵁ D

omit [IsOpenImmersion ι] in
theorem range_θd : Set.range (θd f L p D τ hτ ι hτι a hc) ⊆ Set.range (U f p D a).ι := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  change a.hom (θd f L p D τ hτ ι hτι a hc w) ∈ (D : Set P)
  rw [← Scheme.Hom.comp_apply, θd_hom, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact (ι _).2

/-- Lift the chart map to the subdomain mapping into the boundary open. -/
def θU : ((W f L p D τ hτ ι hτι : (GV f p D ι).Opens) : Scheme.{u}) ⟶ ((U f p D a : (a.dom :
    Scheme.{u}).Opens) : Scheme.{u}) :=
  IsOpenImmersion.lift (U f p D a).ι _ (range_θd f L p D τ hτ ι hτι a hc)

omit [IsOpenImmersion ι] in
theorem θU_ι : θU f L p D τ hτ ι hτι a hc ≫ (U f p D a).ι = θd f L p D τ hτ ι hτι a hc :=
  IsOpenImmersion.lift_fac _ _ _

scoped instance : IsOpenImmersion (θU f L p D τ hτ ι hτι a hc) := by
  have : IsOpenImmersion (θU f L p D τ hτ ι hτι a hc ≫ (U f p D a).ι) := by
    rw [θU_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ (U f p D a).ι

/-- The structure morphism of the chart comparison domain. -/
abbrev tU : ((U f p D a : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of k) :=
  ((U f p D a).ι ≫ a.dom.ι ≫ pullback.fst f p) ≫ f

/-- The acting group point on the restricted domain. -/
def γU : SchemeHomOver (tU f p D a) f := ⟨(U f p D a).ι ≫ a.dom.ι ≫ pullback.fst f p, rfl⟩

theorem range_Uι_hom : Set.range ((U f p D a).ι ≫ a.hom) ⊆ Set.range D.ι := by
  rintro _ ⟨u, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact u.2

/-- Lift the action value to the boundary open. -/
def hU : ((U f p D a : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) ⟶ (D : Scheme.{u}) :=
  IsOpenImmersion.lift D.ι _ (range_Uι_hom f p D a)

theorem hU_ι : hU f p D a ≫ D.ι = (U f p D a).ι ≫ a.hom := IsOpenImmersion.lift_fac _ _ _

include hτ in
theorem gU_over : (hU f p D a ≫ τ) ≫ f = tU f p D a := by
  calc (hU f p D a ≫ τ) ≫ f = hU f p D a ≫ (τ ≫ f) := Category.assoc _ _ _
    _ = hU f p D a ≫ (D.ι ≫ p) := by rw [hτ]
    _ = (hU f p D a ≫ D.ι) ≫ p := (Category.assoc _ _ _).symm
    _ = ((U f p D a).ι ≫ a.hom) ≫ p := by rw [hU_ι]
    _ = (U f p D a).ι ≫ (a.hom ≫ p) := Category.assoc _ _ _
    _ = (U f p D a).ι ≫ (a.dom.ι ≫ pullback.snd f p ≫ p) := by rw [a.hom_comp]
    _ = (U f p D a).ι ≫ (a.dom.ι ≫ (pullback.fst f p ≫ f)) := by rw [← pullback.condition]
    _ = tU f p D a := by simp only [tU, Category.assoc]

/-- The group point obtained from the lifted action value. -/
def gU : SchemeHomOver (tU f p D a) f := ⟨hU f p D a ≫ τ, gU_over f p D τ hτ a⟩

/-- Recover the second group point from the action value. -/
def βU : SchemeHomOver (tU f p D a) f := L.mul _ (L.inv _ (γU f p D a)) (gU f p D τ hτ a)

/-- The pair used to compare the action with the proper boundary model. -/
def ψ : ((U f p D a : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) ⟶ pullback p f :=
  pullback.lift ((U f p D a).ι ≫ a.dom.ι ≫ pullback.snd f p) (βU f L p D τ hτ a).1 (by
    rw [(βU f L p D τ hτ a).2, Category.assoc, Category.assoc, ← pullback.condition]
    simp only [tU, Category.assoc])

/-- The graph of the boundary-model morphism. -/
def Γ : (D : Scheme.{u}) ⟶ pullback p f := pullback.lift D.ι τ hτ.symm

theorem isClosed_range_Γ [IsSeparated p] [IsProper τ] : IsClosed (Set.range (Γ f p D τ hτ)) := by
  have : IsProper (Γ f p D τ hτ ≫ pullback.snd p f) := by
    rw [Γ]; erw [pullback.lift_snd]; infer_instance
  have : IsProper (Γ f p D τ hτ) := IsProper.of_comp (Γ f p D τ hτ) (pullback.snd p f)
  exact (Γ f p D τ hτ).isClosedMap.isClosed_range

include hτι in
omit [IsOpenImmersion ι] in
theorem θU_hU : θU f L p D τ hτ ι hτι a hc ≫ hU f p D a = (wW f L p D τ hτ ι hτι).1 ≫ ι := by
  rw [← cancel_mono D.ι, Category.assoc, hU_ι, ← Category.assoc, θU_ι, θd_hom, Category.assoc]

include hτι in
omit [IsOpenImmersion ι] in
theorem θU_βU : θU f L p D τ hτ ι hτι a hc ≫ (βU f L p D τ hτ a).1 =
    (vW f L p D τ hτ ι hτι).1 ≫ V.ι := by
  have et : θU f L p D τ hτ ι hτι a hc ≫ tU f p D a = tW f L p D τ hτ ι hτι := by
    simp only [tU, tW, tGV, ← Category.assoc]
    rw [θU_ι, θd_ι]
  let X' : SchemeHomOver (θU f L p D τ hτ ι hτι a hc ≫ tU f p D a) f :=
    schemeHomOverComp _ rfl (γU f p D a)
  let Y' : SchemeHomOver (θU f L p D τ hτ ι hτι a hc ≫ tU f p D a) f :=
    schemeHomOverComp _ rfl (gU f p D τ hτ a)
  let Z' : SchemeHomOver (θU f L p D τ hτ ι hτι a hc ≫ tU f p D a) f :=
    ⟨(vW f L p D τ hτ ι hτι).1 ≫ V.ι, by rw [et]; exact (vGW f L p D τ hτ ι hτι).2⟩
  have hX : X'.1 = (γW f L p D τ hτ ι hτι).1 := by
    simp only [X', GoodReductionJacobian.schemeHomOverComp_coe, γU, γW, γ₀, ← Category.assoc, θU_ι,
      θd_ι]
  have hY : Y'.1 = (L.mul _ X' Z').1 := by
    have h1 : Y'.1 = (L.mul _ (γW f L p D τ hτ ι hτι) (vGW f L p D τ hτ ι hτι)).1 := by
      simp only [Y', GoodReductionJacobian.schemeHomOverComp_coe, gU]
      rw [← Category.assoc, θU_hU, Category.assoc, hτι, wW_ι]
      change _ = (L.mul _ (schemeHomOverComp _ rfl (γ₀ f p D ι)) (schemeHomOverComp _ rfl (vG₀ f p D
        τ hτ ι hτι))).1
      rw [← L.mul_natural]; rfl
    rw [h1]
    exact mul_val_congr L et.symm _ _ _ _ hX.symm rfl
  have key : schemeHomOverComp _ rfl (βU f L p D τ hτ a) = Z' := by
    rw [βU, L.mul_natural, inv_natural]
    change L.mul _ (L.inv _ X') Y' = Z'
    rw [Subtype.ext hY, OpTransport.inv_mul_cancel_left]
  exact congrArg Subtype.val key

include hτι in
omit [IsOpenImmersion ι] in
theorem θU_ψ : θU f L p D τ hτ ι hτι a hc ≫ ψ f L p D τ hτ a =
    ((vW f L p D τ hτ ι hτι).1 ≫ ι) ≫ Γ f p D τ hτ := by
  apply pullback.hom_ext
  · rw [Category.assoc, ψ, Category.assoc, Γ]
    erw [pullback.lift_fst, pullback.lift_fst]
    rw [← Category.assoc, θU_ι, ← Category.assoc, θd_ι, Category.assoc, pullback.condition]
    simp only [vW, v₀, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]
  · rw [Category.assoc, ψ, Category.assoc, Γ]
    erw [pullback.lift_snd, pullback.lift_snd]
    rw [θU_βU, Category.assoc, hτι]

include hτ hτι in
/-- Insert the unit group point and the model inclusion into the action product. -/
def σX : (V : Scheme.{u}) ⟶ pullback f p :=
  pullback.lift (L.one (V.ι ≫ f)).1 (ι ≫ D.ι) (by rw [(L.one (V.ι ≫ f)).2, j_comp f p D τ hτ ι hτι])

/-- Lift the unit-section pair into the pulled-back chart. -/
def σ : (V : Scheme.{u}) ⟶ GV f p D ι :=
  pullback.lift (σX f L p D τ hτ ι hτι) (𝟙 _) (by
    rw [Category.id_comp]; exact pullback.lift_snd _ _ _)

omit [IsOpenImmersion ι] in
theorem σ_m₀ : σ f L p D τ hτ ι hτι ≫ (m₀ f L p D τ hτ ι hτι).1 = V.ι := by
  have hfst : σ f L p D τ hτ ι hτι ≫ pullback.fst (pullback.snd f p) (ι ≫ D.ι) = σX f L p D τ hτ ι
    hτι :=
    pullback.lift_fst _ _ _
  have hsnd : σ f L p D τ hτ ι hτι ≫ pullback.snd (pullback.snd f p) (ι ≫ D.ι) = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hσG : σ f L p D τ hτ ι hτι ≫ (γ₀ f p D ι).1 = (L.one (V.ι ≫ f)).1 := by
    change σ f L p D τ hτ ι hτι ≫ (pullback.fst _ _ ≫ pullback.fst f p) = _
    rw [← Category.assoc, hfst]
    exact pullback.lift_fst _ _ _
  have hσV : σ f L p D τ hτ ι hτι ≫ (vG₀ f p D τ hτ ι hτι).1 = V.ι := by
    change σ f L p D τ hτ ι hτι ≫ (pullback.snd _ _ ≫ V.ι) = _
    rw [← Category.assoc, hsnd, Category.id_comp]
  have et : σ f L p D τ hτ ι hτι ≫ tGV f p D ι = V.ι ≫ f := by
    change σ f L p D τ hτ ι hτι ≫ ((γ₀ f p D ι).1 ≫ f) = _
    rw [← Category.assoc, hσG]
    exact (L.one (V.ι ≫ f)).2
  have h1 : (schemeHomOverComp (σ f L p D τ hτ ι hτι) rfl (m₀ f L p D τ hτ ι hτι)).1 =
      (L.mul _ (L.one (V.ι ≫ f)) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)).1 := by
    rw [m₀, L.mul_natural]
    exact mul_val_congr L et _ _ _ _ hσG hσV
  rw [L.one_mul] at h1
  exact h1

scoped instance [Nonempty (V : Scheme.{u})] : Nonempty ((W f L p D τ hτ ι hτι : (GV f p D ι).Opens)
    : Scheme.{u}) := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (V : Scheme.{u}))
  refine ⟨⟨σ f L p D τ hτ ι hτι v, ?_⟩⟩
  change (m₀ f L p D τ hτ ι hτι).1 (σ f L p D τ hτ ι hτι v) ∈ (V : Set G)
  rw [← Scheme.Hom.comp_apply, σ_m₀]
  exact v.2

include L hτ hτι hc in
theorem snd_mem [IsAlgClosed k] [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P] [IsProper τ] [Nonempty (V : Scheme.{u})]
    (z : ↥(a.dom : Scheme.{u})) (hz : a.hom.base z ∈ (D : Set P)) :
    (pullback.snd f p).base (a.dom.ι.base z) ∈ (D : Set P) := by
  have : GeometricallyIrreducible f := geometricallyIrreducible L
  have : IrreducibleSpace ↥(pullback f p) := inferInstance
  have : Nonempty ((U f p D a : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) := ⟨⟨z, hz⟩⟩
  have : Nonempty (a.dom : Scheme.{u}) := ⟨z⟩
  have : IrreducibleSpace (a.dom : Scheme.{u}) := a.dom.ι.isOpenEmbedding.irreducibleSpace
  have : IrreducibleSpace ((U f p D a : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) :=
    (U f p D a).ι.isOpenEmbedding.irreducibleSpace
  let S : Set ↥((U f p D a : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) :=
    (ψ f L p D τ hτ a).base ⁻¹' Set.range (Γ f p D τ hτ)
  have hS : IsClosed S := (isClosed_range_Γ f p D τ hτ).preimage (ψ f L p D τ hτ a).continuous
  have hsub : Set.range (θU f L p D τ hτ ι hτι a hc) ⊆ S := by
    rintro _ ⟨w, rfl⟩
    change (ψ f L p D τ hτ a) (θU f L p D τ hτ ι hτι a hc w) ∈ Set.range (Γ f p D τ hτ)
    rw [← Scheme.Hom.comp_apply, θU_ψ, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hopen : IsOpen (Set.range (θU f L p D τ hτ ι hτι a hc)) :=
    (θU f L p D τ hτ ι hτι a hc).isOpenEmbedding.isOpen_range
  have hne : (Set.range (θU f L p D τ hτ ι hτι a hc)).Nonempty := Set.range_nonempty _
  have hdense : Dense (Set.range (θU f L p D τ hτ ι hτι a hc)) := hopen.dense hne
  have hSuniv : S = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hdense.closure_eq]
    exact hS.closure_subset_iff.mpr hsub
  let zU : ↥((U f p D a : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) := ⟨z, hz⟩
  have hzS : zU ∈ S := by rw [hSuniv]; trivial
  obtain ⟨d, hd⟩ := hzS
  have h1 := congrArg (pullback.fst p f).base hd
  change ((Γ f p D τ hτ) ≫ pullback.fst p f) d =
    ((ψ f L p D τ hτ a) ≫ pullback.fst p f) zU at h1
  rw [Γ, ψ] at h1
  erw [pullback.lift_fst, pullback.lift_fst] at h1
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1
  have hz' : (U f p D a).ι zU = z := rfl
  rw [hz'] at h1
  rw [← h1]
  exact d.2

end Main

end BoundaryStability
end PartialAction
end GoodReductionJacobian
end AbelianVarieties.NOSProofs.PartialActionBoundary

end

open AbelianVarieties.NOSProofs.PartialActionBoundary.GoodReductionJacobian.PartialAction
open BoundaryStability

namespace GoodReductionJacobian.PartialAction

theorem hom_base_notMem_of_snd_notMem_of_isProper
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsSeparated p] [LocallyOfFiniteType p]
      [IsIntegral P]
    (D : P.Opens) (τ : (D : Scheme.{u}) ⟶ G) [IsProper τ] (hτ : τ ≫ f = D.ι ≫ p)
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u}))
    [IsOpenImmersion ι] (hτι : ι ≫ τ = V.ι)
    (a : PartialAction k f p)
    (hc : a.Compatible L V (ι ≫ D.ι) (j_comp f p D τ hτ ι hτι))
    (z : ↥(a.dom : Scheme.{u})) (hz : (pullback.snd f p).base (a.dom.ι.base z) ∉ (D : Set P)) :
    a.hom.base z ∉ (D : Set P) :=
  fun hmem => hz (snd_mem f L p D τ hτ ι hτι a hc z hmem)

end GoodReductionJacobian.PartialAction

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

universe u

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits hiding pair
open NeronModelInfra (SchemeHomOver)

namespace AbelianVarieties.NOSProofs.PartialActionExistence

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian

namespace PartialAction
open _root_.GoodReductionJacobian.PartialAction

namespace InducedAction

open
  AbelianVarieties.NOSProofs.PartialActionTransport.GoodReductionJacobian.PartialAction.OpTransport
  (geometricallyIrreducible)

open AbelianVarieties.NOSProofs.PartialActionLaws.GoodReductionJacobian.PartialAction.ActionLaws
  (comp_comp comp_congr pair_comp liftDom_eq)

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}

theorem comp_mul (L : RelativeGroupLaw k f) {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x y : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.mul t x y) =
      L.mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y) :=
  L.mul_natural t t' ψ hψ x y

section Chart

variable (L : RelativeGroupLaw k f) {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
  (hι : ι ≫ p = V.ι ≫ f)

/-- The structure morphism of the group-model product. -/
abbrev q (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k)) :
    pullback f p ⟶ Spec (CommRingCat.of k) :=
  pullback.fst f p ≫ f

/-- The product domain whose model coordinate lies in the chosen open chart. -/
def U₁ (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))
    (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι] : (pullback f p).Opens :=
  pullback.snd f p ⁻¹ᵁ (Scheme.Hom.opensRange ι)

/-- The structure morphism of the chart comparison domain. -/
abbrev tU (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))
    (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι] :
    ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of k) :=
  (U₁ f p ι).ι ≫ q f p

/-- The acting group point on the restricted domain. -/
def γU (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))
    (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι] : SchemeHomOver (tU f p ι) f :=
  ⟨(U₁ f p ι).ι ≫ pullback.fst f p, rfl⟩

@[scoped simp]
theorem γU_coe (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))
    (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι] :
    (γU f p ι).1 = (U₁ f p ι).ι ≫ pullback.fst f p := rfl

/-- Recover the open-model coordinate from the product domain. -/
def vLift (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))
    (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι] :
    ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}) ⟶ (V : Scheme.{u}) :=
  IsOpenImmersion.lift ι ((U₁ f p ι).ι ≫ pullback.snd f p) (by
    rintro _ ⟨z, rfl⟩
    exact z.2)

@[reassoc (attr := simp)]
theorem vLift_ι (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))
    (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι] :
    vLift f p ι ≫ ι = (U₁ f p ι).ι ≫ pullback.snd f p :=
  IsOpenImmersion.lift_fac _ _ _

include hι in
theorem vLift_comp : (vLift f p ι ≫ V.ι) ≫ f = tU f p ι := by
  rw [Category.assoc, ← hι, vLift_ι_assoc, ← pullback.condition]

/-- The recovered open-model point regarded as a group point. -/
def vU : SchemeHomOver (tU f p ι) f := ⟨vLift f p ι ≫ V.ι, vLift_comp ι hι⟩

@[scoped simp]
theorem vU_coe : (vU ι hι).1 = vLift f p ι ≫ V.ι := rfl

/-- Multiply the acting group point and the recovered model point. -/
def mU : SchemeHomOver (tU f p ι) f := L.mul (tU f p ι) (γU f p ι) (vU ι hι)

/-- The open chart where the product stays in the chosen model. -/
def W : ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}).Opens := (mU L ι hι).1 ⁻¹ᵁ V

/-- The initial action domain obtained from the multiplication chart. -/
def dom₀ : (pullback f p).Opens := (U₁ f p ι).ι ''ᵁ (W L ι hι)

/-- Identify the multiplication chart with its open image in the action product. -/
def isoW : ((W L ι hι : ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}).Opens) : Scheme.{u}) ≅
    ((dom₀ L ι hι : (pullback f p).Opens) : Scheme.{u}) :=
  (U₁ f p ι).ι.isoImage (W L ι hι)

@[reassoc]
theorem isoW_hom_ι : (isoW L ι hι).hom ≫ (dom₀ L ι hι).ι = (W L ι hι).ι ≫ (U₁ f p ι).ι :=
  Scheme.Hom.isoImage_hom_ι _ _

@[reassoc]
theorem isoW_inv_ι : (isoW L ι hι).inv ≫ (W L ι hι).ι ≫ (U₁ f p ι).ι = (dom₀ L ι hι).ι :=
  Scheme.Hom.isoImage_inv_ι _ _

/-- Restrict multiplication to the chart where its value lies in the open model. -/
def mW : ((W L ι hι : ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}).Opens) : Scheme.{u}) ⟶
    (V : Scheme.{u}) :=
  (mU L ι hι).1 ∣_ V

@[reassoc]
theorem mW_ι : mW L ι hι ≫ V.ι = (W L ι hι).ι ≫ (mU L ι hι).1 := morphismRestrict_ι _ _

/-- The action morphism on the initial open chart. -/
def hom₀ : ((dom₀ L ι hι : (pullback f p).Opens) : Scheme.{u}) ⟶ P :=
  (isoW L ι hι).inv ≫ mW L ι hι ≫ ι

include hι in
theorem hom₀_comp : hom₀ L ι hι ≫ p = (dom₀ L ι hι).ι ≫ pullback.snd f p ≫ p := by
  simp only [hom₀, Category.assoc]
  rw [hι, mW_ι_assoc, (mU L ι hι).2, isoW_inv_ι_assoc]
  dsimp only [q]
  rw [pullback.condition]

section TPoints

variable {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
  (v w : SchemeHomOver t (V.ι ≫ f))

/-- Lift a compatible pair into the initial product domain. -/
def liftU : T ⟶ ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}) :=
  IsOpenImmersion.lift (U₁ f p ι).ι (pair γ (modelPoint ι hι v)) (by
    rintro _ ⟨τ, rfl⟩
    rw [Scheme.Opens.range_ι]
    change pullback.snd f p (pair γ (modelPoint ι hι v) τ) ∈ Scheme.Hom.opensRange ι
    rw [← Scheme.Hom.comp_apply, pair, pullback.lift_snd, modelPoint_coe, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩)

@[reassoc (attr := simp)]
theorem liftU_ι : liftU ι hι γ v ≫ (U₁ f p ι).ι = pair γ (modelPoint ι hι v) :=
  IsOpenImmersion.lift_fac _ _ _

theorem liftU_tU : liftU ι hι γ v ≫ tU f p ι = t := by
  rw [tU, q, liftU_ι_assoc, pair, pullback.lift_fst_assoc]
  exact γ.2

theorem comp_liftU_γU : schemeHomOverComp (liftU ι hι γ v) (liftU_tU ι hι γ v) (γU f p ι) = γ :=
  Subtype.ext (by
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, γU_coe, liftU_ι_assoc, pair,
      pullback.lift_fst])

theorem liftU_vLift : liftU ι hι γ v ≫ vLift f p ι = v.1 := by
  rw [← cancel_mono ι, Category.assoc, vLift_ι, liftU_ι_assoc, pair, pullback.lift_snd,
    modelPoint_coe]

theorem comp_liftU_vU : schemeHomOverComp (liftU ι hι γ v) (liftU_tU ι hι γ v) (vU ι hι) =
    NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) :=
  Subtype.ext (by
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, vU_coe,
      NeronModelInfra.schemeHomOverComp_coe,
      ← Category.assoc, liftU_vLift])

theorem comp_liftU_mU : schemeHomOverComp (liftU ι hι γ v) (liftU_tU ι hι γ v) (mU L ι hι) =
    L.mul t γ (NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)) := by
  rw [mU, comp_mul, comp_liftU_γU, comp_liftU_vU]

variable (hvw : NeronModelInfra.schemeHomOverComp w (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
  L.mul t γ (NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)))

include hvw in
theorem liftU_mU : liftU ι hι γ v ≫ (mU L ι hι).1 = w.1 ≫ V.ι := by
  have h := congrArg Subtype.val ((comp_liftU_mU L ι hι γ v).trans hvw.symm)
  simpa only [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe]
    using h

include hvw in
theorem range_liftU_subset :
    Set.range (liftU ι hι γ v) ⊆ ((W L ι hι : ((U₁ f p ι : (pullback f p).Opens) :
      Scheme.{u}).Opens) : Set _) := by
  rintro _ ⟨τ, rfl⟩
  change (mU L ι hι).1 (liftU ι hι γ v τ) ∈ V
  rw [← Scheme.Hom.comp_apply, liftU_mU L ι hι γ v w hvw, Scheme.Hom.comp_apply]
  exact (w.1 τ).2

/-- Lift a compatible pair into the multiplication chart. -/
def liftW : T ⟶ ((W L ι hι : ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}).Opens) :
    Scheme.{u}) :=
  IsOpenImmersion.lift (W L ι hι).ι (liftU ι hι γ v) (by
    rw [Scheme.Opens.range_ι]; exact range_liftU_subset L ι hι γ v w hvw)

@[reassoc (attr := simp)]
theorem liftW_ι : liftW L ι hι γ v w hvw ≫ (W L ι hι).ι = liftU ι hι γ v :=
  IsOpenImmersion.lift_fac _ _ _

theorem pair_eq_liftW :
    pair γ (modelPoint ι hι v) = (liftW L ι hι γ v w hvw ≫ (isoW L ι hι).hom) ≫ (dom₀ L ι hι).ι :=
      by
  rw [Category.assoc, isoW_hom_ι, liftW_ι_assoc, liftU_ι]

include hvw in
theorem range_pair_subset_dom₀ :
    Set.range (pair γ (modelPoint ι hι v)) ⊆ ((dom₀ L ι hι : (pullback f p).Opens) : Set _) := by
  rw [pair_eq_liftW L ι hι γ v w hvw]
  rintro _ ⟨τ, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact (_ : ↥(dom₀ L ι hι)).2

theorem liftW_mW : liftW L ι hι γ v w hvw ≫ mW L ι hι = w.1 := by
  rw [← cancel_mono V.ι, Category.assoc, mW_ι, liftW_ι_assoc, liftU_mU L ι hι γ v w hvw]

theorem liftW_hom₀ : (liftW L ι hι γ v w hvw ≫ (isoW L ι hι).hom) ≫ hom₀ L ι hι = w.1 ≫ ι := by
  rw [hom₀, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, liftW_mW]

end TPoints

/-- The identity point of the chosen open model. -/
def idV (V : G.Opens) : SchemeHomOver (V.ι ≫ f) (V.ι ≫ f) := ⟨𝟙 _, Category.id_comp _⟩

theorem idV_eq : NeronModelInfra.schemeHomOverComp (idV V) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)
    =
    L.mul (V.ι ≫ f) (L.one _)
      (NeronModelInfra.schemeHomOverComp (idV V) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)) := by
  rw [L.one_mul]

theorem nonempty_W [Nonempty (V : Scheme.{u})] :
    Nonempty ((W L ι hι : ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}).Opens) :
      Scheme.{u}) :=
  Nonempty.map (liftW L ι hι (L.one _) (idV V) (idV V) (idV_eq L)) inferInstance

theorem dense_dom₀ [Nonempty (V : Scheme.{u})] [IrreducibleSpace ↥(pullback f p)] :
    Dense ((dom₀ L ι hι : (pullback f p).Opens) : Set ↥(pullback f p)) := by
  refine (dom₀ L ι hι).2.dense ?_
  obtain ⟨x⟩ := nonempty_W L ι hι
  exact ⟨_, ((isoW L ι hι).hom x).2⟩

end Chart

section Extension

variable (L : RelativeGroupLaw k f) {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
  (hι : ι ≫ p = V.ι ≫ f) [Nonempty (V : Scheme.{u})] [IrreducibleSpace ↥(pullback f p)]

/-- The initial action as a partial map. -/
def chart : (pullback f p).PartialMap P := ⟨dom₀ L ι hι, dense_dom₀ L ι hι, hom₀ L ι hι⟩

@[scoped simp]
theorem chart_domain : (chart L ι hι).domain = dom₀ L ι hι := rfl
@[scoped simp]
theorem chart_hom : (chart L ι hι).hom = hom₀ L ι hι := rfl

/-- The rational map represented by the initial action chart. -/
def ρ : (pullback f p) ⤏ P := (chart L ι hι).toRationalMap

variable [IsReduced (pullback f p)] [P.IsSeparated]

theorem toPartialMap_domain : (ρ L ι hι).toPartialMap.domain = (ρ L ι hι).domain := rfl

include hι in
theorem toPartialMap_hom_comp :
    (ρ L ι hι).toPartialMap.hom ≫ p =
      (ρ L ι hι).toPartialMap.domain.ι ≫ pullback.snd f p ≫ p := by
  let : (pullback f p).Over (Spec (CommRingCat.of k)) := ⟨q f p⟩
  let : P.Over (Spec (CommRingCat.of k)) := ⟨p⟩
  have : (chart L ι hι).IsOver (Spec (CommRingCat.of k)) := by
    rw [Scheme.PartialMap.isOver_iff]
    change hom₀ L ι hι ≫ p = (dom₀ L ι hι).ι ≫ pullback.fst f p ≫ f
    rw [hom₀_comp, pullback.condition]
  have : (ρ L ι hι).IsOver (Spec (CommRingCat.of k)) := by
    unfold ρ; infer_instance
  have h : (ρ L ι hι).toPartialMap.IsOver (Spec (CommRingCat.of k)) := inferInstance
  rw [Scheme.PartialMap.isOver_iff] at h
  have h' : (ρ L ι hι).toPartialMap.hom ≫ p =
      (ρ L ι hι).toPartialMap.domain.ι ≫ pullback.fst f p ≫ f := h
  rw [h', pullback.condition]

/-- The maximal partial action determined by the multiplication rational map. -/
def action : PartialAction k f p where
  dom := (ρ L ι hι).toPartialMap.domain
  dense_dom := (ρ L ι hι).toPartialMap.dense_domain
  hom := (ρ L ι hι).toPartialMap.hom
  hom_comp := toPartialMap_hom_comp L ι hι

theorem action_dom : (action L ι hι).dom = (ρ L ι hι).domain := rfl

theorem dom₀_le : dom₀ L ι hι ≤ (action L ι hι).dom :=
  (chart L ι hι).le_domain_toRationalMap

theorem homOfLE_hom :
    (pullback f p).homOfLE (dom₀_le L ι hι) ≫ (action L ι hι).hom = hom₀ L ι hι := by
  exact (chart L ι hι).toPartialMap_toRationalMap_restrict

include hι in
theorem compatible : (action L ι hι).Compatible L V ι hι := by
  intro T t γ v w hvw
  have hd : (action L ι hι).Defined γ (modelPoint ι hι v) :=
    (range_pair_subset_dom₀ L ι hι γ v w hvw).trans (dom₀_le L ι hι)
  refine ⟨hd, Subtype.ext ?_⟩
  have hlift : (action L ι hι).liftDom γ (modelPoint ι hι v) hd =
      (liftW L ι hι γ v w hvw ≫ (isoW L ι hι).hom) ≫
        (pullback f p).homOfLE (dom₀_le L ι hι) :=
    liftDom_eq _ _ _ hd _ (by
      rw [Category.assoc, Scheme.homOfLE_ι, ← pair_eq_liftW])
  rw [act_coe, hlift, Category.assoc, homOfLE_hom, liftW_hom₀, modelPoint_coe]

theorem maximal : (action L ι hι).Maximal := by
  intro U' h' hle heq
  refine le_antisymm ?_ hle
  let π' : (pullback f p).PartialMap P :=
    ⟨U', (action L ι hι).dense_dom.mono (fun _ hx => hle hx), h'⟩
  have hres : π'.restrict (action L ι hι).dom (action L ι hι).dense_dom hle =
      (ρ L ι hι).toPartialMap := by
    have hh : (pullback f p).homOfLE hle ≫ π'.hom = (ρ L ι hι).toPartialMap.hom := heq
    unfold Scheme.PartialMap.restrict
    rw [hh]
    rfl
  have hρ : π'.toRationalMap = ρ L ι hι := by
    rw [← Scheme.PartialMap.restrict_toRationalMap π' (action L ι hι).dom (action L ι hι).dense_dom
      hle, hres, Scheme.RationalMap.toRationalMap_toPartialMap]
  calc U' = π'.domain := rfl
    _ ≤ π'.toRationalMap.domain := π'.le_domain_toRationalMap
    _ = (action L ι hι).dom := by rw [hρ]; rfl

end Extension

section Structure

variable (L : RelativeGroupLaw k f)

theorem isReduced_pullback [Smooth f] [IsReduced P] [IsLocallyNoetherian P] :
    IsReduced (pullback f p) :=
  AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.snd f p)

theorem valuativeCriterion_existence [IsProper p] : ValuativeCriterion.Existence p := by
  have h : UniversallyClosed p := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at h
  exact h.1

theorem valuationRing_of_ringKrullDim_le_one (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R] (h : ringKrullDim R ≤ 1) :
    ValuationRing R := by
  have : Ring.KrullDimLE 1 R := Order.KrullDimLE.mk (by rw [Nat.cast_one]; exact h)
  have key : IsIntegrallyClosed R ∧
      ∀ Q : Ideal R, Q ≠ ⊥ → Q.IsPrime → Q = IsLocalRing.maximalIdeal R :=
    ⟨inferInstance, fun Q hQ hQ' => IsLocalRing.eq_maximalIdeal (hQ'.isMaximal_of_ne_bot hQ)⟩
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 2 4).mpr key

theorem isIntegrallyClosed_stalk [Smooth f] [IsIntegral P] [IsIntegral (pullback f p)]
    (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y)) (z : ↥(pullback f p)) :
    IsIntegrallyClosed ((pullback f p).presheaf.stalk z) := by
  have hP : ∀ U : P.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(P, U) := fun U hU =>
    AlgebraicGeometry.IsIntegral.isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk hn U
      hU
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ z)
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : IsDomain Γ(pullback f p, U) := IsIntegral.component_integral U
  have : IsIntegrallyClosed Γ(pullback f p, U) :=
    AlgebraicGeometry.isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
      (pullback.snd f p) hP U hU
  let : Algebra Γ(pullback f p, U) ((pullback f p).presheaf.stalk z) :=
    (pullback f p).presheaf.algebra_section_stalk (⟨z, hzU⟩ : U)
  have : IsLocalization.AtPrime ((pullback f p).presheaf.stalk z)
      (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := hU.isLocalization_stalk ⟨z, hzU⟩
  exact isIntegrallyClosed_of_isLocalization ((pullback f p).presheaf.stalk z)
    (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)

theorem valuationRing_stalk [Smooth f] [IsIntegral P] [LocallyOfFiniteType p]
    [IsIntegral (pullback f p)]
    (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y)) (z : ↥(pullback f p))
    (hz : ringKrullDim ((pullback f p).presheaf.stalk z) ≤ 1) :
    ValuationRing ((pullback f p).presheaf.stalk z) := by
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsLocallyNoetherian (pullback f p) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f p)
  have : IsIntegrallyClosed ((pullback f p).presheaf.stalk z) :=
    isIntegrallyClosed_stalk hn z
  exact valuationRing_of_ringKrullDim_le_one _ hz

end Structure

section Assembly

theorem exists_partialAction (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y))
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f) :
    ∃ a : PartialAction k f p, a.Compatible L V ι hι ∧ a.Maximal ∧
      ∀ z : ↥(pullback f p), ringKrullDim ((pullback f p).presheaf.stalk z) ≤ 1 → z ∈ a.dom := by
  have : GeometricallyIrreducible f := geometricallyIrreducible L
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsReduced (pullback f p) := isReduced_pullback
  have : IrreducibleSpace ↥(pullback f p) := inferInstance
  have : IsIntegral (pullback f p) := isIntegral_of_irreducibleSpace_of_isReduced _
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  refine ⟨action L ι hι, compatible L ι hι, maximal L ι hι, fun z hz => ?_⟩
  rw [action_dom]
  exact Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk
    (pullback.snd f p ≫ p) p (valuativeCriterion_existence (p := p)) (chart L ι hι)
    (hom₀_comp L ι hι) z (valuationRing_stalk hn z hz)

end Assembly

end InducedAction

end PartialAction

end GoodReductionJacobian
end AbelianVarieties.NOSProofs.PartialActionExistence

end

open CategoryTheory AlgebraicGeometry NeronModelInfra
    _root_.GoodReductionJacobian
    _root_.AbelianVarieties.NOSProofs.PartialActionExistence.GoodReductionJacobian
open CategoryTheory.Limits hiding pair

open AbelianVarieties.NOSProofs.PartialActionExistence.GoodReductionJacobian.PartialAction
open InducedAction (exists_partialAction)

namespace GoodReductionJacobian.RelativeGroupLaw

theorem exists_partialAction_compatible_maximal_of_isProper
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y))
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f) :
    ∃ a : PartialAction k f p, a.Compatible L V ι hι ∧ a.Maximal ∧
      ∀ z : ↥(pullback f p), ringKrullDim ((pullback f p).presheaf.stalk z) ≤ 1 → z ∈ a.dom :=
  exists_partialAction k f L p hn V ι hι

end GoodReductionJacobian.RelativeGroupLaw

end
