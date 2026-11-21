/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Morphisms.ClosedBaseChangeLifts
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Tactic.Algebraize
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.RingNF
public import Nyll.SchemeTheory.Morphisms.AppLECongr

/-!
# bijective app Top of is Proper of flat of is Adic Complete
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace bijective_appTop_of_isProper_of_flat_of_isAdicComplete

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace SolH0T1

lemma mem_map_colon_of_flat {A C : Type*} [CommRing A] [CommRing C] (f : A →+* C)
    (hf : f.Flat) (I : Ideal A) (π : A) (c : C) (h : f π * c ∈ I.map f) :
    c ∈ (I.colon {π}).map f := by
  algebraize [f]
  set J : Ideal A := I.colon {π} with hJ
  let f₁ : J →ₗ[A] A := J.subtype
  let f₂ : A →ₗ[A] (A ⧸ I) := (Submodule.mkQ I).comp (LinearMap.mulLeft A π)
  have hex : Function.Exact f₁ f₂ := by
    intro a
    simp only [f₁, f₂, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Set.mem_range,
      Submodule.subtype_apply, Subtype.exists, exists_prop, exists_eq_right]
    rw [hJ, Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
  have hexC := Module.Flat.lTensor_exact C hex
  have h2 : (f₂.lTensor C) (c ⊗ₜ[A] (1 : A)) = 0 := by
    simp only [LinearMap.lTensor_tmul, f₂, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulLeft_apply, mul_one, Submodule.mkQ_apply]
    apply (TensorProduct.tensorQuotEquivQuotSMul C I).injective
    change (tensorQuotEquivQuotSMul C I) (c ⊗ₜ[A] Ideal.Quotient.mk I π) = _
    rw [map_zero, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk,
      Submodule.Quotient.mk_eq_zero]
    have hle : (I.map (algebraMap A C)).restrictScalars A ≤ I • (⊤ : Submodule A C) := by
      rw [Ideal.smul_top_eq_map]
    have h' : π • c ∈ (I.map (algebraMap A C)).restrictScalars A := by
      rw [Submodule.restrictScalars_mem, Algebra.smul_def]; exact h
    exact hle h'
  obtain ⟨z, hz⟩ := (hexC _).mp h2
  have hc : c = TensorProduct.rid A C (f₁.lTensor C z) := by
    rw [hz, TensorProduct.rid_tmul, one_smul]
  have key : ∀ w : C ⊗[A] J, TensorProduct.rid A C (f₁.lTensor C w) ∈ J.map (algebraMap A C) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul x j =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, f₁, Submodule.subtype_apply]
      rw [Algebra.smul_def, mul_comm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ j.2)
    | add x y hx hy => simpa [map_add] using add_mem hx hy
  rw [hc]
  exact key z

end SolH0T1

open _root_.AlgebraicGeometry.ClosedBaseChangeLifts

noncomputable section

namespace SolH0T2

variable {X : Scheme.{u}} {A : CommRingCat.{u}} (p : X ⟶ Spec A)

lemma quot_comp_factor {I J : Ideal A} (h : I ≤ J) :
    quot I ≫ CommRingCat.ofHom (Ideal.Quotient.factor h) = quot (A := A) J := by
  ext a; rfl

/-- The transition morphism between closed base changes induced by an inclusion of ideals. -/
def τ {I J : Ideal A} (h : I ≤ J) : XI p J ⟶ XI p I :=
  pullback.lift (ι p J) (pI p J ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
    (by rw [Category.assoc, ← Spec.map_comp, quot_comp_factor, pullback.condition])

@[scoped simp] lemma τ_ι {I J : Ideal A} (h : I ≤ J) : τ p h ≫ ι p I = ι p J := pullback.lift_fst _
  _ _

@[scoped simp] lemma τ_pI {I J : Ideal A} (h : I ≤ J) :
    τ p h ≫ pI p I = pI p J ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) :=
  pullback.lift_snd _ _ _

/-- The transition homomorphism on global sections induced by an inclusion of ideals. -/
def ρ {I J : Ideal A} (h : I ≤ J) : Γ(XI p I, ⊤) →+* Γ(XI p J, ⊤) := ((τ p h).appTop).hom

lemma ρ_φ {I J : Ideal A} (hIJ : I ≤ J) (a : A) :
    ρ p hIJ (φ p I (Ideal.Quotient.mk I a)) = φ p J (Ideal.Quotient.mk J a) := by
  apply eq_of_forall_liftsAt
  intro U
  exact ⟨alg p U a, LiftsAt.trans_of p (τ p hIJ) (τ_ι p hIJ) (LiftsAt.alg p I U a),
    LiftsAt.alg p J U a⟩

/-- A local lift together with a divisibility relation modulo the chosen ideal. -/
def LocData (I : Ideal A) (π : A) (t : Γ(XI p I, ⊤)) (U : X.affineOpens) (c d : Γ(X, U)) : Prop :=
  LiftsAt p I U t c ∧ c - alg p U π * d ∈ I.map (alg p U)

lemma LocData.restrict {I : Ideal A} {π : A} {t : Γ(XI p I, ⊤)} {U W : X.affineOpens}
    (i : (W : X.Opens) ≤ U)
    {c d : Γ(X, U)} (h : LocData p I π t U c d) :
    LocData p I π t W (X.presheaf.map (homOfLE i).op c) (X.presheaf.map (homOfLE i).op d) := by
  refine ⟨h.1.restrict p i, ?_⟩
  have := Ideal.mem_map_of_mem (X.presheaf.map (homOfLE i).op).hom h.2
  rw [Ideal.map_map] at this
  simp only [map_sub, map_mul] at this
  rw [alg_map] at this
  convert this using 2
  ext a
  simp [alg_map]

section Step

variable {p}
variable (𝔪 : Ideal A) [𝔪.IsMaximal] (I : Ideal A) (π : A)

/--
The flatness, ideal, and section-bijectivity hypotheses for one induction step through a small
ideal extension.
-/
structure StepHyp : Prop where
  /-- The structure homomorphism on each affine chart is flat. -/
  flat : ∀ U : X.affineOpens, (alg p U).Flat
  /-- The chosen element belongs to the maximal ideal. -/
  hπm : π ∈ 𝔪
  /-- The chosen element is not in the smaller ideal. -/
  hπI : π ∉ I
  /-- Multiplication by the chosen element sends the maximal ideal into the smaller ideal. -/
  hmul : ∀ a ∈ 𝔪, a * π ∈ I
  /-- The smaller ideal is contained in the maximal ideal. -/
  hIm : I ≤ 𝔪
  /-- The map on global sections is bijective over the maximal-ideal quotient. -/
  bijm : Function.Bijective (φ p 𝔪)
  /-- The map on global sections is bijective after adjoining the chosen element to the ideal. -/
  bijI' : Function.Bijective (φ p (I ⊔ Ideal.span {π}))

variable {𝔪 I π} (S : StepHyp (p := p) 𝔪 I π)
include S

omit [𝔪.IsMaximal] S in lemma StepHyp.le_sup : I ≤ I ⊔ Ideal.span {π} := le_sup_left

lemma StepHyp.colon_eq : I.colon {π} = 𝔪 := by
  have h1 : 𝔪 ≤ I.colon {π} := fun a ha => by
    rw [Submodule.mem_colon_singleton, smul_eq_mul]; exact S.hmul a ha
  have h2 : I.colon {π} ≠ ⊤ := by
    intro h
    have : (1 : A) ∈ I.colon {π} := h ▸ Submodule.mem_top
    rw [Submodule.mem_colon_singleton, one_smul] at this
    exact S.hπI this
  exact (Ideal.IsMaximal.eq_of_le inferInstance h2 h1).symm
omit [𝔪.IsMaximal] in lemma StepHyp.span_mul_le : Ideal.span {π} * 𝔪 ≤ I := by
  rw [Ideal.span_singleton_mul_le_iff]
  intro a ha
  rw [mul_comm]; exact S.hmul a ha
omit [𝔪.IsMaximal] in
lemma StepHyp.pi_mul_mem {U : X.affineOpens} {x : Γ(X, U)} (hx : x ∈ 𝔪.map (alg p U)) :
    alg p U π * x ∈ I.map (alg p U) := by
  have : alg p U π * x ∈ (Ideal.span {π} * 𝔪).map (alg p U) := by
    rw [Ideal.map_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (Ideal.subset_span rfl)) hx
  exact Ideal.map_mono S.span_mul_le this
omit [𝔪.IsMaximal] S in
lemma StepHyp.exists_locData {t : Γ(XI p I, ⊤)} (ht : ρ p (le_sup_left : I ≤ I ⊔ Ideal.span {π}) t
  = 0) (U : X.affineOpens) :
    ∃ c d, LocData p I π t U c d := by
  obtain ⟨c, hc⟩ := LiftsAt.exists p I U.2 t
  have h1 : LiftsAt p (I ⊔ Ideal.span {π}) U 0 c := by
    let hI : I ≤ I ⊔ Ideal.span {π} := le_sup_left
    have : LiftsAt p (I ⊔ Ideal.span {π}) U (ρ p hI t) c :=
      LiftsAt.trans_of p (τ p hI) (τ_ι p hI) hc
    rwa [ht] at this
  rw [LiftsAt.mem_iff_of_zero p U.2, Ideal.map_sup, Ideal.map_span, Set.image_singleton,
    Submodule.mem_sup] at h1
  obtain ⟨i, hi, s, hs, rfl⟩ := h1
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hs
  refine ⟨i + d * alg p U π, d, hc, ?_⟩
  rw [mul_comm]
  simpa using hi

lemma StepHyp.locData_unique {t : Γ(XI p I, ⊤)} {U : X.affineOpens} {c d c' d' : Γ(X, U)}
    (h : LocData p I π t U c d) (h' : LocData p I π t U c' d') :
    d - d' ∈ 𝔪.map (alg p U) := by
  have h1 : c - c' ∈ I.map (alg p U) := (h.1.sub_mem_iff p U.2).mp h'.1
  have h2 : alg p U π * (d - d') ∈ I.map (alg p U) := by
    have : alg p U π * (d - d') = (c - c') - (c - alg p U π * d) + (c' - alg p U π * d') := by ring
    rw [this]
    exact add_mem (sub_mem h1 h.2) h'.2
  have := SolH0T1.mem_map_colon_of_flat (alg p U) (S.flat U) I π (d - d') h2
  rwa [S.colon_eq] at this

/-- The local section over the maximal-ideal fibre obtained from the chosen divisibility witness. -/
def StepHyp.eLoc {t : Γ(XI p I, ⊤)} (ht : ρ p (le_sup_left : I ≤ I ⊔ Ideal.span {π}) t = 0) (U :
  X.affineOpens) :
    Γ(XI p 𝔪, (ι p 𝔪) ⁻¹ᵁ U) :=
  (ι p 𝔪).app U (StepHyp.exists_locData (p := p) (I := I) (π := π) ht U).choose_spec.choose

lemma StepHyp.eLoc_eq {t : Γ(XI p I, ⊤)} (ht : ρ p (le_sup_left : I ≤ I ⊔ Ideal.span {π}) t = 0) (U
  : X.affineOpens)
    {c d : Γ(X, U)} (h : LocData p I π t U c d) :
    StepHyp.eLoc (p := p) (𝔪 := 𝔪) (I := I) (π := π) ht U = (ι p 𝔪).app U d := by
  unfold eLoc
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, (ker_ι_app p 𝔪 U.2).1]
  exact S.locData_unique (StepHyp.exists_locData (p := p) (I := I) (π := π) ht
    U).choose_spec.choose_spec h

lemma StepHyp.eLoc_restrict {t : Γ(XI p I, ⊤)} (ht : ρ p (le_sup_left : I ≤ I ⊔ Ideal.span {π}) t =
  0) {U W : X.affineOpens}
    (i : (W : X.Opens) ≤ U) :
    (XI p 𝔪).presheaf.map (homOfLE ((ι p 𝔪).preimage_mono i)).op
      (StepHyp.eLoc (p := p) (𝔪 := 𝔪) (I := I) (π := π) ht U) =
        StepHyp.eLoc (p := p) (𝔪 := 𝔪) (I := I) (π := π) ht W := by
  obtain ⟨c, d, h⟩ := StepHyp.exists_locData (p := p) (I := I) (π := π) ht U
  rw [S.eLoc_eq ht U h, S.eLoc_eq ht W (LocData.restrict p i h)]
  have nat := (ι p 𝔪).naturality (homOfLE i).op
  have h2 : (ι p 𝔪).app W (X.presheaf.map (homOfLE i).op d) =
      (XI p 𝔪).presheaf.map ((Opens.map (ι p 𝔪).base).map (homOfLE i)).op ((ι p 𝔪).app U d) := by
    rw [← CommRingCat.comp_apply, nat, CommRingCat.comp_apply]
    rfl
  change _ = (ι p 𝔪).app W (X.presheaf.map (homOfLE i).op d)
  rw [h2]
  exact presheaf_map_congr _ _ _

lemma StepHyp.exists_glue {t : Γ(XI p I, ⊤)} (ht : ρ p (le_sup_left : I ≤ I ⊔ Ideal.span {π}) t =
  0) :
    ∃ g : Γ(XI p 𝔪, ⊤), ∀ U : X.affineOpens,
      (XI p 𝔪).presheaf.map (homOfLE le_top).op g =
        StepHyp.eLoc (p := p) (𝔪 := 𝔪) (I := I) (π := π) ht U := by
  have hcov : (⊤ : (XI p 𝔪).Opens) ≤ ⨆ U : X.affineOpens, (ι p 𝔪) ⁻¹ᵁ (U : X.Opens) := by
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
    exact le_top
  have hcompat : TopCat.Presheaf.IsCompatible (XI p 𝔪).presheaf
      (fun U : X.affineOpens => (ι p 𝔪) ⁻¹ᵁ (U : X.Opens))
      (fun U => StepHyp.eLoc (p := p) (𝔪 := 𝔪) (I := I) (π := π) ht U) := by
    intro U V
    let ιS := fun W : {W : X.affineOpens // (W : X.Opens) ≤ (U : X.Opens) ⊓ V} =>
      (ι p 𝔪) ⁻¹ᵁ (W.1 : X.Opens)
    have hcov' : (ι p 𝔪) ⁻¹ᵁ (U : X.Opens) ⊓ (ι p 𝔪) ⁻¹ᵁ (V : X.Opens) ≤ ⨆ W, ιS W := by
      intro y hy
      have hy' : (ι p 𝔪) y ∈ (U : X.Opens) ⊓ (V : X.Opens) := hy
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hy' ((U : X.Opens) ⊓ (V : X.Opens)).isOpen
      exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
    apply TopCat.Sheaf.eq_of_locally_eq' (XI p 𝔪).sheaf ιS _
      (fun W => homOfLE ((ι p 𝔪).preimage_mono W.2)) hcov'
    intro W
    change (XI p 𝔪).presheaf.map _ ((XI p 𝔪).presheaf.map _
      (StepHyp.eLoc (p := p) (𝔪 := 𝔪) (I := I) (π := π) ht U)) =
      (XI p 𝔪).presheaf.map _ ((XI p 𝔪).presheaf.map _
        (StepHyp.eLoc (p := p) (𝔪 := 𝔪) (I := I) (π := π) ht V))
    conv_lhs => erw [← CommRingCat.comp_apply, ← Functor.map_comp]
    conv_rhs => erw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rw [presheaf_map_congr _ (homOfLE ((ι p 𝔪).preimage_mono (W.2.trans inf_le_left))).op,
      S.eLoc_restrict ht (W.2.trans inf_le_left),
      presheaf_map_congr _ (homOfLE ((ι p 𝔪).preimage_mono (W.2.trans inf_le_right))).op,
      S.eLoc_restrict ht (W.2.trans inf_le_right)]
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' (XI p 𝔪).sheaf
    (fun U : X.affineOpens => (ι p 𝔪) ⁻¹ᵁ (U : X.Opens)) ⊤ (fun U => homOfLE le_top) hcov
    (fun U => StepHyp.eLoc (p := p) (𝔪 := 𝔪) (I := I) (π := π) ht U) hcompat
  exact ⟨g, hg⟩

lemma StepHyp.ker_ρ {t : Γ(XI p I, ⊤)} (ht : ρ p (le_sup_left : I ≤ I ⊔ Ideal.span {π}) t = 0) :
    ∃ u : A, t = φ p I (Ideal.Quotient.mk I (u * π)) := by
  obtain ⟨g, hg⟩ := S.exists_glue ht
  obtain ⟨u', hu'⟩ := S.bijm.2 g
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u'
  refine ⟨u, ?_⟩
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_liftsAt
  intro U c' hc'
  obtain ⟨c, d, h⟩ := StepHyp.exists_locData (p := p) (I := I) (π := π) ht U
  have hd : d - alg p U u ∈ 𝔪.map (alg p U) := by
    rw [← (ker_ι_app p 𝔪 U.2).1, RingHom.mem_ker, map_sub, sub_eq_zero, ← S.eLoc_eq ht U h, ← hg U,
      ← hu']
    exact (LiftsAt.alg p 𝔪 U u).symm
  have hrep : LiftsAt p I U (t - φ p I (Ideal.Quotient.mk I (u * π))) (c - alg p U (u * π)) :=
    h.1.sub p (LiftsAt.alg p I U (u * π))
  have hmem : c - alg p U (u * π) ∈ I.map (alg p U) := by
    have : c - alg p U (u * π) = (c - alg p U π * d) + alg p U π * (d - alg p U u) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem h.2 (S.pi_mul_mem hd)
  have := (hrep.sub_mem_iff p U.2).mp hc'
  have h3 : c' = (c - alg p U (u * π)) - ((c - alg p U (u * π)) - c') := by ring
  rw [h3]
  exact sub_mem hmem this

lemma StepHyp.injective : Function.Injective (φ p I) := by
  rw [injective_iff_map_eq_zero]
  intro a' ha'
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  have h1 : φ p (I ⊔ Ideal.span {π}) (Ideal.Quotient.mk _ a) = 0 := by
    rw [← ρ_φ p (le_sup_left : I ≤ I ⊔ Ideal.span {π}), ha', map_zero]
  have h2 : a ∈ I ⊔ Ideal.span {π} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact S.bijI'.1 (by rw [h1, map_zero])
  rw [Submodule.mem_sup] at h2
  obtain ⟨i, hi, s, hs, rfl⟩ := h2
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hs
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine add_mem hi ?_
  have h3 : φ p I (Ideal.Quotient.mk I (u * π)) = 0 := by
    have : Ideal.Quotient.mk I (i + u * π) = Ideal.Quotient.mk I (u * π) := by
      rw [Ideal.Quotient.eq]; simpa using hi
    rw [← this]; exact ha'
  suffices hu : u ∈ 𝔪 from S.hmul u hu
  have hall : ∀ U : X.affineOpens, alg p U u ∈ 𝔪.map (alg p U) := by
    intro U
    have hz : LiftsAt p I U 0 (alg p U (u * π)) := by
      have := LiftsAt.alg p I U (u * π); rwa [h3] at this
    rw [LiftsAt.mem_iff_of_zero p U.2, map_mul, mul_comm] at hz
    have := SolH0T1.mem_map_colon_of_flat (alg p U) (S.flat U) I π _ hz
    rwa [S.colon_eq] at this
  have hzero : φ p 𝔪 (Ideal.Quotient.mk 𝔪 u) = 0 := by
    apply eq_zero_of_forall_liftsAt
    intro U c hc
    have := ((LiftsAt.alg p 𝔪 U u).sub_mem_iff p U.2).mp hc
    have h4 : c = alg p U u - (alg p U u - c) := by ring
    rw [h4]; exact sub_mem (hall U) this
  have : (Ideal.Quotient.mk 𝔪 u) = 0 := S.bijm.1 (by rw [hzero, map_zero])
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

lemma StepHyp.surjective : Function.Surjective (φ p I) := by
  intro r
  obtain ⟨b', hb'⟩ := S.bijI'.2 (ρ p (le_sup_left : I ≤ I ⊔ Ideal.span {π}) r)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  have h1 : ρ p (le_sup_left : I ≤ I ⊔ Ideal.span {π}) (r - φ p I (Ideal.Quotient.mk I b)) = 0 := by
    rw [map_sub, ρ_φ p (le_sup_left : I ≤ I ⊔ Ideal.span {π}), hb', sub_self]
  obtain ⟨u, hu⟩ := S.ker_ρ h1
  refine ⟨Ideal.Quotient.mk I (b + u * π), ?_⟩
  rw [map_add, map_add, ← hu]; ring

lemma StepHyp.bijective : Function.Bijective (φ p I) := ⟨S.injective, S.surjective⟩

end Step

end SolH0T2

attribute [local simp] SolH0T2.τ_ι
attribute [local simp] SolH0T2.τ_pI


end

attribute [local simp] SolH0T2.τ_ι
attribute [local simp] SolH0T2.τ_pI


noncomputable section

namespace SolH0T2

variable {X : Scheme.{u}} {A : CommRingCat.{u}} (p : X ⟶ Spec A)

local notation "𝔪" => IsLocalRing.maximalIdeal (CommRingCat.carrier A)

lemma alg_flat [Flat p] (U : X.affineOpens) : (alg p U).Flat := by
  unfold alg
  refine RingHom.Flat.comp ?_ (p.flat_appLE (isAffineOpen_top _) U.2 le_top)
  exact RingHom.Flat.of_bijective (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv.bijective

theorem levels_bijective [IsNoetherianRing A] [IsLocalRing A] [Flat p]
    (hm : Function.Bijective (φ p 𝔪)) :
    ∀ I : Ideal A, I ≤ 𝔪 → (∃ k, 𝔪 ^ k ≤ I) → Function.Bijective (φ p I) := by
  intro I
  induction I using IsNoetherian.induction with
  | hgt I IH =>
    intro hIm hk
    classical
    by_cases hI : I = 𝔪
    · subst hI; exact hm
    let j := Nat.find hk
    have hj : 𝔪 ^ j ≤ I := Nat.find_spec hk
    have hj0 : j ≠ 0 := by
      intro h0
      rw [h0, pow_zero, Ideal.one_eq_top, top_le_iff] at hj
      exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (hj ▸ hIm))
    have hj1 : j ≠ 1 := by
      intro h1
      rw [h1, pow_one] at hj
      exact hI (le_antisymm hIm hj)
    have hj2 : 2 ≤ j := by omega
    have hlt : ¬ 𝔪 ^ (j - 1) ≤ I := Nat.find_min hk (by omega)
    obtain ⟨π, hπ, hπI⟩ := IsConcreteLE.not_le_iff_exists.mp hlt
    have hπm : π ∈ 𝔪 := Ideal.pow_le_self (by omega) hπ
    have hmul : ∀ a ∈ 𝔪, a * π ∈ I := by
      intro a ha
      apply hj
      have : 𝔪 ^ j = 𝔪 * 𝔪 ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [this]
      exact Ideal.mul_mem_mul ha hπ
    set I' := I ⊔ Ideal.span {π} with hI'
    have hlt' : I < I' := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro h
      apply hπI
      rw [h]
      exact Ideal.mem_sup_right (Ideal.subset_span rfl)
    have hI'm : I' ≤ 𝔪 := sup_le hIm ((Ideal.span_singleton_le_iff_mem _).mpr hπm)
    have bijI' : Function.Bijective (φ p I') := IH I' hlt' hI'm ⟨j, hj.trans le_sup_left⟩
    have S : StepHyp (p := p) 𝔪 I π :=
      { flat := alg_flat p
        hπm := hπm
        hπI := hπI
        hmul := hmul
        hIm := hIm
        bijm := hm
        bijI' := bijI' }
    exact S.bijective

lemma map_top_apply (I : Ideal A) (t : Γ(XI p I, ⊤)) :
    (XI p I).presheaf.map (homOfLE (le_top (a := (ι p I) ⁻¹ᵁ ⊤))).op t = t := by
  have : (homOfLE (le_top (a := (ι p I) ⁻¹ᵁ (⊤ : X.Opens)))).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [this]; erw [CategoryTheory.Functor.map_id]; rfl

lemma ι_appTop_alg (I : Ideal A) (a : A) :
    (ι p I).appTop (alg p ⊤ a) = φ p I (Ideal.Quotient.mk I a) := by
  have := LiftsAt.alg p I ⊤ a
  unfold LiftsAt at this
  rw [map_top_apply] at this
  exact this

lemma res_mem_of_ι_appTop_eq_zero (I : Ideal A) (t : Γ(X, ⊤)) (ht : (ι p I).appTop t = 0)
    (U : X.affineOpens) : X.presheaf.map (homOfLE le_top).op t ∈ I.map (alg p U) := by
  rw [← (ker_ι_app p I U.2).1, RingHom.mem_ker]
  have nat := (ι p I).naturality (homOfLE (le_top (a := (U : X.Opens)))).op
  have h2 := congrArg (fun φ => φ.hom t) nat
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  change ((ι p I).app U) ((X.presheaf.map (homOfLE le_top).op) t) = 0
  erw [h2]
  change (XI p I).presheaf.map _ ((ι p I).appTop t) = 0
  rw [ht, map_zero]

theorem eq_zero_of_forall_ι_appTop_eq_zero [IsNoetherianRing A] [IsLocalRing A] [IsProper p]
    (t : Γ(X, ⊤)) (ht : ∀ k : ℕ, (ι p (𝔪 ^ (k + 1))).appTop t = 0) : t = 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hA : ∀ x : X, p x = IsLocalRing.closedPoint A →
      X.presheaf.germ ⊤ x trivial t = 0 := by
    intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    let θ : A →+* X.presheaf.stalk x := (X.presheaf.germ U x hxU).hom.comp (alg p U)
    have hθ : Ideal.map θ 𝔪 ≤ IsLocalRing.maximalIdeal _ := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      change ¬ IsUnit (X.presheaf.germ U x hxU (alg p U a))
      rw [← X.mem_basicOpen]
      unfold alg
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [Scheme.basicOpen_appLE p U ⊤ (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
        ((Scheme.ΓSpecIso A).inv a), basicOpen_eq_of_affine]
      rintro ⟨-, h2⟩
      change p x ∈ PrimeSpectrum.basicOpen a at h2
      rw [hx] at h2
      have h3 : a ∉ (IsLocalRing.closedPoint ↑A).asIdeal := h2
      exact h3 ha
    have hmem : ∀ k, X.presheaf.germ ⊤ x trivial t ∈ (IsLocalRing.maximalIdeal _) ^ (k + 1) := by
      intro k
      have h1 := res_mem_of_ι_appTop_eq_zero p _ t (ht k) ⟨U, hU⟩
      have h2 := Ideal.mem_map_of_mem (X.presheaf.germ U x hxU).hom h1
      rw [Ideal.map_map, Ideal.map_pow] at h2
      have h3 : (X.presheaf.germ U x hxU) (X.presheaf.map (homOfLE le_top).op t) =
          X.presheaf.germ ⊤ x trivial t := by
        rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
      rw [← h3]
      exact Ideal.pow_right_mono hθ _ h2
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal (X.presheaf.stalk
      x))
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    have : X.presheaf.germ ⊤ x trivial t ∈ ⨅ i : ℕ, IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^
      i := by
      rw [Ideal.mem_iInf]
      intro i
      cases i with
      | zero => simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
      | succ k => exact hmem k
    rw [hbot] at this
    exact this
  let S : Set X := {x | X.presheaf.germ ⊤ x trivial t = 0}
  have hSopen : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    have hx' : X.presheaf.germ ⊤ x trivial t = X.presheaf.germ ⊤ x trivial 0 := by
      rw [map_zero]; exact hx
    obtain ⟨W, hxW, iU, iV, hW⟩ := X.presheaf.germ_eq (U := ⊤) (V := ⊤) x trivial trivial t 0 hx'
    refine ⟨W, ?_, W.isOpen, hxW⟩
    intro y hy
    change X.presheaf.germ ⊤ y trivial t = 0
    rw [← X.presheaf.germ_res iU y hy, CommRingCat.comp_apply, hW, map_zero, map_zero]
  have hS : S = Set.univ := by
    by_contra hne
    have hcl : IsClosed (p '' Sᶜ) := p.isClosedMap _ hSopen.isClosed_compl
    let O : Opens (Spec A) := ⟨(p '' Sᶜ)ᶜ, hcl.isOpen_compl⟩
    have hO : IsLocalRing.closedPoint A ∈ O := by
      rintro ⟨x, hx, hpx⟩
      exact hx (hA x hpx)
    have hOtop : O = ⊤ := (IsLocalRing.closed_point_mem_iff).mp hO
    have hempty : p '' Sᶜ = ∅ := by
      have := congrArg (fun V : Opens (Spec A) => (V : Set (Spec A))) hOtop
      simp only [O, Opens.coe_mk, Opens.coe_top, compl_eq_comm, Set.compl_univ] at this
      exact this.symm
    rw [Set.image_eq_empty, Set.compl_empty_iff] at hempty
    exact hne hempty
  apply TopCat.Presheaf.section_ext X.sheaf ⊤ t 0
  intro x hx
  rw [map_zero]
  have : x ∈ S := hS ▸ Set.mem_univ x
  exact this
omit p in
lemma smodEq_pow_iff [IsLocalRing A] {x y : A} {n : ℕ} :
    x ≡ y [SMOD (𝔪 ^ n • ⊤ : Submodule A A)] ↔ x - y ∈ 𝔪 ^ n := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]

theorem bijective_alg_top [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete 𝔪 A]
    [IsProper p] [Flat p] (hm : Function.Bijective (φ p 𝔪)) :
    Function.Bijective (alg p ⊤) := by
  have hlev : ∀ k : ℕ, Function.Bijective (φ p (𝔪 ^ (k + 1))) := fun k =>
    levels_bijective p hm _ (Ideal.pow_le_self (Nat.succ_ne_zero k)) ⟨k + 1, le_rfl⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    have hk : ∀ k, a ∈ 𝔪 ^ (k + 1) := by
      intro k
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      apply (hlev k).1
      rw [map_zero, ← ι_appTop_alg, ha, map_zero]
    have : a ∈ ⨅ i : ℕ, 𝔪 ^ i := by
      rw [Ideal.mem_iInf]; intro i
      cases i with
      | zero => simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
      | succ k => exact hk k
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top]
      at this
  · intro s
    have hex : ∀ k, ∃ a : A, φ p (𝔪 ^ (k + 1)) (Ideal.Quotient.mk _ a) = (ι p (𝔪 ^ (k + 1))).appTop
      s := by
      intro k
      obtain ⟨a', ha'⟩ := (hlev k).2 ((ι p (𝔪 ^ (k + 1))).appTop s)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
      exact ⟨a, ha'⟩
    choose a ha using hex
    have hpow : ∀ {k l : ℕ}, k ≤ l → 𝔪 ^ (l + 1) ≤ 𝔪 ^ (k + 1) := fun h =>
      Ideal.pow_le_pow_right (by omega)
    have hcompat : ∀ {k l : ℕ}, k ≤ l → a l - a k ∈ 𝔪 ^ (k + 1) := by
      intro k l hkl
      rw [← Ideal.Quotient.eq, ← (hlev k).1.eq_iff, ha k, ← ρ_φ p (hpow hkl), ha l]
      change ((ι p (𝔪 ^ (l + 1))).appTop ≫ (τ p (hpow hkl)).appTop) s = _
      rw [← Scheme.Hom.comp_appTop, τ_ι]
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := 𝔪) (M := A))
      (f := a) (fun {k l} hkl => by
        rw [smodEq_pow_iff]
        have := hcompat hkl
        rw [← neg_sub, neg_mem_iff] at this
        cases k with
        | zero => simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
        | succ k => exact Ideal.pow_le_pow_right (Nat.le_succ _) this)
    refine ⟨L, ?_⟩
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_ι_appTop_eq_zero p
    intro k
    rw [map_sub, ι_appTop_alg, sub_eq_zero, ← ha k]
    congr 1
    rw [Ideal.Quotient.eq]
    have h1 : a (k + 1) - L ∈ 𝔪 ^ (k + 1) := by
      have := hL (k + 1)
      rwa [smodEq_pow_iff] at this
    have h2 : a (k + 1) - a k ∈ 𝔪 ^ (k + 1) := hcompat (Nat.le_succ k)
    have : L - a k = (a (k + 1) - a k) - (a (k + 1) - L) := by ring
    rw [this]
    exact sub_mem h2 h1

lemma bijective_φ_iff (I : Ideal A) :
    Function.Bijective (φ p I) ↔ Function.Bijective ((pI p I).appTop) := by
  unfold φ
  simp only [RingHom.coe_comp]
  exact Function.Bijective.of_comp_iff _
    (Scheme.ΓSpecIso (.of (A ⧸ I))).symm.commRingCatIsoToRingEquiv.bijective

theorem bijective_appTop [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete 𝔪 A]
    [IsProper p] [Flat p] (h : Function.Bijective ((pI p 𝔪).appTop)) :
    Function.Bijective p.appTop := by
  have h1 := bijective_alg_top p ((bijective_φ_iff p 𝔪).mpr h)
  unfold alg at h1
  have hApp := p.appLE_top_eq_appTop
  rw [hApp] at h1
  simp only [RingHom.coe_comp] at h1
  exact (Function.Bijective.of_comp_iff _
    (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv.bijective).mp h1

end SolH0T2

attribute [local simp] SolH0T2.τ_ι
attribute [local simp] SolH0T2.τ_pI


end

attribute [local simp] SolH0T2.τ_ι
attribute [local simp] SolH0T2.τ_pI


theorem _root_.AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_isAdicComplete
    {X : Scheme.{u}} {A : CommRingCat.{u}} [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : X ⟶ Spec A) [IsProper p] [Flat p]
    (h : Function.Bijective (pullback.snd p (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))).appTop) :
    Function.Bijective p.appTop :=
  SolH0T2.bijective_appTop p h
end AlgebraicCurves.Geometry.Schemes.Proofs.bijective_appTop_of_isProper_of_flat_of_isAdicComplete
end ProofImplementation
