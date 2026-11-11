/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.SurjectiveOnStalks
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Nyll.SchemeTheory.RingTheory.IntegralClosure.Normalization
public import Nyll.SchemeTheory.Descent.FiniteQuotients

/-!
# Affine neighborhoods and generic finiteness

Finite sets admit common affine neighborhoods under finite flat descent.
Separated quasi-finite morphisms become finite on a nonempty open neighborhood
of each minimal prime, and hence on some open of an irreducible target.
-/

@[expose] public section

namespace AlgebraicGeometry

universe u
open CategoryTheory

/-- The target-local property of finite morphisms, supplied by their affine property. -/
theorem isFiniteLocalAtTarget :
    IsZariskiLocalAtTarget (@IsFinite : CategoryTheory.MorphismProperty Scheme.{u}) := by
  have hAffine : HasAffineProperty
      (@IsFinite : CategoryTheory.MorphismProperty Scheme.{u}) (affineAnd RingHom.Finite) :=
    (HasAffineProperty.affineAnd_iff
      (@IsFinite : CategoryTheory.MorphismProperty Scheme.{u})
      RingHom.finite_respectsIso RingHom.finite_localizationPreserves.away
      RingHom.finite_ofLocalizationSpan).mpr
        (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => isFinite_iff f)
  exact (HasAffineProperty.iff.mp hAffine).1

end AlgebraicGeometry

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_IsAffineOpen_isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AlgebraicGeometry.IsAffineOpen

universe u

open CategoryTheory AlgebraicGeometry

theorem isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes
    {X : Scheme.{u}} [IsReduced X] {V : X.Opens} (hV : IsAffineOpen V)
    (x : X) (hxV : x ∈ V) (hmax : ∀ y : X, y ⤳ x → y = x)
    (F : Type u) [Field F] (φ : Spec (CommRingCat.of F) ⟶ X) [IsPreimmersion φ]
    (hφx : φ.base (IsLocalRing.closedPoint F) = x)
    [Algebra Γ(X, V) F]
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) F)) ≫ hV.fromSpec = φ) :
    IsLocalization (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl F := by
  classical
  have hpt : hV.fromSpec.base
      ((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) F))).base
        (IsLocalRing.closedPoint F)) = x := by
    rw [← hφx, ← hφ]; rfl
  have h𝔭 : hV.primeIdealOf ⟨x, hxV⟩ =
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) F))).base (IsLocalRing.closedPoint F) := by
    apply hV.fromSpec.isOpenEmbedding.injective
    rw [hpt]
    exact hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hmem : ∀ s : Γ(X, V),
      s ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal ↔ algebraMap Γ(X, V) F s = 0 := by
    intro s
    rw [h𝔭]
    change algebraMap Γ(X, V) F s ∈ IsLocalRing.maximalIdeal F ↔ _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) F)) ≫ hV.fromSpec) := by
    rw [hφ]; infer_instance
  have hpre : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) F))) :=
    IsPreimmersion.of_comp _ hV.fromSpec
  have hsos : (algebraMap Γ(X, V) F).SurjectiveOnStalks :=
    ((IsPreimmersion.SpecMap_iff _).mp hpre).2
  set 𝔭 := hV.primeIdealOf ⟨x, hxV⟩ with h𝔭def
  have hkill : ∀ d ∈ 𝔭.asIdeal, ∃ c : 𝔭.asIdeal.primeCompl, (c : Γ(X, V)) * d = 0 := by
    intro d hd
    set L := Localization.AtPrime 𝔭.asIdeal with hL
    have huniq : ∀ Q : Ideal L, Q.IsPrime → Q = IsLocalRing.maximalIdeal L := by
      intro Q hQ
      let q : PrimeSpectrum Γ(X, V) := ⟨Q.comap (algebraMap Γ(X, V) L), Ideal.IsPrime.comap _⟩
      have hq𝔭 : q ≤ 𝔭 := by
        intro s hs
        by_contra hs'
        have hu : IsUnit (algebraMap Γ(X, V) L s) :=
          IsLocalization.map_units L (⟨s, hs'⟩ : 𝔭.asIdeal.primeCompl)
        exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hs hu)
      have hfx : hV.fromSpec.base 𝔭 = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
      have hspec : hV.fromSpec.base q ⤳ x := by
        rw [← hfx]
        exact ((PrimeSpectrum.le_iff_specializes q 𝔭).mp hq𝔭).map hV.fromSpec.base.hom.continuous
      have hqx : q = 𝔭 := by
        apply hV.fromSpec.isOpenEmbedding.injective
        rw [hmax _ hspec, hfx]
      apply le_antisymm (IsLocalRing.le_maximalIdeal hQ.ne_top)
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro s hs
      have hs' : s ∈ q.asIdeal := by rw [hqx]; exact hs
      exact hs'
    have hmax0 : IsLocalRing.maximalIdeal L = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have : m ∈ nilradical L := by
        rw [nilradical_eq_sInf, Submodule.mem_sInf]
        intro J hJ
        rw [huniq J hJ]; exact hm
      rw [mem_nilradical] at this
      exact this.eq_zero
    have : algebraMap Γ(X, V) L d = 0 := by
      rw [← Ideal.mem_bot, ← hmax0, ← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hd
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff 𝔭.asIdeal.primeCompl L d).mp this
    exact ⟨c, hc⟩
  constructor; constructor
  · rintro ⟨s, hs⟩
    rw [isUnit_iff_ne_zero]
    exact fun h => hs ((hmem s).mpr h)
  · intro z
    obtain ⟨a, r, c, hc, hr, e⟩ :=
      (RingHom.surjectiveOnStalks_iff_forall_maximal'.mp hsos) ⊥ Ideal.bot_isMaximal z
    have hc0 : c ≠ 0 := fun h => hc (h ▸ Submodule.zero_mem _)
    have hr𝔭 : r ∉ 𝔭.asIdeal := fun h => hr (by rw [(hmem r).mp h]; exact Submodule.zero_mem _)
    refine ⟨(a, ⟨r, hr𝔭⟩), ?_⟩
    change z * algebraMap Γ(X, V) F r = algebraMap Γ(X, V) F a
    have e' : c * (algebraMap Γ(X, V) F r * z) = c * algebraMap Γ(X, V) F a := by
      rwa [mul_assoc] at e
    have e'' := mul_left_cancel₀ hc0 e'
    rw [mul_comm]; exact e''
  · intro a b hab
    have : a - b ∈ 𝔭.asIdeal := by rw [hmem, map_sub, hab, sub_self]
    obtain ⟨c, hc⟩ := hkill _ this
    refine ⟨c, ?_⟩
    rw [← sub_eq_zero, ← mul_sub, hc]

end AlgebraicGeometry.IsAffineOpen
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isAffineOpen_subset_of_finite_of_isAffine.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.NOSProofs.AffineNeighborhoods.FiniteSets

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AffinePoints

open SchemeTheory.Descent.InvariantAffineNeighborhoods.InvariantNeighborhoods in
lemma not_mem_primeIdealOf_iff {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) {x : X} (hx : x ∈ V)
    (r : Γ(X, V)) : r ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal ↔ x ∈ X.basicOpen r := by
  exact (mem_basicOpen_iff_notMem hV r hx).symm

end AffinePoints

end SchemeTheory.NOSProofs.AffineNeighborhoods.FiniteSets

namespace AlgebraicGeometry

universe u
open CategoryTheory CategoryTheory.Limits
open SchemeTheory.NOSProofs.AffineNeighborhoods.FiniteSets.AffinePoints in
theorem exists_isAffineOpen_subset_of_finite_of_isAffine
    {X : Scheme.{u}} [IsAffine X] (V : X.Opens) (F : Set V.toScheme) (hF : F.Finite) :
    ∃ W : (V.toScheme).Opens, IsAffineOpen W ∧ F ⊆ (W : Set V.toScheme) := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · exact ⟨⊥, isAffineOpen_bot _, Set.empty_subset _⟩
  have hT : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  have key : ∀ (x : X) (r : Γ(X, ⊤)),
      r ∉ (hT.primeIdealOf ⟨x, trivial⟩).asIdeal ↔ x ∈ X.basicOpen r :=
    fun x r => not_mem_primeIdealOf_iff hT trivial r
  have hg : ∀ v : V.toScheme, ∃ r : Γ(X, ⊤), X.basicOpen r ≤ V ∧ v.1 ∈ X.basicOpen r :=
    fun v => hT.exists_basicOpen_le ⟨v.1, v.2⟩ trivial
  choose g hgV hgv using hg
  let I : Ideal Γ(X, ⊤) := Ideal.span (Set.range g)
  have hIV : ∀ r ∈ I, X.basicOpen r ≤ V := by
    intro r hr x hx
    by_contra hxV
    have : I ≤ (hT.primeIdealOf ⟨x, trivial⟩).asIdeal := by
      apply Ideal.span_le.mpr
      rintro _ ⟨v, rfl⟩
      by_contra h
      exact hxV (hgV v ((key x (g v)).mp h))
    exact (key x r).mpr hx (this hr)
  have havoid : ¬ ((I : Set Γ(X, ⊤)) ⊆ ⋃ v ∈ (hF.toFinset : Set V.toScheme),
      ((hT.primeIdealOf ⟨v.1, trivial⟩).asIdeal : Set Γ(X, ⊤))) := by
    rw [Ideal.subset_union_prime v₀ v₀ (fun v _ _ _ => (hT.primeIdealOf ⟨v.1, trivial⟩).isPrime)]
    rintro ⟨v, -, hle⟩
    exact (key v.1 (g v)).mpr (hgv v) (hle (Ideal.subset_span ⟨v, rfl⟩))
  rw [Set.not_subset] at havoid
  obtain ⟨r, hrI, hr⟩ := havoid
  refine ⟨V.ι ⁻¹ᵁ X.basicOpen r, ?_, ?_⟩
  · rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_eq_right.mpr (hIV r hrI)]
    exact hT.basicOpen r
  · intro v hv
    change v.1 ∈ X.basicOpen r
    exact (key v.1 r).mp (fun h =>
      hr (Set.mem_biUnion (Finset.mem_coe.mpr (hF.mem_toFinset.mpr hv)) h))

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.NOSProofs.AffineNeighborhoods.FiniteFlatDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace KernelRelation

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

theorem rel_iff {T : Scheme.{u}} (x y : T ⟶ X) :
    (∃ φ : T ⟶ pullback p p, φ ≫ pullback.fst p p = x ∧ φ ≫ pullback.snd p p = y) ↔
      x ≫ p = y ≫ p := by
  constructor
  · rintro ⟨φ, rfl, rfl⟩
    rw [Category.assoc, Category.assoc, pullback.condition]
  · intro h
    exact ⟨pullback.lift x y h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem hequiv (T : Scheme.{u}) :
    _root_.Equivalence fun x y : T ⟶ X =>
      ∃ φ : T ⟶ pullback p p, φ ≫ pullback.fst p p = x ∧ φ ≫ pullback.snd p p = y := by
  constructor
  · intro x
    exact (rel_iff p x x).2 rfl
  · intro x y h
    exact (rel_iff p y x).2 ((rel_iff p x y).1 h).symm
  · intro x y z h h'
    exact (rel_iff p x z).2 (((rel_iff p x y).1 h).trans ((rel_iff p y z).1 h'))

end KernelRelation

end SchemeTheory.NOSProofs.AffineNeighborhoods.FiniteFlatDescent

namespace AlgebraicGeometry

universe u
open CategoryTheory CategoryTheory.Limits
open SchemeTheory.NOSProofs.AffineNeighborhoods.FiniteFlatDescent.KernelRelation in
theorem exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsFinite p] [Flat p]
    [LocallyOfFinitePresentation p] [Surjective p]
    (S : Finset Y) (W : X.Opens) (hW : IsAffineOpen W) (hSW : ∀ x : X, p.base x ∈ S → x ∈ W) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ ∀ y ∈ S, y ∈ V := by
  classical
  have hfin : (p.base ⁻¹' (S : Set Y)).Finite := p.finite_preimage S.finite_toSet
  obtain ⟨W', hW'aff, hSW', -, hinv⟩ :=
    Scheme.exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation
      (pullback.fst p p) (pullback.snd p p) (hequiv p) hfin hW (fun x hx r hr => by
        apply hSW
        have hc : p.base ((pullback.snd p p).base r) = p.base ((pullback.fst p p).base r) := by
          change (pullback.snd p p ≫ p).base r = (pullback.fst p p ≫ p).base r
          rw [pullback.condition]
        rw [hc]
        have hr' : (pullback.fst p p).base r = x := hr
        rw [hr']
        exact hx)
  obtain ⟨V, hV, hpV⟩ :=
    Scheme.exists_isAffineOpen_preimage_eq_of_invariant
      (pullback.fst p p) (pullback.snd p p)
      (fun _ _ h₁ h₂ => pullback.hom_ext h₁ h₂) (hequiv p) p pullback.condition
      (IsPullback.of_hasPullback p p)
      W' hW'aff hinv
  refine ⟨V, hV, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := p.surjective y
  have hx : x ∈ (W' : Set X) := hSW' (show x ∈ p.base ⁻¹' (S : Set Y) from hy)
  have hx' : x ∈ p ⁻¹ᵁ V := by rw [hpV]; exact hx
  exact hx'

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_LocallyQuasiFinite_exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.NOSProofs.AffineNeighborhoods.GenericFiniteness

universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

theorem isFinite_ι_of_isClosed {X : Scheme.{u}} (W : X.Opens)
    (hW : IsClosed (W : Set X)) : IsFinite W.ι := by
  have : IsClosedImmersion W.ι :=
    IsClosedImmersion.of_isPreimmersion W.ι (by rw [Scheme.Opens.range_ι]; exact hW)
  infer_instance
theorem IsFinite.of_forall_isClosed_of_iSup_eq_top {X Y : Scheme.{u}}
    (f : X ⟶ Y) {n : ℕ} (U : Fin n → X.Opens)
    (hU : ⨆ i, U i = ⊤) (hcl : ∀ i, IsClosed ((U i : Set X))) (hfin : ∀ i, IsFinite ((U i).ι ≫ f)) :
    IsFinite f := by
  induction n generalizing X with
  | zero =>
    have : IsEmpty X := ⟨fun x => by
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hU, TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨i, -⟩ := hx
      exact Fin.elim0 i⟩
    infer_instance
  | succ n ih =>
    let V : X.Opens := U 0
    let W : X.Opens := ⟨(V : Set X)ᶜ, (hcl 0).isOpen_compl⟩
    have hWcl : IsClosed (W : Set X) := by
      change IsClosed (V : Set X)ᶜ
      exact (U 0).2.isClosed_compl
    have hVW : IsCompl V.ι.opensRange W.ι.opensRange := by
      rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
      refine IsCompl.of_eq ?_ ?_
      · apply TopologicalSpace.Opens.ext
        rw [TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_bot]
        exact Set.inter_compl_self _
      · apply TopologicalSpace.Opens.ext
        rw [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top]
        exact Set.union_compl_self _
    obtain ⟨hc⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl V.ι W.ι hVW
    have hV : IsFinite (V.ι ≫ f) := hfin 0
    have hW : IsFinite (W.ι ≫ f) := by
      have : IsFinite W.ι := isFinite_ι_of_isClosed W hWcl
      refine ih (W.ι ≫ f) (fun i => W.ι ⁻¹ᵁ U i.succ) ?_ ?_ ?_
      · refine top_le_iff.mp fun w _ => ?_
        have hw : W.ι.base w ∈ (⊤ : X.Opens) := trivial
        rw [← hU, TopologicalSpace.Opens.mem_iSup] at hw
        obtain ⟨i, hi⟩ := hw
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · exfalso
          have : W.ι.base w ∈ (W : Set X) := by rw [← Scheme.Opens.range_ι W]; exact ⟨w, rfl⟩
          exact this hi
        · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hi⟩
      · intro i
        exact (hcl i.succ).preimage W.ι.continuous
      · intro i
        rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
        have := hfin i.succ
        infer_instance
    let e := hc.coconePointUniqueUpToIso (coprodIsCoprod (V : Scheme.{u}) (W : Scheme.{u}))
    have hVι : V.ι ≫ e.hom = coprod.inl := by
      exact hc.comp_coconePointUniqueUpToIso_hom
        (coprodIsCoprod (V : Scheme.{u}) (W : Scheme.{u})) ⟨WalkingPair.left⟩
    have hWι : W.ι ≫ e.hom = coprod.inr := by
      exact hc.comp_coconePointUniqueUpToIso_hom
        (coprodIsCoprod (V : Scheme.{u}) (W : Scheme.{u})) ⟨WalkingPair.right⟩
    have hdesc : e.inv ≫ f = coprod.desc (V.ι ≫ f) (W.ι ≫ f) := by
      apply coprod.hom_ext
      · rw [coprod.inl_desc, ← hVι]; erw [Category.assoc, e.hom_inv_id_assoc]
      · rw [coprod.inr_desc, ← hWι]; erw [Category.assoc, e.hom_inv_id_assoc]
    have h1 : IsFinite (coprod.desc (V.ι ≫ f) (W.ι ≫ f)) := inferInstance
    have h2 : IsFinite (e.hom : X ⟶ (V : Scheme.{u}) ⨿ (W : Scheme.{u})) := inferInstance
    have h3 : IsFinite ((e.hom : X ⟶ (V : Scheme.{u}) ⨿ (W : Scheme.{u})) ≫
        coprod.desc (V.ι ≫ f) (W.ι ≫ f)) :=
      MorphismProperty.comp_mem @IsFinite _ _ h2 h1
    rw [← hdesc, e.hom_inv_id_assoc] at h3
    exact h3
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
namespace AffineCharts
open _root_.AlgebraicGeometry

theorem exists_isFinite_restrict_chart {R : Type u} [CommRing R] {A : CommRingCat.{u}}
    (φ : CommRingCat.of R ⟶ A) (hft : φ.hom.FiniteType) (hqf : φ.hom.QuasiFinite)
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ∃ r : R, r ∉ p ∧ ∀ s : R, IsFinite (Spec.map φ ∣_ PrimeSpectrum.basicOpen (r * s)) := by
  have hLocal : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.isFiniteLocalAtTarget
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    hLocal.toRespects
  let D : R → (Spec (CommRingCat.of R)).Opens := fun t => PrimeSpectrum.basicOpen t
  algebraize [φ.hom]
  obtain ⟨r, hr, hfin⟩ :=
    Algebra.QuasiFinite.exists_not_mem_finite_awayMap_of_mem_minimalPrimes (A := A) p hp
  refine ⟨r, hr, fun s => ?_⟩
  have h1 : IsFinite (Spec.map φ ∣_ PrimeSpectrum.basicOpen r) := by
    refine (MorphismProperty.arrow_mk_iso_iff @IsFinite (SpecMapRestrictBasicOpenIso φ r)).mpr ?_
    exact (IsFinite.SpecMap_iff _).mpr hfin
  have hle : PrimeSpectrum.basicOpen (r * s) ≤ PrimeSpectrum.basicOpen r := by
    rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_left
  have h2 := IsZariskiLocalAtTarget.restrict h1 ((D r).ι ⁻¹ᵁ D (r * s))
  have h3 := (MorphismProperty.arrow_mk_iso_iff @IsFinite
    (morphismRestrictRestrict (Spec.map φ) (D r) ((D r).ι ⁻¹ᵁ D (r * s)))).mp h2
  have heq : (D r).ι ''ᵁ ((D r).ι ⁻¹ᵁ D (r * s)) = D (r * s) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hle
  exact (MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictEq (Spec.map φ) heq)).mp h3

theorem main {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsSeparated f] [QuasiCompact f]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ∃ r : R, r ∉ p ∧ IsFinite (f ∣_ PrimeSpectrum.basicOpen r) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := X.affineCover.finiteSubcover
  have hA : ∀ i : 𝒰.I₀, IsAffine (𝒰.X i) := fun i => by
    change IsAffine (X.affineCover.X _); infer_instance
  let c : ∀ i : 𝒰.I₀, Spec (Γ(𝒰.X i, ⊤)) ⟶ X := fun i => (𝒰.X i).isoSpec.inv ≫ 𝒰.f i
  have hc : ∀ i, IsOpenImmersion (c i) := fun i => inferInstance
  have hchart : ∀ i : 𝒰.I₀, ∃ r : R, r ∉ p ∧
      ∀ s : R, IsFinite ((c i ≫ f) ∣_ PrimeSpectrum.basicOpen (r * s)) := by
    intro i
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (c i ≫ f)
    have hft : φ.hom.FiniteType := by
      have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
      exact HasRingHomProperty.Spec_iff.mp this
    have hqf : φ.hom.QuasiFinite := by
      have : LocallyQuasiFinite (Spec.map φ) := by rw [hφ]; infer_instance
      exact HasRingHomProperty.Spec_iff.mp this
    obtain ⟨r, hr, h⟩ := exists_isFinite_restrict_chart φ hft hqf p hp
    exact ⟨r, hr, fun s => by have := h s; rwa [hφ] at this⟩
  choose rr hrr hfinr using hchart
  have hprime : p.IsPrime := hp.1.1
  refine ⟨∏ i, rr i, hprime.prod_mem_iff.not.mpr (by
    simpa only [Finset.mem_univ, true_and, not_exists] using hrr), ?_⟩
  set r := ∏ i, rr i with hr
  set V : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen r
  let h : ∀ i : 𝒰.I₀, ((c i) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme ⟶ (f ⁻¹ᵁ V).toScheme :=
    fun i => (c i) ∣_ (f ⁻¹ᵁ V)
  have hfin : ∀ i, IsFinite (h i ≫ f ∣_ V) := by
    intro i
    rw [← morphismRestrict_comp]
    have : r = rr i * ∏ j ∈ Finset.univ.erase i, rr j :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    rw [show V = PrimeSpectrum.basicOpen (rr i * ∏ j ∈ Finset.univ.erase i, rr j) by rw [← this]]
    exact hfinr i _
  have hclosed : ∀ i, IsClosed (Set.range (h i)) := by
    intro i
    have : IsProper (h i) := IsProper.of_comp (h i) (f ∣_ V)
    exact (h i).isClosedMap.isClosed_range
  let U : 𝒰.I₀ → (f ⁻¹ᵁ V).toScheme.Opens := fun i => (h i).opensRange
  have hcov : ⨆ i, U i = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    set j := 𝒰.idx ((f ⁻¹ᵁ V).ι x) with hj
    obtain ⟨y, hy⟩ : ∃ y, 𝒰.f j y = (f ⁻¹ᵁ V).ι x := 𝒰.covers ((f ⁻¹ᵁ V).ι x)
    have hy' : c j ((𝒰.X j).isoSpec.hom y) = (f ⁻¹ᵁ V).ι x := by
      calc c j ((𝒰.X j).isoSpec.hom y) = ((𝒰.X j).isoSpec.hom ≫ c j) y :=
            (Scheme.Hom.comp_apply _ _ _).symm
        _ = (𝒰.f j) y := by simp only [c, Iso.hom_inv_id_assoc]
        _ = (f ⁻¹ᵁ V).ι x := hy
    have hyV : (𝒰.X j).isoSpec.hom y ∈ (c j) ⁻¹ᵁ (f ⁻¹ᵁ V) := by
      change c j _ ∈ f ⁻¹ᵁ V
      rw [hy']; exact x.2
    let w : ((c j) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme := ⟨(𝒰.X j).isoSpec.hom y, hyV⟩
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨j, ⟨w, ?_⟩⟩
    apply (f ⁻¹ᵁ V).ι.injective
    change (h j ≫ (f ⁻¹ᵁ V).ι) w = (f ⁻¹ᵁ V).ι x
    change (((c j) ∣_ (f ⁻¹ᵁ V)) ≫ (f ⁻¹ᵁ V).ι) w = (f ⁻¹ᵁ V).ι x
    rw [morphismRestrict_ι]
    exact hy'
  have hUfin : ∀ i, IsFinite ((U i).ι ≫ f ∣_ V) := by
    intro i
    rw [← Scheme.Hom.isoOpensRange_inv_comp (h i), Category.assoc]
    infer_instance
  let e := (Fintype.equivFin 𝒰.I₀).symm
  refine IsFinite.of_forall_isClosed_of_iSup_eq_top (f ∣_ V) (U ∘ e) ?_ (fun k => hclosed (e k))
    (fun k => hUfin (e k))
  rw [← hcov]
  exact (Function.Surjective.iSup_comp e.surjective U)
end AffineCharts

end SchemeTheory.NOSProofs.AffineNeighborhoods.GenericFiniteness

namespace AlgebraicGeometry.LocallyQuasiFinite

universe u
open CategoryTheory
open SchemeTheory.NOSProofs.AffineNeighborhoods.GenericFiniteness.AffineCharts in
theorem exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsSeparated f] [QuasiCompact f]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ∃ r : R, r ∉ p ∧ IsFinite (f ∣_ PrimeSpectrum.basicOpen r) :=
  main f p hp

end AlgebraicGeometry.LocallyQuasiFinite
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_LocallyQuasiFinite_exists_isFinite_morphismRestrict_of_irreducibleSpace.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AlgebraicGeometry.LocallyQuasiFinite

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem exists_isFinite_morphismRestrict_of_irreducibleSpace
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsSeparated f] [QuasiCompact f] [IrreducibleSpace Y] :
    ∃ U : Y.Opens, (U : Set Y).Nonempty ∧ IsFinite (f ∣_ U) := by
  classical
  have hLocal : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.isFiniteLocalAtTarget
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    hLocal.toRespects
  let η : Y := genericPoint Y
  obtain ⟨V₀, hV₀, hηV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top η)
  let V : Y.Opens := V₀
  have hV : IsAffineOpen V := hV₀
  have hηV : η ∈ V := hηV
  let e := hV.isoSpec
  let g : (f ⁻¹ᵁ V).toScheme ⟶ Spec (CommRingCat.of Γ(Y, V)) := (f ∣_ V) ≫ e.hom
  let p : PrimeSpectrum Γ(Y, V) := e.hom.base ⟨η, hηV⟩
  have hpmin : p.asIdeal ∈ minimalPrimes Γ(Y, V) := by
    rw [minimalPrimes_eq_minimals]
    refine ⟨p.isPrime, fun q hq hqp => ?_⟩
    let y : V := e.inv.base ⟨q, hq⟩
    have h1 : (⟨η, hηV⟩ : V) ⤳ y := by
      rw [← Topology.IsInducing.subtypeVal.specializes_iff]
      exact genericPoint_specializes _
    have h2 : p ⤳ e.hom.base y := h1.map e.hom.continuous
    have h3 : e.hom.base y = ⟨q, hq⟩ := by
      change (e.inv ≫ e.hom).base ⟨q, hq⟩ = _
      rw [e.inv_hom_id]; rfl
    rw [h3, ← PrimeSpectrum.le_iff_specializes] at h2
    exact h2
  have : IsSeparated g := inferInstance
  obtain ⟨r, hrp, hfin⟩ :=
    exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes g p.asIdeal hpmin
  let W : V.toScheme.Opens := e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
  refine ⟨V.ι ''ᵁ W, ⟨η, ?_⟩, ?_⟩
  · refine ⟨⟨η, hηV⟩, ?_, rfl⟩
    change p ∈ PrimeSpectrum.basicOpen r
    exact hrp
  · have h1 : IsFinite ((f ∣_ V) ∣_ W) := by
      have hc : g ∣_ PrimeSpectrum.basicOpen r =
          ((f ∣_ V) ∣_ W) ≫ (e.hom ∣_ PrimeSpectrum.basicOpen r) :=
        morphismRestrict_comp _ _ _
      rw [hc] at hfin
      have restrictIso {Z T : Scheme.{u}} (e : Z ≅ T) (U : T.Opens) :
          IsIso (e.hom ∣_ U) := inferInstance
      have : IsIso (e.hom ∣_
          (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of Γ(Y, V))).Opens)) :=
        restrictIso e _
      exact (MorphismProperty.cancel_right_of_respectsIso @IsFinite ((f ∣_ V) ∣_ W)
        (e.hom ∣_ PrimeSpectrum.basicOpen r)).mp hfin
    exact ((MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictRestrict f V W)).mp h1)

end AlgebraicGeometry.LocallyQuasiFinite
end
